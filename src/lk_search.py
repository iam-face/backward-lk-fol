"""Backward proof search for LK' (Hou 2021), Algorithm 1 (propositional) and
Algorithm 2 (first-order).

Two modes are supported:

* ``baseline``  -- a faithful implementation of Algorithm 2 with the textbook
  rule priority and naive enumeration of instantiation terms.
* ``improved``  -- the same calculus, the same set of inference rules, but with
  three additional search-control hooks:

    (A) *Loop pruning on instantiation history*. A state is pruned if its
        fingerprint (sequent shape together with the per-quantifier set of
        already-used instantiation terms) reappears on the current
        depth-first path.
    (B) *Connection-driven term selection*. When choosing a witness term
        ``t`` for ``forallL`` / ``existsR``, the prover prefers ``t`` such
        that some atom in the body of the principal formula unifies with a
        literal of opposing classical polarity elsewhere in the sequent.
        Falls back to enumeration when no connection is available.
    (C) *Axiom-closing prioritisation*. Among the legal moves at a node,
        those whose result already satisfies the axiom condition are tried
        first.

Neither mode wraps an external prover.
"""

from __future__ import annotations

import sys
import time
from dataclasses import dataclass
from itertools import product
from typing import Dict, FrozenSet, List, Optional, Set, Tuple, Union

from fol import (
    And,
    Const,
    Exists,
    Forall,
    Formula,
    Func,
    Imp,
    Not,
    Or,
    Pred,
    Var,
    Bottom,
    Term,
    alpha_eq,
    free_symbols_formula,
    rename_bound,
    sub_formula,
    sub_term,
    term_depth,
)
from sequent import Sequent
from unify import collect_atoms, unify_atoms


# --- Configuration and statistics ---------------------------------------------


@dataclass
class SearchConfig:
    max_steps: int = 50_000
    time_limit_s: float = 5.0
    mode: str = "baseline"  # "baseline" | "improved"
    max_term_depth: int = 2
    fresh_prefix: str = "c"


@dataclass
class SearchStats:
    steps: int = 0
    max_depth: int = 0
    quantifier_apps: int = 0
    pruned: int = 0
    connection_hits: int = 0
    wall_s: float = 0.0


@dataclass
class SearchResult:
    proved: bool
    stats: SearchStats
    reason: str


# --- Sequent utilities --------------------------------------------------------


def _formulas_sorted(fs: FrozenSet[Formula]) -> List[Formula]:
    return sorted(fs, key=lambda f: str(f))


def _is_axiom(s: Sequent) -> bool:
    for a in s.left:
        if isinstance(a, Bottom):
            return True
        for b in s.right:
            if alpha_eq(a, b):
                return True
    return False


def _sequent_fingerprint(s: Sequent) -> str:
    return (
        str(sorted(map(str, s.left)))
        + " || "
        + str(sorted(map(str, s.right)))
    )


def _free_names_sequent(s: Sequent) -> Set[str]:
    n: Set[str] = set()
    for f in list(s.left) + list(s.right):
        n |= free_symbols_formula(f)[0]
    return n


def _collect_signature(s: Sequent) -> Set[Tuple[str, int]]:
    sig: Set[Tuple[str, int]] = set()
    for f in list(s.left) + list(s.right):
        sig |= free_symbols_formula(f)[1]
    return sig


def _enumerate_ground_terms(
    sig: Set[Tuple[str, int]], max_depth: int
) -> List[Term]:
    base: List[Term] = [Const(name) for name, ar in sorted(sig) if ar == 0]
    out: List[Term] = list(base)
    seen = {str(t) for t in out}
    for _ in range(max(0, max_depth)):
        new_terms: List[Term] = []
        for name, ar in sorted(sig):
            if ar == 0:
                continue
            for combo in product(base, repeat=ar):
                t = Func(name, combo)
                k = str(t)
                if k not in seen:
                    seen.add(k)
                    new_terms.append(t)
        out.extend(new_terms)
        base = base + new_terms
    return out


def _subterms_in_formula(f: Formula) -> List[Term]:
    out: List[Term] = []

    def walk_term(t: Term) -> None:
        out.append(t)
        if isinstance(t, Func):
            for a in t.args:
                walk_term(a)

    def walk(g: Formula) -> None:
        if isinstance(g, Pred):
            for t in g.args:
                walk_term(t)
        elif isinstance(g, Not):
            walk(g.inner)
        elif isinstance(g, (And, Or, Imp)):
            walk(g.left)
            walk(g.right)
        elif isinstance(g, (Forall, Exists)):
            walk(g.body)

    walk(f)
    return out


def _terms_for_instantiation(s: Sequent, cfg: SearchConfig) -> List[Term]:
    found: List[Term] = []
    seen: Set[str] = set()

    def add_term(t: Term) -> None:
        k = str(t)
        if k not in seen:
            seen.add(k)
            found.append(t)

    sig = _collect_signature(s)
    for name, ar in sig:
        if ar == 0:
            add_term(Const(name))
    for f in list(s.left) + list(s.right):
        for g in _subterms_in_formula(f):
            add_term(g)
    for t in _enumerate_ground_terms(sig, cfg.max_term_depth):
        add_term(t)
    for n in sorted(_free_names_sequent(s)):
        add_term(Var(n))
    return found


def _terms_mentioned_in_sequent(s: Sequent) -> Set[str]:
    keys: Set[str] = set()
    for f in list(s.left) + list(s.right):
        for t in _subterms_in_formula(f):
            keys.add(str(t))
    return keys


def _sort_terms_for_improved(s: Sequent, ts: List[Term]) -> List[Term]:
    """Prefer terms already present in the sequent, then shallow terms."""
    mentioned = _terms_mentioned_in_sequent(s)
    return sorted(
        ts,
        key=lambda t: (0 if str(t) in mentioned else 1, term_depth(t), str(t)),
    )


# --- Connection-driven term selection (improved mode) -------------------------


def _polarised_atoms(f: Formula) -> List[Tuple[Pred, bool]]:
    """All atoms in `f` together with their classical polarity inside `f`.

    Atoms with sign ``True`` are positive occurrences (close against negative
    occurrences in the opposing side of the sequent). The walker handles
    negation, implication antecedents and binary connectives the standard
    way; quantifiers propagate transparently.
    """
    return collect_atoms(f, True)


def _candidate_terms_from_unification(
    s: Sequent,
    principal: Formula,
    bound_var: str,
    body: Formula,
    principal_on_left: bool,
) -> List[Term]:
    """Suggest instantiation terms for the principal's bound variable using
    syntactic unification with literals already on the sequent.

    For each body atom ``A``, scan for any sequent atom ``B`` whose polarity
    is opposite (so an ``id``-style closure becomes possible after the rule
    fires) and try to unify ``A`` and ``B``. If the unifier binds the
    principal's bound variable to a term ``t``, suggest ``t``.

    Returned in priority order, deduplicated by string representation.
    """
    body_atoms = _polarised_atoms(body)
    if not body_atoms:
        return []
    seq_atoms: List[Tuple[Pred, bool, bool]] = []  # (atom, polarity, is_left)
    for f in s.left:
        if f is principal:
            continue
        for a, sign in _polarised_atoms(f):
            seq_atoms.append((a, sign, True))
    for f in s.right:
        if f is principal:
            continue
        for a, sign in _polarised_atoms(f):
            seq_atoms.append((a, sign, False))

    suggestions: List[Term] = []
    seen: Set[str] = set()
    for ba, ba_sign in body_atoms:
        for sa, sa_sign, sa_is_left in seq_atoms:
            if principal_on_left:
                wants_positive = ba_sign
                provides_positive = (sa_sign if not sa_is_left else not sa_sign)
            else:
                wants_positive = ba_sign
                provides_positive = (not sa_sign if not sa_is_left else sa_sign)
            if wants_positive == provides_positive:
                continue
            sigma = unify_atoms(ba, sa)
            if sigma is None:
                continue
            t = sigma.get(bound_var)
            if t is None:
                continue
            if isinstance(t, Var) and t.name == bound_var:
                continue
            k = str(t)
            if k in seen:
                continue
            seen.add(k)
            suggestions.append(t)
    return suggestions


# --- Used-terms bookkeeping ---------------------------------------------------


class UsedTerms:
    def __init__(self, data: Dict[str, FrozenSet[str]] | None = None) -> None:
        self.data: Dict[str, FrozenSet[str]] = dict(data or {})

    def key_for(self, f: Formula) -> str:
        return str(f)

    def used(self, f: Formula) -> FrozenSet[str]:
        return self.data.get(self.key_for(f), frozenset())

    def with_used(self, f: Formula, t: Term) -> "UsedTerms":
        k = self.key_for(f)
        prev = set(self.data.get(k, frozenset()))
        prev.add(str(t))
        d = dict(self.data)
        d[k] = frozenset(prev)
        return UsedTerms(d)


def _state_fingerprint(s: Sequent, used: UsedTerms) -> str:
    ud = tuple(
        sorted((k, tuple(sorted(v))) for k, v in used.data.items())
    )
    return _sequent_fingerprint(s) + " ||USED|| " + str(ud)


# --- Backward LK' rules -------------------------------------------------------


def _without(fs: FrozenSet[Formula], x: Formula) -> FrozenSet[Formula]:
    return frozenset(f for f in fs if f is not x)


def _with(fs: FrozenSet[Formula], *add: Formula) -> FrozenSet[Formula]:
    t = set(fs)
    for a in add:
        t.add(a)
    return frozenset(t)


def _negL(s: Sequent, fm: Formula) -> Sequent | None:
    if not isinstance(fm, Not):
        return None
    return Sequent(_without(s.left, fm), _with(s.right, fm.inner))


def _negR(s: Sequent, fm: Formula) -> Sequent | None:
    if not isinstance(fm, Not):
        return None
    return Sequent(_with(s.left, fm.inner), _without(s.right, fm))


def _andL(s: Sequent, fm: Formula) -> Sequent | None:
    if not isinstance(fm, And):
        return None
    return Sequent(_with(_without(s.left, fm), fm.left, fm.right), s.right)


def _orR(s: Sequent, fm: Formula) -> Sequent | None:
    if not isinstance(fm, Or):
        return None
    return Sequent(s.left, _with(_without(s.right, fm), fm.left, fm.right))


def _impR(s: Sequent, fm: Formula) -> Sequent | None:
    if not isinstance(fm, Imp):
        return None
    return Sequent(_with(s.left, fm.left), _with(_without(s.right, fm), fm.right))


def _andR(s: Sequent, fm: Formula) -> Tuple[Sequent, Sequent]:
    gamma = s.left
    delta = _without(s.right, fm)
    return (
        Sequent(gamma, _with(delta, fm.left)),
        Sequent(gamma, _with(delta, fm.right)),
    )


def _orL(s: Sequent, fm: Formula) -> Tuple[Sequent, Sequent]:
    gamma = _without(s.left, fm)
    return (
        Sequent(_with(gamma, fm.left), s.right),
        Sequent(_with(gamma, fm.right), s.right),
    )


def _impL(s: Sequent, fm: Formula) -> Tuple[Sequent, Sequent]:
    """Gamma, A->B |- Delta  ==>  Gamma |- A, Delta  and  Gamma, B |- Delta."""
    gamma = _without(s.left, fm)
    s1 = Sequent(gamma, _with(s.right, fm.left))
    s2 = Sequent(_with(gamma, fm.right), s.right)
    return s1, s2


def _forallL(s: Sequent, fm: Formula, t: Term) -> Sequent | None:
    if not isinstance(fm, Forall):
        return None
    body = rename_bound(fm.body, _free_names_sequent(s) | {fm.var})
    inst = sub_formula(body, fm.var, t)
    return Sequent(_with(s.left, inst), s.right)


def _existsR(s: Sequent, fm: Formula, t: Term) -> Sequent | None:
    if not isinstance(fm, Exists):
        return None
    body = rename_bound(fm.body, _free_names_sequent(s) | {fm.var})
    inst = sub_formula(body, fm.var, t)
    return Sequent(s.left, _with(s.right, inst))


def _forallR(s: Sequent, fm: Formula, fresh: str) -> Sequent | None:
    if not isinstance(fm, Forall):
        return None
    c = Const(fresh)
    body = rename_bound(fm.body, _free_names_sequent(s) | {fm.var} | {fresh})
    inst = sub_formula(body, fm.var, c)
    return Sequent(s.left, _with(_without(s.right, fm), inst))


def _existsL(s: Sequent, fm: Formula, fresh: str) -> Sequent | None:
    if not isinstance(fm, Exists):
        return None
    c = Const(fresh)
    body = rename_bound(fm.body, _free_names_sequent(s) | {fm.var} | {fresh})
    inst = sub_formula(body, fm.var, c)
    return Sequent(_with(_without(s.left, fm), inst), s.right)


def _next_fresh(s: Sequent, cfg: SearchConfig, counter: int) -> Tuple[str, int]:
    used = _free_names_sequent(s)
    prefix = cfg.fresh_prefix
    name = f"{prefix}{counter}"
    while name in used:
        counter += 1
        name = f"{prefix}{counter}"
    return name, counter + 1


# --- Move generation ----------------------------------------------------------


Move = Tuple[str, Union[Sequent, Tuple[Sequent, Sequent]], int, UsedTerms]


def _propositional_moves(
    s: Sequent, used: UsedTerms, fc0: int
) -> List[Move]:
    out: List[Move] = []
    for fm in _formulas_sorted(s.left):
        ns = _negL(s, fm)
        if ns is not None:
            out.append(("negL", ns, fc0, used))
        ns = _andL(s, fm)
        if ns is not None:
            out.append(("andL", ns, fc0, used))
    for fm in _formulas_sorted(s.right):
        ns = _negR(s, fm)
        if ns is not None:
            out.append(("negR", ns, fc0, used))
        ns = _orR(s, fm)
        if ns is not None:
            out.append(("orR", ns, fc0, used))
        ns = _impR(s, fm)
        if ns is not None:
            out.append(("impR", ns, fc0, used))
    for fm in _formulas_sorted(s.right):
        if isinstance(fm, And):
            out.append(("andR", _andR(s, fm), fc0, used))
    for fm in _formulas_sorted(s.left):
        if isinstance(fm, Or):
            out.append(("orL", _orL(s, fm), fc0, used))
        if isinstance(fm, Imp):
            out.append(("impL", _impL(s, fm), fc0, used))
    return out


def _eigenvariable_moves(
    s: Sequent, cfg: SearchConfig, used: UsedTerms, fc0: int
) -> Tuple[List[Move], int]:
    out: List[Move] = []
    fc = fc0
    for fm in _formulas_sorted(s.right):
        if isinstance(fm, Forall):
            name, fc = _next_fresh(s, cfg, fc)
            ch = _forallR(s, fm, name)
            if ch is not None:
                out.append(("forallR", ch, fc, used))
    for fm in _formulas_sorted(s.left):
        if isinstance(fm, Exists):
            name, fc = _next_fresh(s, cfg, fc)
            ch = _existsL(s, fm, name)
            if ch is not None:
                out.append(("existsL", ch, fc, used))
    return out, fc


def _term_instantiation_moves(
    s: Sequent,
    cfg: SearchConfig,
    used: UsedTerms,
    fc0: int,
    stats: Optional[SearchStats] = None,
) -> List[Move]:
    out: List[Move] = []
    enumerated = _terms_for_instantiation(s, cfg)
    if cfg.mode == "improved":
        enumerated = _sort_terms_for_improved(s, enumerated)

    for fm in _formulas_sorted(s.left):
        if isinstance(fm, Forall):
            ordered: List[Term] = []
            seen: Set[str] = set()
            if cfg.mode == "improved":
                conn = _candidate_terms_from_unification(
                    s, fm, fm.var, fm.body, True
                )
                for t in conn:
                    k = str(t)
                    if k not in seen:
                        seen.add(k)
                        ordered.append(t)
                if conn and stats is not None:
                    stats.connection_hits += 1
            for t in enumerated:
                k = str(t)
                if k not in seen:
                    seen.add(k)
                    ordered.append(t)
            u = used.used(fm)
            for t in ordered:
                if str(t) in u:
                    continue
                ch = _forallL(s, fm, t)
                if ch is not None:
                    nu = used.with_used(fm, t)
                    out.append(("forallL_t", ch, fc0, nu))

    for fm in _formulas_sorted(s.right):
        if isinstance(fm, Exists):
            ordered = []
            seen = set()
            if cfg.mode == "improved":
                conn = _candidate_terms_from_unification(
                    s, fm, fm.var, fm.body, False
                )
                for t in conn:
                    k = str(t)
                    if k not in seen:
                        seen.add(k)
                        ordered.append(t)
                if conn and stats is not None:
                    stats.connection_hits += 1
            for t in enumerated:
                k = str(t)
                if k not in seen:
                    seen.add(k)
                    ordered.append(t)
            u = used.used(fm)
            for t in ordered:
                if str(t) in u:
                    continue
                ch = _existsR(s, fm, t)
                if ch is not None:
                    nu = used.with_used(fm, t)
                    out.append(("existsR_t", ch, fc0, nu))

    return out


def _fresh_quantifier_fallback_moves(
    s: Sequent, cfg: SearchConfig, used: UsedTerms, fc0: int
) -> List[Move]:
    out: List[Move] = []
    fc = fc0
    for fm in _formulas_sorted(s.left):
        if isinstance(fm, Forall):
            name, fc = _next_fresh(s, cfg, fc)
            t: Term = Const(name)
            ch = _forallL(s, fm, t)
            if ch is not None:
                nu = used.with_used(fm, t)
                out.append(("forallL_new", ch, fc, nu))
    for fm in _formulas_sorted(s.right):
        if isinstance(fm, Exists):
            name, fc = _next_fresh(s, cfg, fc)
            t = Const(name)
            ch = _existsR(s, fm, t)
            if ch is not None:
                nu = used.with_used(fm, t)
                out.append(("existsR_new", ch, fc, nu))
    return out


def generate_moves(
    s: Sequent,
    cfg: SearchConfig,
    used: UsedTerms,
    fresh_counter: int,
    stats: Optional[SearchStats] = None,
) -> List[Move]:
    """Produce candidate moves in textbook priority order.

    For Algorithm 2 (Hou 2021): non-branching propositional, branching
    propositional, eigenvariable rules, then ``forallL`` / ``existsR``
    instantiations with terms from the current universe, falling back to a
    brand new constant.
    """
    out: List[Move] = []
    out.extend(_propositional_moves(s, used, fresh_counter))
    eig_moves, fc_after_eig = _eigenvariable_moves(s, cfg, used, fresh_counter)
    out.extend(eig_moves)
    out.extend(_term_instantiation_moves(s, cfg, used, fresh_counter, stats))
    out.extend(_fresh_quantifier_fallback_moves(s, cfg, used, fc_after_eig))

    if cfg.mode == "improved":
        def closes(res: Union[Sequent, Tuple[Sequent, Sequent]]) -> int:
            if isinstance(res, tuple):
                return int(_is_axiom(res[0]) and _is_axiom(res[1]))
            return int(_is_axiom(res))

        out.sort(key=lambda m: (-closes(m[1]),))

    return out


# --- Driver -------------------------------------------------------------------


def prove_sequent(goal: Sequent, cfg: SearchConfig) -> SearchResult:
    prev_rl = sys.getrecursionlimit()
    sys.setrecursionlimit(max(prev_rl, 50_000))
    try:
        return _prove_sequent_inner(goal, cfg)
    finally:
        sys.setrecursionlimit(prev_rl)


def _prove_sequent_inner(goal: Sequent, cfg: SearchConfig) -> SearchResult:
    stats = SearchStats()
    t0 = time.perf_counter()
    path_fps: List[str] = []

    def dfs(s: Sequent, depth: int, used: UsedTerms, fc: int) -> bool:
        nonlocal stats
        stats.steps += 1
        stats.max_depth = max(stats.max_depth, depth)
        if stats.steps >= cfg.max_steps:
            return False
        if time.perf_counter() - t0 > cfg.time_limit_s:
            return False
        if _is_axiom(s):
            return True

        if cfg.mode == "improved":
            fp = _state_fingerprint(s, used)
            if fp in path_fps:
                stats.pruned += 1
                return False
            path_fps.append(fp)

        moves = generate_moves(s, cfg, used, fc, stats)
        if not moves:
            if cfg.mode == "improved":
                path_fps.pop()
            return False

        for label, res, fc_new, used_new in moves:
            if label.startswith(("forall", "exists")):
                stats.quantifier_apps += 1
            if isinstance(res, tuple):
                s1, s2 = res
                ok = dfs(s1, depth + 1, used_new, fc_new) and dfs(
                    s2, depth + 1, used_new, fc_new
                )
            else:
                ok = dfs(res, depth + 1, used_new, fc_new)
            if ok:
                if cfg.mode == "improved":
                    path_fps.pop()
                return True

        if cfg.mode == "improved":
            path_fps.pop()
        return False

    proved = dfs(goal, 0, UsedTerms(), 0)
    stats.wall_s = time.perf_counter() - t0
    if proved:
        return SearchResult(True, stats, "proved")
    if stats.steps >= cfg.max_steps:
        return SearchResult(False, stats, "step_limit")
    if stats.wall_s >= cfg.time_limit_s - 1e-9:
        return SearchResult(False, stats, "time_limit")
    return SearchResult(False, stats, "open")


def prove_formula(formula: Formula, cfg: SearchConfig) -> SearchResult:
    goal = Sequent(frozenset(), frozenset({formula}))
    return prove_sequent(goal, cfg)
