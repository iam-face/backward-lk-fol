"""First-order syntactic unification used by the connection-driven heuristic.

The improved prover uses unification to bias term selection in `forallL` and
`existsR`: when a quantified formula is about to be instantiated, the search
prefers an instantiation term `t` such that the resulting instance unifies
with a literal of opposing classical polarity elsewhere in the sequent. The
branch then tends to close by ``id`` after a short propositional clean-up.
The heuristic only re-orders existing rule applications, so soundness is
inherited from LK'.

Only the body of the quantified formula is examined; deeper proof obligations
still go through the full LK' rule set. Unification follows the standard
algorithm (Robinson, 1965) with an explicit occurs-check.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Tuple

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
    Term,
    Var,
)


Subst = Dict[str, Term]


def _walk(t: Term, sigma: Subst) -> Term:
    while isinstance(t, Var) and t.name in sigma:
        nxt = sigma[t.name]
        if nxt is t:
            return t
        t = nxt
    return t


def _occurs(name: str, t: Term, sigma: Subst) -> bool:
    t = _walk(t, sigma)
    if isinstance(t, Var):
        return t.name == name
    if isinstance(t, Const):
        return False
    if isinstance(t, Func):
        return any(_occurs(name, a, sigma) for a in t.args)
    return False


def _bind(name: str, t: Term, sigma: Subst) -> Optional[Subst]:
    if _occurs(name, t, sigma):
        return None
    new = dict(sigma)
    new[name] = t
    return new


def unify_terms(a: Term, b: Term, sigma: Optional[Subst] = None) -> Optional[Subst]:
    sigma = dict(sigma) if sigma else {}
    a = _walk(a, sigma)
    b = _walk(b, sigma)
    if isinstance(a, Var):
        if isinstance(b, Var) and a.name == b.name:
            return sigma
        return _bind(a.name, b, sigma)
    if isinstance(b, Var):
        return _bind(b.name, a, sigma)
    if isinstance(a, Const) and isinstance(b, Const):
        return sigma if a.name == b.name else None
    if isinstance(a, Func) and isinstance(b, Func):
        if a.name != b.name or len(a.args) != len(b.args):
            return None
        for x, y in zip(a.args, b.args):
            sigma = unify_terms(x, y, sigma)
            if sigma is None:
                return None
        return sigma
    return None


def unify_atoms(a: Pred, b: Pred, sigma: Optional[Subst] = None) -> Optional[Subst]:
    if a.name != b.name or len(a.args) != len(b.args):
        return None
    s: Optional[Subst] = dict(sigma) if sigma else {}
    for x, y in zip(a.args, b.args):
        s = unify_terms(x, y, s)
        if s is None:
            return None
    return s


def collect_atoms(f: Formula, sign: bool = True) -> List[Tuple[Pred, bool]]:
    """Collect predicate atoms with their classical polarity.

    `sign` is True for positive contexts. Negation flips it, implication
    flips its antecedent, and the other connectives propagate the sign as in
    classical logic. The polarity is used by the connection heuristic so
    that a negated occurrence on the left can connect with a positive
    occurrence on the right.
    """
    out: List[Tuple[Pred, bool]] = []

    def walk(g: Formula, s: bool) -> None:
        if isinstance(g, Pred):
            out.append((g, s))
            return
        if isinstance(g, Not):
            walk(g.inner, not s)
            return
        if isinstance(g, And) or isinstance(g, Or):
            walk(g.left, s)
            walk(g.right, s)
            return
        if isinstance(g, Imp):
            walk(g.left, not s)
            walk(g.right, s)
            return
        if isinstance(g, (Forall, Exists)):
            walk(g.body, s)
            return

    walk(f, sign)
    return out
