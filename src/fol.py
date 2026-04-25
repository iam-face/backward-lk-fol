"""First-order logic AST, substitution, alpha-equivalence."""

from __future__ import annotations

from dataclasses import dataclass
from typing import FrozenSet, Iterator, Optional, Set, Tuple, Union

# --- Terms ---


@dataclass(frozen=True)
class Var:
    name: str

    def __str__(self) -> str:
        return self.name

    def free_vars(self) -> Set[str]:
        return {self.name}

    def func_symbols(self) -> Set[Tuple[str, int]]:
        return set()


@dataclass(frozen=True)
class Const:
    name: str

    def __str__(self) -> str:
        return self.name

    def free_vars(self) -> Set[str]:
        return set()

    def func_symbols(self) -> Set[Tuple[str, int]]:
        return {(self.name, 0)}


@dataclass(frozen=True)
class Func:
    name: str
    args: Tuple["Term", ...]

    def __str__(self) -> str:
        if not self.args:
            return self.name
        return f"{self.name}({', '.join(str(a) for a in self.args)})"

    def free_vars(self) -> Set[str]:
        s: Set[str] = set()
        for a in self.args:
            s |= a.free_vars()
        return s

    def func_symbols(self) -> Set[Tuple[str, int]]:
        fs = {(self.name, len(self.args))}
        for a in self.args:
            fs |= a.func_symbols()
        return fs


Term = Union[Var, Const, Func]


def term_depth(t: Term) -> int:
    if isinstance(t, (Var, Const)):
        return 0
    return 1 + max((term_depth(a) for a in t.args), default=0)


# --- Formulas ---


@dataclass(frozen=True)
class Pred:
    name: str
    args: Tuple[Term, ...]

    def __str__(self) -> str:
        if not self.args:
            return self.name
        return f"{self.name}({', '.join(str(a) for a in self.args)})"

    def free_vars(self) -> Set[str]:
        s: Set[str] = set()
        for a in self.args:
            s |= a.free_vars()
        return s

    def func_symbols(self) -> Set[Tuple[str, int]]:
        fs = {(self.name, len(self.args))}
        for a in self.args:
            fs |= a.func_symbols()
        return fs


@dataclass(frozen=True)
class Bottom:
    def __str__(self) -> str:
        return "False"

    def free_vars(self) -> Set[str]:
        return set()

    def func_symbols(self) -> Set[Tuple[str, int]]:
        return set()


@dataclass(frozen=True)
class Not:
    inner: "Formula"

    def __str__(self) -> str:
        return f"~({self.inner})"

    def free_vars(self) -> Set[str]:
        return self.inner.free_vars()

    def func_symbols(self) -> Set[Tuple[str, int]]:
        return self.inner.func_symbols()


@dataclass(frozen=True)
class And:
    left: "Formula"
    right: "Formula"

    def __str__(self) -> str:
        return f"({self.left}) & ({self.right})"

    def free_vars(self) -> Set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def func_symbols(self) -> Set[Tuple[str, int]]:
        return self.left.func_symbols() | self.right.func_symbols()


@dataclass(frozen=True)
class Or:
    left: "Formula"
    right: "Formula"

    def __str__(self) -> str:
        return f"({self.left}) | ({self.right})"

    def free_vars(self) -> Set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def func_symbols(self) -> Set[Tuple[str, int]]:
        return self.left.func_symbols() | self.right.func_symbols()


@dataclass(frozen=True)
class Imp:
    left: "Formula"
    right: "Formula"

    def __str__(self) -> str:
        return f"({self.left}) -> ({self.right})"

    def free_vars(self) -> Set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def func_symbols(self) -> Set[Tuple[str, int]]:
        return self.left.func_symbols() | self.right.func_symbols()


@dataclass(frozen=True)
class Forall:
    var: str
    body: "Formula"

    def __str__(self) -> str:
        return f"forall {self.var}. ({self.body})"

    def free_vars(self) -> Set[str]:
        return self.body.free_vars() - {self.var}

    def func_symbols(self) -> Set[Tuple[str, int]]:
        return self.body.func_symbols()


@dataclass(frozen=True)
class Exists:
    var: str
    body: "Formula"

    def __str__(self) -> str:
        return f"exists {self.var}. ({self.body})"

    def free_vars(self) -> Set[str]:
        return self.body.free_vars() - {self.var}

    def func_symbols(self) -> Set[Tuple[str, int]]:
        return self.body.func_symbols()


Formula = Union[Pred, Bottom, Not, And, Or, Imp, Forall, Exists]


def formula_depth(f: Formula) -> int:
    if isinstance(f, (Pred, Bottom)):
        return 0
    if isinstance(f, Not):
        return 1 + formula_depth(f.inner)
    if isinstance(f, (And, Or, Imp)):
        return 1 + max(formula_depth(f.left), formula_depth(f.right))
    if isinstance(f, (Forall, Exists)):
        return 1 + formula_depth(f.body)
    raise TypeError(f)


def sub_term(t: Term, x: str, s: Term) -> Term:
    if isinstance(t, Var):
        return s if t.name == x else t
    if isinstance(t, Const):
        return t
    if isinstance(t, Func):
        return Func(t.name, tuple(sub_term(a, x, s) for a in t.args))
    raise TypeError(t)


def sub_formula(f: Formula, x: str, t: Term) -> Formula:
    """Substitute term t for free occurrences of variable x (capture-avoiding)."""
    if isinstance(f, Pred):
        return Pred(f.name, tuple(sub_term(a, x, t) for a in f.args))
    if isinstance(f, Bottom):
        return f
    if isinstance(f, Not):
        return Not(sub_formula(f.inner, x, t))
    if isinstance(f, And):
        return And(sub_formula(f.left, x, t), sub_formula(f.right, x, t))
    if isinstance(f, Or):
        return Or(sub_formula(f.left, x, t), sub_formula(f.right, x, t))
    if isinstance(f, Imp):
        return Imp(sub_formula(f.left, x, t), sub_formula(f.right, x, t))
    if isinstance(f, Forall):
        if f.var == x:
            return f
        if isinstance(t, Var) and t.name == f.var:
            return f
        if f.var in t.free_vars():
            raise ValueError("capture in Forall")
        return Forall(f.var, sub_formula(f.body, x, t))
    if isinstance(f, Exists):
        if f.var == x:
            return f
        if isinstance(t, Var) and t.name == f.var:
            return f
        if f.var in t.free_vars():
            raise ValueError("capture in Exists")
        return Exists(f.var, sub_formula(f.body, x, t))
    raise TypeError(f)


def rename_bound(f: Formula, avoid: Set[str]) -> Formula:
    """Rename bound variables so inner binders do not clash with avoid."""

    def go(g: Formula, avoid2: Set[str]) -> Formula:
        if isinstance(g, (Pred, Bottom)):
            return g
        if isinstance(g, Not):
            return Not(go(g.inner, avoid2))
        if isinstance(g, And):
            return And(go(g.left, avoid2), go(g.right, avoid2))
        if isinstance(g, Or):
            return Or(go(g.left, avoid2), go(g.right, avoid2))
        if isinstance(g, Imp):
            return Imp(go(g.left, avoid2), go(g.right, avoid2))
        if isinstance(g, Forall):
            if g.var in avoid2:
                n = fresh_name(avoid2 | g.body.free_vars())
                b = sub_formula(g.body, g.var, Var(n))
                return Forall(n, go(b, avoid2 | {n}))
            return Forall(g.var, go(g.body, avoid2 | {g.var}))
        if isinstance(g, Exists):
            if g.var in avoid2:
                n = fresh_name(avoid2 | g.body.free_vars())
                b = sub_formula(g.body, g.var, Var(n))
                return Exists(n, go(b, avoid2 | {n}))
            return Exists(g.var, go(g.body, avoid2 | {g.var}))
        raise TypeError(g)

    return go(f, set(avoid))


def fresh_name(used: Set[str], prefix: str = "v") -> str:
    i = 0
    while True:
        n = f"{prefix}{i}"
        if n not in used:
            return n
        i += 1


def alpha_eq(f: Formula, g: Formula) -> bool:
    """Structural equality up to alpha renaming of bound variables."""

    def eq(a: Formula, b: Formula, ren: dict) -> bool:
        if type(a) is not type(b):
            return False
        if isinstance(a, Pred):
            assert isinstance(b, Pred)
            if a.name != b.name or len(a.args) != len(b.args):
                return False
            return all(terms_eq(x, y, ren) for x, y in zip(a.args, b.args))
        if isinstance(a, Bottom):
            return True
        if isinstance(a, Not):
            assert isinstance(b, Not)
            return eq(a.inner, b.inner, ren)
        if isinstance(a, And):
            assert isinstance(b, And)
            return eq(a.left, b.left, ren) and eq(a.right, b.right, ren)
        if isinstance(a, Or):
            assert isinstance(b, Or)
            return eq(a.left, b.left, ren) and eq(a.right, b.right, ren)
        if isinstance(a, Imp):
            assert isinstance(b, Imp)
            return eq(a.left, b.left, ren) and eq(a.right, b.right, ren)
        if isinstance(a, Forall):
            assert isinstance(b, Forall)
            avoid = (
                set(ren.keys())
                | set(ren.values())
                | a.body.free_vars()
                | b.body.free_vars()
                | {a.var, b.var}
            )
            z = fresh_name(avoid, prefix="_a")
            ren2 = dict(ren)
            ren2[a.var] = z
            ren2[b.var] = z
            return eq(sub_formula(a.body, a.var, Var(z)), sub_formula(b.body, b.var, Var(z)), ren2)
        if isinstance(a, Exists):
            assert isinstance(b, Exists)
            avoid = (
                set(ren.keys())
                | set(ren.values())
                | a.body.free_vars()
                | b.body.free_vars()
                | {a.var, b.var}
            )
            z = fresh_name(avoid, prefix="_a")
            ren2 = dict(ren)
            ren2[a.var] = z
            ren2[b.var] = z
            return eq(sub_formula(a.body, a.var, Var(z)), sub_formula(b.body, b.var, Var(z)), ren2)
        raise TypeError(a)

    def terms_eq(x: Term, y: Term, ren: dict) -> bool:
        if isinstance(x, Var) and isinstance(y, Var):
            lx = ren.get(x.name, x.name)
            ly = ren.get(y.name, y.name)
            return lx == ly
        if isinstance(x, Const) and isinstance(y, Const):
            return x.name == y.name
        if isinstance(x, Func) and isinstance(y, Func):
            if x.name != y.name or len(x.args) != len(y.args):
                return False
            return all(terms_eq(p, q, ren) for p, q in zip(x.args, y.args))
        return False

    return eq(f, g, {})


def iter_subformulas(f: Formula) -> Iterator[Formula]:
    yield f
    if isinstance(f, Not):
        yield from iter_subformulas(f.inner)
    elif isinstance(f, (And, Or, Imp)):
        yield from iter_subformulas(f.left)
        yield from iter_subformulas(f.right)
    elif isinstance(f, (Forall, Exists)):
        yield from iter_subformulas(f.body)


def free_symbols_formula(f: Formula) -> Tuple[Set[str], Set[Tuple[str, int]]]:
    """Variables (free) and function/predicate symbols with arity."""
    vs: Set[str] = set()
    fs: Set[Tuple[str, int]] = set()

    def walk(g: Formula) -> None:
        nonlocal vs, fs
        if isinstance(g, Pred):
            fs.add((g.name, len(g.args)))
            for t in g.args:
                vs |= t.free_vars()
                fs |= t.func_symbols()
        elif isinstance(g, Bottom):
            pass
        elif isinstance(g, Not):
            walk(g.inner)
        elif isinstance(g, (And, Or, Imp)):
            walk(g.left)
            walk(g.right)
        elif isinstance(g, (Forall, Exists)):
            walk(g.body)
            vs.discard(g.var)

    walk(f)
    return vs, fs
