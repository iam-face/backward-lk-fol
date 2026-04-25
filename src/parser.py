"""Parse one FOL formula per line. ASCII syntax (see README)."""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Tuple

from fol import And, Const, Exists, Forall, Formula, Func, Imp, Not, Or, Pred, Term, Var, Bottom


@dataclass
class ParseError(Exception):
    msg: str
    pos: int


class Lexer:
    def __init__(self, s: str) -> None:
        self.s = s.strip()
        self.i = 0
        self.n = len(self.s)

    def peek(self) -> str:
        self._skip_ws()
        return self.s[self.i] if self.i < self.n else ""

    def _skip_ws(self) -> None:
        while self.i < self.n and self.s[self.i].isspace():
            self.i += 1

    def consume(self, ch: str) -> None:
        self._skip_ws()
        if self.i >= self.n or self.s[self.i] != ch:
            raise ParseError(f"expected {ch!r}", self.i)
        self.i += 1

    def try_consume(self, ch: str) -> bool:
        self._skip_ws()
        if self.i < self.n and self.s[self.i] == ch:
            self.i += 1
            return True
        return False

    def read_ident(self) -> str:
        self._skip_ws()
        if self.i >= self.n:
            raise ParseError("expected identifier", self.i)
        c = self.s[self.i]
        if not (c.isalpha() or c == "_"):
            raise ParseError("expected identifier start", self.i)
        j = self.i
        while j < self.n and (self.s[j].isalnum() or self.s[j] == "_"):
            j += 1
        name = self.s[self.i : j]
        self.i = j
        return name


def parse_formula_line(line: str) -> Formula:
    """Parse a single formula from a line (comments: # to EOL)."""
    if "#" in line:
        line = line[: line.index("#")]
    line = line.strip()
    if not line:
        raise ValueError("empty line")
    f, pos = parse_formula_full(line, 0)
    lexer = Lexer(line[pos:])
    lexer._skip_ws()
    if lexer.i < lexer.n:
        raise ParseError("trailing junk", lexer.i)
    return f


def parse_formula_full(s: str, start: int) -> Tuple[Formula, int]:
    lx = Lexer(s[start:])
    f = parse_imp(lx)
    return f, start + lx.i


def parse_imp(lx: Lexer) -> Formula:
    a = parse_or(lx)
    lx._skip_ws()
    if lx.i + 1 < lx.n and lx.s[lx.i : lx.i + 2] == "->":
        lx.i += 2
        b = parse_imp(lx)
        return Imp(a, b)
    return a


def parse_or(lx: Lexer) -> Formula:
    a = parse_and(lx)
    while True:
        lx._skip_ws()
        if lx.try_consume("|"):
            b = parse_and(lx)
            a = Or(a, b)
        else:
            break
    return a


def parse_and(lx: Lexer) -> Formula:
    a = parse_unary(lx)
    while True:
        lx._skip_ws()
        if lx.try_consume("&"):
            b = parse_unary(lx)
            a = And(a, b)
        else:
            break
    return a


def parse_unary(lx: Lexer) -> Formula:
    lx._skip_ws()
    if lx.try_consume("~"):
        return Not(parse_unary(lx))
    if _starts_with_keyword(lx, "forall"):
        lx.i += len("forall")
        lx._skip_ws()
        v = lx.read_ident()
        lx.consume(".")
        body = parse_imp(lx)
        return Forall(v, body)
    if _starts_with_keyword(lx, "exists"):
        lx.i += len("exists")
        lx._skip_ws()
        v = lx.read_ident()
        lx.consume(".")
        body = parse_imp(lx)
        return Exists(v, body)
    return parse_atom(lx)


def _starts_with_keyword(lx: Lexer, kw: str) -> bool:
    lx._skip_ws()
    if lx.i + len(kw) > lx.n:
        return False
    chunk = lx.s[lx.i : lx.i + len(kw)]
    if chunk != kw:
        return False
    after = lx.i + len(kw)
    if after < lx.n and (lx.s[after].isalnum() or lx.s[after] == "_"):
        return False
    return True


def parse_atom(lx: Lexer) -> Formula:
    lx._skip_ws()
    if lx.try_consume("("):
        f = parse_imp(lx)
        lx.consume(")")
        return f
    name = lx.read_ident()
    if name == "False" or name == "bottom":
        return Bottom()
    lx._skip_ws()
    if lx.try_consume("("):
        args = parse_term_list(lx)
        lx.consume(")")
        return Pred(name, tuple(args))
    return Pred(name, ())


def parse_term_list(lx: Lexer) -> List[Term]:
    lx._skip_ws()
    if lx.peek() == ")":
        return []
    ts = [parse_term(lx)]
    while True:
        lx._skip_ws()
        if lx.try_consume(","):
            ts.append(parse_term(lx))
        else:
            break
    return ts


def parse_term(lx: Lexer) -> Term:
    lx._skip_ws()
    if lx.peek() == "(":
        lx.consume("(")
        t = parse_term(lx)
        lx.consume(")")
        return t
    name = lx.read_ident()
    lx._skip_ws()
    if lx.try_consume("("):
        args = parse_term_list(lx)
        lx.consume(")")
        return Func(name, tuple(args))
    if name[0].isupper():
        return Const(name)
    return Var(name)
