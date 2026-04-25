"""Generate parameterised benchmark families into ``benchmarks/generated/``.

Every formula written here is classically valid. The goal is to produce
families where the only thing that changes between successive lines is one
syntactic parameter (chain depth, quantifier nesting, conjunction width).
This lets the experiment plot prover behaviour against problem size on a
controlled axis, rather than mixing structural variation with size variation.

Run from the ``work/`` folder:

    python scripts/generate_benchmarks.py
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "benchmarks" / "generated"


def _write(name: str, lines: list[str]) -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / name).write_text("\n".join(lines) + "\n", encoding="ascii")


def write_prop_implication_chain() -> None:
    """Right-nested implication tautologies of growing depth.

    Line k is ``P -> (P -> ... -> P)`` with k+1 occurrences of ``P``. Every
    such formula is a classical tautology because it has the shape of an
    iterated identity.
    """
    lines: list[str] = []
    for k in range(1, 11):
        body = "P"
        for _ in range(k):
            body = f"P -> ({body})"
        lines.append(body)
    _write("prop_implication_chain.txt", lines)


def write_universal_modus_ponens_chain() -> None:
    """Generalised modus ponens chains that strain term reuse.

    Line k expresses ``forall x. (P0(x) -> P1(x)) & ... & (Pk-1(x) -> Pk(x)) &
    P0(x) -> Pk(x)``. The connection-driven heuristic should resolve every
    instance immediately by unification with the conclusion ``Pk(x)``.
    """
    lines: list[str] = []
    for k in range(1, 8):
        antecedents = " & ".join(f"(P{i}(x) -> P{i + 1}(x))" for i in range(k))
        antecedents = f"({antecedents}) & P0(x)"
        body = f"({antecedents}) -> P{k}(x)"
        lines.append(f"forall x. ({body})")
    _write("universal_modus_ponens.txt", lines)


def write_quantifier_alternation_valid() -> None:
    """Valid quantifier-alternation formulas of growing depth.

    Each line uses a single binary predicate ``R``: a depth-k instance of the
    one-direction quantifier swap ``(exists x. forall y. R(x,y)) -> (forall
    y. exists x. R(x,y))`` extended by an outer chain of identity-style
    implications. These are valid in classical FOL and force the prover to
    interleave eigenvariable and instantiation rules.
    """
    lines: list[str] = []
    for k in range(1, 7):
        ant = "exists x. forall y. R(x, y)"
        cons = "forall y. exists x. R(x, y)"
        guards = " & ".join([f"(forall z. R(z, z))" for _ in range(k)])
        if guards:
            body = f"(({ant}) & ({guards})) -> ({cons})"
        else:
            body = f"({ant}) -> ({cons})"
        lines.append(body)
    _write("quantifier_alternation_valid.txt", lines)


def write_conjunction_width() -> None:
    """Wide conjunctions whose elements are individually valid.

    Line k: ``(A_1 & A_2 & ... & A_k)`` where each ``A_i`` is a small valid
    formula. The conjunction is therefore valid. Wider lines stress the
    propositional ``andR`` branching factor without changing the difficulty
    of any single conjunct.
    """
    lines: list[str] = []
    base_clauses = [
        "(P -> P)",
        "(Q -> Q)",
        "(P | ~P)",
        "(~~R -> R)",
        "((P -> Q) -> (~Q -> ~P))",
        "((P & Q) -> P)",
        "((P & Q) -> Q)",
        "(P -> (P | Q))",
    ]
    for k in range(2, 9):
        body = " & ".join(base_clauses[:k])
        lines.append(body)
    _write("conjunction_width.txt", lines)


def main() -> None:
    write_prop_implication_chain()
    write_universal_modus_ponens_chain()
    write_quantifier_alternation_valid()
    write_conjunction_width()
    print(f"Wrote benchmarks to {OUT}")


if __name__ == "__main__":
    main()
