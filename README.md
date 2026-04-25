# 3806ICT Assignment 1: backward LK' proof search

A Python implementation of the backward LK' proof-search procedure
described in Hou (2021), Chapter 2, Algorithm 2, with an `improved`
variant that adds three search-control hooks while keeping the same
LK' rule set.

## Layout

```
src/
  fol.py             # AST (Term, Formula), substitution, alpha-equivalence
  parser.py          # recursive-descent parser for the course ASCII grammar
  sequent.py         # two-sided frozenset sequent type
  unify.py           # first-order syntactic unification with occurs check
  lk_search.py       # rules, move generator and DFS engine (both modes)
tests/
  test_parser_and_prover.py
benchmarks/
  crafted/           # 8 propositional valid, 8 first-order valid, 4 invalid
  generated/         # 4 parameterised families written by generate_benchmarks.py
  pelletier/         # 11 + 9 transcribed Pelletier (1986) problems + README
scripts/
  generate_benchmarks.py    # writes benchmarks/generated/*.txt
  run_experiments.py        # runs both modes on every benchmark, writes CSV
results/
  run.csv            # most recent output of run_experiments.py
requirements.txt
```

## Input syntax

One formula per line. Lines starting with `#` are comments.

- Connectives: `~` (not), `&` (and), `|` (or), `->` (implies), `False` (bottom).
- Quantifiers: `forall x. (F)`, `exists x. (F)`.
- Predicates: `P`, `P(x)`, `R(x, y)`.
- Terms: lowercase identifier = variable, uppercase = nullary constant,
  `f(x, y)` = function application.

## Modes

- **`baseline`**: a faithful realisation of Algorithm 2. Move
  priority follows the textbook: non-branching propositional,
  branching propositional, eigenvariable, then `forallL` / `existsR`
  with terms drawn from the current Herbrand-style universe, falling
  back to a brand-new constant.
- **`improved`**: the same calculus and the same rule set, with
  three additional search-control hooks:
  - **(A) Loop pruning** on the joint state of sequent shape and
    per-quantifier instantiation history (`UsedTerms`); a state is
    pruned when its fingerprint already appears on the depth-first
    call stack.
  - **(B) Connection-driven term selection**: when expanding
    `forallL` or `existsR`, prefer instantiation terms drawn from
    the most-general unifier between an atom of the principal's body
    and an atom of opposing classical polarity in the rest of the
    sequent. Falls back to enumeration when no connection exists.
  - **(C) Axiom-closing prioritisation**: candidate moves whose
    result already satisfies the axiom condition are tried first.

The hooks add no inference rules and remove none, so soundness is
inherited directly from LK'.

## Reproducing the experiment

From this directory:

```
pip install -r requirements.txt
python -m pytest tests/ -v
python scripts/generate_benchmarks.py
python scripts/run_experiments.py --benchmark-root benchmarks \
  --out results/run.csv --max-steps 200000 --time-limit 5.0
```

`run_experiments.py` walks every `.txt` benchmark, runs both modes
under identical caps (200,000 expansion steps and 5 s clock
per formula), and writes one CSV row per (formula, mode) pair with
the fields:

```
dataset, file, line_id, expected_valid, mode, proved, reason,
steps, max_depth, quantifier_apps, pruned, connection_hits, wall_s
```

`expected_valid = False` is inferred from the file name (currently
only `benchmarks/crafted/fol_invalid_or_hard.txt` contains invalid
formulas); the prover should classify every one of those as `open`
or as a timeout, never as `proved`.

## Tests

The `pytest` suite covers the parser, alpha-equivalence,
capture-avoiding substitution, every propositional rule and a small
set of first-order proofs in both modes (including Pelletier P18,
the drinker formula, under the `improved` mode and a regression
that neither mode proves `(P -> Q) -> (Q -> P)`).

```
python -m pytest tests/ -v
```

## References

- Hou, Z.: *Fundamentals of Logic and Computation: With Practical
  Automated Reasoning and Verification*. Texts in Computer Science.
  Springer, Cham (2021).
- Pelletier, F. J.: Seventy-five Problems for Testing Automatic
  Theorem Provers. *Journal of Automated Reasoning* 2(2),
  191-216 (1986).
- Robinson, J. A.: A Machine-Oriented Logic Based on the
  Resolution Principle. *Journal of the ACM* 12(1), 23-41 (1965).
