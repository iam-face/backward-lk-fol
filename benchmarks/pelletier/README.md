# Pelletier benchmark set

Hand-transcribed selection from Pelletier's standard list of problems for
testing automatic theorem provers. Source:

> F. J. Pelletier. *Seventy-five Problems for Testing Automatic Theorem
> Provers.* Journal of Automated Reasoning 2(2):191-216, 1986.

The same problem identifiers (P1, P2, ...) are reused throughout the
literature, which makes the set a useful reference point for a small
classroom prover. The chosen subset spans propositional reasoning, monadic
and dyadic predicates, deeper quantifier nesting (e.g. P19, P20) and a
couple of well-known awkward cases (the drinker formula P18 and Russell's
antinomy P39).

Two files:

- `pelletier_propositional.txt`: P1, P2, P3, P4, P5, P6, P7, P9, P13, P16,
  P17. Biconditional problems (P10-P12, P14, P15) are omitted because the
  course ASCII grammar lacks `<->`.
- `pelletier_first_order.txt`: P18, P19, P20, P24, P25, P39, plus three
  classical quantifier-distribution and one-direction swap formulas added
  as rule-level regression checks.

All formulas in both files are valid in classical first-order logic, so a
sound and complete prover must report every line as proved. Failures are
therefore a measure of search effectiveness under the configured budget.
