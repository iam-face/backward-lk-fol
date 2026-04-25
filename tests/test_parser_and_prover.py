"""Regression tests for the parser, AST, and prover.

Small, fast checks covering the textbook examples and a handful of
soundness conditions (parser shape, alpha-equivalence, an invalid
formula that must not be proved, the drinker formula under improved
mode).
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1] / "src"
sys.path.insert(0, str(ROOT))

from fol import alpha_eq  # noqa: E402
from lk_search import SearchConfig, prove_formula  # noqa: E402
from parser import parse_formula_line  # noqa: E402


# --- Parser ------------------------------------------------------------------


def test_parse_simple() -> None:
    f = parse_formula_line("P -> P")
    assert str(f) == "(P) -> (P)"


def test_parse_quantifiers() -> None:
    f = parse_formula_line("forall x. (R(x) -> R(x))")
    assert "forall" in str(f)


def test_alpha_eq() -> None:
    a = parse_formula_line("forall x. R(x)")
    b = parse_formula_line("forall y. R(y)")
    assert alpha_eq(a, b)


# --- Baseline prover (faithful to Algorithm 2) -------------------------------


@pytest.fixture()
def cfg_base() -> SearchConfig:
    return SearchConfig(max_steps=20_000, time_limit_s=2.0, mode="baseline")


@pytest.fixture()
def cfg_impr() -> SearchConfig:
    return SearchConfig(max_steps=20_000, time_limit_s=2.0, mode="improved")


@pytest.mark.parametrize(
    "line",
    [
        "P -> P",
        "(P -> Q) -> ((~P -> Q) -> Q)",
        "P | ~P",
        "((P | Q) & ~P) -> Q",
        "forall x. (R(x) -> R(x))",
        "(forall x. P(x)) -> (exists x. P(x))",
    ],
)
def test_baseline_proves_valid(cfg_base: SearchConfig, line: str) -> None:
    f = parse_formula_line(line)
    r = prove_formula(f, cfg_base)
    assert r.proved, (r.reason, r.stats.steps)


def test_baseline_does_not_prove_invalid(cfg_base: SearchConfig) -> None:
    f = parse_formula_line("(P -> Q) -> (Q -> P)")
    r = prove_formula(f, cfg_base)
    assert not r.proved


# --- Improved prover ---------------------------------------------------------


@pytest.mark.parametrize(
    "line",
    [
        "P -> P",
        "(P -> Q) -> ((~P -> Q) -> Q)",
        "P | ~P",
        "((P | Q) & ~P) -> Q",
        "forall x. (R(x) -> R(x))",
        "(forall x. P(x)) -> (exists x. P(x))",
        "(forall x. (P(x) -> Q(x))) -> ((exists x. P(x)) -> exists x. Q(x))",
    ],
)
def test_improved_proves_valid(cfg_impr: SearchConfig, line: str) -> None:
    f = parse_formula_line(line)
    r = prove_formula(f, cfg_impr)
    assert r.proved, (r.reason, r.stats.steps)


def test_improved_does_not_prove_invalid(cfg_impr: SearchConfig) -> None:
    f = parse_formula_line("(P -> Q) -> (Q -> P)")
    r = prove_formula(f, cfg_impr)
    assert not r.proved


def test_improved_solves_drinker(cfg_impr: SearchConfig) -> None:
    """Pelletier P18 (drinker formula) under the improved mode."""
    f = parse_formula_line("exists y. forall x. (D(y) -> D(x))")
    r = prove_formula(f, cfg_impr)
    assert r.proved, (r.reason, r.stats.steps)
