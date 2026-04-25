"""Run baseline vs improved prover on benchmark .txt files (one formula per
line) and write a CSV summarising every run.

Usage (from ``work/``):

    python scripts/run_experiments.py
    python scripts/run_experiments.py --max-steps 200000 --time-limit 5.0

Each formula is processed twice (mode = baseline, then mode = improved) under
identical caps so per-row metrics are directly comparable.
"""

from __future__ import annotations

import argparse
import csv
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
sys.path.insert(0, str(SRC))

from lk_search import SearchConfig, prove_formula  # noqa: E402
from parser import parse_formula_line  # noqa: E402


# Files whose every line is invalid in classical FOL. Useful to record the
# expected outcome so that "did not prove" can be classified as correct
# behaviour (timeout/open is the only sound response from a sound prover) or
# as a true failure on a valid formula.
_INVALID_FILES = {"fol_invalid_or_hard.txt"}


def _expected_valid(filename: str) -> bool:
    return filename not in _INVALID_FILES


def load_formulas(path: Path) -> list[tuple[str, str]]:
    out: list[tuple[str, str]] = []
    n = 0
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        n += 1
        out.append((f"L{n}", line))
    return out


def collect_txt_files(root: Path) -> list[Path]:
    return sorted(p for p in root.rglob("*.txt") if p.is_file())


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--benchmark-root", type=Path, default=ROOT / "benchmarks")
    ap.add_argument("--out", type=Path, default=ROOT / "results" / "run.csv")
    ap.add_argument("--max-steps", type=int, default=100_000)
    ap.add_argument("--time-limit", type=float, default=5.0)
    args = ap.parse_args()

    args.out.parent.mkdir(parents=True, exist_ok=True)
    files = collect_txt_files(args.benchmark_root)
    if not files:
        print("No .txt benchmarks under", args.benchmark_root)
        sys.exit(1)

    fieldnames = [
        "dataset",
        "file",
        "line_id",
        "expected_valid",
        "mode",
        "proved",
        "reason",
        "steps",
        "max_depth",
        "quantifier_apps",
        "pruned",
        "connection_hits",
        "wall_s",
    ]
    with args.out.open("w", newline="", encoding="utf-8") as fp:
        w = csv.DictWriter(fp, fieldnames=fieldnames)
        w.writeheader()
        for bf in files:
            rel = bf.relative_to(args.benchmark_root)
            dataset = str(rel.parent)
            for mode in ("baseline", "improved"):
                for lid, text in load_formulas(bf):
                    t0 = time.perf_counter()
                    try:
                        f = parse_formula_line(text)
                    except Exception as e:  # noqa: BLE001
                        w.writerow(
                            {
                                "dataset": dataset,
                                "file": rel.name,
                                "line_id": lid,
                                "expected_valid": _expected_valid(rel.name),
                                "mode": mode,
                                "proved": False,
                                "reason": f"parse_error:{e}",
                                "steps": "",
                                "max_depth": "",
                                "quantifier_apps": "",
                                "pruned": "",
                                "connection_hits": "",
                                "wall_s": round(time.perf_counter() - t0, 6),
                            }
                        )
                        continue
                    cfg = SearchConfig(
                        max_steps=args.max_steps,
                        time_limit_s=args.time_limit,
                        mode=mode,
                    )
                    r = prove_formula(f, cfg)
                    w.writerow(
                        {
                            "dataset": dataset,
                            "file": rel.name,
                            "line_id": lid,
                            "expected_valid": _expected_valid(rel.name),
                            "mode": mode,
                            "proved": r.proved,
                            "reason": r.reason,
                            "steps": r.stats.steps,
                            "max_depth": r.stats.max_depth,
                            "quantifier_apps": r.stats.quantifier_apps,
                            "pruned": r.stats.pruned,
                            "connection_hits": r.stats.connection_hits,
                            "wall_s": round(r.stats.wall_s, 6),
                        }
                    )

    print(f"Wrote {args.out}")


if __name__ == "__main__":
    main()
