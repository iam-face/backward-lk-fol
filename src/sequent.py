"""Sequents as sets of formulas."""

from __future__ import annotations

from dataclasses import dataclass
from typing import FrozenSet

from fol import Formula


@dataclass(frozen=True)
class Sequent:
    left: FrozenSet[Formula]
    right: FrozenSet[Formula]

    def __str__(self) -> str:
        ls = ", ".join(sorted((str(f) for f in self.left), key=str))
        rs = ", ".join(sorted((str(f) for f in self.right), key=str))
        return f"{ls} |- {rs}"
