#!/usr/bin/env python3
"""Check the auditable Challenge mirror and selected declaration interfaces.

This source consistency check supplements Lean and Comparator; it does not
establish elaborated type equality or prove the statements.
"""

import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
BEGIN = "-- BEGIN ATTENTION DEFINITIONS\n"
END = "-- END ATTENTION DEFINITIONS\n"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def check(root: Path = ROOT) -> None:
    canonical = (root / "DeepLean/Attention/Definitions.lean").read_text()
    challenge = (root / "Challenge.lean").read_text()
    solution = (root / "Solution.lean").read_text()
    config = json.loads((root / "comparator.json").read_text())
    for name, text, imports in (
        ("Library definitions", canonical, ["public import Mathlib"]),
        ("Challenge", challenge, ["public import Mathlib"]),
        ("Solution", solution, ["public import DeepLean"]),
    ):
        require(text.startswith("module\n"), f"{name} must use the module system")
        require(re.findall(r"^(?:(?:public|private|meta|all)\s+)*import [^\n]+$", text, re.M) == imports,
                f"Unexpected {name} imports or import visibility")
        require(text.count("@[expose] public section\n") == 1,
                f"{name} must expose its public interface")
        require(not re.search(r"^\s*(?:private|protected)\s", text, re.M),
                f"{name} interface must remain public")
    require(challenge.count(BEGIN) == challenge.count(END) == 1,
            "Expected one marked definition block")
    definitions = canonical.split("-/\n", 1)[1].lstrip("\n")
    copied, statements = challenge.split(BEGIN, 1)[1].split(END, 1)
    require(copied == definitions, "Challenge definitions differ from the library")

    def signatures(text: str) -> dict[str, str]:
        # These interfaces use a final ` :=` on the statement's last line.
        # Named arguments inside parentheses do not end with this delimiter.
        matches = re.findall(
            r"^theorem ([A-Za-z_][A-Za-z0-9_']*)\b(.*?) :=(?: by)?\n",
            text, re.M | re.S,
        )
        require(len(matches) == 3, "Expected exactly three certification theorems")
        return {name: " ".join(signature.split()) for name, signature in matches}

    expected = signatures(statements)
    require(list(expected) == ["normalizer_counterexample", "softmax_identifiability",
                               "softmax_generic_identifiability"],
            "Unexpected certification theorem names or order")
    require("Measurable S ∧ ¬ ContinuousAt S 0 ∧" in expected["normalizer_counterexample"],
            "Counterexample must explicitly assert discontinuity at zero")
    require(signatures(solution) == expected, "Challenge/Solution source types differ")
    require(config["theorem_names"] == ["DeepLean.Attention." + name for name in expected],
            "Comparator must select exactly the three declared theorem names")
    require(config["challenge_module"] == "Challenge", "Unexpected challenge module")
    require(config["solution_module"] == "Solution", "Unexpected solution module")
    require(config.get("definition_names", []) == [], "Definition holes are not used")
    require(set(config["permitted_axioms"]) == {"propext", "Quot.sound", "Classical.choice"},
            "Unexpected permitted axiom set")
    require(config["enable_nanoda"] is True, "NanoDa must remain enabled")
    for name, text in (("Challenge", statements), ("Solution", solution)):
        require(text.count("namespace DeepLean.Attention") == 1, f"Unexpected {name} namespace")
        require(text.rstrip().endswith("end DeepLean.Attention"), f"Unclosed {name} namespace")
    require(len(challenge.splitlines()) <= 300 and len(challenge.encode()) <= 32 * 1024,
            "Challenge exceeds Palomar's audit-size warning threshold")
    print("Public module interfaces, Challenge definition mirror, Mathlib-only imports, "
          "explicit discontinuity, three source interfaces, "
          "and Comparator selection agree.")


if __name__ == "__main__":
    try:
        check()
    except (KeyError, ValueError, OSError) as error:
        print(f"Attention interface check failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error
