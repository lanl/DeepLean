#!/usr/bin/env python3
"""Regression checks for the certification source-boundary guard."""

import contextlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "attention_interface", ROOT / "scripts/check-attention-interface.py"
)
INTERFACE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(INTERFACE)


class AttentionInterfaceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for name in ("Challenge.lean", "Solution.lean", "comparator.json",
                     "DeepLean/Attention/Definitions.lean"):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, target)

    def edit(self, name: str, old: str, new: str) -> None:
        path = self.root / name
        text = path.read_text()
        self.assertIn(old, text)
        path.write_text(text.replace(old, new, 1))

    def check(self) -> None:
        with contextlib.redirect_stdout(io.StringIO()):
            INTERFACE.check(self.root)

    def test_current_interface_passes(self) -> None:
        self.check()

    def test_missing_module_header_rejected(self) -> None:
        self.edit("Solution.lean", "module\n", "")
        with self.assertRaisesRegex(ValueError, "module system"):
            self.check()

    def test_private_import_rejected(self) -> None:
        self.edit("Challenge.lean", "public import Mathlib", "import Mathlib")
        with self.assertRaisesRegex(ValueError, "import visibility"):
            self.check()

    def test_non_mathlib_challenge_import_rejected(self) -> None:
        self.edit("Challenge.lean", "public import Mathlib", "public import DeepLean")
        with self.assertRaisesRegex(ValueError, "imports"):
            self.check()

    def test_private_theorem_rejected(self) -> None:
        self.edit("Solution.lean", "theorem normalizer_counterexample", "private theorem normalizer_counterexample")
        with self.assertRaisesRegex(ValueError, "remain public"):
            self.check()

    def test_definition_drift_rejected(self) -> None:
        self.edit("Challenge.lean", "scalarScore (4 * m₂)", "scalarScore (2 * m₂)")
        with self.assertRaisesRegex(ValueError, "definitions differ"):
            self.check()

    def test_shared_omission_of_discontinuity_rejected(self) -> None:
        for name in ("Challenge.lean", "Solution.lean"):
            self.edit(name, "      ¬ ContinuousAt S 0 ∧\n", "")
        with self.assertRaisesRegex(ValueError, "discontinuity"):
            self.check()

    def test_hypothesis_drift_rejected(self) -> None:
        self.edit("Solution.lean", "(ht : 2 ≤ t)", "(ht : 3 ≤ t)")
        with self.assertRaisesRegex(ValueError, "source types differ"):
            self.check()

    def test_wrong_selected_namespace_rejected(self) -> None:
        self.edit("comparator.json", "DeepLean.Attention.normalizer_counterexample",
                  "Other.Attention.normalizer_counterexample")
        with self.assertRaisesRegex(ValueError, "three declared theorem names"):
            self.check()

    def test_extra_axiom_rejected(self) -> None:
        path = self.root / "comparator.json"
        config = json.loads(path.read_text())
        config["permitted_axioms"].append("sorryAx")
        path.write_text(json.dumps(config))
        with self.assertRaisesRegex(ValueError, "axiom set"):
            self.check()

    def test_disabled_nanoda_rejected(self) -> None:
        path = self.root / "comparator.json"
        config = json.loads(path.read_text())
        config["enable_nanoda"] = False
        path.write_text(json.dumps(config))
        with self.assertRaisesRegex(ValueError, "NanoDa"):
            self.check()


if __name__ == "__main__":
    unittest.main()
