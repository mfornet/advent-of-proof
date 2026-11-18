#!/usr/bin/env python3
"""Build Comparator challenges from the archived templates for Lean 4.30."""

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TEMPLATES = ROOT / "templates"
CHALLENGES = ROOT / "Challenge"
CONFIGS = ROOT / "comparator"

TARGETS = {
    1: ([], ["goal"]),
    2: (["strip"], []),
    3: (["subseq_refl", "subseq_trans", "subseq_len", "subseq_antisym"], []),
    4: (["goal"], []),
    5: ([], ["goal"]),
    6: (["compile_correct"], []),
    7: (["goal"], []),
    8: (["prf₁", "prf₂"], []),
    9: ([], ["goal"]),
    10: (["prop₁", "prop₂", "uniqueness"], ["co"]),
    11: (["ident_red", "const_sop_red", "const_kop_red", "app_app_red", "beta"],
         ["ident", "const_sop", "const_kop", "app_app", "lambda"]),
    12: (["handshaking"], []),
    13: (["goal₁", "goal₂"], []),
    14: (["proof"], []),
    15: (["composition", "assoc", "identity_l", "identity_r", "inverse_l", "inverse_r"],
         ["comp", "ι", "inv"]),
    16: (["goal"], []),
    17: (["goal"], []),
    18: (["compose_correct", "compose_assoc", "merge_pushout"], []),
    19: (["nullable_correct₁", "nullable_correct₂", "step_correct₁", "step_correct₂",
          "steps_correct₁", "steps_correct₂", "check_lemma₁", "check_lemma₂"], []),
    20: (["identᵣ", "assoc"], []),
    21: (["lem₁", "lem₂", "lem₃"], []),
    22: (["reflexive", "symmetric", "transitive", "bisim_is_bisim", "hml_bisim"], []),
    23: (["goal"], []),
    24: (["toList_injective"], []),
}


def replace_once(source: str, old: str, new: str) -> str:
    if source.count(old) != 1:
        raise ValueError(f"Expected exactly one occurrence of {old!r}")
    return source.replace(old, new)


def make_compatible(day: int, source: str) -> str:
    if day == 4:
        source = replace_once(source, "import Std.Data.Int.Lemmas", "import Mathlib.Tactic")
    if day in (8, 13, 15, 18):
        source = re.sub(r"(?m)^import Mathlib\.Data\.Vector\s*$",
                        "import Mathlib.Data.Vector.Basic", source)
        source = re.sub(r"(?<!\.)\bVector\b", "List.Vector", source)
        source = re.sub(r"(?m)^import Mathlib\.Data\.Vector\.Basic[ \t]*\n"
                        r"(?=import Mathlib\.Data\.Vector\.Basic)", "", source)
    if day == 12:
        source = replace_once(source, "import Std.Data.Fin.Basic\n", "")
        source = replace_once(source, "import Mathlib.Data.List.Range \n",
                              "import Mathlib.Data.List.Range\n"
                              "import Mathlib.Algebra.BigOperators.Group.List.Basic\n"
                              "import Mathlib.Algebra.BigOperators.Fin\n")
        source = replace_once(source, "Nat.sum (List.map g.degree g.V)",
                              "(List.map g.degree g.V).sum")
    if day == 13:
        source = replace_once(source, "import Mathlib.Logic.Equiv.Fin\n",
                              "import Mathlib.Logic.Equiv.Fin.Basic\n")
    if day == 17:
        source = source.replace(".bind", ".flatMap")
    if day == 21:
        source = replace_once(source, "import Std.Data.List.Basic",
                              "import Mathlib.Data.List.Basic")
        source = replace_once(source, "Δ.removeNth", "Δ.eraseIdx")
    if day == 23:
        source = replace_once(source, "σ.A.get! σ.i", "σ.A.getD σ.i 0")
    if day in (5, 9):
        if len(re.findall(r"(?m)^theorem goal :", source)) != 1:
            raise ValueError(f"Day {day}: expected one theorem goal declaration")
        source = re.sub(r"(?m)^theorem goal :", "def goal :", source, count=1)
    return source


def main() -> None:
    CHALLENGES.mkdir(exist_ok=True)
    CONFIGS.mkdir(exist_ok=True)
    for day in range(1, 25):
        original = (TEMPLATES / f"Problem{day:02d}.lean").read_text()
        namespace = f"Problem{day}"
        theorem_names, definition_names = TARGETS[day]
        for name in theorem_names + definition_names:
            if not re.search(r"(?m)^\s*(?:theorem|lemma|def|noncomputable def)\s+" +
                             re.escape(name) + r"\b", original):
                raise ValueError(f"Day {day}: target {name!r} is absent from original template")

        adapted = make_compatible(day, original).rstrip() + "\n"
        header = (f"-- Trusted Comparator challenge for Advent of Proof 2023, Q{day}.\n"
                  f"-- Adapted from templates/Problem{day:02d}.lean for Lean 4.30.\n")
        imports = re.match(r"(?:import [^\n]+\n)*", adapted).group()
        body = adapted[len(imports):].lstrip("\n")
        challenge = (header + imports + "\n" + f"namespace {namespace}\n\n" + body +
                     f"\nend {namespace}\n")
        # Q19's recursive definitions generate module-specific hygiene names.
        # Its fixed definitions live in shared Spec.Problem19, and its challenge
        # declarations are maintained in Challenge/Problem19.lean.
        if day != 19:
            (CHALLENGES / f"Problem{day:02d}.lean").write_text(challenge)

        axioms = re.findall(r"(?m)^axiom\s+([^\s:]+)", original)
        config = {
            "challenge_module": f"Challenge.Problem{day:02d}",
            "solution_module": f"Solution.Problem{day:02d}",
            "theorem_names": [f"{namespace}.{name}" for name in theorem_names],
            "definition_names": [f"{namespace}.{name}" for name in definition_names],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"] +
                                [f"{namespace}.{name}" for name in axioms],
            "enable_nanoda": False,
        }
        (CONFIGS / f"Problem{day:02d}.json").write_text(
            json.dumps(config, ensure_ascii=False, indent=2) + "\n")


if __name__ == "__main__":
    main()
