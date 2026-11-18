# Advent of Proof 2023 with Comparator

This repository contains all 24 original Lean challenge templates from
[Advent of Proof 2023](https://typesig.pl/2023/11/30/advent-of-proof.html), plus
a [Comparator](https://github.com/leanprover/comparator) project for checking
solutions against them.

## Layout

| Path | Purpose |
| --- | --- |
| `templates/ProblemXX.lean` | Original downloaded templates, saved unchanged. |
| `templates/sources.json` | Pinned source URL and title for each day. |
| `Challenge/ProblemXX.lean` | Trusted challenge declarations adapted to this project's Lean version. |
| `Solution/ProblemXX.lean` | Proof attempts, moved from the old `AdventOfProof/` directory. |
| `comparator/ProblemXX.json` | Comparator configuration for each day's original targets. |
| `Spec/Problem19.lean` | Fixed Q19 definitions shared by both modules so Lean generates identical helper declarations. |

The project uses Lean 4.30.0 and Mathlib v4.30.0. Some 2023 imports and APIs no
longer compile, so the `Challenge` modules make minimal compatibility changes.
For example, Q5 and Q9 use `def` for their `Type` valued goals, and Q19 shares
its fixed recursive definitions through `Spec`. The raw files in `templates/`
preserve the original wording and syntax.

## Build and check a problem

The `comparator` binary must be installed or supplied with `COMPARATOR_BIN`.
Build a matching `lean4export` once:

```sh
scripts/setup_lean4export.sh
```

`setup_lean4export.sh` downloads the exporter at the repository's Lean version
and builds it under ignored `.tools/`. If you already have a local checkout of
`leanprover/lean4export`, set `LEAN4EXPORT_SOURCE` to that directory to build
from its matching tag without downloading it again.
For ordinary development, `lake build Challenge Solution` compiles the whole
project. If you plan to rely on Comparator's safe verification guarantee, use
a fresh trusted checkout and run Comparator before compiling solution files
outside its sandbox.

On Linux with a working `landrun`, check one day or all days:

```sh
scripts/check_comparator.sh 1
scripts/check_comparator.sh all
```

For Comparator's **safe verification guarantee**, invoke the script with the
[Linux `systemd-run` isolation](https://github.com/leanprover/comparator#comparator)
specified by Comparator:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$(pwd)" \
  -- bash -c 'scripts/check_comparator.sh 1'
```

The wrapper supplies the correct exporter, config, and `landrun` paths; it
does not add that outer isolation itself.
Review `Challenge/`, `Spec/`, `comparator/`, and `lakefile.toml` as trusted
inputs before using the guarantee. Comparator also requires human review of
definition holes, whose mathematical intent cannot be inferred from their types.

On macOS, `landrun` cannot apply its Linux Landlock sandbox. To run a local
development check, explicitly use Comparator's `fake-landrun.sh`:

```sh
COMPARATOR_LANDRUN=/path/to/comparator/scripts/fake-landrun.sh scripts/check_comparator.sh 1
```

This exercises Comparator's matching and kernel checks but runs the solution
without the sandbox, so it does not provide the safe verification guarantee.

The current solutions pass Comparator on days 1–14, 16, 19, 23, and 24. Days
15, 17, 18, 20, 21, and 22 still contain `sorry` and correctly fail its axiom
check. `scripts/check_comparator.sh all` exits nonzero until those proofs are
finished.

To refresh the templates from their pinned URLs or regenerate the challenge
modules and configs:

```sh
python3 scripts/download_templates.py
python3 scripts/generate_comparator_setup.py
```

Q19's challenge is maintained separately because its fixed recursive
definitions must stay in `Spec/Problem19.lean`.
