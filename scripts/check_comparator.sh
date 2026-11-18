#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
version="$(cat "$repo_root/lean-toolchain")"
version="${version##*:}"
export COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT:-$repo_root/.tools/lean4export-$version/.lake/build/bin/lean4export}"
comparator_bin="${COMPARATOR_BIN:-$(command -v comparator || true)}"

if [[ ! -x "$COMPARATOR_LEAN4EXPORT" ]]; then
  echo "Build the matching exporter first: scripts/setup_lean4export.sh" >&2
  exit 2
fi
if [[ -z "$comparator_bin" || ! -x "$comparator_bin" ]]; then
  echo "Comparator binary not found; set COMPARATOR_BIN or add comparator to PATH" >&2
  exit 2
fi
if [[ -z "${COMPARATOR_LANDRUN:-}" ]]; then
  export COMPARATOR_LANDRUN="$(command -v landrun || true)"
fi
if [[ -z "$COMPARATOR_LANDRUN" || ! -x "$COMPARATOR_LANDRUN" ]]; then
  echo "landrun not found; set COMPARATOR_LANDRUN to its executable path" >&2
  exit 2
fi
if [[ "$(uname -s)" != Linux && "$COMPARATOR_LANDRUN" != *fake-landrun.sh ]]; then
  echo "landrun's sandbox requires Linux; on macOS use Comparator's fake-landrun.sh for development checks" >&2
  exit 2
fi
if [[ "$COMPARATOR_LANDRUN" == *fake-landrun.sh ]]; then
  echo "Development check only: fake-landrun does not sandbox the solution" >&2
fi

run_day() {
  local number="$1" formatted
  printf -v formatted '%02d' "$number"
  echo "Checking problem $formatted"
  (cd "$repo_root" && lake env "$comparator_bin" "comparator/Problem$formatted.json")
}

if [[ $# -ne 1 ]]; then
  echo "Usage: scripts/check_comparator.sh <1..24|all>" >&2
  exit 2
fi
if [[ "$1" == all ]]; then
  failed=0
  for number in {1..24}; do
    run_day "$number" || failed=1
  done
  exit "$failed"
fi
if ! [[ "$1" =~ ^(0?[1-9]|1[0-9]|2[0-4])$ ]]; then
  echo "Problem must be 1 through 24" >&2
  exit 2
fi
run_day "$((10#$1))"
