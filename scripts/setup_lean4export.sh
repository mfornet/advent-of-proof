#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
toolchain="$(cat "$repo_root/lean-toolchain")"
version="${toolchain##*:}"
case "$version" in
  v[0-9]*) ;;
  *) echo "Unexpected Lean toolchain: $toolchain" >&2; exit 1 ;;
esac

exporter_dir="$repo_root/.tools/lean4export-$version"
if [[ ! -f "$exporter_dir/lakefile.toml" ]]; then
  mkdir -p "$repo_root/.tools"
  if [[ -n "${LEAN4EXPORT_SOURCE:-}" ]]; then
    mkdir "$exporter_dir"
    git -C "$LEAN4EXPORT_SOURCE" archive "$version" | tar -x -C "$exporter_dir"
  else
    git clone --depth 1 --branch "$version" \
      https://github.com/leanprover/lean4export.git "$exporter_dir"
  fi
fi

if [[ "$(cat "$exporter_dir/lean-toolchain")" != "$toolchain" ]]; then
  echo "Exporter toolchain does not match $toolchain" >&2
  exit 1
fi

(cd "$exporter_dir" && lake build lean4export)
echo "Exporter: $exporter_dir/.lake/build/bin/lean4export"
