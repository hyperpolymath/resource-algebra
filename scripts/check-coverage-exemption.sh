#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# check-coverage-exemption.sh — verify the DECLARED code-coverage exemption.
#
# .machine_readable/coverage-exemption.toml declares that this repository has
# no measurable runtime code (it is prover-only: Agda, with Rocq and Lean
# rechecks). A declaration nobody checks is a silent skip, so this script
# makes it falsifiable: it fails if a tracked file under a declared root has a
# runtime-code extension and is not on the declared, shrink-only pending list.
#
# Usage: check-coverage-exemption.sh [REPO_ROOT]
# Exit: 0 declaration holds; 1 it is false or malformed; 2 setup error.
set -euo pipefail
root="${1:-.}"
decl="$root/.machine_readable/coverage-exemption.toml"
[ -f "$decl" ] || { echo "check-coverage-exemption: $decl missing" >&2; exit 2; }
git -C "$root" rev-parse --git-dir >/dev/null 2>&1 || { echo "check-coverage-exemption: $root is not a git tree" >&2; exit 2; }

# Minimal TOML reader: `key = true|false` and `key = ["a", "b"]` on one line.
scalar() { sed -n "s/^$1[[:space:]]*=[[:space:]]*\(.*[^[:space:]]\)[[:space:]]*$/\1/p" "$decl" | head -1; }
list()   { scalar "$1" | tr -d '[]"' | tr ',' '\n' | sed 's/^[[:space:]]*//;s/[[:space:]]*$//' | sed '/^$/d'; }

[ "$(scalar measurable-runtime-code)" = "false" ] || {
  echo "::error::coverage-exemption: measurable-runtime-code is not false; this exemption does not apply" >&2; exit 1; }
mapfile -t roots   < <(list product-roots)
mapfile -t exts    < <(list runtime-extensions)
mapfile -t pending < <(list pending-removal)
[ "${#roots[@]}" -gt 0 ] && [ "${#exts[@]}" -gt 0 ] || {
  echo "::error::coverage-exemption: product-roots and runtime-extensions must be non-empty" >&2; exit 1; }

fail=0; seen=0
while IFS= read -r f; do
  seen=$((seen+1))
  ext="${f##*.}"
  hit=0; for e in "${exts[@]}"; do [ "$ext" = "$e" ] && hit=1; done
  [ "$hit" -eq 1 ] || continue
  ok=0; for p in "${pending[@]}"; do case "$f" in "$p"/*|"$p") ok=1;; esac; done
  if [ "$ok" -eq 1 ]; then echo "pending-removal (declared): $f"; continue; fi
  echo "::error::coverage-exemption: runtime code under a declared root: $f" >&2; fail=1
done < <(git -C "$root" ls-files -- "${roots[@]}")
[ "$seen" -gt 0 ] || { echo "::error::coverage-exemption: no tracked files under ${roots[*]} (denominator = 0)" >&2; exit 1; }
[ "$fail" -eq 0 ] || exit 1
echo "coverage-exemption: holds ($seen tracked file(s) under ${roots[*]}, none runtime code outside the declared pending list)"
