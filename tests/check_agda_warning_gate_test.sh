#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
# The Agda gate must fail on any warning, UnsupportedIndexedMatch included:
# the order and the injectivity lemmas were restated so the cone raises
# none, and nothing is suppressed. The test reads the flags from
# scripts/check-agda.sh, as proofs.yml does, and checks
# tests/warning/IndexedMatch.agda, whose one clause needs injectivity of
# suc. Agda 2.6.3 does not print the warning's name when it is an error, so
# the test matches the reason Agda gives, which every version prints.
# Control: without -W error the fixture checks, so the gate's refusal
# comes from the warning alone. Case: with the gate's flags Agda must stop,
# naming UnsupportedIndexedMatch.
set -uo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL="${LC_ALL:-C.UTF-8}"
prover="${AGDA:-agda}"
command -v "$prover" >/dev/null || { echo "FAIL: no Agda on PATH" >&2; exit 1; }
line=$(sed -n 's/^flags=(\(.*\))$/\1/p' scripts/check-agda.sh)
[[ -n "$line" ]] || { echo "FAIL: no flags=(...) line in scripts/check-agda.sh" >&2; exit 1; }
read -r -a gate <<<"$line"
fixture=tests/warning/IndexedMatch.agda
fail=0

# Control: the gate's flags with every -W pair removed.
loose=()
for ((i = 0; i < ${#gate[@]}; i++)); do
  if [[ "${gate[i]}" == -W ]]; then ((i++)); continue; fi
  loose+=("${gate[i]}")
done
if out=$("$prover" "${loose[@]}" -i tests/warning "$fixture" 2>&1); then
  echo "PASS: control: the fixture checks once warnings are not errors"
else
  printf 'FAIL: control: the fixture does not check even without -W error\n%s\n' "$(tail -5 <<<"$out")" >&2; fail=1
fi

# Case: the gate's own flags.
out=$("$prover" "${gate[@]}" -i tests/warning "$fixture" 2>&1); rc=$?
if [[ $rc -eq 0 ]]; then
  echo "FAIL: the gate's flags accepted an indexed match: UnsupportedIndexedMatch is not an error" >&2; fail=1
elif ! grep -q 'injectivity of the data constructor suc' <<<"$out"; then
  printf 'FAIL: Agda stopped for another reason (exit %s)\n%s\n' "$rc" "$(tail -5 <<<"$out")" >&2; fail=1
else
  echo "PASS: the gate's flags refuse an indexed match (exit $rc): UnsupportedIndexedMatch"
fi
exit "$fail"
