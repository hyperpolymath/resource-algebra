#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
# CI/gate must be a verdict, not a rubber stamp. Positive control: all green
# passes. Negative cases: failure, cancelled, skipped, empty and malformed
# input each fail. Drift: the gate's `needs:` must list every other job in
# proofs.yml. Exemption: planting runtime code under src/ makes the declared
# coverage exemption fail.
set -uo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."
fail=0
chk() { # chk NAME WANT-RC JSON
  NEEDS_JSON="$3" bash scripts/ci-gate.sh >/dev/null 2>&1; rc=$?
  if [ "$rc" -eq "$2" ]; then echo "ok   $1"; else echo "FAIL $1: rc=$rc want $2"; fail=1; fi
}
chk "all success passes"      0 '{"a":{"result":"success"},"b":{"result":"success"}}'
chk "one failure fails"       1 '{"a":{"result":"success"},"b":{"result":"failure"}}'
chk "one cancelled fails"     1 '{"a":{"result":"success"},"b":{"result":"cancelled"}}'
chk "one skipped fails"       1 '{"a":{"result":"success"},"b":{"result":"skipped"}}'
chk "empty needs fails"       1 '{}'
chk "malformed fails"         1 'not json'

wf=.github/workflows/proofs.yml
jobs="$(sed -n '/^jobs:/,$ s/^  \([a-z0-9-]*\):$/\1/p' "$wf" | grep -vx 'gate' | sort | tr '\n' ' ')"
needs="$(sed -n 's/^    needs: \[\(.*\)\]$/\1/p' "$wf" | tr -d ',' | tr ' ' '\n' | sort | tr '\n' ' ')"
if [ "$jobs" = "$needs" ]; then echo "ok   gate needs every other job ($needs)"; else echo "FAIL needs drift: jobs=[$jobs] needs=[$needs]"; fail=1; fi
grep -q '^    name: CI/gate$' "$wf" && echo "ok   job name is exactly CI/gate" || { echo "FAIL job name"; fail=1; }

work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
git ls-files -z | xargs -0 -I{} cp --parents {} "$work" 2>/dev/null
git -C "$work" init -q && git -C "$work" add -A >/dev/null 2>&1
bash scripts/check-coverage-exemption.sh "$work" >/dev/null 2>&1 && echo "ok   exemption holds on the tree" || { echo "FAIL exemption on clean tree"; fail=1; }
mkdir -p "$work/src/ResourceAlgebra" && echo 'fn main(){}' > "$work/src/ResourceAlgebra/planted.rs" && git -C "$work" add -A
bash scripts/check-coverage-exemption.sh "$work" >/dev/null 2>&1 && { echo "FAIL planted runtime code accepted"; fail=1; } || echo "ok   planted runtime code rejected"
exit $fail
