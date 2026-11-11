#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
# scripts/check-agda.sh must stop when a module supplied with the prover
# declares a postulate outside the named trusted base (PROOF-POLICY §8.4.7):
# Level, lzero, lsuc and _⊔_ in Agda.Primitive, each bound by its BUILTIN
# pragma. A stub prover answers --print-agda-dir with a copy of Agda's own
# library that has one planted change, and passes every other call to the
# real prover. The proofs still check, so only the trusted-base check can
# stop the gate. Each case must fail with the message it names.
set -uo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
real="$(command -v "${AGDA:-agda}")" || { echo "FAIL: no Agda on PATH" >&2; exit 1; }
real_dir="$("$real" --print-agda-dir)"
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
fail=0
run_case() { # run_case NAME WANT-MESSAGE ; the planted library is $work/$1
  local name="$1" want="$2" out rc
  cat > "$work/$name.agda-stub" <<STUB
#!/usr/bin/env bash
if [ "\${1:-}" = --print-agda-dir ]; then echo "$work/$name"; exit 0; fi
exec "$real" "\$@"
STUB
  chmod +x "$work/$name.agda-stub"
  out=$(AGDA="$work/$name.agda-stub" bash scripts/check-agda.sh 2>&1); rc=$?
  if [[ $rc -eq 0 ]] || grep -q 'PASS: import cone has' <<<"$out"; then
    printf 'FAIL: %s: gate passed the trusted-base check (exit %s)\n' "$name" "$rc" >&2; fail=1
  elif ! grep -qF -- "$want" <<<"$out"; then
    printf 'FAIL: %s: gate stopped for another reason (exit %s)\n%s\n' "$name" "$rc" "$(tail -5 <<<"$out")" >&2; fail=1
  else
    echo "PASS: $name stops the gate (exit $rc): $want"
  fi
}
plant() { mkdir -p "$work/$1/lib" && cp -r "$real_dir/lib/prim" "$work/$1/lib/prim"; }

plant other-module
printf '\npostulate\n  planted : Set\n' >> "$work/other-module/lib/prim/Agda/Builtin/Unit.agda"
run_case other-module 'a prover-supplied postulate outside Agda.Primitive'

plant extra-name
printf '\npostulate\n  planted : Set\n' >> "$work/extra-name/lib/prim/Agda/Primitive.agda"
run_case extra-name "expected exactly 'Level _⊔_ lsuc lzero '"

plant inline
printf '\npostulate planted : Set\n' >> "$work/inline/lib/prim/Agda/Primitive.agda"
run_case inline 'Agda.Primitive has a postulate outside its level blocks'

plant unbound
sed -i 's/^{-# BUILTIN LEVELMAX .*$//' "$work/unbound/lib/prim/Agda/Primitive.agda"
run_case unbound 'Agda.Primitive does not bind _⊔_ with BUILTIN LEVELMAX'

# The unchanged library must pass, so a failure above is the planted change.
plant unchanged
cat > "$work/unchanged.agda-stub" <<STUB
#!/usr/bin/env bash
if [ "\${1:-}" = --print-agda-dir ]; then echo "$work/unchanged"; exit 0; fi
exec "$real" "\$@"
STUB
chmod +x "$work/unchanged.agda-stub"
if out=$(AGDA="$work/unchanged.agda-stub" bash scripts/check-agda.sh 2>&1) && grep -q 'PASS: import cone has' <<<"$out"; then
  echo "PASS: the unchanged library passes the trusted-base check"
else
  printf 'FAIL: the unchanged library did not pass\n%s\n' "$(tail -5 <<<"$out")" >&2; fail=1
fi
exit $fail
