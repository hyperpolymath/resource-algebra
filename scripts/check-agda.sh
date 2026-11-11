#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Core proofs plus expected rejections.  Pattern: residual-evidence-types.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL="${LC_ALL:-C.UTF-8}"
prover="${AGDA:-agda}"
"$prover" --version
# The canonical theory-proof invocation (standards PROOF-POLICY §2.1,
# 2026-11-01) is --safe --without-K --cubical-compatible. -W error makes any
# warning a failure, except UnsupportedIndexedMatch, which is suppressed.
# --no-libraries keeps the import cone first-party (no standard library);
# --double-check re-checks every term with the core type checker.
flags=(--safe --without-K --cubical-compatible --no-libraries --ignore-interfaces --double-check -W error -W noUnsupportedIndexedMatch -i src)
# PROOF-POLICY §8.4.6: a comment-aware postulate scan of the import cone
# (src/), alongside --safe. scripts/scan-postulates.pl reads each file in
# source order (nested block comments, line comments, strings) and fails on
# a file it cannot read.
# find runs to a file, not a process substitution, so its own failure (a
# directory it cannot read) stops the gate instead of leaving a partial cone.
cone_list="$(mktemp)"
work="$(mktemp -d)"
trap 'rm -f "$cone_list"; rm -rf "$work"' EXIT
find src -name '*.agda' -print0 > "$cone_list" \
  || { echo "ERROR: could not list the import cone (src/)" >&2; exit 1; }
mapfile -d '' cone < "$cone_list"
(( ${#cone[@]} > 0 )) || { echo "ERROR: no Agda sources in the import cone" >&2; exit 1; }
if ! perl scripts/scan-postulates.pl "${cone[@]}"; then
  echo "ERROR: postulate in the import cone (src/), or an unreadable file" >&2
  exit 1
fi
echo "PASS: no postulate in the import cone (src/)"
"$prover" "${flags[@]}" --dependency-graph="$work/All.dot" src/ResourceAlgebra/All.agda
# PROOF-POLICY §8.4.7: the prover's own modules are in the cone. The cone is
# the module set Agda reports for the graded root (All.agda). Each module is
# resolved to src/ or to the library supplied with the prover; a module found
# in neither fails. Pattern: januskey scripts/check-agda.sh.
sed -n 's/.*label="\([^"]*\)".*/\1/p' "$work/All.dot" | LC_ALL=C sort -u > "$work/cone.txt" \
  || { echo "ERROR: could not read the dependency graph Agda wrote" >&2; exit 1; }
agda_prim="$("$prover" --print-agda-dir)/lib/prim"
first_party=0; prover_lib=()
while IFS= read -r name; do
  if [ -f "src/${name//.//}.agda" ]; then first_party=$((first_party + 1)); continue; fi
  candidate="$agda_prim/${name//.//}.agda"
  [ -f "$candidate" ] || { echo "ERROR: cannot resolve module $name of the import cone to a source file" >&2; exit 1; }
  prover_lib+=("$candidate")
done < "$work/cone.txt"
(( first_party > 0 )) || { echo "ERROR: Agda reported no first-party module in the import cone" >&2; exit 1; }
(( ${#prover_lib[@]} > 0 )) || { echo "ERROR: Agda reported no prover-supplied module in the import cone" >&2; exit 1; }
# Modules supplied with the prover are its trusted base. The only postulates
# allowed there are Agda.Primitive's universe-level primitives: exactly Level,
# lzero, lsuc and _⊔_, each bound by its BUILTIN pragma. The check reads the
# declared names and the bindings, not the file name, so a prover pin that
# adds a postulate to Agda.Primitive fails here, and so does a postulate in
# any other prover-supplied module of the cone.
status=0; perl scripts/scan-postulates.pl "${prover_lib[@]}" > "$work/prover.hits" 2> "$work/prover.err" || status=$?
(( status <= 1 )) || { cat "$work/prover.err" >&2; echo "ERROR: could not scan the prover-supplied modules" >&2; exit 1; }
prim="$agda_prim/Agda/Primitive.agda"
if grep -vqF -- "$prim:" "$work/prover.hits"; then
  cat "$work/prover.hits"
  echo "ERROR: a prover-supplied postulate outside Agda.Primitive" >&2; exit 1
fi
# The names the postulate blocks declare: the indented lines after a bare
# `postulate`, up to the next line that is not indented; line comments removed.
declared="$(LC_ALL=C awk '
  { sub(/--.*/, "") }
  /^postulate[ \t]*$/ { inblock = 1; next }
  inblock && /^[ \t]*$/ { next }
  inblock && /^[ \t]/ { split($0, lhs, ":"); n = split(lhs[1], names, /[ \t]+/)
                        for (k = 1; k <= n; k++) if (names[k] != "") print names[k]; next }
  { inblock = 0 }
' "$prim" | LC_ALL=C sort | tr '\n' ' ')"
expected="Level _⊔_ lsuc lzero "
[ "$declared" = "$expected" ] || {
  echo "ERROR: Agda.Primitive postulates '$declared', expected exactly '$expected'" >&2; exit 1; }
# Every postulate hit is one of those block openers, so no postulate hides
# in a shape the name reader above does not read.
blocks="$(LC_ALL=C grep -cE '^postulate[[:space:]]*$' "$prim" || true)"
[ "$(wc -l < "$work/prover.hits" | tr -d ' ')" = "$blocks" ] || {
  cat "$work/prover.hits"
  echo "ERROR: Agda.Primitive has a postulate outside its level blocks" >&2; exit 1; }
mkdir -p _build/check-logs
: > _build/check-logs/trusted-base.txt
for binding in "LEVEL Level" "LEVELZERO lzero" "LEVELSUC lsuc" "LEVELMAX _⊔_"; do
  LC_ALL=C grep -qE -- "^\{-#[[:space:]]+BUILTIN[[:space:]]+${binding% *}[[:space:]]+${binding#* }[[:space:]]+#-\}" "$prim" || {
    echo "ERROR: Agda.Primitive does not bind ${binding#* } with BUILTIN ${binding% *}" >&2; exit 1; }
  echo "agda Agda.Primitive ${binding#* } BUILTIN ${binding% *}" >> _build/check-logs/trusted-base.txt
done
echo "PASS: import cone has $first_party first-party and ${#prover_lib[@]} prover-supplied modules; Agda.Primitive postulates exactly ${expected% }, each bound by its BUILTIN pragma; no other prover-supplied postulate"
# Unit tests (closed computations and small lemmas over the instances).
"$prover" "${flags[@]}" -i tests/unit tests/unit/AllTests.agda
echo "PASS: unit tests (tests/unit/AllTests.agda)"
mkdir -p _build/check-logs
shopt -s nullglob
rejects=(tests/reject/*.agda)
shopt -u nullglob
if (( ${#rejects[@]} == 0 )); then
  echo 'ERROR: no expected-rejection modules found under tests/reject' >&2
  exit 1
fi
for file in "${rejects[@]}"; do
  name="$(basename -- "$file" .agda)"
  # The refusal must carry the message the fixture names: failing at the
  # declaration for some other reason must not pass.
  expect="$(sed -n 's/^-- EXPECT: //p' "$file" | head -1)"
  if [ -z "$expect" ]; then
    echo "ERROR: $name has no '-- EXPECT: <regex>' line" >&2
    exit 1
  fi
  log="_build/check-logs/$name.log"
  # The lines of the fixture's `invalid` definition: from its first clause
  # (the first `invalid` line that is not the type signature) to the last
  # clause or continuation line before the next top-level declaration.
  read -r def_first def_last < <(awk '
    !start { if (/^invalid([[:space:]]|$)/ && !/^invalid[[:space:]]*:/) start = last = NR; next }
    done || !NF || /^--/ { next }
    /^invalid([[:space:]]|$)/ || /^[[:space:]]/ { last = NR; next }
    { done = 1 }
    END { print start + 0, last + 0 }' "$file")
  if (( def_first == 0 )); then
    echo "ERROR: $file has no \`invalid\` definition to reject" >&2
    exit 1
  fi
  if "$prover" "${flags[@]}" -i tests/reject "$file" >"$log" 2>&1; then
    cat "$log"
    echo "ERROR: invalid proof accepted: $name" >&2
    exit 1
  fi
  # Agda stops at its first error, so the first location it reports in this
  # file must lie inside `invalid`.  Any `when checking that` diagnostic used
  # to pass, so an earlier, unrelated type error passed before Agda ever
  # reached the claim the fixture exists to refute.
  err_line="$(grep -oE "/$name\.agda:[0-9]+," "$log" | head -1 | sed -E 's/.*:([0-9]+),$/\1/' || true)"
  if [[ -z "$err_line" ]] ||
     (( err_line < def_first || err_line > def_last )) ||
     ! grep -q 'when checking that' "$log" ||
     grep -Eq 'Not in scope|Failed to find|Unsolved|Parse error' "$log"; then
    cat "$log"
    echo "ERROR: unexpected failure while checking $name" \
         "(first error at line ${err_line:-none}; \`invalid\` spans lines $def_first-$def_last)" >&2
    exit 1
  fi
  if ! grep -Eq -- "$expect" "$log"; then
    cat "$log"
    echo "ERROR: $name was refused, but not with: $expect" >&2
    exit 1
  fi
  echo "PASS: rejected $name at its invalid declaration (line $err_line: $expect)"
done
echo "PASS: core proofs, unit tests and all ${#rejects[@]} expected rejections"
