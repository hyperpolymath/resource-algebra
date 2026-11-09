#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# scripts/scan-postulates.pl reads Agda in source order: a comment cannot
# hide code, a string cannot fake a comment, and an unreadable input fails.
set -uo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
scan=scripts/scan-postulates.pl
d=$(mktemp -d); trap 'rm -rf "$d"' EXIT
fail=0
check() { # check WANT-EXIT NAME CONTENT
  printf '%b' "$3" > "$d/$2"
  perl "$scan" "$d/$2" >/dev/null 2>&1; got=$?
  if [ "$got" -eq "$1" ]; then echo "PASS: $2 -> $got"; else echo "FAIL: $2 -> $got, want $1"; fail=1; fi
}
check 0 clean.agda        'module A where\nx = 1\n'
check 1 real.agda         'module B where\npostulate p : Set\n'
check 1 linehide.agda     'module C where\n-- {-\npostulate p : Set\n-- -}\n'
check 0 nested.agda       'module D where\n{- {- -} postulate -}\n'
check 0 string.agda       'module E where\ns = "postulate -} {-"\n'
check 0 comment.agda      'module F where\n{-# OPTIONS --safe #-}\n-- postulate\n'
check 0 charlit.agda      "module G where\nc = '\"'\n-- \"\nx = 1\n"
mkdir -p "$d/with space"
check 1 'with space/s.agda' 'postulate q : Set\n'
perl "$scan" "$d/missing.agda" >/dev/null 2>&1; got=$?
if [ "$got" -eq 2 ]; then echo "PASS: unreadable file -> 2"; else echo "FAIL: unreadable file -> $got, want 2"; fail=1; fi
perl "$scan" >/dev/null 2>&1; got=$?
if [ "$got" -eq 2 ]; then echo "PASS: no files -> 2"; else echo "FAIL: no files -> $got, want 2"; fail=1; fi
exit $fail
