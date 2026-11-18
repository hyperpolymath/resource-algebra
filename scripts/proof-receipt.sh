#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# proof-receipt.sh: the proof receipt of this repository,
# verification/receipts/resource-algebra-proofs_praxis.deed (PROOF-POLICY
# §8.5.1, profile proof-receipt), written and checked by the estate's shared
# generator (standards scripts/proof-receipt.sh).  This file holds only what
# is resource-algebra's own: the claim list, the run ledger, and the hooks
# that name each leg's invocation and input set.  The generator, the reader,
# the reference digest and the §8.5.3 git checker are fetched below at one
# standards commit, each checked against its sha256.
#
#   --write   write the receipt from the ledger and git
#   --check   regenerate it and refuse any difference, run the §8.5.3 git
#             checks, check that each current receipt still describes the
#             tree, and run the pinned reader with its negative control
#   --run-row PROVER --run URL --commit SHA --checker TEXT --reported TEXT
#             --axioms none [--image NAME@sha256:…]
#             print the ledger row of a run that just passed
#
# What is typed and what is derived.  The claim list and the run ledger are
# typed here; each ledger row is printed by --run-row from the proofs.yml run
# it names, and its checker and reported text are copied from that run's
# log.  Every digest is a git fact that the generator rechecks against the
# tree.  The grade is never typed: the generator derives it and the pinned
# reader derives it again, refusing a receipt that overstates it.
#
# Needs: git, sha256sum, curl, bun.
# The receipt_* hooks below are called by the sourced generator, not here.
# shellcheck disable=SC2317
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL=C.UTF-8

# ── The pinned standard ───────────────────────────────────────────────────────
RECEIPT_STANDARDS_COMMIT=f4e8304465ea39433dc926687251d5aa91787600
RECEIPT_STD=_build/standards
standards_raw="https://raw.githubusercontent.com/metadatastician/standards/$RECEIPT_STANDARDS_COMMIT"
pinned_files=(
  "scripts/proof-receipt.sh:b7e294e031fa3b17511746537f3dbde1d40f08f2188e7b5f8cd9f0265e5573d7"
  "1-formats/deed/tools/deed_lint.js:de5b38d7752625ec665329e45b6d6bb244589b4e098dc2e63371088cd660678c"
  "scripts/proof-inputs-sha256.sh:dfc6dde01a3a79df638eebe4cad0eae584d8f17280077e149174c0667e9508f4"
  "scripts/check-proof-receipt.sh:f2375747238464535d1b4a61f658f07cb2f8504c69bfb1812311c79429a4e23e"
)
fetch_standard() {
  local pair rel sha f
  for pair in "${pinned_files[@]}"; do
    rel="${pair%%:*}"; sha="${pair#*:}"; f="$RECEIPT_STD/$rel"
    if [ ! -f "$f" ] || ! printf '%s  %s\n' "$sha" "$f" | sha256sum -c --quiet - 2>/dev/null; then
      mkdir -p "$(dirname "$f")"
      curl --proto '=https' --tlsv1.2 -sSfL -o "$f" "$standards_raw/$rel"
    fi
    printf '%s  %s\n' "$sha" "$f" | sha256sum -c --quiet - \
      || { printf 'ERROR: %s does not match its pinned sha256\n' "$f" >&2; exit 1; }
  done
}
fetch_standard

RECEIPT_OUT=verification/receipts/resource-algebra-proofs_praxis.deed
RECEIPT_REPOSITORY=hyperpolymath/resource-algebra
RECEIPT_DEFAULT_BRANCH=main
RECEIPT_CANONICAL_NAME=resource-algebra-proof-receipt
RECEIPT_SCRIPT=scripts/proof-receipt.sh
# The estate chora's id, as resource-algebra_chora.deed has it (owner ruling Q2).
RECEIPT_BEHOLDING_CHORA='#u8"chora:estate/github.com/hyperpolymath"'
status=docs/status/PROOF-STATUS.adoc
bridge_repo=hyperpolymath/tropical-types
bridge_dir=_build/dependencies/tropical-types
bridge_file=TropicalSessionTypes.lean
# The generator needs the import's clone directory to exist; the commit
# itself is fetched on demand by receipt_ensure_import below.
[ -d "$bridge_dir/.git" ] || git init -q "$bridge_dir"

# ── The claim list ────────────────────────────────────────────────────────────
# The theory rows of docs/status/PROOF-STATUS.adoc: id | §5 token of the Agda
# proof | kind | Rocq route | Rocq §2.2 state | Lean route | Lean state |
# reasons.  Every row but M-2 is PROVEN in Agda and re-proved by hand in Rocq
# and in Lean with its statement reconciled.  M-2 (MaxPlus agrees with
# tropical-types' Tropical semiring) is a Lean bridge only: its statement
# names a Lean-only object, so it has no Agda proof and no Rocq leg, and its
# Lean leg is checked but has no Agda statement to be reconciled with.
receipt_claims() {
  local id
  for id in C-1 C-2 C-3 C-4a C-4b L-1 M-1; do
    printf '%s|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||\n' "$id"
  done
  printf '%s\n' "M-2|open|theorem|unavailable||re-proved|LEAN-CHECKED|the statement names tropical-types' Lean instance, which Rocq cannot import|"
  for id in H-1 H-3 N-1 Q-1 Q-2 Q-3 Q-4 E-1 E-2 E-3 F-1 F-2 F-3 F-4 F-5 F-6 F-7 F-8 F-9 F-10 S-1 S-2 S-3 S-4; do
    printf '%s|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||\n' "$id"
  done
}

# ── The run ledger ────────────────────────────────────────────────────────────
# prover | run | commit | checker | invocation | inputs sha256 | what the run
# reported | state | reason | axioms | imports | trusted base | image.
# One proofs.yml run on main checks all three legs; each row names its job.
# Every gate fails on any axiom (check-agda.sh: --safe and the postulate
# scan; the Rocq job: every Print Assumptions closed; the Lean job and the
# bridge check: every #print axioms empty), so no row lists one.
# Only the Rocq job runs in an image that ships its checker, pinned by
# digest, so only its row names one.  The Agda and Lean jobs run in base
# images pinned by digest and install the checker at run time, which the
# owner ruled on 2026-11-18 is not isolation (docs/status/PROOF-NEEDS.adoc
# PN-7): their rows name no image, and no row can reach PWG-1 until they
# run in prover images.  The Lean row is superseded: the leg and the bridge
# moved under lake, and the first run on main under lake replaces it.
# Earlier runs are listed, superseded, in docs/status/PROOF-STATUS.adoc.
receipt_runs() {
  local u=https://github.com/hyperpolymath/resource-algebra/actions/runs/44209774341/job
  local c=15fa113c7427e2de009eade9148295d08c046b33
  # The Lean invocation of that run, before the legs moved under lake.
  local lean_direct='lean ResourceAlgebra.lean in verification/proofs/lean4, core only; then bash scripts/check-lean-bridge.sh (lean -o on TropicalSessionTypes.lean and ResourceAlgebra.lean, then lean TropicalBridge.lean with LEAN_PATH)'
  cat <<ROWS
agda|$u/134484857967|$c|Agda version 2.6.4.3 (Debian trixie agda-bin=2.6.4.3-1+b2, container debian:trixie-slim, not pinned by digest)|$(receipt_invocation agda)|6d3250447bd3271db46ebac1e48005a6988baf87b6b923ecd3914fbe1b74ae9d|PASS: core proofs, unit tests and all 13 expected rejections|current||||0c1f64c3c7f0a26cbc92595168858485a9883f6196d287497dcc805faf5c58eb
rocq|$u/134484858135|$c|Rocq 9.3.0, then rocqchk|$(receipt_invocation rocq)|b52b1348c6cace05db2ac026d1137a1a3027b14ec84e9fb599259c3693c8b1b7|RESULT: PASS -- gated modules compile; the Assumptions step then passed, which fails unless all 75 printed theorems are closed under the global context and rocqchk accepts the compiled file|current|||||rocq/rocq-prover:9.3.0@sha256:97a68f230e785726c3bab4ba17e1d416fdd630de4af4548eb49b08712f29af93
lean|$u/134484858201|$c|Lean 4.35.0 (release archive, sha256 7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d, on the hosted runner, no image)|$lean_direct|015e62121942646e938318c4015212bb32434493c238e3cef7168858c68d9cb6|RESULT: PASS -- gated modules compile; the Axioms step then passed, which fails unless all 84 printed theorems depend on no axiom; PASS: M-2 bridge to hyperpolymath/tropical-types@f2e465c966d14d4986dfc492875cc54653d9751e; 6 of 6 printed theorems depend on no axiom|superseded|its inputs and its checker changed in hyperpolymath/resource-algebra#53: the leg and the M-2 bridge now build under lake (scripts/check-lean-leg.sh, scripts/check-lean-bridge.sh, two Lake packages), and this run called lean directly, which the owner ruled on 2026-11-17 does not qualify (PROOF-POLICY §8.2). To be replaced by the first run on main of the legs under lake|
ROWS
}

receipt_echoes() { :; }
receipt_header() {
  cat <<'EOF'
;; SPDX-License-Identifier: MPL-2.0
;; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
;;
;; The proof receipt of resource-algebra (PROOF-POLICY §8.5.1, profile
;; proof-receipt).
;; GENERATED by scripts/proof-receipt.sh with the shared standards generator:
;; regenerate with --write, check with --check.  Each (receipt …) is a row of
;; the run ledger in that script; every digest is computed from git objects.
;; Every :pwg is derived, and the pinned reader refuses one its legs and
;; receipts do not support.  The rows and their statement correspondence are
;; in docs/status/PROOF-STATUS.adoc.
;; Only the Rocq receipts name an :image (pinned by digest), so no row is
;; PWG-1 (§8.2).  The Lean leg and the M-2 bridge moved under lake, so the
;; Lean run recorded here is superseded and the Lean legs have no current
;; receipt until the first run on main under lake is recorded.
EOF
}
# The prover's four universe-level primitives, each bound by its BUILTIN
# pragma; check-agda.sh checks them by name and binding on every run.
receipt_trusted_base() {
  cat <<'EOF'
Agda.Primitive|Level|BUILTIN LEVEL
Agda.Primitive|lzero|BUILTIN LEVELZERO
Agda.Primitive|lsuc|BUILTIN LEVELSUC
Agda.Primitive|_⊔_|BUILTIN LEVELMAX
EOF
}
receipt_invocation() {
  local flags
  case "$1" in
    agda)
      flags="$(sed -n 's/^flags=(\(.*\))$/\1/p' scripts/check-agda.sh)"
      [ -n "$flags" ] || receipt_die 'no flags=(…) line in scripts/check-agda.sh'
      printf 'agda %s src/ResourceAlgebra/All.agda\n' "$flags" ;;
    rocq) printf '%s\n' 'rocq compile ResourceAlgebra.v in verification/proofs/coq, then rocqchk' ;;
    lean) printf '%s\n' 'lake build in a copy of verification/proofs/lean4 made by bash scripts/check-lean-leg.sh (core only, no dependencies); then lake build of ResourceAlgebra, TropicalSessionTypes and TropicalBridge in the work directory made by bash scripts/check-lean-bridge.sh' ;;
    *) receipt_die "unknown prover: $1" ;;
  esac
}
# §8.5.1 input sets, from the tree.
#  agda: the import cone of src/ResourceAlgebra/All.agda under src/ (the
#        run is --no-libraries, so no library file is read).
#  rocq: the one file the job compiles.
#  lean: the leg and the M-2 bridge, each with its Lake package files
#        (lakefile.toml and the committed lake-manifest.json, a pinned
#        input under §8.5.1), the shared lean-toolchain, and the two
#        checker scripts: scripts/check-lean-leg.sh, and
#        scripts/check-lean-bridge.sh, which holds the pin of the imported
#        repository, so a repin changes this digest.
receipt_inputs() {
  case "$1" in
    agda) receipt_agda_cone src/ResourceAlgebra/All.agda src ;;
    rocq) printf '%s\n' verification/proofs/coq/ResourceAlgebra.v ;;
    lean) printf '%s\n' scripts/check-lean-bridge.sh scripts/check-lean-leg.sh \
            verification/bridges/tropical-types/TropicalBridge.lean \
            verification/bridges/tropical-types/lake-manifest.json \
            verification/bridges/tropical-types/lakefile.toml \
            verification/proofs/lean4/ResourceAlgebra.lean \
            verification/proofs/lean4/lake-manifest.json \
            verification/proofs/lean4/lakefile.toml \
            verification/proofs/lean4/lean-toolchain ;;
    *) receipt_die "unknown prover: $1" ;;
  esac
}
# The one file of tropical-types the M-2 bridge imports, at the pin
# scripts/check-lean-bridge.sh holds at home commit C.
receipt_imports() {
  local pin
  [ "$1" = lean ] || return 0
  pin="$(git show "$2:scripts/check-lean-bridge.sh" | sed -n 's/^TT_COMMIT=\([0-9a-f]\{40\}\)$/\1/p')"
  [ -n "$pin" ] || receipt_die "no tropical-types pin in scripts/check-lean-bridge.sh at $2"
  printf '%s|%s|%s|%s\n' "$bridge_repo" "$pin" "$bridge_dir" "$bridge_file"
}
# Make commit C of repository R present in clone D, as check-lean-bridge.sh
# fetches it.
receipt_ensure_import() {
  local repo="$1" commit="$2" dir="$3"
  [ -d "$dir/.git" ] || git init -q "$dir"
  if ! git -C "$dir" cat-file -e "$commit^{commit}" 2>/dev/null; then
    git -C "$dir" fetch -q --depth 1 "https://github.com/$repo" "$commit" \
      || receipt_die "could not fetch $repo at $commit"
  fi
  git -C "$dir" checkout -q --detach "$commit"
}
# The graded rows of PROOF-STATUS.adoc: the row ids of its tables from the
# first theorem section up to "Correspondences with other repositories (not
# graded)".
receipt_status_ids() {
  sed -n '/^== Core (Core\.agda)$/,/^== Correspondences with other repositories (not graded)$/p' "$status" \
    | sed -n 's/^| \([A-Z][A-Z]*-[0-9][0-9]*[a-z]\{0,1\}\)$/\1/p'
}
# The claims whose recheck legs PROOF-STATUS.adoc records as RECONCILED.  Its
# "Recheck legs (every row)" table is one record for every theorem row; M-2
# has its own section ("M-2 bridge (Lean only)") and no reconciled leg.
receipt_recorded_legs() {
  local rec
  rec="$(sed -n '/^== Recheck legs (every row)$/,/^=== Receipts$/p' "$status")"
  if awk '/^\| Rocq$/{l="rocq"} /^\| Lean$/{l="lean"} l && /^\| `RECONCILED`/{ok[l]=1} END{exit !(ok["rocq"] && ok["lean"])}' <<<"$rec"; then
    grep -q '^=== M-2 bridge (Lean only)$' "$status" || receipt_die "no M-2 bridge section in $status"
    receipt_status_ids | grep -vx 'M-2' || true
  fi
}

. "$RECEIPT_STD/scripts/proof-receipt.sh"
receipt_main "$@"
