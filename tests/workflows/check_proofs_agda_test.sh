#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# check_proofs_agda_test.sh — controls for the agda branch of scripts/check-proofs.sh.
#
# The gate refuses a gated Agda module whose own OPTIONS pragma sets a warning
# flag (-W / --warning): such a pragma overrides the gate's `-W error`
# (e.g. {-# OPTIONS -W noerror #-}). A FAKE agda goes first on PATH, so these
# controls test the gate's verdict logic and not the prover; nothing here runs
# a real Agda. The fake records its arguments so the clean case can also check
# that `-W error` reaches the prover. This is a test of the gate, not a proof
# that any proof checks. (The prover-independent gate for this repository's
# own modules is scripts/check-agda.sh; tests/workflows/check_agda_pragma_test.sh.)
#
# Exit: 0 all controls hold; 1 a control failed.

set -uo pipefail

REPO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# A PATH with the shell tools the gate needs and NO prover; the fake is added per case.
BASEBIN="$WORK/basebin"; mkdir -p "$BASEBIN"
for t in bash sed grep find sort comm mktemp cat head dirname basename rm tr cut wc awk env perl; do
    p="$(command -v "$t" 2>/dev/null || true)"
    [ -n "$p" ] && ln -s "$p" "$BASEBIN/$t"
done
FAKEBIN="$WORK/fakebin"; mkdir -p "$FAKEBIN"
cat >"$FAKEBIN/agda" <<'FAKE'
#!/usr/bin/env bash
if [ "${1:-}" = "--version" ]; then echo "fake 0"; exit 0; fi
# One argument per line, so the gate cannot pass by handing "-W error" as one word.
printf '%s\n' "$@" >>"${FAKE_AGDA_LOG:-/dev/null}"
exit 0
FAKE
chmod +x "$FAKEBIN/agda"

FAILED=0; CHECKS=0
# fixture NAME — a throwaway repo root holding only the gate and its scanner.
fixture() {
    local d="$WORK/$1"; mkdir -p "$d/scripts" "$d/verification/proofs/agda"
    cp "$REPO_DIR/scripts/check-proofs.sh" "$REPO_DIR/scripts/scan-dangerous.sh" "$REPO_DIR/scripts/scan-agda-pragmas.pl" "$d/scripts/"
    echo "$d"
}
# module DIR CONTENT — one gated Agda module A.agda and its MANIFEST.
module() {
    printf '%s' "$2" >"$1/verification/proofs/agda/A.agda"
    echo 'verification/proofs/agda|A.agda|gated|' >"$1/verification/proofs/agda/MANIFEST"
}
# run LABEL WANT_RC DIR PATTERN  — PATTERN must appear in the output.
run() {
    local label="$1" want="$2" dir="$3" pat="${4:-}" rc=0 out
    : >"$WORK/agda.args"
    out="$(FAKE_AGDA_LOG="$WORK/agda.args" PATH="$FAKEBIN:$BASEBIN" bash "$dir/scripts/check-proofs.sh" agda 2>&1)" || rc=$?
    CHECKS=$((CHECKS + 1))
    if [ "$rc" -ne "$want" ]; then
        FAILED=$((FAILED + 1)); echo "  FAIL  $label (want rc=$want, got rc=$rc)"; sed 's/^/        /' <<<"$out" | tail -12
    elif [ -n "$pat" ] && ! grep -qF -- "$pat" <<<"$out"; then
        FAILED=$((FAILED + 1)); echo "  FAIL  $label (rc ok, output lacks: $pat)"; sed 's/^/        /' <<<"$out" | tail -12
    else
        echo "  PASS  $label"
    fi
}
# prover_ran LABEL WANT(yes|no) — whether the fake agda was invoked on a module.
prover_ran() {
    local label="$1" want="$2" ran=no
    [ -s "$WORK/agda.args" ] && ran=yes
    CHECKS=$((CHECKS + 1))
    if [ "$ran" = "$want" ]; then echo "  PASS  $label"
    else FAILED=$((FAILED + 1)); echo "  FAIL  $label (prover ran: $ran, want: $want)"; fi
}

# --- positive control ------------------------------------------------------------
d="$(fixture agdaok)"
module "$d" $'{-# OPTIONS --safe --without-K #-}\nmodule A where\n'
run "agda: a pragma without a warning flag passes" 0 "$d" "RESULT: PASS"
if awk 'prev == "-W" && $0 == "error" { ok = 1 } { prev = $0 } END { exit !ok }' "$WORK/agda.args"; then
    CHECKS=$((CHECKS + 1)); echo "  PASS  agda: the gate runs the prover with -W error"
else
    CHECKS=$((CHECKS + 1)); FAILED=$((FAILED + 1)); echo "  FAIL  agda: -W error did not reach the prover: $(cat "$WORK/agda.args")"
fi

d="$(fixture agdacomment)"
module "$d" $'{-# OPTIONS --safe #-}\n-- never use -W noerror or --warning here\nmodule A where\n'
run "agda: -W in a comment outside any pragma passes" 0 "$d" "RESULT: PASS"

# --- negative controls -----------------------------------------------------------
d="$(fixture agdawarn)"
module "$d" $'{-# OPTIONS -W noerror #-}\nmodule A where\n'
run "agda: an OPTIONS pragma that overrides -W error fails" 1 "$d" "OPTIONS pragma sets a warning flag"
prover_ran "agda: the refused module never reaches the prover" no

d="$(fixture agdawarnlong)"
module "$d" $'{-# OPTIONS --safe --warning=noerror #-}\nmodule A where\n'
run "agda: the --warning spelling fails" 1 "$d" "OPTIONS pragma sets a warning flag"

d="$(fixture agdawarnspace)"
module "$d" $'{-# OPTIONS --safe --warning noerror #-}\nmodule A where\n'
run "agda: --warning with a separate argument fails" 1 "$d" "OPTIONS pragma sets a warning flag"

d="$(fixture agdamultiline)"
module "$d" $'{-# OPTIONS --safe\n    -W noerror #-}\nmodule A where\n'
run "agda: a pragma split over lines fails" 1 "$d" "OPTIONS pragma sets a warning flag"
prover_ran "agda: the split pragma never reaches the prover" no

d="$(fixture agdawarnabbrev)"
module "$d" $'{-# OPTIONS --safe --warn=noerror #-}\nmodule A where\n'
run "agda: the --warn abbreviation fails" 1 "$d" "OPTIONS pragma sets a warning flag"

d="$(fixture agdawashort)"
module "$d" $'{-# OPTIONS --wa=noerror #-}\nmodule A where\n'
run "agda: the shortest --wa abbreviation fails" 1 "$d" "OPTIONS pragma sets a warning flag"

d="$(fixture agdahashinopt)"
module "$d" $'{-# OPTIONS --verbose=check#-}:0 -W noerror #-}\nmodule A where\n'
run "agda: a #-} inside an option does not end the scan" 1 "$d" "OPTIONS pragma sets a warning flag"
prover_ran "agda: that module never reaches the prover" no

d="$(fixture agdaquarmissing)"
printf '%s\n' 'verification/proofs/agda|Gone.agda|quarantine|removed' >"$d/verification/proofs/agda/MANIFEST"
run "agda: a quarantined module the scan cannot read fails the gate" 1 "$d" "pre-check could not run"

d="$(fixture agdagatedmissing)"
printf '%s\n' 'verification/proofs/agda|Gone.agda|gated|' >"$d/verification/proofs/agda/MANIFEST"
run "agda: a gated module the scan cannot read fails" 1 "$d" "could not scan Gone.agda"
prover_ran "agda: an unreadable module never reaches the prover" no

echo "$CHECKS controls, $FAILED failed"
[ "$FAILED" -eq 0 ]
