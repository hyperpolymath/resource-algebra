#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# check_agda_pragma_test.sh — controls for scripts/check-agda.sh's refusal of an
# OPTIONS pragma that sets a warning flag (-W / --warning).
#
# A module's own pragma overrides the gate's command line, so
# {-# OPTIONS -W noerror #-} would undo `-W error` for that module. The gate
# must refuse it in EVERY module it checks (src/, tests/unit, tests/reject),
# before Agda runs, and name the file and line. Each case is a throwaway copy
# of the gate with one planted module and a FAKE_AGDA prover that answers --version
# and records any other call, so the refusal is tested on its own: nothing here
# runs a real Agda, and a refused case must not reach the prover at all. The
# clean cases must get past the scan (its PASS line is printed and no refusal).
# Whether the repository's real modules pass is the real gate's job
# (scripts/check-agda.sh, run by proofs.yml with the pinned Agda).
#
# Exit: 0 all controls hold; 1 a control failed.

set -uo pipefail

REPO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
command -v perl >/dev/null || { echo "FAIL: perl is required" >&2; exit 1; }

FAKE_AGDA="$WORK/fake-agda"
cat >"$FAKE_AGDA" <<'FAKE'
#!/usr/bin/env bash
if [ "${1:-}" = "--version" ]; then echo "stub 0"; exit 0; fi
printf '%s\n' "$*" >>"$FAKE_LOG"
exit 0
FAKE
chmod +x "$FAKE_AGDA"

FAILED=0; CHECKS=0
note() { CHECKS=$((CHECKS + 1)); if [ "$1" = ok ]; then echo "  PASS  $2"; else FAILED=$((FAILED + 1)); echo "  FAIL  $2"; fi; }

# fixture NAME — a gate copy whose three module directories each hold one clean module.
fixture() {
    local d="$WORK/$1" m
    mkdir -p "$d/scripts" "$d/src/ResourceAlgebra" "$d/tests/unit" "$d/tests/reject"
    cp "$REPO_DIR/scripts/check-agda.sh" "$REPO_DIR/scripts/scan-postulates.pl" "$REPO_DIR/scripts/scan-agda-pragmas.pl" "$d/scripts/"
    for m in src/ResourceAlgebra/All tests/unit/AllTests tests/reject/Bad; do
        printf '{-# OPTIONS --safe --without-K #-}\nmodule %s where\n' "$(basename "$m")" >"$d/$m.agda"
    done
    echo "$d"
}
# gate DIR — run the gate copy with the stub prover; sets OUT, RC and the stub log.
gate() {
    : >"$WORK/stub.log"
    OUT="$(cd "$1" && FAKE_LOG="$WORK/stub.log" AGDA="$FAKE_AGDA" bash scripts/check-agda.sh 2>&1)"; RC=$?
}
# refused LABEL DIR FILE:LINE — the gate stopped on the pragma, named the place,
# and never ran the prover on a module.
refused() {
    gate "$2"
    if [ "$RC" -ne 0 ] \
        && grep -qF -- "Error: OPTIONS pragma sets a warning flag, overriding the gate's -W error: $3:" <<<"$OUT" \
        && ! grep -qF 'PASS: no OPTIONS pragma' <<<"$OUT" \
        && [ ! -s "$WORK/stub.log" ]; then
        note ok "$1"
    else
        note bad "$1 (rc=$RC)"; sed 's/^/        /' <<<"$OUT" | tail -8
    fi
}
# passes_scan LABEL DIR — the pragma scan passed (the gate may stop later on the stub).
passes_scan() {
    gate "$2"
    if grep -qF 'PASS: no OPTIONS pragma sets a warning flag' <<<"$OUT" \
        && ! grep -qF 'OPTIONS pragma sets a warning flag, overriding' <<<"$OUT"; then
        note ok "$1"
    else
        note bad "$1 (rc=$RC)"; sed 's/^/        /' <<<"$OUT" | tail -8
    fi
}
plant() { printf '%s' "$3" >"$1/$2"; }

# --- positive controls -----------------------------------------------------------
d="$(fixture clean)"
passes_scan "clean modules in src, tests/unit and tests/reject pass the scan" "$d"

d="$(fixture comment)"
plant "$d" src/ResourceAlgebra/All.agda $'{-# OPTIONS --safe --without-K #-}\n-- never write -W noerror or --warning in a pragma\nmodule All where\n'
passes_scan "-W named in a comment outside any pragma passes the scan" "$d"

d="$(fixture realflags)"
plant "$d" src/ResourceAlgebra/All.agda $'{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}\nmodule All where\n'
passes_scan "the repository's own pragma flags pass the scan" "$d"

# --- negative controls -----------------------------------------------------------
d="$(fixture src-W)"
plant "$d" src/ResourceAlgebra/All.agda $'{-# OPTIONS -W noerror #-}\nmodule All where\n'
refused "src: {-# OPTIONS -W noerror #-} is refused" "$d" src/ResourceAlgebra/All.agda:1

d="$(fixture src-warning)"
plant "$d" src/ResourceAlgebra/All.agda $'{-# OPTIONS --safe --warning=noerror #-}\nmodule All where\n'
refused "src: the --warning spelling is refused" "$d" src/ResourceAlgebra/All.agda:1

d="$(fixture src-warning-arg)"
plant "$d" src/ResourceAlgebra/All.agda $'{-# OPTIONS --safe --warning noerror #-}\nmodule All where\n'
refused "src: --warning with a separate argument is refused" "$d" src/ResourceAlgebra/All.agda:1

d="$(fixture src-multiline)"
plant "$d" src/ResourceAlgebra/All.agda $'-- header\n{-# OPTIONS --safe\n            --without-K\n            -W noerror #-}\nmodule All where\n'
refused "src: a pragma split over lines is refused, at the line it starts" "$d" src/ResourceAlgebra/All.agda:2

d="$(fixture src-nested)"
mkdir -p "$d/src/ResourceAlgebra/Instances"
printf '{-# OPTIONS --safe #-}\nmodule Inst where\n' >"$d/src/ResourceAlgebra/Instances/Inst.agda"
plant "$d" src/ResourceAlgebra/Instances/Inst.agda $'{-# OPTIONS --safe -Wnoerror #-}\nmodule Inst where\n'
refused "src: a nested module is scanned too (-Wnoerror, no space)" "$d" src/ResourceAlgebra/Instances/Inst.agda:1

d="$(fixture unit-W)"
plant "$d" tests/unit/AllTests.agda $'{-# OPTIONS --safe -W noerror #-}\nmodule AllTests where\n'
refused "tests/unit: a warning flag is refused" "$d" tests/unit/AllTests.agda:1

d="$(fixture reject-W)"
plant "$d" tests/reject/Bad.agda $'{-# OPTIONS --safe --warning=noerror #-}\nmodule Bad where\n'
refused "tests/reject: a warning flag is refused" "$d" tests/reject/Bad.agda:1

d="$(fixture src-warn-abbrev)"
plant "$d" src/ResourceAlgebra/All.agda $'{-# OPTIONS --safe --warn=noerror #-}\nmodule All where\n'
refused "src: the --warn abbreviation is refused" "$d" src/ResourceAlgebra/All.agda:1

d="$(fixture src-wa-short)"
plant "$d" src/ResourceAlgebra/All.agda $'{-# OPTIONS --wa=noerror #-}\nmodule All where\n'
refused "src: the shortest --wa abbreviation is refused" "$d" src/ResourceAlgebra/All.agda:1

d="$(fixture src-hash-in-option)"
plant "$d" src/ResourceAlgebra/All.agda $'{-# OPTIONS --verbose=check#-}:0 -W noerror #-}\nmodule All where\n'
refused "src: a #-} inside an option does not end the scan" "$d" src/ResourceAlgebra/All.agda:1

d="$(fixture unit-literate)"
plant "$d" tests/unit/Helper.lagda.md $'# Helper\n\n```agda\n{-# OPTIONS -W noerror #-}\nmodule Helper where\n```\n'
refused "tests/unit: a literate module (.lagda.md) is scanned too" "$d" tests/unit/Helper.lagda.md:4

d="$(fixture unit-dangling)"
ln -s Nowhere.agda "$d/tests/unit/Dangling.agda"
gate "$d"
if [ "$RC" -ne 0 ] && grep -qF 'could not scan the modules for OPTIONS pragmas' <<<"$OUT" \
    && ! grep -qF 'PASS: no OPTIONS pragma' <<<"$OUT" && [ ! -s "$WORK/stub.log" ]; then
    note ok "tests/unit: a module the scan cannot read (dangling symlink) fails the gate"
else
    note bad "tests/unit: a module the scan cannot read (dangling symlink) fails the gate (rc=$RC)"; sed 's/^/        /' <<<"$OUT" | tail -8
fi

# A file that opens but whose read fails (EIO) must fail the gate, never pass as
# an empty file. /proc/self/mem is a readable regular file whose reads at
# offset 0 fail on Linux. Elsewhere the control is reported as not run, loudly.
if [ -r /proc/self/mem ]; then
    d="$(fixture unit-read-error)"
    ln -s /proc/self/mem "$d/tests/unit/Mem.agda"
    gate "$d"
    if [ "$RC" -ne 0 ] && grep -qF 'error reading tests/unit/Mem.agda' <<<"$OUT" \
        && grep -qF 'could not scan the modules for OPTIONS pragmas' <<<"$OUT" && [ ! -s "$WORK/stub.log" ]; then
        note ok "tests/unit: a module whose read fails part-way fails the gate, not read as empty"
    else
        note bad "tests/unit: a module whose read fails part-way fails the gate (rc=$RC)"; sed 's/^/        /' <<<"$OUT" | tail -8
    fi
else
    echo "  NOT RUN  read-error control: /proc/self/mem is not readable on this platform"
fi

d="$(fixture unit-empty)"
: >"$d/tests/unit/Empty.agda"
passes_scan "an empty module is read as empty and passes the scan" "$d"

echo "$CHECKS controls, $FAILED failed"
[ "$FAILED" -eq 0 ]
