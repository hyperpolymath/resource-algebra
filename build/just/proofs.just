# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# FORMAL VERIFICATION (PROOFS)
#
# Imported by ../../Justfile via `import? "build/just/proofs.just"`.
# This repository's obligations are theory (standards PROOF-POLICY §1): the
# Agda source in src/, rechecked in Rocq and Lean under verification/proofs/.
# It has no ABI, FFI or protocol, so no Idris2 or TLA+ obligations
# (docs/status/PROOF-NEEDS.adoc). Run `just proof-check-all` for the sweep.

# Check every proof leg this repository owns (Agda, Rocq, Lean)
proof-check-all: proof-check-agda proof-check-coq proof-check-lean4 proof-scan-dangerous
    @echo "=== All proof checks complete ==="

# Each proof-check-<prover> delegates to scripts/check-proofs.sh, the single
# source of truth. A missing toolchain is FATAL (never a skip); every module is
# checked from its own source root; a proof file absent from the prover's
# manifest (verification/proofs/<prover>/MANIFEST) is an error. See the script
# header for the four "checks that could not fail" this replaces.

# Check Idris2 proofs (per MANIFEST; fatal if idris2 absent)
proof-check-idris2:
    @bash scripts/check-proofs.sh idris2

# Check Lean4 proofs (per MANIFEST; fatal if lean absent)
proof-check-lean4:
    @bash scripts/check-proofs.sh lean4

# Check the Agda source of truth: the canonical PROOF-POLICY §2.1 invocation
# with -Werror over src/, the unit tests and the expected rejections. This is
# the command CI (proofs.yml) runs; scripts/check-proofs.sh agda would look in
# verification/proofs/agda, which this repository does not use, and report
# "nothing to check".
proof-check-agda:
    @bash scripts/check-agda.sh

# Check Coq proofs (per MANIFEST; fatal if coqc absent)
proof-check-coq:
    @bash scripts/check-proofs.sh coq

# Scan for dangerous constructs USED in proof code (believe_me, sorry, Admitted,
# postulate, ...). Comments are ignored — a comment naming a banned construct
# must not trip the gate. See scripts/scan-dangerous.sh.
proof-scan-dangerous:
    @bash scripts/scan-dangerous.sh

# Show proof status summary
proof-status:
    #!/usr/bin/env bash
    echo "=== Proof Status ==="
    echo ""
    echo "Agda:   $(find src -name '*.agda' 2>/dev/null | wc -l) files (src/, the source of truth)"
    echo "Rocq:   $(find verification/proofs/coq -name '*.v' 2>/dev/null | wc -l) files"
    echo "Lean4:  $(find verification/proofs/lean4 -name '*.lean' 2>/dev/null | wc -l) files"
    echo ""
    # PROOF-STATUS may live at root, docs/status/ (post-#20), .md or .adoc (post-#23)
    for candidate in docs/status/PROOF-STATUS.adoc docs/status/PROOF-STATUS.md PROOF-STATUS.adoc PROOF-STATUS.md; do
        if [ -f "$candidate" ]; then
            grep -E "^Out of [0-9]+ theory rows" -A2 "$candidate" 2>/dev/null || echo "(No census line in $candidate)"
            exit 0
        fi
    done
    echo "(No PROOF-STATUS file found at root or docs/status/)"
