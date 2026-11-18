#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
# scripts/check-lean-leg.sh must fail when a printed theorem depends on an
# axiom, when the build fails, when nothing is printed, and when the build
# rewrites lake-manifest.json. A stub lake (LAKE=) misreports the build, once
# each way, and each case must fail for the stated reason.
set -uo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
stub=$(mktemp -d); trap 'rm -rf "$stub"' EXIT
n=$(grep -cE '^[[:space:]]*#print[[:space:]]+axioms[[:space:]]' verification/proofs/lean4/ResourceAlgebra.lean)

# $1 name, $2 shell body of the stub, run in the build directory
make_stub() { printf '#!/usr/bin/env bash\n%s\n' "$2" > "$stub/$1"; chmod +x "$stub/$1"; }

# n axiom-free reports, as lake prints them
free_reports="for i in \$(seq 1 $n); do echo \"info: ResourceAlgebra.lean:\$i:0: 'RA.t\$i' does not depend on any axioms\"; done"

fails=0
expect_fail() { # $1 stub, $2 message the script must give
  out=$(LAKE="$stub/$1" bash scripts/check-lean-leg.sh 2>&1); rc=$?
  if [[ $rc -eq 0 ]] || grep -q '^PASS:' <<<"$out"; then
    printf 'FAIL: %s: the script passed (exit %s)\n%s\n' "$1" "$rc" "$out" >&2; fails=1; return
  fi
  if ! grep -q -- "$2" <<<"$out"; then
    printf 'FAIL: %s: the script stopped for another reason (exit %s)\n%s\n' "$1" "$rc" "$out" >&2; fails=1; return
  fi
  echo "PASS: $1 makes the script fail ($2)"
}

make_stub axiom "echo \"info: ResourceAlgebra.lean:1:0: 'RA.t' depends on axioms: [propext]\"; exit 0"
expect_fail axiom 'a printed theorem depends on axioms'

make_stub broken "echo 'error: ResourceAlgebra.lean:1:0: unknown identifier'; exit 1"
expect_fail broken 'does not build under lake'

make_stub silent "echo 'Build completed successfully (3 jobs).'; exit 0"
expect_fail silent 'printed theorems are axiom-free'

make_stub short "$free_reports | head -n $((n - 1)); exit 0"
expect_fail short 'printed theorems are axiom-free'

make_stub rewrite "$free_reports; echo '{}' > lake-manifest.json; exit 0"
expect_fail rewrite 'rewrote lake-manifest.json'

exit $fails
