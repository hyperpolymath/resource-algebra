#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# scripts/check-lean-bridge.sh must fail when the bridge package does not
# build, when a bridge theorem depends on an axiom, when nothing is printed,
# and when the build rewrites lake-manifest.json. A stub lake (LAKE=)
# misreports the build, once each way, and each case must fail for the stated
# reason. The script fetches tropical-types at its pin, so this test needs the
# network.
set -uo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
stub=$(mktemp -d); trap 'rm -rf "$stub"' EXIT
n=$(grep -c '^#print axioms' verification/bridges/tropical-types/TropicalBridge.lean)

# $1 name, $2 shell body of the stub, run in the build directory
make_stub() { printf '#!/usr/bin/env bash\n%s\n' "$2" > "$stub/$1"; chmod +x "$stub/$1"; }

# n axiom-free reports for the bridge, as lake prints them
free_reports="for i in \$(seq 1 $n); do echo \"info: TropicalBridge.lean:\$i:0: 'RA.TropicalBridge.t\$i' does not depend on any axioms\"; done"

fails=0
expect_fail() { # $1 stub, $2 message the script must give
  out=$(LAKE="$stub/$1" bash scripts/check-lean-bridge.sh 2>&1); rc=$?
  if [[ $rc -eq 0 ]] || grep -q '^PASS:' <<<"$out"; then
    printf 'FAIL: %s: the script passed (exit %s)\n%s\n' "$1" "$rc" "$out" >&2; fails=1; return
  fi
  if ! grep -q -- "$2" <<<"$out"; then
    printf 'FAIL: %s: the script stopped for another reason (exit %s)\n%s\n' "$1" "$rc" "$out" >&2; fails=1; return
  fi
  echo "PASS: $1 makes the script fail ($2)"
}

make_stub axiom "echo \"info: TropicalBridge.lean:1:0: 'RA.TropicalBridge.rmax_eq_max' depends on axioms: [propext]\"; exit 0"
expect_fail axiom 'a printed theorem depends on axioms'

make_stub broken "echo 'error: TropicalBridge.lean:1:0: unknown module prefix'; exit 1"
expect_fail broken 'does not build under lake'

make_stub silent "echo 'Build completed successfully (5 jobs).'; exit 0"
expect_fail silent 'bridge theorems are axiom-free'

make_stub short "$free_reports | head -n $((n - 1)); exit 0"
expect_fail short 'bridge theorems are axiom-free'

# Reports for another file do not count towards the bridge's own.
make_stub otherfile "$free_reports | sed 's/TropicalBridge.lean/ResourceAlgebra.lean/'; exit 0"
expect_fail otherfile 'bridge theorems are axiom-free'

make_stub rewrite "$free_reports; echo '{}' > lake-manifest.json; exit 0"
expect_fail rewrite 'rewrote lake-manifest.json'

exit $fails
