#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# scripts/check-lean-bridge.sh must fail when the bridge does not compile and
# when a bridge theorem depends on an axiom. A stub lean (LEAN=) compiles the
# two imported modules and then misreports the bridge, once each way. The
# script fetches tropical-types at its pin, so this test needs the network.
set -uo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
stub=$(mktemp -d); trap 'rm -rf "$stub"' EXIT

make_stub() { # $1 name, $2 what the stub prints when checking the bridge, $3 its exit code
  cat > "$stub/$1" <<FAKE_LEAN
#!/usr/bin/env bash
if [ "\$1" = "-o" ]; then : > "\$2"; exit 0; fi
printf '%s\n' "$2"
exit $3
FAKE_LEAN
  chmod +x "$stub/$1"
}

fails=0
expect_fail() { # $1 stub, $2 message the script must give
  out=$(LEAN="$stub/$1" bash scripts/check-lean-bridge.sh 2>&1); rc=$?
  if [[ $rc -eq 0 ]] || grep -q '^PASS:' <<<"$out"; then
    printf 'FAIL: %s: the script passed (exit %s)\n%s\n' "$1" "$rc" "$out" >&2; fails=1; return
  fi
  if ! grep -q -- "$2" <<<"$out"; then
    printf 'FAIL: %s: the script stopped for another reason (exit %s)\n%s\n' "$1" "$rc" "$out" >&2; fails=1; return
  fi
  echo "PASS: $1 makes the script fail ($2)"
}

make_stub axiom "'RA.TropicalBridge.rmax_eq_max' depends on axioms: [propext]" 0
expect_fail axiom 'bridge theorems are axiom-free'

make_stub broken "TropicalBridge.lean:1:0: error: unknown module prefix" 1
expect_fail broken 'the bridge does not compile'

make_stub silent "" 0
expect_fail silent 'bridge theorems are axiom-free'

exit $fails
