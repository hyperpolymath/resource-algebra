#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# scripts/check-agda.sh must stop when find cannot list the import cone.
# A stub find on PATH prints one real file of the cone and exits non-zero,
# as find does when it meets a directory it cannot read; CI can do this even
# as root. The gate must exit non-zero and must not report the postulate
# scan as passed. Before the fix, the scan passed on the partial list.
set -uo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
stub=$(mktemp -d); trap 'rm -rf "$stub"' EXIT
cat > "$stub/find" <<'STUB'
#!/usr/bin/env bash
printf 'src/ResourceAlgebra/All.agda\0'
echo "find: 'src/locked': Permission denied" >&2
exit 1
STUB
chmod +x "$stub/find"

out=$(PATH="$stub:$PATH" bash scripts/check-agda.sh 2>&1); rc=$?
if [[ $rc -eq 0 ]] || grep -q 'PASS: no postulate' <<<"$out"; then
  printf 'FAIL: gate passed although find failed (exit %s)\n%s\n' "$rc" "$out" >&2
  exit 1
fi
if ! grep -q 'could not list the import cone' <<<"$out"; then
  printf 'FAIL: gate stopped for another reason (exit %s)\n%s\n' "$rc" "$out" >&2
  exit 1
fi
echo "PASS: a find failure stops the gate (exit $rc) before the postulate scan passes"
