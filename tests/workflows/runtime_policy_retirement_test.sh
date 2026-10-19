#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Exercise PR #13's retirement and relocked-tag guards through the real gate.
# A synchronized legacy workflow must still fail the retirement requirement.
# Usage: bash tests/workflows/runtime_policy_retirement_test.sh
# Requires the gate's existing dependencies: mikefarah yq v4, jq and GNU awk.
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
gate="$repo/tests/workflows/actions_lock_sha_refs_test.sh"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
workflows="$scratch/workflows with spaces"
mkdir -p "$workflows"
cp -a "$repo/.github/workflows/." "$workflows/"
original_lock="$repo/.github/workflows/actions.lock"

# Print the captured gate output so a setup failure cannot masquerade as an
# expected rejection from the specific guard being tested.
fail() {
    echo "FAIL: $*" >&2
    if [[ -f "$scratch/gate.log" ]]; then cat "$scratch/gate.log" >&2; fi
    exit 1
}

# Exercise the complete passing gate before introducing one defect at a time.
bash "$gate" "$workflows" > "$scratch/gate.log" 2>&1 \
    || fail 'unmodified workflows must pass the regression gate'
grep -Fq 'PASS: restoring governance restores passing validation' "$scratch/gate.log" \
    || fail 'the lock regression gate must run the governance migration controls'
echo 'PASS: current workflows and lock pass the complete regression gate'

# Require the intended exit status and diagnostic, rather than accepting any
# failure (for example, an unrelated lock-sync or fixture error).
reject_case() {
    local label=$1 diagnostic=$2 status=0
    bash "$gate" "$workflows" > "$scratch/gate.log" 2>&1 || status=$?
    [[ "$status" == 1 ]] || fail "$label: expected exit 1, got $status"
    grep -Fq "FAIL: $diagnostic" "$scratch/gate.log" \
        || fail "$label: the gate did not identify the intended regression"
    echo "PASS: $label rejected by the regression gate"
}

workflow_error='runtime-policy.yml must remain folded into governance'
lock_error='runtime-policy.yml must not retain a lock entry'

printf '%s\n' '# SPDX-License-Identifier: MPL-2.0' 'name: Retired workflow' \
    > "$workflows/runtime-policy.yml"
reject_case 'restored regular workflow' "$workflow_error"
rm "$workflows/runtime-policy.yml"

mkdir "$workflows/runtime-policy.yml"
reject_case 'directory occupying the retired workflow path' "$workflow_error"
rmdir "$workflows/runtime-policy.yml"

ln -s governance.yml "$workflows/runtime-policy.yml"
reject_case 'retired workflow symlink to an existing workflow' "$workflow_error"
rm "$workflows/runtime-policy.yml"

# -e alone cannot detect this path; the explicit -L guard must also hold.
ln -s missing-workflow.yml "$workflows/runtime-policy.yml"
reject_case 'dangling retired workflow symlink' "$workflow_error"
rm "$workflows/runtime-policy.yml"

# A key is stale regardless of its value, including a null value that a
# truthiness check could overlook. Preserve the lock generator's formatting.
for value in '[]' 'null' "['actions/checkout@v7.0.1']"; do
    awk -v entry="    '.github/workflows/runtime-policy.yml': $value" '
        { print }
        /^workflows:$/ { print entry }
    ' "$original_lock" > "$workflows/actions.lock"
    reject_case "retired lock entry with value $value" "$lock_error"
done

# Both sides can be restored consistently, so lock synchronization alone is
# insufficient. This fixture passes the real sync gate before being rejected.
awk '
    { print }
    /^workflows:$/ { print "    \047.github/workflows/runtime-policy.yml\047: []" }
' "$original_lock" > "$workflows/actions.lock"
printf '%s\n' '# SPDX-License-Identifier: MPL-2.0' 'name: Retired workflow' \
    > "$workflows/runtime-policy.yml"
bash "$repo/scripts/check-lock-sync.sh" "$workflows" > "$scratch/gate.log" 2>&1 \
    || fail 'the synchronized legacy fixture must pass lock synchronization'
reject_case 'synchronized restored workflow and lock entry' "$workflow_error"
rm "$workflows/runtime-policy.yml"

# A different symbolic ref still satisfies the SHA-ref safety predicate but
# must fail the additional exact-tag assertion introduced by this PR. Select
# the first action checked by the gate so this control stays fast.
cache_key=$(yq -o=json '.' "$original_lock" | jq -er '
    [.dependencies | keys[] | select(test("^actions/cache@[0-9a-f]{40}$"))]
    | select(length == 1) | .[0]
')
cache_tag=$(yq -o=json '.' "$original_lock" | jq -er --arg key "$cache_key" \
    '.dependencies[$key].ref')
awk -v header="    '$cache_key':" '
    $0 == header { in_record = 1; print; next }
    in_record && /^        ref:/ {
        print "        ref: \047unexpected-symbolic-ref\047"
        in_record = 0
        next
    }
    { print }
' "$original_lock" > "$workflows/actions.lock"
reject_case 'different nonempty symbolic action ref' \
    "$cache_key must retain its relocked tag $cache_tag"
