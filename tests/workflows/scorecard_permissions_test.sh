#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# PR #7: the caller's explicit job permission map must grant actions: read.
# Top-level grants do not supply omitted scopes in a job permission map.
# Run: bash tests/workflows/scorecard_permissions_test.sh
# Requires mikefarah/yq v4.
set -euo pipefail

repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
workflow="$repo/.github/workflows/scorecard.yml"
fixture=$(mktemp -d)
trap 'rm -rf "$fixture"' EXIT

fail() { echo "FAIL: $*" >&2; exit 1; }
yq --version | grep -q 'github.com/mikefarah/yq.*version v4\.' \
    || fail "mikefarah/yq v4 is required"

permissions_ok() {
    yq -e '
        .jobs.scorecard.permissions |
        (.actions == "read" and .contents == "read" and
         .["security-events"] == "write" and .["id-token"] == "write")
    ' "$1" >/dev/null 2>&1
}

reject_mutant() {
    local label=$1 expression=$2
    cp "$workflow" "$fixture/mutant.yml"
    yq -i "$expression" "$fixture/mutant.yml"
    cmp -s "$workflow" "$fixture/mutant.yml" && fail "$label: mutation did not change the workflow"
    if permissions_ok "$fixture/mutant.yml"; then
        fail "$label: invalid job permissions accepted"
    fi
}

permissions_ok "$workflow" || fail "Scorecard lacks a required caller grant"

# The original failure: workflow-level actions: read is still present, but the
# job's explicit map omits actions. A text search would incorrectly pass this.
reject_mutant "top-level-only actions grant" 'del(.jobs.scorecard.permissions.actions)'
reject_mutant "actions disabled" '.jobs.scorecard.permissions.actions = "none"'
reject_mutant "unnecessary actions write access" '.jobs.scorecard.permissions.actions = "write"'
reject_mutant "null actions grant" '.jobs.scorecard.permissions.actions = null'
reject_mutant "empty job permission map" '.jobs.scorecard.permissions = {}'
reject_mutant "missing job permission map" 'del(.jobs.scorecard.permissions)'

# A grant on a sibling job cannot authorize the reusable call either.
reject_mutant "actions grant on the wrong job" '
    del(.jobs.scorecard.permissions.actions) |
    .jobs.other.permissions.actions = "read"
'

# Adding the staleness-check grant must preserve the existing checkout, SARIF
# upload and OIDC grants needed by this same reusable call.
for scope in contents security-events id-token; do
    SCOPE="$scope" reject_mutant "missing $scope grant" \
        'del(.jobs.scorecard.permissions[strenv(SCOPE)])'
done

# YAML quoting, comments and key order have no effect on permission semantics.
cp "$workflow" "$fixture/reordered.yml"
yq -i '.jobs.scorecard.permissions = {
    "id-token": "write", "security-events": "write",
    "contents": "read", "actions": "read"
}' "$fixture/reordered.yml"
printf '\n# actions: none (a comment, not a grant)\n' >>"$fixture/reordered.yml"
permissions_ok "$fixture/reordered.yml" || fail "equivalent YAML permissions rejected"

echo "PASS: Scorecard caller grants; 10 invalid permission controls rejected; equivalent YAML accepted"
