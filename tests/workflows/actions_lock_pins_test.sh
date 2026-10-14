#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# PR #7: the four transitive action records must retain their immutable refs.
# Run: bash tests/workflows/actions_lock_pins_test.sh
# Requires mikefarah/yq v4 and gawk (for the repository's lock-sync gate).
set -euo pipefail

repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
lock="$repo/.github/workflows/actions.lock"
fixture=$(mktemp -d)
trap 'rm -rf "$fixture"' EXIT

fail() { echo "FAIL: $*" >&2; exit 1; }
yq --version | grep -q 'github.com/mikefarah/yq.*version v4\.' \
    || fail "mikefarah/yq v4 is required"

# Discover the current standards pin from the caller, so a legitimate future
# pin bump does not require copying new SHAs into this test.
caller=$(yq -r '.jobs.scorecard.uses' "$repo/.github/workflows/scorecard.yml")
standards_key="${caller%%/.github/workflows/*}@${caller##*@}"

pin_ok() {
    local key=$1 file=$2 sha=${1##*@}
    [[ "$sha" =~ ^[0-9a-f]{40}$ ]] || return 1
    DEP_KEY="$key" PIN_SHA="$sha" yq -e '
        .dependencies[strenv(DEP_KEY)] |
        (.ref == strenv(PIN_SHA) and .commit == ("sha1-" + strenv(PIN_SHA)))
    ' "$file" >/dev/null 2>&1
}

reject_mutant() {
    local label=$1 key=$2
    cmp -s "$lock" "$fixture/mutant.lock" && fail "$label: mutation did not change the lock"
    if pin_ok "$key" "$fixture/mutant.lock"; then
        fail "$label: invalid pin accepted"
    fi
}

# Closure is essential: a valid-looking ref alone cannot start a workflow if
# the called reusable's dependency graph has a dangling edge.
bash "$repo/scripts/check-lock-sync.sh" "$repo/.github/workflows" >"$fixture/sync.log" 2>&1 \
    || { cat "$fixture/sync.log" >&2; fail "repository lock is not in sync and transitively closed"; }

checked=0
while read -r action old_tag; do
    refs=$(STANDARDS_KEY="$standards_key" ACTION="$action" yq -r '
        .dependencies[strenv(STANDARDS_KEY)].uses[] |
        select(split("@")[0] == strenv(ACTION))
    ' "$lock")
    [ -n "$refs" ] || fail "$action: absent from the standards dependency graph"
    [[ "$refs" != *$'\n'* ]] || fail "$action: ambiguous transitive pin"
    key=$refs
    pin_ok "$key" "$lock" || fail "$action: ref and commit must match the full SHA in its dependency key"

    # Reproduce the exact pre-PR metadata while leaving the SHA key and commit
    # intact. Closure alone accepts this, but the immutable-ref contract must not.
    cp "$lock" "$fixture/mutant.lock"
    DEP_KEY="$key" OLD_TAG="$old_tag" yq -i \
        '.dependencies[strenv(DEP_KEY)].ref = strenv(OLD_TAG)' "$fixture/mutant.lock"
    reject_mutant "$action: old tag $old_tag" "$key"

    cp "$lock" "$fixture/mutant.lock"
    DEP_KEY="$key" yq -i '.dependencies[strenv(DEP_KEY)].ref = "main"' "$fixture/mutant.lock"
    reject_mutant "$action: floating branch" "$key"

    cp "$lock" "$fixture/mutant.lock"
    DEP_KEY="$key" SHORT_SHA="${key##*@}" yq -i \
        '.dependencies[strenv(DEP_KEY)].ref = (strenv(SHORT_SHA) | sub(".$"; ""))' "$fixture/mutant.lock"
    reject_mutant "$action: 39-character ref" "$key"

    cp "$lock" "$fixture/mutant.lock"
    DEP_KEY="$key" yq -i \
        '.dependencies[strenv(DEP_KEY)].commit = "sha1-0000000000000000000000000000000000000000"' "$fixture/mutant.lock"
    reject_mutant "$action: mismatched commit" "$key"

    cp "$lock" "$fixture/mutant.lock"
    DEP_KEY="$key" yq -i 'del(.dependencies[strenv(DEP_KEY)].ref)' "$fixture/mutant.lock"
    reject_mutant "$action: missing ref" "$key"

    cp "$lock" "$fixture/mutant.lock"
    DEP_KEY="$key" yq -i 'del(.dependencies[strenv(DEP_KEY)])' "$fixture/mutant.lock"
    reject_mutant "$action: missing dependency record" "$key"
    checked=$((checked + 1))
done <<'ACTIONS'
actions/upload-artifact v7.0.2
denoland/setup-deno v2.0.5
dtolnay/rust-toolchain v1
oven-sh/setup-bun v2.2.0
ACTIONS

echo "PASS: $checked immutable action records; 24 invalid metadata controls rejected; lock graph closed"
