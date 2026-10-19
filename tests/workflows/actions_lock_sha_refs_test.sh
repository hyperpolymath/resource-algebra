#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# The four SHA-keyed leaves added by standards must carry a symbolic (tag)
# ref, with the SHA in their key and commit. GitHub's runner rejects a record
# whose ref is its own SHA ("invalid lockfile pin", enforced from 2026-10-15;
# standards#1271), so the SHA ref PR #7 asked for stopped every job that
# resolved such a record. The commit, not the ref, pins the action.
# Separate tag-keyed records remain valid. This test is offline.
# Usage: bash tests/workflows/actions_lock_sha_refs_test.sh [workflow-directory]
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
WF_DIR="${1:-$REPO/.github/workflows}"
LOCK="$WF_DIR/actions.lock"
FIXTURE=$(mktemp -d)
trap 'rm -rf "$FIXTURE"' EXIT

fail() { echo "FAIL: $*" >&2; exit 1; }
command -v jq >/dev/null || fail "jq is required"
yq --version | grep -q 'github.com/mikefarah/yq/' || fail "mikefarah yq v4 is required"
yq -o=json '.' "$LOCK" > "$FIXTURE/lock.json"

# Use the standards pin actually called by governance, so a later standards
# update does not require copying its commit into this test.
STANDARDS=$(jq -er '
    [.workflows[".github/workflows/governance.yml"][]
     | select(startswith("hyperpolymath/standards@"))]
    | select(length == 1) | .[0]
' "$FIXTURE/lock.json") || fail "governance must lock exactly one standards reusable"

# Assertions on parsed data, independent of the sync gate (which checks edges
# but deliberately does not inspect ref/commit metadata).
pinned_record() {
    local key="$1" file="$2"
    jq -e --arg key "$key" '
        ($key | split("@")[1]) as $sha
        | .dependencies[$key] as $record
        | ($sha | test("^[0-9a-f]{40}$"))
          and ($record.commit == ("sha1-" + $sha))
          and ($record.ref | type == "string" and . != "")
          and ($record.ref | test("^[0-9a-fA-F]{40}$") | not)
    ' "$file" >/dev/null
}

# Run the production gate on the real workflows before negative controls, so
# an unrelated fixture/setup failure cannot masquerade as a useful rejection.
bash "$REPO/scripts/check-lock-sync.sh" "$WF_DIR" > "$FIXTURE/sync.log" 2>&1 \
    || { cat "$FIXTURE/sync.log" >&2; fail "the current lock must be in sync and closed"; }
mkdir -p "$FIXTURE/workflows"
cp -a "$WF_DIR/." "$FIXTURE/workflows/"

checked=0
while IFS='|' read -r action tag_ref owner_id repo_id; do
    key=$(jq -er --arg standards "$STANDARDS" --arg action "$action" '
        [.dependencies[$standards].uses[] | select(startswith($action + "@"))]
        | select(length == 1) | .[0]
    ' "$FIXTURE/lock.json") || fail "$action must occur exactly once in standards transitive coverage"

    pinned_record "$key" "$FIXTURE/lock.json" \
        || fail "$key must have a symbolic ref and its own SHA as commit"
    jq -e --arg key "$key" --argjson owner "$owner_id" --argjson repo "$repo_id" '
        .dependencies[$key] | .owner_id == $owner and .repo_id == $repo
    ' "$FIXTURE/lock.json" >/dev/null || fail "$key lost its repository identity"

    # Reproduce the record GitHub's runner refuses: the key's own SHA as ref
    # (the shape PR #7 wrote), and the same SHA in upper case.
    sha=${key##*@}
    for bad_ref in "$sha" "${sha^^}" ""; do
        jq --arg key "$key" --arg ref "$bad_ref" '
            .dependencies[$key].ref = $ref
        ' "$FIXTURE/lock.json" > "$FIXTURE/mutated.json"
        if pinned_record "$key" "$FIXTURE/mutated.json"; then
            fail "$key accepted the refused ref '$bad_ref'"
        fi
    done

    # A valid-looking, different SHA is still a broken key/commit binding.
    jq --arg key "$key" '
        .dependencies[$key].commit = "sha1-0000000000000000000000000000000000000000"
    ' "$FIXTURE/lock.json" > "$FIXTURE/mutated.json"
    if pinned_record "$key" "$FIXTURE/mutated.json"; then
        fail "$key accepted a mismatched commit"
    fi

    # Delete only this leaf record, keeping its incoming standards edge and
    # all other workflow/lock data intact. Preserve gh-actions-lock layout:
    # the production gate parses that layout, not yq's reformatted output.
    awk -v key="$key" '
        $0 == "    \047" key "\047:" { skip = 1; next }
        skip && /^    \047/ { skip = 0 }
        !skip { print }
    ' "$LOCK" > "$FIXTURE/workflows/actions.lock"
    if bash "$REPO/scripts/check-lock-sync.sh" "$FIXTURE/workflows" > "$FIXTURE/sync.log" 2>&1; then
        fail "sync gate accepted a missing record for $key"
    fi
    if ! grep -qF 'DANGLING EDGES' "$FIXTURE/sync.log" \
        || ! grep -qF "$key" "$FIXTURE/sync.log"; then
        cat "$FIXTURE/sync.log" >&2
        fail "sync gate did not identify the missing $key"
    fi

    # upload-artifact and setup-bun also have direct tag users. Their records
    # must coexist with the SHA records; the repair must not globally ban tags.
    if [[ "$action" == actions/upload-artifact || "$action" == oven-sh/setup-bun ]]; then
        jq -e --arg key "$key" --arg alias "$action@$tag_ref" --arg tag "$tag_ref" '
            .dependencies[$alias].ref == $tag
            and (.dependencies[$alias].commit == .dependencies[$key].commit)
            and ([.workflows[][] | select(. == $alias)] | length > 0)
        ' "$FIXTURE/lock.json" >/dev/null || fail "$action lost its separate referenced tag record"
    fi

    checked=$((checked + 1))
    echo "PASS: $action SHA binding, identity, negative controls and closure"
done <<'CASES'
actions/upload-artifact|v7.0.2|44036562|192625955
denoland/setup-deno|v2.0.5|42048915|356423100
dtolnay/rust-toolchain|v1|1940490|260749683
oven-sh/setup-bun|v2.2.0|108928776|512644635
CASES

[[ "$checked" == 4 ]] || fail "expected to check all four changed dependency records"
echo "PASS: actions.lock SHA-ref regression controls ($checked dependencies)"
