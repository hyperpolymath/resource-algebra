#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# The twelve SHA-keyed leaves relocked in PR #12 must carry a symbolic (tag)
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

# All six callers must use the same immutable standards revision, including
# the reusable's path (a lock key alone loses that path information).
standards_sha=${STANDARDS##*@}
[[ "$standards_sha" =~ ^[0-9a-f]{40}$ ]] || fail "standards must be pinned by SHA"
for workflow in governance hypatia-scan mirror rust-ci scorecard secret-scanner; do
    jq -e --arg workflow ".github/workflows/$workflow.yml" --arg standards "$STANDARDS" '
        .workflows[$workflow] == [$standards]
    ' "$FIXTURE/lock.json" >/dev/null || fail "$workflow must lock the shared standards pin"
    expected="hyperpolymath/standards/.github/workflows/$workflow-reusable.yml@$standards_sha"
    yq -o=json '.jobs' "$WF_DIR/$workflow.yml" | jq -e --arg expected "$expected" '
        [.[].uses | select(. != null)] == [$expected]
    ' >/dev/null || fail "$workflow must call $expected"
done

# Reusable-workflow records still use a SHA ref. The symbolic-ref requirement
# applies to action leaves, so do not reject this intentional exception.
jq -e --arg standards "$STANDARDS" --arg sha "$standards_sha" '
    .dependencies[$standards]
    | .ref == $sha and .commit == ("sha1-" + $sha)
      and .owner_id == 6759885 and .repo_id == 1116521501
      and (.uses | type == "array" and length > 0)
' "$FIXTURE/lock.json" >/dev/null || fail "standards lost its SHA binding or repository identity"
echo "PASS: six standards callers share a locked SHA and the correct reusable paths"

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

    # Any full SHA ref is refused, even one unrelated to the commit, and hex
    # case must not bypass the check (including mixed case).
    sha=${key##*@}
    for bad_ref in "$sha" "${sha^^}" 'aBcDeF0123456789aBcDeF0123456789aBcDeF01' \
        '0000000000000000000000000000000000000000' ""; do
        jq --arg key "$key" --arg ref "$bad_ref" '
            .dependencies[$key].ref = $ref
        ' "$FIXTURE/lock.json" > "$FIXTURE/mutated.json"
        if pinned_record "$key" "$FIXTURE/mutated.json"; then
            fail "$key accepted the refused ref '$bad_ref'"
        fi
    done

    # Missing and non-string metadata must not masquerade as a symbolic ref.
    # jq may report a type error for these inputs; either way the gate must
    # reject the record rather than treating its truthiness as a valid pin.
    for bad_ref in null false 42 '[]' '{}'; do
        jq --arg key "$key" --argjson ref "$bad_ref" '
            .dependencies[$key].ref = $ref
        ' "$FIXTURE/lock.json" > "$FIXTURE/mutated.json"
        if pinned_record "$key" "$FIXTURE/mutated.json" 2> "$FIXTURE/ref.err"; then
            fail "$key accepted a non-string ref $bad_ref"
        fi
    done
    jq --arg key "$key" 'del(.dependencies[$key].ref)' \
        "$FIXTURE/lock.json" > "$FIXTURE/mutated.json"
    if pinned_record "$key" "$FIXTURE/mutated.json" 2> "$FIXTURE/ref.err"; then
        fail "$key accepted a missing ref"
    fi

    # A valid-looking, different SHA is still a broken key/commit binding.
    jq --arg key "$key" '
        .dependencies[$key].commit = "sha1-0000000000000000000000000000000000000000"
    ' "$FIXTURE/lock.json" > "$FIXTURE/mutated.json"
    if pinned_record "$key" "$FIXTURE/mutated.json"; then
        fail "$key accepted a mismatched commit"
    fi

    # A raw SHA, absent value, or JSON null cannot replace the sha1- binding.
    for bad_commit in "\"$sha\"" null false '""'; do
        jq --arg key "$key" --argjson commit "$bad_commit" '
            .dependencies[$key].commit = $commit
        ' "$FIXTURE/lock.json" > "$FIXTURE/mutated.json"
        if pinned_record "$key" "$FIXTURE/mutated.json"; then
            fail "$key accepted an invalid commit $bad_commit"
        fi
    done
    jq --arg key "$key" 'del(.dependencies[$key].commit)' \
        "$FIXTURE/lock.json" > "$FIXTURE/mutated.json"
    if pinned_record "$key" "$FIXTURE/mutated.json"; then
        fail "$key accepted a missing commit"
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

    # Some actions also have direct tag users (notably Pages' cache and Code
    # Quality's editorconfig checker). Their tag and SHA records must coexist
    # with identical commits and repository identities.
    if [[ "$action" == actions/cache || "$action" == actions/checkout \
        || "$action" == actions/upload-artifact \
        || "$action" == editorconfig-checker/action-editorconfig-checker \
        || "$action" == erlef/setup-beam || "$action" == oven-sh/setup-bun ]]; then
        jq -e --arg key "$key" --arg alias "$action@$tag_ref" --arg tag "$tag_ref" '
            .dependencies[$alias].ref == $tag
            and (.dependencies[$alias].commit == .dependencies[$key].commit)
            and (.dependencies[$alias].owner_id == .dependencies[$key].owner_id)
            and (.dependencies[$alias].repo_id == .dependencies[$key].repo_id)
            and ([.workflows[][] | select(. == $alias)] | length > 0)
        ' "$FIXTURE/lock.json" >/dev/null || fail "$action lost its separate referenced tag record"
    fi

    checked=$((checked + 1))
    echo "PASS: $action SHA binding, identity, negative controls and closure"
done <<'CASES'
actions/cache|v6.1.0|44036562|215566462
actions/checkout|v7.0.1|44036562|197814629
actions/upload-artifact|v7.0.2|44036562|192625955
denoland/setup-deno|v2.0.5|42048915|356423100
dtolnay/rust-toolchain|v1|1940490|260749683
editorconfig-checker/action-editorconfig-checker|v3.0.0|26415196|297874902
erlef/setup-beam|v1.24.1|47606891|331103973
goto-bus-stop/setup-zig|v2.2.1|1006268|212984112
ossf/scorecard-action|v2.4.4|67707773|421101922
oven-sh/setup-bun|v2.2.0|108928776|512644635
swatinem/rust-cache|v2.9.2|580492|298565987
webfactory/ssh-agent|v0.10.0|135788|208510314
CASES

[[ "$checked" == 12 ]] || fail "expected to check all twelve changed dependency records"
echo "PASS: actions.lock SHA-ref regression controls ($checked dependencies)"
