#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Every SHA-keyed action record in actions.lock must carry a symbolic (tag)
# ref, with the SHA in its key and commit. GitHub's runner rejects a record
# whose ref is its own SHA ("invalid lockfile pin", enforced from 2026-10-15;
# standards#1271), so the SHA ref PR #7 asked for stopped every job that
# resolved such a record. The commit, not the ref, pins the action.
#
# No workflow may call a reusable from hyperpolymath/standards: the repository
# moved to metadatastician/standards, and a reusable `uses:` does not follow
# the rename ("workflow was not found"). Governance and the secret scanner
# check out the standards policy at a SHA pin instead.
# This test is offline.
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

# Folding runtime policy into governance must remove both the workflow and
# its lock entry. A valid, fully locked legacy workflow would pass sync alone.
[[ ! -e "$WF_DIR/runtime-policy.yml" && ! -L "$WF_DIR/runtime-policy.yml" ]] \
    || fail "runtime-policy.yml must remain folded into governance"
jq -e '.workflows | has(".github/workflows/runtime-policy.yml") | not' \
    "$FIXTURE/lock.json" >/dev/null || fail "runtime-policy.yml must not retain a lock entry"
echo "PASS: retired runtime-policy workflow and lock entry are absent"

# No job or step may name the moved repository, and the lock may not record
# it. Comments are not `uses:` values, so they do not trip this.
for workflow in "$WF_DIR"/*.yml; do
    yq -o=json '[.. | select(tag == "!!map" and has("uses")) | .uses]' "$workflow" \
        | jq -e '[.[] | select(type == "string" and startswith("hyperpolymath/standards/"))] | length == 0' \
            >/dev/null || fail "$(basename "$workflow") calls a reusable from the moved hyperpolymath/standards"
done
jq -e '[.dependencies | keys[] | select(startswith("hyperpolymath/standards"))] | length == 0' \
    "$FIXTURE/lock.json" >/dev/null || fail "actions.lock still records hyperpolymath/standards"
for workflow in governance secret-scanner; do
    yq -o=json '[.jobs[].steps[]? | select(.with.repository? == "metadatastician/standards") | .with.ref]' \
        "$WF_DIR/$workflow.yml" \
        | jq -e 'length > 0 and all(.[]; type == "string" and test("^[0-9a-f]{40}$"))' \
            >/dev/null || fail "$workflow must check out metadatastician/standards at a full SHA"
done
echo "PASS: no reusable from the moved standards; governance and secret scanner pin metadatastician/standards"

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

# The table must name every SHA-keyed record the lock holds, so a new record
# cannot escape these controls by not being listed.
jq -r '.dependencies | keys[] | select(test("@[0-9a-f]{40}$"))' "$FIXTURE/lock.json" \
    | sort > "$FIXTURE/locked.txt"

checked=0
: > "$FIXTURE/listed.txt"
while IFS='|' read -r key tag_ref owner_id repo_id alias; do
    echo "$key" >> "$FIXTURE/listed.txt"
    action=${key%@*}

    pinned_record "$key" "$FIXTURE/lock.json" \
        || fail "$key must have a symbolic ref and its own SHA as commit"
    # Another nonempty symbolic ref also passes pinned_record, but would no
    # longer identify the tag this record was locked at.
    jq -e --arg key "$key" --arg tag "$tag_ref" '
        .dependencies[$key].ref == $tag
    ' "$FIXTURE/lock.json" >/dev/null || fail "$key must retain its relocked tag $tag_ref"
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

    # Delete only this record, keeping its incoming workflow edges and all
    # other lock data intact. Preserve gh-actions-lock layout: the production
    # gate parses that layout, not yq's reformatted output.
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

    # Some actions also have direct tag users. Their tag and SHA records must
    # coexist with identical commits and repository identities.
    if [[ "$alias" == alias ]]; then
        jq -e --arg key "$key" --arg alias "$action@$tag_ref" --arg tag "$tag_ref" '
            .dependencies[$alias].ref == $tag
            and (.dependencies[$alias].commit == .dependencies[$key].commit)
            and (.dependencies[$alias].owner_id == .dependencies[$key].owner_id)
            and (.dependencies[$alias].repo_id == .dependencies[$key].repo_id)
            and ([.workflows[][] | select(. == $alias)] | length > 0)
        ' "$FIXTURE/lock.json" >/dev/null || fail "$action lost its separate referenced tag record"
    fi

    checked=$((checked + 1))
    echo "PASS: $key SHA binding, identity, negative controls and closure"
done <<'CASES'
actions/attest@508db95dd578ae2727ebd6217d5ba78e4fbda05d|v4.2.1|44036562|760701061|-
actions/cache@55cc8345863c7cc4c66a329aec7e433d2d1c52a9|v6.1.0|44036562|215566462|alias
actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1|v7.0.1|44036562|197814629|alias
actions/download-artifact@9000827ccba6bdab643e8b6fd33ac0654aef8333|v8.0.2|44036562|192626254|-
actions/upload-artifact@bbbca2ddaa5d8feaa63e36b76fdaad77386f024f|v7.0.0|44036562|192625955|-
actions/upload-artifact@cf430e030ddbb5b0abf93d22962f4752f3646cd9|v7.0.2|44036562|192625955|alias
dependabot/fetch-metadata@25dd0e34f4fe68f24cc83900b1fe3fe149efef98|v3.1.0|27347476|371068214|-
editorconfig-checker/action-editorconfig-checker@51f63319f592f97930c73d9c46184d20bd206393|v3.0.0|26415196|297874902|-
erlef/setup-beam@54075bcc5e249e4758d363f27d099f55d843f124|v1.24.1|47606891|331103973|-
github/codeql-action@9b3254085494b55a0f7c4c2b3d2d52cc712ce370|v4.39.1|9919|259445878|-
ossf/scorecard-action@fa7117db83c52d787ae5a89f350999701505d78e|v2.5.0|67707773|421101922|-
oven-sh/setup-bun@0c5077e51419868618aeaa5fe8019c62421857d6|v2.2.0|108928776|512644635|-
CASES

sort "$FIXTURE/listed.txt" | diff - "$FIXTURE/locked.txt" > "$FIXTURE/coverage.diff" \
    || { cat "$FIXTURE/coverage.diff" >&2; fail "the case table must list exactly the lock's SHA-keyed records"; }
[[ "$checked" -gt 0 ]] || fail "no SHA-keyed records were checked"
echo "PASS: actions.lock SHA-ref regression controls ($checked dependencies)"

# This regression gate already runs in Estate Rules CI. Include the validators'
# migration controls so requiring governance in place of runtime-policy cannot
# regress while the workflow and its lock entry still look correct.
bash "$REPO/tests/workflows/runtime_policy_migration_test.sh"
