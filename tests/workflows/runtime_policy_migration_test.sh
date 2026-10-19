#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# PR #13: both validators must require governance in place of runtime-policy.
# Exercise the real scripts against an isolated repository, including negative
# controls. The template validator treats missing workflows as errors; the
# workflow validator reports them as recommendations and still exits zero.
# Usage: bash tests/workflows/runtime_policy_migration_test.sh
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
fixture="$scratch/repository with spaces"
workflows="$fixture/.github/workflows"

fail() {
    echo "FAIL: $*" >&2
    for log in "$scratch/template.log" "$scratch/workflows.log"; do
        if [[ -f "$log" ]]; then cat "$log" >&2; fi
    done
    exit 1
}

# Supply the unrelated structure checks with a minimal complete repository.
# Copy the real deed readers so an early setup error cannot look like the
# expected rejection of a missing governance workflow.
mkdir -p "$workflows" "$fixture/.machine_readable" "$fixture/scripts" \
    "$fixture/src/interface/Abi" "$fixture/src/interface/ffi/src" \
    "$fixture/src/interface/ffi/test" "$fixture/src/interface/generated/abi" \
    "$fixture/docs/developer" "$fixture/docs/governance"
cp "$repo/scripts/deed-field.sh" "$repo/scripts/check-no-a2ml.sh" "$fixture/scripts/"
cat > "$fixture/fixture_chora.deed" <<'DEED'
(repo-deed
  (status :phase active)
  (maturity :level experimental)
  (meta :type library)
  (ecosystem :project "fixture")
  (anchor :purpose "workflow validation fixture")
  (policies (maintenance-axes :corrective-first #t)))
DEED
for file in README.adoc EXPLAINME.adoc LICENSE Justfile AUDIT.adoc \
    TOPOLOGY.adoc CONTRIBUTING.md docs/developer/ABI-FFI-README.adoc \
    src/interface/Abi/Types.idr src/interface/Abi/Layout.idr \
    src/interface/Abi/Foreign.idr src/interface/abi.ipkg \
    src/interface/ffi/build.zig src/interface/ffi/src/main.zig \
    src/interface/ffi/test/integration_test.zig; do
    printf '%s\n' '# SPDX-License-Identifier: MPL-2.0' > "$fixture/$file"
done

# Compiler calls are outside this regression's scope. Bash functions keep the
# test independent of locally installed compilers and create no build outputs.
zig() { [[ $# == 1 && $1 == build ]]; }
idris2() { [[ $# == 2 && $1 == --typecheck && $2 == src/interface/abi.ipkg ]]; }
export -f zig idris2

write_workflow() {
    printf '%s\n' '# SPDX-License-Identifier: MPL-2.0' 'name: Fixture' > "$1"
}

# Keep the fixture's contract independent of the validators' arrays: deriving
# it from their implementation would also copy a regressed requirement.
for workflow in hypatia-scan codeql scorecard quality mirror instant-sync \
    guix-policy security-policy wellknown-enforcement workflow-linter \
    governance secret-scanner; do
    write_workflow "$workflows/$workflow.yml"
done
cp "$workflows/governance.yml" "$scratch/governance.yml"

run_case() {
    local label=$1 governance_present=$2 template_status=0 workflow_status=0
    local validators=${3:-both}
    local expected_status=0 expected_errors=0
    if [[ "$governance_present" == no ]]; then
        expected_status=1
        expected_errors=1
    fi

    # Verbose mode exposes which required workflow was actually resolved.
    bash "$repo/scripts/validate-template.sh" "$fixture" 1 \
        > "$scratch/template.log" 2>&1 || template_status=$?
    [[ "$template_status" == "$expected_status" ]] \
        || fail "$label: template validator exited $template_status, expected $expected_status"
    [[ $(grep -c 'ERROR' "$scratch/template.log" || true) == "$expected_errors" ]] \
        || fail "$label: template validator reported unrelated errors"

    if [[ "$governance_present" == yes ]]; then
        grep -Fq 'Workflow found: governance.yml' "$scratch/template.log" \
            || fail "$label: template validator did not recognize governance"
        grep -Fq 'Validation PASSED' "$scratch/template.log" \
            || fail "$label: template validator did not reach its passing summary"
    else
        grep -Fq 'Required workflow missing: governance.yml' "$scratch/template.log" \
            || fail "$label: template rejection did not identify governance"
        grep -Fq 'Validation FAILED' "$scratch/template.log" \
            || fail "$label: template validator did not reach its failing summary"
    fi
    if grep -Eq '(Required workflow missing:|Workflow found:) runtime-policy\.yml' \
        "$scratch/template.log"; then
        fail "$label: template validator still requires runtime-policy.yml"
    fi
    if [[ "$validators" == template ]]; then
        echo "PASS: $label (template validator)"
        return
    fi

    bash "$repo/tests/workflows/validate_workflows_test.sh" "$workflows" \
        > "$scratch/workflows.log" 2>&1 || workflow_status=$?
    [[ "$workflow_status" == 0 ]] \
        || fail "$label: workflow recommendations unexpectedly failed validation"
    grep -Fq 'Workflow validation PASSED' "$scratch/workflows.log" \
        || fail "$label: workflow validator did not reach its summary"

    if [[ "$governance_present" == yes ]]; then
        grep -Fq 'Found: governance.yml' "$scratch/workflows.log" \
            || fail "$label: workflow validator did not recognize governance"
        if grep -Fq 'Missing: governance.yml' "$scratch/workflows.log"; then
            fail "$label: workflow validator also reported governance missing"
        fi
    else
        grep -Fq 'Missing: governance.yml' "$scratch/workflows.log" \
            || fail "$label: workflow validator did not recommend governance"
        if grep -Fq 'Found: governance.yml' "$scratch/workflows.log"; then
            fail "$label: workflow validator accepted a substitute for governance"
        fi
    fi

    if grep -Eq '(Missing:|Found:) runtime-policy\.yml' "$scratch/workflows.log"; then
        fail "$label: workflow validator still requires runtime-policy.yml"
    fi
    echo "PASS: $label (both validators)"
}

run_case 'governance alone satisfies the migrated requirement' yes

rm "$workflows/governance.yml"
run_case 'neither workflow leaves governance missing' no

write_workflow "$workflows/runtime-policy.yml"
run_case 'legacy runtime policy cannot substitute for governance' no

cp "$scratch/governance.yml" "$workflows/governance.yml"
run_case 'governance is recognized when a legacy workflow is also present' yes

rm "$workflows/runtime-policy.yml" "$workflows/governance.yml"
mkdir "$workflows/governance.yml"
# The workflow validator's generic scan also treats named directories as
# malformed YAML files; isolate this presence boundary to template validation.
run_case 'a directory named governance.yml is not a workflow file' no template
rmdir "$workflows/governance.yml"

cp "$scratch/governance.yml" "$workflows/governance.yaml"
run_case 'governance.yaml does not satisfy the required governance.yml path' no
rm "$workflows/governance.yaml"

cp "$scratch/governance.yml" "$workflows/governance.yml"
run_case 'restoring governance restores passing validation' yes
