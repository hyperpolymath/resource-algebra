#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
# Run from any directory: bash tests/unit/resource_algebra_test.sh
# Mirrors scripts/check-agda.sh's proof flags and honors its AGDA override.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."
export LC_ALL="${LC_ALL:-C.UTF-8}"
prover="${AGDA:-agda}"
"$prover" --version
"$prover" --safe --without-K --no-libraries --ignore-interfaces --double-check \
  -i src -i tests/unit tests/unit/AllTests.agda
echo 'PASS: MinMax, morphism, and Prelude unit tests'

# Keep the expected failures in the existing harness, which verifies that
# they fail at their declarations rather than at parsing/import resolution.
bash scripts/check-agda.sh
