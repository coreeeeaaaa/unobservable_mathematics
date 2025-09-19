#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
cd lean
lake build
cd ..
bash tools/proof_coverage.sh | tee proof_coverage.txt