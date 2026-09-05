#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")/.."

python3 scripts/check_construction.py
lake build
