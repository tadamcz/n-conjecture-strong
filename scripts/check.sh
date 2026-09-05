#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")/.."

python3 scripts/check_construction.py
lake build
audit_output=$(lake env lean Audit.lean)
printf '%s\n' "$audit_output"
AUDIT_OUTPUT="$audit_output" python3 - <<'PY'
import os
import re

entries = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", os.environ["AUDIT_OUTPUT"])
expected = {
    "StrongFour.family_admissible",
    "StrongFour.no_uniform_bound",
    "StrongFour.conjecture_false",
    "StrongFour.qualityLimsup_ge",
    "StrongFour.qualityLimsup_ne_one",
}
assert {name for name, _ in entries} == expected
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in entries:
    assert {a.strip() for a in axioms.split(",") if a.strip()} <= allowed, (name, axioms)
print("Final theorem axiom audit: PASS")
PY
