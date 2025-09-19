#!/usr/bin/env bash
set -euo pipefail
SRC="src"
defs=$(grep -R -E "^\s*def\s+" -n ${SRC} | wc -l | tr -d ' ')
thms=$(grep -R -E "^\s*(theorem|lemma)\s+" -n ${SRC} | wc -l | tr -d ' ')
sry=$(grep -R "sorry" -n ${SRC} | wc -l | tr -d ' ')
echo "defs=${defs}"
echo "theorems=${thms}"
echo "sorry=${sry}"
if [ "$sry" -gt 0 ]; then echo "status=INCOMPLETE"; else echo "status=SORRY_FREE"; fi