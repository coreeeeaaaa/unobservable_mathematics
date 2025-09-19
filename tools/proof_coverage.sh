#!/usr/bin/env bash
set -euo pipefail

SRC="lean/src"
if [ ! -d "$SRC" ]; then
  echo "error: source dir not found: $SRC" >&2
  echo "defs=0"; echo "theorems=0"; echo "sorry=0"; echo "status=SORRY_FREE"
  exit 0
fi

# grep 실패(매치 없음) 시 set -e 때문에 죽지 않도록 || true
defs=$(grep -R -E "^\s*def\s+"          -n "$SRC" | wc -l | tr -d ' ' || true)
thms=$(grep -R -E "^\s*(theorem|lemma)\s+" -n "$SRC" | wc -l | tr -d ' ' || true)
sry=$(grep -R "sorry"                    -n "$SRC" | wc -l | tr -d ' ' || true)

# 숫자 보정
defs=${defs:-0}; thms=${thms:-0}; sry=${sry:-0}

echo "defs=${defs}"
echo "theorems=${thms}"
echo "sorry=${sry}"
if [ "$sry" -gt 0 ]; then
  echo "status=INCOMPLETE"
else
  echo "status=SORRY_FREE"
fi