#!/usr/bin/env bash
# Write logs/<Item>-build.log and logs/<Item>-print-axioms.log.
# No argument records every item in checks/PrintAxioms.lean.
# An item argument records only that item, so a parallel branch does not
# rewrite the other items' logs.
set -eu
cd "$(dirname "$0")/.."

args=("$@")
if python3 -c 'import sys; raise SystemExit(0 if sys.version_info[0] == 3 else 1)' >/dev/null 2>&1; then
  py=(python3)
elif python -c 'import sys; raise SystemExit(0 if sys.version_info[0] == 3 else 1)' >/dev/null 2>&1; then
  py=(python)
elif py -3 -c 'import sys; raise SystemExit(0 if sys.version_info[0] == 3 else 1)' >/dev/null 2>&1; then
  py=(py -3)
else
  echo "python is required" >&2
  exit 1
fi

exec "${py[@]}" checks/item_logs.py "${args[@]}"
