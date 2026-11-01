#!/usr/bin/env bash
# Check the main theorems under the three kernels that Palomar uses, after `lake build`: Comparator runs
# Lean's kernel and NanoDa, and con-ron checks an export of the same theorems. All three reject any axiom
# outside the three standard ones.
# The module and the theorems come from the Comparator configuration, by default palomar/comparator.json.
set -u

config=${1:-palomar/comparator.json}
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

module=$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["solution_module"])' "$config")
mapfile -t theorems < <(python3 -c 'import json, sys; print("\n".join(json.load(open(sys.argv[1]))["theorem_names"]))' "$config")
echo "Module $module, ${#theorems[@]} theorems: ${theorems[*]}"

status=0
echo "== Lean's kernel and NanoDa, through Comparator"
lake env lake comparator --config="$config" || status=1

echo "== con-ron"
if lake env leanexport "$module" -- "${theorems[@]}" >"$out/main.ndjson"; then
  lake env con-ron "$out/main.ndjson" || status=1
else
  echo "export failed"
  status=1
fi

if [ "$status" -ne 0 ]; then
  echo "FAILED"
  exit 1
fi
echo "All three kernels accepted ${#theorems[@]} theorems of $module."
