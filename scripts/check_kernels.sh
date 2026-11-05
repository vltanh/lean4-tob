#!/usr/bin/env bash
# Check the main theorems under the three kernels that Palomar uses, after `lake build`: Comparator runs
# Lean's kernel and NanoDa, and con-ron checks an export of the same theorems. All three reject any axiom
# outside the three standard ones.
# The module and the theorems come from Comparator configurations: by default those of the entries in
# papers/*/palomar/comparator.json, one per paper, or the files given as arguments.
set -u

if [ "$#" -gt 0 ]; then
  configs=("$@")
else
  configs=(papers/*/palomar/comparator.json)
fi
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

failed=()
total=0
for config in "${configs[@]}"; do
  module=$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["solution_module"])' "$config")
  mapfile -t theorems < <(python3 -c 'import json, sys; print("\n".join(json.load(open(sys.argv[1]))["theorem_names"]))' "$config")
  echo "== $config: module $module, ${#theorems[@]} theorems: ${theorems[*]}"

  status=0
  echo "-- Lean's kernel and NanoDa, through Comparator"
  lake env lake comparator --config="$config" || status=1

  echo "-- con-ron"
  if lake env leanexport "$module" -- "${theorems[@]}" >"$out/main.ndjson"; then
    lake env con-ron "$out/main.ndjson" || status=1
  else
    echo "export failed"
    status=1
  fi

  if [ "$status" -ne 0 ]; then
    failed+=("$config")
  else
    echo "All three kernels accepted ${#theorems[@]} theorems of $module."
    total=$((total + ${#theorems[@]}))
  fi
done

if [ "${#failed[@]}" -ne 0 ]; then
  echo "FAILED: ${failed[*]}"
  exit 1
fi
echo "All three kernels accepted the $total theorems of ${#configs[@]} entries."
