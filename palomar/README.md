# Files for a possible Palomar submission

No submission to [Palomar](https://github.com/mathlib-initiative) is planned. These files are kept in case that changes, and
`comparator.json` is also useful on its own.

- `comparator.json` runs Comparator on the main theorems, with `MainResults` as both the challenge and the solution. Run it,
  with con-ron as the third kernel, after `lake build`:

  ```
  scripts/check_kernels.sh palomar/comparator.json
  ```

  This checks the closure of each theorem under Lean's kernel, NanoDa and con-ron, and rejects `sorryAx`. It does not compare a
  separate statement file with a proof, which is what Palomar's Challenge and Solution are for.
- `formalization.yaml` is the project's metadata, with the statements aligned to the `TreeOfBlobs.*` theorems of `src/MainResults.lean`.

A submission would still need:

1. A Challenge that imports only Mathlib, with the definitions that its statements use in a block of its own, and the bridges
   from them to the library's definitions. The last such file, with `scripts/sync_challenge_defs.py`, which kept its block equal to
   the library's, and `scripts/gen_solution.py`, which generated the Solution from it, is in the git history at `f838ea4`.
2. A Solution that restates those theorems and proves them from the libraries, and a `comparator.json` that names the two modules.
3. These two files at the root of the repository, with `formalization.yaml` pointing at the new modules.
