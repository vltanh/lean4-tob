# Files for possible Palomar submissions

No submission to [Palomar](https://github.com/mathlib-initiative) is planned. These files are kept in case that changes, and the
Comparator configurations are also useful on their own.

There is one entry per paper, each in its own folder, on the module of that paper's main theorems:

| Entry | Main theorems | Report |
| --- | --- | --- |
| [`ECToBlob/`](ECToBlob) | [`src/MainResults/ECToBlob.lean`](../src/MainResults/ECToBlob.lean), with NANUQ and Legried et al. 2021 | [`docs/reports/ECToBlob.md`](../docs/reports/ECToBlob.md) |
| [`TOBQMC/`](TOBQMC) | [`src/MainResults/TOBQMC.lean`](../src/MainResults/TOBQMC.lean), with Ané et al. 2024, Huber et al. 2025, Dinh, Baños 2025, Kane, Tao 2017 | [`docs/reports/TOBQMC.md`](../docs/reports/TOBQMC.md) |
| [`TINNiK/`](TINNiK) | [`src/MainResults/TINNiK.lean`](../src/MainResults/TINNiK.lean), with Mitchell et al. 2019 and Studier, Keppler 1988 | [`docs/reports/TINNiK.md`](../docs/reports/TINNiK.md) |
| [`AllmanEtAl2023/`](AllmanEtAl2023) | [`src/MainResults/AllmanEtAl2023.lean`](../src/MainResults/AllmanEtAl2023.lean) | [`docs/reports/AllmanEtAl2023.md`](../docs/reports/AllmanEtAl2023.md) |
| [`Gusfield2007/`](Gusfield2007) | [`src/MainResults/Gusfield2007.lean`](../src/MainResults/Gusfield2007.lean), with the five sources that only it uses | [`docs/reports/Gusfield2007.md`](../docs/reports/Gusfield2007.md) |

Each folder has:

- `comparator.json`, which runs Comparator on the paper's main theorems, with its module as both the challenge and the solution.
  `scripts/check_kernels.sh` checks every entry, or the configurations it is given, after `lake build`:

  ```
  scripts/check_kernels.sh                                  # all five entries
  scripts/check_kernels.sh palomar/TINNiK/comparator.json   # one entry
  ```

  This checks the closure of each theorem under Lean's kernel, NanoDa and con-ron, and rejects `sorryAx`. One theorem, of
  Gusfield et al.'s entry, has a computation as a visible hypothesis, which this doesn't check. It does not compare a separate
  statement file with a proof, which is what Palomar's Challenge and Solution are for. `lake comparator`, `leanexport` and
  `con-ron` come from the toolchain under `lake env`.
- `formalization.yaml`, the entry's metadata, valid against the schema it names: the paper, the sources it cites, the statements
  aligned to the `TreeOfBlobs.*` theorems of its module, and its fidelity section, which lists every divergence from the paper.
  The paper's report has the details.

A submission of an entry would still need:

1. A Challenge that imports only Mathlib, with the definitions that its statements use in a block of its own, and the bridges
   from them to the library's definitions. The last such file, with `scripts/sync_challenge_defs.py`, which kept its block equal to
   the library's, and `scripts/gen_solution.py`, which generated the Solution from it, is in the git history at `f838ea4`, for the
   three papers of the time together.
2. A Solution that restates those theorems and proves them from the libraries, and a `comparator.json` that names the two modules.
3. These files at the root of the repository that holds the paper, with `formalization.yaml` pointing at the new modules.
