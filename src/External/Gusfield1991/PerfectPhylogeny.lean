module

public import Gusfield2007.Defs

/-!
# The Perfect Phylogeny Theorem (Gusfield 1991)

Stated with `sorry`. See the `README.md` of this directory.
-/

@[expose] public section

open scoped Classical

namespace Gusfield1991

open Gusfield2007

/-- **The Perfect Phylogeny Theorem** (`ext:perfect_phylogeny`), for a matrix `A` with rows `X` and no constant column: it has a perfect phylogeny
exactly when no two columns contain all four pairs of states. -/
theorem exists_isPerfectPhylogeny_iff {X κ : Type*} [Finite X] [Nonempty X] [Finite κ] (A : X → κ → Bool)
    (hA : ∀ k, ∃ x y, A x k ≠ A y k) :
    (∃ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : X → Fin n) (edge : κ → Sym2 (Fin n)), IsPerfectPhylogeny T φ A edge) ↔
      ∀ k l, ∃ a b, ∀ x, ¬ (A x k = a ∧ A x l = b) := by
  sorry

variable {ι : Type*} [Finite ι]

/-- **The Perfect Phylogeny Theorem**, in the terms of Gusfield et al. 2007, line 154: a network with no recombination
derives `M` exactly when no two columns of `M` are incompatible. -/
theorem exists_network_iff (M : Finset (ι → Bool)) (hM : M.Nonempty) :
    (∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), (∀ x, ¬ N.IsRecomb x) ∧ N.Derives M) ↔
      ∀ i j, ¬ Incompatible M i j := by
  sorry

/-- **The Perfect Phylogeny Theorem**, rooted, in the terms of Gusfield et al. 2007, line 156: a network with no
recombination derives `M` with ancestral sequence `S` exactly when no two columns conflict relative to `S`. -/
theorem exists_network_rooted_iff (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty)
    (hC : NoConstantColumn (addRow M S)) :
    (∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), (∀ x, ¬ N.IsRecomb x) ∧ N.Derives M ∧ N.ancestral = S) ↔
      ∀ i j, ¬ Conflict S M i j := by
  sorry

end Gusfield1991
