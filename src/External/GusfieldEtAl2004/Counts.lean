module

public import External.GusfieldEtAl2004.ReducedUnrooted
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Operation counts for the algorithm of Gusfield, Eddhu, Langley 2004

Gusfield et al. 2007, line 180: a reduced galled tree "can be found in polynomial time". The source's algorithm is in its Sections 3 to 7, with the "overall time bound" `O(nm + n³)`. The algorithm that this repository computes is in `Algorithm.lean` and `Build.lean`, with its count. This module has the source's own steps at the source's costs, with no statement that they are right. No machine model is used. As in the counts of the other papers in this repository, each theorem counts what a step of the method enumerates, and says what each one costs in the source's terms.

What is proved with its correctness:

* the conflict graph is read from `m² n` entries (`incompatible_iff_pairsAt`, `card_reads`);
* when `M` has a galled tree, its value `R(M)` is the number of non-trivial components of that graph (`R_eq_card_cent`), so the value has this cost and no more needs to be constructed.

What is only counted, as the source's steps, with no statement that the steps are right:

* the Site-Arrangement Algorithm of Section 3.2 tries each distinct row of `M(C)` (`card_restrictRows_le`), for each non-trivial component, and these have at most `m` sites in all, and are at most `m / 2` (`sum_card_supp_le`, `two_mul_card_cent_le`);
* `galledTreeOperations` adds up the steps of Sections 3.2, 4 and 6, with a perfect phylogeny test at the cost `n |C|` that the source cites from Gusfield 1991. `galledTreeOperations_le` is the polynomial bound. These steps aren't the ones of `Build.lean`.

The source's `O(n³)` uses that a galled tree has at most `2n` distinct columns, which it cites from Wang et al. 2001, not read and not proved here. So the bound here is in `n` and `m`.
-/

@[expose] public noncomputable section

open scoped Classical

namespace GusfieldEtAl2004

open Gusfield2007 Gusfield2007.Decomp

variable {ι : Type*}

/-- The pairs of states at the sites `i`, `j` of the rows of `M`: one reading of each row. -/
def pairsAt (M : Finset (ι → Bool)) (i j : ι) : Finset (Bool × Bool) := M.image fun r => (r i, r j)

/-- The test of the four gametes reads the pairs of states of the rows. -/
theorem incompatible_iff_pairsAt (M : Finset (ι → Bool)) (i j : ι) : Incompatible M i j ↔ ∀ a b, (a, b) ∈ pairsAt M i j := by
  simp only [Incompatible, pairsAt, Finset.mem_image, Prod.mk.injEq]

/-- The test for a conflict relative to `S` reads the pairs of states of the rows. -/
theorem conflict_iff_pairsAt (S : ι → Bool) (M : Finset (ι → Bool)) (i j : ι) : Conflict S M i j ↔ ∀ a b, (a ≠ S i ∨ b ≠ S j) → (a, b) ∈ pairsAt M i j := by
  simp only [Conflict, pairsAt, Finset.mem_image, Prod.mk.injEq]

/-- The conflict graph is read from `m² n` pairs of a row and two sites: "we next build the conflict graph" (Section 7 of the source). -/
theorem card_reads [Fintype ι] (M : Finset (ι → Bool)) : (Finset.univ ×ˢ Finset.univ ×ˢ M : Finset (ι × ι × (ι → Bool))).card = Fintype.card ι ^ 2 * M.card := by
  simp only [Finset.card_product, Finset.card_univ]
  ring

/-- The Site-Arrangement Algorithm tries "each distinct sequence in `M(C)`": at most one for each row of `M`. -/
theorem card_restrictRows_le (C : Set ι) (M : Finset (ι → Bool)) : (restrictRows C M).card ≤ M.card :=
  Finset.card_image_le

/-- The non-trivial components have at most `m` sites in all. -/
theorem sum_card_supp_le [Fintype ι] (G : SimpleGraph ι) [Fintype (Cent G)] : ∑ C : Cent G, Nat.card C.1.supp ≤ Fintype.card ι := by
  have hinj : Function.Injective fun x : Σ C : Cent G, C.1.supp => (x.2 : ι) := by
    rintro ⟨C, i, hi⟩ ⟨C', j, hj⟩ h
    obtain rfl : i = j := h
    have hCC : C = C' := Subtype.ext (hi.symm.trans hj)
    subst hCC
    rfl
  have : Finite (Σ C : Cent G, C.1.supp) := Finite.of_injective _ hinj
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := ι)] at hcard
  rw [← Nat.card_sigma]
  exact hcard

/-- Each non-trivial component has at least two sites, so there are at most `m / 2` of them, and so at most that many recombinations in a reduced galled tree. -/
theorem two_mul_card_cent_le [Fintype ι] (G : SimpleGraph ι) : 2 * Nat.card (Cent G) ≤ Fintype.card ι := by
  have : Finite G.ConnectedComponent := Finite.of_surjective G.connectedComponentMk fun c => c.exists_rep
  have : Fintype (Cent G) := Fintype.ofFinite _
  refine le_trans ?_ (sum_card_supp_le G)
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_le_sum fun C _ => ?_
  have hfin : C.1.supp.Finite := Set.toFinite _
  have h₂ := (Set.one_lt_ncard hfin).2 C.2
  rw [Nat.card_coe_set_eq]
  omega

/-- The steps of the algorithm of the source on `n` rows and `m` sites, in the number of entries of the matrix read: the conflict graph (`m² n`, Section 7); the arrangement of the galls, a perfect phylogeny test of cost `n |C|` for each of at most `n` rows, with `Σ |C| ≤ m`
(`n² m`, Section 3.2); the ancestry of the galls, up to six entries for each ordered pair of at most `m / 2` galls (`6 (m / 2)²`, Theorem 4.1); the node of each row, a traversal of the sites (`n m`, Phase 2 of Section 6); and a walk over the rows for each site (`m n`, Phase 3 of Section 6). -/
def galledTreeOperations (n m : ℕ) : ℕ := m ^ 2 * n + n ^ 2 * m + 6 * (m / 2) ^ 2 + n * m + m * n

/-- **The source's steps, counted** (`ext:galled_steps`): the steps listed in `galledTreeOperations` read at most `8 (n + m)³ + 2 (n + m)²` entries. This counts the steps; that they find a reduced galled tree isn't formalized: see the head of this file. -/
theorem galledTreeOperations_le (n m : ℕ) : galledTreeOperations n m ≤ 8 * (n + m) ^ 3 + 2 * (n + m) ^ 2 := by
  have h₁ : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
  have h₂ : 4 * (m / 2) ^ 2 ≤ m ^ 2 := by
    have : (2 * (m / 2)) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left h₁ 2
    linarith [show (2 * (m / 2)) ^ 2 = 4 * (m / 2) ^ 2 by ring]
  simp only [galledTreeOperations]
  nlinarith [h₂, Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2 * m), Nat.zero_le (n * m ^ 2), Nat.zero_le (m ^ 3), Nat.zero_le (n ^ 2), Nat.zero_le (n * m), Nat.zero_le (m ^ 2)]

end GusfieldEtAl2004
