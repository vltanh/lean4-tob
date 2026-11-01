module

public import Gusfield2007.Structure
public import External.SempleSteel2003.SplitsEquivalence
public import External.Gusfield1991.PerfectPhylogeny

/-!
# Gusfield et al. 2007, Sections 3.2 and 3.3: super-characters, the matrix `B`, the tree `T̄`

Lemma 3, the existence and uniqueness of `T̄`, Lemma 4.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

variable {ι : Type*}

/-- **Line 283** (`g:char_unique`). "Every row in `B` has value 1 in exactly one column of `B(C)`". -/
theorem existsUnique_charValue_eq_true {M : Finset (ι → Bool)} (c : (incompatGraph M).ConnectedComponent) {r : ι → Bool}
    (hr : r ∈ M) : ∃! k : SuperChar M, k.1 = c ∧ charValue k r = true := by
  sorry

/-- **Line 281** (`g:four_chars`). "For any non-trivial connected component `C`, the submatrix `M(C)` contains at least
four distinct sequences". -/
theorem four_le_card_restrictRows {M : Finset (ι → Bool)} {c : (incompatGraph M).ConnectedComponent}
    (hc : c.supp.Nontrivial) : 4 ≤ (restrictRows c.supp M).card := by
  sorry

/-- **Lemma 3** (`g:lem3`). "No pair of characters of `B` are incompatible" (line 256). -/
theorem lemma3 (M : Finset (ι → Bool)) (p q : SuperChar M) : ¬ Incompatible (matrixB M) p q := by
  sorry

/-- **Line 264** (`g:tbar`). "Applying the Perfect Phylogeny Theorem, Lemma 3 establishes that there is a perfect phylogeny
`T̄` where each character of `B` labels one edge in `T̄`, and each edge is labeled by one or more characters of `B`". Each
edge here is each internal edge, by the reading of `IsTBar`.

A remark on line 271: "all columns in `B` are distinct" isn't so, since a trivial component gives two columns with one
bipartition, and columns from different components can have one bipartition. What the proof uses is that splits of edges
are distinct, which is a part of `IsTBar`. -/
theorem exists_isTBar [Finite ι] (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : M → Fin n) (edge : SuperChar M → Sym2 (Fin n)), IsTBar M T φ edge := by
  sorry

/-- **Lines 156, 344** (`g:tbar_unique`). `T̄` is unique: "the splits of an undirected tree uniquely define the tree". -/
theorem isTBar_unique {M : Finset (ι → Bool)} {W W' : Type*} [Finite ι] [Finite W] [Finite W'] (hM : M.Nonempty)
    {T : SimpleGraph W} {T' : SimpleGraph W'} {φ : M → W} {φ' : M → W'} {edge : SuperChar M → Sym2 W}
    {edge' : SuperChar M → Sym2 W'} (h : IsTBar M T φ edge) (h' : IsTBar M T' φ' edge') :
    ∃ f : T ≃g T', ∀ r, f (φ r) = φ' r := by
  sorry

/-- **Lemma 4** (`g:lem4`). "Let `C` be an arbitrary component of `G(M)`. In `T̄`, there is a node `v_C` such that all the
edges labeled by characters of `B` that originate from connected component `C`, are incident with `v_C`. [...] Further, `v_C`
is on the 0-side of each split defined by an edge labeled by a character of `B` that originates from `C`" (line 275).

For a trivial component, the paper keeps one of its two columns ("one column can be removed", line 245; "only one
character originates from `C`", line 281). Here both are kept, and they label one edge whose 0-sides are opposite, so the second
clause is for a non-trivial `C`. A trivial `C` has it for each of the columns, at one of the ends of the edge. -/
theorem lemma4 {M : Finset (ι → Bool)} {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W}
    {edge : SuperChar M → Sym2 W} (h : IsTBar M T φ edge) (c : (incompatGraph M).ConnectedComponent) :
    ∃ v, (∀ k : SuperChar M, k.1 = c → v ∈ edge k) ∧
      (c.supp.Nontrivial → ∀ k : SuperChar M, k.1 = c → ∀ r : M, charValue k r = true →
        ¬ SameSide T (edge k) (φ r) v) := by
  sorry

/-- **Line 277** (`g:vC_only`). The paper notes that "Lemma 4 does not assert that `v_C` is only incident with edges labeled by
characters that originate from `C`". It is so, for a non-trivial `C`: each other branch at `v_C` would have a leaf, which is on
the 1-side of an edge of the star by line 283, but on its 0-side since it's reached without crossing that edge. -/
theorem adj_center_labelled {M : Finset (ι → Bool)} {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W}
    {edge : SuperChar M → Sym2 W} (h : IsTBar M T φ edge) {c : (incompatGraph M).ConnectedComponent}
    (hc : c.supp.Nontrivial) {v : W} (hv : ∀ k : SuperChar M, k.1 = c → v ∈ edge k)
    (hv' : ∀ k : SuperChar M, k.1 = c → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v) {u : W}
    (hu : T.Adj v u) : ∃ k : SuperChar M, k.1 = c ∧ edge k = s(v, u) := by
  sorry

end Gusfield2007
