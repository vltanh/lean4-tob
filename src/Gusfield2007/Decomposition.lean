module

public import Gusfield2007.Blobs
public import Gusfield2007.SuperCharacters
public import External.GusfieldEtAl2004.SameBlob

/-!
# Gusfield et al. 2007, Sections 2.3, 3.4, 3.5: the Decomposition Theorem

The construction that inflates a node of `T̄` to a blob, Theorem 1 and its converse, the analogue with a given ancestral
sequence, Theorem 3, and the fact that the minima are over nonempty sets.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

universe u

variable {ι : Type u}

/-- **Line 299** (`g:inflate`). "Any super-character in `M` that is associated with `C` can be derived from `S(C)` using at
most one mutation per site, if an unlimited number of recombination nodes are allowed. This is true even if only
single-crossovers are allowed, or if multiple-crossovers are permitted. So, each central-star node `v` can be inflated into a
blob `b_v` containing one node labeled by each super-character in `M(C)`, and other nodes if needed."

Here the sites `κ` are those of `C`, at least two (a non-trivial component), `T` the super-characters, `S₀` the ancestral
sequence, in any crossover model. The network has the ancestral sequence at the root; it derives `T`, so that each element
of `T` labels a leaf, and no other leaf exists, which would become a row; every arc is on a cycle, so that all the sites are on
it; and there's exactly one blob. So it's what's needed to replace a node of `T̄`, with the edge of `T̄` for each super-character
out of its leaf, and the entering edge into the root. The leaves are recombination nodes, since every arc is on a cycle. -/
theorem inflate {κ : Type u} [LinearOrder κ] [Fintype κ] (c : Crossover) (hκ : 2 ≤ Fintype.card κ)
    (T : Finset (κ → Bool)) (hT : T.Nonempty) (S₀ : κ → Bool) :
    ∃ (a b : ℕ) (N : Network κ (Fin a) (Fin b)), N.Obeys c ∧ N.ancestral = S₀ ∧ N.Derives T ∧
      (∀ e, N.OnCycle e) ∧ ∃! B, N.IsBlob B := by
  sorry

variable [LinearOrder ι] [Finite ι]

/-- The minimum `R c M` is over a nonempty set when `M` is nonempty. So `sInf` is the minimum of the paper. -/
theorem recombSet_nonempty (c : Crossover) {M : Finset (ι → Bool)} (hM : M.Nonempty) :
    {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.recombCount = k}.Nonempty := by
  sorry

/-- The minimum `RS c S M` is over a nonempty set when `M` is nonempty. -/
theorem rootedRecombSet_nonempty (c : Crossover) (S : ι → Bool) {M : Finset (ι → Bool)} (hM : M.Nonempty) :
    {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.recombCount = k}.Nonempty := by
  sorry

/-- `R¹_S(M(C_k)) ≥ R¹(M(C_k))` (line 608), and in general `R(M) ≤ R_S(M)`. -/
theorem R_le_RS (c : Crossover) (S : ι → Bool) {M : Finset (ι → Bool)} (hM : M.Nonempty) : R c M ≤ RS c S M := by
  obtain ⟨a, b, N, h₁, h₂, -, h₄⟩ := Nat.sInf_mem (rootedRecombSet_nonempty c S hM)
  exact Nat.sInf_le ⟨a, b, N, h₁, h₂, h₄⟩

/-- Multiple crossovers are no constraint: `R(M) ≤ R¹(M)`. -/
theorem R_multiple_le (c : Crossover) {M : Finset (ι → Bool)} (hM : M.Nonempty) : R .multiple M ≤ R c M := by
  obtain ⟨a, b, N, -, h₂, h₃⟩ := Nat.sInf_mem (recombSet_nonempty c hM)
  exact Nat.sInf_le ⟨a, b, N, trivial, h₂, h₃⟩

/-- **Theorem 1** (`g:thm1`), the Decomposition Theorem. "Let `G(M)` be the incompatibility graph for `M`. Then, there is a
phylogenetic network that derives `M` where every blob contains all and only the sites of a single non-trivial connected
component of `G(M)`, and every compatible site is on a tree edge. The result holds no matter what constraints, if any, are
placed on the number of crossovers allowed at a recombination node" (line 173).

The hypothesis that `M` is nonempty is implicit in the paper: a network has a leaf. The standing assumption isn't needed for
truth (a constant column can go on an arc out of a root of degree one), but `T̄` is built under it. -/
theorem theorem1 (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧
      N.IsFullyDecomposedFor (incompatGraph M) := by
  sorry

/-- **Line 178** (`g:fd_iff`). The second wording of Theorem 1: "the blobs are in one-one correspondence with the non-trivial
connected components of `G(M)`, and if `b_C` is the blob corresponding to component `C`, then `b_C` contains all and only the
sites in `C`". It's equivalent to `IsFullyDecomposedFor`, granted that each non-trivial component is on a blob, which is the
converse below. -/
theorem isFullyDecomposedFor_iff_correspondence {V E : Type*} (N : Network ι V E) (G : SimpleGraph ι)
    (hG : ∀ c : G.ConnectedComponent, c.supp.Nontrivial → ∃ B, N.IsBlob B ∧ ∀ i ∈ c.supp, N.site i ∈ B) :
    N.IsFullyDecomposedFor G ↔ N.BlobCorrespondence G ∧ N.BlobsNodeDisjoint := by
  sorry

omit [LinearOrder ι] [Finite ι] in
/-- A non-trivial connected component of a graph whose edges join sites on one blob is on one blob. -/
theorem Network.exists_isBlob_of_reachable {V E : Type*} (N : Network ι V E) {G : SimpleGraph ι}
    (hG : ∀ i j, G.Adj i j → ∃ B, N.IsBlob B ∧ N.site i ∈ B ∧ N.site j ∈ B)
    (c : G.ConnectedComponent) (hc : c.supp.Nontrivial) :
    ∃ B, N.IsBlob B ∧ ∀ i ∈ c.supp, N.site i ∈ B := by
  obtain ⟨i₀, hi₀, i₁, hi₁, hne⟩ := hc
  have hr : G.Reachable i₀ i₁ := SimpleGraph.ConnectedComponent.eq.1 (hi₀.trans (Eq.symm hi₁))
  obtain ⟨p⟩ := hr
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ j _ hj _ =>
    obtain ⟨B, hB, h₀, -⟩ := hG _ _ hj
    refine ⟨B, hB, fun i hi => ?_⟩
    have hr' : G.Reachable i₀ i := SimpleGraph.ConnectedComponent.eq.1 (hi₀.trans (Eq.symm hi))
    clear hi
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr'
    induction hr' with
    | refl => exact h₀
    | @tail u w _ huw ih =>
      obtain ⟨B', hB', h₁, h₂⟩ := hG _ _ huw
      have : B = B' := hB.eq_of_inter_nonempty hB' ⟨N.site u, ih, h₁⟩
      exact this ▸ h₂

omit [LinearOrder ι] [Finite ι] in
/-- **Lines 182 to 185** (`g:converse`). "In any phylogenetic network that derives `M`, all sites from the same non-trivial
connected component of `G(M)` must appear on the same blob, and this does not depend on the number of crossovers used at
recombination node." The paper cites this from Gusfield et al. 2004b as easy. -/
theorem converse {V E : Type*} [Finite V] [Finite E] (N : Network ι V E) {M : Finset (ι → Bool)} (hN : N.Derives M)
    (c : (incompatGraph M).ConnectedComponent) (hc : c.supp.Nontrivial) :
    ∃ B, N.IsBlob B ∧ ∀ i ∈ c.supp, N.site i ∈ B :=
  N.exists_isBlob_of_reachable (fun _ _ h => GusfieldEtAl2004.exists_isBlob_of_incompatible N
    (fun _ hr => by
      obtain ⟨v, -, hv⟩ := hN.surjOn hr
      exact ⟨v, hv⟩) h) c hc

omit [LinearOrder ι] [Finite ι] in
/-- **Line 190** (`g:converse_rooted`). "No further decomposition is possible": the converse for `G_S(M)`, for a network with
ancestral sequence `S`. -/
theorem converse_rooted {V E : Type*} [Finite V] [Finite E] (N : Network ι V E) {M : Finset (ι → Bool)} {S : ι → Bool}
    (hN : N.Derives M) (hS : N.ancestral = S) (c : (conflictGraph S M).ConnectedComponent)
    (hc : c.supp.Nontrivial) : ∃ B, N.IsBlob B ∧ ∀ i ∈ c.supp, N.site i ∈ B :=
  N.exists_isBlob_of_reachable (fun _ _ h => GusfieldEtAl2004.exists_isBlob_of_incompatible N
    (L := addRow M S)
    (fun r hr => by
      rcases mem_addRow.1 hr with rfl | hr
      · exact ⟨N.root, hS⟩
      · obtain ⟨v, -, hv⟩ := hN.surjOn hr
        exact ⟨v, hv⟩)
    ((conflict_iff_incompatible_addRow S M _ _).1 h)) c hc

/-- **Line 178**, second wording, for Theorem 1. -/
theorem theorem1_correspondence (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧
      N.BlobCorrespondence (incompatGraph M) := by
  obtain ⟨a, b, N, h₁, h₂, h₃⟩ := theorem1 c M hM hC
  exact ⟨a, b, N, h₁, h₂, ((isFullyDecomposedFor_iff_correspondence N _ (converse N h₂)).1 h₃).1⟩

/-- **Line 187** (`g:thm1_rooted`). "There is an analogous theorem to Theorem 1 in the case that the ancestral sequence `S` is
known in advance. In that case, there is a phylogenetic network that derives `M`, with ancestral sequence `S`, where the blobs
are in one-one correspondence with the non-trivial connected components of `G_S(M)`, and any non-conflicting site is on a
tree edge". -/
theorem theorem1_rooted (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.IsFullyDecomposedFor (conflictGraph S M) := by
  sorry

/-- **Theorem 3** (`g:thm3`). "For any sequence `S`, there is a fully-decomposed phylogenetic network for `M` with ancestral
sequence `S`, containing exactly `Σ_{C ∈ G_S(M)} R_{S(C)}(M(C))` recombination nodes when multiple-crossover recombination is
allowed, and containing exactly `Σ_{C ∈ G_S(M)} R¹_{S(C)}(M(C))` recombination nodes when only single-crossover recombination
is allowed" (line 316).

A note for the proof, which the paper leaves at "the proof of Theorem 1, when applied to `M + S`". An optimal network for
`M(C)` has one blob when `C` is non-trivial, by the converse and because a blob with no site has the same label on all its
nodes, so that an arc can be dropped. Its other arcs carry no site, and can be contracted. Each row of `M(C)` labels a leaf, by
`Derives`, and that leaf gets the edge of `T̄` for that super-character; a recombination leaf gets an outgoing arc. The node
of `T̄` where `S` sits isn't a centre `v_C`, since a centre has no row. So each blob has an entering edge, attached at its top. -/
theorem theorem3 (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.IsFullyDecomposedFor (conflictGraph S M) ∧
      N.recombCount = ∑ᶠ C : (conflictGraph S M).ConnectedComponent,
        RS c (C.supp.domRestrict S) (restrictRows C.supp M) := by
  sorry

end Gusfield2007
