module

public import Gusfield2007.Blobs
public import Gusfield2007.SuperCharacters
public import Gusfield2007.InflateNet
public import Gusfield2007.TBarFrame
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
out of its leaf, and the entering edge into the root. The leaves are recombination nodes, since every arc is on a cycle.

The paper gives no construction; the proof is the one of `Decomp.exists_inflate_net`, in the three models at once. -/
theorem inflate {κ : Type u} [LinearOrder κ] [Fintype κ] (c : Crossover) (hκ : 2 ≤ Fintype.card κ)
    (T : Finset (κ → Bool)) (hT : T.Nonempty) (S₀ : κ → Bool) :
    ∃ (a b : ℕ) (N : Network κ (Fin a) (Fin b)), N.Obeys c ∧ N.ancestral = S₀ ∧ N.Derives T ∧
      (∀ e, N.OnCycle e) ∧ ∃! B, N.IsBlob B :=
  Decomp.exists_inflate_net c (by omega) T hT S₀

variable [LinearOrder ι] [Finite ι]

/-- The network that replaces the centre of a non-trivial component `C` of `G(M)`, with ancestral sequence `S(C)`: "any super-character in `M` that is associated with `C` can be derived from `S(C)`" (line 299). It derives the other super-characters of `C`, which number at least three. -/
theorem exists_inflate_piece (c : Crossover) {M : Finset (ι → Bool)} (C : Decomp.Cent (incompatGraph M)) (S : ι → Bool) :
    ∃ (a b : ℕ) (N : Network C.1.supp (Fin a) (Fin b)), N.Obeys c ∧ N.ancestral = C.1.supp.domRestrict S ∧
      N.Derives ((restrictRows C.1.supp M).erase (C.1.supp.domRestrict S)) ∧ (∀ e, N.OnCycle e) ∧ ∃! B, N.IsBlob B := by
  have h₃ : ((restrictRows C.1.supp M).erase (C.1.supp.domRestrict S)).Nonempty := by
    have h₄ := four_le_card_restrictRows C.2
    have h₅ := Finset.pred_card_le_card_erase (s := restrictRows C.1.supp M) (a := C.1.supp.domRestrict S)
    rw [← Finset.card_pos]
    omega
  have : Fintype C.1.supp := Fintype.ofFinite _
  have hnt : Nontrivial C.1.supp := Set.nontrivial_coe_sort.2 C.2
  exact inflate c (Fintype.one_lt_card_iff_nontrivial.2 hnt) _ h₃ _

/-- The minimum `RS c S M` is over a nonempty set when `M` is nonempty. -/
theorem rootedRecombSet_nonempty (c : Crossover) (S : ι → Bool) {M : Finset (ι → Bool)} (hM : M.Nonempty) :
    {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.recombCount = k}.Nonempty := by
  have : Fintype ι := Fintype.ofFinite ι
  by_cases hι : IsEmpty ι
  · obtain ⟨a, b, N, hr, hd, hs, -⟩ := Gusfield1991.exists_network_of_no_conflict M S hM (fun i => hι.elim i) (fun i => hι.elim i)
    exact ⟨_, a, b, N, Network.obeys_of_tgt_injective (Network.tgt_injective_of_no_recomb hr) c, hd, hs, rfl⟩
  · have hcard : 1 ≤ Fintype.card ι := by
      rw [not_isEmpty_iff] at hι
      exact Fintype.card_pos
    obtain ⟨a, b, N, h₁, h₂, h₃, -, -⟩ := Decomp.exists_inflate_net c hcard M hM S
    exact ⟨_, a, b, N, h₁, h₃, h₂, rfl⟩

/-- The minimum `R c M` is over a nonempty set when `M` is nonempty. So `sInf` is the minimum of the paper. -/
theorem recombSet_nonempty (c : Crossover) {M : Finset (ι → Bool)} (hM : M.Nonempty) :
    {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.recombCount = k}.Nonempty := by
  obtain ⟨k, a, b, N, h₁, h₂, -, h₄⟩ := rootedRecombSet_nonempty c hM.choose hM
  exact ⟨k, a, b, N, h₁, h₂, h₄⟩

/-- `R¹_S(M(C_k)) ≥ R¹(M(C_k))` (line 608), and in general `R(M) ≤ R_S(M)`. -/
theorem R_le_RS (c : Crossover) (S : ι → Bool) {M : Finset (ι → Bool)} (hM : M.Nonempty) : R c M ≤ RS c S M := by
  obtain ⟨a, b, N, h₁, h₂, -, h₄⟩ := Nat.sInf_mem (rootedRecombSet_nonempty c S hM)
  exact Nat.sInf_le ⟨a, b, N, h₁, h₂, h₄⟩

/-- **Theorem 1**, the proof (`g:thm1`): the network of lines 299 to 303, for any sequence `S` as root and `T̄` built from `M + S`. Line 312 reuses this proof for the rooted
statements. The networks `P C` inflate the central nodes.

Line 299 selects any node of `T̄` as the root, and writes `S(C)` for the ancestral sequence of `v_C`. Three remarks on it: "`M(G)`" is a misprint for `G(M)`; when the root is `v_C`, its label is `0` on every character of `B` from `C`, by Lemma 4, so by our reading it gives no sequence on the sites of `C`, though line 416 says of this proof that "the label on v can be used for the ancestral sequence of b_v";
and the sentence on connecting edges uses the fact that line 277 doesn't assert, which is `adj_center_labelled`. Here the root is the row `S` of `M + S`, so that the case of a central root doesn't arise. If `S` is in `M`, the row needs its
own leaf (the root isn't one): a new leaf below the root, with no site. -/
theorem exists_network_of_pieces (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M)
    {a b : Decomp.Cent (incompatGraph (addRow M S)) → ℕ}
    (P : ∀ C : Decomp.Cent (incompatGraph (addRow M S)), Network C.1.supp (Fin (a C)) (Fin (b C)))
    (hob : ∀ C, (P C).Obeys c) (hanc : ∀ C, (P C).ancestral = C.1.supp.domRestrict S)
    (hder : ∀ C, (P C).Derives ((restrictRows C.1.supp (addRow M S)).erase (C.1.supp.domRestrict S)))
    (hP : ∀ C, (∃! B, (P C).IsBlob B) ∧ ∀ i, ∃ B, (P C).IsBlob B ∧ (P C).site i ∈ B) :
    ∃ (a' b' : ℕ) (N : Network ι (Fin a') (Fin b')), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.IsFullyDecomposedFor (incompatGraph (addRow M S)) ∧ N.recombCount = ∑ᶠ C, (P C).recombCount := by
  have hM' : (addRow M S).Nonempty := ⟨S, mem_addRow.2 (Or.inl rfl)⟩
  have hC' : NoConstantColumn (addRow M S) := hC.addRow S
  have hS : S ∈ addRow M S := mem_addRow.2 (Or.inl rfl)
  -- It's enough to have such a network on any finite types.
  suffices hmain : ∃ (V E : Type u) (_ : Finite V) (_ : Finite E) (N : Network ι V E), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.IsFullyDecomposedFor (incompatGraph (addRow M S)) ∧ N.recombCount = ∑ᶠ C, (P C).recombCount by
    obtain ⟨V, E, _, _, N, h₁, h₂, h₃, h₄, h₅⟩ := hmain
    obtain ⟨a', b', N', eV, eE, hiso⟩ := N.exists_fin_iso
    obtain ⟨i₁, i₂, i₃, i₄, i₅⟩ := hiso.invariants
    exact ⟨a', b', N', (i₂ c).2 h₁, (i₃ M).2 h₂, i₄.trans h₃, (i₅ _).2 h₄, i₁.trans h₅⟩
  by_cases hne : ∃ r ∈ addRow M S, r ≠ S
  · obtain ⟨n, T, φ, edge, h⟩ := exists_isTBar (addRow M S) hM' hC'
    obtain ⟨V, E, hV, hE, N, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h.exists_glued P hS hC' hanc hder hne
    by_cases hSM : S ∈ M
    · -- The row `S` gets a new leaf below the root.
      have hl : N.label N.root = S := h₂
      refine ⟨Option V, Option E, inferInstance, inferInstance, Decomp.addLeaf N N.root, Decomp.addLeaf_obeys (h₁ c hob), ?_, h₂,
        Decomp.addLeaf_fullyDecomposed (h₅ hP), Decomp.addLeaf_recombCount.trans h₆⟩
      have hd := Decomp.addLeaf_derives h₃ h₄ (by rw [hl]; simp)
      rwa [hl, addRow_eq_of_mem hSM, Finset.insert_erase hSM] at hd
    · refine ⟨V, E, hV, hE, N, h₁ c hob, ?_, h₂, h₅ hP, h₆⟩
      have heq : (addRow M S).erase S = M := Finset.erase_insert hSM
      rwa [heq] at h₃
  · -- All the rows are `S`, and so there are no sites.
    push Not at hne
    have hι : IsEmpty ι := by
      refine ⟨fun i => ?_⟩
      obtain ⟨r, hr, r', hr', hrr⟩ := hC i
      rw [hne r (mem_addRow.2 (Or.inr hr)), hne r' (mem_addRow.2 (Or.inr hr'))] at hrr
      exact hrr rfl
    obtain ⟨a', b', N, hr, hd, hs, -⟩ := Gusfield1991.exists_network_of_no_conflict M S hM (fun i => hι.elim i) (fun i => hι.elim i)
    have hcomp : IsEmpty (Decomp.Cent (incompatGraph (addRow M S))) := ⟨fun C => by
      obtain ⟨i, -⟩ := C.1.exists_rep
      exact hι.elim i⟩
    refine ⟨ULift (Fin a'), ULift (Fin b'), inferInstance, inferInstance, N.map Equiv.ulift.symm Equiv.ulift.symm, ?_⟩
    have hiso := N.isIso_map (Equiv.ulift.symm : Fin a' ≃ ULift (Fin a')) (Equiv.ulift.symm : Fin b' ≃ ULift (Fin b'))
    obtain ⟨i₁, i₂, i₃, i₄, i₅⟩ := hiso.invariants
    refine ⟨(i₂ c).2 (Network.obeys_of_tgt_injective (Network.tgt_injective_of_no_recomb hr) c), (i₃ M).2 hd, i₄.trans hs, (i₅ _).2 ?_, ?_⟩
    · refine ⟨fun B hB => ?_, fun i => hι.elim i, fun B _ hB => ?_⟩
      · obtain ⟨Q, ⟨w, x, p, q, hc, -⟩, -⟩ := hB
        exact absurd hc.1 (hr x)
      · obtain ⟨Q, ⟨w, x, p, q, hc, -⟩, -⟩ := hB
        exact absurd hc.1 (hr x)
    · rw [i₁, Network.recombCount_eq_zero_of_tgt_injective (Network.tgt_injective_of_no_recomb hr), finsum_of_isEmpty]

/-- The network of Theorem 1 for any root, with each central node inflated as line 299 says. -/
theorem exists_network_inflated (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.IsFullyDecomposedFor (incompatGraph (addRow M S)) := by
  have hinf := fun C => exists_inflate_piece c (M := addRow M S) C S
  choose a b P hob hanc hder hall huniq using hinf
  obtain ⟨a', b', N, h₁, h₂, h₃, h₄, -⟩ := exists_network_of_pieces c M S hM hC P hob hanc hder fun C =>
    ⟨huniq C, fun i => (P C).exists_isBlob_of_onCycle (hall C _)⟩
  exact ⟨a', b', N, h₁, h₂, h₃, h₄⟩

/-- **Theorem 1** (`g:thm1`), the Decomposition Theorem. "Let `G(M)` be the incompatibility graph for `M`. Then, there is a
phylogenetic network that derives `M` where every blob contains all and only the sites of a single non-trivial connected
component of `G(M)`, and every compatible site is on a tree edge. The result holds no matter what constraints, if any, are
placed on the number of crossovers allowed at a recombination node" (line 173).

The hypothesis that `M` is nonempty is implicit in the paper: a network has a leaf. The standing assumption isn't needed for
truth (a constant column can go on an arc out of a root of degree one), but `T̄` is built under it.

The proof is the paper's, in `exists_network_of_pieces`, with the root of `T̄` at a row of `M`: one of the selections that line 299 leaves arbitrary. -/
theorem theorem1 (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧
      N.IsFullyDecomposedFor (incompatGraph M) := by
  obtain ⟨S, hS⟩ := hM
  obtain ⟨a, b, N, h₁, h₂, -, h₄⟩ := exists_network_inflated c M S ⟨S, hS⟩ hC
  rw [addRow_eq_of_mem hS] at h₄
  exact ⟨a, b, N, h₁, h₂, h₄⟩

omit [LinearOrder ι] [Finite ι] in
/-- **Line 178** (`g:fd_iff`). The second wording of Theorem 1: "the blobs are in one-one correspondence with the non-trivial
connected components of `G(M)`, and if `b_C` is the blob corresponding to component `C`, then `b_C` contains all and only the
sites in `C`". It's equivalent to `IsFullyDecomposedFor`, granted that each non-trivial component is on a blob, which is the
converse below. -/
theorem isFullyDecomposedFor_iff_correspondence {V E : Type*} (N : Network ι V E) (G : SimpleGraph ι)
    (hG : ∀ c : G.ConnectedComponent, c.supp.Nontrivial → ∃ B, N.IsBlob B ∧ ∀ i ∈ c.supp, N.site i ∈ B) :
    N.IsFullyDecomposedFor G ↔ N.BlobCorrespondence G ∧ N.BlobsNodeDisjoint := by
  constructor
  · intro hF
    refine ⟨?_, hF.nodeDisjoint⟩
    choose f hf hfs using fun c : {c : G.ConnectedComponent // c.supp.Nontrivial} => hG c.1 c.2
    -- The blob of a component contains the sites of that component and no others.
    have hiff : ∀ c i, N.site i ∈ f c ↔ i ∈ c.1.supp := by
      intro c i
      obtain ⟨c', -, hc'⟩ := hF.blob_component (f c) (hf c)
      obtain ⟨j, hj⟩ := c.1.exists_rep
      have hj' : j ∈ c'.supp := (hc' j).1 (hfs c j hj)
      have hcc : c.1 = c' := hj.symm.trans hj'
      rw [hc' i, hcc]
    have hinj : Function.Injective (fun c => (⟨f c, hf c⟩ : {B : Set E // N.IsBlob B})) := by
      intro c c' heq
      have heq' : f c = f c' := congrArg Subtype.val heq
      obtain ⟨j, hj⟩ := c.1.exists_rep
      have h₁ : j ∈ c.1.supp := hj
      have h₂ := (hiff c' j).1 (heq' ▸ (hiff c j).2 h₁)
      exact Subtype.ext (hj.symm.trans h₂)
    have hsurj : Function.Surjective (fun c => (⟨f c, hf c⟩ : {B : Set E // N.IsBlob B})) := by
      rintro ⟨B, hB⟩
      obtain ⟨c, hc, hci⟩ := hF.blob_component B hB
      refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
      obtain ⟨j, hj⟩ := c.exists_rep
      have hj' : j ∈ c.supp := hj
      exact (hf ⟨c, hc⟩).eq_of_inter_nonempty hB ⟨N.site j, hfs ⟨c, hc⟩ j hj', (hci j).2 hj'⟩
    exact ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, hiff⟩
  · rintro ⟨⟨f, hf⟩, hd⟩
    refine ⟨fun B hB => ?_, fun i hi => ?_, hd⟩
    · obtain ⟨c, hc⟩ := f.surjective ⟨B, hB⟩
      refine ⟨c.1, c.2, fun i => ?_⟩
      rw [← hf c i, hc]
    · intro hon
      obtain ⟨B, hB, hmem⟩ := N.exists_isBlob_of_onCycle hon
      obtain ⟨c, hc⟩ := f.surjective ⟨B, hB⟩
      have hic : i ∈ c.1.supp := (hf c i).1 (by rw [hc]; exact hmem)
      -- A site in a non-trivial component has a neighbour.
      obtain ⟨a, ha, b, hb, hab⟩ := c.2
      have hne : ∃ j ∈ c.1.supp, j ≠ i := by
        by_cases hai : a = i
        · exact ⟨b, hb, fun hbi => hab (hai.trans hbi.symm)⟩
        · exact ⟨a, ha, hai⟩
      obtain ⟨j, hj, hji⟩ := hne
      obtain ⟨p⟩ : G.Reachable i j := SimpleGraph.ConnectedComponent.eq.1 (hic.trans (Eq.symm hj))
      cases p with
      | nil => exact hji rfl
      | cons h _ => exact hi _ h

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

/-- **Lines 187 to 190** (`g:thm1_rooted`). "There is an analogous theorem to Theorem 1 in the case that the ancestral sequence `S` is
known in advance. In that case, there is a phylogenetic network that derives `M`, with ancestral sequence `S`, where the blobs
are in one-one correspondence with the non-trivial connected components of `G_S(M)`, and any non-conflicting site is on a
tree edge".

The paper says this "follows from Theorem 1, and the fact that two sites conflict relative to `S` if and only if they are incompatible in `M + S`". The statement of Theorem 1 for `M + S` gives a network with `S` at a
leaf, and not at the root, and a network can't be re-rooted through a blob. What gives the result is the proof of Theorem 1, as line 312 says for Theorem 3: `T̄` for `M + S`, rooted at the node labelled `S`. So the proof here is `exists_network_inflated`. -/
theorem theorem1_rooted (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.IsFullyDecomposedFor (conflictGraph S M) := by
  rw [conflictGraph_eq_incompatGraph_addRow]
  exact exists_network_inflated c M S hM hC

/-- The ancestral sequence, as a row, changes nothing in the count: a network for the other rows gets it as a leaf below the root, and a network for all of them loses that
leaf, and all that's above it alone. -/
theorem RS_erase_eq (c : Crossover) (L : Finset (ι → Bool)) (S₀ : ι → Bool) (hcol : ∀ i, ∃ t ∈ L.erase S₀, t i ≠ S₀ i)
    (hne : (L.erase S₀).Nonempty) : RS c S₀ (L.erase S₀) = RS c S₀ L := by
  by_cases hS : S₀ ∈ L
  · apply le_antisymm
    · have hL : L.Nonempty := ⟨S₀, hS⟩
      obtain ⟨a, b, N, h₁, h₂, h₃, h₄⟩ := Nat.sInf_mem (rootedRecombSet_nonempty c S₀ hL)
      have hroot : N.label N.root = S₀ := h₃
      have hP : Decomp.PruneHyp N (fun _ => True) (fun v => N.IsLeaf v ∧ N.label v ≠ S₀) := by
        refine ⟨fun v hv => ?_, fun _ _ _ hf => absurd trivial hf, fun _ h => h.1, fun i => ?_, ?_⟩
        · have : ¬ ∀ e, N.tgt e ≠ v := fun h => hv ((N.root_iff v).1 h)
          push Not at this
          obtain ⟨e, he⟩ := this
          exact ⟨e, trivial, he⟩
        · obtain ⟨t, ht, hti⟩ := hcol i
          obtain ⟨htS, htL⟩ := Finset.mem_erase.1 ht
          obtain ⟨l, hl, rfl⟩ := h₂.surjOn (Finset.mem_coe.2 htL)
          exact ⟨l, ⟨hl, htS⟩, by rwa [hroot]⟩
        · obtain ⟨t, ht⟩ := hne
          obtain ⟨htS, htL⟩ := Finset.mem_erase.1 ht
          obtain ⟨l, hl, rfl⟩ := h₂.surjOn (Finset.mem_coe.2 htL)
          exact ⟨l, hl, htS⟩
      have hd : (Decomp.prune hP).Derives (L.erase S₀) := by
        refine Decomp.prune_derives hP ⟨fun v hv => ?_, fun u hu v hv huv => h₂.injOn hu.1 hv.1 huv, fun r hr => ?_⟩
        · exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hv.2, Finset.mem_coe.1 (h₂.mapsTo hv.1)⟩)
        · obtain ⟨hrS, hrL⟩ := Finset.mem_erase.1 (Finset.mem_coe.1 hr)
          obtain ⟨l, hl, rfl⟩ := h₂.surjOn (Finset.mem_coe.2 hrL)
          exact ⟨l, ⟨hl, hrS⟩, rfl⟩
      exact (RS_le_recombCount _ (Decomp.prune_obeys hP h₁) hd h₃).trans ((Decomp.prune_recombCount_le hP).trans_eq h₄)
    · obtain ⟨a, b, N, h₁, h₂, h₃, h₄⟩ := Nat.sInf_mem (rootedRecombSet_nonempty c S₀ hne)
      have hroot : N.label N.root = S₀ := h₃
      have hnotleaf : ¬ N.IsLeaf N.root := fun hl => by
        have := Finset.mem_coe.1 (h₂.mapsTo hl)
        rw [hroot] at this
        exact (Finset.mem_erase.1 this).1 rfl
      have hd := Decomp.addLeaf_derives h₂ hnotleaf (by rw [hroot]; simp)
      rw [hroot, Finset.insert_erase hS] at hd
      exact (RS_le_recombCount _ (Decomp.addLeaf_obeys h₁) hd (by rw [Decomp.addLeaf_ancestral]; exact h₃)).trans
        (Decomp.addLeaf_recombCount.trans_le h₄.le)
  · rw [Finset.erase_eq_of_notMem hS]

/-- The network for a component in the proof of Theorem 3: optimal, with one blob containing all the sites, for a connected conflict graph. A network with the fewest recombination nodes has
no blob without a site, since that blob has a recombination node with the label of both parents, from which an arc can be dropped. -/
theorem exists_optimal_piece (c : Crossover) (L : Finset (ι → Bool)) (S₀ : ι → Bool) (hcol : ∀ i, ∃ t ∈ L.erase S₀, t i ≠ S₀ i)
    (hne : (L.erase S₀).Nonempty) (hnt : Nontrivial ι) (hconn : ∀ i j, (conflictGraph S₀ (L.erase S₀)).Reachable i j) :
    ∃ (a b : ℕ) (P : Network ι (Fin a) (Fin b)), P.Obeys c ∧ P.ancestral = S₀ ∧ P.Derives (L.erase S₀) ∧ P.recombCount = RS c S₀ L ∧
      (∃! B, P.IsBlob B) ∧ ∀ i, ∃ B, P.IsBlob B ∧ P.site i ∈ B := by
  obtain ⟨a, b, N, h₁, h₂, h₃, h₄⟩ := Nat.sInf_mem (rootedRecombSet_nonempty c S₀ hne)
  have hroot : N.label N.root = S₀ := h₃
  have h₄' : N.recombCount = RS c S₀ (L.erase S₀) := h₄
  -- All the sites are on one blob, by the converse.
  obtain ⟨i₀, i₁, hi⟩ := exists_pair_ne ι
  have hsupp : ∀ i, i ∈ ((conflictGraph S₀ (L.erase S₀)).connectedComponentMk i₀).supp := fun i =>
    SimpleGraph.ConnectedComponent.eq.2 (hconn i i₀)
  obtain ⟨B₀, hB₀, hsite⟩ := converse_rooted N h₂ h₃ ((conflictGraph S₀ (L.erase S₀)).connectedComponentMk i₀)
    ⟨i₀, hsupp i₀, i₁, hsupp i₁, hi⟩
  have hsite' : ∀ i, N.site i ∈ B₀ := fun i => hsite i (hsupp i)
  -- Each blob has a site.
  have hsitefree : ∀ B, N.IsBlob B → ∃ i, N.site i ∈ B := by
    intro B hB
    by_contra hcon
    push Not at hcon
    obtain ⟨e, f, hef, ht, he, -⟩ := Decomp.exists_copy_of_siteFree N hB hcon
    have hP : Decomp.PruneHyp N (fun g => g ≠ f) N.IsLeaf := by
      refine ⟨fun v hv => ?_, fun e' f' he' hf' ht' i => ?_, fun _ h => h, fun i => ?_, ?_⟩
      · have : ¬ ∀ e, N.tgt e ≠ v := fun h => hv ((N.root_iff v).1 h)
        push Not at this
        obtain ⟨g, hg⟩ := this
        by_cases hgf : g = f
        · exact ⟨e, hef, by rw [ht, ← hgf, hg]⟩
        · exact ⟨g, hgf, hg⟩
      · obtain rfl : f' = f := not_not.1 hf'
        rcases N.inDegree_le_two e' e f' (ht'.trans ht.symm) ht with h | h | h
        · rw [h]
          exact he i
        · exact absurd h he'
        · exact absurd h hef
      · obtain ⟨t, ht₁, hti⟩ := hcol i
        obtain ⟨l, hl, rfl⟩ := h₂.surjOn (Finset.mem_coe.2 ht₁)
        exact ⟨l, hl, by rwa [hroot]⟩
      · obtain ⟨t, ht₁⟩ := hne
        obtain ⟨l, hl, -⟩ := h₂.surjOn (Finset.mem_coe.2 ht₁)
        exact ⟨l, hl⟩
    have hd : (Decomp.prune hP).Derives (L.erase S₀) := Decomp.prune_derives hP h₂
    have hlt := Decomp.prune_recombCount_lt hP (f := f) (not_not.2 rfl) ⟨e, f, hef, ht, rfl⟩
    have hle := RS_le_recombCount _ (Decomp.prune_obeys hP h₁) hd h₃
    omega
  refine ⟨a, b, N, h₁, h₃, h₂, h₄'.trans (RS_erase_eq c L S₀ hcol hne), ⟨B₀, hB₀, fun B hB => ?_⟩, fun i => ⟨B₀, hB₀, hsite' i⟩⟩
  obtain ⟨i, hi'⟩ := hsitefree B hB
  exact hB.eq_of_inter_nonempty hB₀ ⟨N.site i, hi', hsite' i⟩

/-- **Theorem 3** (`g:thm3`). "For any sequence `S`, there is a fully-decomposed phylogenetic network for `M` with ancestral
sequence `S`, containing exactly `Σ_{C ∈ G_S(M)} R_{S(C)}(M(C))` recombination nodes when multiple-crossover recombination is
allowed, and containing exactly `Σ_{C ∈ G_S(M)} R¹_{S(C)}(M(C))` recombination nodes when only single-crossover recombination
is allowed" (line 316).

The paper leaves the proof at "the proof of Theorem 1, when applied to `M + S`", which is `exists_network_of_pieces`, with `T̄` built from `M + S` and rooted at the row `S`. Here is what it
leaves to the reader.

* For a non-trivial `C`, the network inflating `v_C` is one with the fewest recombination nodes for `M(C)`, with ancestral sequence `S(C)`, without the row `S(C)`, if it's there (`exists_optimal_piece`). The edge of `T̄` for `S(C)` enters
  the blob, and so a leaf labelled `S(C)` has no edge of `T̄` to carry; removing it doesn't change the count (`RS_erase_eq`).
* It has one blob, by the converse and because a blob with no site has a recombination node with the label of both its parents, from which an arc can be dropped (`Decomp.exists_copy_of_siteFree`).
* Its other arcs carry no site, and they remain as tree arcs of the network. Each of its leaves gets the edge of `T̄` for its super-character, which is an outgoing arc also when the leaf is a recombination node.
* The node of `T̄` where `S` sits isn't a centre `v_C`, since a centre has no row. So each blob has an entering edge, attached at its root.
* A trivial component needs no recombination, by the Perfect Phylogeny Theorem. -/
theorem theorem3 (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.IsFullyDecomposedFor (conflictGraph S M) ∧
      N.recombCount = ∑ᶠ C : (conflictGraph S M).ConnectedComponent,
        RS c (C.supp.domRestrict S) (restrictRows C.supp M) := by
  rw [conflictGraph_eq_incompatGraph_addRow]
  -- The network for each non-trivial component.
  have hrows : ∀ C : (incompatGraph (addRow M S)).ConnectedComponent, restrictRows C.supp (addRow M S) =
      insert (C.supp.domRestrict S) (restrictRows C.supp M) := fun C => Finset.image_insert _ _ _
  have hcol : ∀ (C : (incompatGraph (addRow M S)).ConnectedComponent) (i : C.supp),
      ∃ t ∈ (restrictRows C.supp M).erase (C.supp.domRestrict S), t i ≠ C.supp.domRestrict S i := by
    intro C i
    obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ := hC i.1
    obtain ⟨r, hr, hri⟩ : ∃ r ∈ M, r i.1 ≠ S i.1 := by
      by_cases h₁ : r₁ i.1 = S i.1
      · exact ⟨r₂, hr₂, fun h₂ => hne (h₁.trans h₂.symm)⟩
      · exact ⟨r₁, hr₁, h₁⟩
    refine ⟨C.supp.domRestrict r, Finset.mem_erase.2 ⟨fun heq => hri (congrFun heq i), mem_restrictRows.2 ⟨r, hr, rfl⟩⟩, hri⟩
  have hpieces : ∀ C : Decomp.Cent (incompatGraph (addRow M S)), ∃ (a b : ℕ) (P : Network C.1.supp (Fin a) (Fin b)), P.Obeys c ∧
      P.ancestral = C.1.supp.domRestrict S ∧ P.Derives ((restrictRows C.1.supp M).erase (C.1.supp.domRestrict S)) ∧
      P.recombCount = RS c (C.1.supp.domRestrict S) (restrictRows C.1.supp M) ∧ (∃! B, P.IsBlob B) ∧
      ∀ i, ∃ B, P.IsBlob B ∧ P.site i ∈ B := by
    intro C
    have hnt : Nontrivial C.1.supp := Set.nontrivial_coe_sort.2 C.2
    obtain ⟨i₀⟩ : Nonempty C.1.supp := inferInstance
    obtain ⟨t₀, ht₀, -⟩ := hcol C.1 i₀
    refine exists_optimal_piece c _ _ (hcol C.1) ⟨t₀, ht₀⟩ hnt ?_
    -- The conflict graph of `M(C)` is connected, since the incompatibilities in `M + S` are visible in `M(C) + S(C)`.
    have hadj : ∀ {u w : ι} (hu : u ∈ C.1.supp) (hw : w ∈ C.1.supp), (incompatGraph (addRow M S)).Adj u w →
        (conflictGraph (C.1.supp.domRestrict S) ((restrictRows C.1.supp M).erase (C.1.supp.domRestrict S))).Adj ⟨u, hu⟩ ⟨w, hw⟩ := by
      intro u w hu hw huw
      refine (conflict_iff_incompatible_addRow _ _ _ _).2 fun x y => ?_
      obtain ⟨r, hr, hx, hy⟩ := huw x y
      refine ⟨C.1.supp.domRestrict r, ?_, hx, hy⟩
      rcases mem_addRow.1 hr with rfl | hr
      · exact mem_addRow.2 (Or.inl rfl)
      · by_cases heq : C.1.supp.domRestrict r = C.1.supp.domRestrict S
        · exact mem_addRow.2 (Or.inl heq)
        · exact mem_addRow.2 (Or.inr (Finset.mem_erase.2 ⟨heq, mem_restrictRows.2 ⟨r, hr, rfl⟩⟩))
    have hwalk : ∀ {u w : ι}, (incompatGraph (addRow M S)).Walk u w → ∀ (hu : u ∈ C.1.supp) (hw : w ∈ C.1.supp),
        (conflictGraph (C.1.supp.domRestrict S) ((restrictRows C.1.supp M).erase (C.1.supp.domRestrict S))).Reachable ⟨u, hu⟩ ⟨w, hw⟩ := by
      intro u w p
      induction p with
      | nil => exact fun _ _ => SimpleGraph.Reachable.refl _
      | @cons u v w huv _ ih =>
        intro hu hw
        have hv : v ∈ C.1.supp := by
          have : (incompatGraph (addRow M S)).connectedComponentMk v = (incompatGraph (addRow M S)).connectedComponentMk u :=
            SimpleGraph.ConnectedComponent.eq.2 huv.reachable.symm
          exact this.trans hu
        exact (hadj hu hv huv).reachable.trans (ih hv hw)
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨p⟩ : (incompatGraph (addRow M S)).Reachable i j := SimpleGraph.ConnectedComponent.eq.1 (hi.trans (Eq.symm hj))
    exact hwalk p hi hj
  choose a b P hob hanc hder hcount hone hsites using hpieces
  have hder' : ∀ C, (P C).Derives ((restrictRows C.1.supp (addRow M S)).erase (C.1.supp.domRestrict S)) := by
    intro C
    rw [hrows, Finset.erase_insert_eq_erase]
    exact hder C
  obtain ⟨a', b', N, h₁, h₂, h₃, h₄, h₅⟩ := exists_network_of_pieces c M S hM hC P hob hanc hder' fun C => ⟨hone C, hsites C⟩
  refine ⟨a', b', N, h₁, h₂, h₃, h₄, h₅.trans ?_⟩
  -- The sum over the non-trivial components is the sum over all: a trivial component needs no recombination.
  have hzero : ∀ C : (incompatGraph (addRow M S)).ConnectedComponent, ¬ C.supp.Nontrivial →
      RS c (C.supp.domRestrict S) (restrictRows C.supp M) = 0 := by
    intro C hnt
    have hsub : Subsingleton C.supp := (Set.not_nontrivial_iff.1 hnt).coe_sort
    have hne : (restrictRows C.supp M).Nonempty := hM.image _
    obtain ⟨a₀, b₀, N₀, hr, hd, hs, -⟩ := Gusfield1991.exists_network_of_no_conflict (restrictRows C.supp M) (C.supp.domRestrict S) hne
      ((hC.restrictRows C.supp).addRow _) (fun i j hc => by
        obtain rfl := Subsingleton.elim i j
        exact (conflictGraph _ _).irrefl hc)
    have := RS_le_recombCount N₀ (Network.obeys_of_tgt_injective (Network.tgt_injective_of_no_recomb hr) c) hd hs
    rw [Network.recombCount_eq_zero_of_tgt_injective (Network.tgt_injective_of_no_recomb hr)] at this
    omega
  calc ∑ᶠ C, (P C).recombCount = ∑ᶠ C : Decomp.Cent (incompatGraph (addRow M S)), RS c (C.1.supp.domRestrict S) (restrictRows C.1.supp M) :=
        finsum_congr hcount
    _ = ∑ᶠ C : (incompatGraph (addRow M S)).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M) := by
      rw [finsum_subtype_eq_finsum_cond (f := fun C : (incompatGraph (addRow M S)).ConnectedComponent => RS c (C.supp.domRestrict S) (restrictRows C.supp M))
        (fun C => C.supp.Nontrivial)]
      refine finsum_congr fun C => ?_
      rw [finsum_eq_if]
      split_ifs with hC'
      · rfl
      · exact (hzero C hC').symm

end Gusfield2007
