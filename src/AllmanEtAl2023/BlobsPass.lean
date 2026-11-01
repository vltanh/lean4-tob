module

public import AllmanEtAl2023.Basic
public import AllmanEtAl2023.Lemma2
public import AllmanEtAl2023.BlobDefinitions

/-!
# Allman, Baños, Mitchell, Rhodes 2023: "blobs pass to blobs, and cut edges to cut edges"

"To apply this to induced phylogenetic networks on subsets of taxa, observe that induced networks are obtained from subnetworks by suppressing degree-2 nodes. Under this operation, blobs pass to blobs, and
cut edges to cut edges." (before Corollary 2; `a:claim:suppress-blobs`).

What the sentence is used for is that a set of taxa determines a blob of the induced network exactly when it determines a blob of the subnetwork: `isBlobQuartetOnInduced_iff`. The sentence doesn't mention
step 3 of Definition 6, removing a stem, which the claim needs too.

To follow a blob through the steps of Definition 6, we use what "determines" says about cut edges and nothing else (`determines_iff_noTwoInSide`): no side of a cut edge away from the blob has two of the taxa. Then
a cut edge of a network gives one of the network after each step, with the same taxa on its sides and the node of the blob on the other side, and the other way round. That is the sentence of the paper:

* `noTwoInSide_retained_iff`: step 1, the subnetwork as a network;
* `noTwoInSide_of_suppress`, `noTwoInSide_suppress_chainEnd`: step 2, suppressing;
* `noTwoInSide_of_removeStem`, `noTwoInSide_removeStem`: step 3, removing a stem.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph
open scoped Classical

namespace AllmanEtAl2023.BlobsPass

variable {V E X : Type*}

/-- No side of a cut edge, away from `v`, has two of the labels. -/
def NoTwoInSide {ι : Type*} (G : DirectedMultigraph V E) (F : Set E) (v : V) (ℓ : ι → V) (S : Finset ι) : Prop :=
  ∀ e T, OnlyCrosses G F e T → v ∉ T → ∀ s ∈ S, ∀ t ∈ S, ℓ s ∈ T → ℓ t ∈ T → s = t

/-- **What "determines" says about cut edges.** Labels on pendant nodes determine the blob of `v` exactly when no side of a cut edge, away from `v`, has two of them. -/
theorem determines_iff_noTwoInSide {ι : Type*} {G : DirectedMultigraph V E} {F : Set E} {v : V} {ℓ : ι → V} {S : Finset ι} (h3 : 3 ≤ S.card)
    (hp : ∀ s ∈ S, IsPendantIn G F (ℓ s)) (hc : ∀ s ∈ S, G.Walks F v (ℓ s)) (hinj : Set.InjOn ℓ S) :
    Determines G F v ℓ S ↔ NoTwoInSide G F v ℓ S := by
  constructor
  · intro hdet e T hT hv s hs t ht hsT htT
    exact hdet.eq_of_mem_side hT hv hs ht (hc s hs) (hc t ht) hsT htT
  · intro hno s hs t ht hst hw
    rcases exists_leadsTo (hc s hs) with hb | ⟨g, hg⟩
    · -- `v` is the taxon `s`, whose edge has all the others on its other side
      have hvs := (hp s hs).eq_of_sameBlobIn hb
      obtain ⟨g, hg⟩ := (hp s hs).onlyCrosses
      obtain ⟨u, hu, hne₁, hne₂⟩ : ∃ u ∈ S, u ≠ s ∧ u ≠ t := by
        obtain ⟨a, ha, b, hb', c, hc', h₁, h₂, h₃⟩ := Finset.two_lt_card.mp (by omega : 2 < S.card)
        by_cases has : a = s
        · by_cases hbt : b = t
          · exact ⟨c, hc', fun h' => h₂ (has.trans h'.symm), fun h' => h₃ (hbt.trans h'.symm)⟩
          · exact ⟨b, hb', fun h' => h₁ (has.trans h'.symm), hbt⟩
        · by_cases hat : a = t
          · by_cases hbs : b = s
            · exact ⟨c, hc', fun h' => h₃ (hbs.trans h'.symm), fun h' => h₂ (hat.trans h'.symm)⟩
            · exact ⟨b, hb', hbs, fun h' => h₁ (hat.trans h'.symm)⟩
          · exact ⟨a, ha, has, hat⟩
      have hvT : v ∉ ({ℓ s} : Set V)ᶜ := by
        simp [hvs]
      have hmem : ∀ x ∈ S, x ≠ s → ℓ x ∈ ({ℓ s} : Set V)ᶜ := fun x hx hne h' => hne (hinj hx hs h')
      exact hne₂ (hno g _ hg hvT u hu t ht (hmem u hu hne₁) (hmem t ht hst.symm))
    · -- what is beyond the incident cut edge `g` isn't left without it
      have hO : OnlyCrosses G F g (far G F g v) := onlyCrosses_far
      have hsT : ℓ s ∈ far G F g v := hg.2
      have hiff := G.mem_iff_mem_of_walks (F := F \ incidentCuts G F v) (S := far G F g v)
        (fun f hf hcr => hf.2 (hO f hf.1 hcr ▸ hg.1)) hw
      exact hst (hno g _ hO not_mem_far_self s hs t ht hsT (hiff.mp hsT))

/-- On a phylogenetic network, the taxa are pendant, and the network is connected. -/
theorem determines_univ_iff {M : RootedNetwork V E X} (hM : M.IsPhylogenetic) {v : V} {S : Finset X} (h3 : 3 ≤ S.card) :
    Determines M.graph Set.univ v M.leaf S ↔ NoTwoInSide M.graph Set.univ v M.leaf S :=
  determines_iff_noTwoInSide h3 (fun s _ => isPendantIn_leaf hM s _) (fun _ _ => M.graph_connected hM _ _)
    (fun _ _ _ _ h' => hM.leaf_injective h')

/-! ### Step 2: suppressing -/

section Suppress

variable {P : RootedNetwork V E X} (hP : P.IsPhylogenetic)

include hP

/-- A cut edge of the network gives one of the suppressed network, at a node of the suppressed network. -/
theorem noTwoInSide_of_suppress {v : {v // ¬ P.IsChainVertex v}} {S : Finset X}
    (h : NoTwoInSide (P.suppress hP).graph Set.univ v (P.suppress hP).leaf S) : NoTwoInSide P.graph Set.univ v.1 P.leaf S := by
  intro e T hT hv s hs t ht hsT htT
  -- `e` crosses, since `v` and `ℓ s` are on different sides
  have hcr : P.graph.Crosses e T := by
    by_contra hno
    have hiff := P.graph.mem_iff_mem_of_walks (F := Set.univ) (S := T) (fun f _ hc => hno (hT f (Set.mem_univ _) hc ▸ hc))
      (P.graph_connected hP v.1 (P.leaf s))
    exact hv (hiff.mpr hsT)
  have hS : ∀ f, P.graph.Crosses f T ↔ f = e := fun f => ⟨hT f (Set.mem_univ _), fun h' => h' ▸ hcr⟩
  obtain ⟨f₀, hf₀, hon⟩ := exists_isOnChain hP e
  refine h ⟨f₀, hf₀⟩ (Subtype.val ⁻¹' T) (fun g _ hc => ?_) hv s hs t ht hsT htT
  have hc' : (P.graph.source g.1 ∈ T ∧ chainEnd hP (P.graph.target g.1) ∉ T) ∨ (chainEnd hP (P.graph.target g.1) ∈ T ∧ P.graph.source g.1 ∉ T) := hc
  exact Subtype.ext (((crosses_chain_iff hP hS).mp hc').unique hon g.2 hf₀)

/-- A cut edge of the suppressed network gives one of the network, with the chain of a node going to its end. -/
theorem noTwoInSide_suppress_chainEnd {v : V} {S : Finset X} (h : NoTwoInSide P.graph Set.univ v P.leaf S) :
    NoTwoInSide (P.suppress hP).graph Set.univ ⟨chainEnd hP v, not_isChainVertex_chainEnd hP v⟩ (P.suppress hP).leaf S := by
  intro e' T' hT' hv s hs t ht hsT htT
  let φ : V → {v // ¬ P.IsChainVertex v} := fun x => ⟨chainEnd hP x, not_isChainVertex_chainEnd hP x⟩
  have hleaf : ∀ x, φ (P.leaf x) = (P.suppress hP).leaf x := fun x => Subtype.ext (chainEnd_eq_self hP (not_isChainVertex_leaf hP x))
  refine h e'.1 (φ ⁻¹' T') (fun f _ hc => ?_) hv s hs t ht (by simpa only [Set.mem_preimage, hleaf] using hsT) (by simpa only [Set.mem_preimage, hleaf] using htT)
  by_cases hf : P.IsChainVertex (P.graph.source f)
  · exfalso
    have heq : φ (P.graph.source f) = φ (P.graph.target f) := Subtype.ext (chainEnd_eq_of_adj hP hf ⟨f, rfl, rfl⟩)
    simp only [DirectedMultigraph.Crosses, Set.mem_preimage, heq, and_not_self, or_self] at hc
  · have hs' : φ (P.graph.source f) = ⟨P.graph.source f, hf⟩ := Subtype.ext (chainEnd_eq_self hP hf)
    have hc' : (P.suppress hP).graph.Crosses ⟨f, hf⟩ T' := by
      simp only [DirectedMultigraph.Crosses, Set.mem_preimage, hs'] at hc
      exact hc
    exact congrArg Subtype.val (hT' ⟨f, hf⟩ (Set.mem_univ _) hc')

end Suppress

/-! ### Step 3: removing a stem -/

section Stem

variable {M : RootedNetwork V E X} (hM : M.IsPhylogenetic)

/-- The node of the network with the stem removed that a node goes to. -/
def stemMap (M : RootedNetwork V E X) (hM : M.IsPhylogenetic) (x : V) : {v // ¬ (HasStem M ∧ v = M.root)} :=
  if h : HasStem M ∧ x = M.root then (removeStem M hM).root else ⟨x, h⟩

include hM

/-- A cut edge of the network gives one with the stem removed, at a node that stays. -/
theorem noTwoInSide_of_removeStem {v : {v // ¬ (HasStem M ∧ v = M.root)}} {S : Finset X}
    (h : NoTwoInSide (removeStem M hM).graph Set.univ v (removeStem M hM).leaf S) : NoTwoInSide M.graph Set.univ v.1 M.leaf S := by
  intro e T hT hv s hs t ht hsT htT
  by_cases he : HasStem M ∧ M.graph.source e = M.root
  · -- the stem: all but the root is on one side
    exfalso
    obtain ⟨hst, hse⟩ := he
    have hee := (stemArc_spec M hst e).mp hse
    have hstay : ∀ a, a ≠ M.root → (a ∈ T ↔ M.graph.target e ∈ T) := by
      intro a ha
      have hr := target_stemArc_reaches hM hst ha
      rw [← hee] at hr
      have hav := avoidingReach_of_target_reaches hM.acyclic .refl hr
      refine (M.graph.mem_iff_mem_of_walks (F := {e}ᶜ) (S := T) (fun f hf hc => hf (hT f (Set.mem_univ _) hc)) ?_).symm
      refine Relation.ReflTransGen.mono ?_ _ _ hav
      rintro x y ⟨f, hf, hfs, hft⟩
      exact ⟨f, hf, Or.inl ⟨hfs, hft⟩⟩
    have h₁ := hstay v.1 (fun h' => v.2 ⟨hst, h'⟩)
    have h₂ := hstay _ (M.leaf_ne_root hM s)
    exact hv (h₁.mpr (h₂.mp hsT))
  · refine h ⟨e, he⟩ (Subtype.val ⁻¹' T) (fun g _ hc => ?_) hv s hs t ht hsT htT
    exact Subtype.ext (hT g.1 (Set.mem_univ _) hc)

/-- A cut edge with the stem removed gives one of the network, with the root going to its child. -/
theorem noTwoInSide_removeStem {v : V} {S : Finset X} (h : NoTwoInSide M.graph Set.univ v M.leaf S) :
    NoTwoInSide (removeStem M hM).graph Set.univ (stemMap M hM v) (removeStem M hM).leaf S := by
  intro e' T' hT' hv s hs t ht hsT htT
  have hleaf : ∀ x, stemMap M hM (M.leaf x) = (removeStem M hM).leaf x := fun x => by
    have hne : ¬ (HasStem M ∧ M.leaf x = M.root) := fun h' => M.leaf_ne_root hM x h'.2
    simp only [stemMap, dite_eq_right hne]
    rfl
  refine h e'.1 (stemMap M hM ⁻¹' T') (fun f _ hc => ?_) hv s hs t ht (by simpa only [Set.mem_preimage, hleaf] using hsT) (by simpa only [Set.mem_preimage, hleaf] using htT)
  have htgt : ∀ g : E, stemMap M hM (M.graph.target g) = ⟨M.graph.target g, fun h' => target_ne_root hM g h'.2⟩ := fun g => by
    have hne : ¬ (HasStem M ∧ M.graph.target g = M.root) := fun h' => target_ne_root hM g h'.2
    simp only [stemMap, dite_eq_right hne]
  by_cases hf : HasStem M ∧ M.graph.source f = M.root
  · exfalso
    obtain ⟨hst, hse⟩ := hf
    have hee := (stemArc_spec M hst f).mp hse
    have heq : stemMap M hM (M.graph.source f) = stemMap M hM (M.graph.target f) := by
      rw [htgt]
      have hd : HasStem M ∧ M.graph.source f = M.root := ⟨hst, hse⟩
      simp only [stemMap, dite_eq_left hd]
      apply Subtype.ext
      simp only [removeStem, dite_eq_left hst, hee]
    simp only [DirectedMultigraph.Crosses, Set.mem_preimage, heq, and_not_self, or_self] at hc
  · have hs' : stemMap M hM (M.graph.source f) = ⟨M.graph.source f, hf⟩ := by
      simp only [stemMap, dite_eq_right hf]
    have hc' : (removeStem M hM).graph.Crosses ⟨f, hf⟩ T' := by
      simp only [DirectedMultigraph.Crosses, Set.mem_preimage, hs', htgt] at hc
      exact hc
    exact congrArg Subtype.val (hT' ⟨f, hf⟩ (Set.mem_univ _) hc')

end Stem

/-! ### Step 1, and all of it -/

section Retained

variable {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) {Y : Set X} (hY : Y.Nontrivial)

/-- **Step 1 of Definition 6**: the subnetwork of the edges ancestral to `Y`, and the same as a network. -/
theorem noTwoInSide_retained_iff (v : N.belowVertices N.root Y) {S : Finset Y} :
    NoTwoInSide (retained hN Y hY).graph Set.univ v (retained hN Y hY).leaf S ↔
      NoTwoInSide N.graph (N.ancestralArcs Y) v.1 (fun x : Y => N.leaf x.1) S := by
  have hP := hN.isPhylogenetic
  constructor
  · intro h e T hT hv s hs t ht hsT htT
    have hvA : v.1 ∈ N.ancestralVertices Y := v.2.2
    have hsA : N.leaf s.1 ∈ N.ancestralVertices Y := N.leaf_mem_ancestralVertices s.2
    by_cases he : e ∈ N.ancestralArcs Y
    · have hke : e ∈ N.belowArcs N.root Y := ⟨hP.root_reaches _, he⟩
      refine h ⟨e, hke⟩ (Subtype.val ⁻¹' T) (fun g _ hc => ?_) hv s hs t ht hsT htT
      exact Subtype.ext (hT g.1 g.2.2 hc)
    · exfalso
      have hiff := N.graph.mem_iff_mem_of_walks (F := N.ancestralArcs Y) (S := T) (fun f hf hc => he (hT f hf hc ▸ hf))
        (walks_ancestral hP hvA hsA)
      exact hv (hiff.mpr hsT)
  · intro h e' T' hT' hv s hs t ht hsT htT
    have hval : ∀ x (hx : x ∈ N.belowVertices N.root Y), x ∈ Subtype.val '' T' ↔ (⟨x, hx⟩ : N.belowVertices N.root Y) ∈ T' := fun x hx => by
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · exact fun hm => ⟨_, hm, rfl⟩
    refine h e'.1 (Subtype.val '' T') (fun f hf hc => ?_) (fun hm => hv ((hval _ v.2).mp hm)) s hs t ht ⟨_, hsT, rfl⟩ ⟨_, htT, rfl⟩
    have hkf : f ∈ N.belowArcs N.root Y := ⟨hP.root_reaches _, hf⟩
    have hsv : N.graph.source f ∈ N.belowVertices N.root Y := ⟨hP.root_reaches _, N.source_mem_ancestralVertices hf⟩
    have htv : N.graph.target f ∈ N.belowVertices N.root Y := ⟨hP.root_reaches _, hf⟩
    have hc' : (retained hN Y hY).graph.Crosses ⟨f, hkf⟩ T' := by
      simp only [DirectedMultigraph.Crosses, hval _ hsv, hval _ htv] at hc
      exact hc
    exact congrArg Subtype.val (hT' ⟨f, hkf⟩ (Set.mem_univ _) hc')

/-- **"Under this operation, blobs pass to blobs, and cut edges to cut edges"** (`a:claim:suppress-blobs`, before Corollary 2): a B-quartet on the induced network is a set that determines a blob of the subnetwork of the
edges ancestral to `Y`. The paper's sentence omits step 3 of Definition 6. -/
theorem isBlobQuartetOnInduced_iff {Q : Finset X} (hQ : (Q : Set X) ⊆ Y) (h4 : Q.card = 4) :
    IsBlobQuartetOnInduced hN Y hY Q ↔ ∃ v ∈ N.ancestralVertices Y, Determines N.graph (N.ancestralArcs Y) v N.leaf Q := by
  have hP := hN.isPhylogenetic
  have hR := retained_isPhylogenetic hN Y hY
  have hM := retainedSuppressed_isPhylogenetic hN Y hY
  have hI := induced_isPhylogenetic hN Y hY
  have hmemY : ∀ {x}, x ∈ Q → x ∈ Y := fun hx => hQ hx
  have hdetN : ∀ v ∈ N.ancestralVertices Y, (Determines N.graph (N.ancestralArcs Y) v N.leaf Q ↔ NoTwoInSide N.graph (N.ancestralArcs Y) v N.leaf Q) := fun v hv =>
    determines_iff_noTwoInSide (by omega) (fun s _ => isPendantIn_leaf hP s _)
      (fun s hs => walks_ancestral hP hv (N.leaf_mem_ancestralVertices (hmemY hs))) (fun _ _ _ _ h' => hP.leaf_injective h')
  have hsub : ∀ (inst : DecidablePred (· ∈ Y)) (v : V), (NoTwoInSide N.graph (N.ancestralArcs Y) v N.leaf Q ↔
      NoTwoInSide N.graph (N.ancestralArcs Y) v (fun x : Y => N.leaf x.1) (@Finset.subtype X (· ∈ Y) inst Q)) := by
    intro inst v
    constructor
    · intro h e T hT hv s hs t ht hsT htT
      exact Subtype.ext (h e T hT hv s.1 (Finset.mem_subtype.mp hs) t.1 (Finset.mem_subtype.mp ht) hsT htT)
    · intro h e T hT hv s hs t ht hsT htT
      exact congrArg Subtype.val (h e T hT hv ⟨s, hmemY hs⟩ (Finset.mem_subtype.mpr hs) ⟨t, hmemY ht⟩ (Finset.mem_subtype.mpr ht) hsT htT)
  have hcard : ∀ inst : DecidablePred (· ∈ Y), (@Finset.subtype X (· ∈ Y) inst Q).card = 4 := fun inst => by
    rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => hmemY hx), h4]
  unfold IsBlobQuartetOnInduced
  constructor
  · rintro ⟨h4', b, hb⟩
    induction b using Quotient.inductionOn with
    | h v =>
      obtain ⟨h3, hd⟩ := isDeterminedBy_blobOf_iff.mp hb
      have h₁ := (determines_univ_iff hI h3).mp hd
      have h₂ := noTwoInSide_of_removeStem hM h₁
      have h₃ := noTwoInSide_of_suppress hR h₂
      have h₄ := (noTwoInSide_retained_iff hN hY v.1.1).mp h₃
      exact ⟨v.1.1.1, v.1.1.2.2, (hdetN _ v.1.1.2.2).mpr ((hsub _ _).mpr h₄)⟩
  · rintro ⟨v, hv, hd⟩
    refine ⟨hcard _, ?_⟩
    have h₁ := (hsub (fun _ => Classical.propDecidable _) v).mp ((hdetN v hv).mp hd)
    have h₂ := (noTwoInSide_retained_iff hN hY ⟨v, hP.root_reaches v, hv⟩).mpr h₁
    have h₃ := noTwoInSide_suppress_chainEnd hR h₂
    have h₄ := noTwoInSide_removeStem hM h₃
    have h3' : 3 ≤ (@Finset.subtype X (· ∈ Y) (fun _ => Classical.propDecidable _) Q).card := by
      rw [hcard]
      omega
    exact ⟨blobOf _ _, isDeterminedBy_blobOf_iff.mpr ⟨h3', (determines_univ_iff hI h3').mpr h₄⟩⟩

end Retained

end AllmanEtAl2023.BlobsPass
