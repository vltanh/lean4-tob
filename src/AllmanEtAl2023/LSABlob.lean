module

public import AllmanEtAl2023.BlobStructure
public import AllmanEtAl2023.TwoBlobs
public import AllmanEtAl2023.TrdTree

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the blob containing the LSA

* "It results in the degree of the blob containing the LSA not changing in passing from a rooted network `𝒩⁺` to its LSA network `𝒩⊕`" (after Definition 7): `blobDegree_lsaPlus`.
* "If the LSA of the original phylogenetic network `𝒩⁺` lies in an `m`-blob, `m ≥ 4`, that blob gives only an `(m - 1)`-multifurcation in the reduced unrooted tree of blobs" (after
  Definition 11): `existsUnique_multifurcation`.
* "If the LSA lies in a 3-blob, then that blob will be completely suppressed, and not represented by a node" (after Definition 11): `not_liesIn_of_three`. A blob with more than one node becomes a 2-blob of `𝒩⁻` here: the root is suppressed, and
  the two edges of the root become one edge.

The paper gives no proofs of these, and the proofs here are ours. Cut edges and blobs of `𝒩⁺`, `𝒩⊕`, `𝒩⁻` are compared in `isBridge_lsaPlus_iff`, `blobOf_lsaPlus_iff`, `blobOf_semidirected_iff`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph
open scoped Classical

namespace AllmanEtAl2023.BlobStructure

variable {V E X : Type*}

/-! ### From a rooted network to the network with its root suppressed -/

section Unroot

variable {P : RootedNetwork V E X}

/-- **In a blob with more than the root, the root's edges are not cut edges**: the root has two edges, and it has two edges in the blob. -/
theorem not_isBridge_of_source_eq_root (hP : P.IsPhylogenetic) (hout : P.graph.outdegree P.root = 2) {q : V} (hq : q ≠ P.root) (hb : blobOf P.graph q = blobOf P.graph P.root) {f : E}
    (hf : P.graph.source f = P.root) : ¬ P.graph.underlying.IsBridge f := by
  obtain ⟨f₁, f₂, hne, hat₁, hat₂, hn₁, hn₂⟩ := InPassing.exists_two_nonCuts hP hq.symm (sameBlobIn_univ_iff.mpr hb.symm)
  have hsrc : ∀ {g}, g ∈ TreeSuppression.edgesAt P.graph P.root → P.graph.source g = P.root := by
    rintro g (h | h)
    · exact h
    · exact absurd h (target_ne_root hP g)
  obtain ⟨p, q', hpq, hset⟩ := Set.ncard_eq_two.mp hout
  have hmem : ∀ g, P.graph.source g = P.root ↔ g = p ∨ g = q' := fun g => by
    have := Set.ext_iff.mp hset g
    simpa using this
  have hcut : ∀ {g}, g ∈ nonCutsIn P.graph Set.univ → ¬ P.graph.underlying.IsBridge g := fun hg hb => hg.2 (isCutIn_univ_iff.mpr hb)
  have hf' := (hmem f).mp hf
  have h₁ := (hmem f₁).mp (hsrc hat₁)
  have h₂ := (hmem f₂).mp (hsrc hat₂)
  have hff : f = f₁ ∨ f = f₂ := by
    rcases hf' with rfl | rfl <;> rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp_all
  rcases hff with rfl | rfl
  · exact hcut hn₁
  · exact hcut hn₂

variable (hP : P.IsPhylogenetic) {e₀ : E} (he₀ : P.graph.source e₀ = P.root) (hout : P.graph.outdegree P.root = 2)

omit hout in
theorem source_unrootAt_of_ne {g : {e // e ≠ e₀}} (h : P.graph.source g.1 ≠ P.root) : (unrootAt P hP e₀).graph.source g = ⟨P.graph.source g.1, h⟩ := by
  simp only [unrootAt, dite_eq_right h]

omit hout in
theorem source_unrootAt_of_eq {g : {e // e ≠ e₀}} (h : P.graph.source g.1 = P.root) : (unrootAt P hP e₀).graph.source g = ⟨P.graph.target e₀, target_ne_root hP e₀⟩ := by
  simp only [unrootAt, dite_eq_left h]

include he₀ hout in
/-- **Blobs of the network with the root suppressed** are those of the network, without the root. -/
theorem blobOf_unrootAt_iff (u w : {v // v ≠ P.root}) : blobOf (unrootAt P hP e₀).graph u = blobOf (unrootAt P hP e₀).graph w ↔ blobOf P.graph u.1 = blobOf P.graph w.1 := by
  have hbr := fun f : {e // e ≠ e₀} => InPassing.isBridge_unrootAt_iff hP he₀ hout f
  constructor
  · intro h
    have key : ∀ {a b : {v // v ≠ P.root}}, (unrootAt P hP e₀).graph.AdjOn {e | ¬ (unrootAt P hP e₀).graph.underlying.IsBridge e} a b → blobOf P.graph a.1 = blobOf P.graph b.1 := by
      have hone : ∀ g : {e // e ≠ e₀}, ¬ (unrootAt P hP e₀).graph.underlying.IsBridge g → blobOf P.graph ((unrootAt P hP e₀).graph.source g).1 = blobOf P.graph ((unrootAt P hP e₀).graph.target g).1 := by
        intro g hg
        have hg' : ¬ P.graph.underlying.IsBridge g.1 := fun h => hg ((hbr g).mpr h)
        have hstep : blobOf P.graph (P.graph.source g.1) = blobOf P.graph (P.graph.target g.1) := Quotient.sound (Relation.ReflTransGen.single ⟨g.1, hg', Or.inl ⟨rfl, rfl⟩⟩)
        by_cases hs : P.graph.source g.1 = P.root
        · rw [source_unrootAt_of_eq hP hs]
          have hne : P.graph.target g.1 ≠ P.root := target_ne_root hP g.1
          have hb₀ : blobOf P.graph (P.graph.target g.1) = blobOf P.graph P.root := by rw [← hstep, hs]
          have hn₀ := not_isBridge_of_source_eq_root hP hout hne hb₀ he₀
          have h₀ : blobOf P.graph P.root = blobOf P.graph (P.graph.target e₀) := by
            rw [← he₀]
            exact Quotient.sound (Relation.ReflTransGen.single ⟨e₀, hn₀, Or.inl ⟨rfl, rfl⟩⟩)
          exact h₀.symm.trans hb₀.symm
        · rw [source_unrootAt_of_ne hP hs]
          exact hstep
      rintro a b ⟨g, hg, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · exact hone g hg
      · exact (hone g hg).symm
    have hw := Quotient.exact h
    induction hw with
    | refl => rfl
    | tail _ hstep ih => exact (ih (Quotient.sound ‹_›)).trans (key hstep)
  · intro h
    let π : V → {v // v ≠ P.root} := fun v => if hv : v = P.root then ⟨P.graph.target e₀, target_ne_root hP e₀⟩ else ⟨v, hv⟩
    have hπ : ∀ a : {v // v ≠ P.root}, π a.1 = a := fun a => by simp only [π, dite_eq_right a.2]
    have key : ∀ {a b : V}, P.graph.AdjOn {e | ¬ P.graph.underlying.IsBridge e} a b → blobOf (unrootAt P hP e₀).graph (π a) = blobOf (unrootAt P hP e₀).graph (π b) := by
      have hone : ∀ g : E, ¬ P.graph.underlying.IsBridge g → blobOf (unrootAt P hP e₀).graph (π (P.graph.source g)) = blobOf (unrootAt P hP e₀).graph (π (P.graph.target g)) := by
        intro g hg
        by_cases hge : g = e₀
        · subst hge
          rw [he₀, hπ ⟨P.graph.target g, target_ne_root hP g⟩]
          simp only [π, dite_eq_left]
        · have hg' : ¬ (unrootAt P hP e₀).graph.underlying.IsBridge (⟨g, hge⟩ : {e // e ≠ e₀}) := fun hc => hg ((hbr ⟨g, hge⟩).mp hc)
          have hstep := Quotient.sound (s := (unrootAt P hP e₀).graph.blobSetoid) (Relation.ReflTransGen.single ⟨(⟨g, hge⟩ : {e // e ≠ e₀}), hg', Or.inl ⟨rfl, rfl⟩⟩)
          have hsrc : π (P.graph.source g) = (unrootAt P hP e₀).graph.source ⟨g, hge⟩ := by
            by_cases hs : P.graph.source g = P.root
            · rw [source_unrootAt_of_eq hP (g := ⟨g, hge⟩) hs]
              simp only [π, dite_eq_left hs]
            · rw [source_unrootAt_of_ne hP (g := ⟨g, hge⟩) hs]
              simp only [π, dite_eq_right hs]
          have htgt : π (P.graph.target g) = (unrootAt P hP e₀).graph.target ⟨g, hge⟩ := hπ ⟨P.graph.target g, target_ne_root hP g⟩
          rw [hsrc, htgt]
          exact hstep
      rintro a b ⟨g, hg, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · exact hone g hg
      · exact (hone g hg).symm
    have hw : P.graph.Walks {e | ¬ P.graph.underlying.IsBridge e} u.1 w.1 := Quotient.exact h
    have hgen : ∀ z, P.graph.Walks {e | ¬ P.graph.underlying.IsBridge e} u.1 z → blobOf (unrootAt P hP e₀).graph (π u.1) = blobOf (unrootAt P hP e₀).graph (π z) := by
      intro z hz
      induction hz with
      | refl => rfl
      | tail _ hstep ih => exact ih.trans (key hstep)
    have := hgen _ hw
    rwa [hπ, hπ] at this

include he₀ hout in
/-- **The degree, when the root isn't alone in its blob**: the two edges of the root are in the blob, so the cut edges are the same. -/
theorem cutDegree_unrootAt {u : {v // v ≠ P.root}} (hu : blobOf P.graph u.1 = blobOf P.graph P.root) :
    cutDegree (unrootAt P hP e₀).graph (blobOf (unrootAt P hP e₀).graph u) = cutDegree P.graph (blobOf P.graph P.root) := by
  have hbr := fun f : {e // e ≠ e₀} => InPassing.isBridge_unrootAt_iff hP he₀ hout f
  have hnc : ∀ {f : E}, P.graph.source f = P.root → ¬ P.graph.underlying.IsBridge f := fun hf => not_isBridge_of_source_eq_root hP hout u.2 hu hf
  have hbl := fun w : {v // v ≠ P.root} => (blobOf_unrootAt_iff hP he₀ hout w u).trans (by rw [hu])
  have hinc : ∀ g : {e // e ≠ e₀}, P.graph.source g.1 ≠ P.root → (IsIncidentToBlob (unrootAt P hP e₀).graph g (blobOf (unrootAt P hP e₀).graph u) ↔ IsIncidentToBlob P.graph g.1 (blobOf P.graph P.root)) := by
    intro g hg
    unfold IsIncidentToBlob
    rw [source_unrootAt_of_ne hP hg]
    simp only [hbl]
    rfl
  refine Set.ncard_congr (fun g _ => g.1) (fun g hg => ?_) (fun a b _ _ h => Subtype.ext h) (fun e he => ?_)
  · have hb := (hbr g).mp hg.1
    exact ⟨hb, (hinc g fun hs => hnc hs hb).mp hg.2⟩
  · have hne : e ≠ e₀ := fun h => hnc he₀ (h ▸ he.1)
    refine ⟨⟨e, hne⟩, ⟨(hbr ⟨e, hne⟩).mpr he.1, (hinc ⟨e, hne⟩ fun hs => hnc hs he.1).mpr he.2⟩, rfl⟩

end Unroot

/-! ### From a rooted network to its LSA network -/

section Plus

variable {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) (hX : Nontrivial X)

/-- Each node goes to itself if it is kept in `𝒩⊕`, and to the root of `𝒩⊕` if it is above the LSA. -/
def toPlus (v : V) : N.belowVertices (lsaNode hN hX) Set.univ :=
  if h : v ∈ N.belowVertices (lsaNode hN hX) Set.univ then ⟨v, h⟩ else (lsaPlus hN hX).root

theorem toPlus_val (a : N.belowVertices (lsaNode hN hX) Set.univ) : toPlus hN hX a.1 = a := by
  simp only [toPlus, dite_eq_left a.2]

/-- An arc that is not kept in `𝒩⊕` has both ends at the root of `𝒩⊕`. -/
theorem toPlus_of_notMem {g : E} (hg : g ∉ N.belowArcs (lsaNode hN hX) Set.univ) :
    toPlus hN hX (N.graph.source g) = (lsaPlus hN hX).root ∧ toPlus hN hX (N.graph.target g) = (lsaPlus hN hX).root := by
  have hP := hN.isPhylogenetic
  rw [mem_belowArcs_univ_iff, not_not] at hg
  constructor
  · refine dite_eq_right fun h => absurd (hg.trans h.1) (not_reaches_target_source hP.acyclic g)
  · by_cases h : N.graph.target g ∈ N.belowVertices (lsaNode hN hX) Set.univ
    · have hEq := eq_of_reaches_of_reaches hP.acyclic hg h.1
      simp only [toPlus, dite_eq_left h]
      exact Subtype.ext hEq
    · simp only [toPlus, dite_eq_right h]

/-- **An edge of `𝒩⊕` is a cut edge exactly when it is one of `𝒩⁺`.** -/
theorem isBridge_lsaPlus_iff (f : N.belowArcs (lsaNode hN hX) Set.univ) :
    (lsaPlus hN hX).graph.underlying.IsBridge f ↔ N.graph.underlying.IsBridge f.1 := by
  rw [DirectedMultigraph.isBridge_iff, DirectedMultigraph.isBridge_iff]
  constructor
  · rintro ⟨S', hS'⟩
    refine ⟨toPlus hN hX ⁻¹' S', fun g => ?_⟩
    by_cases hg : g ∈ N.belowArcs (lsaNode hN hX) Set.univ
    · have hc := hS' ⟨g, hg⟩
      have hs : toPlus hN hX (N.graph.source g) = (lsaPlus hN hX).graph.source ⟨g, hg⟩ := toPlus_val hN hX ((lsaPlus hN hX).graph.source ⟨g, hg⟩)
      have ht : toPlus hN hX (N.graph.target g) = (lsaPlus hN hX).graph.target ⟨g, hg⟩ := toPlus_val hN hX ((lsaPlus hN hX).graph.target ⟨g, hg⟩)
      simp only [DirectedMultigraph.Crosses, Set.mem_preimage, hs, ht]
      exact hc.trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    · obtain ⟨h₁, h₂⟩ := toPlus_of_notMem hN hX hg
      have hne : g ≠ f.1 := fun h => hg (h ▸ f.2)
      simp only [DirectedMultigraph.Crosses, Set.mem_preimage, h₁, h₂, hne, iff_false]
      tauto
  · rintro ⟨S, hS⟩
    refine ⟨Subtype.val ⁻¹' S, fun g => ?_⟩
    exact (hS g.1).trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- **Blobs of `𝒩⊕`** are those of `𝒩⁺`, on the nodes kept. -/
theorem blobOf_lsaPlus_iff (u w : N.belowVertices (lsaNode hN hX) Set.univ) :
    blobOf (lsaPlus hN hX).graph u = blobOf (lsaPlus hN hX).graph w ↔ blobOf N.graph u.1 = blobOf N.graph w.1 := by
  constructor
  · intro h
    have hw := Quotient.exact h
    induction hw with
    | refl => rfl
    | @tail b c _ hstep ih =>
      refine (ih (Quotient.sound ‹_›)).trans ?_
      obtain ⟨g, hg, hl⟩ := hstep
      have hg' : ¬ N.graph.underlying.IsBridge g.1 := fun hc => hg ((isBridge_lsaPlus_iff hN hX g).mpr hc)
      have hb : blobOf N.graph (N.graph.source g.1) = blobOf N.graph (N.graph.target g.1) := Quotient.sound (Relation.ReflTransGen.single ⟨g.1, hg', Or.inl ⟨rfl, rfl⟩⟩)
      rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hb
      · exact hb.symm
  · intro h
    have hone : ∀ g : E, ¬ N.graph.underlying.IsBridge g → blobOf (lsaPlus hN hX).graph (toPlus hN hX (N.graph.source g)) = blobOf (lsaPlus hN hX).graph (toPlus hN hX (N.graph.target g)) := by
      intro g hg
      by_cases hgm : g ∈ N.belowArcs (lsaNode hN hX) Set.univ
      · have hs : toPlus hN hX (N.graph.source g) = (lsaPlus hN hX).graph.source ⟨g, hgm⟩ := toPlus_val hN hX ((lsaPlus hN hX).graph.source ⟨g, hgm⟩)
        have ht : toPlus hN hX (N.graph.target g) = (lsaPlus hN hX).graph.target ⟨g, hgm⟩ := toPlus_val hN hX ((lsaPlus hN hX).graph.target ⟨g, hgm⟩)
        rw [hs, ht]
        exact Quotient.sound (Relation.ReflTransGen.single ⟨⟨g, hgm⟩, fun hc => hg ((isBridge_lsaPlus_iff hN hX ⟨g, hgm⟩).mp hc), Or.inl ⟨rfl, rfl⟩⟩)
      · obtain ⟨h₁, h₂⟩ := toPlus_of_notMem hN hX hgm
        rw [h₁, h₂]
    have hw : N.graph.Walks {e | ¬ N.graph.underlying.IsBridge e} u.1 w.1 := Quotient.exact h
    have hgen : ∀ z, N.graph.Walks {e | ¬ N.graph.underlying.IsBridge e} u.1 z → blobOf (lsaPlus hN hX).graph (toPlus hN hX u.1) = blobOf (lsaPlus hN hX).graph (toPlus hN hX z) := by
      intro z hz
      induction hz with
      | refl => rfl
      | tail _ hstep ih =>
        refine ih.trans ?_
        obtain ⟨g, hg, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := hstep
        · exact hone g hg
        · exact (hone g hg).symm
    have := hgen _ hw
    rwa [toPlus_val, toPlus_val] at this

/-- The cut edges of the blob of the LSA in `𝒩⊕` are those of `𝒩⁺`, other than the edge entering the LSA. -/
theorem cutDegree_lsaPlus :
    cutDegree (lsaPlus hN hX).graph (blobOf (lsaPlus hN hX).graph (lsaPlus hN hX).root) =
      (incidentCutEdges N.graph (blobOf N.graph (lsaNode hN hX)) \ {e | N.graph.target e = lsaNode hN hX}).ncard := by
  have hP := hN.isPhylogenetic
  have hbl : ∀ w : N.belowVertices (lsaNode hN hX) Set.univ, blobOf (lsaPlus hN hX).graph w = blobOf (lsaPlus hN hX).graph (lsaPlus hN hX).root ↔ blobOf N.graph w.1 = blobOf N.graph (lsaNode hN hX) :=
    fun w => blobOf_lsaPlus_iff hN hX w _
  refine Set.ncard_congr (fun g _ => g.1) (fun g hg => ?_) (fun a b _ _ h => Subtype.ext h) (fun e he => ?_)
  · refine ⟨⟨(isBridge_lsaPlus_iff hN hX g).mp hg.1, ?_⟩, fun ht => ?_⟩
    · have h : IsIncidentToBlob (lsaPlus hN hX).graph g _ := hg.2
      unfold IsIncidentToBlob at h ⊢
      simp only [hbl] at h
      exact h
    · have hgm := g.2
      have ht' : N.graph.target g.1 = lsaNode hN hX := ht
      rw [mem_belowArcs_univ_iff, ht'] at hgm
      exact hgm .refl
  · obtain ⟨⟨hb, hi⟩, hne⟩ := he
    have hgm : e ∈ N.belowArcs (lsaNode hN hX) Set.univ := by
      rw [mem_belowArcs_univ_iff]
      intro hr
      refine hne (?_ : N.graph.target e = lsaNode hN hX)
      have hreach : N.graph.Reaches (lsaNode hN hX) (N.graph.target e) := by
        rcases hi with ⟨h, -⟩ | ⟨h, -⟩
        · exact ((reaches_lsaNode_iff_of_blobOf_eq hN hX h).mpr .refl).tail ⟨e, rfl, rfl⟩
        · exact (reaches_lsaNode_iff_of_blobOf_eq hN hX h).mpr .refl
      exact eq_of_reaches_of_reaches hP.acyclic hr hreach
    refine ⟨⟨e, hgm⟩, ⟨(isBridge_lsaPlus_iff hN hX ⟨e, hgm⟩).mpr hb, ?_⟩, rfl⟩
    unfold IsIncidentToBlob
    simp only [hbl]
    exact hi

/-- **"It results in the degree of the blob containing the LSA not changing in passing from a rooted network `𝒩⁺` to its LSA network `𝒩⊕`"** (`a:claim:lsa-degree`, after Definition 7). -/
theorem blobDegree_lsaPlus :
    blobDegree (lsaPlus hN hX) (blobOf (lsaPlus hN hX).graph (lsaPlus hN hX).root) = blobDegree N (blobOf N.graph (lsaNode hN hX)) := by
  have hP := hN.isPhylogenetic
  have : Finite E := hP.finite_arcs
  have h := cutDegree_lsaPlus hN hX
  simp only [blobDegree, ↓reduceIte, h]
  by_cases hr : lsaNode hN hX = N.root
  · have hC : {e | N.graph.target e = lsaNode hN hX} = ∅ := Set.eq_empty_of_forall_notMem fun e he => target_ne_root hP e (Eq.trans he hr)
    rw [hC, Set.sdiff_empty, hr]
    simp only [↓reduceIte, cutDegree]
  · rcases Relation.ReflTransGen.cases_tail (hP.root_reaches (lsaNode hN hX)) with hr' | ⟨b, -, i, -, hi⟩
    · exact absurd hr' hr
    have hC : {e | N.graph.target e = lsaNode hN hX} = {i} := Set.eq_singleton_iff_unique_mem.mpr ⟨hi, fun e he => eq_of_target_eq_lsaNode hN hX he hi⟩
    have hbne : blobOf N.graph N.root ≠ blobOf N.graph (lsaNode hN hX) := fun hb => hr (eq_of_reaches_of_reaches hP.acyclic (hP.root_reaches _) ((reaches_lsaNode_iff_of_blobOf_eq hN hX hb).mpr .refl)).symm
    have hmem : i ∈ incidentCutEdges N.graph (blobOf N.graph (lsaNode hN hX)) := by
      rw [incidentCutEdges_blobOf]
      have hs : blobOf N.graph (N.graph.source i) ≠ blobOf N.graph (lsaNode hN hX) := fun hb => not_reaches_target_source hP.acyclic i (hi ▸ (reaches_lsaNode_iff_of_blobOf_eq hN hX hb).mpr .refl)
      exact mem_incidentCuts_of_target hs (congrArg _ hi)
    have hpos : 0 < (incidentCutEdges N.graph (blobOf N.graph (lsaNode hN hX))).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨i, hmem⟩
    rw [hC, Set.ncard_sdiff_singleton_of_mem hmem]
    simp only [hbne, ↓reduceIte, cutDegree]
    omega

end Plus

/-! ### The blob of the LSA in the semidirected network and in the tree of blobs -/

section Semi

variable {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) (hX : Nontrivial X)

/-- **Blobs of `𝒩⁻`** are those of `𝒩⁺`, on the nodes kept. -/
theorem blobOf_semidirected_iff (u w : SemiV hN hX) :
    blobOf (semidirected hN hX).graph u = blobOf (semidirected hN hX).graph w ↔ blobOf N.graph u.1.1 = blobOf N.graph w.1.1 :=
  (blobOf_unrootAt_iff (lsaPlus_isPhylogenetic hN hX) (rootTreeArc_spec hN hX).1 (lsaPlus_outdegree_root hN hX) u w).trans (blobOf_lsaPlus_iff hN hX u.1 w.1)

/-- **The degree of a node of the blob of the LSA in `𝒩⁻`**: "`m - 1`". -/
theorem cutDegree_semidirected_add_one {u : SemiV hN hX} (hu : blobOf N.graph u.1.1 = blobOf N.graph (lsaNode hN hX)) :
    cutDegree (semidirected hN hX).graph (blobOf (semidirected hN hX).graph u) + 1 = blobDegree N (blobOf N.graph (lsaNode hN hX)) := by
  have h := cutDegree_unrootAt (lsaPlus_isPhylogenetic hN hX) (rootTreeArc_spec hN hX).1 (lsaPlus_outdegree_root hN hX) (u := u) ((blobOf_lsaPlus_iff hN hX u.1 _).mpr hu)
  have h' := blobDegree_lsaPlus hN hX
  simp only [blobDegree, ↓reduceIte] at h'
  exact (congrArg (· + 1) h).trans h'

/-- A node of `T_rd(𝒩⁻)` *lies in* a blob of `𝒩⁺`: it is a blob of `𝒩⁻` with a node there, so by `blobOf_semidirected_iff` all its nodes are there. -/
def LiesIn (t : TrdV hN hX) (b : N.graph.BlobVertex) : Prop :=
  ∃ u : SemiV hN hX, blobOf (semidirected hN hX).graph u = t.1 ∧ blobOf N.graph u.1.1 = b

/-- The degree of a node of `T_rd(𝒩⁻)`. -/
theorem ncard_neighborSet_trd (t : TrdV hN hX) : ((Trd hN hX).graph.neighborSet t).ncard = cutDegree (semidirected hN hX).graph t.1 := by
  have : Finite V := hN.isPhylogenetic.finite_vertices
  have : Finite E := hN.isPhylogenetic.finite_arcs
  have h := TreeSuppression.ncard_neighborSet_suppressDegreeTwo (treeOfBlobs_semidirected_isTree hN hX) t
  rw [nodeDegree_bridgeQuotient] at h
  exact h

/-- **"If the LSA lies in a 3-blob, then that blob will be completely suppressed, and not represented by a node"** (`a:claim:lsa-three`, after Definition 11). -/
theorem not_liesIn_of_three (hm : blobDegree N (blobOf N.graph (lsaNode hN hX)) = 3) (t : TrdV hN hX) : ¬ LiesIn hN hX t (blobOf N.graph (lsaNode hN hX)) := by
  have : Finite E := hN.isPhylogenetic.finite_arcs
  rintro ⟨u, hu₁, hu⟩
  have h := cutDegree_semidirected_add_one hN hX hu
  refine t.2 ?_
  rw [← hu₁, show nodeDegree (semidirected hN hX).treeOfBlobs (blobOf (semidirected hN hX).graph u) = cutDegree (semidirected hN hX).graph (blobOf (semidirected hN hX).graph u) from nodeDegree_bridgeQuotient _]
  omega

/-- A blob of degree at least 4 containing the LSA has another node. -/
theorem exists_ne_of_four (hm : 4 ≤ blobDegree N (blobOf N.graph (lsaNode hN hX))) : ∃ u, u ≠ lsaNode hN hX ∧ blobOf N.graph u = blobOf N.graph (lsaNode hN hX) := by
  have hP := hN.isPhylogenetic
  have : Finite E := hP.finite_arcs
  by_contra hno
  push Not at hno
  have hsub : incidentCutEdges N.graph (blobOf N.graph (lsaNode hN hX)) ⊆ TreeSuppression.edgesAt N.graph (lsaNode hN hX) := by
    rintro e ⟨-, (⟨h, -⟩ | ⟨h, -⟩)⟩
    · refine Or.inl (by_contra fun hne => hno _ hne h)
    · refine Or.inr (by_contra fun hne => hno _ hne h)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 := InPassing.ncard_edgesAt_le_three hN (lsaNode hN hX)
  by_cases hr : blobOf N.graph N.root = blobOf N.graph (lsaNode hN hX)
  · -- then the LSA is the root
    have hroot : N.root = lsaNode hN hX := by
      by_contra hne
      exact hno _ hne hr
    have hat : TreeSuppression.edgesAt N.graph (lsaNode hN hX) = {e | N.graph.source e = N.root} := by
      ext e
      constructor
      · rintro (h | h)
        · exact h.trans hroot.symm
        · exact absurd (h.trans hroot.symm) (target_ne_root hP e)
      · exact fun h => Or.inl (h.trans hroot)
    have h2 := hN.isBinary.1
    rw [hat] at hle
    change _ ≤ N.graph.outdegree N.root at hle
    simp only [blobDegree, hr, ↓reduceIte, cutDegree] at hm
    omega
  · simp only [blobDegree, hr, ↓reduceIte, cutDegree] at hm
    omega

/-- **"If the LSA of the original phylogenetic network `𝒩⁺` lies in an `m`-blob, `m ≥ 4`, that blob gives only an `(m - 1)`-multifurcation in the reduced unrooted tree of blobs"** (`a:claim:lsa-multifurcation`, after Definition 11): one node
of `T_rd(𝒩⁻)` lies in the blob, and it has degree `m - 1`. -/
theorem existsUnique_multifurcation (hm : 4 ≤ blobDegree N (blobOf N.graph (lsaNode hN hX))) :
    ∃! t : TrdV hN hX, LiesIn hN hX t (blobOf N.graph (lsaNode hN hX)) ∧ ((Trd hN hX).graph.neighborSet t).ncard = blobDegree N (blobOf N.graph (lsaNode hN hX)) - 1 := by
  have : Finite E := hN.isPhylogenetic.finite_arcs
  obtain ⟨v, hv, hb⟩ := exists_ne_of_four hN hX hm
  have hreach : N.graph.Reaches (lsaNode hN hX) v := (reaches_lsaNode_iff_of_blobOf_eq hN hX hb).mpr .refl
  have hmem : v ∈ N.belowVertices (lsaNode hN hX) Set.univ := (mem_belowVertices_univ_iff hN hX v).mpr fun h => hv (eq_of_reaches_of_reaches hN.isPhylogenetic.acyclic h.1 hreach)
  let u : SemiV hN hX := ⟨⟨v, hmem⟩, fun h => hv (congrArg Subtype.val h)⟩
  have hu : blobOf N.graph u.1.1 = blobOf N.graph (lsaNode hN hX) := hb
  have hc := cutDegree_semidirected_add_one hN hX hu
  have hdeg : nodeDegree (semidirected hN hX).treeOfBlobs (blobOf (semidirected hN hX).graph u) ≠ 2 := by
    rw [show nodeDegree (semidirected hN hX).treeOfBlobs (blobOf (semidirected hN hX).graph u) = cutDegree (semidirected hN hX).graph (blobOf (semidirected hN hX).graph u) from nodeDegree_bridgeQuotient _]
    omega
  refine ⟨⟨_, hdeg⟩, ⟨⟨u, rfl, hu⟩, ?_⟩, ?_⟩
  · rw [ncard_neighborSet_trd]
    change cutDegree (semidirected hN hX).graph (blobOf (semidirected hN hX).graph u) = _
    omega
  · rintro t ⟨⟨w, hw, hwb⟩, -⟩
    refine Subtype.ext ?_
    rw [← hw]
    exact (blobOf_semidirected_iff hN hX w u).mpr (hwb.trans hu.symm)

end Semi

end AllmanEtAl2023.BlobStructure
