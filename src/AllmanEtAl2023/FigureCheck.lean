module

public import AllmanEtAl2023.TwoBlobs
public import AllmanEtAl2023.Theorem3

/-!
# Allman, Baños, Mitchell, Rhodes 2023: checking the claims about an explicit network

For the examples of Figures 3 and 9. A network on numbered nodes and edges is finite, so connectivity can be computed: `reachSet`, `walks_iff`, and the ancestors of a set of taxa: `ancSet`, `ancestralArcs_eq`.

A blob is determined by a set of taxa if the taxa have different colours under a colouring of the nodes in which the edges joining different colours are cut edges at the blob (`Cert`). A set is a T-quartet if a cut edge separates it (`CutCheck`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph
open scoped Classical

namespace AllmanEtAl2023.FigureCheck

open InPassing

/-! ### Iterating a growing map on finite sets -/

section Iterate

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A growing map on finite sets stops growing, by the size of the type. -/
theorem iterate_fixed (f : Finset α → Finset α) (hf : ∀ S, S ⊆ f S) {S : Finset α} (hS : S.Nonempty) :
    f (f^[Fintype.card α] S) = f^[Fintype.card α] S := by
  have key : ∀ k, f^[k + 1] S = f^[k] S ∨ k + 1 ≤ (f^[k] S).card := by
    intro k
    induction k with
    | zero => exact Or.inr (Finset.card_pos.mpr hS)
    | succ k ih =>
      by_cases he : f^[k + 1] S = f^[k] S
      · refine Or.inl ?_
        rw [Function.iterate_succ_apply', he]
        rwa [Function.iterate_succ_apply'] at he
      · refine Or.inr ?_
        rcases ih with ih | ih
        · exact absurd ih he
        · have hss : f^[k] S ⊂ f^[k + 1] S := by
            rw [Function.iterate_succ_apply']
            refine Finset.ssubset_iff_subset_ne.mpr ⟨hf _, fun h => he ?_⟩
            rw [Function.iterate_succ_apply', ← h]
          have := Finset.card_lt_card hss
          omega
  rcases key (Fintype.card α) with h | h
  · rwa [Function.iterate_succ_apply'] at h
  · have := Finset.card_le_univ (f^[Fintype.card α] S)
    omega

end Iterate

/-! ### Walks -/

section Walks

variable {n m k : ℕ} (src tgt : Fin m → Fin n)

/-- One step of walking along the edges `F`, from the nodes `S`. -/
def stepSet (F : Finset (Fin m)) (S : Finset (Fin n)) : Finset (Fin n) :=
  S ∪ (F.filter fun e => src e ∈ S).image tgt ∪ (F.filter fun e => tgt e ∈ S).image src

/-- The nodes joined to `S` by the edges `F`. -/
def reachSet (F : Finset (Fin m)) (S : Finset (Fin n)) : Finset (Fin n) := (stepSet src tgt F)^[n] S

variable {src tgt}

theorem subset_stepSet (F : Finset (Fin m)) (S : Finset (Fin n)) : S ⊆ stepSet src tgt F S := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_union_left _ hx)

theorem stepSet_reachSet (F : Finset (Fin m)) (u : Fin n) : stepSet src tgt F (reachSet src tgt F {u}) = reachSet src tgt F {u} := by
  have h := iterate_fixed (stepSet src tgt F) (subset_stepSet F) (S := {u}) (Finset.singleton_nonempty u)
  rwa [Fintype.card_fin] at h

/-- The graph of a numbered network. -/
abbrev graphOf (src tgt : Fin m → Fin n) : DirectedMultigraph (Fin n) (Fin m) := ⟨src, tgt⟩

/-- **What `reachSet` computes.** -/
theorem walks_iff {F : Finset (Fin m)} {u w : Fin n} : (graphOf src tgt).Walks (F : Set (Fin m)) u w ↔ w ∈ reachSet src tgt F {u} := by
  constructor
  · intro h
    induction h with
    | refl =>
      have hsub : ∀ j, u ∈ (stepSet src tgt F)^[j] {u} := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          rw [Function.iterate_succ_apply']
          exact subset_stepSet F _ ih
      exact hsub n
    | @tail b c _ hstep ih =>
      obtain ⟨e, he, (⟨hs, ht⟩ | ⟨hs, ht⟩)⟩ := hstep
      · rw [← stepSet_reachSet]
        refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, ht⟩))
        rw [show src e = b from hs]
        exact ih
      · rw [← stepSet_reachSet]
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, hs⟩)
        rw [show tgt e = b from ht]
        exact ih
  · intro h
    have key : ∀ j, ∀ w ∈ (stepSet src tgt F)^[j] {u}, (graphOf src tgt).Walks (F : Set (Fin m)) u w := by
      intro j
      induction j with
      | zero =>
        intro w hw
        rw [Finset.mem_singleton.mp hw]
        exact .refl
      | succ j ih =>
        intro w hw
        rw [Function.iterate_succ_apply'] at hw
        rcases Finset.mem_union.mp hw with hw | hw
        · rcases Finset.mem_union.mp hw with hw | hw
          · exact ih w hw
          · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hw
            obtain ⟨he₁, he₂⟩ := Finset.mem_filter.mp he
            exact (ih _ he₂).tail ⟨e, he₁, Or.inl ⟨rfl, rfl⟩⟩
        · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hw
          obtain ⟨he₁, he₂⟩ := Finset.mem_filter.mp he
          exact (ih _ he₂).tail ⟨e, he₁, Or.inr ⟨rfl, rfl⟩⟩
    exact key n w h

/-- A cut edge of the edges `F`, by computation. -/
theorem isCutIn_iff {F : Finset (Fin m)} {e : Fin m} : IsCutIn (graphOf src tgt) (F : Set (Fin m)) e ↔ e ∈ F ∧ tgt e ∉ reachSet src tgt (F.erase e) {src e} := by
  unfold IsCutIn
  rw [← Finset.coe_singleton e, ← Finset.coe_sdiff, Finset.sdiff_singleton_eq_erase, walks_iff]
  rfl

/-- **The edges of `C` are not cut edges of what contains them**, if the others join their ends. -/
theorem sameBlobIn_of_cycle {F : Set (Fin m)} {C : Finset (Fin m)} (hsub : (C : Set (Fin m)) ⊆ F) (hC : ∀ f ∈ C, tgt f ∈ reachSet src tgt (C.erase f) {src f}) {u w : Fin n}
    (h : w ∈ reachSet src tgt C {u}) : SameBlobIn (graphOf src tgt) F u w := by
  have hw : (graphOf src tgt).Walks (C : Set (Fin m)) u w := walks_iff.mpr h
  refine Relation.ReflTransGen.mono ?_ _ _ hw
  rintro a b ⟨e, he, hl⟩
  refine ⟨e, ⟨hsub he, fun hcut => hcut.2 ?_⟩, hl⟩
  have hw' : (graphOf src tgt).Walks ((C.erase e : Finset (Fin m)) : Set (Fin m)) (src e) (tgt e) := walks_iff.mpr (hC e he)
  refine Relation.ReflTransGen.mono ?_ _ _ hw'
  rintro x y ⟨g, hg, hl'⟩
  have hg' := Finset.mem_erase.mp hg
  exact ⟨g, ⟨hsub hg'.2, hg'.1⟩, hl'⟩

end Walks

/-! ### Colourings -/

/-- **A colouring determines a blob**: walks that avoid the cut edges at the blob keep their colour. -/
theorem determines_of_coloring {V E ι α : Type*} {G : DirectedMultigraph V E} {F : Set E} {v : V} {ℓ : ι → V} {S : Finset ι} (col : V → α)
    (hcol : ∀ e ∈ F, col (G.source e) ≠ col (G.target e) → e ∈ incidentCuts G F v) (hinj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → col (ℓ s) ≠ col (ℓ t)) : Determines G F v ℓ S := by
  intro s hs t ht hst hw
  have key : ∀ z, G.Walks (F \ incidentCuts G F v) (ℓ s) z → col (ℓ s) = col z := by
    intro z hz
    induction hz with
    | refl => rfl
    | tail _ hstep ih =>
      obtain ⟨e, he, (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)⟩ := hstep
      · rw [ih, ← h₁, ← h₂]
        exact by_contra fun hne => he.2 (hcol e he.1 hne)
      · rw [ih, ← h₁, ← h₂]
        exact by_contra fun hne => he.2 (hcol e he.1 fun h' => hne h'.symm)
  exact hinj s hs t ht hst (key _ hw)

section Cert

variable {n m k : ℕ} (src tgt : Fin m → Fin n) (ℓ : Fin k → Fin n)

/-- **The check of a colouring `col`** with the edges `F`: the edges `C` join a blob, the edges joining different colours are cut edges at that blob, and the taxa have different colours. -/
def Cert (F C : Finset (Fin m)) (v : Fin n) (col : Fin n → Fin n) (Q : Finset (Fin k)) : Prop :=
  C ⊆ F ∧ (∀ f ∈ C, tgt f ∈ reachSet src tgt (C.erase f) {src f}) ∧
    (∀ e ∈ F, col (src e) ≠ col (tgt e) → tgt e ∉ reachSet src tgt (F.erase e) {src e} ∧ (src e ∈ reachSet src tgt C {v} ∨ tgt e ∈ reachSet src tgt C {v})) ∧
    ∀ s ∈ Q, ∀ t ∈ Q, s ≠ t → col (ℓ s) ≠ col (ℓ t)

instance (F C : Finset (Fin m)) (v : Fin n) (col : Fin n → Fin n) (Q : Finset (Fin k)) : Decidable (Cert src tgt ℓ F C v col Q) := by
  unfold Cert
  exact instDecidableAnd

variable {src tgt ℓ}

/-- The check gives Definition 8. -/
theorem Cert.determines {F C : Finset (Fin m)} {v : Fin n} {col : Fin n → Fin n} {Q : Finset (Fin k)} (h : Cert src tgt ℓ F C v col Q) :
    Determines (graphOf src tgt) (F : Set (Fin m)) v ℓ Q := by
  obtain ⟨hsub, hC, hcut, hinj⟩ := h
  refine determines_of_coloring col (fun e he hne => ?_) hinj
  obtain ⟨h₁, h₂⟩ := hcut e he hne
  refine ⟨isCutIn_iff.mpr ⟨he, h₁⟩, ?_⟩
  rcases h₂ with h₂ | h₂
  · exact Or.inl (sameBlobIn_of_cycle (by exact_mod_cast hsub) hC h₂)
  · exact Or.inr (sameBlobIn_of_cycle (by exact_mod_cast hsub) hC h₂)

theorem Cert.mono {F C : Finset (Fin m)} {v : Fin n} {col : Fin n → Fin n} {Q Q' : Finset (Fin k)} (h : Cert src tgt ℓ F C v col Q) (hQ : Q' ⊆ Q) : Cert src tgt ℓ F C v col Q' :=
  ⟨h.1, h.2.1, h.2.2.1, fun s hs t ht => h.2.2.2 s (hQ hs) t (hQ ht)⟩

/-- **A colouring checked on the whole network works for any edges containing the blob**: a cut edge stays one in less of the network. -/
theorem Cert.determines_of_subset {C : Finset (Fin m)} {v : Fin n} {col : Fin n → Fin n} {Q : Finset (Fin k)} (h : Cert src tgt ℓ Finset.univ C v col Q) {F : Set (Fin m)} (hCF : (C : Set (Fin m)) ⊆ F) :
    Determines (graphOf src tgt) F v ℓ Q := by
  obtain ⟨-, hC, hcut, hinj⟩ := h
  refine determines_of_coloring col (fun e he hne => ?_) hinj
  obtain ⟨h₁, h₂⟩ := hcut e (Finset.mem_univ e) hne
  have hcu : IsCutIn (graphOf src tgt) ((Finset.univ : Finset (Fin m)) : Set (Fin m)) e := isCutIn_iff.mpr ⟨Finset.mem_univ e, h₁⟩
  refine ⟨isCutIn_of_subset (by simp) hcu he, ?_⟩
  rcases h₂ with h₂ | h₂
  · exact Or.inl (sameBlobIn_of_cycle hCF hC h₂)
  · exact Or.inr (sameBlobIn_of_cycle hCF hC h₂)

/-- The cut edges among the edges `F`. -/
def cutsOf (src tgt : Fin m → Fin n) (F : Finset (Fin m)) : Finset (Fin m) := F.filter fun e => tgt e ∉ reachSet src tgt (F.erase e) {src e}

/-- The nodes of the blob of `v` among the edges `F`. -/
def blobSet (src tgt : Fin m → Fin n) (F : Finset (Fin m)) (v : Fin n) : Finset (Fin n) := reachSet src tgt (F \ cutsOf src tgt F) {v}

/-- The cut edges at the blob of `v` among the edges `F`. -/
def incidentOf (src tgt : Fin m → Fin n) (F : Finset (Fin m)) (v : Fin n) : Finset (Fin m) :=
  (cutsOf src tgt F).filter fun e => src e ∈ blobSet src tgt F v ∨ tgt e ∈ blobSet src tgt F v

theorem sameBlobIn_iff {F : Finset (Fin m)} {u w : Fin n} : SameBlobIn (graphOf src tgt) (F : Set (Fin m)) u w ↔ w ∈ blobSet src tgt F u := by
  have hset : nonCutsIn (graphOf src tgt) (F : Set (Fin m)) = ((F \ cutsOf src tgt F : Finset (Fin m)) : Set (Fin m)) := by
    ext e
    simp only [nonCutsIn, isCutIn_iff, Set.mem_ofPred_eq, Finset.mem_coe, Finset.coe_sdiff, Set.mem_sdiff, cutsOf, Finset.coe_filter]
  unfold SameBlobIn
  rw [hset, walks_iff]
  rfl

theorem incidentCuts_eq {F : Finset (Fin m)} {v : Fin n} : incidentCuts (graphOf src tgt) (F : Set (Fin m)) v = (incidentOf src tgt F v : Finset (Fin m)) := by
  ext e
  simp only [incidentCuts, isCutIn_iff, sameBlobIn_iff, Set.mem_ofPred_eq, Finset.mem_coe, incidentOf, Finset.mem_filter, cutsOf]

end Cert

/-! ### Ancestors -/

section Ancestors

variable {n m k : ℕ} (src tgt : Fin m → Fin n) (ℓ : Fin k → Fin n)

/-- One step up. -/
def ascend (S : Finset (Fin n)) : Finset (Fin n) := S ∪ (Finset.univ.filter fun e => tgt e ∈ S).image src

/-- The nodes above the taxa `Y`. -/
def ancSet (Y : Finset (Fin k)) : Finset (Fin n) := (ascend src tgt)^[n] (Y.image ℓ)

/-- The edges above the taxa `Y`. -/
def arcsOf (Y : Finset (Fin k)) : Finset (Fin m) := Finset.univ.filter fun e => tgt e ∈ ancSet src tgt ℓ Y

variable {src tgt ℓ} {r : Fin n}

theorem ancSet_mono {Y Y' : Finset (Fin k)} (h : Y ⊆ Y') : ancSet src tgt ℓ Y ⊆ ancSet src tgt ℓ Y' := by
  have key : ∀ j, (ascend src tgt)^[j] (Y.image ℓ) ⊆ (ascend src tgt)^[j] (Y'.image ℓ) := by
    intro j
    induction j with
    | zero => exact Finset.image_subset_image h
    | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ (ih hx)
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, ih (Finset.mem_filter.mp he).2⟩, rfl⟩)
  exact key n

theorem arcsOf_mono {Y Y' : Finset (Fin k)} (h : Y ⊆ Y') : arcsOf src tgt ℓ Y ⊆ arcsOf src tgt ℓ Y' := fun e he =>
  Finset.mem_filter.mpr ⟨Finset.mem_univ e, ancSet_mono h (Finset.mem_filter.mp he).2⟩

/-- **What `ancSet` computes.** -/
theorem mem_ancestralVertices_iff {Y : Finset (Fin k)} (hY : Y.Nonempty) {v : Fin n} : v ∈ (finNetwork src tgt r ℓ).ancestralVertices (Y : Set (Fin k)) ↔ v ∈ ancSet src tgt ℓ Y := by
  have hsub : ∀ S : Finset (Fin n), S ⊆ ascend src tgt S := fun _ _ hx => Finset.mem_union_left _ hx
  have hfix : ascend src tgt (ancSet src tgt ℓ Y) = ancSet src tgt ℓ Y := by
    have h := iterate_fixed (ascend src tgt) hsub (S := Y.image ℓ) (hY.image ℓ)
    rwa [Fintype.card_fin] at h
  constructor
  · rintro ⟨x, hx, hr⟩
    have hbase : ℓ x ∈ ancSet src tgt ℓ Y := by
      have hgrow : ∀ j, ℓ x ∈ (ascend src tgt)^[j] (Y.image ℓ) := by
        intro j
        induction j with
        | zero => exact Finset.mem_image_of_mem ℓ (Finset.mem_coe.mp hx)
        | succ j ih =>
          rw [Function.iterate_succ_apply']
          exact hsub _ ih
      exact hgrow n
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact hbase
    | @head a c hac _ ih =>
      obtain ⟨e, hs, ht⟩ := hac
      rw [← hfix]
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, ?_⟩, hs⟩)
      rw [show tgt e = c from ht]
      exact ih
  · intro hv
    have key : ∀ j, ∀ w ∈ (ascend src tgt)^[j] (Y.image ℓ), w ∈ (finNetwork src tgt r ℓ).ancestralVertices (Y : Set (Fin k)) := by
      intro j
      induction j with
      | zero =>
        intro w hw
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
        exact ⟨x, Finset.mem_coe.mpr hx, .refl⟩
      | succ j ih =>
        intro w hw
        rw [Function.iterate_succ_apply'] at hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact ih w hw
        · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hw
          obtain ⟨x, hx, hr⟩ := ih _ (Finset.mem_filter.mp he).2
          exact ⟨x, hx, hr.head ⟨e, rfl, rfl⟩⟩
    exact key n v hv

theorem ancestralArcs_eq {Y : Finset (Fin k)} (hY : Y.Nonempty) : (finNetwork src tgt r ℓ).ancestralArcs (Y : Set (Fin k)) = (arcsOf src tgt ℓ Y : Finset (Fin m)) := by
  ext e
  simp only [arcsOf, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  exact mem_ancestralVertices_iff hY

end Ancestors

/-! ### On the network -/

section Network

variable {n m k : ℕ} {src tgt : Fin m → Fin n} {r : Fin n} {ℓ : Fin k → Fin n}

/-- **A blob determined by a set**, by a colouring. -/
theorem isDeterminedBy_of_cert {Q : Finset (Fin k)} {C : Finset (Fin m)} {v : Fin n} {col : Fin n → Fin n} (h3 : 3 ≤ Q.card) (h : Cert src tgt ℓ Finset.univ C v col Q) :
    IsDeterminedBy (finNetwork src tgt r ℓ).graph (finNetwork src tgt r ℓ).leaf (blobOf (finNetwork src tgt r ℓ).graph v) Q := by
  have hd := h.determines
  rw [Finset.coe_univ] at hd
  exact isDeterminedBy_blobOf_iff.mpr ⟨h3, hd⟩

/-- **A B-quartet of an induced network**, by a colouring. -/
theorem onInduced_of_cert (hN : IsBinaryNetwork (finNetwork src tgt r ℓ)) {Y Q : Finset (Fin k)} (hY : (Y : Set (Fin k)).Nontrivial) (hQ : Q ⊆ Y) (h4 : Q.card = 4) {C : Finset (Fin m)} {v : Fin n}
    {col : Fin n → Fin n} (hv : v ∈ ancSet src tgt ℓ Y) (h : Cert src tgt ℓ (arcsOf src tgt ℓ Y) C v col Q) :
    IsBlobQuartetOnInduced hN (Y : Set (Fin k)) hY Q := by
  have hne : Y.Nonempty := Finset.coe_nonempty.mp hY.nonempty
  refine (Bridges.isBlobQuartetOnInduced_iff hN _ hY (Finset.coe_subset.mpr hQ) h4).mpr ⟨v, (mem_ancestralVertices_iff hne).mpr hv, ?_⟩
  rw [ancestralArcs_eq hne]
  exact h.determines

/-- **The degree of a blob**, by computation. -/
theorem blobDegree_finNetwork (v : Fin n) :
    blobDegree (finNetwork src tgt r ℓ) (blobOf (finNetwork src tgt r ℓ).graph v) =
      if r ∈ blobSet src tgt Finset.univ v then (incidentOf src tgt Finset.univ v).card + 1 else (incidentOf src tgt Finset.univ v).card := by
  have hd : cutDegree (finNetwork src tgt r ℓ).graph (blobOf (finNetwork src tgt r ℓ).graph v) = (incidentOf src tgt Finset.univ v).card := by
    rw [cutDegree, incidentCutEdges_blobOf, ← Set.ncard_coe_finset (incidentOf src tgt Finset.univ v), ← incidentCuts_eq, Finset.coe_univ]
    rfl
  have hb : blobOf (finNetwork src tgt r ℓ).graph r = blobOf (finNetwork src tgt r ℓ).graph v ↔ r ∈ blobSet src tgt Finset.univ v := by
    rw [← sameBlobIn_iff, Finset.coe_univ, eq_comm]
    exact (sameBlobIn_univ_iff (G := graphOf src tgt)).symm
  unfold blobDegree
  simp only [hd]
  change (if blobOf (finNetwork src tgt r ℓ).graph r = _ then _ else _) = _
  by_cases h : r ∈ blobSet src tgt Finset.univ v
  · simp only [hb.mpr h, h, ↓reduceIte]
  · have hn : ¬ blobOf (finNetwork src tgt r ℓ).graph r = blobOf (finNetwork src tgt r ℓ).graph v := fun h' => h (hb.mp h')
    simp only [hn, h, ↓reduceIte]

/-- **A B-quartet of an induced network**, by a colouring checked on the whole network. -/
theorem onInduced_of_cert_univ (hN : IsBinaryNetwork (finNetwork src tgt r ℓ)) {Y Q : Finset (Fin k)} (hY : (Y : Set (Fin k)).Nontrivial) (hQ : Q ⊆ Y) (h4 : Q.card = 4) {C : Finset (Fin m)} {v : Fin n}
    {col : Fin n → Fin n} (hv : v ∈ ancSet src tgt ℓ Y) (hCY : C ⊆ arcsOf src tgt ℓ Y) (h : Cert src tgt ℓ Finset.univ C v col Q) :
    IsBlobQuartetOnInduced hN (Y : Set (Fin k)) hY Q := by
  have hne : Y.Nonempty := Finset.coe_nonempty.mp hY.nonempty
  refine (Bridges.isBlobQuartetOnInduced_iff hN _ hY (Finset.coe_subset.mpr hQ) h4).mpr ⟨v, (mem_ancestralVertices_iff hne).mpr hv, ?_⟩
  rw [ancestralArcs_eq hne]
  exact h.determines_of_subset (Finset.coe_subset.mpr hCY)

/-- **`T_rd(𝒩⁻_Q)` is unresolved**, by a colouring. -/
theorem inducedHasStarTopology_of_cert (hN : IsBinaryNetwork (finNetwork src tgt r ℓ)) {a b c d : Fin k} (h : ({a, b, c, d} : Finset (Fin k)).card = 4) {C : Finset (Fin m)} {v : Fin n} {col : Fin n → Fin n}
    (hv : v ∈ ancSet src tgt ℓ {a, b, c, d}) (hc : Cert src tgt ℓ (arcsOf src tgt ℓ {a, b, c, d}) C v col {a, b, c, d}) : InducedHasStarTopology hN a b c d h := by
  refine (Bridges.inducedHasStarTopology_iff hN h).mpr ((Bridges.isBlobQuartetOnInduced_self_iff hN h).mp ?_)
  exact onInduced_of_cert hN _ (Finset.Subset.refl _) h hv hc

/-- The check of a cut edge of the edges above `Y`, with `P` on the side `S`, and `R` off it. -/
def CutCheck (src tgt : Fin m → Fin n) (ℓ : Fin k → Fin n) (Y P R : Finset (Fin k)) (e : Fin m) (S : Finset (Fin n)) : Prop :=
  e ∈ arcsOf src tgt ℓ Y ∧ (∀ f ∈ arcsOf src tgt ℓ Y, (((src f ∈ S ∧ tgt f ∉ S) ∨ (tgt f ∈ S ∧ src f ∉ S)) ↔ f = e)) ∧ (∀ x ∈ P, ℓ x ∈ S) ∧ ∀ x ∈ R, ℓ x ∉ S

instance (Y P R : Finset (Fin k)) (e : Fin m) (S : Finset (Fin n)) : Decidable (CutCheck src tgt ℓ Y P R e S) := by
  unfold CutCheck
  exact instDecidableAnd

theorem CutCheck.crosses {Y P R : Finset (Fin k)} {e : Fin m} {S : Finset (Fin n)} (hY : Y.Nonempty) (hc : CutCheck src tgt ℓ Y P R e S) :
    ∀ f ∈ (finNetwork src tgt r ℓ).ancestralArcs (Y : Set (Fin k)), (finNetwork src tgt r ℓ).graph.Crosses f (S : Set (Fin n)) ↔ f = e := by
  rw [ancestralArcs_eq hY]
  intro f hf
  have := hc.2.1 f (Finset.mem_coe.mp hf)
  simpa [DirectedMultigraph.Crosses, finNetwork] using this

/-- **`T_rd(𝒩⁻_Q)` has the topology `ab|cd`**, by a cut edge. -/
theorem inducedHasQuartetTopology_of_cut (hN : IsBinaryNetwork (finNetwork src tgt r ℓ)) {a b c d : Fin k} (h : ({a, b, c, d} : Finset (Fin k)).card = 4) {e : Fin m} {S : Finset (Fin n)}
    (hc : CutCheck src tgt ℓ {a, b, c, d} {a, b} {c, d} e S) : InducedHasQuartetTopology hN a b c d h := by
  have hne : ({a, b, c, d} : Finset (Fin k)).Nonempty := ⟨a, by simp⟩
  refine (Bridges.inducedHasQuartetTopology_iff hN h).mpr ⟨{a, b}, by simp [quartetTree_val], ?_⟩
  rw [quartetTree_taxa]
  refine ⟨e, ?_, (S : Set (Fin n)), hc.crosses hne, fun x hx => ?_⟩
  · rw [ancestralArcs_eq hne]
    exact hc.1
  · obtain ⟨-, -, hP, hR⟩ := hc
    have hx' := Finset.mem_coe.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    constructor
    · intro hxS
      rcases hx' with rfl | rfl | rfl | rfl
      · simp
      · simp
      · exact absurd hxS (hR _ (by simp))
      · exact absurd hxS (hR _ (by simp))
    · intro hxB
      have hxB' := Finset.mem_coe.mp hxB
      exact hP x hxB'

/-- **A set separated by a cut edge of the induced network is a T-quartet there.** -/
theorem not_onInduced_of_cut (hN : IsBinaryNetwork (finNetwork src tgt r ℓ)) {Y : Finset (Fin k)} (hY : (Y : Set (Fin k)).Nontrivial) {a b c d : Fin k} (hQ : ({a, b, c, d} : Finset (Fin k)) ⊆ Y)
    (h : ({a, b, c, d} : Finset (Fin k)).card = 4) {e : Fin m} {S : Finset (Fin n)} (hc : CutCheck src tgt ℓ Y {a, b} {c, d} e S) : ¬ IsBlobQuartetOnInduced hN (Y : Set (Fin k)) hY {a, b, c, d} := by
  have hne : Y.Nonempty := Finset.coe_nonempty.mp hY.nonempty
  have hP := hN.isPhylogenetic
  rintro hB
  obtain ⟨v, hv, hd⟩ := (Bridges.isBlobQuartetOnInduced_iff hN _ hY (Finset.coe_subset.mpr hQ) h).mp hB
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hmem : ∀ x ∈ ({a, b, c, d} : Finset (Fin k)), (finNetwork src tgt r ℓ).leaf x ∈ (finNetwork src tgt r ℓ).ancestralVertices (Y : Set (Fin k)) := fun x hx =>
    (finNetwork src tgt r ℓ).leaf_mem_ancestralVertices (Finset.mem_coe.mpr (hQ hx))
  refine Determines.no_split (T := (S : Set (Fin n))) (e := e) hd hab hcd (fun s hs => walks_ancestral hP hv (hmem s hs)) (fun f hf hcr => ((hc.crosses hne) f hf).mp hcr) ?_ ?_ ?_ ?_
  · exact Finset.mem_coe.mpr (hc.2.2.1 a (by simp))
  · exact Finset.mem_coe.mpr (hc.2.2.1 b (by simp))
  · exact fun h' => hc.2.2.2 c (by simp) (Finset.mem_coe.mp h')
  · exact fun h' => hc.2.2.2 d (by simp) (Finset.mem_coe.mp h')

end Network

end AllmanEtAl2023.FigureCheck
