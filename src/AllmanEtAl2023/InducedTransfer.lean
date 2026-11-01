module

public import AllmanEtAl2023.Bridges

/-!
# Allman, Baños, Mitchell, Rhodes 2023: cut-edge splits of an induced network on a subset

The induction of Theorem 3 applies itself to a network induced on fewer taxa, and then speaks of its induced 4-taxon networks. It needs those to be the induced 4-taxon networks of
`𝒩⁺`, as far as quartets go, and the paper doesn't say so (`a:claim:induced-induced`). The proof follows the three steps of Definition 6. Each step keeps which arcs dominate and which are
above which taxa (`RootedNetwork.Separates`, and `hasCutSplitOn_iff_separates` of the library says that this is the same as the cut-edge splits on any set of taxa):

* `retained_hasCutSplitOn_iff`: step 1;
* `suppress_hasCutSplitOn_iff`: step 2;
* `removeStem_hasCutSplitOn_iff`: step 3;
* `induced_hasCutSplitOn_iff`, `inducedCutSplit_induced_iff`: all of them.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph
open scoped Classical

namespace AllmanEtAl2023.Bridges

variable {V E X : Type*}

/-! ### Step 2: suppression -/

section Suppress

variable {P : RootedNetwork V E X} (hP : P.IsPhylogenetic)

omit hP in
/-- A chain does not use an arc whose source is off chains. -/
theorem avoidingReach_of_chainReach {e : E} (he : ¬ P.IsChainVertex (P.graph.source e)) {u w : V} (h : P.ChainReach u w) :
    P.AvoidingReach e u w := by
  induction h with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    obtain ⟨ha, f, hs, ht⟩ := hab
    refine ih.tail ⟨f, ?_, hs, ht⟩
    rintro rfl
    exact he (hs ▸ ha)

include hP in
/-- **Paths avoiding an arc, under suppression.** -/
theorem suppress_avoidingReach_iff (e : {e // ¬ P.IsChainVertex (P.graph.source e)}) (u v : {v // ¬ P.IsChainVertex v}) :
    (P.suppress hP).AvoidingReach e u v ↔ P.AvoidingReach e.1 u.1 v.1 := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail a b _ hab ih =>
      obtain ⟨g, hge, hs, ht⟩ := hab
      have hs' : P.graph.source g.1 = a.1 := congrArg Subtype.val hs
      have ht' : chainEnd hP (P.graph.target g.1) = b.1 := congrArg Subtype.val ht
      have hg' : g.1 ≠ e.1 := fun h => hge (Subtype.ext h)
      refine (ih.tail ⟨g.1, hg', hs', rfl⟩).trans ?_
      rw [← ht']
      exact avoidingReach_of_chainReach e.2 (chainReach_chainEnd hP _)
  · intro h
    have key : ∀ w, P.AvoidingReach e.1 u.1 w →
        (P.suppress hP).AvoidingReach e u ⟨chainEnd hP w, not_isChainVertex_chainEnd hP w⟩ := by
      intro w hw
      induction hw with
      | refl =>
        have : (⟨chainEnd hP u.1, not_isChainVertex_chainEnd hP u.1⟩ : {v // ¬ P.IsChainVertex v}) = u :=
          Subtype.ext (chainEnd_eq_self hP u.2)
        rw [this]
        exact .refl
      | @tail a b _ hab ih =>
        obtain ⟨f, hfe, hs, ht⟩ := hab
        by_cases ha : P.IsChainVertex a
        · have heq := chainEnd_eq_of_adj hP ha ⟨f, hs, ht⟩
          simpa only [heq] using ih
        · refine ih.tail ?_
          have hne : ¬ P.IsChainVertex (P.graph.source f) := hs ▸ ha
          refine ⟨⟨f, hne⟩, fun h => hfe (congrArg Subtype.val h), Subtype.ext ?_, ?_⟩
          · exact hs.trans (chainEnd_eq_self hP ha).symm
          · exact Subtype.ext (by subst ht; rfl)
    have := key _ h
    have heq : (⟨chainEnd hP v.1, not_isChainVertex_chainEnd hP v.1⟩ : {v // ¬ P.IsChainVertex v}) = v :=
      Subtype.ext (chainEnd_eq_self hP v.2)
    rwa [heq] at this

include hP in
theorem suppress_dominates_iff (e : {e // ¬ P.IsChainVertex (P.graph.source e)}) (x : X) :
    (P.suppress hP).Dominates e x ↔ P.Dominates e.1 x :=
  not_congr (suppress_avoidingReach_iff hP e _ _)

include hP in
/-- Paths of the suppressed network are paths of the network. -/
theorem reaches_of_suppress_reaches {u v : {v // ¬ P.IsChainVertex v}} (h : (P.suppress hP).graph.Reaches u v) :
    P.graph.Reaches u.1 v.1 := by
  induction h with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    obtain ⟨g, hs, ht⟩ := hab
    have hs' : P.graph.source g.1 = a.1 := congrArg Subtype.val hs
    have ht' : chainEnd hP (P.graph.target g.1) = b.1 := congrArg Subtype.val ht
    refine (ih.tail ⟨g.1, hs', rfl⟩).trans ?_
    rw [← ht']
    exact (chainReach_chainEnd hP _).reaches

include hP in
/-- A path from a node to a node off chains passes through the end of its chain. -/
theorem chainEnd_reaches {w t : V} (h : P.graph.Reaches w t) (ht : ¬ P.IsChainVertex t) : P.graph.Reaches (chainEnd hP w) t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rw [chainEnd_eq_self hP ht]
    exact .refl
  | @head a b hab hbt ih =>
    by_cases ha : P.IsChainVertex a
    · rw [chainEnd_eq_of_adj hP ha hab]
      exact ih
    · rw [chainEnd_eq_self hP ha]
      exact hbt.head hab

include hP in
theorem suppress_isBelow_iff (e : {e // ¬ P.IsChainVertex (P.graph.source e)}) (x : X) :
    (P.suppress hP).IsBelow e x ↔ P.IsBelow e.1 x := by
  constructor
  · intro h
    have h' := reaches_of_suppress_reaches hP h
    exact ((chainReach_chainEnd hP _).reaches).trans h'
  · intro h
    exact suppress_reaches_of_reaches hP _ _ (chainEnd_reaches hP h (not_isChainVertex_leaf hP x))

include hP in
theorem suppress_separates_iff (e : {e // ¬ P.IsChainVertex (P.graph.source e)}) (A B : Set X) :
    (P.suppress hP).Separates e A B ↔ P.Separates e.1 A B := by
  unfold RootedNetwork.Separates
  simp only [suppress_dominates_iff hP, suppress_isBelow_iff hP]

include hP in
/-- One step up a chain: the arc into a chain vertex dominates what the arc out of it dominates. -/
theorem Separates.of_step {e g : E} {A B : Set X} (hs : P.IsChainVertex (P.graph.source e))
    (hg : P.graph.target g = P.graph.source e) (h : P.Separates e A B) : P.Separates g A B := by
  obtain ⟨gg, hgg⟩ := (P.graph.indegree_eq_one_iff _).mp hs.1
  obtain ⟨ee, hee⟩ := (P.graph.outdegree_eq_one_iff _).mp hs.2
  refine ⟨fun x hx hav => h.1 x hx ?_, fun y hy hb => h.2 y hy ?_⟩
  · have key : ∀ w, P.AvoidingReach g P.root w → w ≠ P.graph.source e ∧ P.AvoidingReach e P.root w := by
      intro w hw
      induction hw with
      | refl => exact ⟨fun h => not_isChainVertex_root hP (h ▸ hs), .refl⟩
      | @tail a b _ hab ih =>
        obtain ⟨f, hfg, hfs, hft⟩ := hab
        refine ⟨fun hb => hfg ?_, ih.2.tail ⟨f, ?_, hfs, hft⟩⟩
        · rw [(hgg f).mp (hft.trans hb), (hgg g).mp hg]
        · rintro rfl
          exact ih.1 hfs.symm
    exact (key _ hav).2
  · have hb' : P.graph.Reaches (P.graph.source e) (P.leaf y) := hg ▸ hb
    rcases Relation.ReflTransGen.cases_head hb' with h' | ⟨c, ⟨f, hfs, hft⟩, hc⟩
    · exact absurd (h' ▸ hs) (not_isChainVertex_leaf hP y)
    · have hfe : f = e := by rw [(hee f).mp hfs, (hee e).mp rfl]
      subst hfe
      change P.graph.Reaches _ _
      rw [hft]
      exact hc

include hP in
/-- An arc on a chain separates only what the arc starting the chain separates. -/
theorem Separates.of_isOnChain {f e : E} {A B : Set X} (hon : P.IsOnChain f e) (h : P.Separates e A B) : P.Separates f A B := by
  rcases hon with rfl | ⟨hs, hc⟩
  · exact h
  · have key : ∀ w, P.ChainReach (P.graph.target f) w → ∀ e', P.graph.source e' = w → P.IsChainVertex w →
        P.Separates e' A B → P.Separates f A B := by
      intro w hw
      induction hw with
      | refl => exact fun e' he' hch h' => Separates.of_step hP (he' ▸ hch) he'.symm h'
      | @tail a b _ hab ih =>
        intro e' he' hch h'
        obtain ⟨ha, g, hgs, hgt⟩ := hab
        exact ih g hgs ha (Separates.of_step hP (he' ▸ hch) (hgt.trans he'.symm) h')
    exact key _ hc e rfl hs h

include hP in
/-- **Step 2 of Definition 6 keeps the cut-edge splits on any set of taxa.** -/
theorem suppress_hasCutSplitOn_iff (Z A : Set X) : (P.suppress hP).HasCutSplitOn Z A ↔ P.HasCutSplitOn Z A := by
  rw [hasCutSplitOn_iff_separates (suppress_isPhylogenetic hP), hasCutSplitOn_iff_separates hP]
  constructor
  · rintro ⟨e, h⟩
    refine ⟨e.1, ?_⟩
    simpa only [suppress_separates_iff hP] using h
  · rintro ⟨e, h⟩
    obtain ⟨f, hf, hon⟩ := exists_isOnChain hP e
    refine ⟨⟨f, hf⟩, ?_⟩
    simp only [suppress_separates_iff hP]
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨h₁, Separates.of_isOnChain hP hon h₂⟩
    · exact Or.inr ⟨h₁, Separates.of_isOnChain hP hon h₂⟩

end Suppress

/-! ### Step 3: removing a stem -/

section Stem

variable {M : RootedNetwork V E X} (hM : M.IsPhylogenetic)

include hM in
/-- Paths avoiding an arc, on removing a stem. -/
theorem removeStem_avoidingReach_iff (e : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)})
    (u v : {v // ¬ (HasStem M ∧ v = M.root)}) :
    (removeStem M hM).AvoidingReach e u v ↔ M.AvoidingReach e.1 u.1 v.1 := by
  constructor
  · intro h
    refine Relation.ReflTransGen.lift Subtype.val ?_ u v h
    rintro a b ⟨f, hfe, hs, ht⟩
    exact ⟨f.1, fun h => hfe (Subtype.ext h), congrArg Subtype.val hs, congrArg Subtype.val ht⟩
  · intro h
    have key : ∀ w, M.AvoidingReach e.1 u.1 w → ∃ hw : ¬ (HasStem M ∧ w = M.root), (removeStem M hM).AvoidingReach e u ⟨w, hw⟩ := by
      intro w hw
      induction hw with
      | refl => exact ⟨u.2, .refl⟩
      | @tail a b _ hab ih =>
        obtain ⟨ha, hr⟩ := ih
        obtain ⟨f, hfe, hs, ht⟩ := hab
        refine ⟨fun h => target_ne_root hM f (ht.trans h.2), hr.tail ?_⟩
        exact ⟨⟨f, fun h => ha ⟨h.1, hs ▸ h.2⟩⟩, fun h => hfe (congrArg Subtype.val h), Subtype.ext hs, Subtype.ext ht⟩
    exact (key _ h).2

include hM in
theorem removeStem_dominates_iff (e : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}) (x : X) :
    (removeStem M hM).Dominates e x ↔ M.Dominates e.1 x := by
  refine not_congr ((removeStem_avoidingReach_iff hM e _ _).trans ?_)
  by_cases hst : HasStem M
  · have hroot : ((removeStem M hM).root).1 = M.graph.target (stemArc M hst) := by
      simp only [removeStem, dite_eq_left hst]
    rw [hroot]
    have hne : stemArc M hst ≠ e.1 := fun h => e.2 ⟨hst, h ▸ (stemArc_spec M hst _).mpr rfl⟩
    constructor
    · exact fun h => Relation.ReflTransGen.head ⟨stemArc M hst, hne, (stemArc_spec M hst _).mpr rfl, rfl⟩ h
    · intro h
      rcases Relation.ReflTransGen.cases_head h with h' | ⟨c, ⟨f, -, hfs, hft⟩, hc⟩
      · exact absurd h'.symm (M.leaf_ne_root hM x)
      · rw [(stemArc_spec M hst f).mp hfs] at hft
        rwa [hft]
  · have hroot : ((removeStem M hM).root).1 = M.root := by
      simp only [removeStem, dite_eq_right hst]
    rw [hroot]
    rfl

include hM in
/-- Directed paths, on removing a stem. -/
theorem removeStem_reaches_iff (u v : {v // ¬ (HasStem M ∧ v = M.root)}) :
    (removeStem M hM).graph.Reaches u v ↔ M.graph.Reaches u.1 v.1 := by
  constructor
  · intro h
    refine Relation.ReflTransGen.lift Subtype.val ?_ u v h
    rintro a b ⟨f, hs, ht⟩
    exact ⟨f.1, congrArg Subtype.val hs, congrArg Subtype.val ht⟩
  · intro h
    have key : ∀ w, M.graph.Reaches u.1 w → ∃ hw : ¬ (HasStem M ∧ w = M.root), (removeStem M hM).graph.Reaches u ⟨w, hw⟩ := by
      intro w hw
      induction hw with
      | refl => exact ⟨u.2, .refl⟩
      | @tail a b _ hab ih =>
        obtain ⟨ha, hr⟩ := ih
        obtain ⟨f, hs, ht⟩ := hab
        refine ⟨fun h => target_ne_root hM f (ht.trans h.2), hr.tail ?_⟩
        exact ⟨⟨f, fun h => ha ⟨h.1, hs ▸ h.2⟩⟩, Subtype.ext hs, Subtype.ext ht⟩
    exact (key _ h).2

include hM in
theorem removeStem_isBelow_iff (e : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}) (x : X) :
    (removeStem M hM).IsBelow e x ↔ M.IsBelow e.1 x :=
  removeStem_reaches_iff hM _ _

include hM in
theorem removeStem_separates_iff (e : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}) (A B : Set X) :
    (removeStem M hM).Separates e A B ↔ M.Separates e.1 A B := by
  unfold RootedNetwork.Separates
  simp only [removeStem_dominates_iff hM, removeStem_isBelow_iff hM]

include hM in
/-- The stem is above every taxon, so it doesn't separate. -/
theorem separates_keeps {e : E} {A B : Set X} (hB : B.Nonempty) (h : M.Separates e A B) :
    ¬ (HasStem M ∧ M.graph.source e = M.root) := by
  rintro ⟨hst, hs⟩
  obtain ⟨y, hy⟩ := hB
  have hee := (stemArc_spec M hst e).mp hs
  refine h.2 y hy ?_
  rw [hee]
  exact target_stemArc_reaches hM hst (M.leaf_ne_root hM y)

include hM in
/-- **Step 3 of Definition 6 keeps the cut-edge splits on a set of taxa, with a taxon on each side.** -/
theorem removeStem_hasCutSplitOn_iff [Nontrivial X] {Z A : Set X} (h₁ : (Z ∩ A).Nonempty) (h₂ : (Z \ A).Nonempty) :
    (removeStem M hM).HasCutSplitOn Z A ↔ M.HasCutSplitOn Z A := by
  rw [hasCutSplitOn_iff_separates (removeStem_isPhylogenetic hM), hasCutSplitOn_iff_separates hM]
  constructor
  · rintro ⟨e, h⟩
    refine ⟨e.1, ?_⟩
    simpa only [removeStem_separates_iff hM] using h
  · rintro ⟨e, h⟩
    rcases h with ⟨hne, h⟩ | ⟨hne, h⟩
    · exact ⟨⟨e, separates_keeps hM h₂ h⟩, Or.inl ⟨hne, (removeStem_separates_iff hM _ _ _).mpr h⟩⟩
    · exact ⟨⟨e, separates_keeps hM h₁ h⟩, Or.inr ⟨hne, (removeStem_separates_iff hM _ _ _).mpr h⟩⟩

end Stem

/-! ### Step 1, and all of it -/

section Retained

variable {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) {Y : Set X} (hY : Y.Nontrivial)

/-- **Step 1 of Definition 6 keeps the cut-edge splits on a subset of `Y`, with a taxon on each side.** -/
theorem retained_hasCutSplitOn_iff {Z A : Set X} (hZ : Z ⊆ Y) (h₁ : (Z ∩ A).Nonempty) (h₂ : (Z \ A).Nonempty) :
    (retained hN Y hY).HasCutSplitOn (Subtype.val ⁻¹' Z) (Subtype.val ⁻¹' A) ↔ N.HasCutSplitOn Z A := by
  have hP := hN.isPhylogenetic
  have hR := retained_isPhylogenetic hN Y hY
  have hst := N.root_isStableAncestor Y
  have hdom : ∀ (e : N.belowArcs N.root Y) (x : Y), (retained hN Y hY).Dominates e x ↔ N.Dominates e.1 x.1 :=
    fun e x => belowNetwork_dominates_iff hP hst
  have hbel : ∀ (e : N.belowArcs N.root Y) (x : Y), (retained hN Y hY).IsBelow e x ↔ N.IsBelow e.1 x.1 :=
    fun e x => belowNetwork_isBelow_iff
  have htransfer : ∀ (e : N.belowArcs N.root Y) (S T : Set X), S ⊆ Y → T ⊆ Y →
      ((retained hN Y hY).Separates e (Subtype.val ⁻¹' S) (Subtype.val ⁻¹' T) ↔ N.Separates e.1 S T) := by
    intro e S T hS hT
    constructor
    · rintro ⟨hd, hn⟩
      exact ⟨fun x hx => (hdom e ⟨x, hS hx⟩).mp (hd _ hx), fun x hx hb => hn ⟨x, hT hx⟩ hx ((hbel e _).mpr hb)⟩
    · rintro ⟨hd, hn⟩
      exact ⟨fun x hx => (hdom e x).mpr (hd _ hx), fun x hx hb => hn _ hx ((hbel e x).mp hb)⟩
  have hkeep : ∀ (e : E) (S T : Set X), S ⊆ Y → S.Nonempty → N.Separates e S T → e ∈ N.belowArcs N.root Y := by
    rintro e S T hS ⟨x, hx⟩ ⟨hd, -⟩
    exact (mem_belowArcs_root_iff hN e).mpr ⟨x, hS hx, (hd x hx).isBelow hP⟩
  have hin₁ : Z ∩ A ⊆ Y := fun x hx => hZ hx.1
  have hin₂ : Z \ A ⊆ Y := fun x hx => hZ hx.1
  have hset₁ : (Subtype.val ⁻¹' Z ∩ Subtype.val ⁻¹' A : Set Y) = Subtype.val ⁻¹' (Z ∩ A) := rfl
  have hset₂ : (Subtype.val ⁻¹' Z \ Subtype.val ⁻¹' A : Set Y) = Subtype.val ⁻¹' (Z \ A) := rfl
  have hne₁ : (Subtype.val ⁻¹' (Z ∩ A) : Set Y).Nonempty := by
    obtain ⟨x, hx⟩ := h₁
    exact ⟨⟨x, hin₁ hx⟩, hx⟩
  have hne₂ : (Subtype.val ⁻¹' (Z \ A) : Set Y).Nonempty := by
    obtain ⟨x, hx⟩ := h₂
    exact ⟨⟨x, hin₂ hx⟩, hx⟩
  rw [hasCutSplitOn_iff_separates hR, hasCutSplitOn_iff_separates hP, hset₁, hset₂]
  constructor
  · rintro ⟨e, ⟨-, h⟩ | ⟨-, h⟩⟩
    · exact ⟨e.1, Or.inl ⟨h₁, (htransfer e _ _ hin₁ hin₂).mp h⟩⟩
    · exact ⟨e.1, Or.inr ⟨h₂, (htransfer e _ _ hin₂ hin₁).mp h⟩⟩
  · rintro ⟨e, ⟨-, h⟩ | ⟨-, h⟩⟩
    · have he := hkeep e _ _ hin₁ h₁ h
      exact ⟨⟨e, he⟩, Or.inl ⟨hne₁, (htransfer ⟨e, he⟩ _ _ hin₁ hin₂).mpr h⟩⟩
    · have he := hkeep e _ _ hin₂ h₂ h
      exact ⟨⟨e, he⟩, Or.inr ⟨hne₂, (htransfer ⟨e, he⟩ _ _ hin₂ hin₁).mpr h⟩⟩

/-- **The cut-edge splits, on a subset `Z` of `Y`, of the network induced on `Y`, are those of the network.** -/
theorem induced_hasCutSplitOn_iff {Z A : Set X} (hZ : Z ⊆ Y) (h₁ : (Z ∩ A).Nonempty) (h₂ : (Z \ A).Nonempty) :
    (induced hN Y hY).HasCutSplitOn (Subtype.val ⁻¹' Z) (Subtype.val ⁻¹' A) ↔ N.HasCutSplitOn Z A := by
  have : Nontrivial Y := hY.coe_sort
  have hne₁ : (Subtype.val ⁻¹' Z ∩ Subtype.val ⁻¹' A : Set Y).Nonempty := by
    obtain ⟨x, hx⟩ := h₁
    exact ⟨⟨x, hZ hx.1⟩, hx⟩
  have hne₂ : (Subtype.val ⁻¹' Z \ Subtype.val ⁻¹' A : Set Y).Nonempty := by
    obtain ⟨x, hx⟩ := h₂
    exact ⟨⟨x, hZ hx.1⟩, hx⟩
  exact (removeStem_hasCutSplitOn_iff _ hne₁ hne₂).trans
    ((suppress_hasCutSplitOn_iff (retained_isPhylogenetic hN Y hY) _ _).trans
      (retained_hasCutSplitOn_iff hN hY hZ h₁ h₂))

end Retained

/-! ### Quartet trees -/

section Quartets

variable {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) {Y : Set X} (hY : Y.Nontrivial) [DecidableEq X]

/-- **The cut-edge split `s` of an induced 4-taxon network of `𝒩⁺_Y` is the cut-edge split of the induced 4-taxon network of `𝒩⁺`.** -/
theorem inducedCutSplit_induced_iff [Fintype X] [Fintype Y] [DecidableEq Y] (s : QuartetTree Y) :
    InducedCutSplit (induced hN Y hY) s ↔ InducedCutSplit N (s.map Subtype.val_injective) := by
  have key : ∀ B ∈ s.val, (induced hN Y hY).HasCutSplitOn (s.taxa : Set Y) (B : Set Y) ↔
      N.HasCutSplitOn ((s.taxa.image Subtype.val : Finset X) : Set X) ((B.image Subtype.val : Finset X) : Set X) := by
    intro B hB
    have hBs : B ⊆ s.taxa := QuartetTree.subset_taxa _ hB
    have hZ : ((s.taxa.image Subtype.val : Finset X) : Set X) ⊆ Y := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact y.2
    have hpre : ∀ T : Finset Y, (Subtype.val ⁻¹' ((T.image Subtype.val : Finset X) : Set X) : Set Y) = T := fun T => by
      rw [Finset.coe_image]
      exact Set.preimage_image_eq _ Subtype.val_injective
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [s.2.2.1 _ hB]; omega : 0 < B.card)
    have hother := QuartetTree.sdiff_mem _ hB
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by rw [s.2.2.1 _ hother]; omega : 0 < (s.taxa \ B).card)
    obtain ⟨hzt, hzB⟩ := Finset.mem_sdiff.mp hz
    have h₁ : (((s.taxa.image Subtype.val : Finset X) : Set X) ∩ ((B.image Subtype.val : Finset X) : Set X)).Nonempty :=
      ⟨y.1, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (hBs hy)), Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hy)⟩
    have h₂ : (((s.taxa.image Subtype.val : Finset X) : Set X) \ ((B.image Subtype.val : Finset X) : Set X)).Nonempty := by
      refine ⟨z.1, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hzt), fun hzB' => ?_⟩
      obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hzB')
      exact hzB (Subtype.ext hwz ▸ hw)
    have := induced_hasCutSplitOn_iff hN hY hZ h₁ h₂
    rwa [hpre, hpre] at this
  constructor
  · rintro ⟨B, hB, hcut⟩
    refine ⟨B.image Subtype.val, Finset.mem_image_of_mem _ hB, ?_⟩
    rw [QuartetTree.map_taxa]
    exact (key B hB).mp hcut
  · rintro ⟨B', hB', hcut⟩
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB'
    rw [QuartetTree.map_taxa] at hcut
    exact ⟨B, hB, (key B hB).mpr hcut⟩

/-- A quartet tree of `Y`, as a quartet tree of `X`. -/
theorem map_quartetTree [DecidableEq Y] {a b c d : Y} (h : ({a, b, c, d} : Finset Y).card = 4)
    (h' : ({a.1, b.1, c.1, d.1} : Finset X).card = 4) :
    QuartetTree.map (ι := Subtype.val) Subtype.val_injective (quartetTree a b c d h) = quartetTree a.1 b.1 c.1 d.1 h' := by
  apply Subtype.ext
  simp [QuartetTree.map_val, Finset.image_insert, Finset.image_singleton]

/-- The trees on four taxa, as what `IsTreelike` says. -/
theorem isTreelike_quartet_iff [Fintype X] {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    IsTreelike N {a, b, c, d} ↔ InducedCutSplit N (quartetTree a b c d h) ∨
      InducedCutSplit N (quartetTree a c b d (card_acbd h)) ∨ InducedCutSplit N (quartetTree a d b c (card_adbc h)) := by
  unfold IsTreelike
  rw [treesOn_eq h]
  simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]

/-- `IsTreelike` of the network induced on `Y`. -/
theorem isTreelike_induced_iff [Fintype X] [Fintype Y] [DecidableEq Y] {a b c d : Y} (h : ({a, b, c, d} : Finset Y).card = 4)
    (h' : ({a.1, b.1, c.1, d.1} : Finset X).card = 4) :
    IsTreelike (induced hN Y hY) {a, b, c, d} ↔ IsTreelike N {a.1, b.1, c.1, d.1} := by
  rw [isTreelike_quartet_iff h, isTreelike_quartet_iff h', inducedCutSplit_induced_iff hN hY, inducedCutSplit_induced_iff hN hY,
    inducedCutSplit_induced_iff hN hY, map_quartetTree h h', map_quartetTree (card_acbd h) (card_acbd h'),
    map_quartetTree (card_adbc h) (card_adbc h')]

/-- **The unresolved topology of `T_rd(𝒩⁻_Q)` is `¬ IsTreelike`.** -/
theorem inducedHasStarTopology_iff [Fintype X] {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    InducedHasStarTopology hN a b c d h ↔ ¬ IsTreelike N {a, b, c, d} := by
  rw [← isBlobQuartetOnInduced_self_iff hN h]
  let Q : Finset X := {a, b, c, d}
  have hQnt := nontrivial_coe_of_card_four h
  have hM := induced_isBinaryNetwork hN (Q : Set X) hQnt
  have hcard : Fintype.card ↥(Q : Set X) = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact h
  let a' : ↥(Q : Set X) := ⟨a, by simp [Q]⟩
  let b' : ↥(Q : Set X) := ⟨b, by simp [Q]⟩
  let c' : ↥(Q : Set X) := ⟨c, by simp [Q]⟩
  let d' : ↥(Q : Set X) := ⟨d, by simp [Q]⟩
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have sne : ∀ {x y : ↥(Q : Set X)}, x.1 ≠ y.1 → x ≠ y := fun hxy he => hxy (congrArg Subtype.val he)
  have h' : ({a', b', c', d'} : Finset ↥(Q : Set X)).card = 4 :=
    TreeMetric.card_four_of_ne (sne hab) (sne hac) (sne had) (sne hbc) (sne hbd) (sne hcd)
  have hsub : ∀ inst : DecidablePred (· ∈ (Q : Set X)), @Finset.subtype X (· ∈ (Q : Set X)) inst Q = {a', b', c', d'} := by
    intro inst
    ext z
    obtain ⟨z, hz⟩ := z
    simp only [Finset.mem_subtype, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, a', b', c', d']
    simp [Q]
  have hgoal : IsBlobQuartetOnInduced hN (Q : Set X) hQnt Q ↔ IsBlobQuartet (induced hN (Q : Set X) hQnt) {a', b', c', d'} := by
    unfold IsBlobQuartetOnInduced
    rw [hsub]
  have hB := isBlobQuartet_iff_isBQuartet hM.isPhylogenetic h'
  have hu : (Trd hM (nontrivial_of_card_four hcard)).DisplaysUnresolved {a', b', c', d'} ↔ IsBQuartet (induced hN (Q : Set X) hQnt) {a', b', c', d'} := by
    unfold LabelledGraph.DisplaysUnresolved IsBQuartet
    rw [splits_Trd hM]
    exact ⟨fun hu => hu.2, fun hu => ⟨h', hu⟩⟩
  exact (hasStarTopology_iff_displaysUnresolved hM hcard h').trans (hu.trans (hB.symm.trans hgoal.symm))

end Quartets

end AllmanEtAl2023.Bridges
