module

public import AllmanEtAl2023.Basic
public import AllmanEtAl2023.Concordance
public import AllmanEtAl2023.Lemma2
public import AllmanEtAl2023.TreeSuppression

/-!
# Allman, Baños, Mitchell, Rhodes 2023: bridges between the paper's objects and the older representation

The numbered results are stated on the paper's objects, in `AllmanEtAl2023.Printed`. `src/AllmanEtAl2023/SubgraphBlobs.lean`, `CutOrder.lean`,
`CycleLemma.lean`, `Reduction.lean`, `Basic.lean`, `Theorem1.lean`, `Corollary1.lean` are stated on another representation, through split
families and cut-edge splits on ancestral subgraphs. These are the bridges:

* `isBlobQuartet_iff_isBQuartet`: Definition 12 and `Phylogenetics.IsBQuartet` (proved).
* `isBlobQuartet_iff_exists_determines`, `exists_isDeterminedBy_three` (proved).
* `removeStem_hasCutSplit_iff`, `induced_hasCutSplit_iff` (proved): the cut-edge splits of the paper's induced network are
  `RootedNetwork.HasCutSplitOn` of the library, with both sides nonempty.
* `isBlobQuartetOnInduced_iff`, `isBlobQuartetOnInduced_self_iff`, `isTreelike_iff_resolves` (proved): a B-quartet on the induced network, in the older forms.
* `inducedHasQuartetTopology_iff`: the resolved topology on the induced network is `InducedCutSplit`, from `hasQuartetTopology_iff_displays`.
* `unrootAt_cut_iff`, `lsaPlus_hasCutSplit_iff`, `splits_Trd` (proved): the splits of the graph `T_rd(𝒩⁻)` are `Phylogenetics.treeOfBlobs`.
* `hasQuartetTopology_iff_displays`, `hasStarTopology_iff_displaysUnresolved`: on four taxa, the literal topologies are the displayed
  ones (`sorry`; the content of the last sentences of Lemma 1).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph
open scoped Classical

namespace AllmanEtAl2023.Bridges

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### B-quartets -/

/-- On a phylogenetic network, every arc is ancestral to a taxon. -/
theorem ancestralArcs_univ (hN : N.IsPhylogenetic) : N.ancestralArcs Set.univ = Set.univ := by
  refine Set.eq_univ_of_forall fun e => ?_
  obtain ⟨x, hx⟩ := exists_reaches_leaf hN (N.graph.target e)
  exact ⟨x, Set.mem_univ x, hx⟩

/-- On a phylogenetic network, every node is ancestral to a taxon. -/
theorem ancestralVertices_univ (hN : N.IsPhylogenetic) : N.ancestralVertices Set.univ = Set.univ := by
  refine Set.eq_univ_of_forall fun v => ?_
  obtain ⟨x, hx⟩ := exists_reaches_leaf hN v
  exact ⟨x, Set.mem_univ x, hx⟩

/-- **Definition 12 in the language of the older code.** -/
theorem isBlobQuartet_iff_exists_determines {Q : Finset X} (hQ : Q.card = 4) :
    IsBlobQuartet N Q ↔ ∃ v, Determines N.graph Set.univ v N.leaf Q := by
  have h3 : 3 ≤ Q.card := by omega
  constructor
  · rintro ⟨-, b, hb⟩
    induction b using Quotient.inductionOn with
    | h v => exact ⟨v, (Printed.isDeterminedBy_blobOf_iff.mp hb).2⟩
  · rintro ⟨v, hv⟩
    exact ⟨hQ, blobOf _ v, Printed.isDeterminedBy_blobOf_iff.mpr ⟨h3, hv⟩⟩

/-- **Definition 12 is the library's B-quartet**, on phylogenetic networks. The library says that the tree of blobs resolves no
quartet tree on the set, and Definition 12 says that a blob is determined by the set. -/
theorem isBlobQuartet_iff_isBQuartet [Fintype X] [DecidableEq X] (hN : N.IsPhylogenetic) {Q : Finset X} (hQ : Q.card = 4) :
    IsBlobQuartet N Q ↔ IsBQuartet N Q := by
  rw [isBlobQuartet_iff_exists_determines hQ, isBQuartet_iff_not_resolves hN hQ,
    not_resolves_iff_exists_determines hN (Finset.subset_univ Q) hQ, Finset.coe_univ,
    ancestralArcs_univ hN, ancestralVertices_univ hN]
  simp

/-- **"On a network `𝒩⁺` every subset of 3 taxa determines a blob"** (`a:claim:three-taxa`). -/
theorem exists_isDeterminedBy_three [DecidableEq X] (hN : N.IsPhylogenetic) {a b c : X} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ∃ B, IsDeterminedBy N.graph N.leaf B {a, b, c} := by
  obtain ⟨v, -, hv⟩ := exists_determines_three (N := N) (Z := Set.univ) hN (Set.mem_univ a) (Set.mem_univ b)
    (Set.mem_univ c) hab hac hbc
  rw [ancestralArcs_univ hN] at hv
  have h3 : ({a, b, c} : Finset X).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  exact ⟨blobOf _ v, Printed.isDeterminedBy_blobOf_iff.mpr ⟨h3.ge, hv⟩⟩

/-! ### Cut-edge splits of the induced network -/

section Stem

variable {M : RootedNetwork V E X}

/-- **Removing a stem keeps the cut-edge splits with a taxon on each side.** -/
theorem removeStem_hasCutSplit_iff (hM : M.IsPhylogenetic) {A : Set X} (h₁ : A.Nonempty) (h₂ : Aᶜ.Nonempty) :
    (removeStem M hM).HasCutSplit A ↔ M.HasCutSplit A := by
  have : Finite E := hM.finite_arcs
  constructor
  · rintro ⟨e, S, hS, rfl⟩
    by_cases hst : HasStem M
    · -- the root goes with its child
      let c := M.graph.target (stemArc M hst)
      have hcne : ¬ (HasStem M ∧ c = M.root) := fun h => target_ne_root hM _ h.2
      let T : Set V := {v | (v = M.root ∧ (⟨c, hcne⟩ : {v // ¬ (HasStem M ∧ v = M.root)}) ∈ S) ∨
        ∃ h' : ¬ (HasStem M ∧ v = M.root), (⟨v, h'⟩ : {v // ¬ (HasStem M ∧ v = M.root)}) ∈ S}
      have hmem : ∀ v (hv : ¬ (HasStem M ∧ v = M.root)), v ∈ T ↔ (⟨v, hv⟩ : {v // ¬ (HasStem M ∧ v = M.root)}) ∈ S := by
        intro v hv
        constructor
        · rintro (⟨hr, -⟩ | ⟨_, h⟩)
          · exact absurd ⟨hst, hr⟩ hv
          · exact h
        · exact fun h => Or.inr ⟨hv, h⟩
      have hroot : M.root ∈ T ↔ (⟨c, hcne⟩ : {v // ¬ (HasStem M ∧ v = M.root)}) ∈ S := by
        constructor
        · rintro (⟨-, h⟩ | ⟨h', -⟩)
          · exact h
          · exact absurd ⟨hst, rfl⟩ h'
        · exact fun h => Or.inl ⟨rfl, h⟩
      refine ⟨e.1, T, fun f => ?_, ?_⟩
      · by_cases hf : HasStem M ∧ M.graph.source f = M.root
        · have hfe : f = stemArc M hst := (stemArc_spec M hst f).mp hf.2
          subst hfe
          have hne : stemArc M hst ≠ e.1 := fun h => e.2 ⟨hst, h ▸ hf.2⟩
          simp only [DirectedMultigraph.Crosses, hf.2, hroot]
          simp only [hmem _ hcne, c, hne, iff_false]
          tauto
        · have hc := hS ⟨f, hf⟩
          have ht : ¬ (HasStem M ∧ M.graph.target f = M.root) := fun h => target_ne_root hM f h.2
          simp only [DirectedMultigraph.Crosses] at hc ⊢
          rw [hmem _ hf, hmem _ ht]
          exact hc.trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      · ext x
        have hl : ¬ (HasStem M ∧ M.leaf x = M.root) := fun h => M.leaf_ne_root hM x h.2
        exact hmem _ hl
    · refine ⟨e.1, Subtype.val '' S, fun f => ?_, ?_⟩
      · have hf : ¬ (HasStem M ∧ M.graph.source f = M.root) := fun h => hst h.1
        have hc := hS ⟨f, hf⟩
        have himg : ∀ v, v ∈ Subtype.val '' S ↔
            (⟨v, fun h => hst h.1⟩ : {v // ¬ (HasStem M ∧ v = M.root)}) ∈ S := fun v => by
          constructor
          · rintro ⟨w, hw, rfl⟩
            exact hw
          · exact fun h => ⟨_, h, rfl⟩
        simp only [DirectedMultigraph.Crosses, himg]
        exact hc.trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      · ext x
        constructor
        · rintro ⟨w, hw, hwx⟩
          have : (removeStem M hM).leaf x = w := Subtype.ext hwx.symm
          change (removeStem M hM).leaf x ∈ S
          rw [this]
          exact hw
        · exact fun h => ⟨_, h, rfl⟩
  · rintro ⟨e, S, hS, rfl⟩
    have hke : ¬ (HasStem M ∧ M.graph.source e = M.root) := by
      rintro ⟨hst, hs⟩
      have hee : e = stemArc M hst := (stemArc_spec M hst e).mp hs
      have hroot : ∀ f, M.graph.source f = M.root ↔ f = e := fun f => by
        rw [hee]
        exact stemArc_spec M hst f
      rcases side_eq_of_stem hM hroot hS with h | h
      · rw [h] at h₁
        exact Set.not_nonempty_empty h₁
      · rw [h] at h₂
        simp at h₂
    refine ⟨⟨e, hke⟩, Subtype.val ⁻¹' S, fun f => ?_, rfl⟩
    have hc := hS f.1
    exact hc.trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end Stem

section Induced

variable (hN : IsBinaryNetwork N) {Y : Set X} (hY : Y.Nontrivial)

include hN in
/-- Retained edges are those ancestral to `Y`. -/
theorem mem_belowArcs_root_iff (e : E) : e ∈ N.belowArcs N.root Y ↔ e ∈ N.ancestralArcs Y :=
  ⟨fun h => h.2, fun h => ⟨hN.isPhylogenetic.root_reaches _, h⟩⟩

/-- **Step 1 of Definition 6**, on cut-edge splits. -/
theorem retained_hasCutSplit_iff {A : Set X} :
    (retained hN Y hY).HasCutSplit (Subtype.val ⁻¹' A) ↔ N.HasCutSplitOn Y A := by
  constructor
  · rintro ⟨e, S, hS, hA⟩
    refine ⟨e.1, e.2.2, Subtype.val '' S, fun f hf => ?_, fun x hx => ?_⟩
    · have hkf : f ∈ N.belowArcs N.root Y := (mem_belowArcs_root_iff hN f).mpr hf
      have hc := hS ⟨f, hkf⟩
      have hsv : N.graph.source f ∈ N.belowVertices N.root Y :=
        ⟨hN.isPhylogenetic.root_reaches _, N.source_mem_ancestralVertices hf⟩
      have htv : N.graph.target f ∈ N.belowVertices N.root Y := ⟨hN.isPhylogenetic.root_reaches _, hf⟩
      have himg : ∀ v (hv : v ∈ N.belowVertices N.root Y), v ∈ Subtype.val '' S ↔ ⟨v, hv⟩ ∈ S := fun v hv => by
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact hw
        · exact fun h => ⟨_, h, rfl⟩
      simp only [DirectedMultigraph.Crosses, himg _ hsv, himg _ htv]
      exact hc.trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    · have hm := Set.ext_iff.mp hA ⟨x, hx⟩
      simp only [Set.mem_preimage] at hm
      rw [← hm]
      constructor
      · rintro ⟨w, hw, hwx⟩
        have : (retained hN Y hY).leaf ⟨x, hx⟩ = w := Subtype.ext hwx.symm
        exact this ▸ hw
      · exact fun h => ⟨_, h, rfl⟩
  · rintro ⟨e, he, S, hS, hA⟩
    refine ⟨⟨e, (mem_belowArcs_root_iff hN e).mpr he⟩, Subtype.val ⁻¹' S, fun f => ?_, ?_⟩
    · have hc := hS f.1 f.2.2
      exact hc.trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    · ext x
      exact hA x.1 x.2

/-- **The cut-edge splits of the induced network of Definition 6** are the library's `HasCutSplitOn`, with a taxon of `Y` on each side. -/
theorem induced_hasCutSplit_iff {A : Set X} (h₁ : (Y ∩ A).Nonempty) (h₂ : (Y \ A).Nonempty) :
    (induced hN Y hY).HasCutSplit (Subtype.val ⁻¹' A) ↔ N.HasCutSplitOn Y A := by
  have hne : (Subtype.val ⁻¹' A : Set Y).Nonempty := by
    obtain ⟨x, hx, hxA⟩ := h₁
    exact ⟨⟨x, hx⟩, hxA⟩
  have hne' : (Subtype.val ⁻¹' A : Set Y)ᶜ.Nonempty := by
    obtain ⟨x, hx, hxA⟩ := h₂
    exact ⟨⟨x, hx⟩, hxA⟩
  exact (removeStem_hasCutSplit_iff _ hne hne').trans
    ((suppress_hasCutSplit_iff (retained_isPhylogenetic hN Y hY) _).trans (retained_hasCutSplit_iff hN hY))

end Induced

/-! ### The graph `T_rd(𝒩⁻)` -/

section Unroot

variable {M : RootedNetwork V E X}

/-- **Suppressing the root keeps the cut-edge splits.** The two edges at the root have the same split. -/
theorem unrootAt_cut_iff (hM : M.IsPhylogenetic) {e₀ : E} (he₀ : M.graph.source e₀ = M.root)
    (hout : M.graph.outdegree M.root = 2) (A : Set X) :
    (∃ e T, (∀ f, (unrootAt M hM e₀).graph.Crosses f T ↔ f = e) ∧ (unrootAt M hM e₀).leaf ⁻¹' T = A) ↔
      M.HasCutSplit A := by
  have hsrc₁ : ∀ f : {e // e ≠ e₀}, M.graph.source f.1 = M.root →
      ((unrootAt M hM e₀).graph.source f).1 = M.graph.target e₀ := fun f hf => by
    simp only [unrootAt, dite_eq_left hf]
  have hsrc₂ : ∀ f : {e // e ≠ e₀}, M.graph.source f.1 ≠ M.root →
      ((unrootAt M hM e₀).graph.source f).1 = M.graph.source f.1 := fun f hf => by
    simp only [unrootAt, dite_eq_right hf]
  have htgt : ∀ f : {e // e ≠ e₀}, ((unrootAt M hM e₀).graph.target f).1 = M.graph.target f.1 := fun _ => rfl
  constructor
  · rintro ⟨g, T', hT', rfl⟩
    -- the root goes with the child of `e₀`
    let T : Set V := {v | if h : v = M.root then
      (⟨M.graph.target e₀, target_ne_root hM e₀⟩ : {v // v ≠ M.root}) ∈ T' else (⟨v, h⟩ : {v // v ≠ M.root}) ∈ T'}
    have hmem : ∀ v (hv : v ≠ M.root), v ∈ T ↔ (⟨v, hv⟩ : {v // v ≠ M.root}) ∈ T' := fun v hv => by
      simp only [T, Set.mem_ofPred_eq, dite_eq_right hv]
    have hroot : M.root ∈ T ↔
        (⟨M.graph.target e₀, target_ne_root hM e₀⟩ : {v // v ≠ M.root}) ∈ T' := by
      change (if h : M.root = M.root then _ else _) ↔ _
      rw [dite_eq_left rfl]
    have hsrc : ∀ f : {e // e ≠ e₀}, M.graph.source f.1 ∈ T ↔ (unrootAt M hM e₀).graph.source f ∈ T' := by
      intro f
      by_cases hf : M.graph.source f.1 = M.root
      · rw [hf, hroot]
        have : (unrootAt M hM e₀).graph.source f =
            (⟨M.graph.target e₀, target_ne_root hM e₀⟩ : {v // v ≠ M.root}) := Subtype.ext (hsrc₁ f hf)
        rw [this]
      · rw [hmem _ hf]
        have : (unrootAt M hM e₀).graph.source f = (⟨M.graph.source f.1, hf⟩ : {v // v ≠ M.root}) :=
          Subtype.ext (hsrc₂ f hf)
        rw [this]
    have htg : ∀ f : {e // e ≠ e₀}, M.graph.target f.1 ∈ T ↔ (unrootAt M hM e₀).graph.target f ∈ T' := fun f =>
      hmem _ (target_ne_root hM f.1)
    refine ⟨g.1, T, fun f => ?_, ?_⟩
    · by_cases hf : f = e₀
      · subst hf
        have hne : f ≠ g.1 := fun h => g.2 h.symm
        have hs : M.graph.source f ∈ T ↔ M.graph.target f ∈ T := by
          rw [he₀, hroot, hmem _ (target_ne_root hM f)]
        simp only [DirectedMultigraph.Crosses, hne, iff_false]
        tauto
      · have hc := hT' ⟨f, hf⟩
        simp only [DirectedMultigraph.Crosses] at hc ⊢
        have h₁ := hsrc ⟨f, hf⟩
        have h₂ := htg ⟨f, hf⟩
        rw [show (M.graph.source f ∈ T) = _ from propext h₁, show (M.graph.target f ∈ T) = _ from propext h₂]
        exact hc.trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    · ext x
      exact hmem _ (M.leaf_ne_root hM x)
  · rintro ⟨e, T, hT, rfl⟩
    obtain ⟨e₁, hne₁, hroot⟩ := exists_other_root_arc hout he₀
    have hcr : ∀ f : {e // e ≠ e₀}, M.graph.source f.1 ≠ M.root →
        ((unrootAt M hM e₀).graph.Crosses f (Subtype.val ⁻¹' T) ↔ M.graph.Crosses f.1 T) := by
      intro f hf
      simp only [DirectedMultigraph.Crosses, Set.mem_preimage, hsrc₂ f hf, htgt]
    have hcr₁ : (unrootAt M hM e₀).graph.Crosses ⟨e₁, hne₁⟩ (Subtype.val ⁻¹' T) ↔
        (M.graph.target e₀ ∈ T ∧ M.graph.target e₁ ∉ T) ∨ (M.graph.target e₁ ∈ T ∧ M.graph.target e₀ ∉ T) := by
      have he₁ : M.graph.source e₁ = M.root := (hroot e₁).mpr (Or.inr rfl)
      simp only [DirectedMultigraph.Crosses, Set.mem_preimage, hsrc₁ ⟨e₁, hne₁⟩ he₁, htgt]
    have hc₀ := hT e₀
    have hc₁ := hT e₁
    have hs₁ : M.graph.source e₁ = M.root := (hroot e₁).mpr (Or.inr rfl)
    simp only [DirectedMultigraph.Crosses] at hc₀ hc₁
    rw [he₀] at hc₀
    rw [hs₁] at hc₁
    -- the edge of the network that crosses
    by_cases he : e = e₀ ∨ e = e₁
    · refine ⟨⟨e₁, hne₁⟩, Subtype.val ⁻¹' T, fun f => ?_, rfl⟩
      by_cases hf : M.graph.source f.1 = M.root
      · have hfe : f = ⟨e₁, hne₁⟩ := Subtype.ext (((hroot f.1).mp hf).resolve_left f.2)
        subst hfe
        simp only [iff_true]
        rw [hcr₁]
        have hne' : e₁ ≠ e₀ := hne₁
        rcases he with rfl | rfl
        · have h₁ := hc₀.mpr rfl
          have h₂ : ¬ _ := fun h => hne₁ (hc₁.mp h)
          tauto
        · have h₁ := hc₁.mpr rfl
          have h₂ : ¬ _ := fun h => hne₁.symm (hc₀.mp h)
          tauto
      · refine (hcr f hf).trans ((hT f.1).trans ?_)
        have hfne : f.1 ≠ e₁ := fun h => hf ((hroot f.1).mpr (Or.inr h))
        constructor
        · intro hfe
          rcases he with rfl | rfl
          · exact absurd hfe f.2
          · exact absurd hfe hfne
        · intro hfe
          exact absurd (congrArg Subtype.val hfe) hfne
    · push Not at he
      obtain ⟨he₀', he₁'⟩ := he
      refine ⟨⟨e, he₀'⟩, Subtype.val ⁻¹' T, fun f => ?_, rfl⟩
      by_cases hf : M.graph.source f.1 = M.root
      · have hfe : f = ⟨e₁, hne₁⟩ := Subtype.ext (((hroot f.1).mp hf).resolve_left f.2)
        subst hfe
        have hneq : (⟨e₁, hne₁⟩ : {e // e ≠ e₀}) ≠ ⟨e, he₀'⟩ := fun h => he₁' (congrArg Subtype.val h).symm
        simp only [hneq, iff_false]
        rw [hcr₁]
        have h₁ : ¬ _ := fun h => he₀' (hc₀.mp h).symm
        have h₂ : ¬ _ := fun h => he₁' (hc₁.mp h).symm
        tauto
      · exact (hcr f hf).trans ((hT f.1).trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)

end Unroot

/-- The taxa of `𝒩⊕` are renamed: its cut-edge splits are those of the library's `lsaNetwork`. -/
theorem lsaPlus_hasCutSplit_iff (hN : IsBinaryNetwork N) (hX : Nontrivial X) (A : Set X) :
    (lsaPlus hN hX).HasCutSplit A ↔
      (lsaNetwork hN.isPhylogenetic Set.univ Set.univ_nonempty).HasCutSplit (Subtype.val ⁻¹' A) := by
  constructor
  · rintro ⟨e, S, hS, rfl⟩
    exact ⟨e, S, hS, rfl⟩
  · rintro ⟨e, S, hS, hA⟩
    refine ⟨e, S, hS, ?_⟩
    ext x
    exact Set.ext_iff.mp hA ⟨x, Set.mem_univ x⟩

/-- **The bridge of the tree of blobs**: the splits of the graph `T_rd(𝒩⁻)` of Definition 11 are the library's split family `treeOfBlobs N`. The cut edges of `𝒩⁺` with a
taxon on each side are those of `𝒩⊕` (`hasCutSplitOn_iff_lsaNetwork_hasCutSplit`), of `𝒩⁻` (`unrootAt_cut_iff`), of `T(𝒩⁻)` (`labelled_cut_iff_quotient`), and of `T_rd(𝒩⁻)`
(`TreeSuppression.hasSide_iff`). -/
theorem splits_Trd [Fintype X] [DecidableEq X] (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    (Trd hN hX).splits = treeOfBlobs N := by
  have hP := hN.isPhylogenetic
  have : Finite V := hN.finite_vertices
  have : Finite E := hN.finite_arcs
  have hTree := treeOfBlobs_semidirected_isTree hN hX
  ext A
  rw [mem_treeOfBlobs_iff]
  simp only [LabelledGraph.splits, Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun h₁ => and_congr_right fun h₂ => ?_
  have h₁' : (Set.univ ∩ (A : Set X)).Nonempty := by
    obtain ⟨x, hx⟩ := h₁
    exact ⟨x, Set.mem_univ x, hx⟩
  have h₂' : (Set.univ \ (A : Set X)).Nonempty := by
    obtain ⟨x, hx⟩ := h₂
    exact ⟨x, Set.mem_univ x, by simpa using hx⟩
  have hside := TreeSuppression.hasSide_iff hTree (Trd hN hX).leaf (A : Set X)
  have hquot := (semidirected hN hX).graph.labelled_cut_iff_quotient (semidirected hN hX).leaf (A : Set X)
  have hun := unrootAt_cut_iff (lsaPlus_isPhylogenetic hN hX) (rootTreeArc_spec hN hX).1
    (lsaPlus_outdegree_root hN hX) (A : Set X)
  refine hside.trans (hquot.symm.trans (hun.trans ((lsaPlus_hasCutSplit_iff hN hX _).trans ?_)))
  exact (hasCutSplitOn_iff_lsaNetwork_hasCutSplit hP Set.nontrivial_univ h₁' h₂').symm.trans
    (hasCutSplit_iff_hasCutSplitOn_univ hP _).symm

/-- On four taxa, `T_rd(𝒩⁻)` has the quartet tree topology `ab|cd` exactly when it displays `ab|cd`. -/
theorem hasQuartetTopology_iff_displays [Fintype X] [DecidableEq X] (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4)
    {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d ↔
      Displays (Trd hN (nontrivial_of_card_four hcard)).splits (quartetTree a b c d h) := by
  sorry

/-- On four taxa, `T_rd(𝒩⁻)` has the unresolved quartet topology exactly when it displays no resolved quartet. -/
theorem hasStarTopology_iff_displaysUnresolved [Fintype X] [DecidableEq X] (hN : IsBinaryNetwork N)
    (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    (Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d ↔
      (Trd hN (nontrivial_of_card_four hcard)).DisplaysUnresolved {a, b, c, d} := by
  sorry

/-! ### Quartets on induced networks -/

section InducedQuartets

/-- The elements of `Q` in `A`, as taxa of `Y` or of `X`. -/
theorem card_inter_subtype {Y : Set X} [Fintype Y] (Q : Finset X) (A : Finset Y) :
    (A ∩ Q.subtype (· ∈ Y)).card = (Q.filter (· ∈ Subtype.val '' (A : Set Y))).card := by
  rw [← Finset.card_map (Function.Embedding.subtype (· ∈ Y))]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_inter, Finset.mem_subtype, Function.Embedding.subtype_apply,
    Finset.mem_filter, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨y, ⟨hA, hq⟩, rfl⟩
    exact ⟨hq, y, hA, rfl⟩
  · rintro ⟨hq, y, hA, rfl⟩
    exact ⟨y, ⟨hA, hq⟩, rfl⟩

/-- **"Under this operation, blobs pass to blobs, and cut edges to cut edges"** (`a:claim:suppress-blobs`, before Corollary 2): a B-quartet on the induced network is a set that
determines a blob of the subnetwork of the edges ancestral to `Y`. This proof goes through cut-edge splits. -/
theorem isBlobQuartetOnInduced_iff (hN : IsBinaryNetwork N) (Y : Set X) (hY : Y.Nontrivial) {Q : Finset X}
    (hQ : (Q : Set X) ⊆ Y) (h4 : Q.card = 4) :
    IsBlobQuartetOnInduced hN Y hY Q ↔ ∃ v ∈ N.ancestralVertices Y, Determines N.graph (N.ancestralArcs Y) v N.leaf Q := by
  have hP := hN.isPhylogenetic
  have : Finite X := hP.finite_taxa
  let _ : Fintype Y := Fintype.ofFinite Y
  have hY' : ((Y.toFinset : Finset X) : Set X) = Y := Set.coe_toFinset Y
  have hQY' : Q ⊆ Y.toFinset := fun x hx => Set.mem_toFinset.mpr (hQ hx)
  have hc : (Q.subtype (· ∈ Y)).card = 4 := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => hQ hx), h4]
  have hM := induced_isPhylogenetic hN Y hY
  rw [IsBlobQuartetOnInduced, isBlobQuartet_iff_isBQuartet hM hc, IsBQuartet, TreeMetric.forall_not_displays_iff hc]
  have key := not_resolves_iff_exists_determines hP hQY' h4
  rw [hY'] at key
  rw [← key]
  constructor
  · rintro hno ⟨e, he, h2⟩
    have hbelow : (Q.filter (N.IsBelow e)).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hbelow
    obtain ⟨hxq, hxb⟩ := Finset.mem_filter.mp hx
    have hc2 : (Q.filter fun x => ¬ N.IsBelow e x).card = 2 := by
      have := Finset.card_filter_add_card_filter_not (s := Q) (N.IsBelow e)
      omega
    obtain ⟨y, hy⟩ : (Q.filter fun x => ¬ N.IsBelow e x).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨hyq, hyb⟩ := Finset.mem_filter.mp hy
    have hcut := hasCutSplitOn_of_isCutOn (A := {x | N.IsBelow e x}) hP he (fun _ _ => Iff.rfl) (hQY' hxq) hxb
    rw [hY'] at hcut
    have hind := (induced_hasCutSplit_iff hN hY (A := {x | N.IsBelow e x}) ⟨x, hQ hxq, hxb⟩ ⟨y, hQ hyq, hyb⟩).mpr hcut
    let A : Finset Y := Finset.univ.filter fun z => N.IsBelow e z.1
    have hA : (A : Set Y) = Subtype.val ⁻¹' {x | N.IsBelow e x} := by
      ext z
      simp [A]
    refine hno A ((mem_treeOfBlobs_iff A).mpr ⟨⟨⟨x, hQ hxq⟩, by simp [A, hxb]⟩, ⟨⟨y, hQ hyq⟩, by simp [A, hyb]⟩, ?_⟩) ?_
    · rw [hA]
      exact hind
    · rw [card_inter_subtype Q A, ← h2]
      congr 1
      refine Finset.filter_congr fun z hz => ?_
      simp only [Set.mem_image, Finset.mem_coe, A, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · exact fun hb => ⟨⟨z, hQ hz⟩, hb, rfl⟩
  · rintro hR A hA h2
    obtain ⟨h₁, h₂, hcut⟩ := (mem_treeOfBlobs_iff A).mp hA
    obtain ⟨x, hx⟩ := h₁
    obtain ⟨y, hy⟩ := h₂
    have hpre : Subtype.val ⁻¹' (Subtype.val '' (A : Set Y)) = (A : Set Y) :=
      Set.preimage_image_eq _ Subtype.val_injective
    have hN₁ : (Y ∩ Subtype.val '' (A : Set Y)).Nonempty := ⟨x.1, x.2, x, hx, rfl⟩
    have hN₂ : (Y \ Subtype.val '' (A : Set Y)).Nonempty := by
      refine ⟨y.1, y.2, ?_⟩
      rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      exact (Finset.mem_compl.mp hy) (this ▸ hz)
    have hon := (induced_hasCutSplit_iff hN hY hN₁ hN₂).mp (by rw [hpre]; exact hcut)
    have hon' : ∀ B : Set X, N.HasCutSplitOn Y B → N.HasCutSplitOn ((Y.toFinset : Finset X) : Set X) B := fun B h => by
      rw [hY']
      exact h
    refine hR (resolves_of_hasCutSplitOn hP (hon' _ hon) hQY' h4 ?_)
    rw [← card_inter_subtype Q A]
    exact h2

/-- The B-quartet of Definition 12 is unresolved on the whole network. -/
theorem isBlobQuartet_iff_not_resolves [Fintype X] [DecidableEq X] (hN : IsBinaryNetwork N) {Q : Finset X} (hQ : Q.card = 4) :
    IsBlobQuartet N Q ↔ ¬ Resolves N Finset.univ Q :=
  (isBlobQuartet_iff_isBQuartet hN.isPhylogenetic hQ).trans (isBQuartet_iff_not_resolves hN.isPhylogenetic hQ)

/-- A B-quartet on its induced network has no cut-edge split there. -/
theorem not_isTreelike_of_isBlobQuartetOnInduced [Fintype X] [DecidableEq X] (hN : IsBinaryNetwork N) {t : Finset X} (ht : t.card = 4)
    (h : IsBlobQuartetOnInduced hN (t : Set X) (nontrivial_coe_of_card_four ht) t) : ¬ IsTreelike N t := by
  have hP := hN.isPhylogenetic
  obtain ⟨v, hv, hd⟩ := (isBlobQuartetOnInduced_iff hN (t : Set X) _ subset_rfl ht).mp h
  have hR := (not_resolves_iff_exists_determines hP (Finset.Subset.refl t) ht).mpr ⟨v, hv, hd⟩
  rintro ⟨s, hs, B, hB, hcB⟩
  have hst : s.taxa = t := (Finset.mem_filter.mp hs).2
  rw [hst] at hcB
  have hBs : B ⊆ t := hst ▸ QuartetTree.subset_taxa _ hB
  refine hR (resolves_of_hasCutSplitOn hP hcB (Finset.Subset.refl _) ht ?_)
  convert s.2.2.1 B hB using 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_coe]
  exact ⟨fun h => h.2, fun h => ⟨hBs h, h⟩⟩

/-- A 4-taxon set is treelike exactly when a cut edge resolves it on its own induced subgraph. -/
theorem isTreelike_iff_resolves [Fintype X] [DecidableEq X] (hN : N.IsPhylogenetic) {t : Finset X} (ht : t.card = 4) :
    IsTreelike N t ↔ Resolves N t t := by
  constructor
  · rintro ⟨s, hs, B, hB, hcB⟩
    have hst : s.taxa = t := (Finset.mem_filter.mp hs).2
    rw [hst] at hcB
    have hBs : B ⊆ t := hst ▸ QuartetTree.subset_taxa _ hB
    refine resolves_of_hasCutSplitOn hN hcB (Finset.Subset.refl _) ht ?_
    convert s.2.2.1 B hB using 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_coe]
    exact ⟨fun h => h.2, fun h => ⟨hBs h, h⟩⟩
  · rintro ⟨e, he, h2⟩
    have hc2 : (t.filter fun x => ¬ N.IsBelow e x).card = 2 := by
      have := Finset.card_filter_add_card_filter_not (s := t) (N.IsBelow e)
      omega
    obtain ⟨a, b, hab, hfa⟩ := Finset.card_eq_two.mp h2
    obtain ⟨c, d, hcd, hfc⟩ := Finset.card_eq_two.mp hc2
    have hmem₁ : ∀ x, (x ∈ t ∧ N.IsBelow e x) ↔ x = a ∨ x = b := fun x => by
      have := Finset.ext_iff.mp hfa x
      simpa only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] using this
    have hmem₂ : ∀ x, (x ∈ t ∧ ¬ N.IsBelow e x) ↔ x = c ∨ x = d := fun x => by
      have := Finset.ext_iff.mp hfc x
      simpa only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] using this
    obtain ⟨hat, Ba⟩ := (hmem₁ a).mpr (Or.inl rfl)
    obtain ⟨hbt, Bb⟩ := (hmem₁ b).mpr (Or.inr rfl)
    obtain ⟨hct, Nc⟩ := (hmem₂ c).mpr (Or.inl rfl)
    obtain ⟨hdt, Nd⟩ := (hmem₂ d).mpr (Or.inr rfl)
    have hte : t = {a, b, c, d} := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hx
        by_cases hbx : N.IsBelow e x
        · rcases (hmem₁ x).mp ⟨hx, hbx⟩ with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rcases (hmem₂ x).mp ⟨hx, hbx⟩ with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
      · rintro (rfl | rfl | rfl | rfl) <;> assumption
    have h4 : ({a, b, c, d} : Finset X).card = 4 := hte ▸ ht
    refine ⟨quartetTree a b c d h4, mem_treesOn.2 ((quartetTree_taxa _ _ _ _ _).trans hte.symm), {a, b}, by simp, ?_⟩
    rw [quartetTree_taxa, ← hte]
    refine hasCutSplitOn_of_isCutOn hN he (fun x hx => ?_) hat Ba
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨fun hb => (hmem₁ x).mp ⟨hx, hb⟩, fun h => ((hmem₁ x).mpr h).2⟩

/-- **The unresolved quartet on the induced network, by Definition 12, is `¬ IsTreelike`.** -/
theorem isBlobQuartetOnInduced_self_iff [Fintype X] [DecidableEq X] (hN : IsBinaryNetwork N) {t : Finset X} (ht : t.card = 4) :
    IsBlobQuartetOnInduced hN (t : Set X) (nontrivial_coe_of_card_four ht) t ↔ ¬ IsTreelike N t := by
  rw [isBlobQuartetOnInduced_iff hN (t : Set X) _ subset_rfl ht, isTreelike_iff_resolves hN.isPhylogenetic ht,
    not_resolves_iff_exists_determines hN.isPhylogenetic (Finset.Subset.refl t) ht]

/-- **The resolved topology of `T_rd(𝒩⁻_Q)` is the library's `InducedCutSplit`.** -/
theorem inducedHasQuartetTopology_iff [Fintype X] [DecidableEq X] (hN : IsBinaryNetwork N) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) :
    InducedHasQuartetTopology hN a b c d h ↔ InducedCutSplit N (quartetTree a b c d h) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hP := hN.isPhylogenetic
  let Q : Finset X := {a, b, c, d}
  have hQnt := nontrivial_coe_of_card_four h
  have hM := induced_isBinaryNetwork hN (Q : Set X) hQnt
  have hcard : Fintype.card ↥(Q : Set X) = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact h
  have hmem : ∀ x ∈ Q, x ∈ (Q : Set X) := fun x hx => hx
  let a' : ↥(Q : Set X) := ⟨a, by simp [Q]⟩
  let b' : ↥(Q : Set X) := ⟨b, by simp [Q]⟩
  let c' : ↥(Q : Set X) := ⟨c, by simp [Q]⟩
  let d' : ↥(Q : Set X) := ⟨d, by simp [Q]⟩
  have sne : ∀ {x y : ↥(Q : Set X)}, x.1 ≠ y.1 → x ≠ y := fun hxy he => hxy (congrArg Subtype.val he)
  have h' : ({a', b', c', d'} : Finset ↥(Q : Set X)).card = 4 :=
    TreeMetric.card_four_of_ne (sne hab) (sne hac) (sne had) (sne hbc) (sne hbd) (sne hcd)
  have hS : IsSplitFamily (treeOfBlobs (induced hN (Q : Set X) hQnt)) :=
    (isUnrootedTree_treeOfBlobs hM.isPhylogenetic).isSplitFamily (by omega)
  have hstep : InducedHasQuartetTopology hN a b c d h ↔
      ∃ A ∈ treeOfBlobs (induced hN (Q : Set X) hQnt), a' ∈ A ∧ b' ∈ A ∧ c' ∉ A ∧ d' ∉ A := by
    refine (hasQuartetTopology_iff_displays hM hcard h').trans ?_
    rw [splits_Trd hM]
    exact TreeMetric.displays_quartetTree_iff hS h'
  refine hstep.trans ⟨?_, ?_⟩
  · rintro ⟨A, hA, ha, hb, hc, hd⟩
    obtain ⟨-, -, hcut⟩ := (mem_treeOfBlobs_iff A).mp hA
    have hpre : Subtype.val ⁻¹' (Subtype.val '' (A : Set ↥(Q : Set X))) = (A : Set ↥(Q : Set X)) :=
      Set.preimage_image_eq _ Subtype.val_injective
    have hN₁ : ((Q : Set X) ∩ Subtype.val '' (A : Set ↥(Q : Set X))).Nonempty := ⟨a, a'.2, a', ha, rfl⟩
    have hN₂ : ((Q : Set X) \ Subtype.val '' (A : Set ↥(Q : Set X))).Nonempty := by
      refine ⟨c, c'.2, ?_⟩
      rintro ⟨z, hz, hzc⟩
      have : z = c' := Subtype.ext hzc
      exact hc (this ▸ hz)
    have hon := (induced_hasCutSplit_iff hN hQnt hN₁ hN₂).mp (by rw [hpre]; exact hcut)
    refine ⟨{a, b}, by simp, ?_⟩
    rw [quartetTree_taxa]
    refine (hasCutSplitOn_congr ?_).mp hon
    ext x
    simp only [Set.mem_inter_iff, Set.mem_image, Finset.mem_coe, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, y, hy, rfl⟩
      refine ⟨hx, ?_⟩
      have hx' : y.1 = a ∨ y.1 = b ∨ y.1 = c ∨ y.1 = d := by simpa [Q] using hx
      rcases hx' with hx' | hx' | hx' | hx'
      · exact Or.inl hx'
      · exact Or.inr hx'
      · have hyc : y = c' := Subtype.ext hx'
        exact absurd (hyc ▸ hy) hc
      · have hyd : y = d' := Subtype.ext hx'
        exact absurd (hyd ▸ hy) hd
    · rintro ⟨hx, rfl | rfl⟩
      · exact ⟨hx, a', ha, rfl⟩
      · exact ⟨hx, b', hb, rfl⟩
  · rintro ⟨B, hB, hcB⟩
    rw [quartetTree_taxa] at hcB
    obtain ⟨A₀, hon, hA₀⟩ : ∃ A₀ : Set X, N.HasCutSplitOn (Q : Set X) A₀ ∧ a ∈ A₀ ∧ b ∈ A₀ ∧ c ∉ A₀ ∧ d ∉ A₀ := by
      simp only [quartetTree_val, Finset.mem_insert, Finset.mem_singleton] at hB
      rcases hB with rfl | rfl
      · exact ⟨_, hcB, by simp, by simp, by simp [hac.symm, hbc.symm], by simp [had.symm, hbd.symm]⟩
      · exact ⟨_, (hasCutSplitOn_compl _ _).mpr hcB, by simp [hac, had], by simp [hbc, hbd], by simp, by simp⟩
    obtain ⟨hA₁, hA₂, hA₃, hA₄⟩ := hA₀
    have hN₁ : ((Q : Set X) ∩ A₀).Nonempty := ⟨a, a'.2, hA₁⟩
    have hN₂ : ((Q : Set X) \ A₀).Nonempty := ⟨c, c'.2, hA₃⟩
    have hind := (induced_hasCutSplit_iff hN hQnt hN₁ hN₂).mpr hon
    let A : Finset ↥(Q : Set X) := Finset.univ.filter fun z => z.1 ∈ A₀
    have hA : (A : Set ↥(Q : Set X)) = Subtype.val ⁻¹' A₀ := by
      ext z
      simp [A]
    refine ⟨A, (mem_treeOfBlobs_iff A).mpr ⟨⟨a', by simp [A, a', hA₁]⟩, ⟨c', by simp [A, c', hA₃]⟩, ?_⟩,
      by simp [A, a', hA₁], by simp [A, b', hA₂], by simp [A, c', hA₃], by simp [A, d', hA₄]⟩
    rw [hA]
    exact hind

end InducedQuartets

end AllmanEtAl2023.Bridges
