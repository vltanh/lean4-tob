module

public import AllmanEtAl2023.Bridges
public import AllmanEtAl2023.SuppressStem

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the unnumbered claims that Theorem 1 and Corollary 1 use

Each has a label of our own, `a:claim:…`, in the routes of the paper.

* `a:claim:cf-induced`: "In passing to an induced network, B-quartets may become T-quartets, although `CF`s remain unchanged": `nmscCF_induced`.
* `a:claim:generic-induced`: "the generic conditions ... give rise to a generic condition on numerical parameter values on the `n`-taxon network":
  `isMetric_inducedParams`, `isGenericNull_inducedParams`. And `induced_isBinaryNetwork` (proved, in `src/AllmanEtAl2023/InducedNetwork.lean`).
* `a:claim:rooted-forms`: "the reduced rooted tree of blobs thus has topology `(((a, b), c), d)`, `((a, b), (c, d))`, or `((a, b), c, d)`": `rootedForms`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### `CF`s of an induced network -/

section CF

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]

/-- **"In passing to an induced network, ... `CF`s remain unchanged"** (`a:claim:cf-induced`; also in Section 4: "The `CF`s computed from the induced 4-taxon networks
are the same as gene tree probabilities from the large network marginalized to 4-taxon sets, by the structure of the NMSC model"). The three steps of Definition 6:
`nmscCF_retained`, `NMSC.nmscCF_suppress`, `nmscCF_removeStem`. The paper's "by the structure of the NMSC model" is sampling consistency and these three; no exchangeability of four
lineages is used, and `Y` is any set of taxa. -/
theorem nmscCF_induced (hN : IsBinaryNetwork N) {θ : MetricData E} (hθ : N.IsMetric θ) (Y : Set X) (hY : Y.Nontrivial)
    [Fintype Y] [DecidableEq Y] [Fintype (InducedV hN Y hY)] [Fintype (InducedE hN Y hY)] (s : QuartetTree Y) :
    nmscCF (induced hN Y hY) (inducedParams hN Y hY θ) 0 s = nmscCF N θ 0 (s.map Subtype.val_injective) := by
  have hP := hN.isPhylogenetic
  obtain ⟨Q, rfl⟩ := (Set.toFinite Y).exists_finset_coe
  have : Nontrivial (Q : Set X) := hY.coe_sort
  let _ : Fintype (N.belowVertices N.root (Q : Set X)) := Fintype.ofFinite _
  let _ : Fintype (N.belowArcs N.root (Q : Set X)) := Fintype.ofFinite _
  let _ : Fintype {v // ¬ (retained hN (Q : Set X) hY).IsChainVertex v} := Fintype.ofFinite _
  let _ : Fintype {e // ¬ (retained hN (Q : Set X) hY).IsChainVertex ((retained hN (Q : Set X) hY).graph.source e)} := Fintype.ofFinite _
  have hR := retained_isPhylogenetic hN (Q : Set X) hY
  have hθR : (retained hN (Q : Set X) hY).IsMetric (belowMetric N.root (Q : Set X) θ) := isMetric_belowMetric hP (N.root_isStableAncestor _) hθ
  exact (nmscCF_suppressStem hR hθR.isNormalized le_rfl s).trans (nmscCF_retained hP hθ.isNormalized le_rfl hR s)

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The map of parameters sends valid parameters to valid parameters (`a:claim:generic-induced`). -/
theorem isMetric_inducedParams (hN : IsBinaryNetwork N) {θ : MetricData E} (hθ : N.IsMetric θ) (Y : Set X)
    (hY : Y.Nontrivial) [Fintype (InducedE hN Y hY)] :
    (induced hN Y hY).IsMetric (inducedParams hN Y hY θ) := by
  have hP := hN.isPhylogenetic
  have : Nontrivial Y := hY.coe_sort
  let _ : Fintype (N.belowArcs N.root Y) := Fintype.ofFinite _
  let _ : Fintype {e // ¬ (retained hN Y hY).IsChainVertex ((retained hN Y hY).graph.source e)} := Fintype.ofFinite _
  have hR := retained_isPhylogenetic hN Y hY
  have hθR : (retained hN Y hY).IsMetric (belowMetric N.root Y θ) := isMetric_belowMetric hP (N.root_isStableAncestor _) hθ
  exact isMetric_suppressStem hR hθR

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A phylogenetic network on a nonempty set of taxa has an arc. -/
theorem nonempty_arcs_of_isPhylogenetic {V' E' X' : Type*} {M : RootedNetwork V' E' X'} (hM : M.IsPhylogenetic) [Nonempty X'] : Nonempty E' := by
  obtain ⟨x⟩ := ‹Nonempty X'›
  obtain ⟨e, -⟩ := (M.graph.indegree_eq_one_iff _).mp (hM.leaf_indegree x)
  exact ⟨e⟩

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- **"They give rise to a generic condition on numerical parameter values on the `n`-taxon network"** (`a:claim:generic-induced`, in the proof of Corollary 1):
preimages of null sets under the map of parameters are null. -/
theorem isGenericNull_inducedParams (hN : IsBinaryNetwork N) (Y : Set X) (hY : Y.Nontrivial)
    [Fintype (InducedE hN Y hY)] {A' : Set (MetricData (InducedE hN Y hY))}
    (hA' : (induced hN Y hY).IsGenericNull A') :
    N.IsGenericNull {θ | N.IsMetric θ ∧ inducedParams hN Y hY θ ∈ A'} := by
  have hP := hN.isPhylogenetic
  have : Nontrivial Y := hY.coe_sort
  let _ : Fintype (N.belowArcs N.root Y) := Fintype.ofFinite _
  let _ : Fintype {e // ¬ (retained hN Y hY).IsChainVertex ((retained hN Y hY).graph.source e)} := Fintype.ofFinite _
  have hR := retained_isPhylogenetic hN Y hY
  have hS := retainedSuppressed_isPhylogenetic hN Y hY
  have hst := N.root_isStableAncestor Y
  obtain ⟨e₀⟩ := nonempty_arcs_of_isPhylogenetic (induced_isPhylogenetic hN Y hY)
  obtain ⟨e₁⟩ := nonempty_arcs_of_isPhylogenetic hR
  have h₃ := isGenericNull_stemMetric hS e₀ hA'
  have h₂ := isGenericNull_suppressMetric hR h₃
  have h₁ := isGenericNull_belowMetric hP hst e₁ h₂
  intro d hd
  refine MeasureTheory.measure_mono_null ?_ (h₁ d hd)
  rintro x ⟨θ, ⟨hθ, hA⟩, rest⟩
  have hθR : (retained hN Y hY).IsMetric (belowMetric N.root Y θ) := isMetric_belowMetric hP hst hθ
  exact ⟨θ, ⟨hθ, hθR, isMetric_suppressMetric hR hθR, hA⟩, rest⟩

end CF

/-! ### The rooted forms -/

section RootedForms

variable [DecidableEq X]

/-- The non-singleton clusters of a rooted tree: the taxa below an edge. -/
def rootedClusters {V' E' : Type*} (R : RootedNetwork V' E' X) : Set (Set X) :=
  {A | 2 ≤ A.ncard ∧ ∃ e, A = {x | R.IsBelow e x}}

/-- The same four taxa. -/
theorem insert_acbd (a b c d : X) : ({a, b, c, d} : Finset X) = {a, c, b, d} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The same four taxa. -/
theorem insert_adbc (a b c d : X) : ({a, b, c, d} : Finset X) = {a, d, b, c} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

omit [DecidableEq X] in
/-- A side `S` of an edge with its target in `S` is the taxa below the edge. -/
theorem mem_side_iff_isBelow {V' E' : Type*} {R : RootedNetwork V' E' X} (hR : R.IsPhylogenetic) {e : E'} {S : Set V'} (hS : ∀ f, R.graph.Crosses f S ↔ f = e)
    (ht : R.graph.target e ∈ S) (hs : R.graph.source e ∉ S) (x : X) : R.leaf x ∈ S ↔ R.IsBelow e x := by
  obtain ⟨y, hy⟩ := exists_reaches_leaf hR (R.graph.target e)
  obtain ⟨-, hd, hn⟩ := separates_of_crossing (Y := Set.univ) hR (e := e) ⟨y, Set.mem_univ y, hy⟩ (fun f _ hfe hc => hfe ((hS f).mp hc)) ht hs
  refine ⟨fun hx => (hd x (Set.mem_univ x) hx).isBelow hR, fun hb => ?_⟩
  by_contra hx
  exact hn x (Set.mem_univ x) hx hb

omit [DecidableEq X] in
/-- In a rooted network that is a tree, an edge has a side, with exactly the taxa below it. -/
theorem exists_side_of_isTree {V' E' : Type*} {R : RootedNetwork V' E' X} (hR : R.IsPhylogenetic) (hT : R.graph.IsTree) (e : E') :
    ∃ S : Set V', (∀ f, R.graph.Crosses f S ↔ f = e) ∧ R.graph.target e ∈ S ∧ R.graph.source e ∉ S ∧ ∀ x, R.leaf x ∈ S ↔ R.IsBelow e x := by
  obtain ⟨S, hS, ht, hs⟩ := DirectedMultigraph.exists_oriented_cut ((R.graph.isBridge_iff_not_walks_delete e).mpr (hT.2 e))
  exact ⟨S, hS, ht, hs, mem_side_iff_isBelow hR hS ht hs⟩

omit [DecidableEq X] in
/-- **The splits of the tree of blobs are the cuts of the LSA network.** -/
theorem mem_splits_Trd_iff (hN : IsBinaryNetwork N) (hX : Nontrivial X) [Fintype X] [DecidableEq X] (A : Finset X) :
    A ∈ (Trd hN hX).splits ↔ A.Nonempty ∧ Aᶜ.Nonempty ∧ (lsaPlus hN hX).HasCutSplit (A : Set X) := by
  have hP := hN.isPhylogenetic
  rw [Bridges.splits_Trd, mem_treeOfBlobs_iff]
  refine and_congr_right fun h₁ => and_congr_right fun h₂ => ?_
  have h₁' : (Set.univ ∩ (A : Set X)).Nonempty := by
    obtain ⟨x, hx⟩ := h₁
    exact ⟨x, Set.mem_univ x, hx⟩
  have h₂' : (Set.univ \ (A : Set X)).Nonempty := by
    obtain ⟨x, hx⟩ := h₂
    exact ⟨x, Set.mem_univ x, by simpa using hx⟩
  rw [hasCutSplit_iff_hasCutSplitOn_univ hP, hasCutSplitOn_iff_lsaNetwork_hasCutSplit hP Set.nontrivial_univ h₁' h₂', Bridges.lsaPlus_hasCutSplit_iff]

/-- **"Permuting taxon names if necessary, we may assume that the reduced rooted tree of blobs thus has topology `(((a, b), c), d)`, `((a, b), (c, d))`, or `((a, b), c, d)`"**
(`a:claim:rooted-forms`, in the proof of Theorem 1). Here are the seven rooted forms before the permutation: the root on a pendant edge, on the internal edge, or at one of the two nodes.

The clusters of the rooted tree are sides of its cut edges. So they are splits of `T_rd(𝒩⁻)`, proper, since the root of `𝒩⊕` is its own LSA: a cluster of two taxa is a cherry `{a, b}` or `{c, d}`, and a cluster of
three is all but one. The cut edge of `ab|cd` has one cherry below it. And clusters of a tree are not crossing. -/
theorem rootedForms [Fintype X] (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X}
    (hT : (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) :
    rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{a, b}, {a, b, c}} ∨
      rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{a, b}, {a, b, d}} ∨
      rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{c, d}, {c, d, a}} ∨
      rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{c, d}, {c, d, b}} ∨
      rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{a, b}, {c, d}} ∨
      rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{a, b}} ∨
      rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{c, d}} := by
  have hX := nontrivial_of_card_four hcard
  have hM := lsaPlus_isPhylogenetic hN hX
  have hR : (reducedRootedTree hN hX).IsPhylogenetic := blobTree_isPhylogenetic hM
  have hRT : (reducedRootedTree hN hX).graph.IsTree := blobTree_isTree hM
  -- the names are all the taxa
  have hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    obtain ⟨u, w, hn, -, -⟩ := hT
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true] at hn
    obtain ⟨⟨h₁, h₂, h₃, -⟩, ⟨h₄, h₅, -⟩, ⟨h₆, -⟩, -⟩ := hn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro rfl
      exact h₁ rfl
    · rintro rfl
      exact h₂ rfl
    · rintro rfl
      exact h₃ rfl
    · rintro rfl
      exact h₄ rfl
    · rintro rfl
      exact h₅ rfl
    · rintro rfl
      exact h₆ rfl
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := hne
  have h4 : ({a, b, c, d} : Finset X).card = 4 := TreeMetric.card_four_of_ne hab hac had hbc hbd hcd
  have hall := Bridges.forall_eq_of_card_four hcard h4
  have huniv : ({a, b, c, d} : Finset X) = Finset.univ := Finset.eq_univ_of_card _ (h4.trans hcard.symm)
  -- what `T_rd(𝒩⁻)` displays
  have hU : IsUnrootedTree (Trd hN hX).splits := by
    rw [Bridges.splits_Trd]
    exact isUnrootedTree_treeOfBlobs hN.isPhylogenetic
  have hd₀ := (Bridges.hasQuartetTopology_iff_displays hN hcard h4).mp hT
  have hno₁ : ¬ Displays (Trd hN hX).splits (quartetTree a c b d (card_acbd h4)) := fun hd =>
    quartetTree_ne_acbd h4 (hU.displays_unique hd₀ hd (by simp only [quartetTree_taxa]; exact insert_acbd a b c d))
  have hno₂ : ¬ Displays (Trd hN hX).splits (quartetTree a d b c (card_adbc h4)) := fun hd =>
    quartetTree_ne_adbc h4 (hU.displays_unique hd₀ hd (by simp only [quartetTree_taxa]; exact insert_adbc a b c d))
  have hdisp : ∀ {p q r t : X} (hp : ({p, q, r, t} : Finset X).card = 4) {A : Finset X}, A ∈ (Trd hN hX).splits →
      A ∈ (quartetTree p q r t hp).val → Displays (Trd hN hX).splits (quartetTree p q r t hp) := fun {p q r t} hp {A} hA hm =>
    ⟨A, hA, by
      have : (quartetTree p q r t hp).taxa = Finset.univ := Finset.eq_univ_of_card _ ((quartetTree p q r t hp).card_taxa.trans hcard.symm)
      rw [this, Finset.inter_univ]
      exact hm⟩
  -- a cluster is one of the six
  have hsix : ∀ A ∈ rootedClusters (reducedRootedTree hN hX), A = {a, b} ∨ A = {c, d} ∨ A = {a, b, c} ∨ A = {a, b, d} ∨ A = {c, d, a} ∨ A = {c, d, b} := by
    rintro A ⟨h2, e, rfl⟩
    set A' : Finset X := Finset.univ.filter fun x => (reducedRootedTree hN hX).IsBelow e x with hA'
    have hcoe : (A' : Set X) = {x | (reducedRootedTree hN hX).IsBelow e x} := by
      ext x
      simp [hA']
    rw [← hcoe, Set.ncard_coe_finset] at h2
    obtain ⟨S, hS, -, -, hSx⟩ := exists_side_of_isTree hR hRT e
    have hcutR : (reducedRootedTree hN hX).HasCutSplit (A' : Set X) := ⟨e, S, hS, by
      rw [hcoe]
      ext x
      exact hSx x⟩
    have hcutM : (lsaPlus hN hX).HasCutSplit (A' : Set X) := (blobTree_hasCutSplit_iff hM _).mp hcutR
    have hcne : A'ᶜ.Nonempty := by
      by_contra hemp
      have hu : (A' : Set X) = Set.univ := by
        rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at hemp
        rw [hemp, Finset.coe_univ]
      rw [hu] at hcutM
      exact Bridges.lsaPlus_not_hasCutSplit_empty hN hX ((hasCutSplit_compl (N := lsaPlus hN hX) ∅).mp (by rw [Set.compl_empty]; exact hcutM))
    have hmem : A' ∈ (Trd hN hX).splits := (mem_splits_Trd_iff hN hX A').mpr ⟨Finset.card_pos.mp (by omega), hcne, hcutM⟩
    have hle : A'.card ≤ 3 := by
      have hlt := Finset.card_pos.mpr hcne
      rw [Finset.card_compl, hcard] at hlt
      omega
    rw [← hcoe]
    rcases (by omega : A'.card = 2 ∨ A'.card = 3) with hc2 | hc3
    · obtain ⟨p, q, hpq, hApq⟩ := Finset.card_eq_two.mp hc2
      rw [hApq] at hmem ⊢
      rcases hall p with rfl | rfl | rfl | rfl <;> rcases hall q with rfl | rfl | rfl | rfl
      · exact absurd rfl hpq
      · left; simp
      · exact absurd (hdisp (card_acbd h4) hmem (by simp)) hno₁
      · exact absurd (hdisp (card_adbc h4) hmem (by simp)) hno₂
      · left; simp [Set.pair_comm]
      · exact absurd rfl hpq
      · exact absurd (hdisp (card_adbc h4) hmem (by simp [Finset.pair_comm])) hno₂
      · exact absurd (hdisp (card_acbd h4) hmem (by simp [Finset.pair_comm])) hno₁
      · exact absurd (hdisp (card_acbd h4) hmem (by simp [Finset.pair_comm])) hno₁
      · exact absurd (hdisp (card_adbc h4) hmem (by simp [Finset.pair_comm])) hno₂
      · exact absurd rfl hpq
      · right; left; simp
      · exact absurd (hdisp (card_adbc h4) hmem (by simp [Finset.pair_comm])) hno₂
      · exact absurd (hdisp (card_acbd h4) hmem (by simp [Finset.pair_comm])) hno₁
      · right; left; simp [Set.pair_comm]
      · exact absurd rfl hpq
    · obtain ⟨x, hx⟩ := hcne
      have hxA : x ∉ A' := Finset.mem_compl.mp hx
      have hiff : ∀ y, y ∈ A' ↔ y ≠ x := by
        have heq : A' = Finset.univ.erase x := Finset.eq_of_subset_of_card_le
          (fun y hy => Finset.mem_erase.mpr ⟨fun h => hxA (h ▸ hy), Finset.mem_univ y⟩)
          (by rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcard, hc3])
        intro y
        rw [heq]
        simp
      rcases hall x with rfl | rfl | rfl | rfl
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
        ext y
        simp only [Finset.mem_coe, hiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hall y with rfl | rfl | rfl | rfl <;> simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        ext y
        simp only [Finset.mem_coe, hiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hall y with rfl | rfl | rfl | rfl <;> simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        ext y
        simp only [Finset.mem_coe, hiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hall y with rfl | rfl | rfl | rfl <;> simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
      · refine Or.inr (Or.inr (Or.inl ?_))
        ext y
        simp only [Finset.mem_coe, hiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hall y with rfl | rfl | rfl | rfl <;> simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
  -- clusters of a tree are not crossing
  have hcross : ∀ {A B : Set X}, A ∈ rootedClusters (reducedRootedTree hN hX) → B ∈ rootedClusters (reducedRootedTree hN hX) →
      ∀ {x y z : X}, x ∈ A → x ∈ B → y ∈ A → y ∉ B → z ∉ A → z ∈ B → False := by
    rintro A B ⟨-, e, rfl⟩ ⟨-, f, rfl⟩ x y z h₁ h₂ h₃ h₄ h₅ h₆
    obtain ⟨S, hS, ht, hs, hSx⟩ := exists_side_of_isTree hR hRT f
    have hf : IsCutOn (reducedRootedTree hN hX) Finset.univ f := fun w _ hw => by
      obtain ⟨y', hy'⟩ := exists_reaches_leaf hR ((reducedRootedTree hN hX).graph.target f)
      exact (separates_of_crossing (Y := Set.univ) hR (e := f) ⟨y', Set.mem_univ y', hy'⟩ (fun g _ hgf hc => hgf ((hS g).mp hc)) ht hs).2.1 w
        (Set.mem_univ w) ((hSx w).mpr hw)
    exact not_crossing hR hf (Finset.mem_univ x) h₁ h₂ h₃ h₄ h₅ h₆
  -- a cherry is a cluster
  have hex : ({a, b} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) ∨ ({c, d} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) := by
    have hm := LabelledGraph.HasQuartetTopology.pair_mem_splits hT hall
    obtain ⟨-, -, hcut⟩ := (mem_splits_Trd_iff hN hX _).mp hm
    obtain ⟨e, S, hS, hA⟩ := (blobTree_hasCutSplit_iff hM _).mpr hcut
    have hleaf : ∀ x, (reducedRootedTree hN hX).leaf x ∈ S ↔ x = a ∨ x = b := fun x => by
      have := Set.ext_iff.mp hA x
      have h' : ((lsaPlus hN hX).blobTree hM).leaf x ∈ S ↔ x = a ∨ x = b := by simpa using this
      exact h'
    have hncard : ∀ {p q : X}, p ≠ q → 2 ≤ ({p, q} : Set X).ncard := fun hpq => (Set.ncard_pair hpq).ge
    rcases (hS e).mpr rfl with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · -- the target of `e` is off `S`
      right
      refine ⟨hncard hcd, e, ?_⟩
      ext x
      have hb := mem_side_iff_isBelow hR (S := Sᶜ) (e := e) (fun f => (reducedRootedTree hN hX).graph.crosses_compl f S |>.trans (hS f)) ht (not_not.mpr hs) x
      simp only [Set.mem_compl_iff, hleaf] at hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      rw [← hb]
      rcases hall x with rfl | rfl | rfl | rfl <;> simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
    · left
      refine ⟨hncard hab, e, ?_⟩
      ext x
      have hb := mem_side_iff_isBelow hR hS ht hs x
      rw [hleaf] at hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      exact hb
  -- the exclusions
  have hn₁₂ : ({a, b, c} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) → ({a, b, d} : Set X) ∉ rootedClusters (reducedRootedTree hN hX) := fun h₁ h₂ =>
    hcross h₁ h₂ (x := a) (y := c) (z := d) (by simp) (by simp) (by simp) (by simp [hac.symm, hbc.symm, hcd]) (by simp [had.symm, hbd.symm, hcd.symm]) (by simp)
  have hn₁₃ : ({a, b, c} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) → ({c, d, a} : Set X) ∉ rootedClusters (reducedRootedTree hN hX) := fun h₁ h₂ =>
    hcross h₁ h₂ (x := a) (y := b) (z := d) (by simp) (by simp) (by simp) (by simp [hab.symm, hbc, hbd]) (by simp [had.symm, hbd.symm, hcd.symm]) (by simp)
  have hn₁₄ : ({a, b, c} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) → ({c, d, b} : Set X) ∉ rootedClusters (reducedRootedTree hN hX) := fun h₁ h₂ =>
    hcross h₁ h₂ (x := b) (y := a) (z := d) (by simp) (by simp) (by simp) (by simp [hab, hac, had]) (by simp [had.symm, hbd.symm, hcd.symm]) (by simp)
  have hn₂₃ : ({a, b, d} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) → ({c, d, a} : Set X) ∉ rootedClusters (reducedRootedTree hN hX) := fun h₁ h₂ =>
    hcross h₁ h₂ (x := a) (y := b) (z := c) (by simp) (by simp) (by simp) (by simp [hab.symm, hbc, hbd]) (by simp [hac.symm, hbc.symm, hcd]) (by simp)
  have hn₂₄ : ({a, b, d} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) → ({c, d, b} : Set X) ∉ rootedClusters (reducedRootedTree hN hX) := fun h₁ h₂ =>
    hcross h₁ h₂ (x := b) (y := a) (z := c) (by simp) (by simp) (by simp) (by simp [hab, hac, had]) (by simp [hac.symm, hbc.symm, hcd]) (by simp)
  have hn₃₄ : ({c, d, a} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) → ({c, d, b} : Set X) ∉ rootedClusters (reducedRootedTree hN hX) := fun h₁ h₂ =>
    hcross h₁ h₂ (x := c) (y := a) (z := b) (by simp) (by simp) (by simp) (by simp [hab, hac, had]) (by simp [hab.symm, hbc, hbd]) (by simp)
  have hnp₃ : ({a, b} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) → ({c, d, a} : Set X) ∉ rootedClusters (reducedRootedTree hN hX) := fun h₁ h₂ =>
    hcross h₁ h₂ (x := a) (y := b) (z := c) (by simp) (by simp) (by simp) (by simp [hab.symm, hbc, hbd]) (by simp [hac.symm, hbc.symm]) (by simp)
  have hnp₄ : ({a, b} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) → ({c, d, b} : Set X) ∉ rootedClusters (reducedRootedTree hN hX) := fun h₁ h₂ =>
    hcross h₁ h₂ (x := b) (y := a) (z := c) (by simp) (by simp) (by simp) (by simp [hab, hac, had]) (by simp [hac.symm, hbc.symm]) (by simp)
  have hnq₁ : ({c, d} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) → ({a, b, c} : Set X) ∉ rootedClusters (reducedRootedTree hN hX) := fun h₁ h₂ =>
    hcross h₁ h₂ (x := c) (y := d) (z := a) (by simp) (by simp) (by simp) (by simp [had.symm, hbd.symm, hcd.symm]) (by simp [hac, had]) (by simp)
  have hnq₂ : ({c, d} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) → ({a, b, d} : Set X) ∉ rootedClusters (reducedRootedTree hN hX) := fun h₁ h₂ =>
    hcross h₁ h₂ (x := d) (y := c) (z := a) (by simp) (by simp) (by simp) (by simp [hac.symm, hbc.symm, hcd]) (by simp [hac, had]) (by simp)
  -- the seven forms
  change rootedClusters (reducedRootedTree hN hX) = _ ∨ rootedClusters (reducedRootedTree hN hX) = _ ∨ rootedClusters (reducedRootedTree hN hX) = _ ∨
    rootedClusters (reducedRootedTree hN hX) = _ ∨ rootedClusters (reducedRootedTree hN hX) = _ ∨ rootedClusters (reducedRootedTree hN hX) = _ ∨
    rootedClusters (reducedRootedTree hN hX) = _
  by_cases hp₁ : ({a, b} : Set X) ∈ rootedClusters (reducedRootedTree hN hX)
  · by_cases hp₂ : ({c, d} : Set X) ∈ rootedClusters (reducedRootedTree hN hX)
    · -- `((a, b), (c, d))`
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Set.ext fun A => ⟨fun hA => ?_, ?_⟩)))))
      · rcases hsix A hA with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hA (hnq₁ hp₂)
        · exact absurd hA (hnq₂ hp₂)
        · exact absurd hA (hnp₃ hp₁)
        · exact absurd hA (hnp₄ hp₁)
      · rintro (rfl | rfl)
        · exact hp₁
        · exact hp₂
    · by_cases ht₁ : ({a, b, c} : Set X) ∈ rootedClusters (reducedRootedTree hN hX)
      · -- `(((a, b), c), d)`
        refine Or.inl (Set.ext fun A => ⟨fun hA => ?_, ?_⟩)
        · rcases hsix A hA with rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact absurd hA hp₂
          · exact Or.inr rfl
          · exact absurd hA (hn₁₂ ht₁)
          · exact absurd hA (hnp₃ hp₁)
          · exact absurd hA (hnp₄ hp₁)
        · rintro (rfl | rfl)
          · exact hp₁
          · exact ht₁
      · by_cases ht₂ : ({a, b, d} : Set X) ∈ rootedClusters (reducedRootedTree hN hX)
        · -- `(((a, b), d), c)`
          refine Or.inr (Or.inl (Set.ext fun A => ⟨fun hA => ?_, ?_⟩))
          · rcases hsix A hA with rfl | rfl | rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact absurd hA hp₂
            · exact absurd hA ht₁
            · exact Or.inr rfl
            · exact absurd hA (hnp₃ hp₁)
            · exact absurd hA (hnp₄ hp₁)
          · rintro (rfl | rfl)
            · exact hp₁
            · exact ht₂
        · -- `((a, b), c, d)`
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Set.ext fun A => ⟨fun hA => ?_, ?_⟩))))))
          · rcases hsix A hA with rfl | rfl | rfl | rfl | rfl | rfl
            · rfl
            · exact absurd hA hp₂
            · exact absurd hA ht₁
            · exact absurd hA ht₂
            · exact absurd hA (hnp₃ hp₁)
            · exact absurd hA (hnp₄ hp₁)
          · rintro rfl
            exact hp₁
  · have hp₂ := hex.resolve_left hp₁
    by_cases ht₃ : ({c, d, a} : Set X) ∈ rootedClusters (reducedRootedTree hN hX)
    · -- `(((c, d), a), b)`
      refine Or.inr (Or.inr (Or.inl (Set.ext fun A => ⟨fun hA => ?_, ?_⟩)))
      · rcases hsix A hA with rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hA hp₁
        · exact Or.inl rfl
        · exact absurd hA (hnq₁ hp₂)
        · exact absurd hA (hnq₂ hp₂)
        · exact Or.inr rfl
        · exact absurd hA (hn₃₄ ht₃)
      · rintro (rfl | rfl)
        · exact hp₂
        · exact ht₃
    · by_cases ht₄ : ({c, d, b} : Set X) ∈ rootedClusters (reducedRootedTree hN hX)
      · -- `(((c, d), b), a)`
        refine Or.inr (Or.inr (Or.inr (Or.inl (Set.ext fun A => ⟨fun hA => ?_, ?_⟩))))
        · rcases hsix A hA with rfl | rfl | rfl | rfl | rfl | rfl
          · exact absurd hA hp₁
          · exact Or.inl rfl
          · exact absurd hA (hnq₁ hp₂)
          · exact absurd hA (hnq₂ hp₂)
          · exact absurd hA ht₃
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact hp₂
          · exact ht₄
      · -- `((c, d), a, b)`
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Set.ext fun A => ⟨fun hA => ?_, ?_⟩))))))
        · rcases hsix A hA with rfl | rfl | rfl | rfl | rfl | rfl
          · exact absurd hA hp₁
          · rfl
          · exact absurd hA (hnq₁ hp₂)
          · exact absurd hA (hnq₂ hp₂)
          · exact absurd hA ht₃
          · exact absurd hA ht₄
        · rintro rfl
          exact hp₂

end RootedForms

end AllmanEtAl2023
