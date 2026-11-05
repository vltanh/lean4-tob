module

public import Phylogenetics.Network.Cuts
public import Phylogenetics.Network.DeletedArcs
public import Phylogenetics.Network.Quartets
public import Phylogenetics.Tree.Metric
public import Phylogenetics.Tree.Splits

/-!
# Cut splits of induced networks, in the language of domination

* `ECToBlob.FalseEdge.RDom N a b c d`: an arc has `a, b` below it and `c, d` off it, which is a cut split of the
  network induced on `a, b, c, d` (`ECToBlob.FalseEdge.rdom_of_hasCutSplitOn`,
  `ECToBlob.Coarsening.inducedCutSplit_of_rdom`, `ECToBlob.Coarsening.exists_rdom_of_inducedCutSplit`).
* `ECToBlob.FalseEdge.Sep T P x y`: an edge of `T` inside `P` separates `x` from `y`; quartet trees as four taxa
  (`ECToBlob.FalseEdge.taxa_quartetTree`, `ECToBlob.FalseEdge.exists_tuple`).
* `ECToBlob.Deterministic.inducedCutSplit_of_mem`: a side of the tree of blobs is a cut split of the network induced
  on each quartet it resolves.
* `TOBQMC.eq_of_splitOffAt`: off a deletion, the arcs of two splits on four taxa are nested or disjoint, so the splits
  are one quartet tree. This is a step of the source's proof of Lemma 1 of Ané et al. 2024 (`src/TOBQMC/Lemma1.lean`).

ECToBlob and TOB-QMC use these, and so does NANUQ's Proposition 9.
-/

@[expose] public noncomputable section

open scoped Classical

section
open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace ECToBlob.FalseEdge

variable {V E X : Type*} {N : RootedNetwork V E X}

/-- `x₁x₂|x₃x₄` is a cut split of the network induced on the four taxa, in the language of
domination: `hasCutSplitOn_iff_separates`. -/
def RDom (N : RootedNetwork V E X) (x₁ x₂ x₃ x₄ : X) : Prop :=
  ∃ g, (N.Dominates g x₁ ∧ N.Dominates g x₂ ∧ ¬ N.IsBelow g x₃ ∧ ¬ N.IsBelow g x₄) ∨
    (N.Dominates g x₃ ∧ N.Dominates g x₄ ∧ ¬ N.IsBelow g x₁ ∧ ¬ N.IsBelow g x₂)

theorem RDom.swap {x₁ x₂ x₃ x₄ : X} (h : RDom N x₁ x₂ x₃ x₄) : RDom N x₁ x₂ x₄ x₃ := by
  obtain ⟨g, ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩⟩ := h
  · exact ⟨g, Or.inl ⟨h1, h2, h4, h3⟩⟩
  · exact ⟨g, Or.inr ⟨h2, h1, h3, h4⟩⟩

theorem RDom.symm {x₁ x₂ x₃ x₄ : X} (h : RDom N x₁ x₂ x₃ x₄) : RDom N x₃ x₄ x₁ x₂ := by
  obtain ⟨g, h | h⟩ := h
  · exact ⟨g, Or.inr h⟩
  · exact ⟨g, Or.inl h⟩

section Trees

variable [Fintype X] [DecidableEq X]

/-- The taxa `x`, `y` of the side `P` of an edge of `T` are in distinct blocks at that edge. -/
def Sep (T : Finset (Finset X)) (P : Finset X) (x y : X) : Prop :=
  x ≠ y ∧ ¬ ∃ C ∈ T, C ⊂ P ∧ x ∈ C ∧ y ∈ C

omit [Fintype X] [DecidableEq X] in
theorem Sep.symm {T : Finset (Finset X)} {P : Finset X} {x y : X} (h : Sep T P x y) :
    Sep T P y x :=
  ⟨h.1.symm, fun ⟨C, hC, hCP, hy, hx⟩ => h.2 ⟨C, hC, hCP, hx, hy⟩⟩

/-- Being in one block is transitive, so at each `z` one of the taxa in distinct blocks is in
another block than `z`. -/
theorem Sep.or {T : Finset (Finset X)} (hT : IsSplitFamily T) {P : Finset X} (hP : P ≠ univ)
    {x y : X} (h : Sep T P x y) (z : X) : Sep T P z x ∨ Sep T P z y := by
  by_contra hcon
  rw [not_or] at hcon
  have key : ∀ {t : X}, ¬ Sep T P z t → z = t ∨ ∃ C ∈ T, C ⊂ P ∧ z ∈ C ∧ t ∈ C := by
    intro t ht
    by_cases hzt : z = t
    · exact Or.inl hzt
    · right
      by_contra hne
      exact ht ⟨hzt, hne⟩
  rcases key hcon.1 with rfl | ⟨C₁, hC₁, hC₁P, hz₁, hx₁⟩
  · rcases key hcon.2 with rfl | ⟨C₂, hC₂, hC₂P, hz₂, hy₂⟩
    · exact h.1 rfl
    · exact h.2 ⟨C₂, hC₂, hC₂P, hz₂, hy₂⟩
  · rcases key hcon.2 with rfl | ⟨C₂, hC₂, hC₂P, hz₂, hy₂⟩
    · exact h.2 ⟨C₁, hC₁, hC₁P, hx₁, hz₁⟩
    · rcases hT.compatible C₁ hC₁ C₂ hC₂ with hs | hs | hs | hs
      · exact h.2 ⟨C₂, hC₂, hC₂P, hs hx₁, hy₂⟩
      · exact h.2 ⟨C₁, hC₁, hC₁P, hx₁, hs hy₂⟩
      · exact Finset.disjoint_left.1 hs hz₁ hz₂
      · apply hP
        rw [eq_univ_iff_forall]
        intro t
        have : t ∈ C₁ ∪ C₂ := hs ▸ mem_univ t
        rcases mem_union.1 this with ht | ht
        · exact hC₁P.1 ht
        · exact hC₂P.1 ht

/-! ### Quartet trees as four taxa -/

omit [Fintype X] in
theorem insert_pair_comm (a b c d : X) : ({c, d, a, b} : Finset X) = {a, b, c, d} := by
  ext z
  simp only [mem_insert, mem_singleton]
  tauto

omit [Fintype X] in
theorem insert_insert_pair_comm (a b c d : X) : ({a, b, d, c} : Finset X) = {a, b, c, d} := by
  ext z
  simp only [mem_insert, mem_singleton]
  tauto

omit [Fintype X] in
theorem pair_insert_comm (a b c d : X) : ({b, a, c, d} : Finset X) = {a, b, c, d} := by
  ext z
  simp only [mem_insert, mem_singleton]
  tauto

omit [Fintype X] in
theorem taxa_quartetTree {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    (quartetTree a b c d h).taxa = {a, b, c, d} := by
  ext z
  simp [QuartetTree.taxa, quartetTree]
  tauto

omit [Fintype X] in
theorem inter_four {A : Finset X} {a b c d : X} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∉ A)
    (hd : d ∉ A) :
    A ∩ {a, b, c, d} = {a, b} := by
  ext z
  simp only [mem_inter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hz, rfl | rfl | rfl | rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hz hc
    · exact absurd hz hd
  · rintro (rfl | rfl)
    · exact ⟨ha, Or.inl rfl⟩
    · exact ⟨hb, Or.inr (Or.inl rfl)⟩

/-- A quartet with taxa in distinct blocks at the edge is in the multipartition of the edge. -/
theorem quartetTree_mem {T : Finset (Finset X)} {A : Finset X} {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∉ A) (hd : d ∉ A)
    (hab : Sep T A a b) (hcd : Sep T Aᶜ c d) :
    quartetTree a b c d h ∈ multipartitionQuartets T A := by
  have h₁ : A ∩ (quartetTree a b c d h).taxa = {a, b} := by
    rw [taxa_quartetTree, inter_four ha hb hc hd]
  have h₂ : Aᶜ ∩ (quartetTree a b c d h).taxa = {c, d} := by
    rw [taxa_quartetTree, ← insert_pair_comm a b c d,
      inter_four (mem_compl.2 hc) (mem_compl.2 hd) (fun h' => mem_compl.1 h' ha)
        (fun h' => mem_compl.1 h' hb)]
  simp only [multipartitionQuartets, bipartitionQuartets, mem_filter, mem_univ, true_and]
  refine ⟨?_, ?_, ?_⟩
  · rw [h₁]
    simp [quartetTree]
  · rw [h₁]
    rintro ⟨C, hC, hCA, hsub⟩
    exact hab.2 ⟨C, hC, hCA, hsub (by simp), hsub (by simp)⟩
  · rw [h₂]
    rintro ⟨C, hC, hCA, hsub⟩
    exact hcd.2 ⟨C, hC, hCA, hsub (by simp), hsub (by simp)⟩

/-- Every quartet of the multipartition has this form. -/
theorem exists_tuple {T : Finset (Finset X)} {A : Finset X} {s : QuartetTree X}
    (hs : s ∈ multipartitionQuartets T A) :
    ∃ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), s = quartetTree a b c d h ∧ a ∈ A ∧
      b ∈ A ∧ c ∉ A ∧ d ∉ A ∧ Sep T A a b ∧ Sep T Aᶜ c d := by
  obtain ⟨hcard, h2, hdisj⟩ := s.2
  obtain ⟨B, C, hBC, hsv⟩ := Finset.card_eq_two.1 hcard
  have hB : B ∈ s.val := by simp [hsv]
  have hC : C ∈ s.val := by simp [hsv]
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (h2 B hB)
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.1 (h2 C hC)
  have hdj := Finset.disjoint_left.1 (hdisj _ hB _ hC hBC)
  have hac : a ≠ c := fun h => hdj (a := a) (by simp) (by simp [h])
  have had : a ≠ d := fun h => hdj (a := a) (by simp) (by simp [h])
  have hbc : b ≠ c := fun h => hdj (a := b) (by simp) (by simp [h])
  have hbd : b ≠ d := fun h => hdj (a := b) (by simp) (by simp [h])
  have hc4 := TreeMetric.card_four_of_ne hab hac had hbc hbd hcd
  have htaxa : s.taxa = {a, b, c, d} := by
    ext z
    simp [QuartetTree.taxa, hsv]
    tauto
  simp only [multipartitionQuartets, bipartitionQuartets, mem_filter, mem_univ, true_and] at hs
  obtain ⟨hmem, hn₁, hn₂⟩ := hs
  rw [hsv, mem_insert, mem_singleton] at hmem
  have hmemA : ∀ {y : X}, y ∈ s.taxa → (y ∈ A ∩ s.taxa ↔ y ∈ A) := fun hy => by simp [hy]
  have hta : a ∈ s.taxa := by simp [htaxa]
  have htb : b ∈ s.taxa := by simp [htaxa]
  have htc : c ∈ s.taxa := by simp [htaxa]
  have htd : d ∈ s.taxa := by simp [htaxa]
  have sep : ∀ {P : Finset X} {x y : X}, x ≠ y → x ∈ P ∩ s.taxa → y ∈ P ∩ s.taxa →
      P ∩ s.taxa = {x, y} → (¬ ∃ C ∈ T, C ⊂ P ∧ P ∩ s.taxa ⊆ C) → Sep T P x y := by
    intro P x y hxy _ _ hP hn
    refine ⟨hxy, ?_⟩
    rintro ⟨C, hC, hCP, hx, hy⟩
    refine hn ⟨C, hC, hCP, ?_⟩
    rw [hP]
    intro z hz
    rcases mem_insert.1 hz with rfl | hz
    · exact hx
    · rw [mem_singleton.1 hz]
      exact hy
  rcases hmem with hA | hA
  · have ha : a ∈ A := ((hmemA hta).1 (by simp [hA]))
    have hb : b ∈ A := ((hmemA htb).1 (by simp [hA]))
    have hc : c ∉ A := fun h => by
      have : c ∈ A ∩ s.taxa := mem_inter.2 ⟨h, htc⟩
      rw [hA] at this
      simp [hac.symm, hbc.symm] at this
    have hd : d ∉ A := fun h => by
      have : d ∈ A ∩ s.taxa := mem_inter.2 ⟨h, htd⟩
      rw [hA] at this
      simp [had.symm, hbd.symm] at this
    have hAc : Aᶜ ∩ s.taxa = {c, d} := by
      rw [htaxa, ← insert_pair_comm a b c d,
        inter_four (mem_compl.2 hc) (mem_compl.2 hd) (fun h' => mem_compl.1 h' ha)
          (fun h' => mem_compl.1 h' hb)]
    refine ⟨a, b, c, d, hc4, Subtype.ext hsv, ha, hb, hc, hd, ?_, ?_⟩
    · exact sep hab (by simp [hA]) (by simp [hA]) hA hn₁
    · exact sep hcd (by simp [hAc]) (by simp [hAc]) hAc hn₂
  · have ha : c ∈ A := ((hmemA htc).1 (by simp [hA]))
    have hb : d ∈ A := ((hmemA htd).1 (by simp [hA]))
    have hc : a ∉ A := fun h => by
      have : a ∈ A ∩ s.taxa := mem_inter.2 ⟨h, hta⟩
      rw [hA] at this
      simp [hac, had] at this
    have hd : b ∉ A := fun h => by
      have : b ∈ A ∩ s.taxa := mem_inter.2 ⟨h, htb⟩
      rw [hA] at this
      simp [hbc, hbd] at this
    have hAc : Aᶜ ∩ s.taxa = {a, b} := by
      rw [htaxa, inter_four (mem_compl.2 hc) (mem_compl.2 hd) (fun h' => mem_compl.1 h' ha)
          (fun h' => mem_compl.1 h' hb)]
    have hc4' := TreeMetric.card_four_of_ne hcd hac.symm hbc.symm had.symm hbd.symm hab
    refine ⟨c, d, a, b, hc4', Subtype.ext ?_, ha, hb, hc, hd, ?_, ?_⟩
    · rw [hsv]
      simp [quartetTree, Finset.pair_comm]
    · exact sep hcd (by simp [hA]) (by simp [hA]) hA hn₁
    · exact sep hab (by simp [hAc]) (by simp [hAc]) hAc hn₂

omit [Fintype X] in
/-- A cut split of an induced network, read from a quartet tree. -/
theorem hasCutSplitOn_of_inducedCutSplit {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hi : InducedCutSplit N (quartetTree a b c d h)) :
    N.HasCutSplitOn (({a, b, c, d} : Finset X) : Set X) (({a, b} : Finset X) : Set X) := by
  obtain ⟨B, hB, hcut⟩ := hi
  rw [taxa_quartetTree] at hcut
  simp only [quartetTree, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl
  · exact hcut
  · obtain ⟨_, hac, had, hbc, hbd, _⟩ := ne_of_card_four h
    refine (hasCutSplitOn_congr ?_).1 ((hasCutSplitOn_compl _ _).2 hcut)
    ext z
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, hn⟩
      · exact ⟨Or.inl rfl, Or.inl rfl⟩
      · exact ⟨Or.inr (Or.inl rfl), Or.inr rfl⟩
      · exact absurd (Or.inl rfl) hn
      · exact absurd (Or.inr rfl) hn
    · rintro ⟨hz, rfl | rfl⟩
      · exact ⟨hz, by simp [hac, had]⟩
      · exact ⟨hz, by simp [hbc, hbd]⟩

omit [Fintype X] in
/-- A cut split of an induced network in the language of domination. -/
theorem rdom_of_hasCutSplitOn (hN : N.IsPhylogenetic) {a b c d : X} (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d)
    (h : N.HasCutSplitOn (({a, b, c, d} : Finset X) : Set X) (({a, b} : Finset X) : Set X)) :
    RDom N a b c d := by
  rw [hasCutSplitOn_iff_separates hN] at h
  obtain ⟨g, ⟨_, h⟩ | ⟨_, h⟩⟩ := h
  · exact ⟨g, Or.inl ⟨h.1 a (by simp), h.1 b (by simp), h.2 c (by simp [hac.symm, hbc.symm]),
      h.2 d (by simp [had.symm, hbd.symm])⟩⟩
  · exact ⟨g, Or.inr ⟨h.1 c (by simp [hac.symm, hbc.symm]), h.1 d (by simp [had.symm, hbd.symm]),
      h.2 a (by simp), h.2 b (by simp)⟩⟩

end Trees

end ECToBlob.FalseEdge
end

section
open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace ECToBlob.Deterministic

open ECToBlob.FalseEdge

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- A side of the tree of blobs is a cut split of the network induced on each quartet it resolves.
-/
theorem inducedCutSplit_of_mem {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {A : Finset X}
    (hA : A ∈ treeOfBlobs N) {s : QuartetTree X} (hs : A ∩ s.taxa ∈ s.val) :
    InducedCutSplit N s := by
  obtain ⟨_, _, _, hcut⟩ := mem_filter.1 hA
  refine ⟨_, hs, ?_⟩
  have hcard₂ : (A ∩ s.taxa).card = 2 := s.2.2.1 _ hs
  have hcard₄ : s.taxa.card = 4 := s.card_taxa
  have hne₁ : ((s.taxa : Set X) ∩ (A : Set X)).Nonempty := by
    obtain ⟨x, hx⟩ : (A ∩ s.taxa).Nonempty := Finset.card_pos.1 (by omega)
    exact ⟨x, by simpa [and_comm] using hx⟩
  have hne₂ : ((s.taxa : Set X) \ (A : Set X)).Nonempty := by
    have : (s.taxa \ A).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
      rw [Finset.inter_eq_right.2 hemp] at hcard₂
      omega
    obtain ⟨x, hx⟩ := this
    exact ⟨x, by simpa using hx⟩
  refine (hasCutSplitOn_congr ?_).1 (hcut.hasCutSplitOn hN hne₁ hne₂)
  ext x
  simp only [Set.mem_inter_iff, Finset.mem_coe, mem_inter]
  tauto

end ECToBlob.Deterministic
end

section
open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace ECToBlob.Coarsening

open ECToBlob.FalseEdge ECToBlob.Deterministic

variable {V E X : Type*} {N : RootedNetwork V E X}

section Quartets

variable [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- A cut split of an induced network, from the language of domination. -/
theorem inducedCutSplit_of_rdom (hN : N.IsPhylogenetic) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) (hr : RDom N a b c d) :
    InducedCutSplit N (quartetTree a b c d h) := by
  obtain ⟨_, hac, had, hbc, hbd, _⟩ := ne_of_card_four h
  refine ⟨{a, b}, by simp [quartetTree], ?_⟩
  rw [taxa_quartetTree, hasCutSplitOn_iff_separates hN]
  have hin : ∀ x, x ∈ ((({a, b, c, d} : Finset X) : Set X) ∩ (({a, b} : Finset X) : Set X)) →
      x = a ∨ x = b := by
    intro x hx
    simpa using hx.2
  have hout : ∀ x, x ∈ ((({a, b, c, d} : Finset X) : Set X) \ (({a, b} : Finset X) : Set X)) →
      x = c ∨ x = d := by
    intro x hx
    have h₁ : x = a ∨ x = b ∨ x = c ∨ x = d := by simpa using hx.1
    have h₂ : ¬ (x = a ∨ x = b) := by simpa using hx.2
    tauto
  obtain ⟨g, ⟨g₁, g₂, g₃, g₄⟩ | ⟨g₁, g₂, g₃, g₄⟩⟩ := hr
  · refine ⟨g, Or.inl ⟨⟨a, by simp, by simp⟩, ?_, ?_⟩⟩
    · intro x hx
      rcases hin x hx with rfl | rfl
      · exact g₁
      · exact g₂
    · intro x hx
      rcases hout x hx with rfl | rfl
      · exact g₃
      · exact g₄
  · refine ⟨g, Or.inr ⟨⟨c, by simp, by simp [hac.symm, hbc.symm]⟩, ?_, ?_⟩⟩
    · intro x hx
      rcases hout x hx with rfl | rfl
      · exact g₁
      · exact g₂
    · intro x hx
      rcases hin x hx with rfl | rfl
      · exact g₃
      · exact g₄

omit [Fintype X] in
theorem mem_multipartitionQuartets_empty [Fintype X] {A : Finset X} {s : QuartetTree X}
    (hs : s ∈ bipartitionQuartets A) : s ∈ multipartitionQuartets (∅ : Finset (Finset X)) A :=
  mem_filter.2 ⟨hs, by simp, by simp⟩

/-- A cut split of an induced network, in the language of domination. -/
theorem exists_rdom_of_inducedCutSplit (hN : N.IsPhylogenetic) {s : QuartetTree X}
    (h : InducedCutSplit N s) :
    ∃ (a b c d : X) (hc : ({a, b, c, d} : Finset X).card = 4), s = quartetTree a b c d hc ∧
      RDom N a b c d := by
  obtain ⟨B, hB, hcut⟩ := id h
  have hmem : s ∈ bipartitionQuartets B := by
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rwa [Finset.inter_eq_left.2 (s.subset_taxa hB)]
  obtain ⟨a, b, c, d, hc, rfl, ha, hb, hc', hd, hab, hcd⟩ :=
    exists_tuple (mem_multipartitionQuartets_empty hmem)
  obtain ⟨_, hac, had, hbc, hbd, _⟩ := ne_of_card_four hc
  exact ⟨a, b, c, d, hc, rfl,
    rdom_of_hasCutSplitOn hN hac had hbc hbd (hasCutSplitOn_of_inducedCutSplit hc h)⟩

end Quartets

end ECToBlob.Coarsening
end

section
open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace TOBQMC

variable {V E X : Type*} {N : RootedNetwork V E X} {D : Set E}

section Uniqueness

variable [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- An arc of a split below the arc of another: its cherry is inside the other's cherry. -/
theorem subset_of_separatesOff_of_reachesOff (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {s s' : QuartetTree X}
    (hss : s.taxa = s'.taxa) {e e' : E} {P P' : Finset X} (hP : P ∈ s.val) (hP' : P' ∈ s'.val)
    (hsep : N.SeparatesOff D e (P : Set X) ((s.taxa \ P : Finset X) : Set X))
    (hsep' : N.SeparatesOff D e' (P' : Set X) ((s'.taxa \ P' : Finset X) : Set X))
    (hr : N.ReachesOff D (N.graph.target e) (N.graph.target e')) : P' ⊆ P := by
  intro y hy
  by_contra hyP
  have hyb := (hsep'.1 y hy).isBelowOff hN hD
  have hyq : y ∈ s.taxa \ P := mem_sdiff.mpr ⟨hss ▸ s'.subset_taxa hP' hy, hyP⟩
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < P.card by rw [s.card_of_mem hP]; norm_num)
  exact hsep.2 y hyq ⟨((hsep.1 x hx).isBelowOff hN hD).1, hr.trans hyb.2⟩

omit [Fintype X] in
/-- **The split of a cut edge is the only non-trivial split**: off a deletion, the arcs of two splits on four taxa are
nested or disjoint, so the splits are one quartet tree. -/
theorem eq_of_splitOffAt (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {s s' : QuartetTree X}
    (hss : s.taxa = s'.taxa) {e e' : E} (hs : N.SplitOffAt D e s) (hs' : N.SplitOffAt D e' s') :
    s = s' := by
  obtain ⟨P, hP, hsep⟩ := hs
  obtain ⟨P', hP', hsep'⟩ := hs'
  have hc := s.card_of_mem hP
  have hc' := s'.card_of_mem hP'
  by_cases hdis : Disjoint P P'
  · -- disjoint: `P'` is the other cherry of `s`
    have hsub : P' ⊆ s.taxa \ P := fun y hy =>
      mem_sdiff.mpr ⟨hss ▸ s'.subset_taxa hP' hy, disjoint_right.mp hdis hy⟩
    have heq : P' = s.taxa \ P := eq_of_subset_of_card_le hsub (by
      rw [card_sdiff_of_subset (s.subset_taxa hP), s.card_taxa]
      omega)
    exact QuartetTree.eq_of_taxa_eq_of_mem hss (heq ▸ s.sdiff_mem hP) hP'
  · -- they share a taxon: two arcs dominating it are ordered
    obtain ⟨x, hxP, hxP'⟩ := not_disjoint_iff.mp hdis
    have hPP' : P = P' := by
      by_cases hee : e = e'
      · subst hee
        exact (eq_of_subset_of_card_le (subset_of_separatesOff_of_reachesOff hN hD hss hP hP' hsep hsep' .refl)
          (by omega)).symm
      · have hle : ∀ {a b : E}, N.ReachesOff D (N.graph.target a) (N.graph.source b) → b ∉ D →
            N.ReachesOff D (N.graph.target a) (N.graph.target b) := fun h hb => h.tail_arc hb
        have hb := ((hsep.1 x hxP).isBelowOff hN hD).1
        have hb' := ((hsep'.1 x hxP').isBelowOff hN hD).1
        rcases DominatesOff.reaches_or_reaches hN hD (hsep.1 x hxP) (hsep'.1 x hxP') hee with h | h
        · exact (eq_of_subset_of_card_le
            (subset_of_separatesOff_of_reachesOff hN hD hss hP hP' hsep hsep' (hle h hb')) (by omega)).symm
        · exact eq_of_subset_of_card_le
            (subset_of_separatesOff_of_reachesOff hN hD hss.symm hP' hP hsep' hsep (hle h hb)) (by omega)
    exact QuartetTree.eq_of_taxa_eq_of_mem hss hP (hPP' ▸ hP')

end Uniqueness

end TOBQMC
end
