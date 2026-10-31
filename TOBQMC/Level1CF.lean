module

public import Basic.Phylogenetics.NMSC.TreeCF
public import TOBQMC.Level1Blobs

/-!
# TOB-QMC §4.3: concordance factors of induced cut-edge splits at level 1

TOB-QMC's consistency claim (lines 596–600 of v5) needs TINNiK's hypothesis tests to be correct on all
four-taxon subsets, that is, CF-detectability at the parameters of the network. The paper's assumptions give
it directly on the non-treelike subsets (6a) and on the subsets that the tree of blobs resolves
(T-quartet-nonanomaly, with exchangeability). The paper does not discuss the third class: an
induced cut-edge split `s` that the tree of blobs does not display. Nothing needs to be assumed there, as
`s` has the strictly largest concordance factor.

Take a highest arc `e` that separates a cherry `P` of `s` from the other cherry. It is not a bridge, as
the tree of blobs would display `s`. So its blob has a reticulation `h`, and `h` is below `e`, so no
taxon of the other cherry is below `h`. As `e` is highest, a taxon of the other cherry is below the source of `e`,
hence below a second arc `f` leaving that source, and `f` dominates the taxa of the other cherry below it,
since the only way into the descendants of a non-bridge of the blob is `h`. This is a fork, for
`NMSC.nmscCF_lt_of_fork`.

The network need not be binary here. Nor does the proof place the taxa in distinct blocks at the blob, or
use Lemma 4.

## Main results

* `Level1.exists_fork`: the fork of an induced cut-edge split that the tree of blobs does not display.
* `Level1.nmscCF_lt_of_not_displays`: the concordance factor of such a split is strictly the largest.
* `Level1.nmscCF_lt_of_inducedCutSplit`: T-quartet-nonanomaly gives the same on all induced cut-edge
  splits, condition 6b of the paper, at level 1.
* `Level1.cfDetectable`: CF-detectability under the paper's assumptions.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace TOBQMC.Level1

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

omit [Fintype X] [DecidableEq X] in
/-- A bridge dominates the taxa below it. -/
theorem dominates_of_isBridge (hN : N.IsPhylogenetic) {f : E} (hf : IsBridge N f) {x : X}
    (hb : N.IsBelow f x) : N.Dominates f x := by
  intro hav
  have hroot : ¬ N.graph.Reaches (N.graph.target f) N.root :=
    fun hr => target_ne_root hN f (eq_root_of_reaches_root hN hr)
  obtain ⟨g, hgf, hs, ht, -⟩ := exists_entering_arc hav hroot hb
  exact hs ((isBridge_iff_reaches hN f).mp hf g hgf ht)

/-- A bridge separating the cherry `P` of `s` from the other taxa makes the tree of blobs display `s`. -/
theorem displays_of_isBridge (hN : N.IsPhylogenetic) (s : QuartetTree X) {P : Finset X}
    (hP : P ∈ s.val) {e : E} (hb : IsBridge N e) (hd : ∀ x ∈ P, N.Dominates e x)
    (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x) :
    Displays (treeOfBlobs N) s := by
  set A : Finset X := univ.filter fun z => N.IsBelow e z with hA
  have hmem : ∀ z, z ∈ A ↔ N.IsBelow e z := fun z => by simp [hA]
  have hcut : N.HasCutSplit (A : Set X) := by
    refine ⟨e, {u | N.graph.Reaches (N.graph.target e) u}, isBridge_crosses_iff hN hb, ?_⟩
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, mem_coe, hmem]
    rfl
  have hPcard := s.card_of_mem hP
  obtain ⟨a, ha⟩ := card_pos.mp (by omega : 0 < P.card)
  have hQ := s.sdiff_mem hP
  obtain ⟨c, hc⟩ := card_pos.mp (by rw [s.card_of_mem hQ]; omega : 0 < (s.taxa \ P).card)
  obtain ⟨hcq, hcP⟩ := mem_sdiff.mp hc
  have hAne : A.Nonempty := ⟨a, (hmem a).2 ((hd a ha).isBelow hN)⟩
  have hAcne : Aᶜ.Nonempty := ⟨c, mem_compl.2 fun h => hn c hcq hcP ((hmem c).1 h)⟩
  refine ⟨A, by simp only [treeOfBlobs, mem_filter, mem_univ, true_and]; exact ⟨hAne, hAcne, hcut⟩, ?_⟩
  have heq : A ∩ s.taxa = P := by
    ext z
    rw [mem_inter, hmem]
    constructor
    · rintro ⟨hb', hz⟩
      by_contra hzP
      exact hn z hz hzP hb'
    · exact fun hz => ⟨(hd z hz).isBelow hN, s.subset_taxa hP hz⟩
  rw [heq]
  exact hP

omit [Fintype X] in
/-- An induced cut-edge split: an arc dominates one of its cherries, with the other taxa not below it. -/
theorem exists_separating_arc (hN : N.IsPhylogenetic) {s : QuartetTree X}
    (hs : InducedCutSplit N s) :
    ∃ P ∈ s.val, ∃ e, (∀ x ∈ P, N.Dominates e x) ∧ ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x := by
  obtain ⟨B, hB, hcut⟩ := hs
  obtain ⟨e, ⟨-, hd, hn⟩ | ⟨-, hd, hn⟩⟩ := (hasCutSplitOn_iff_separates hN _ _).1 hcut
  · exact ⟨B, hB, e, fun x hx => hd x ⟨s.subset_taxa hB hx, hx⟩, fun x hx hxB => hn x ⟨hx, hxB⟩⟩
  · refine ⟨s.taxa \ B, s.sdiff_mem hB, e,
      fun x hx => hd x ⟨(mem_sdiff.1 hx).1, (mem_sdiff.1 hx).2⟩, fun x hx hxB => hn x ⟨hx, ?_⟩⟩
    by_contra hxn
    exact hxB (mem_sdiff.2 ⟨hx, hxn⟩)

section LevelOne

variable [Fintype V] [Fintype E]

omit [Fintype X] [DecidableEq X] in
/-- The source of a non-bridge has only one incoming arc: if it had two, it would be the reticulation
of its blob, which the target of the arc reaches. -/
theorem indegree_source_le_one (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) {e : E}
    (he : ¬ IsBridge N e) : N.graph.indegree (N.graph.source e) ≤ 1 := by
  by_contra hc
  exact not_reaches_source hN e (reaches_reticulation hN hLevel .refl (by omega)
    (sameBlob_of_not_isBridge he))

omit [Fintype X] in
/-- A highest separating arc `e`, not a bridge: a taxon of the other cherry is below its source. If the
source is not the root, it has one parent arc, which dominates what `e` dominates, so as `e` is
highest it has a taxon of the other cherry below it. -/
theorem exists_mem_reaches_source (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    (s : QuartetTree X) {P : Finset X} (hP : P ∈ s.val) {e : E} (hb : ¬ IsBridge N e)
    (hd : ∀ x ∈ P, N.Dominates e x)
    (hmax : ∀ g, (∀ x ∈ P, N.Dominates g x) → (∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow g x) →
      ¬ Relation.TransGen N.graph.Adj (N.graph.target g) (N.graph.target e)) :
    ∃ x ∈ s.taxa, x ∉ P ∧ N.graph.Reaches (N.graph.source e) (N.leaf x) := by
  by_cases hroot : N.graph.source e = N.root
  · have hQ := s.sdiff_mem hP
    obtain ⟨x, hx⟩ := card_pos.mp (by rw [s.card_of_mem hQ]; omega : 0 < (s.taxa \ P).card)
    exact ⟨x, (mem_sdiff.1 hx).1, (mem_sdiff.1 hx).2, hroot ▸ hN.root_reaches _⟩
  · have hin := indegree_source_le_one hN hLevel hb
    obtain ⟨p, hp⟩ := NMSC.exists_arc_into hN hroot
    have hdp : ∀ x ∈ P, N.Dominates p x := by
      intro x hx hav
      have h1 := hav.source_of_not_avoidingReach (hd x hx)
      rcases Relation.ReflTransGen.cases_tail h1 with heq | ⟨c, -, g, hgp, -, hg⟩
      · exact hroot heq
      · exact hgp (eq_of_indegree_le_one hN (hp ▸ hin) (hg.trans hp.symm))
    by_contra hno
    push Not at hno
    refine hmax p hdp (fun x hx hxP hbx => hno x hx hxP (hp ▸ hbx)) ?_
    exact Relation.TransGen.single ⟨e, hp.symm, rfl⟩

/-- **The fork of an induced cut-edge split that the tree of blobs does not display**, at level 1. -/
theorem exists_fork (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) {s : QuartetTree X}
    (hs : InducedCutSplit N s) (hnd : ¬ Displays (treeOfBlobs N) s) :
    ∃ P ∈ s.val, ∃ (e f : E) (c : X), N.graph.source f = N.graph.source e ∧
      (∀ x ∈ P, N.Dominates e x) ∧ (∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x) ∧
      c ∈ s.taxa ∧ c ∉ P ∧ N.IsBelow f c ∧
      ∀ x ∈ s.taxa, x ∉ P → N.IsBelow f x → N.Dominates f x := by
  obtain ⟨P, hP, e₀, hd₀, hn₀⟩ := exists_separating_arc hN hs
  -- a highest separating arc
  obtain ⟨_, ⟨e, ⟨hd, hn⟩, rfl⟩, hmin⟩ := exists_source hN
    (S := N.graph.target '' {e | (∀ x ∈ P, N.Dominates e x) ∧ ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x})
    ⟨_, e₀, ⟨hd₀, hn₀⟩, rfl⟩
  have hb : ¬ IsBridge N e := fun hb => hnd (displays_of_isBridge hN s hP hb hd hn)
  -- the other taxon, below a second arc at the source of `e`
  obtain ⟨c, hcq, hcP, hcw⟩ := exists_mem_reaches_source hN hLevel s hP hb hd
    fun g hgd hgn => hmin _ ⟨g, ⟨hgd, hgn⟩, rfl⟩
  obtain ⟨f, hfs, hcf⟩ : ∃ f, N.graph.source f = N.graph.source e ∧ N.IsBelow f c := by
    rcases Relation.ReflTransGen.cases_head hcw with heq | ⟨_, ⟨f, hf, rfl⟩, hc⟩
    · exfalso
      have h0 := (hN.leaves (N.leaf c)).mpr ⟨c, rfl⟩
      exact (DirectedMultigraph.outdegree_eq_zero_iff _ _).mp h0 e heq
    · exact ⟨f, hf, hc⟩
  refine ⟨P, hP, e, f, c, hfs, hd, hn, hcq, hcP, hcf, fun x hx hxP hbx => ?_⟩
  -- the reticulation of the blob is below `e`, so `x` is not below it
  by_cases hfb : IsBridge N f
  · exact dominates_of_isBridge hN hfb hbx
  · obtain ⟨h, hh, hh₂⟩ := (exists_reticulation_or_forall_isBridge hN (N.graph.source e)).resolve_right
      fun hall => hb (hall e (Or.inl rfl))
    have hth := reaches_reticulation hN hLevel hh hh₂ (sameBlob_of_not_isBridge hb)
    exact dominates_of_below hN hLevel hh hh₂ (hfs ▸ sameBlob_of_not_isBridge hfb) hbx
      fun hhx => hn x hx hxP (hth.trans hhx)

/-- **The third class.** At level 1, an induced cut-edge split that the tree of blobs does not display has
the strictly largest concordance factor, for all valid parameters and `0 ≤ ρ ≤ 1`. -/
theorem nmscCF_lt_of_not_displays (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {s : QuartetTree X}
    (hs : InducedCutSplit N s) (hnd : ¬ Displays (treeOfBlobs N) s) {r : QuartetTree X}
    (hr : r ∈ s.alternatives) : nmscCF N θ ρ r < nmscCF N θ ρ s := by
  obtain ⟨P, hP, e, f, c, hfs, hd, hn, hcq, hcP, hcf, hdf⟩ := exists_fork hN hLevel hs hnd
  exact NMSC.nmscCF_lt_of_fork hN hθ hρ s hP hfs hd hn hcq hcP hcf hdf hr

/-- At level 1, condition 4 of TOB-QMC (T-quartet-nonanomaly) gives condition 6b (class 1
quartet-nonanomaly): on every induced cut-edge split, the split has the strictly largest concordance
factor. -/
theorem nmscCF_lt_of_inducedCutSplit (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) {s : QuartetTree X}
    (hs : InducedCutSplit N s) {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    nmscCF N θ ρ r < nmscCF N θ ρ s := by
  by_cases hd : Displays (treeOfBlobs N) s
  · exact hNon s hd r hr
  · exact nmscCF_lt_of_not_displays hN hLevel hθ hρ hs hd hr

/-- **CF-detectability under the assumptions of TOB-QMC**, for all four-taxon subsets of a level-1
network: non-treelike subsets by 6a; subsets the tree of blobs resolves by T-quartet-nonanomaly and
exchangeability; and the other treelike subsets by `nmscCF_lt_of_not_displays`, with no assumption.
This is what TOB-QMC §4.3 needs for TINNiK's tests to be correct on all subsets. -/
theorem cfDetectable {θ : MetricData E} {ρ : ℝ} (hStd : StandardAssumptions N θ ρ)
    (hLevel : IsLevelOne N) (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      External.AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) :
    External.AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ) :=
  ⟨fun s hs => ⟨fun _ hr =>
      (nmscCF_lt_of_inducedCutSplit hStd.phylogenetic hLevel hStd.metric hStd.rho hNon hs hr).ne,
    NMSC.cut_alternatives hStd.phylogenetic hStd.metric hStd.rho s hs⟩, hBlob⟩

end LevelOne

end TOBQMC.Level1
