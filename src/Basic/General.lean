module

public import Phylogenetics.NMSC.DisplayedTreeModel

/-!
# General results that the library does not have yet

These results do not depend on the three papers, and belong in the library `Phylogenetics`, where they can
move as they are.

* `RootedNetwork.isWeakMetric_choiceNetworkMetric`, `RootedNetwork.nmscCF_choiceMetric_eq_third_of_nonneg`: taxa
  that a parent choice leaves unresolved have concordance factors `1/3` in the parameters of the choice, for all
  correlations. The library has the case `ρ = 1`, `RootedNetwork.nmscCF_choiceMetric_eq_third`.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics.RootedNetwork

section ChoiceMetric

open NMSC

variable {V E X : Type*} {N : RootedNetwork V E X}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {θ : MetricData E}

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- The network of a parent choice has weak parameters when its lengths are nonnegative. -/
theorem isWeakMetric_choiceNetworkMetric [Fintype E] {θ : MetricData E} (hN : N.IsPhylogenetic)
    (c : N.ParentChoice) (x₀ : X) (hℓ : ∀ f, N.IsKeptArc c f → 0 ≤ θ.length f) :
    (N.choiceNetwork hN c x₀).IsWeakMetric (N.choiceNetworkMetric θ c) := by
  have htree : ∀ f g : {f // N.IsKeptArc c f},
      (N.choiceNetwork hN c x₀).graph.target f = (N.choiceNetwork hN c x₀).graph.target g → f = g :=
    fun _ _ h => eq_of_target_choiceNetwork hN c x₀ h
  have hle : ∀ v, ¬ 2 ≤ (N.choiceNetwork hN c x₀).graph.indegree v := fun v h2 => by
    have : (N.choiceNetwork hN c x₀).graph.indegree v ≤ 1 :=
      (Set.ncard_le_one (Set.toFinite _)).2 fun a ha b hb => htree _ _ (ha.trans hb.symm)
    omega
  exact ⟨fun f => hℓ f.val f.property, fun _ _ => zero_le_one, fun _ _ => rfl,
    fun v hv => absurd hv (hle v)⟩

/-- **Taxa that a parent choice leaves unresolved have concordance factors `1/3` in the parameters of the
choice**, as a polytomy of the displayed tree gives no information, whatever the lengths, and for all `ρ`. -/
theorem nmscCF_choiceMetric_eq_third_of_nonneg {ρ : ℝ} (hN : N.IsPhylogenetic) (c : N.ParentChoice)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hℓ : ∀ f, 0 ≤ θ.length f) {q : Finset X} (hq : #q = 4)
    (hstar : ∀ r ∈ treesOn q, ¬ Displays (N.displayedSides c) r) {r : QuartetTree X}
    (hr : r ∈ treesOn q) : nmscCF N (N.choiceMetric θ c) ρ r = 1 / 3 := by
  obtain ⟨a, -⟩ : q.Nonempty := card_pos.1 (by omega)
  have hM := isPhylogenetic_choiceNetwork hN c a
  have hmem : ∀ (u : {v // N.IsKeptVertex c v}) (x : X),
      (N.choiceNetwork hN c a).graph.Reaches u ((N.choiceNetwork hN c a).leaf x) ↔
        x ∈ N.displayedCluster c u.val := fun u x =>
    ⟨fun h => mem_displayedCluster.2 (reachesOff_of_reaches_choiceNetwork hN c a h),
      fun h => reaches_choiceNetwork hN c a u.property (isKeptVertex_leaf c x)
        (mem_displayedCluster.1 h)⟩
  have hne : ∀ u : {v // N.IsKeptVertex c v},
      #(q.filter fun x => (N.choiceNetwork hN c a).graph.Reaches u
        ((N.choiceNetwork hN c a).leaf x)) ≠ 2 := by
    intro u h2
    have heq : (q.filter fun x => (N.choiceNetwork hN c a).graph.Reaches u
        ((N.choiceNetwork hN c a).leaf x)) = N.displayedCluster c u.val ∩ q := by
      ext x
      simp [hmem, and_comm]
    rw [heq] at h2
    have hAne : N.displayedCluster c u.val ≠ ∅ := by
      intro h
      rw [h, empty_inter] at h2
      simp at h2
    have hAu : N.displayedCluster c u.val ≠ univ := by
      intro h
      rw [h, univ_inter, hq] at h2
      norm_num at h2
    have hA : N.displayedCluster c u.val ∈ N.displayedSides c :=
      mem_unroot.2 (Or.inl ⟨mem_displayedClusters.2 ⟨hAne, _, rfl⟩, hAu⟩)
    exact hstar _ (mem_treesOn.2 (quartetOfCherry_taxa _ _ hq inter_subset_right h2))
      (displays_quartetOfCherry hA hq h2)
  have ht := hasTrivialFourBlob_of_tree hM (fun f g h => eq_of_target_choiceNetwork hN c a h) hq hne
  rw [← nmscCF_choiceNetwork hN c a hρ.1 θ r]
  exact trivial_uniform_weak hM (isWeakMetric_choiceNetworkMetric hN c a fun f _ => hℓ f) hρ hq ht hr

end ChoiceMetric

end Phylogenetics.RootedNetwork
