module

public import External.AllmanEtAl2023.Reduction
public import TOBQMC.WQC

/-!
# TOB-QMC Lemma 1: displayed quartet trees and 4-blobs

TOB-QMC (`notes/paper2025/v5.txt`, embedded lines 384-385): "A semi-directed, binary network on four taxa displays
exactly one binary quartet tree if, and only if, it does not contain a 4-blob." It cites Lemma 1 of its reference [5],
which is Ané, Fogg, Allman, Baños, Rhodes 2024 (J. Math. Biol. 88(3), 29): "A 4-taxon binary network N displays a
single quartet tree (i.e., is of class 1) if, and only if, it does not have a 4-blob."

The definition of that source (§2.1): "A (topological) tree T is displayed in a network N if it can be obtained from N
by deleting all but one parent hybrid edge from each hybrid node in N, and then deleting any edge and node not
contained in any up-down path between two leaves." The library's notion is `TOBQMC.NetworkDisplays`, of Definition 1
of TOB-QMC: a choice `c` of a parent at each reticulation (`IsDisplayDeletion`), with an arc kept by the choice having
exactly a cherry of the quartet tree below it. The proof works with the arcs `D` that a choice deletes, as
`External.AllmanEtAl2023.exists_reduction` does:

* `IsDisplayDeletion N D`: `D` leaves one parent at each vertex but the root. These are the complements of the
  `displayArcs` of the choices (`isDisplayDeletion_compl_displayArcs`, `IsDisplayDeletion.exists_choice`).
* `networkDisplays_iff`: the network displays `s` when some such `D` has an arc inducing the split of `s` off `D`.
* `displayTree N D`: the displayed tree itself, by the sides of its splits. It is an unrooted tree
  (`isUnrootedTree_displayTree`), binary if the network is (`isBinaryTree_displayTree`), and the quartet trees it
  displays are those of the choice (`IsDisplayDeletion.displays_displayTree_iff`).

The source's proof has two directions, and this file has its steps:

* No 4-blob: "N has a cut-edge separating two pairs of taxa, whose split is the only non-trivial split in its
  displayed trees" (`splitOffAt_of_subset`, `eq_of_splitOffAt`).
* A 4-blob: "Iteratively delete hybrid edges from N while it continues to have a 4-blob, until the resulting network
  has a lowest hybrid node h such that removing either parent edge of h leads to subnetworks without a 4-blob [...].
  Then one can show e1 and e2 correspond to incompatible splits [...]. As any tree displayed in N1 or N2 is also
  displayed in N, quartets with these splits are both displayed by N." This is
  `External.AllmanEtAl2023.exists_reduction` and `exists_isDisplayDeletion_superset`.

A displayed tree of a binary network never leaves a quartet unresolved (`existsUnique_inducesQuartet`), which is why
"binary quartet tree" is the right count. This uses that the network is binary: the star tree on four taxa displays no
binary quartet tree.

The statement is proved for four taxa `q` of a network on any number of taxa, as in `IsTreelike`;
`lemma1_of_card_eq_four` is the printed case of a network on four taxa.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork External.AllmanEtAl2023 Finset
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} {N : RootedNetwork V E X} {D : Set E}

/-- `D` is a choice of a displayed tree: it deletes hybrid arcs only and leaves exactly one parent at each vertex
other than the root. ("Deleting all but one parent hybrid edge from each hybrid node".) -/
structure IsDisplayDeletion (N : RootedNetwork V E X) (D : Set E) : Prop extends N.IsDeletion D where
  unique_parent : ∀ f g, f ∉ D → g ∉ D → N.graph.target f = N.graph.target g → f = g

/-- Any deletion extends to a choice of a displayed tree: "any tree displayed in `N₁` or `N₂` is also displayed in
`N`". -/
theorem exists_isDisplayDeletion_superset (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) :
    ∃ D', D ⊆ D' ∧ IsDisplayDeletion N D' := by
  have : Finite E := hN.finite_arcs
  choose p hpD hpt using fun v : {v // v ≠ N.root} => hD.parent v.1 v.2
  let t : E → {v // v ≠ N.root} := fun e => ⟨N.graph.target e, target_ne_root_of_isPhylogenetic hN e⟩
  have hpp : ∀ v, t (p v) = v := fun v => Subtype.ext (hpt v)
  refine ⟨{e | e ≠ p (t e)}, fun e he hc => hpD (t e) (by rw [← hc]; exact he), ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro e he
    have hne : e ≠ p (t e) := he
    exact Set.one_lt_ncard_iff (Set.toFinite _) |>.mpr ⟨e, p (t e), rfl, hpt (t e), hne⟩
  · intro v hv
    refine ⟨p ⟨v, hv⟩, ?_, hpt ⟨v, hv⟩⟩
    simp only [Set.mem_ofPred_eq, not_not, hpp]
  · intro f g hf hg hfg
    simp only [Set.mem_ofPred_eq, not_not] at hf hg
    rw [hf, hg]
    congr 1
    exact Subtype.ext hfg

/-- A network has displayed trees. -/
theorem exists_isDisplayDeletion (hN : N.IsPhylogenetic) : ∃ D, IsDisplayDeletion N D := by
  obtain ⟨D', -, h⟩ := exists_isDisplayDeletion_superset hN (isDeletion_empty hN)
  exact ⟨D', h⟩

/-- Off a choice of a displayed tree, the ancestors of a vertex form a chain. -/
theorem IsDisplayDeletion.reachesOff_or_reachesOff (hD : IsDisplayDeletion N D) {u v w : V}
    (hu : N.ReachesOff D u w) (hv : N.ReachesOff D v w) :
    N.ReachesOff D u v ∨ N.ReachesOff D v u := by
  induction hu with
  | refl => exact Or.inr hv
  | @tail b c hub hbc ih =>
    obtain ⟨f, hf, rfl, rfl⟩ := hbc
    rcases Relation.ReflTransGen.cases_tail hv with heq | ⟨b', hvb', ⟨g, hg, rfl, hgt⟩⟩
    · exact Or.inl (heq ▸ ReachesOff.tail_arc hub hf)
    · have hgf := hD.unique_parent g f hg hf hgt
      subst hgf
      exact ih hvb'

/-- Off a choice of a displayed tree, an arc dominates each taxon below it: the path from the root to the taxon is
unique. -/
theorem IsDisplayDeletion.dominatesOff (hN : N.IsPhylogenetic) (hD : IsDisplayDeletion N D) {e : E}
    (he : e ∉ D) {x : X} (hr : N.ReachesOff D (N.graph.target e) (N.leaf x)) : N.DominatesOff D e x :=
  dominatesOff_of_uniqueParents (q := {x}) hN (fun _ _ _ _ f g hf hg hfw hgw =>
    hD.unique_parent f g hf hg (hfw.trans hgw.symm)) he (hD.root_reachesOff hN _) (mem_singleton_self x) hr

/-- Deleting more arcs keeps a split. -/
theorem splitOffAt_of_subset [Fintype X] [DecidableEq X] {D' : Set E} (hDD : D ⊆ D') {e : E}
    {s : QuartetTree X} (hs : N.SplitOffAt D e s) : N.SplitOffAt D' e s := by
  obtain ⟨P, hP, hdom, hbel⟩ := hs
  refine ⟨P, hP, fun x hx hr => hdom x hx (hr.mono (Set.insert_subset_insert hDD)), ?_⟩
  rintro x hx ⟨he, hr⟩
  exact hbel x hx ⟨fun h => he (hDD h), hr.mono hDD⟩

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

section Displayed

variable [Fintype X] [DecidableEq X]

/-- The rooted tree displayed off `D`, by its clusters: the nonempty sets of taxa below a vertex. -/
def displayTreeClusters (N : RootedNetwork V E X) (D : Set E) : Finset (Finset X) :=
  univ.filter fun A => A.Nonempty ∧ ∃ v, A = taxaBelowOff N D univ v

/-- The unrooted tree displayed off `D`, by the sides of its splits. -/
def displayTree (N : RootedNetwork V E X) (D : Set E) : Finset (Finset X) :=
  unroot (displayTreeClusters N D)

omit [DecidableEq X] in
theorem mem_displayTreeClusters {A : Finset X} :
    A ∈ displayTreeClusters N D ↔ A.Nonempty ∧ ∃ v, A = taxaBelowOff N D univ v := by
  simp [displayTreeClusters]

omit [DecidableEq X] in
/-- The taxa below a higher vertex include those below a lower one. -/
theorem taxaBelowOff_subset_of_reachesOff {u v : V} (h : N.ReachesOff D u v) :
    taxaBelowOff N D univ v ⊆ taxaBelowOff N D univ u := fun x hx =>
  mem_taxaBelowOff.mpr ⟨mem_univ x, h.trans (mem_taxaBelowOff.mp hx).2⟩

omit [DecidableEq X] in
/-- The clusters of a displayed tree are laminar. -/
theorem IsDisplayDeletion.laminar (hD : IsDisplayDeletion N D) (u v : V) :
    taxaBelowOff N D univ u ⊆ taxaBelowOff N D univ v ∨
      taxaBelowOff N D univ v ⊆ taxaBelowOff N D univ u ∨
        Disjoint (taxaBelowOff N D univ u) (taxaBelowOff N D univ v) := by
  by_cases hdis : Disjoint (taxaBelowOff N D univ u) (taxaBelowOff N D univ v)
  · exact Or.inr (Or.inr hdis)
  · obtain ⟨x, hxu, hxv⟩ := not_disjoint_iff.mp hdis
    rcases hD.reachesOff_or_reachesOff (mem_taxaBelowOff.mp hxu).2 (mem_taxaBelowOff.mp hxv).2 with h | h
    · exact Or.inr (Or.inl (taxaBelowOff_subset_of_reachesOff h))
    · exact Or.inl (taxaBelowOff_subset_of_reachesOff h)

omit [DecidableEq X] in
/-- Below the root are all the taxa. -/
theorem taxaBelowOff_root (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) :
    taxaBelowOff N D (univ : Finset X) N.root = univ :=
  eq_univ_of_forall fun x => mem_taxaBelowOff.mpr ⟨mem_univ x, hD.root_reachesOff hN _⟩

omit [DecidableEq X] in
/-- Below a taxon is the taxon. -/
theorem taxaBelowOff_leaf (hN : N.IsPhylogenetic) (x : X) :
    taxaBelowOff N D (univ : Finset X) (N.leaf x) = {x} := by
  ext y
  simp only [mem_taxaBelowOff, mem_univ, true_and, mem_singleton]
  exact ⟨fun h => eq_of_leaf_reachesOff_leaf hN h, fun h => h ▸ .refl⟩

omit [DecidableEq X] in
/-- A displayed tree is a rooted tree on the taxa. -/
theorem isHierarchy_displayTreeClusters [Nonempty X] (hN : N.IsPhylogenetic) (hD : IsDisplayDeletion N D) :
    IsHierarchy (displayTreeClusters N D) := by
  refine ⟨?_, fun x => ?_, fun A hA => (mem_displayTreeClusters.mp hA).1, fun A hA B hB => ?_⟩
  · exact mem_displayTreeClusters.mpr ⟨univ_nonempty, N.root, (taxaBelowOff_root hN hD.toIsDeletion).symm⟩
  · exact mem_displayTreeClusters.mpr ⟨singleton_nonempty x, N.leaf x, (taxaBelowOff_leaf hN x).symm⟩
  · obtain ⟨-, u, rfl⟩ := mem_displayTreeClusters.mp hA
    obtain ⟨-, v, rfl⟩ := mem_displayTreeClusters.mp hB
    exact hD.laminar u v

/-- A displayed tree is an unrooted tree on the taxa. -/
theorem isUnrootedTree_displayTree [Nonempty X] (hN : N.IsPhylogenetic) (hD : IsDisplayDeletion N D) :
    IsUnrootedTree (displayTree N D) :=
  ⟨_, isHierarchy_displayTreeClusters hN hD, rfl⟩

/-- A cluster with two disjoint subclusters covering it has these as its children. -/
theorem childClusters_eq_pair_of_isHierarchy {H : Finset (Finset X)} (hH : IsHierarchy H)
    {B₁ B₂ : Finset X} (h₁ : B₁ ∈ H) (h₂ : B₂ ∈ H) (hdis : Disjoint B₁ B₂) :
    childClusters H (B₁ ∪ B₂) = {B₁, B₂} := by
  obtain ⟨-, -, hne, hlam⟩ := hH
  have hne₁ := hne _ h₁
  have hne₂ := hne _ h₂
  obtain ⟨a₁, ha₁⟩ := hne₁
  obtain ⟨a₂, ha₂⟩ := hne₂
  have ha₁₂ : a₁ ∉ B₂ := disjoint_left.mp hdis ha₁
  have ha₂₁ : a₂ ∉ B₁ := disjoint_right.mp hdis ha₂
  -- a cluster strictly inside the union and strictly above `B₁` cannot exist, nor can one above `B₂`
  have hgap₁ : ∀ C ∈ H, B₁ ⊂ C → C ⊂ B₁ ∪ B₂ → False := by
    intro C hC hlt hgt
    obtain ⟨z, hzC, hzB₁⟩ := Finset.exists_of_ssubset hlt
    have hzB₂ : z ∈ B₂ := (mem_union.mp (hgt.subset hzC)).resolve_left hzB₁
    rcases hlam C hC B₂ h₂ with h | h | h
    · exact ha₁₂ (h (hlt.subset ha₁))
    · exact hgt.2 (union_subset hlt.subset h)
    · exact disjoint_left.mp h hzC hzB₂
  have hgap₂ : ∀ C ∈ H, B₂ ⊂ C → C ⊂ B₁ ∪ B₂ → False := by
    intro C hC hlt hgt
    obtain ⟨z, hzC, hzB₂⟩ := Finset.exists_of_ssubset hlt
    have hzB₁ : z ∈ B₁ := (mem_union.mp (hgt.subset hzC)).resolve_right hzB₂
    rcases hlam C hC B₁ h₁ with h | h | h
    · exact ha₂₁ (h (hlt.subset ha₂))
    · exact hgt.2 (union_subset h hlt.subset)
    · exact disjoint_left.mp h hzC hzB₁
  have hlt₁ : B₁ ⊂ B₁ ∪ B₂ :=
    ⟨subset_union_left, fun h => ha₂₁ (h (mem_union_right _ ha₂))⟩
  have hlt₂ : B₂ ⊂ B₁ ∪ B₂ :=
    ⟨subset_union_right, fun h => ha₁₂ (h (mem_union_left _ ha₁))⟩
  ext C
  simp only [childClusters, mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hC, hCA, hmax⟩
    obtain ⟨z, hz⟩ := hne _ hC
    rcases mem_union.mp (hCA.subset hz) with hzi | hzi
    · left
      rcases hlam C hC B₁ h₁ with h | h | h
      · exact (eq_or_ssubset_of_subset h).resolve_right fun hlt => hmax B₁ h₁ hlt hlt₁
      · exact ((eq_or_ssubset_of_subset h).resolve_right fun hlt => hgap₁ C hC hlt hCA).symm
      · exact absurd hzi (disjoint_left.mp h hz)
    · right
      rcases hlam C hC B₂ h₂ with h | h | h
      · exact (eq_or_ssubset_of_subset h).resolve_right fun hlt => hmax B₂ h₂ hlt hlt₂
      · exact ((eq_or_ssubset_of_subset h).resolve_right fun hlt => hgap₂ C hC hlt hCA).symm
      · exact absurd hzi (disjoint_left.mp h hz)
  · rintro (rfl | rfl)
    · exact ⟨h₁, hlt₁, fun C hC hlt hgt => hgap₁ C hC hlt hgt⟩
    · exact ⟨h₂, hlt₂, fun C hC hlt hgt => hgap₂ C hC hlt hgt⟩

omit [Fintype X] [DecidableEq X] in
/-- A vertex of a binary network has at most two children. -/
theorem outdegree_le_two (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (v : V) :
    N.graph.outdegree v ≤ 2 := by
  by_cases hv : v = N.root
  · subst hv
    exact hBin.1.le
  · have h₁ := hN.nonroot_indegree v hv
    have h₂ := degree_le_three_of_isBinary hN hBin v
    omega

/-- **A displayed tree of a binary network is binary.** A cluster with at least two taxa is that of a lowest vertex
with these taxa below it; this vertex has two children with taxa below them, and at most two children. -/
theorem isBinaryTree_displayTree [Nonempty X] (hN : N.IsPhylogenetic) (hBin : N.IsBinary)
    (hD : IsDisplayDeletion N D) : IsBinaryTree (displayTree N D) := by
  have hH := isHierarchy_displayTreeClusters hN hD
  refine ⟨_, hH, rfl, fun A hA h2 => ?_⟩
  obtain ⟨-, v₀, rfl⟩ := mem_displayTreeClusters.mp hA
  obtain ⟨v, hv, hlow⟩ := exists_lowest hN
    (S := {v | taxaBelowOff N D univ v = taxaBelowOff N D univ v₀}) ⟨v₀, rfl⟩
  rw [Set.mem_ofPred_eq] at hv
  rw [← hv] at h2 ⊢
  have hcyc : ∀ f, N.graph.source f = v → N.ReachesOff D (N.graph.target f) v → False := by
    rintro f rfl hr
    exact not_reaches_target_source hN.acyclic f (ReachesOff.reaches hr)
  -- each taxon below `v` is below a child of `v`
  have hfirst : ∀ x ∈ taxaBelowOff N D (univ : Finset X) v, ∃ f, f ∉ D ∧ N.graph.source f = v ∧
      x ∈ taxaBelowOff N D (univ : Finset X) (N.graph.target f) := by
    intro x hx
    have hne : v ≠ N.leaf x := by
      rintro rfl
      rw [taxaBelowOff_leaf hN x, card_singleton] at h2
      omega
    obtain ⟨f, hf, hfs, hr⟩ := (mem_taxaBelowOff.mp hx).2.exists_first hne
    exact ⟨f, hf, hfs, mem_taxaBelowOff.mpr ⟨mem_univ x, hr⟩⟩
  -- each child of `v` has fewer taxa below it
  have hlt : ∀ f, f ∉ D → N.graph.source f = v →
      taxaBelowOff N D (univ : Finset X) (N.graph.target f) ⊂ taxaBelowOff N D univ v := by
    intro f hf hfs
    have hsub := taxaBelowOff_subset_of_reachesOff (X := X) (hfs ▸ Relation.ReflTransGen.single ⟨f, hf, rfl, rfl⟩ :
      N.ReachesOff D v (N.graph.target f))
    refine ⟨hsub, fun hsup => ?_⟩
    have heq : N.graph.target f = v := hlow _
      (show taxaBelowOff N D univ (N.graph.target f) = taxaBelowOff N D univ v₀ from
        (subset_antisymm hsub hsup).trans hv)
      (.single ⟨f, hfs, rfl⟩)
    exact hcyc f hfs (heq ▸ .refl)
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < (taxaBelowOff N D (univ : Finset X) v).card)
  obtain ⟨f, hf, hfs, hxf⟩ := hfirst x hx
  obtain ⟨z, hzv, hzf⟩ := Finset.exists_of_ssubset (hlt f hf hfs)
  obtain ⟨g, hg, hgs, hzg⟩ := hfirst z hzv
  have hfg : f ≠ g := by
    rintro rfl
    exact hzf hzg
  -- two children have no common taxon: the parent of each child is the arc from `v`
  have hdis : Disjoint (taxaBelowOff N D (univ : Finset X) (N.graph.target f))
      (taxaBelowOff N D univ (N.graph.target g)) := by
    have hord : ∀ {a b : E}, a ∉ D → b ∉ D → N.graph.source a = v → N.graph.source b = v → a ≠ b →
        ¬ N.ReachesOff D (N.graph.target a) (N.graph.target b) := by
      intro a b ha hb hsa hsb hab hr
      rcases Relation.ReflTransGen.cases_tail hr with heq | ⟨c, hc, ⟨h, hh, rfl, hht⟩⟩
      · exact hab (hD.unique_parent a b ha hb heq.symm)
      · have hhb := hD.unique_parent h b hh hb hht
        subst hhb
        exact hcyc a hsa (hsb ▸ hc)
    rw [disjoint_iff_ne]
    rintro w hw _ hw' rfl
    rcases hD.reachesOff_or_reachesOff (mem_taxaBelowOff.mp hw).2 (mem_taxaBelowOff.mp hw').2 with h | h
    · exact hord hf hg hfs hgs hfg h
    · exact hord hg hf hgs hfs hfg.symm h
  -- and there are no other children
  have hun : taxaBelowOff N D (univ : Finset X) v =
      taxaBelowOff N D univ (N.graph.target f) ∪ taxaBelowOff N D univ (N.graph.target g) := by
    refine subset_antisymm (fun w hw => ?_) (union_subset (hlt f hf hfs).subset (hlt g hg hgs).subset)
    obtain ⟨h, hh, hhs, hwh⟩ := hfirst w hw
    by_cases hhf : h = f
    · exact mem_union_left _ (hhf ▸ hwh)
    · by_cases hhg : h = g
      · exact mem_union_right _ (hhg ▸ hwh)
      · exfalso
        have : Finite E := hN.finite_arcs
        have hsub : ({f, g, h} : Set E) ⊆ {e | N.graph.source e = v} := by
          rintro e (rfl | rfl | rfl)
          · exact hfs
          · exact hgs
          · exact hhs
        have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
        have h3 : ({f, g, h} : Set E).ncard = 3 := by
          rw [Set.ncard_eq_three]
          exact ⟨f, g, h, hfg, fun e => hhf e.symm, fun e => hhg e.symm, rfl⟩
        have := outdegree_le_two hN hBin v
        simp only [DirectedMultigraph.outdegree] at this
        omega
  have hmem : ∀ e : E, e ∉ D → N.graph.source e = v → (taxaBelowOff N D (univ : Finset X) (N.graph.target e)).Nonempty →
      taxaBelowOff N D (univ : Finset X) (N.graph.target e) ∈ displayTreeClusters N D :=
    fun e _ _ hne => mem_displayTreeClusters.mpr ⟨hne, _, rfl⟩
  have hf' := hmem f hf hfs ⟨x, hxf⟩
  have hg' := hmem g hg hgs ⟨z, hzg⟩
  rw [hun, childClusters_eq_pair_of_isHierarchy hH hf' hg' hdis, card_pair]
  intro hc
  exact disjoint_left.mp hdis hxf (hc ▸ hxf)

/-- A cluster that restricts to a cherry gives the split of the arc entering its vertex. -/
theorem IsDisplayDeletion.splitOffAt_of_inter_eq (hN : N.IsPhylogenetic) (hD : IsDisplayDeletion N D)
    {s : QuartetTree X} {v : V} {P : Finset X} (hP : P ∈ s.val)
    (hv : taxaBelowOff N D univ v ∩ s.taxa = P) : ∃ e, N.SplitOffAt D e s := by
  have hne : v ≠ N.root := by
    rintro rfl
    rw [taxaBelowOff_root hN hD.toIsDeletion, univ_inter] at hv
    have h2 := s.card_of_mem hP
    rw [← hv, s.card_taxa] at h2
    omega
  obtain ⟨e, he, rfl⟩ := hD.parent v hne
  refine ⟨e, P, hP, fun x hx => ?_, fun x hx hb => ?_⟩
  · have hx' : x ∈ taxaBelowOff N D univ (N.graph.target e) ∩ s.taxa := hv ▸ mem_coe.mp hx
    exact hD.dominatesOff hN he (mem_taxaBelowOff.mp (mem_inter.mp hx').1).2
  · have hxs := mem_sdiff.mp (mem_coe.mp hx)
    exact hxs.2 (hv ▸ mem_inter.mpr ⟨mem_taxaBelowOff.mpr ⟨mem_univ x, hb.2⟩, hxs.1⟩)

/-- **The quartet tree a displayed tree induces**: in the sense `Displays`, it is one with an arc of the displayed
tree inducing its split. -/
theorem IsDisplayDeletion.displays_displayTree_iff (hN : N.IsPhylogenetic) (hD : IsDisplayDeletion N D)
    {s : QuartetTree X} : Displays (displayTree N D) s ↔ ∃ e, N.SplitOffAt D e s := by
  constructor
  · rintro ⟨A, hA, hAs⟩
    simp only [displayTree, unroot, mem_union, mem_erase, mem_image] at hA
    rcases hA with ⟨-, hA⟩ | ⟨C, ⟨-, hC⟩, rfl⟩
    · obtain ⟨-, v, rfl⟩ := mem_displayTreeClusters.mp hA
      exact hD.splitOffAt_of_inter_eq hN hAs rfl
    · obtain ⟨-, v, rfl⟩ := mem_displayTreeClusters.mp hC
      refine hD.splitOffAt_of_inter_eq hN (v := v) (s.sdiff_mem hAs) ?_
      ext y
      simp only [mem_inter, mem_sdiff, mem_compl]
      tauto
  · rintro ⟨e, P, hP, hdom, hbel⟩
    have hPne : P.Nonempty := card_pos.mp (by rw [s.card_of_mem hP]; norm_num)
    have hQne : (s.taxa \ P).Nonempty := card_pos.mp (by rw [s.card_of_mem (s.sdiff_mem hP)]; norm_num)
    obtain ⟨a, ha⟩ := hPne
    obtain ⟨b, hb⟩ := hQne
    have hae := ((hdom a ha).isBelowOff hN hD.toIsDeletion).1
    have hPsub : ∀ x ∈ P, x ∈ taxaBelowOff N D univ (N.graph.target e) := fun x hx =>
      mem_taxaBelowOff.mpr ⟨mem_univ x, ((hdom x hx).isBelowOff hN hD.toIsDeletion).2⟩
    refine ⟨taxaBelowOff N D univ (N.graph.target e), ?_, ?_⟩
    · simp only [displayTree, unroot, mem_union, mem_erase]
      refine Or.inl ⟨?_, mem_displayTreeClusters.mpr ⟨⟨a, hPsub a ha⟩, _, rfl⟩⟩
      intro hu
      exact hbel b hb ⟨hae, (mem_taxaBelowOff.mp (hu ▸ mem_univ b)).2⟩
    · have heq : taxaBelowOff N D univ (N.graph.target e) ∩ s.taxa = P := by
        ext x
        simp only [mem_inter]
        constructor
        · rintro ⟨hx, hxs⟩
          by_contra hxP
          exact hbel x (mem_coe.mpr (mem_sdiff.mpr ⟨hxs, hxP⟩)) ⟨hae, (mem_taxaBelowOff.mp hx).2⟩
        · exact fun hx => ⟨hPsub x hx, s.subset_taxa hP hx⟩
      rw [heq]
      exact hP

omit [Fintype X] [DecidableEq X] in
/-- The arcs a choice of the library deletes leave one parent at each vertex. -/
theorem isDisplayDeletion_compl_displayArcs (hN : N.IsPhylogenetic) {c : V → E} (hc : IsDisplayChoice N c) :
    IsDisplayDeletion N (displayArcs N c)ᶜ := by
  have : Finite E := hN.finite_arcs
  have hkeep : ∀ v, 2 ≤ N.graph.indegree v → c v ∈ displayArcs N c := fun v hv =>
    Or.inr (by rw [hc v hv])
  refine ⟨⟨fun e he => ?_, fun v hv => ?_⟩, fun f g hf hg hfg => ?_⟩
  · have hne : 0 < N.graph.indegree (N.graph.target e) :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨e, rfl⟩
    have hnt : ¬ N.IsTreeArc e := fun h => he (Or.inl h)
    simp only [IsTreeArc] at hnt
    simp only [IsHybridArc]
    omega
  · by_cases h2 : 2 ≤ N.graph.indegree v
    · exact ⟨c v, not_not.mpr (hkeep v h2), hc v h2⟩
    · obtain ⟨f, hf⟩ := (N.graph.one_le_indegree_iff v).mp (hN.nonroot_indegree v hv)
      have h1 := hN.nonroot_indegree v hv
      refine ⟨f, not_not.mpr (Or.inl ?_), hf⟩
      simp only [IsTreeArc, hf]
      omega
  · rw [Set.mem_compl_iff, not_not] at hf hg
    by_cases h1 : N.graph.indegree (N.graph.target f) = 1
    · obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
      have hfa : f ∈ ({a} : Set E) := ha ▸ rfl
      have hga : g ∈ ({a} : Set E) := ha ▸ hfg.symm
      exact hfa.trans hga.symm
    · have hf' : f = c (N.graph.target f) := hf.resolve_left h1
      have hg' : g = c (N.graph.target g) :=
        hg.resolve_left fun h => h1 (by simpa only [IsTreeArc, hfg] using h)
      rw [hf', hg', hfg]

omit [Fintype X] [DecidableEq X] in
/-- The library's reachability along the arcs of a choice is reachability off the arcs it deletes. -/
theorem belowInDisplay_iff {c : V → E} {u : V} {x : X} :
    BelowInDisplay N c u x ↔ N.ReachesOff (displayArcs N c)ᶜ u (N.leaf x) := by
  have h : (fun a b => ∃ f ∈ displayArcs N c, N.graph.source f = a ∧ N.graph.target f = b) =
      fun a b => ∃ f, f ∉ (displayArcs N c)ᶜ ∧ N.graph.source f = a ∧ N.graph.target f = b := by
    funext a b
    simp only [Set.mem_compl_iff, not_not]
  simp only [BelowInDisplay, ReachesOff, h]

omit [Fintype X] [DecidableEq X] in
/-- A set of arcs leaving one parent at each vertex is what a choice of the library deletes. -/
theorem IsDisplayDeletion.exists_choice (hN : N.IsPhylogenetic) (hD : IsDisplayDeletion N D) (e₀ : E) :
    ∃ c, IsDisplayChoice N c ∧ displayArcs N c = Dᶜ := by
  have : Finite E := hN.finite_arcs
  have hp : ∀ v : V, ∃ f : E, v ≠ N.root → f ∉ D ∧ N.graph.target f = v := by
    intro v
    by_cases hv : v = N.root
    · exact ⟨e₀, fun h => absurd hv h⟩
    · obtain ⟨f, hf, hft⟩ := hD.parent v hv
      exact ⟨f, fun _ => ⟨hf, hft⟩⟩
  choose c hc using hp
  refine ⟨c, fun v hv => (hc v ?_).2, ?_⟩
  · rintro rfl
    rw [hN.root_indegree] at hv
    omega
  · ext e
    have hte := target_ne_root_of_isPhylogenetic hN e
    simp only [displayArcs, Set.mem_ofPred_eq, Set.mem_compl_iff]
    constructor
    · rintro (h | h) he
      · have := hD.hybrid e he
        simp only [IsTreeArc] at h
        simp only [IsHybridArc] at this
        omega
      · exact (hc _ hte).1 (h ▸ he)
    · intro he
      exact Or.inr (hD.unique_parent e _ he (hc _ hte).1 (hc _ hte).2.symm)

/-- The display tree of the choice `c` induces the quartet tree `s`: some arc kept by `c` has exactly a cherry of `s`
below it, among the taxa of `s`. `NetworkDisplays` asks for a choice with this property. -/
def InducesQuartet (N : RootedNetwork V E X) (c : V → E) (s : QuartetTree X) : Prop :=
  ∃ e ∈ displayArcs N c, (s.taxa.filter fun x => BelowInDisplay N c (N.graph.target e) x) ∈ s.val

omit [Fintype X] in
/-- Inducing a quartet tree is having an arc that induces its split, off the arcs deleted. -/
theorem inducesQuartet_iff (hN : N.IsPhylogenetic) {c : V → E} (hc : IsDisplayChoice N c) {s : QuartetTree X} :
    InducesQuartet N c s ↔ ∃ e, N.SplitOffAt (displayArcs N c)ᶜ e s := by
  have hD := isDisplayDeletion_compl_displayArcs hN hc
  constructor
  · rintro ⟨e, he, hP⟩
    have he' : e ∉ (displayArcs N c)ᶜ := not_not.mpr he
    refine ⟨e, _, hP, fun x hx => ?_, fun x hx hb => ?_⟩
    · exact hD.dominatesOff hN he' (belowInDisplay_iff.mp (mem_filter.mp (mem_coe.mp hx)).2)
    · have hxs := mem_sdiff.mp (mem_coe.mp hx)
      exact hxs.2 (mem_filter.mpr ⟨hxs.1, belowInDisplay_iff.mpr hb.2⟩)
  · rintro ⟨e, P, hP, hdom, hbel⟩
    obtain ⟨a, ha⟩ : P.Nonempty := card_pos.mp (by rw [s.card_of_mem hP]; norm_num)
    have he := ((hdom a ha).isBelowOff hN hD.toIsDeletion).1
    refine ⟨e, not_not.mp he, ?_⟩
    have heq : (s.taxa.filter fun x => BelowInDisplay N c (N.graph.target e) x) = P := by
      ext x
      simp only [mem_filter]
      constructor
      · rintro ⟨hxs, hb⟩
        by_contra hxP
        exact hbel x (mem_coe.mpr (mem_sdiff.mpr ⟨hxs, hxP⟩)) ⟨he, belowInDisplay_iff.mp hb⟩
      · exact fun hx => ⟨s.subset_taxa hP hx,
          belowInDisplay_iff.mpr ((hdom x hx).isBelowOff hN hD.toIsDeletion).2⟩
    rw [heq]
    exact hP

omit [Fintype X] in
/-- `NetworkDisplays` off the arcs deleted. -/
theorem networkDisplays_iff (hN : N.IsPhylogenetic) {s : QuartetTree X} :
    NetworkDisplays N s ↔ ∃ D, IsDisplayDeletion N D ∧ ∃ e, N.SplitOffAt D e s := by
  constructor
  · rintro ⟨c, hc, hi⟩
    exact ⟨_, isDisplayDeletion_compl_displayArcs hN hc, (inducesQuartet_iff hN hc).mp hi⟩
  · rintro ⟨D, hD, e, hse⟩
    obtain ⟨c, hc, hcD⟩ := hD.exists_choice hN e
    refine ⟨c, hc, (inducesQuartet_iff hN hc).mpr ⟨e, ?_⟩⟩
    rw [hcD, compl_compl]
    exact hse

/-- Off a choice of a displayed tree of a binary network, four taxa have exactly one quartet tree. The tree off `D`
has a `2|2` arc, or a vertex of degree at least four, which a binary network lacks (`isTreelikeOff_or_starOff`). -/
theorem IsDisplayDeletion.existsUnique_splitOffAt (hN : N.IsPhylogenetic) (hBin : N.IsBinary)
    (hD : IsDisplayDeletion N D) {q : Finset X} (hq : q.card = 4) :
    ∃! s, s ∈ treesOn q ∧ ∃ e, N.SplitOffAt D e s := by
  have hroot : taxaBelowOff N D q N.root = q := by
    ext x
    simp only [mem_taxaBelowOff, and_iff_left_iff_imp]
    exact fun _ => hD.root_reachesOff hN _
  have hT : HasUniqueParentsBelow N D q N.root := fun _ _ _ _ f g hf hg hfw hgw =>
    hD.unique_parent f g hf hg (hfw.trans hgw.symm)
  rcases isTreelikeOff_or_starOff hN hD.toIsDeletion hq hT (by rw [hroot]; omega)
    (by rw [hroot]; omega) with ⟨s, hs, e, hse⟩ | ⟨w, hw⟩
  · refine ⟨s, ⟨hs, e, hse⟩, ?_⟩
    rintro r ⟨hr, e', hr'⟩
    exact eq_of_splitOffAt hN hD.toIsDeletion ((mem_treesOn.mp hr).trans (mem_treesOn.mp hs).symm) hr' hse
  · have h₁ := hw.four_le_degree hN hq
    have h₂ := degree_le_three_of_isBinary hN hBin w
    omega

/-- **A display tree of a binary network induces exactly one binary quartet tree** on any four taxa: it never leaves
them unresolved. -/
theorem existsUnique_inducesQuartet (hN : N.IsPhylogenetic) (hBin : N.IsBinary) {c : V → E} (hc : IsDisplayChoice N c)
    {q : Finset X} (hq : q.card = 4) : ∃! s, s ∈ treesOn q ∧ InducesQuartet N c s := by
  simpa only [inducesQuartet_iff hN hc] using
    (isDisplayDeletion_compl_displayArcs hN hc).existsUnique_splitOffAt hN hBin hq

/-- With no 4-blob, "a cut-edge separating two pairs of taxa, whose split is the only non-trivial split in its
displayed trees": all display trees induce the quartet tree of that split. -/
theorem exists_forall_inducesQuartet (hN : N.IsPhylogenetic) {q : Finset X} (htl : IsTreelike N q) :
    ∃ s ∈ treesOn q, ∀ c, IsDisplayChoice N c → InducesQuartet N c s := by
  obtain ⟨s, hs, e, hse⟩ := (isTreelikeOff_empty_iff hN).mpr htl
  exact ⟨s, hs, fun c hc => (inducesQuartet_iff hN hc).mpr ⟨e, splitOffAt_of_subset (Set.empty_subset _) hse⟩⟩

/-- **Lemma 1** (`tob2025:lemma1`). A binary network displays exactly one binary quartet tree on four taxa if, and
only if, it does not contain a 4-blob on them, which is `IsTreelike`.

The proof is the one of its source, Lemma 1 of Ané et al. 2024: a cut edge separating two pairs of taxa gives "the
only non-trivial split in its displayed trees", and from a 4-blob, the reduction of Allman et al. 2023
(`exists_reduction`) gives two subnetworks with incompatible splits, whose displayed trees are displayed by the
network.

Departure from the paper: the source gets the cut edge from "it has two 3-blobs", by Lemma 1 of Allman et al. 2023,
which is not formalized (`External/AllmanEtAl2023/Reduction.lean`). A cut edge with a `2|2` split is what `IsTreelike`
says, so this step is not needed. -/
theorem lemma1 (hN : N.IsPhylogenetic) (hBin : N.IsBinary) {q : Finset X} (hq : q.card = 4) :
    (∃! s, s ∈ treesOn q ∧ NetworkDisplays N s) ↔ IsTreelike N q := by
  constructor
  · rintro ⟨s, -, huniq⟩
    by_contra hnt
    obtain ⟨D, k₁, k₂, -, s₁, s₂, e₁, e₂, hD, hk, ht, hk₁, hk₂, -, -, -, -, hs₁, hs₂, hss, hsp₁, hsp₂⟩ :=
      exists_reduction hN hBin hq hnt
    obtain ⟨D₁, hD₁, hc₁⟩ := exists_isDisplayDeletion_superset hN (hD.insert hN hk.symm ht.symm hk₁)
    obtain ⟨D₂, hD₂, hc₂⟩ := exists_isDisplayDeletion_superset hN (hD.insert hN hk ht hk₂)
    have hm₁ : s₁ ∈ treesOn q ∧ NetworkDisplays N s₁ :=
      ⟨hs₁, (networkDisplays_iff hN).mpr ⟨D₁, hc₁, e₁, splitOffAt_of_subset hD₁ hsp₁⟩⟩
    have hm₂ : s₂ ∈ treesOn q ∧ NetworkDisplays N s₂ :=
      ⟨hs₂, (networkDisplays_iff hN).mpr ⟨D₂, hc₂, e₂, splitOffAt_of_subset hD₂ hsp₂⟩⟩
    exact hss ((huniq s₁ hm₁).trans (huniq s₂ hm₂).symm)
  · intro htl
    obtain ⟨s, hs, e, hse⟩ := (isTreelikeOff_empty_iff hN).mpr htl
    obtain ⟨D₀, hD₀⟩ := exists_isDisplayDeletion hN
    refine ⟨s, ⟨hs, (networkDisplays_iff hN).mpr
      ⟨D₀, hD₀, e, splitOffAt_of_subset (Set.empty_subset _) hse⟩⟩, ?_⟩
    rintro r ⟨hr, hrd⟩
    obtain ⟨D, hD, e', hr'⟩ := (networkDisplays_iff hN).mp hrd
    exact eq_of_splitOffAt hN hD.toIsDeletion ((mem_treesOn.mp hr).trans (mem_treesOn.mp hs).symm) hr'
      (splitOffAt_of_subset (Set.empty_subset _) hse)

/-- **Lemma 1** (`tob2025:lemma1`) as printed, for a network on four taxa: it displays exactly one binary quartet tree
if, and only if, it does not contain a 4-blob. -/
theorem lemma1_of_card_eq_four (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hX : Fintype.card X = 4) :
    (∃! s : QuartetTree X, NetworkDisplays N s) ↔ IsTreelike N (univ : Finset X) := by
  rw [← lemma1 hN hBin (q := univ) (by rw [card_univ, hX])]
  have hu : ∀ s : QuartetTree X, s ∈ treesOn (univ : Finset X) := fun s => mem_treesOn.mpr
    (eq_of_subset_of_card_le (subset_univ _) (by rw [card_univ, hX, s.card_taxa]))
  simp only [hu, true_and]

end Displayed

end TOBQMC
