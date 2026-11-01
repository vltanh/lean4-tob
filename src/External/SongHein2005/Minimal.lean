module

public import External.SongHein2005.Bound
public import External.MyersGriffiths2003.Composite

/-!
# The minimum of `L(P)` is `R¹`: the other inequality of Song and Hein

Song and Hein 2005, equations (3), (5): `min_P L(P) = R_min(S)`. `SongHein2005.R_le_sprLength` is `R¹(M) ≤ L(P)`. This module has the other inequality, so that the minimum is attained and equal to `R¹(M)` (`exists_sprLength_eq_R`, `R_eq_iInf_sprLength`).

The source's argument is in words: "to each ARG corresponding to a set of length-`ℓ` DNA sequences, one can associate a unique length-`ℓ` sequence `P` of trees such that the `i`th tree in `P` describes the evolution of the `i`th character site", and "if ordered trees are used, however, we always have `d_SPR(T, T') = d_rec(T, T')`". It's made precise as follows.

* A **sampling** of a network keeps one arc into each recombination node (`IsSampling`). The kept arcs are a tree on all the nodes, and its clusters are the rows below each node (`below`), with the time of a cluster that of the last node having it as its rows (`sampledTree`). The time of a node is any rank along the arcs.
* The tree of a site is the sampling that follows the crossovers at that site. It's compatible with the column of the site: the rows below the arc of the site are those off the root's state (`keptReach_iff_label_ne`).
* **Changing the kept arc at one recombination node is one ordered-SPR operation** (`same_or_isOrderedSPR`): the subtree below that node is pruned and regrafted, and nothing else moves. Or it's no change at all, if there's no row below the node, or if all rows are.
* Going from site `i` to site `i + 1` changes the kept arc at the nodes with their crossover there, so `L(P)` is at most the number of recombination nodes.

The trees here aren't binary, and their internal nodes can tie. The same statement for binary trees with a total order, the source's class, is `SongHein2005.exists_orderedLength_eq_R` in `External.SongHein2005.BinaryPaths`.
-/

@[expose] public noncomputable section

open scoped Classical

namespace SongHein2005

open Gusfield2007

/-! ### Samplings -/

section Sampling

variable {ι V E : Type*}

/-- A sampling of a network: the arcs kept, all those into a node with one arc in, and exactly one of the two into a recombination node. -/
structure IsSampling (N : Network ι V E) (keep : E → Prop) : Prop where
  tree : ∀ e, (∀ f, N.tgt f = N.tgt e → f = e) → keep e
  one : ∀ e f, e ≠ f → N.tgt e = N.tgt f → (keep e ↔ ¬ keep f)

/-- A path along the kept arcs. -/
def KeptReach (N : Network ι V E) (keep : E → Prop) (a b : V) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ g, keep g ∧ N.src g = a ∧ N.tgt g = b) a b

variable {N : Network ι V E} {keep keep' : E → Prop}

theorem KeptReach.reach {a b : V} (h : KeptReach N keep a b) : N.Reach a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨g, -, h₁, h₂⟩ := hs
    exact ih.tail ⟨g, h₁, h₂⟩

theorem IsSampling.exists_kept (hk : IsSampling N keep) {v : V} (hv : v ≠ N.root) : ∃ g, keep g ∧ N.tgt g = v := by
  obtain ⟨e, rfl⟩ : ∃ e, N.tgt e = v := by
    by_contra hno
    push Not at hno
    exact hv ((N.root_iff v).1 hno)
  by_cases htree : ∀ f, N.tgt f = N.tgt e → f = e
  · exact ⟨e, hk.tree e htree, rfl⟩
  · push Not at htree
    obtain ⟨f, hf, hne⟩ := htree
    by_cases he : keep e
    · exact ⟨e, he, rfl⟩
    · exact ⟨f, by_contra fun hc => he ((hk.one e f hne.symm hf.symm).2 hc), hf⟩

theorem IsSampling.unique (hk : IsSampling N keep) {g g' : E} (hg : keep g) (hg' : keep g') (ht : N.tgt g = N.tgt g') : g = g' := by
  by_contra hne
  exact (hk.one g g' hne ht).1 hg hg'

theorem keptReach_root [Finite V] (hk : IsSampling N keep) (v : V) : KeptReach N keep N.root v := by
  induction v using N.arc_induction with
  | _ v ih =>
    by_cases hv : v = N.root
    · rw [hv]
      exact Relation.ReflTransGen.refl
    · obtain ⟨g, hg, rfl⟩ := hk.exists_kept hv
      exact (ih g rfl).tail ⟨g, hg, rfl, rfl⟩

/-- The nodes above a node in the tree of a sampling are in a chain. -/
theorem keptReach_total (hk : IsSampling N keep) {a b c : V} (h₁ : KeptReach N keep a c) (h₂ : KeptReach N keep b c) : KeptReach N keep a b ∨ KeptReach N keep b a := by
  induction h₁ generalizing b with
  | refl => exact Or.inr h₂
  | @tail c' c hac hstep ih =>
    obtain ⟨g, hg, h₃, h₄⟩ := hstep
    rcases Relation.ReflTransGen.cases_tail h₂ with rfl | ⟨c'', hb, g', hg', h₅, h₆⟩
    · exact Or.inl (hac.tail ⟨g, hg, h₃, h₄⟩)
    · obtain rfl := hk.unique hg hg' (h₄.trans h₆.symm)
      exact ih (h₃ ▸ h₅ ▸ hb)

/-- A rank along the arcs goes up along the kept arcs. -/
theorem KeptReach.rank_le {t : V → ℕ} (ht : ∀ e, t (N.src e) < t (N.tgt e)) {a b : V} (h : KeptReach N keep a b) : t a ≤ t b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih =>
    obtain ⟨g, -, rfl, rfl⟩ := hs
    exact ih.trans (ht g).le

theorem KeptReach.rank_lt {t : V → ℕ} (ht : ∀ e, t (N.src e) < t (N.tgt e)) {a b : V} (h : KeptReach N keep a b) (hne : a ≠ b) : t a < t b := by
  rcases Relation.ReflTransGen.cases_tail h with h₁ | ⟨c, hc, g, -, rfl, rfl⟩
  · exact absurd h₁.symm hne
  · exact (KeptReach.rank_le ht hc).trans_lt (ht g)

end Sampling

/-! ### The tree of a sampling -/

section Tree

variable {ι V E X : Type*} [Fintype X] (N : Network ι V E) (leaf : X → V)

/-- The rows below a node, in the tree of a sampling. -/
def below (keep : E → Prop) (v : V) : Finset X := Finset.univ.filter fun x => KeptReach N keep v (leaf x)

variable {N leaf} {keep keep' : E → Prop}

theorem mem_below {v : V} {x : X} : x ∈ below N leaf keep v ↔ KeptReach N keep v (leaf x) := by
  simp [below]

theorem below_subset {a b : V} (h : KeptReach N keep a b) : below N leaf keep b ⊆ below N leaf keep a := fun _ hx =>
  mem_below.2 (Relation.ReflTransGen.trans h (mem_below.1 hx))

theorem below_leaf (hleaf : ∀ x, N.IsLeaf (leaf x)) (hinj : Function.Injective leaf) (x : X) : below N leaf keep (leaf x) = {x} := by
  ext y
  rw [mem_below, Finset.mem_singleton]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h₁ | ⟨c, ⟨g, -, hg, -⟩, -⟩
    · exact hinj h₁.symm
    · exact absurd hg (hleaf x g)
  · rintro rfl
    exact Relation.ReflTransGen.refl

variable [Fintype V] [DecidableEq X] [Nonempty X]

/-- **The time-ordered tree of a sampling** (`ext:sh_sampled_tree`). -/
def sampledTree (hleaf : ∀ x, N.IsLeaf (leaf x)) (hinj : Function.Injective leaf) (t : V → ℕ) (ht : ∀ e, t (N.src e) < t (N.tgt e)) (hk : IsSampling N keep) : TimeOrderedTree X where
  clusters := (Finset.univ.image (below N leaf keep)).filter Finset.Nonempty
  isHierarchy := by
    have hmem : ∀ v, (below N leaf keep v).Nonempty → below N leaf keep v ∈ (Finset.univ.image (below N leaf keep)).filter Finset.Nonempty := fun v hv =>
      Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hv⟩
    refine ⟨?_, fun x => ?_, fun A hA => (Finset.mem_filter.1 hA).2, fun A hA B hB => ?_⟩
    · have hroot : below N leaf keep N.root = Finset.univ := Finset.eq_univ_of_forall fun x => mem_below.2 (keptReach_root hk _)
      rw [← hroot]
      refine hmem _ ?_
      rw [hroot]
      exact Finset.univ_nonempty
    · rw [← below_leaf hleaf hinj x (keep := keep)]
      exact hmem _ (by rw [below_leaf hleaf hinj x]; exact Finset.singleton_nonempty x)
    · obtain ⟨hA₁, -⟩ := Finset.mem_filter.1 hA
      obtain ⟨hB₁, -⟩ := Finset.mem_filter.1 hB
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hA₁
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hB₁
      by_cases hd : Disjoint (below N leaf keep a) (below N leaf keep b)
      · exact Or.inr (Or.inr hd)
      · obtain ⟨x, hx₁, hx₂⟩ := Finset.not_disjoint_iff.1 hd
        rcases keptReach_total hk (mem_below.1 hx₁) (mem_below.1 hx₂) with h | h
        · exact Or.inr (Or.inl (below_subset h))
        · exact Or.inl (below_subset h)
  time D := (((Finset.univ.filter fun v => below N leaf keep v = D).sup t : ℕ) : ℝ)
  time_lt := by
    intro A hA B hB _ hAB
    obtain ⟨hA₁, hA₂⟩ := Finset.mem_filter.1 hA
    obtain ⟨hB₁, -⟩ := Finset.mem_filter.1 hB
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hA₁
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hB₁
    -- The last nodes with these rows.
    obtain ⟨a', ha', hamax⟩ := Finset.exists_max_image (Finset.univ.filter fun v => below N leaf keep v = below N leaf keep a) t ⟨a, by simp⟩
    obtain ⟨b', hb', hbmax⟩ := Finset.exists_max_image (Finset.univ.filter fun v => below N leaf keep v = below N leaf keep b) t ⟨b, by simp⟩
    have ha'e := (Finset.mem_filter.1 ha').2
    have hb'e := (Finset.mem_filter.1 hb').2
    have hsupa : (Finset.univ.filter fun v => below N leaf keep v = below N leaf keep a).sup t = t a' :=
      le_antisymm (Finset.sup_le hamax) (Finset.le_sup ha')
    have hsupb : (Finset.univ.filter fun v => below N leaf keep v = below N leaf keep b).sup t = t b' :=
      le_antisymm (Finset.sup_le hbmax) (Finset.le_sup hb')
    rw [hsupa, hsupb]
    refine Nat.cast_lt.2 ?_
    obtain ⟨x, hx⟩ := hA₂
    have hxa' : x ∈ below N leaf keep a' := ha'e ▸ hx
    have hxb' : x ∈ below N leaf keep b' := hb'e ▸ hAB.subset hx
    rcases keptReach_total hk (mem_below.1 hxa') (mem_below.1 hxb') with h | h
    · exfalso
      have := below_subset (leaf := leaf) h
      rw [ha'e, hb'e] at this
      exact hAB.2 this
    · refine h.rank_lt ht ?_
      rintro rfl
      rw [ha'e] at hb'e
      exact hAB.ne hb'e

variable {hleaf : ∀ x, N.IsLeaf (leaf x)} {hinj : Function.Injective leaf} {t : V → ℕ} {ht : ∀ e, t (N.src e) < t (N.tgt e)}

theorem mem_clusters {hk : IsSampling N keep} {D : Finset X} :
    D ∈ (sampledTree hleaf hinj t ht hk).clusters ↔ (∃ v, below N leaf keep v = D) ∧ D.Nonempty := by
  change D ∈ (Finset.univ.image (below N leaf keep)).filter Finset.Nonempty ↔ _
  simp [Finset.mem_filter, Finset.mem_image]

theorem time_eq {hk : IsSampling N keep} (D : Finset X) :
    (sampledTree hleaf hinj t ht hk).time D = (((Finset.univ.filter fun v => below N leaf keep v = D).sup t : ℕ) : ℝ) := rfl

/-! ### Changing the kept arc at one node -/

section Step

omit [Fintype V] [DecidableEq X] [Nonempty X] [Fintype X] in
/-- Along the kept arcs below the node `x₀`, nothing changes. -/
theorem keptReach_transfer {x₀ u w : V} (hdiff : ∀ g, N.tgt g ≠ x₀ → (keep g ↔ keep' g)) (hu : KeptReach N keep x₀ u) (h : KeptReach N keep u w) : KeptReach N keep' u w := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c b hc hs ih =>
    obtain ⟨g, hg, rfl, rfl⟩ := hs
    by_cases hx : N.tgt g = x₀
    · exfalso
      refine N.not_reach_tgt_src g ?_
      rw [hx]
      exact KeptReach.reach (Relation.ReflTransGen.trans hu hc)
    · exact ih.tail ⟨g, (hdiff g hx).1 hg, rfl, rfl⟩

omit [Fintype V] [DecidableEq X] [Nonempty X] [Fintype X] in
/-- A path along the kept arcs either is one for the other sampling, or passes through `x₀`. -/
theorem keptReach_or {x₀ u w : V} (hdiff : ∀ g, N.tgt g ≠ x₀ → (keep g ↔ keep' g)) (h : KeptReach N keep u w) : KeptReach N keep' u w ∨ KeptReach N keep x₀ w := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨g, hg, rfl, rfl⟩ := hs
    rcases ih with ih | ih
    · by_cases hx : N.tgt g = x₀
      · exact Or.inr (hx ▸ Relation.ReflTransGen.refl)
      · exact Or.inl (ih.tail ⟨g, (hdiff g hx).1 hg, rfl, rfl⟩)
    · exact Or.inr (ih.tail ⟨g, hg, rfl, rfl⟩)

variable {x₀ : V}

omit [Fintype V] [DecidableEq X] [Nonempty X] in
theorem below_eq_of_reach (hdiff : ∀ g, N.tgt g ≠ x₀ → (keep g ↔ keep' g)) {u : V} (hu : KeptReach N keep x₀ u) :
    below N leaf keep u = below N leaf keep' u := by
  have hsymm : ∀ g, N.tgt g ≠ x₀ → (keep' g ↔ keep g) := fun g hg => (hdiff g hg).symm
  have hu' : KeptReach N keep' x₀ u := keptReach_transfer hdiff Relation.ReflTransGen.refl hu
  ext x
  rw [mem_below, mem_below]
  exact ⟨keptReach_transfer hdiff hu, keptReach_transfer hsymm hu'⟩

omit [Fintype V] [Nonempty X] in
/-- Off the rows below `x₀`, the rows below any node don't change. -/
theorem sdiff_below_eq (hdiff : ∀ g, N.tgt g ≠ x₀ → (keep g ↔ keep' g)) (u : V) :
    below N leaf keep u \ below N leaf keep x₀ = below N leaf keep' u \ below N leaf keep x₀ := by
  have hsymm : ∀ g, N.tgt g ≠ x₀ → (keep' g ↔ keep g) := fun g hg => (hdiff g hg).symm
  have hx₀ := below_eq_of_reach (leaf := leaf) hdiff (Relation.ReflTransGen.refl : KeptReach N keep x₀ x₀)
  ext x
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases keptReach_or hdiff (mem_below.1 h₁) with h | h
    · exact ⟨mem_below.2 h, h₂⟩
    · exact absurd (mem_below.2 h) h₂
  · rintro ⟨h₁, h₂⟩
    rcases keptReach_or hsymm (mem_below.1 h₁) with h | h
    · exact ⟨mem_below.2 h, h₂⟩
    · exact absurd (hx₀ ▸ mem_below.2 h) h₂

variable {hk : IsSampling N keep} {hk' : IsSampling N keep'}

/-- A cluster within the rows below `x₀` stays. -/
theorem mem_clusters_of_subset (hdiff : ∀ g, N.tgt g ≠ x₀ → (keep g ↔ keep' g)) {B : Finset X} (hB : B ⊆ below N leaf keep x₀) (hBc : B ∈ (sampledTree hleaf hinj t ht hk).clusters) :
    B ∈ (sampledTree hleaf hinj t ht hk').clusters := by
  obtain ⟨⟨u, rfl⟩, hne⟩ := mem_clusters.1 hBc
  obtain ⟨x, hx⟩ := hne
  refine mem_clusters.2 ⟨?_, ⟨x, hx⟩⟩
  rcases keptReach_total hk (mem_below.1 hx) (mem_below.1 (hB hx)) with h | h
  · refine ⟨x₀, ?_⟩
    rw [← below_eq_of_reach hdiff Relation.ReflTransGen.refl]
    exact (hB.antisymm (below_subset h)).symm
  · exact ⟨u, (below_eq_of_reach hdiff h).symm⟩

omit [Nonempty X] in
/-- The time of a cluster within the rows below `x₀` doesn't go up. -/
theorem sup_le_sup_of_subset (hk : IsSampling N keep) (ht : ∀ e, t (N.src e) < t (N.tgt e)) (hdiff : ∀ g, N.tgt g ≠ x₀ → (keep g ↔ keep' g)) {B : Finset X} (hB : B ⊆ below N leaf keep x₀) (hne : B.Nonempty) :
    (Finset.univ.filter fun v => below N leaf keep v = B).sup t ≤ (Finset.univ.filter fun v => below N leaf keep' v = B).sup t := by
  refine Finset.sup_le fun u hu => ?_
  have hu' := (Finset.mem_filter.1 hu).2
  obtain ⟨x, hx⟩ := hne
  have hxu : x ∈ below N leaf keep u := hu' ▸ hx
  rcases keptReach_total hk (mem_below.1 hxu) (mem_below.1 (hB hx)) with h | h
  · have heq : below N leaf keep' x₀ = B := by
      rw [← below_eq_of_reach hdiff Relation.ReflTransGen.refl]
      refine (hB.antisymm ?_).symm
      rw [← hu']
      exact below_subset h
    refine (KeptReach.rank_le ht h).trans ?_
    exact Finset.le_sup (f := t) (Finset.mem_filter.2 ⟨Finset.mem_univ _, heq⟩)
  · refine Finset.le_sup (f := t) (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    rw [← below_eq_of_reach hdiff h]
    exact hu'

omit [Nonempty X] in
/-- The time of a cluster within the rows below `x₀` doesn't change. -/
theorem sup_eq_sup_of_subset (hk : IsSampling N keep) (hk' : IsSampling N keep') (ht : ∀ e, t (N.src e) < t (N.tgt e)) (hdiff : ∀ g, N.tgt g ≠ x₀ → (keep g ↔ keep' g)) {B : Finset X} (hB : B ⊆ below N leaf keep x₀) (hne : B.Nonempty) :
    (Finset.univ.filter fun v => below N leaf keep v = B).sup t = (Finset.univ.filter fun v => below N leaf keep' v = B).sup t := by
  have hsymm : ∀ g, N.tgt g ≠ x₀ → (keep' g ↔ keep g) := fun g hg => (hdiff g hg).symm
  have hA : below N leaf keep x₀ = below N leaf keep' x₀ := below_eq_of_reach hdiff Relation.ReflTransGen.refl
  exact le_antisymm (sup_le_sup_of_subset hk ht hdiff hB hne) (sup_le_sup_of_subset hk' ht hsymm (hA ▸ hB) hne)

/-- The time, after pruning: the last node with these rows, off the pruned rows. It's the same for both samplings. -/
def prunedRank (leaf : X → V) (keep : E → Prop) (t : V → ℕ) (N : Network ι V E) (A D : Finset X) : ℕ :=
  (Finset.univ.filter fun u => below N leaf keep u \ A = D).sup t

/-- The time of what remains when a subtree is pruned, in the tree of a sampling. -/
theorem prunedTime_eq {D : Finset X} (hA : (below N leaf keep x₀).Nonempty)
    (hD : D ∈ (sampledTree hleaf hinj t ht hk).prunedClusters (below N leaf keep x₀)) :
    (sampledTree hleaf hinj t ht hk).prunedTime (below N leaf keep x₀) D = (prunedRank leaf keep t N (below N leaf keep x₀) D : ℝ) := by
  set A := below N leaf keep x₀ with hAdef
  have hAc : A ∈ (sampledTree hleaf hinj t ht hk).clusters := mem_clusters.2 ⟨⟨x₀, rfl⟩, hA⟩
  obtain ⟨hor, hdis, hne⟩ := mem_prunedClusters hAc hD
  unfold TimeOrderedTree.prunedTime
  split_ifs with hc
  · rw [time_eq]
    refine Nat.cast_inj.2 (le_antisymm ?_ ?_)
    · refine Finset.sup_mono fun u hu => Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [(Finset.mem_filter.1 hu).2]
      exact hdis.sdiff_eq_left
    · refine Finset.sup_le fun u hu => ?_
      have hu' := (Finset.mem_filter.1 hu).2
      obtain ⟨⟨u', hu'e⟩, -⟩ := mem_clusters.1 hc
      obtain ⟨x, hx⟩ := hne
      have hxu : x ∈ below N leaf keep u := by
        rw [← hu'] at hx
        exact (Finset.mem_sdiff.1 hx).1
      have hxu' : x ∈ below N leaf keep u' := hu'e ▸ hx
      rcases keptReach_total hk (mem_below.1 hxu) (mem_below.1 hxu') with h | h
      · exact (KeptReach.rank_le ht h).trans (Finset.le_sup (f := t) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hu'e⟩))
      · refine Finset.le_sup (f := t) (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
        refine (below_subset h |>.trans (hu'e.le)).antisymm ?_
        rw [← hu']
        exact Finset.sdiff_subset
  · rw [time_eq]
    have hDA := hor.resolve_left hc
    refine Nat.cast_inj.2 (le_antisymm ?_ ?_)
    · refine Finset.sup_mono fun u hu => Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [(Finset.mem_filter.1 hu).2, Finset.union_sdiff_right]
      exact hdis.sdiff_eq_left
    · refine Finset.sup_mono fun u hu => Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      have hu' := (Finset.mem_filter.1 hu).2
      by_cases hd : Disjoint (below N leaf keep u) A
      · exfalso
        rw [hd.sdiff_eq_left] at hu'
        exact hc (mem_clusters.2 ⟨⟨u, hu'⟩, hne⟩)
      · obtain ⟨y, hy₁, hy₂⟩ := Finset.not_disjoint_iff.1 hd
        rcases keptReach_total hk (mem_below.1 hy₁) (mem_below.1 hy₂) with h | h
        · have hsub : A ⊆ below N leaf keep u := below_subset h
          rw [← hu', Finset.sdiff_union_of_subset hsub]
        · exfalso
          have hsub : below N leaf keep u ⊆ A := below_subset h
          rw [Finset.sdiff_eq_empty_iff_subset.2 hsub] at hu'
          exact hne.ne_empty hu'.symm

/-- **Changing the kept arc at one node is one ordered-SPR operation, or no change** (`ext:sh_one_step`). "A subtree that gets pruned and regrafted in an SPR operation corresponds to the descendant subtree of a recombination vertex in an ARG." -/
theorem same_or_isOrderedSPR (hdiff : ∀ g, N.tgt g ≠ x₀ → (keep g ↔ keep' g)) :
    (sampledTree hleaf hinj t ht hk).Same (sampledTree hleaf hinj t ht hk') ∨ (sampledTree hleaf hinj t ht hk).IsOrderedSPR (sampledTree hleaf hinj t ht hk') := by
  have hsymm : ∀ g, N.tgt g ≠ x₀ → (keep' g ↔ keep g) := fun g hg => (hdiff g hg).symm
  have hAeq : below N leaf keep x₀ = below N leaf keep' x₀ := below_eq_of_reach hdiff Relation.ReflTransGen.refl
  set A := below N leaf keep x₀ with hAdef
  have hsub : ∀ B, B ⊆ A → (B ∈ (sampledTree hleaf hinj t ht hk).clusters ↔ B ∈ (sampledTree hleaf hinj t ht hk').clusters) := fun B hB =>
    ⟨mem_clusters_of_subset hdiff hB, mem_clusters_of_subset hsymm (hAeq ▸ hB)⟩
  have htime : ∀ B, B ⊆ A → B ∈ (sampledTree hleaf hinj t ht hk).clusters → (sampledTree hleaf hinj t ht hk).time B = (sampledTree hleaf hinj t ht hk').time B := by
    intro B hB hBc
    rw [time_eq, time_eq, sup_eq_sup_of_subset hk hk' ht hdiff hB (mem_clusters.1 hBc).2]
  have hsd : ∀ u, below N leaf keep u \ A = below N leaf keep' u \ A := sdiff_below_eq hdiff
  by_cases hAne : A.Nonempty
  swap
  · -- No row below the node: nothing changes.
    left
    have hemp : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
    have hbl : ∀ u, below N leaf keep u = below N leaf keep' u := fun u => by
      have := hsd u
      rwa [hemp, Finset.sdiff_empty, Finset.sdiff_empty] at this
    have hfun : below N leaf keep = below N leaf keep' := funext hbl
    refine ⟨?_, fun D _ _ => ?_⟩
    · ext D
      rw [mem_clusters, mem_clusters, hfun]
    · rw [time_eq, time_eq, hfun]
  by_cases hAu : A = Finset.univ
  · -- All the rows are below the node: nothing changes.
    left
    refine ⟨?_, fun D hD _ => htime D (hAu ▸ Finset.subset_univ D) hD⟩
    ext D
    exact hsub D (hAu ▸ Finset.subset_univ D)
  right
  have hpr : (sampledTree hleaf hinj t ht hk).prunedClusters A = (sampledTree hleaf hinj t ht hk').prunedClusters A := by
    have key : ∀ {κ κ' : E → Prop} (hκ : IsSampling N κ) (hκ' : IsSampling N κ'), (∀ u, below N leaf κ u \ A = below N leaf κ' u \ A) →
        (sampledTree hleaf hinj t ht hκ).prunedClusters A ⊆ (sampledTree hleaf hinj t ht hκ').prunedClusters A := by
      intro κ κ' hκ hκ' hu D hD
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hD
      obtain ⟨hB₁, hB₂⟩ := Finset.mem_filter.1 hB
      obtain ⟨⟨u, rfl⟩, -⟩ := mem_clusters.1 hB₁
      have hne : (below N leaf κ u \ A).Nonempty := Finset.sdiff_nonempty.2 hB₂
      refine Finset.mem_image.2 ⟨below N leaf κ' u, Finset.mem_filter.2 ⟨mem_clusters.2 ⟨⟨u, rfl⟩, ?_⟩, ?_⟩, (hu u).symm⟩
      · rw [hu u] at hne
        exact hne.mono Finset.sdiff_subset
      · rw [hu u] at hne
        exact Finset.sdiff_nonempty.1 hne
    exact (key hk hk' hsd).antisymm (key hk' hk fun u => (hsd u).symm)
  refine ⟨A, mem_clusters.2 ⟨⟨x₀, rfl⟩, hAne⟩, mem_clusters.2 ⟨⟨x₀, hAeq.symm⟩, hAne⟩, hAu, hsub, fun B hB hBc _ => htime B hB hBc, hpr, fun D hD _ => ?_⟩
  have h₁ := prunedTime_eq (hk := hk) (hleaf := hleaf) (hinj := hinj) (ht := ht) hAne hD
  have hD' : D ∈ (sampledTree hleaf hinj t ht hk').prunedClusters (below N leaf keep' x₀) := by
    rw [← hAeq]
    exact hpr ▸ hD
  have h₂ := prunedTime_eq (hk := hk') (hleaf := hleaf) (hinj := hinj) (ht := ht) (hAeq ▸ hAne) hD'
  rw [← hAeq] at h₂
  rw [h₁, h₂]
  refine Nat.cast_inj.2 ?_
  unfold prunedRank
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hsd u]

end Step

end Tree

/-! ### Sequences of operations -/

section Steps

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem same_refl (T : TimeOrderedTree X) : T.Same T := ⟨rfl, fun _ _ _ => rfl⟩

theorem IsOrderedSPR_of_same_left {T T' T'' : TimeOrderedTree X} (h : T.Same T') (hs : T'.IsOrderedSPR T'') : T.IsOrderedSPR T'' := by
  obtain ⟨hc, ht⟩ := h
  obtain ⟨A, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hs
  have hpr : T.prunedClusters A = T'.prunedClusters A := by
    unfold TimeOrderedTree.prunedClusters
    rw [hc]
  refine ⟨A, hc ▸ h₁, h₂, h₃, fun B hB => by rw [hc]; exact h₄ B hB, fun B hB hBc hcard => ?_, hpr.trans h₆, fun D hD hcard => ?_⟩
  · rw [ht B hBc hcard]
    exact h₅ B hB (hc ▸ hBc) hcard
  · refine Eq.trans ?_ (h₇ D (hpr ▸ hD) hcard)
    have hAc : A ∈ T.clusters := hc ▸ h₁
    obtain ⟨hor, -, -⟩ := mem_prunedClusters hAc hD
    unfold TimeOrderedTree.prunedTime
    by_cases hDc : D ∈ T.clusters
    · rw [ite_eq_left hDc, ite_eq_left (hc ▸ hDc), ht D hDc hcard]
    · rw [ite_eq_right hDc, ite_eq_right (hc ▸ hDc)]
      refine ht _ (hor.resolve_left hDc) (hcard.trans (Finset.card_le_card Finset.subset_union_left))

theorem sprSteps_of_same_left {T T' T'' : TimeOrderedTree X} (h : T.Same T') {k : ℕ} (hs : TimeOrderedTree.SPRSteps k T' T'') : TimeOrderedTree.SPRSteps k T T'' := by
  cases k with
  | zero =>
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨h₃, h₄⟩ := hs
    exact ⟨h₁.trans h₃, fun A hA hc => (h₂ A hA hc).trans (h₄ A (h₁ ▸ hA) hc)⟩
  | succ k =>
    obtain ⟨T₁, h₁, h₂⟩ := hs
    exact ⟨T₁, IsOrderedSPR_of_same_left h h₁, h₂⟩

theorem sprSteps_trans {k k' : ℕ} {T T' T'' : TimeOrderedTree X} (h : TimeOrderedTree.SPRSteps k T T') (h' : TimeOrderedTree.SPRSteps k' T' T'') : TimeOrderedTree.SPRSteps (k + k') T T'' := by
  induction k generalizing T with
  | zero =>
    rw [Nat.zero_add]
    exact sprSteps_of_same_left h h'
  | succ k ih =>
    obtain ⟨T₁, h₁, h₂⟩ := h
    rw [Nat.succ_add]
    exact ⟨T₁, h₁, ih h₂⟩

theorem doSPR_le_of_steps {k n : ℕ} {T T' : TimeOrderedTree X} (h : TimeOrderedTree.SPRSteps k T T') (hk : k ≤ n) : T.doSPR T' ≤ n := by
  unfold TimeOrderedTree.doSPR
  have hmem : (k : ℕ∞) ∈ ((↑) '' {k | TimeOrderedTree.SPRSteps k T T'} : Set ℕ∞) := ⟨k, h, rfl⟩
  exact (sInf_le hmem).trans (Nat.cast_le.2 hk)

/-- `L(P)` for a sequence along a function on the numbers. -/
theorem sprLength_ofFn_le (Q : ℕ → TimeOrderedTree X) (w : ℕ → ℕ) (hw : ∀ n, (Q n).doSPR (Q (n + 1)) ≤ w n) (m a : ℕ) :
    sprLength (List.ofFn fun i : Fin m => Q (a + i.val)) ≤ ((∑ l ∈ Finset.Ico a (a + (m - 1)), w l : ℕ) : ℕ∞) := by
  induction m generalizing a with
  | zero => simp [sprLength]
  | succ m ih =>
    rcases m with - | m
    · simp [sprLength]
    · have hL : (List.ofFn fun i : Fin (m + 1 + 1) => Q (a + i.val)) = Q a :: List.ofFn fun i : Fin (m + 1) => Q (a + 1 + i.val) := by
        rw [List.ofFn_succ]
        congr 2
        funext i
        congr 1
        simp only [Fin.val_succ]
        omega
      have hL₂ : (List.ofFn fun i : Fin (m + 1) => Q (a + 1 + i.val)) = Q (a + 1) :: List.ofFn fun i : Fin m => Q (a + 1 + i.succ.val) := by
        rw [List.ofFn_succ]
        rfl
      have hIH := ih (a + 1)
      rw [hL, hL₂]
      change (Q a).doSPR (Q (a + 1)) + sprLength (Q (a + 1) :: _) ≤ _
      rw [← hL₂]
      have hb : a + (m + 1 + 1 - 1) = a + 1 + (m + 1 - 1) := by omega
      rw [hb, Finset.sum_eq_sum_Ico_succ_bot (by omega), Nat.cast_add]
      exact add_le_add (hw a) hIH

end Steps

/-! ### The sampling of a choice at each node -/

section Choice

variable {ι V E : Type*} {N : Network ι V E}

/-- The arc kept at a recombination node, for the choice `sel`. -/
def pickArc (left right : {x // N.IsRecomb x} → E) (sel : V → Bool) (x : V) (h : N.IsRecomb x) : E :=
  if sel x then left ⟨x, h⟩ else right ⟨x, h⟩

/-- The kept arcs of the choice `sel`. -/
def keepOf (left right : {x // N.IsRecomb x} → E) (sel : V → Bool) (g : E) : Prop :=
  (∀ f, N.tgt f = N.tgt g → f = g) ∨ ∃ h : N.IsRecomb (N.tgt g), pickArc left right sel (N.tgt g) h = g

variable {left right : {x // N.IsRecomb x} → E}

theorem tgt_pickArc (hl : ∀ x, N.tgt (left x) = x.1) (hr : ∀ x, N.tgt (right x) = x.1) (sel : V → Bool) (x : V) (h : N.IsRecomb x) : N.tgt (pickArc left right sel x h) = x := by
  unfold pickArc
  split_ifs
  · exact hl _
  · exact hr _

theorem pickArc_congr (sel : V → Bool) {x y : V} (hxy : x = y) (h : N.IsRecomb x) (h' : N.IsRecomb y) : pickArc left right sel x h = pickArc left right sel y h' := by
  subst hxy
  rfl

theorem isSampling_keepOf (hl : ∀ x, N.tgt (left x) = x.1) (hr : ∀ x, N.tgt (right x) = x.1) (sel : V → Bool) : IsSampling N (keepOf left right sel) := by
  refine ⟨fun e he => Or.inl he, fun e f hef ht => ?_⟩
  have hx : N.IsRecomb (N.tgt e) := ⟨e, f, hef, rfl, ht.symm⟩
  have hnt : ∀ g, N.tgt g = N.tgt e → (keepOf left right sel g ↔ pickArc left right sel (N.tgt e) hx = g) := by
    intro g hg
    have hntree : ¬ ∀ k, N.tgt k = N.tgt g → k = g := by
      intro hall
      exact hef ((hall e hg.symm).trans (hall f (ht.symm.trans hg.symm)).symm)
    constructor
    · rintro (h | ⟨h, hp⟩)
      · exact absurd h hntree
      · exact (pickArc_congr sel hg.symm hx h).trans hp
    · intro hp
      have hx' : N.IsRecomb (N.tgt g) := hg ▸ hx
      exact Or.inr ⟨hx', (pickArc_congr sel hg hx' hx).trans hp⟩
  rw [hnt e rfl, hnt f ht.symm]
  rcases Network.eq_or_eq_of_tgt hef ht (tgt_pickArc hl hr sel _ hx) with h | h
  · rw [h]
    exact ⟨fun _ hc => hef hc, fun _ => rfl⟩
  · rw [h]
    exact ⟨fun hc _ => hef hc.symm, fun hc => absurd rfl hc⟩

theorem keepOf_iff {sel sel' : V → Bool} {g : E} (h : N.IsRecomb (N.tgt g) → sel (N.tgt g) = sel' (N.tgt g)) : keepOf left right sel g ↔ keepOf left right sel' g := by
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨hx, hp⟩
    refine ⟨hx, ?_⟩
    unfold pickArc at hp ⊢
    rwa [← h hx]
  · rintro ⟨hx, hp⟩
    refine ⟨hx, ?_⟩
    unfold pickArc at hp ⊢
    rwa [h hx]

/-- **The tree of a site is compatible with its column**, by the states along the kept arcs (`ext:sh_compatible`): the nodes below the arc of the site are those off the root's state, when the kept arcs carry the state. -/
theorem keptReach_iff_label_ne [Finite V] {keep : E → Prop} (hk : IsSampling N keep) {i : ι} (hlab : ∀ g, keep g → N.site i ≠ g → N.label (N.tgt g) i = N.label (N.src g) i) (v : V) :
    KeptReach N keep (N.tgt (N.site i)) v ↔ N.label v i ≠ N.label N.root i := by
  constructor
  · intro h
    induction h with
    | refl => exact N.label_tgt_site_ne i
    | tail _ hs ih =>
      obtain ⟨g, hg, rfl, rfl⟩ := hs
      by_cases hsg : N.site i = g
      · subst hsg
        exact absurd (N.reach_of_label_ne ih) (N.not_reach_tgt_src _)
      · rw [hlab g hg hsg]
        exact ih
  · induction v using N.arc_induction with
    | _ v ih =>
      intro hv
      by_cases htop : v = N.tgt (N.site i)
      · rw [htop]
        exact Relation.ReflTransGen.refl
      have hroot : v ≠ N.root := fun h => hv (by rw [h])
      obtain ⟨g, hg, rfl⟩ := hk.exists_kept hroot
      have hsg : N.site i ≠ g := fun h => htop (by rw [h])
      have := hlab g hg hsg
      exact (ih g rfl (by rw [← this]; exact hv)).tail ⟨g, hg, rfl, rfl⟩

end Choice

section Main

variable {X V E ι : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype V] {N : Network ι V E} {leaf : X → V}
  {hleaf : ∀ x, N.IsLeaf (leaf x)} {hinj : Function.Injective leaf} {t : V → ℕ} {ht : ∀ e, t (N.src e) < t (N.tgt e)} {left right : {x // N.IsRecomb x} → E}

theorem sampledTree_same {keep keep' : E → Prop} (hk : IsSampling N keep) (hk' : IsSampling N keep') (h : keep = keep') :
    (sampledTree hleaf hinj t ht hk).Same (sampledTree hleaf hinj t ht hk') := by
  subst h
  exact same_refl _

/-- **Choices that differ at few nodes** (`ext:sh_steps`): as many ordered-SPR operations as nodes. -/
theorem exists_steps (hl : ∀ x, N.tgt (left x) = x.1) (hr : ∀ x, N.tgt (right x) = x.1) (D : Finset V) :
    ∀ sel sel' : V → Bool, (∀ x, N.IsRecomb x → sel x ≠ sel' x → x ∈ D) →
      ∃ k ≤ D.card, TimeOrderedTree.SPRSteps k (sampledTree hleaf hinj t ht (isSampling_keepOf hl hr sel)) (sampledTree hleaf hinj t ht (isSampling_keepOf hl hr sel')) := by
  induction D using Finset.induction_on with
  | empty =>
    intro sel sel' h
    refine ⟨0, le_rfl, sampledTree_same _ _ ?_⟩
    funext g
    refine propext (keepOf_iff fun hx => ?_)
    by_contra hne
    exact Finset.notMem_empty _ (h _ hx hne)
  | insert x₀ D hx₀ ih =>
    intro sel sel' h
    set sel₁ : V → Bool := Function.update sel x₀ (sel' x₀) with hsel₁
    have hdiff : ∀ g, N.tgt g ≠ x₀ → (keepOf left right sel g ↔ keepOf left right sel₁ g) := fun g hg =>
      keepOf_iff fun _ => (Function.update_of_ne hg _ _).symm
    obtain ⟨k, hk, hsteps⟩ := ih sel₁ sel' (by
      intro x hx hne
      by_cases hxx : x = x₀
      · subst hxx
        exact absurd (Function.update_self _ _ _) hne
      · have hne' : sel x ≠ sel' x := by
          rwa [hsel₁, Function.update_of_ne hxx] at hne
        rcases Finset.mem_insert.1 (h x hx hne') with h₁ | h₁
        · exact absurd h₁ hxx
        · exact h₁)
    rw [Finset.card_insert_of_notMem hx₀]
    rcases same_or_isOrderedSPR (hleaf := hleaf) (hinj := hinj) (ht := ht) (hk := isSampling_keepOf hl hr sel) (hk' := isSampling_keepOf hl hr sel₁) hdiff with hs | hs
    · exact ⟨k, by omega, sprSteps_of_same_left hs hsteps⟩
    · exact ⟨k + 1, by omega, _, hs, hsteps⟩

end Main

/-- A rank along the arcs of a network: the number of nodes above. -/
theorem exists_rank {ι V E : Type*} [Fintype V] (N : Network ι V E) : ∃ t : V → ℕ, ∀ e, t (N.src e) < t (N.tgt e) := by
  refine ⟨fun v => (Finset.univ.filter fun u => N.Reach u v).card, fun e => Finset.card_lt_card ?_⟩
  refine ⟨fun u hu => Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, fun hsub => ?_⟩
  · exact (Finset.mem_filter.1 hu).2.tail ⟨e, rfl, rfl⟩
  · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩)
    exact N.not_reach_tgt_src e (Finset.mem_filter.1 this).2

variable {m : ℕ} {M : Finset (Fin m → Bool)}

/-- **The choices of a network** (`ext:sh_choices`). For a network with single crossovers deriving `M`, and any rank along its arcs: the choice of arcs at each number `n` of sites from the left, so that the tree of a site is compatible with its column, and the nodes where one choice differs from the next, which are as many as the recombination nodes at most. -/
theorem exists_choices {V E : Type*} [Fintype V] [Nonempty M] (N : Network (Fin m) V E) (hc : N.Obeys .single) {leaf : M → V} (hl₁ : ∀ r, N.IsLeaf (leaf r)) (hl₂ : ∀ r : M, N.label (leaf r) = r.1)
    (hinj : Function.Injective leaf) (hC : NoConstantColumn M) (t : V → ℕ) (ht : ∀ e, t (N.src e) < t (N.tgt e)) :
    ∃ (left right : {x // N.IsRecomb x} → E) (hleft : ∀ x, N.tgt (left x) = x.1) (hright : ∀ x, N.tgt (right x) = x.1) (sel : ℕ → V → Bool) (D : ℕ → Finset V),
      (∀ i : Fin m, (sampledTree hl₁ hinj t ht (isSampling_keepOf hleft hright (sel i.val))).CompatibleWith fun r => (r : Fin m → Bool) i) ∧
      (∀ n x, N.IsRecomb x → sel n x ≠ sel (n + 1) x → x ∈ D n) ∧ ∑ l ∈ Finset.Ico 0 (m - 1), (D l).card ≤ N.recombCount := by
  rw [Network.obeys_iff] at hc
  have hdata : ∀ x : {x // N.IsRecomb x}, ∃ (e f : E) (c : ℕ), N.tgt e = x.1 ∧ N.tgt f = x.1 ∧ ∀ i : Fin m, N.label x.1 i = if i.val < c then N.label (N.src e) i else N.label (N.src f) i := by
    intro x
    obtain ⟨e, f, -, he, hf, L, hL⟩ := hc x.1 x.2
    obtain ⟨c, hcut⟩ := MyersGriffiths2003.exists_cut L
    refine ⟨e, f, c, he, hf, fun i => ?_⟩
    rw [hL i]
    by_cases hi : i ∈ L
    · rw [ite_eq_left hi, ite_eq_left ((hcut i).1 hi)]
    · rw [ite_eq_right hi, ite_eq_right (fun h => hi ((hcut i).2 h))]
  choose left right c' hleft hright hlab using hdata
  set c : V → ℕ := fun x => if h : N.IsRecomb x then c' ⟨x, h⟩ else 0 with hcdef
  set sel : ℕ → V → Bool := fun n x => decide (n < c x) with hsel
  set X : Finset V := Finset.univ.filter N.IsRecomb with hX
  refine ⟨left, right, hleft, hright, sel, fun n => X.filter fun x => c x = n + 1, fun i => ?_, fun n x hx hne' => ?_, ?_⟩
  · -- The tree of a site is compatible with its column.
    have hk := isSampling_keepOf hleft hright (sel i.val)
    have hcarry : ∀ g, keepOf left right (sel i.val) g → N.site i ≠ g → N.label (N.tgt g) i = N.label (N.src g) i := by
      rintro g (hg | ⟨hx, hp⟩) hsg
      · have := N.label_tree g hg i
        rwa [ite_eq_right hsg] at this
      · have hv := hlab ⟨N.tgt g, hx⟩ i
        have hc' : c (N.tgt g) = c' ⟨N.tgt g, hx⟩ := dite_eq_left hx
        unfold pickArc at hp
        rw [hv]
        by_cases hi : i.val < c' ⟨N.tgt g, hx⟩
        · have hs : sel i.val (N.tgt g) = true := by
            simp only [hsel, decide_eq_true_eq, hc']
            exact hi
          rw [hs] at hp
          have hp' : left ⟨N.tgt g, hx⟩ = g := hp
          rw [ite_eq_left hi]
          exact congrArg (fun z => N.label (N.src z) i) hp'
        · have hs : ¬ sel i.val (N.tgt g) = true := by
            simp only [hsel, decide_eq_true_eq, hc']
            exact hi
          rw [ite_eq_right hs] at hp
          rw [ite_eq_right hi]
          exact congrArg (fun z => N.label (N.src z) i) hp
    have hbelow : ∀ r : M, r ∈ below N leaf (keepOf left right (sel i.val)) (N.tgt (N.site i)) ↔ r.1 i ≠ N.label N.root i := by
      intro r
      rw [mem_below, keptReach_iff_label_ne hk hcarry, hl₂]
    obtain ⟨r₁, hr₁, r₂, hr₂, hne₁₂⟩ := hC i
    have hoff : ∃ r : M, r.1 i ≠ N.label N.root i := by
      by_cases h₁ : r₁ i = N.label N.root i
      · exact ⟨⟨r₂, hr₂⟩, fun h₂ => hne₁₂ (h₁.trans h₂.symm)⟩
      · exact ⟨⟨r₁, hr₁⟩, h₁⟩
    have hon : ∃ r : M, r.1 i = N.label N.root i := by
      by_cases h₁ : r₁ i = N.label N.root i
      · exact ⟨⟨r₁, hr₁⟩, h₁⟩
      · have hbool : ∀ x y z : Bool, x ≠ z → x ≠ y → y = z := by decide
        exact ⟨⟨r₂, hr₂⟩, hbool _ _ _ h₁ hne₁₂⟩
    set C := below N leaf (keepOf left right (sel i.val)) (N.tgt (N.site i)) with hCdef
    refine ⟨C, mem_clusters.2 ⟨⟨_, rfl⟩, ?_⟩, fun heq => ?_, ?_⟩
    · obtain ⟨r, hr⟩ := hoff
      exact ⟨r, (hbelow r).2 hr⟩
    · obtain ⟨r, hr⟩ := hon
      exact (hbelow r).1 (heq ▸ Finset.mem_univ r) hr
    · cases hroot : N.label N.root i
      · refine Or.inl (Finset.ext fun r => ?_)
        rw [hbelow, hroot, Finset.mem_filter]
        simp
      · refine Or.inr (Finset.ext fun r => ?_)
        rw [hbelow, hroot, Finset.mem_filter]
        simp
  · refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩, ?_⟩
    by_contra hcx
    apply hne'
    simp only [hsel, decide_eq_decide]
    omega
  · have hcount' : N.recombCount = X.card := by
      unfold Network.recombCount
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcount']
    calc ∑ l ∈ Finset.Ico 0 (m - 1), (X.filter fun x => c x = l + 1).card ≤ ∑ l ∈ Finset.Ico 0 (m - 1), (X.filter fun x => c x - 1 = l).card := by
          refine Finset.sum_le_sum fun l _ => Finset.card_le_card fun x hx => ?_
          obtain ⟨hx₁, hx₂⟩ := Finset.mem_filter.1 hx
          exact Finset.mem_filter.2 ⟨hx₁, by omega⟩
      _ = (X.filter fun x => c x - 1 ∈ Finset.Ico 0 (m - 1)).card := Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ ≤ X.card := Finset.card_filter_le _ _

/-- **The other inequality** (`ext:song_hein_min`). An optimal network gives a sequence of time-ordered trees compatible with the columns, with `L(P) ≤ R¹(M)`: the tree of a site follows the crossovers at that site. -/
theorem exists_sprLength_le (M : Finset (Fin m → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ P : Fin m → TimeOrderedTree M, (∀ i, (P i).CompatibleWith fun r => (r : Fin m → Bool) i) ∧ sprLength (List.ofFn P) ≤ R .single M := by
  have hne : Nonempty M := hM.to_subtype
  obtain ⟨a, b, N, hc, hd, hcount⟩ := Nat.sInf_mem (recombSet_nonempty .single hM)
  have hex : ∀ r : M, ∃ v, N.IsLeaf v ∧ N.label v = r.1 := fun r => hd.surjOn r.2
  choose leaf hl₁ hl₂ using hex
  have hinj : Function.Injective leaf := fun r r' h => Subtype.ext ((hl₂ r).symm.trans ((congrArg N.label h).trans (hl₂ r')))
  obtain ⟨t, ht⟩ := exists_rank N
  obtain ⟨left, right, hleft, hright, sel, D, hcompat, hD, hsum⟩ := exists_choices N hc hl₁ hl₂ hinj hC t ht
  set Q : ℕ → TimeOrderedTree M := fun n => sampledTree hl₁ hinj t ht (isSampling_keepOf hleft hright (sel n)) with hQ
  have hstep : ∀ n, (Q n).doSPR (Q (n + 1)) ≤ (D n).card := by
    intro n
    obtain ⟨k, hk, hs⟩ := exists_steps (hleaf := hl₁) (hinj := hinj) (ht := ht) hleft hright (D n) (sel n) (sel (n + 1)) (hD n)
    exact doSPR_le_of_steps hs hk
  refine ⟨fun i => Q i.val, hcompat, ?_⟩
  have hle := sprLength_ofFn_le Q (fun n => (D n).card) hstep m 0
  simp only [Nat.zero_add] at hle
  exact hle.trans (Nat.cast_le.2 (hsum.trans (le_of_eq hcount)))

/-- **The minimum of `L(P)` is `R¹(M)`, and it's attained** (`ext:song_hein_eq`). The source's equations (3), (5), `min_P L(P) = R_min(S)`, for time-ordered trees, with the columns not constant. A constant column has no compatible tree here: see the `README.md`. -/
theorem exists_sprLength_eq_R (M : Finset (Fin m → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ P : Fin m → TimeOrderedTree M, (∀ i, (P i).CompatibleWith fun r => (r : Fin m → Bool) i) ∧ sprLength (List.ofFn P) = R .single M := by
  obtain ⟨P, hP, hle⟩ := exists_sprLength_le M hM hC
  exact ⟨P, hP, le_antisymm hle (R_le_sprLength M hM P hP)⟩

/-- **The same, as an infimum** (`ext:song_hein_inf`). -/
theorem R_eq_iInf_sprLength (M : Finset (Fin m → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    (R .single M : ℕ∞) = ⨅ (P : Fin m → TimeOrderedTree M) (_ : ∀ i, (P i).CompatibleWith fun r => (r : Fin m → Bool) i), sprLength (List.ofFn P) := by
  refine le_antisymm (le_iInf₂ fun P hP => R_le_sprLength M hM P hP) ?_
  obtain ⟨P, hP, hle⟩ := exists_sprLength_le M hM hC
  exact iInf₂_le_of_le P hP hle

end SongHein2005
