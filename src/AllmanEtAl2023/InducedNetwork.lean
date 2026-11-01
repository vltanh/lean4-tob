module

public import AllmanEtAl2023.Definitions

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Definition 6, the induced network

The published Definition 6 has three steps, of which the arXiv version has the first two: "1) retaining only those
nodes and edges ancestral to one or more taxa in `Y`, 2) suppressing all nodes with both in- and out-degree 1, and
3) if the root then has outdegree 1, removing it and its descendant edge and designating its child as the root".

The library's `RootedNetwork.inducedNetwork` is another network: it cuts at the LSA of `Y` (Rhodes, Allman, Ané,
Baños 2026, Section 2). Here:

* `retained`: step 1, the library's `belowNetwork` at the root of `N`;
* `RootedNetwork.suppress`: step 2;
* `removeStem`: step 3;
* `induced`, `induced_isBinaryNetwork`: the network, and that it is a network of Definition 1, when `Y` has at
  least two taxa;
* `inducedParams`: its numerical parameters. "For a metric graph the new edge is assigned a length equal to the sum
  of lengths of the two replaced. If the out-edge was hybrid, the new edge is also hybrid and retains the
  hybridization parameter." The library's `suppressMetric` adds lengths along a chain and multiplies inheritances, and
  the inheritances other than the last are `1`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*}

/-! ### Step 3: removing a stem -/

section Stem

variable (M : RootedNetwork V E X)

/-- The root has out-degree 1. -/
def HasStem : Prop := M.graph.outdegree M.root = 1

/-- The edge leaving the root, when it is unique. -/
def stemArc (h : HasStem M) : E := Classical.choose ((M.graph.outdegree_eq_one_iff M.root).mp h)

theorem stemArc_spec (h : HasStem M) (f : E) :
    M.graph.source f = M.root ↔ f = stemArc M h :=
  Classical.choose_spec ((M.graph.outdegree_eq_one_iff M.root).mp h) f

/-- **Step 3 of Definition 6**: "if the root then has outdegree 1, removing it and its descendant edge and designating
its child as the root". Otherwise nothing changes. -/
def removeStem (hM : M.IsPhylogenetic) :
    RootedNetwork {v // ¬ (HasStem M ∧ v = M.root)} {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} X where
  graph :=
    { source := fun e => ⟨M.graph.source e.1, e.2⟩
      target := fun e => ⟨M.graph.target e.1, fun h => target_ne_root hM e.1 h.2⟩ }
  root :=
    if h : HasStem M then ⟨M.graph.target (stemArc M h), fun h' => target_ne_root hM _ h'.2⟩
    else ⟨M.root, fun h' => h h'.1⟩
  leaf x := ⟨M.leaf x, fun h => M.leaf_ne_root hM x h.2⟩

variable {M} (hM : M.IsPhylogenetic)

theorem removeStem_graph_source (e : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}) :
    ((removeStem M hM).graph.source e).1 = M.graph.source e.1 := rfl

theorem removeStem_graph_target (e : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}) :
    ((removeStem M hM).graph.target e).1 = M.graph.target e.1 := rfl

include hM

/-- With a stem, every node other than the root is below the stem. -/
theorem target_stemArc_reaches (h : HasStem M) {v : V} (hv : v ≠ M.root) :
    M.graph.Reaches (M.graph.target (stemArc M h)) v := by
  rcases Relation.ReflTransGen.cases_head (hM.root_reaches v) with h' | ⟨a, ⟨f, hfs, hft⟩, hav⟩
  · exact absurd h'.symm hv
  · rw [(stemArc_spec M h f).mp hfs] at hft
    rwa [hft]

/-- With a stem, its child has no other parent. -/
theorem eq_stemArc_of_target (h : HasStem M) {f : E} (hf : M.graph.target f = M.graph.target (stemArc M h)) :
    f = stemArc M h := by
  by_cases hs : M.graph.source f = M.root
  · exact (stemArc_spec M h f).mp hs
  · exact absurd (Relation.TransGen.head' ⟨f, rfl, hf⟩ (target_stemArc_reaches hM h hs))
      (hM.acyclic _)

/-- With a stem and two taxa, its child is not a taxon. -/
theorem target_stemArc_ne_leaf [Nontrivial X] (h : HasStem M) (x : X) :
    M.graph.target (stemArc M h) ≠ M.leaf x := by
  have := hM.finite_arcs
  intro hx
  obtain ⟨y, hy⟩ := exists_ne x
  have hr := target_stemArc_reaches hM h (M.leaf_ne_root hM y)
  rw [hx] at hr
  have := M.graph.eq_of_reaches_of_outdegree_eq_zero hr ((hM.leaves _).mpr ⟨x, rfl⟩)
  exact hy (hM.leaf_injective this)

/-- A kept node keeps its outgoing edges. -/
theorem removeStem_outdegree (v : {v // ¬ (HasStem M ∧ v = M.root)}) :
    (removeStem M hM).graph.outdegree v = M.graph.outdegree v.1 := by
  refine Set.ncard_congr' ⟨fun e => ⟨e.1.1, congrArg Subtype.val e.2⟩,
    fun e => ⟨⟨e.1, ?_⟩, Subtype.ext e.2⟩, fun _ => rfl, fun _ => rfl⟩
  have he : M.graph.source e.1 = v.1 := e.2
  rw [he]
  exact v.2

/-- A node other than the new root keeps its incoming edges. -/
theorem removeStem_indegree {v : {v // ¬ (HasStem M ∧ v = M.root)}} (hv : v ≠ (removeStem M hM).root) :
    (removeStem M hM).graph.indegree v = M.graph.indegree v.1 := by
  refine Set.ncard_congr' ⟨fun e => ⟨e.1.1, congrArg Subtype.val e.2⟩,
    fun e => ⟨⟨e.1, fun hs => ?_⟩, Subtype.ext e.2⟩, fun _ => rfl, fun _ => rfl⟩
  have he : M.graph.target e.1 = v.1 := e.2
  have hst := (stemArc_spec M hs.1 e.1).mp hs.2
  refine hv (Subtype.ext ?_)
  change v.1 = ((removeStem M hM).root).1
  simp only [removeStem, dite_eq_left hs.1]
  exact he.symm.trans (congrArg M.graph.target hst)

/-- **Removing a stem gives a network**, on at least two taxa. -/
theorem removeStem_isPhylogenetic [Nontrivial X] : (removeStem M hM).IsPhylogenetic := by
  have : Finite V := hM.finite_vertices
  have : Finite E := hM.finite_arcs
  have hrootval : ¬ HasStem M → ((removeStem M hM).root).1 = M.root := fun h => by
    simp only [removeStem, dite_eq_right h]
  have hrootstem : ∀ h : HasStem M,
      ((removeStem M hM).root).1 = M.graph.target (stemArc M h) := fun h => by
    simp only [removeStem, dite_eq_left h]
  have hne : ∀ v : {v // ¬ (HasStem M ∧ v = M.root)}, HasStem M → v.1 ≠ M.root :=
    fun v h hv => v.2 ⟨h, hv⟩
  refine ⟨inferInstance, inferInstance, hM.finite_taxa, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    refine hM.acyclic v.1 (Relation.TransGen.lift Subtype.val ?_ v v hv)
    rintro a b ⟨e, hs, ht⟩
    exact ⟨e.1, congrArg Subtype.val hs, congrArg Subtype.val ht⟩
  · -- the new root reaches everything
    have hlift : ∀ {s t : V} (hs : ¬ (HasStem M ∧ s = M.root)), M.graph.Reaches s t →
        ∃ ht : ¬ (HasStem M ∧ t = M.root), (removeStem M hM).graph.Reaches ⟨s, hs⟩ ⟨t, ht⟩ := by
      intro s t hs hst
      induction hst with
      | refl => exact ⟨hs, .refl⟩
      | @tail a b _ hab ih =>
        obtain ⟨ha, hr⟩ := ih
        obtain ⟨f, hfs, hft⟩ := hab
        refine ⟨fun h => target_ne_root hM f (hft.trans h.2), hr.tail ?_⟩
        exact ⟨⟨f, fun h => ha ⟨h.1, hfs ▸ h.2⟩⟩, Subtype.ext hfs, Subtype.ext hft⟩
    intro v
    by_cases h : HasStem M
    · have hr := target_stemArc_reaches hM h (hne v h)
      obtain ⟨_, hreach⟩ := hlift (fun h' => target_ne_root hM _ h'.2) hr
      have hroot : (removeStem M hM).root = ⟨M.graph.target (stemArc M h), fun h' => target_ne_root hM _ h'.2⟩ :=
        Subtype.ext (hrootstem h)
      rw [hroot]
      exact hreach
    · obtain ⟨_, hreach⟩ := hlift (s := M.root) (fun h' => h h'.1) (hM.root_reaches v.1)
      have hroot : (removeStem M hM).root = ⟨M.root, fun h' => h h'.1⟩ := Subtype.ext (hrootval h)
      rw [hroot]
      exact hreach
  · rw [DirectedMultigraph.indegree_eq_zero_iff]
    intro e he
    have hval := congrArg Subtype.val he
    by_cases h : HasStem M
    · rw [hrootstem h] at hval
      exact e.2 ⟨h, (stemArc_spec M h e.1).mpr (eq_stemArc_of_target hM h hval)⟩
    · rw [hrootval h] at hval
      exact target_ne_root hM e.1 hval
  · intro v hv
    rw [DirectedMultigraph.one_le_indegree_iff]
    have hv1 : v.1 ≠ M.root := by
      by_cases h : HasStem M
      · exact hne v h
      · exact fun hr => hv (Subtype.ext (hr.trans (hrootval h).symm))
    obtain ⟨f, hf⟩ := (M.graph.one_le_indegree_iff _).mp (hM.nonroot_indegree _ hv1)
    refine ⟨⟨f, fun h => ?_⟩, Subtype.ext hf⟩
    have hfe := (stemArc_spec M h.1 f).mp h.2
    refine hv (Subtype.ext ?_)
    rw [hrootstem h.1, ← hf]
    exact congrArg M.graph.target hfe
  · intro x y h
    exact hM.leaf_injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨g, hg⟩ := (M.graph.indegree_eq_one_iff _).mp (hM.leaf_indegree x)
    have hkept : ¬ (HasStem M ∧ M.graph.source g = M.root) := fun h => by
      have hge := (stemArc_spec M h.1 g).mp h.2
      exact target_stemArc_ne_leaf hM h.1 x (hge ▸ (hg g).mpr rfl)
    refine (DirectedMultigraph.indegree_eq_one_iff _ _).mpr ⟨⟨g, hkept⟩, fun f => ?_⟩
    constructor
    · intro hf
      exact Subtype.ext ((hg f.1).mp (congrArg Subtype.val hf))
    · rintro rfl
      exact Subtype.ext ((hg g).mpr rfl)
  · intro v
    rw [removeStem_outdegree hM v]
    refine (hM.leaves v.1).trans ⟨?_, ?_⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, congrArg Subtype.val hx⟩

/-- **Removing a stem gives a binary network**, when the root has out-degree 1 or 2 and every other internal
node has degree 3, on at least two taxa. The child of a stem has one parent, so it has out-degree 2. -/
theorem removeStem_isBinary [Nontrivial X] (hroot : M.graph.outdegree M.root = 1 ∨ M.graph.outdegree M.root = 2)
    (hdeg : ∀ v, v ≠ M.root → M.graph.outdegree v ≠ 0 → M.graph.indegree v + M.graph.outdegree v = 3) :
    (removeStem M hM).IsBinary := by
  have : Finite E := hM.finite_arcs
  have hP := removeStem_isPhylogenetic hM
  refine ⟨?_, fun v hv h0 => ?_⟩
  · rw [removeStem_outdegree]
    by_cases h : HasStem M
    · have hval : ((removeStem M hM).root).1 = M.graph.target (stemArc M h) := by
        simp only [removeStem, dite_eq_left h]
      rw [hval]
      have hne := target_ne_root hM (stemArc M h)
      have h0 : M.graph.outdegree (M.graph.target (stemArc M h)) ≠ 0 := fun h0 => by
        obtain ⟨x, hx⟩ := (hM.leaves _).mp h0
        exact target_stemArc_ne_leaf hM h x hx.symm
      have h3 := hdeg _ hne h0
      have hin : M.graph.indegree (M.graph.target (stemArc M h)) = 1 :=
        (M.graph.indegree_eq_one_iff _).mpr ⟨stemArc M h, fun f =>
          ⟨eq_stemArc_of_target hM h, fun hf => hf ▸ rfl⟩⟩
      omega
    · have hval : ((removeStem M hM).root).1 = M.root := by
        simp only [removeStem, dite_eq_right h]
      rw [hval]
      exact hroot.resolve_left h
  · rw [removeStem_outdegree] at h0 ⊢
    rw [removeStem_indegree hM hv]
    refine hdeg v.1 (fun hr => ?_) h0
    by_cases h : HasStem M
    · exact v.2 ⟨h, hr⟩
    · refine hv (Subtype.ext ?_)
      simp only [removeStem, dite_eq_right h]
      exact hr

end Stem

/-! ### The induced network -/

section Induced

variable {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) (Y : Set X) (hY : Y.Nontrivial)

/-- **Step 1 of Definition 6**: "retaining only those nodes and edges ancestral to one or more taxa in `Y`". The
library's `belowNetwork` at the root of `N`, for which being below the root says nothing more. -/
def retained : RootedNetwork (N.belowVertices N.root Y) (N.belowArcs N.root Y) Y :=
  N.belowNetwork N.root Y
    (by
      obtain ⟨x, hx⟩ := hY.nonempty
      exact ⟨x, hx, hN.isPhylogenetic.root_reaches _⟩)
    fun _ _ => hN.isPhylogenetic.root_reaches _

theorem retained_isPhylogenetic : (retained hN Y hY).IsPhylogenetic :=
  belowNetwork_isPhylogenetic hN.isPhylogenetic hY (N.root_isStableAncestor Y)

/-- **Steps 1 and 2 of Definition 6**. -/
def retainedSuppressed :
    RootedNetwork {v // ¬ (retained hN Y hY).IsChainVertex v}
      {e // ¬ (retained hN Y hY).IsChainVertex ((retained hN Y hY).graph.source e)} Y :=
  (retained hN Y hY).suppress (retained_isPhylogenetic hN Y hY)

theorem retainedSuppressed_isPhylogenetic : (retainedSuppressed hN Y hY).IsPhylogenetic :=
  suppress_isPhylogenetic _

/-- The nodes of the induced network on `Y`. -/
abbrev InducedV := {v // ¬ (HasStem (retainedSuppressed hN Y hY) ∧ v = (retainedSuppressed hN Y hY).root)}

/-- The edges of the induced network on `Y`. -/
abbrev InducedE := {e // ¬ (HasStem (retainedSuppressed hN Y hY) ∧
  (retainedSuppressed hN Y hY).graph.source e = (retainedSuppressed hN Y hY).root)}

/-- **Definition 6** (`a:def:induced`). The *induced rooted binary network* `𝒩⁺_Y` on `Y ⊂ X`, as published: "1) retaining
only those nodes and edges ancestral to one or more taxa in `Y`, 2) suppressing all nodes with both in- and
out-degree 1, and 3) if the root then has outdegree 1, removing it and its descendant edge and designating its
child as the root. We then say `𝒩⁺` *displays* `𝒩⁺_Y`." The arXiv version has steps 1 and 2 only. It is for `Y` with at
least two taxa: on one taxon step 3 leaves a single node, which is not a network of Definition 1. -/
def induced : RootedNetwork (InducedV hN Y hY) (InducedE hN Y hY) Y :=
  removeStem (retainedSuppressed hN Y hY) (retainedSuppressed_isPhylogenetic hN Y hY)

theorem induced_isPhylogenetic : (induced hN Y hY).IsPhylogenetic :=
  have : Nontrivial Y := hY.coe_sort
  removeStem_isPhylogenetic _

/-- The degrees after steps 1 and 2 of Definition 6: the root has out-degree 1 or 2, and every other internal node
has degree 3. A retained node of in-degree 1 with one retained child is suppressed, and a hybrid node keeps its two
parents, since a parent of a retained node is retained. -/
theorem retainedSuppressed_degree :
    ((retainedSuppressed hN Y hY).graph.outdegree (retainedSuppressed hN Y hY).root = 1 ∨
        (retainedSuppressed hN Y hY).graph.outdegree (retainedSuppressed hN Y hY).root = 2) ∧
      ∀ v, v ≠ (retainedSuppressed hN Y hY).root → (retainedSuppressed hN Y hY).graph.outdegree v ≠ 0 →
        (retainedSuppressed hN Y hY).graph.indegree v + (retainedSuppressed hN Y hY).graph.outdegree v = 3 := by
  have hP := hN.isPhylogenetic
  have hB := hN.isBinary
  have : Finite E := hP.finite_arcs
  have hR := retained_isPhylogenetic hN Y hY
  have hS := retainedSuppressed_isPhylogenetic hN Y hY
  have hst := N.root_isStableAncestor Y
  refine ⟨?_, fun v hv h0 => ?_⟩
  · have h1 : (retainedSuppressed hN Y hY).graph.outdegree (retainedSuppressed hN Y hY).root ≠ 0 := by
      intro h
      obtain ⟨x, hx⟩ := (hS.leaves _).mp h
      exact N.leaf_ne_root hP x.1 (congrArg (fun v => v.1.1) hx)
    have h2 : (retainedSuppressed hN Y hY).graph.outdegree (retainedSuppressed hN Y hY).root ≤ 2 := by
      refine (suppress_outdegree hR _).le.trans ?_
      refine (belowNetwork_outdegree_le _).trans ?_
      exact hB.1.le
    omega
  · have hv1 : v.1.1 ≠ N.root := fun h => hv (Subtype.ext (Subtype.ext h))
    have hin : (retainedSuppressed hN Y hY).graph.indegree v = N.graph.indegree v.1.1 :=
      (suppress_indegree hR v).trans (belowNetwork_indegree hP hst v.1 hv1)
    have hout : (retainedSuppressed hN Y hY).graph.outdegree v = (retained hN Y hY).graph.outdegree v.1 :=
      suppress_outdegree hR v
    have hle : (retained hN Y hY).graph.outdegree v.1 ≤ N.graph.outdegree v.1.1 :=
      belowNetwork_outdegree_le _
    have h3 := hB.2 v.1.1 hv1 (by omega)
    have h1 := hP.nonroot_indegree _ hv1
    have hnc : ¬ ((retained hN Y hY).graph.indegree v.1 = 1 ∧ (retained hN Y hY).graph.outdegree v.1 = 1) := v.2
    have hin' : (retained hN Y hY).graph.indegree v.1 = N.graph.indegree v.1.1 :=
      belowNetwork_indegree hP hst v.1 hv1
    omega

/-- **The induced network of a network of Definition 1 is one**, on at least two taxa. -/
theorem induced_isBinaryNetwork : IsBinaryNetwork (induced hN Y hY) := by
  have : Nontrivial Y := hY.coe_sort
  obtain ⟨h₁, h₂⟩ := retainedSuppressed_degree hN Y hY
  exact isBinaryNetwork_iff.mpr
    ⟨induced_isPhylogenetic hN Y hY, removeStem_isBinary _ h₁ h₂⟩

/-- **The parameters of Definition 6**: lengths along a suppressed path add, the hybridization parameter is that of the
last edge, and the descendant edge of a removed root is forgotten. -/
def inducedParams [Fintype E] (θ : MetricData E) : MetricData (InducedE hN Y hY) :=
  have : Fintype (N.belowArcs N.root Y) := Fintype.ofFinite _
  { length := fun e => ((retained hN Y hY).suppressMetric (belowMetric N.root Y θ)).length e.1
    inheritance := fun e => ((retained hN Y hY).suppressMetric (belowMetric N.root Y θ)).inheritance e.1 }

end Induced

end AllmanEtAl2023
