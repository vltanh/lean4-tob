module

public import Basic.Defs
public import Basic.InducedSplits
public import Basic.NMSCChain
public import Phylogenetics.Hierarchy.Basic
public import Phylogenetics.NMSC.DisplayedTreeModel
public import Phylogenetics.Network.Cuts
public import Phylogenetics.Network.DeletedArcs
public import Phylogenetics.Network.Quartets
public import Phylogenetics.Tree.Splits

/-!
# Networks given by tables of arcs, and a binary network with a 4-cycle and a cut edge

`ECToBlob.FinNetwork.net src tgt root lf` is the network with the arcs `src f → tgt f`. With `Tables`, tables of what
each vertex reaches and of what the root reaches off each arc, `decide` checks reachability, domination
(`Tables.rdom_iff`), cut splits (`Tables.hasCutSplit_iff`) and the tree of blobs (`Tables.mem_treeOfBlobs_iff`).

`ECToBlob.FinNetwork.Binary.net`, on the taxa `a, b, c, d, e = 0, …, 4`, is a binary network with the cut edge `de|abc`
and a 4-cycle through `a, b, c`; its tree of blobs has one internal edge (`Binary.mem_treeOfBlobs_iff`). A parent
choice keeps one of the arcs `uh`, `vh` into the reticulation (`Binary.uh_or_vh`), and the quartet trees its tree
displays follow (`Binary.displays_of_uh`, `Binary.displays_of_vh`).

ECToBlob's counterexamples on the displayed tree model (`src/ECToBlob/DisplayedTreeExample.lean`) and TOB-QMC's
at level 2 (`src/TOBQMC/SupplementLevelTwo.lean`, `src/TOBQMC/SupplementLemma2.lean`,
`src/TOBQMC/DisplayedRefinement.lean`) use this network.
-/

@[expose] public noncomputable section

open scoped Classical

section
open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset Filter Topology MeasureTheory

namespace ECToBlob.Section3Observations

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

omit [Fintype E] in
/-- A vertex whose cluster traces a side of a quartet tree makes the tree of the choice display it. -/
theorem displays_of_cluster {c : N.ParentChoice} {s : QuartetTree X}
    {P : Finset X} (hP : P ∈ s.val) {u : V} (hb : ∀ x ∈ P, x ∈ N.displayedCluster c u)
    (hn : ∀ x ∈ s.taxa, x ∉ P → x ∉ N.displayedCluster c u) : Displays (N.displayedSides c) s := by
  have hAq : N.displayedCluster c u ∩ s.taxa = P := by
    ext x
    rw [mem_inter]
    constructor
    · rintro ⟨hxA, hxq⟩
      by_contra hxP
      exact hn x hxq hxP hxA
    · exact fun hx => ⟨hb x hx, s.subset_taxa hP hx⟩
  obtain ⟨a, ha⟩ : P.Nonempty := card_pos.1 (by rw [s.card_of_mem hP]; omega)
  obtain ⟨y, hy⟩ : (s.taxa \ P).Nonempty :=
    card_pos.1 (by rw [s.card_of_mem (s.sdiff_mem hP)]; omega)
  obtain ⟨hyq, hyP⟩ := mem_sdiff.1 hy
  refine ⟨_, mem_unroot.2 (Or.inl ⟨mem_displayedClusters.2 ⟨nonempty_iff_ne_empty.1 ⟨a, hb a ha⟩, u, rfl⟩,
    fun h => hn y hyq hyP (h ▸ mem_univ y)⟩), ?_⟩
  rw [hAq]
  exact hP

end ECToBlob.Section3Observations
end

section
open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology

namespace ECToBlob.FinNetwork

open ECToBlob.Deterministic ECToBlob.Coarsening ECToBlob.FalseEdge ECToBlob.Section3Observations

/-! ### Networks from tables -/

section Tables

variable {k m t : ℕ}

/-- The network with the arcs `src f → tgt f`, the root `root` and the taxa `lf x`. -/
def net (src tgt : Fin m → Fin k) (root : Fin k) (lf : Fin t → Fin k) :
    RootedNetwork (Fin k) (Fin m) (Fin t) := ⟨⟨src, tgt⟩, root, lf⟩

/-- Tables of what the vertices reach, `desc`, and of what the root reaches off one arc, `avoid`, with arcs that go down in
the order of `Fin k`. -/
structure Tables (src tgt : Fin m → Fin k) (root : Fin k) (desc : Fin k → Finset (Fin k))
    (avoid : Fin m → Finset (Fin k)) : Prop where
  desc_refl : ∀ u, u ∈ desc u
  desc_closed : ∀ u f, src f ∈ desc u → tgt f ∈ desc u
  desc_back : ∀ u w, w ∈ desc u → w = u ∨ ∃ f, tgt f = w ∧ src f ∈ desc u
  avoid_root : ∀ e, root ∈ avoid e
  avoid_closed : ∀ e f, f ≠ e → src f ∈ avoid e → tgt f ∈ avoid e
  avoid_back : ∀ e w, w ∈ avoid e → w = root ∨ ∃ f, f ≠ e ∧ tgt f = w ∧ src f ∈ avoid e
  down : ∀ f, (tgt f).val < (src f).val

variable {src tgt : Fin m → Fin k} {root : Fin k} {lf : Fin t → Fin k}
  {desc : Fin k → Finset (Fin k)} {avoid : Fin m → Finset (Fin k)}

/-- A closed set with parents in it is what is reached from a vertex. -/
theorem reflTransGen_iff {r : Fin k → Fin k → Prop} {u : Fin k} {S : Finset (Fin k)} (hu : u ∈ S)
    (hc : ∀ a b, r a b → a ∈ S → b ∈ S)
    (hb : ∀ w ∈ S, w = u ∨ ∃ a, r a w ∧ a ∈ S ∧ w.val < a.val) {w : Fin k} :
    Relation.ReflTransGen r u w ↔ w ∈ S := by
  constructor
  · intro h
    induction h with
    | refl => exact hu
    | tail _ hs ih => exact hc _ _ hs ih
  · intro hw
    have key : ∀ n, ∀ w : Fin k, k - w.val = n → w ∈ S → Relation.ReflTransGen r u w := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro w hn hw
        rcases hb w hw with rfl | ⟨a, hr, ha, hlt⟩
        · exact .refl
        · have ha' := a.isLt
          exact (ih (k - a.val) (by omega) a rfl ha).tail hr
    exact key _ w rfl hw

theorem Tables.reaches_iff (h : Tables src tgt root desc avoid) {u w : Fin k} :
    (net src tgt root lf).graph.Reaches u w ↔ w ∈ desc u := by
  refine reflTransGen_iff (h.desc_refl u) ?_ ?_
  · rintro _ _ ⟨f, rfl, rfl⟩ ha
    exact h.desc_closed u f ha
  · intro w hw
    rcases h.desc_back u w hw with rfl | ⟨f, rfl, hf⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨src f, ⟨f, rfl, rfl⟩, hf, h.down f⟩

theorem Tables.avoidingReach_iff (h : Tables src tgt root desc avoid) {e : Fin m} {w : Fin k} :
    (net src tgt root lf).AvoidingReach e root w ↔ w ∈ avoid e := by
  refine reflTransGen_iff (h.avoid_root e) ?_ ?_
  · rintro _ _ ⟨f, hf, rfl, rfl⟩ ha
    exact h.avoid_closed e f hf ha
  · intro w hw
    rcases h.avoid_back e w hw with rfl | ⟨f, hfe, rfl, hf⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨src f, ⟨f, hfe, rfl, rfl⟩, hf, h.down f⟩

theorem Tables.isBelow_iff (h : Tables src tgt root desc avoid) {e : Fin m} {x : Fin t} :
    (net src tgt root lf).IsBelow e x ↔ lf x ∈ desc (tgt e) := h.reaches_iff

theorem Tables.dominates_iff (h : Tables src tgt root desc avoid) {e : Fin m} {x : Fin t} :
    (net src tgt root lf).Dominates e x ↔ lf x ∉ avoid e :=
  not_congr h.avoidingReach_iff

/-- `RDom` in a decidable form. -/
def RDomT (tgt : Fin m → Fin k) (lf : Fin t → Fin k) (desc : Fin k → Finset (Fin k))
    (avoid : Fin m → Finset (Fin k)) (a b c d : Fin t) : Prop :=
  ∃ g : Fin m, (lf a ∉ avoid g ∧ lf b ∉ avoid g ∧ lf c ∉ desc (tgt g) ∧ lf d ∉ desc (tgt g)) ∨
    (lf c ∉ avoid g ∧ lf d ∉ avoid g ∧ lf a ∉ desc (tgt g) ∧ lf b ∉ desc (tgt g))

instance (tgt : Fin m → Fin k) (lf : Fin t → Fin k) (desc : Fin k → Finset (Fin k))
    (avoid : Fin m → Finset (Fin k)) (a b c d : Fin t) : Decidable (RDomT tgt lf desc avoid a b c d) :=
  inferInstanceAs (Decidable (∃ g : Fin m,
    (lf a ∉ avoid g ∧ lf b ∉ avoid g ∧ lf c ∉ desc (tgt g) ∧ lf d ∉ desc (tgt g)) ∨
    (lf c ∉ avoid g ∧ lf d ∉ avoid g ∧ lf a ∉ desc (tgt g) ∧ lf b ∉ desc (tgt g))))

theorem Tables.rdom_iff (h : Tables src tgt root desc avoid) {a b c d : Fin t} :
    RDom (net src tgt root lf) a b c d ↔ RDomT tgt lf desc avoid a b c d := by
  simp only [RDom, h.dominates_iff, h.isBelow_iff]
  rfl

/-- A cut split of the network on all the taxa, in a decidable form. -/
def SepT (tgt : Fin m → Fin k) (lf : Fin t → Fin k) (desc : Fin k → Finset (Fin k))
    (avoid : Fin m → Finset (Fin k)) (A : Finset (Fin t)) : Prop :=
  ∃ e : Fin m, (A.Nonempty ∧ (∀ x ∈ A, lf x ∉ avoid e) ∧ ∀ x ∉ A, lf x ∉ desc (tgt e)) ∨
    (Aᶜ.Nonempty ∧ (∀ x ∉ A, lf x ∉ avoid e) ∧ ∀ x ∈ A, lf x ∉ desc (tgt e))

instance (tgt : Fin m → Fin k) (lf : Fin t → Fin k) (desc : Fin k → Finset (Fin k))
    (avoid : Fin m → Finset (Fin k)) (A : Finset (Fin t)) : Decidable (SepT tgt lf desc avoid A) :=
  inferInstanceAs (Decidable (∃ e : Fin m,
    (A.Nonempty ∧ (∀ x ∈ A, lf x ∉ avoid e) ∧ ∀ x ∉ A, lf x ∉ desc (tgt e)) ∨
    (Aᶜ.Nonempty ∧ (∀ x ∉ A, lf x ∉ avoid e) ∧ ∀ x ∈ A, lf x ∉ desc (tgt e))))

theorem Tables.hasCutSplit_iff (h : Tables src tgt root desc avoid)
    (hN : (net src tgt root lf).IsPhylogenetic) {A : Finset (Fin t)} :
    (net src tgt root lf).HasCutSplit (A : Set (Fin t)) ↔ SepT tgt lf desc avoid A := by
  rw [hasCutSplit_iff_hasCutSplitOn_univ hN, hasCutSplitOn_iff_separates hN]
  have h₁ : (Set.univ ∩ (A : Set (Fin t))) = A := Set.univ_inter _
  have h₂ : (Set.univ \ (A : Set (Fin t))) = (A : Set (Fin t))ᶜ := (Set.compl_eq_univ_sdiff _).symm
  have hne : ((A : Set (Fin t))ᶜ).Nonempty ↔ Aᶜ.Nonempty := by
    rw [← Finset.coe_compl, Finset.coe_nonempty]
  rw [h₁, h₂]
  refine exists_congr fun e => ?_
  simp only [Separates, h.dominates_iff, h.isBelow_iff, Set.mem_compl_iff, Finset.mem_coe,
    Finset.coe_nonempty, hne]

theorem Tables.mem_treeOfBlobs_iff (h : Tables src tgt root desc avoid)
    (hN : (net src tgt root lf).IsPhylogenetic) {A : Finset (Fin t)} :
    A ∈ treeOfBlobs (net src tgt root lf) ↔ A.Nonempty ∧ Aᶜ.Nonempty ∧ SepT tgt lf desc avoid A := by
  rw [treeOfBlobs, mem_filter, h.hasCutSplit_iff hN]
  simp

/-- A network from tables is phylogenetic, if its arcs go down in the order of `Fin k`. -/
theorem isPhylogenetic_of_down (hdown : ∀ f, (tgt f).val < (src f).val) (h0 : ∀ e, tgt e ≠ root)
    (h1 : ∀ v, v ≠ root → ∃ e, tgt e = v) (hinj : Function.Injective lf)
    (hleaf : ∀ x, ∃ e, tgt e = lf x ∧ ∀ f, tgt f = lf x → f = e) (hs : ∀ x e, src e ≠ lf x)
    (hint : ∀ v, (∀ x, lf x ≠ v) → ∃ e, src e = v) : (net src tgt root lf).IsPhylogenetic :=
  isPhylogenetic_of_rank (N := net src tgt root lf) (fun v => k - v.val)
    (fun e => by
      have h₁ := hdown e
      have h₂ := (src e).isLt
      show k - (src e).val < k - (tgt e).val
      omega) h0 h1 hinj hleaf hs hint

end Tables

/-! ### Parent choices -/

section Choices

variable {k m t : ℕ} {N : RootedNetwork (Fin k) (Fin m) (Fin t)}

/-- An arc that is the only one entering its target is kept by every parent choice. -/
theorem notMem_deletedArcs_of_unique (c : N.ParentChoice) {g : Fin m}
    (hr : N.graph.target g ≠ N.root) (hg : ∀ f, N.graph.target f = N.graph.target g → f = g) :
    g ∉ N.deletedArcs c := by
  have := notMem_deletedArcs_choice c ⟨N.graph.target g, hr⟩
  rwa [hg _ (c ⟨N.graph.target g, hr⟩).property] at this

end Choices

/-! ### A binary network -/

namespace Binary

/-- The tails of the arcs: the vertices `0, …, 4` are the taxa `a, b, c, d, e`, and `5, …, 10` are the reticulation `h`, its
parents `u`, `v`, the top of the cycle `r`, the parent `w` of `d, e`, and the root `s`. The arcs are, in order, `sw`, `sr`, `wd`,
`we`, `ru`, `rv`, `ua`, `uh`, `vb`, `vh`, `hc`. -/
def src : Fin 11 → Fin 11 := ![10, 10, 9, 9, 8, 8, 6, 6, 7, 7, 5]

/-- The heads of the arcs. -/
def tgt : Fin 11 → Fin 11 := ![9, 8, 3, 4, 6, 7, 0, 5, 1, 5, 2]

/-- The taxa, as vertices. -/
def lf : Fin 5 → Fin 11 := ![0, 1, 2, 3, 4]

/-- What each vertex reaches. -/
def desc : Fin 11 → Finset (Fin 11) :=
  ![{0}, {1}, {2}, {3}, {4}, {2, 5}, {0, 2, 5, 6}, {1, 2, 5, 7}, {0, 1, 2, 5, 6, 7, 8}, {3, 4, 9},
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}]

/-- What the root reaches off each arc. -/
def avoid : Fin 11 → Finset (Fin 11) :=
  ![{0, 1, 2, 5, 6, 7, 8, 10}, {3, 4, 9, 10}, {0, 1, 2, 4, 5, 6, 7, 8, 9, 10},
    {0, 1, 2, 3, 5, 6, 7, 8, 9, 10}, {1, 2, 3, 4, 5, 7, 8, 9, 10}, {0, 2, 3, 4, 5, 6, 8, 9, 10},
    {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}, {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10},
    {0, 2, 3, 4, 5, 6, 7, 8, 9, 10}, {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10},
    {0, 1, 3, 4, 5, 6, 7, 8, 9, 10}]

theorem tables : Tables src tgt 10 desc avoid :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **The network**: the cut edge `de|abc`, and the 4-cycle `r, u, h, v` with the taxa `a` at `u`, `b` at `v` and `c` at `h`. -/
abbrev net : RootedNetwork (Fin 11) (Fin 11) (Fin 5) := FinNetwork.net src tgt 10 lf

theorem net_isPhylogenetic : net.IsPhylogenetic :=
  isPhylogenetic_of_down (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- It is binary. -/
theorem net_isBinary : net.IsBinary := by
  refine ⟨?_, fun w hw hout => ?_⟩
  · unfold DirectedMultigraph.outdegree
    rw [ncard_setOf_eq_card_filter (fun e => net.graph.source e = net.root)]
    decide
  · unfold DirectedMultigraph.outdegree at hout
    unfold DirectedMultigraph.indegree DirectedMultigraph.outdegree
    rw [ncard_setOf_eq_card_filter (fun e => net.graph.source e = w)] at hout
    rw [ncard_setOf_eq_card_filter (fun e => net.graph.target e = w), ncard_setOf_eq_card_filter (fun e => net.graph.source e = w)]
    revert w
    decide

/-- The sides of the tree of blobs. -/
theorem mem_treeOfBlobs_iff {A : Finset (Fin 5)} :
    A ∈ treeOfBlobs net ↔ A.card = 1 ∨ Aᶜ.card = 1 ∨ A = {3, 4} ∨ A = {0, 1, 2} := by
  rw [tables.mem_treeOfBlobs_iff net_isPhylogenetic]
  revert A
  decide

/-! #### Parent choices and displayed trees -/

/-- The parent arcs, with the parent `f` at the reticulation. -/
def parentOf (f : Fin 11) : Fin 11 → Fin 11 := ![6, 8, 10, 2, 3, f, 4, 5, 1, 0, 0]

/-- The parent choice that keeps `u → h`. -/
def choiceU : net.ParentChoice := fun w => ⟨parentOf 7 w.val, by
  obtain ⟨w, hw⟩ := w
  revert w
  decide⟩

/-- The parent choice that keeps `v → h`. -/
def choiceV : net.ParentChoice := fun w => ⟨parentOf 9 w.val, by
  obtain ⟨w, hw⟩ := w
  revert w
  decide⟩

variable {x : Fin 5}

/-- A parent choice that keeps `u → h` has the cherry `ac`. -/
theorem displays_of_uh {c : net.ParentChoice} (huh : (7 : Fin 11) ∉ net.deletedArcs c)
    (hx : x = 3 ∨ x = 4) (hc : ({0, 2, 1, x} : Finset (Fin 5)).card = 4) :
    Displays (net.displayedSides c) (quartetTree 0 2 1 x hc) := by
  have h₆ : (6 : Fin 11) ∉ net.deletedArcs c :=
    notMem_deletedArcs_of_unique c (by decide) (by decide)
  have h₁₀ : (10 : Fin 11) ∉ net.deletedArcs c :=
    notMem_deletedArcs_of_unique c (by decide) (by decide)
  refine displays_of_cluster (P := {0, 2}) (u := (6 : Fin 11)) (by simp) (fun y hy => ?_)
    (fun y hyt hyP hy => ?_)
  · rw [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.single ⟨6, h₆, rfl, rfl⟩)
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.head ⟨7, huh, rfl, rfl⟩
        (Relation.ReflTransGen.single ⟨10, h₁₀, rfl, rfl⟩))
  · have hr : lf y ∈ desc 6 := tables.reaches_iff.1 (mem_displayedCluster.1 hy).reaches
    rw [taxa_quartetTree] at hyt
    simp only [mem_insert, mem_singleton] at hyt hyP
    clear hy
    rcases hx with rfl | rfl <;> revert y <;> decide

/-- A parent choice that keeps `v → h` has the cherry `bc`. -/
theorem displays_of_vh {c : net.ParentChoice} (hvh : (9 : Fin 11) ∉ net.deletedArcs c)
    (hx : x = 3 ∨ x = 4) (hc : ({1, 2, 0, x} : Finset (Fin 5)).card = 4) :
    Displays (net.displayedSides c) (quartetTree 1 2 0 x hc) := by
  have h₈ : (8 : Fin 11) ∉ net.deletedArcs c :=
    notMem_deletedArcs_of_unique c (by decide) (by decide)
  have h₁₀ : (10 : Fin 11) ∉ net.deletedArcs c :=
    notMem_deletedArcs_of_unique c (by decide) (by decide)
  refine displays_of_cluster (P := {1, 2}) (u := (7 : Fin 11)) (by simp) (fun y hy => ?_)
    (fun y hyt hyP hy => ?_)
  · rw [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.single ⟨8, h₈, rfl, rfl⟩)
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.head ⟨9, hvh, rfl, rfl⟩
        (Relation.ReflTransGen.single ⟨10, h₁₀, rfl, rfl⟩))
  · have hr : lf y ∈ desc 7 := tables.reaches_iff.1 (mem_displayedCluster.1 hy).reaches
    rw [taxa_quartetTree] at hyt
    simp only [mem_insert, mem_singleton] at hyt hyP
    clear hy
    rcases hx with rfl | rfl <;> revert y <;> decide

/-- A parent choice keeps one of the two arcs into the reticulation. -/
theorem uh_or_vh (c : net.ParentChoice) :
    (7 : Fin 11) ∉ net.deletedArcs c ∨ (9 : Fin 11) ∉ net.deletedArcs c := by
  have hne := notMem_deletedArcs_choice c ⟨5, by decide⟩
  have ht : tgt (c ⟨5, by decide⟩).val = 5 := (c ⟨5, by decide⟩).property
  have hdec : ∀ f : Fin 11, tgt f = 5 → f = 7 ∨ f = 9 := by decide
  rcases hdec _ ht with h | h
  · exact Or.inl (h ▸ hne)
  · exact Or.inr (h ▸ hne)

theorem choiceU_keeps : (7 : Fin 11) ∉ net.deletedArcs choiceU :=
  notMem_deletedArcs_choice choiceU ⟨5, by decide⟩

theorem choiceV_keeps : (9 : Fin 11) ∉ net.deletedArcs choiceV :=
  notMem_deletedArcs_choice choiceV ⟨5, by decide⟩

end Binary

end ECToBlob.FinNetwork
end
