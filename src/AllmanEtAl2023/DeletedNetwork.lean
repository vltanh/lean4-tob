module

public import AllmanEtAl2023.Theorem1a
public import AllmanEtAl2023.Reduction
public import Phylogenetics.NMSC.Witness
public import Phylogenetics.Network.DeletedArcs

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the networks `𝒩ᵢ⁺` of the proof of Theorem 1 (b)

"Consider deleting one of the `kᵢ` from `𝒩⁺` and with it all edges from which the only directed path to a taxon leads through `kᵢ`, suppressing any degree-2 nodes." Here, for a set `D` of hybrid arcs:

* `offNetwork`: the subnetwork `Nᵢ` of what still reaches a taxon off `D`;
* `deleted`: the network `𝒩ᵢ⁺`: suppress the nodes of in- and out-degree 1 and remove a stem, as in Definition 6.

**Gap of the paper, minor.** "Suppressing any degree-2 nodes" is not enough: a root may lose a child, and then it has out-degree 1, and in `𝒩⁺` a node of in-degree 0 and out-degree 1 is not allowed. For example, on the 4-cycle with arcs `r → v`, `r → x`, `x → b`, `x → y`, `y → c`, `y → z`, `z → d`, `z → v`, `v → a`, deleting `r → v` leaves the root with out-degree 1. Step 3 of Definition 6, which removes a stem, is what is needed (`removeStem`). The `CF`s are unaffected (`nmscCF_removeStem`).

The theorems, in the order the proof needs them:

* `offNetwork_isPhylogenetic`, `deleted_isPhylogenetic`, `deleted_isBinaryNetwork`: it is a network of Definition 1;
* `geneTreeDist_offNetwork`, `nmscCF_deleted`: at inheritance `0` on `D`, the `CF`s of `𝒩⁺` are those of `𝒩ᵢ⁺`;
* `deleted_hasCutSplit_iff`, `deleted_inducedCutSplit_iff`: its cut-edge splits are those of the library's `SplitOffAt`;
* `isMetric_deletedParams`, `exists_deleted_lift`: the map of parameters, and that it is onto.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*}

/-! ### The subnetwork -/

section Off

variable (N : RootedNetwork V E X) (D : Set E)

/-- The nodes from which a directed path to a taxon avoids `D`. -/
def offVertices : Set V := {v | ∃ x, N.ReachesOff D v (N.leaf x)}

/-- The arcs off `D` whose child reaches a taxon off `D`: "deleting ... with it all edges from which the only directed path to a taxon leads through `kᵢ`". This is `arcsAbove` on all the taxa. -/
abbrev offArcs : Set E := arcsAbove N D Set.univ

variable {N D}

theorem mem_offArcs_iff {e : E} : e ∈ offArcs N D ↔ e ∉ D ∧ N.graph.target e ∈ offVertices N D := by
  simp [arcsAbove, offVertices]

theorem root_mem_offVertices (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) [Nonempty X] : N.root ∈ offVertices N D := by
  obtain ⟨x⟩ := ‹Nonempty X›
  exact ⟨x, hD.root_reachesOff hN _⟩

theorem source_mem_offVertices {e : E} (he : e ∈ offArcs N D) : N.graph.source e ∈ offVertices N D := by
  obtain ⟨hD, x, -, hx⟩ := he
  exact ⟨x, ReachesOff.head_arc hD hx⟩

variable (N D)

/-- **The subnetwork `Nᵢ`**: what still reaches a taxon off `D`, with vertices of in- and out-degree 1 not yet suppressed. -/
def offNetwork (hroot : N.root ∈ offVertices N D) : RootedNetwork (offVertices N D) (offArcs N D) X where
  graph :=
    { source := fun e => ⟨N.graph.source e.1, source_mem_offVertices e.2⟩
      target := fun e => ⟨N.graph.target e.1, (mem_offArcs_iff.1 e.2).2⟩ }
  root := ⟨N.root, hroot⟩
  leaf x := ⟨N.leaf x, x, .refl⟩

/-- The parameters of `Nᵢ`: those of the same arcs. -/
def offParams (θ : MetricData E) : MetricData (offArcs N D) where
  length e := θ.length e.1
  inheritance e := θ.inheritance e.1

variable {N D}

/-- A path off `D` that ends in `Nᵢ` is a path of `Nᵢ`. -/
theorem reaches_offNetwork_of_reachesOff {hroot : N.root ∈ offVertices N D} {u w : V} (h : N.ReachesOff D u w) (hw : w ∈ offVertices N D) :
    ∃ hu : u ∈ offVertices N D, (offNetwork N D hroot).graph.Reaches ⟨u, hu⟩ ⟨w, hw⟩ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨hw, .refl⟩
  | @head a b hab _ ih =>
    obtain ⟨f, hf, rfl, rfl⟩ := hab
    obtain ⟨hb, hr⟩ := ih
    exact ⟨source_mem_offVertices (mem_offArcs_iff.2 ⟨hf, hb⟩), Relation.ReflTransGen.head ⟨⟨f, mem_offArcs_iff.2 ⟨hf, hb⟩⟩, rfl, rfl⟩ hr⟩

/-- A path of `Nᵢ` is a path off `D`. -/
theorem reachesOff_of_reaches_offNetwork {hroot : N.root ∈ offVertices N D} {u w : offVertices N D} (h : (offNetwork N D hroot).graph.Reaches u w) :
    N.ReachesOff D u.1 w.1 := by
  induction h with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    obtain ⟨f, rfl, rfl⟩ := hab
    exact ih.tail ⟨f.1, f.2.1, rfl, rfl⟩

/-- **The subnetwork `Nᵢ` obeys the laws of a network.** -/
theorem offNetwork_isPhylogenetic (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) (hroot : N.root ∈ offVertices N D) : (offNetwork N D hroot).IsPhylogenetic := by
  have : Finite V := hN.finite_vertices
  have : Finite E := hN.finite_arcs
  have hparent : ∀ x, ∃ g, g ∉ D ∧ N.graph.target g = N.leaf x ∧ ∀ f, N.graph.target f = N.leaf x → f = g := by
    intro x
    obtain ⟨g, hg⟩ := (N.graph.indegree_eq_one_iff _).mp (hN.leaf_indegree x)
    obtain ⟨f, hf, hfx⟩ := hD.parent (N.leaf x) (N.leaf_ne_root hN x)
    have hfg := (hg f).mp hfx
    exact ⟨g, hfg ▸ hf, (hg g).mpr rfl, fun f' hf' => (hg f').mp hf'⟩
  refine ⟨inferInstance, inferInstance, hN.finite_taxa, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    refine hN.acyclic v.1 (Relation.TransGen.lift Subtype.val ?_ v v hv)
    rintro a b ⟨e, hs, ht⟩
    exact ⟨e.1, congrArg Subtype.val hs, congrArg Subtype.val ht⟩
  · intro v
    obtain ⟨_, hr⟩ := reaches_offNetwork_of_reachesOff (hroot := hroot) (hD.root_reachesOff hN v.1) v.2
    exact hr
  · rw [DirectedMultigraph.indegree_eq_zero_iff]
    intro e he
    exact target_ne_root hN e.1 (congrArg Subtype.val he)
  · intro v hv
    rw [DirectedMultigraph.one_le_indegree_iff]
    have hv1 : v.1 ≠ N.root := fun h => hv (Subtype.ext h)
    obtain ⟨f, hf, hfv⟩ := hD.parent v.1 hv1
    exact ⟨⟨f, mem_offArcs_iff.2 ⟨hf, hfv ▸ v.2⟩⟩, Subtype.ext hfv⟩
  · intro x y h
    exact hN.leaf_injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨g, hgD, hgx, huniq⟩ := hparent x
    have hgm : g ∈ offArcs N D := ⟨hgD, x, Set.mem_univ x, hgx ▸ .refl⟩
    refine (DirectedMultigraph.indegree_eq_one_iff _ _).mpr ⟨⟨g, hgm⟩, fun f => ⟨fun hf => ?_, ?_⟩⟩
    · exact Subtype.ext (huniq f.1 (congrArg Subtype.val hf))
    · rintro rfl
      exact Subtype.ext hgx
  · intro v
    have hsink : ∀ x (e : E), N.graph.source e ≠ N.leaf x := fun x =>
      (N.graph.outdegree_eq_zero_iff _).mp ((hN.leaves _).mpr ⟨x, rfl⟩)
    constructor
    · intro h0
      have hno := ((offNetwork N D hroot).graph.outdegree_eq_zero_iff v).mp h0
      obtain ⟨x, hx⟩ := v.2
      refine ⟨x, Subtype.ext ?_⟩
      by_contra hne
      obtain ⟨f, hf, hs, hr⟩ := hx.exists_first (Ne.symm hne)
      exact hno ⟨f, hf, x, Set.mem_univ x, hr⟩ (Subtype.ext hs)
    · rintro ⟨x, rfl⟩
      rw [DirectedMultigraph.outdegree_eq_zero_iff]
      intro e he
      exact hsink x e.1 (congrArg Subtype.val he)

end Off

/-! ### The allocation, with parents of inheritance `0` -/

section Allocation

variable {V E X : Type*} [Fintype E] [Fintype X] [DecidableEq X]

/-- `Fintype.sum_of_injective`, with its instances found by unification. -/
theorem sum_of_injective' {ι κ : Type*} (i₁ : Fintype ι) (i₂ : Fintype κ) (e : ι → κ) (he : Function.Injective e) (f : ι → ℝ) (g : κ → ℝ) (h' : ∀ j, j ∉ Set.range e → g j = 0)
    (h : ∀ i, f i = g (e i)) : (∑ i, f i) = ∑ j, g j :=
  Fintype.sum_of_injective e he f g h' h

/-- `Finset.mem_erase`, for any instance. -/
theorem mem_erase_of_ne' {α : Type*} {i : DecidableEq α} {s : Finset α} {a b : α} (h : a ≠ b) (hs : a ∈ s) : a ∈ @Finset.erase α i s b :=
  Finset.mem_erase.mpr ⟨h, hs⟩

/-- `if_congr`, with its instances found by unification. -/
theorem ite_congr' {α : Type*} {p q : Prop} (i₁ : Decidable p) (i₂ : Decidable q) {a b c d : α} (h : p ↔ q) (h₁ : a = c) (h₂ : b = d) :
    @ite _ p i₁ a b = @ite _ q i₂ c d := by
  subst h₁ h₂
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left (h.mp hp)]
  · rw [ite_eq_right hp, ite_eq_right (fun hq => hp (h.mpr hq))]

/-- `allocationWeight` does not see parents that are not used. -/
theorem allocationWeight_embedding_comp {R P P' : Type*} [Fintype R] (iP : Fintype P) (iP' : Fintype P') (dP : DecidableEq P) (dP' : DecidableEq P') (σ : P' ↪ P) (ρ : ℝ) (γ : P → ℝ) (a : R → P') :
    allocationWeight ρ γ (σ ∘ a) = allocationWeight ρ (γ ∘ σ) a := by
  have him : univ.image (σ ∘ a) = (univ.image a).map σ := by
    ext e
    simp only [mem_image, mem_univ, true_and, Function.comp, mem_map]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨a r, ⟨r, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, rfl⟩
  unfold allocationWeight
  rw [him, card_map, prod_map]
  simp

variable {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ} {D : Set E}

/-- A history of `Nᵢ`, on the arcs of `𝒩⁺`: nothing on the other arcs. -/
def liftOff {α : Type*} (b : offArcs N D → Finset α) (e : E) : Finset α := if h : e ∈ offArcs N D then b ⟨e, h⟩ else ∅

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem liftOff_of_mem {α : Type*} (b : offArcs N D → Finset α) (e : offArcs N D) : liftOff b e.1 = b e := by
  unfold liftOff
  exact dite_eq_left_of_eq_true (eq_true e.2)

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem liftOff_of_notMem {α : Type*} (b : offArcs N D → Finset α) {e : E} (h : e ∉ offArcs N D) : liftOff b e = ∅ := by
  unfold liftOff
  exact dite_eq_right_of_eq_false (eq_false h)

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem liftOff_injective {α : Type*} : Function.Injective (liftOff (N := N) (D := D) (α := α)) := fun b b' h => by
  funext e
  have := congrFun h e.1
  rwa [liftOff_of_mem, liftOff_of_mem] at this

variable [Fintype (offArcs N D)]

/-- **The allocation at a node of `Nᵢ`.** A parent in `D` has inheritance `0`, so no root takes it. -/
theorem allocationFactor_offNetwork (hroot : N.root ∈ offVertices N D) (hD0 : ∀ f ∈ D, θ.inheritance f = 0) (F : Finset (Finset X)) (v : offVertices N D)
    (b : offArcs N D → Finset (Finset X)) :
    allocationFactor (offNetwork N D hroot) (offParams N D θ) ρ F v b = allocationFactor N θ ρ F v.1 (liftOff b) := by
  let σ : {e // (offNetwork N D hroot).graph.target e = v} ↪ {e // N.graph.target e = v.1} :=
    ⟨fun e => ⟨e.1.1, congrArg Subtype.val e.2⟩, fun e e' h => Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h))⟩
  have hmem : ∀ e : {e // N.graph.target e = v.1}, (∃ e₁, σ e₁ = e) ∨ e.1 ∉ offArcs N D := by
    intro e
    by_cases he : e.1 ∈ offArcs N D
    · exact Or.inl ⟨⟨⟨e.1, he⟩, Subtype.ext e.2⟩, rfl⟩
    · exact Or.inr he
  have hin : ∀ e : {e // N.graph.target e = v.1}, e.1 ∉ offArcs N D → e.1 ∈ D := fun e he => by
    by_contra hD
    exact he (mem_offArcs_iff.2 ⟨hD, by rw [e.2]; exact v.2⟩)
  unfold allocationFactor
  refine sum_of_injective' _ _ (fun a => σ ∘ a) (fun a a' h => funext fun r => σ.injective (congrFun h r)) _ _ (fun a ha => ?_) fun a => ?_
  · -- an allocation with a root taking an arc of `D` has weight `0`
    have hex : ∃ r, a r ∉ Set.range σ := by
      by_contra hall
      push Not at hall
      choose a₁ ha₁ using hall
      exact ha ⟨a₁, funext ha₁⟩
    obtain ⟨r, hr⟩ := hex
    have hrD : (a r).1 ∈ D := by
      rcases hmem (a r) with h | h
      · exact absurd h hr
      · exact hin _ h
    have h0 : allocationWeight ρ (fun e : {e // N.graph.target e = v.1} => θ.inheritance e.val) a = 0 :=
      allocationWeight_eq_zero_of_apply a r (hD0 _ hrD)
    rw [h0]
    simp
  · refine ite_congr' _ _ ⟨fun h e => ?_, fun h e => ?_⟩ ?_ rfl
    · rcases hmem e with ⟨e₁, rfl⟩ | he
      · have hb : liftOff b (σ e₁).1 = b e₁.1 := liftOff_of_mem b e₁.1
        rw [hb, h e₁]
        congr 2
        ext r
        simp [σ.injective.eq_iff]
      · rw [liftOff_of_notMem b he]
        ext A
        simp only [notMem_empty, false_iff, mem_forestBelow, not_and, not_exists]
        rintro - C hC
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hC
        have hre : σ (a r) = e := (Finset.mem_filter.mp hr).2
        exact absurd (hre ▸ (a r).1.2) he
    · have hb : liftOff b (σ e).1 = b e.1 := liftOff_of_mem b e.1
      rw [← hb, h (σ e)]
      congr 2
      ext r
      simp [σ.injective.eq_iff]
    · exact (allocationWeight_embedding_comp _ _ _ _ σ ρ (fun e : {e // N.graph.target e = v.1} => θ.inheritance e.val) a).symm

/-- **The forest arriving at a node of `Nᵢ`.** -/
theorem arrivingForest_offNetwork (hroot : N.root ∈ offVertices N D) (t : offArcs N D → Finset (Finset X)) (v : offVertices N D) :
    arrivingForest (offNetwork N D hroot) t v = arrivingForest N (liftOff t) v.1 := by
  ext A
  simp only [arrivingForest, mem_union, mem_image, mem_filter, mem_univ, true_and, mem_biUnion]
  refine or_congr ?_ ?_
  · constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, congrArg Subtype.val hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subtype.ext hx, rfl⟩
  · constructor
    · rintro ⟨e, he, hA⟩
      exact ⟨e.1, congrArg Subtype.val he, by rwa [liftOff_of_mem]⟩
    · rintro ⟨e, he, hA⟩
      by_cases hm : e ∈ offArcs N D
      · rw [liftOff_of_mem t ⟨e, hm⟩] at hA
        exact ⟨⟨e, hm⟩, Subtype.ext he, hA⟩
      · rw [liftOff_of_notMem t hm] at hA
        exact absurd hA (notMem_empty _)

omit [Fintype (offArcs N D)] in
/-- Nothing arrives at a node off `Nᵢ`. -/
theorem arrivingForest_of_notMem (t : offArcs N D → Finset (Finset X)) {v : V} (hv : v ∉ offVertices N D) :
    arrivingForest N (liftOff t) v = ∅ := by
  ext A
  simp only [arrivingForest, mem_union, mem_image, mem_filter, mem_univ, true_and, mem_biUnion, notMem_empty, iff_false, not_or, not_exists, not_and]
  refine ⟨fun x hx _ => hv ⟨x, hx ▸ .refl⟩, fun e he hA => ?_⟩
  have hm : e ∉ offArcs N D := fun hm => hv (he ▸ source_mem_offVertices hm)
  rw [liftOff_of_notMem t hm] at hA
  exact notMem_empty _ hA

omit [Fintype (offArcs N D)] in
/-- **On a history of nonzero weight, the arcs off `Nᵢ` are empty**, at inheritance `0` on `D`. -/
theorem support_off [Fintype V] (hN : N.IsPhylogenetic) (hD0 : ∀ f ∈ D, θ.inheritance f = 0) {bot top : E → Finset (Finset X)} (h : historyWeight N θ ρ bot top ≠ 0) {f : E}
    (hf : f ∉ offArcs N D) : bot f = ∅ ∧ top f = ∅ := by
  rw [historyWeight_eq_injWeight hN] at h
  unfold injWeight at h
  have hDn := downClosed_erase_root (N := N) hN
  have hfm : N.graph.target f ∈ univ.erase N.root := mem_erase.2 ⟨target_ne_root hN f, mem_univ _⟩
  have hF := frontier_of_prod_ne_zero hN (validInj_taxaInj univ) hDn h
  have hgt := hF.good_top f hfm
  have hgb := hF.good_bot f hfm
  have hw : vertexWeight N θ ρ (taxaInj N univ) (N.graph.target f) bot top ≠ 0 := prod_ne_zero_iff.1 h _ hfm
  have hK : kingmanTransition (θ.length f) (bot f) (top f) ≠ 0 := prod_ne_zero_iff.1 (right_ne_zero_of_mul hw) f (mem_arcsInto.2 rfl)
  have hlin : lineages (top f) = lineages (bot f) := (kingmanTransition_support_good hgb hK).2.2
  have hempty : lineages (top f) = ∅ := by
    refine eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨hfD, u, hu, hxu⟩ := notMem_and_reachesOff_of_mem_lineages_top hN (validInj_taxaInj univ) hD0 hDn h hfm hx
    obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxu
    exact hf ⟨hfD, x, Set.mem_univ x, hu⟩
  constructor
  · refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx⟩ := hgb.1.1 A hA
    have : x ∈ lineages (top f) := hlin ▸ mem_lineages.2 ⟨A, hA, hx⟩
    rw [hempty] at this
    exact notMem_empty _ this
  · refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx⟩ := hgt.1.1 A hA
    have : x ∈ lineages (top f) := mem_lineages.2 ⟨A, hA, hx⟩
    rw [hempty] at this
    exact notMem_empty _ this

end Allocation

/-! ### The gene tree distribution -/

section GeneTree

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ} {D : Set E}
  [Fintype (offVertices N D)] [Fintype (offArcs N D)]

/-- **At inheritance `0` on `D`, the gene tree distribution is that of the subnetwork `Nᵢ`**: "set `γᵢ = 0` and lengths for the removed edges to be arbitrary, so that we effectively consider a network with one fewer hybrid nodes". A history of
nonzero weight has nothing on the arcs off `Nᵢ` (`support_off`), the allocation sees parents of inheritance `0` only with weight `0` (`allocationFactor_offNetwork`), and nothing happens on the other arcs. -/
theorem geneTreeDist_offNetwork (hN : N.IsPhylogenetic) (hroot : N.root ∈ offVertices N D) (hD0 : ∀ f ∈ D, θ.inheritance f = 0) (G : Finset (Finset X)) :
    geneTreeDist (offNetwork N D hroot) (offParams N D θ) ρ G = geneTreeDist N θ ρ G := by
  -- a history lifted
  have hH : ∀ b t : offArcs N D → Finset (Finset X), historyWeight (offNetwork N D hroot) (offParams N D θ) ρ b t = historyWeight N θ ρ (liftOff b) (liftOff t) := by
    intro b t
    unfold historyWeight
    congr 1
    · -- the vertices
      have hval : (∏ v ∈ @Finset.erase _ (fun a b => Classical.propDecidable (a = b)) univ (offNetwork N D hroot).root,
            allocationFactor (offNetwork N D hroot) (offParams N D θ) ρ (arrivingForest (offNetwork N D hroot) t v) v b) =
          ∏ v ∈ ((@Finset.erase _ (fun a b => Classical.propDecidable (a = b)) univ (offNetwork N D hroot).root).image Subtype.val),
            allocationFactor N θ ρ (arrivingForest N (liftOff t) v) v (liftOff b) := by
        rw [prod_image fun _ _ _ _ h => Subtype.ext h]
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [allocationFactor_offNetwork hroot hD0, arrivingForest_offNetwork]
      refine Eq.trans (Finset.prod_congr (by ext v; simp) fun _ _ => rfl) (hval.trans ?_)
      refine Finset.prod_subset (fun v hv => ?_) fun v hv hvn => ?_
      · obtain ⟨u, hu, rfl⟩ := mem_image.1 hv
        exact mem_erase.2 ⟨fun h => ne_of_mem_erase' hu (Subtype.ext h), mem_univ _⟩
      · have hdead : v ∉ offVertices N D := fun ha => hvn (mem_image.2 ⟨⟨v, ha⟩,
          mem_erase_of_ne' (fun h => ne_of_mem_erase' hv (congrArg Subtype.val h)) (mem_univ _), rfl⟩)
        rw [arrivingForest_of_notMem t hdead]
        exact allocationFactor_empty_eq_one fun e he => liftOff_of_notMem b fun hm => hdead (he ▸ (mem_offArcs_iff.1 hm).2)
    · -- the arcs
      have hval : (∏ e, kingmanTransition ((offParams N D θ).length e) (b e) (t e)) =
          ∏ e ∈ (univ : Finset (offArcs N D)).image Subtype.val, kingmanTransition (θ.length e) (liftOff b e) (liftOff t e) := by
        rw [prod_image fun _ _ _ _ h => Subtype.ext h]
        refine Finset.prod_congr rfl fun e _ => ?_
        rw [liftOff_of_mem, liftOff_of_mem]
        rfl
      rw [hval]
      refine Finset.prod_subset (subset_univ _) fun e _ he => ?_
      have hm : e ∉ offArcs N D := fun hm => he (mem_image.2 ⟨⟨e, hm⟩, mem_univ _, rfl⟩)
      rw [liftOff_of_notMem b hm, liftOff_of_notMem t hm, kingmanTransition_of_card_roots_le_one isForest_empty (by simp), ite_eq_left rfl]
  -- the root
  have hA : ∀ t : offArcs N D → Finset (Finset X), arrivingForest (offNetwork N D hroot) t (offNetwork N D hroot).root = arrivingForest N (liftOff t) N.root := fun t =>
    arrivingForest_offNetwork hroot t _
  unfold geneTreeDist
  simp only [hH, hA]
  refine sum_of_injective' _ _ liftOff liftOff_injective _ _ (fun bot hbot => ?_) fun b => ?_
  · refine Finset.sum_eq_zero fun top _ => ?_
    by_cases hw : historyWeight N θ ρ bot top = 0
    · rw [hw, zero_mul]
    · exfalso
      refine hbot ⟨fun e => bot e.1, funext fun e => ?_⟩
      by_cases hm : e ∈ offArcs N D
      · exact liftOff_of_mem (fun e => bot e.1) ⟨e, hm⟩
      · rw [liftOff_of_notMem _ hm, (support_off hN hD0 hw hm).1]
  · refine sum_of_injective' _ _ liftOff liftOff_injective _ _ (fun top htop => ?_) fun _ => rfl
    by_cases hw : historyWeight N θ ρ (liftOff b) top = 0
    · rw [hw, zero_mul]
    · exfalso
      refine htop ⟨fun e => top e.1, funext fun e => ?_⟩
      by_cases hm : e ∈ offArcs N D
      · exact liftOff_of_mem (fun e => top e.1) ⟨e, hm⟩
      · rw [liftOff_of_notMem _ hm, (support_off hN hD0 hw hm).2]

/-- **At inheritance `0` on `D`, the `CF`s are those of the subnetwork `Nᵢ`.** -/
theorem nmscCF_offNetwork (hN : N.IsPhylogenetic) (hroot : N.root ∈ offVertices N D) (hD0 : ∀ f ∈ D, θ.inheritance f = 0) (s : QuartetTree X) :
    nmscCF (offNetwork N D hroot) (offParams N D θ) ρ s = nmscCF N θ ρ s := by
  unfold nmscCF
  simp only [geneTreeDist_offNetwork hN hroot hD0]

end GeneTree

/-! ### The parameters of the subnetwork -/

section Params

variable {V E X : Type*} {N : RootedNetwork V E X} {D : Set E} {θ : MetricData E}

/-- An arc off `D` into a node of `Nᵢ` is an arc of `Nᵢ`. -/
theorem mem_offArcs_of_target {e : E} {v : offVertices N D} (he : N.graph.target e = v.1) (heD : e ∉ D) : e ∈ offArcs N D :=
  mem_offArcs_iff.2 ⟨heD, he ▸ v.2⟩

variable [Fintype E] [Fintype (offArcs N D)]

/-- The sum of the inheritance into a node of `Nᵢ`: the other parents are in `D`, of inheritance `0`. -/
theorem sum_offParams_inheritance {hroot : N.root ∈ offVertices N D} (hD0 : ∀ f ∈ D, θ.inheritance f = 0) (v : offVertices N D) :
    (∑ e, @ite _ ((offNetwork N D hroot).graph.target e = v) (Classical.propDecidable _) ((offParams N D θ).inheritance e) 0) =
      ∑ e, if N.graph.target e = v.1 then θ.inheritance e else 0 := by
  refine sum_of_injective' _ _ Subtype.val Subtype.val_injective _ _ (fun e he => ?_) fun e => ?_
  · by_cases ht : N.graph.target e = v.1
    · rw [ite_eq_left ht]
      refine hD0 e ?_
      by_contra heD
      exact he ⟨⟨e, mem_offArcs_of_target ht heD⟩, rfl⟩
    · exact ite_eq_right ht
  · refine ite_congr' _ _ ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩ rfl rfl

omit [Fintype (offArcs N D)] in
/-- The indegree of a node of `Nᵢ` is at most that of the node. -/
theorem offNetwork_indegree_le {hroot : N.root ∈ offVertices N D} (v : offVertices N D) : (offNetwork N D hroot).graph.indegree v ≤ N.graph.indegree v.1 := by
  refine Set.ncard_le_ncard_of_injOn (f := Subtype.val) (t := {e | N.graph.target e = v.1}) (fun e he => congrArg Subtype.val he) (fun _ _ _ _ h => Subtype.ext h) (Set.toFinite _)

omit [Fintype (offArcs N D)] in
/-- The outdegree of a node of `Nᵢ` is at most that of the node. -/
theorem offNetwork_outdegree_le {hroot : N.root ∈ offVertices N D} (v : offVertices N D) : (offNetwork N D hroot).graph.outdegree v ≤ N.graph.outdegree v.1 := by
  refine Set.ncard_le_ncard_of_injOn (f := Subtype.val) (t := {e | N.graph.source e = v.1}) (fun e he => congrArg Subtype.val he) (fun _ _ _ _ h => Subtype.ext h) (Set.toFinite _)

/-- **The parameters of `Nᵢ` are normalized**, at inheritance `0` on `D`. -/
theorem isNormalized_offParams {hroot : N.root ∈ offVertices N D} (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hD0 : ∀ f ∈ D, θ.inheritance f = 0) :
    (offNetwork N D hroot).IsNormalized (offParams N D θ) := by
  have hle : ∀ v : offVertices N D, 2 ≤ (offNetwork N D hroot).graph.indegree v → 2 ≤ N.graph.indegree v.1 := fun v hv => hv.trans (offNetwork_indegree_le v)
  refine ⟨fun e he => ?_, fun v hv => (sum_offParams_inheritance hD0 v).trans (hθ.2 v.1 (hle v hv))⟩
  obtain ⟨g, hg⟩ := ((offNetwork N D hroot).graph.indegree_eq_one_iff _).mp he
  have heg : e = g := (hg e).mp rfl
  subst heg
  by_cases htree : N.IsTreeArc e.1
  · exact hθ.1 _ htree
  · -- the other parents are in `D`
    have hhyb : 2 ≤ N.graph.indegree (N.graph.target e.1) := by
      have h1 := hN.nonroot_indegree _ (target_ne_root hN e.1)
      unfold IsTreeArc at htree
      omega
    have hsum := hθ.2 _ hhyb
    rw [← Finset.sum_filter] at hsum
    have hone : ∑ a ∈ Finset.univ.filter (fun a => N.graph.target a = N.graph.target e.1), θ.inheritance a = θ.inheritance e.1 := by
      refine Finset.sum_eq_single_of_mem e.1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩) fun f hf hne => hD0 f ?_
      by_contra hfD
      have hft : N.graph.target f = N.graph.target e.1 := (Finset.mem_filter.1 hf).2
      have hm : f ∈ offArcs N D := mem_offArcs_iff.2 ⟨hfD, hft ▸ (mem_offArcs_iff.1 e.2).2⟩
      exact hne (congrArg Subtype.val ((hg ⟨f, hm⟩).mp (Subtype.ext hft)))
    exact hone.symm.trans hsum

end Params

/-! ### The network `𝒩ᵢ⁺` -/

section Deleted

variable {V E X : Type*} [Nontrivial X] {N : RootedNetwork V E X} {D : Set E}

variable (hN : IsBinaryNetwork N) (hD : N.IsDeletion D)

include hN hD in
theorem root_mem_offVertices' : N.root ∈ offVertices N D := root_mem_offVertices hN.isPhylogenetic hD

/-- `Nᵢ`, for a network of Definition 1. -/
def offNet : RootedNetwork (offVertices N D) (offArcs N D) X := offNetwork N D (root_mem_offVertices' hN hD)

theorem offNet_isPhylogenetic : (offNet hN hD).IsPhylogenetic := offNetwork_isPhylogenetic hN.isPhylogenetic hD _

/-- `Nᵢ` with its vertices of in- and out-degree 1 suppressed. -/
abbrev offSuppressed := (offNet hN hD).suppress (offNet_isPhylogenetic hN hD)

theorem offSuppressed_isPhylogenetic : (offSuppressed hN hD).IsPhylogenetic := suppress_isPhylogenetic _

/-- **The network `𝒩ᵢ⁺` of the proof of Theorem 1 (b)**: "by suppressing degree-2 nodes give phylogenetic networks". As step 3 of Definition 6, a stem is removed as well, which the paper does not mention (see the head of this file). -/
def deleted := removeStem (offSuppressed hN hD) (offSuppressed_isPhylogenetic hN hD)

theorem deleted_isPhylogenetic : (deleted hN hD).IsPhylogenetic := removeStem_isPhylogenetic _

/-- **`𝒩ᵢ⁺` is a network of Definition 1.** -/
theorem deleted_isBinaryNetwork : IsBinaryNetwork (deleted hN hD) := by
  have hP := hN.isPhylogenetic
  have hB := hN.isBinary
  have : Finite E := hP.finite_arcs
  have hR := offNet_isPhylogenetic hN hD
  have : Fintype E := Fintype.ofFinite E
  have : Fintype (offArcs N D) := Fintype.ofFinite _
  refine isBinaryNetwork_suppressStem hR ((offNetwork_outdegree_le _).trans hB.1.le) fun v hv hnc h0 => ?_
  have hv1 : v.1 ≠ N.root := fun h => hv (Subtype.ext h)
  have hin₁ : (offNet hN hD).graph.indegree v ≤ N.graph.indegree v.1 := offNetwork_indegree_le _
  have hout₁ : (offNet hN hD).graph.outdegree v ≤ N.graph.outdegree v.1 := offNetwork_outdegree_le _
  have h1 := hR.nonroot_indegree _ hv
  have h3 := hB.2 v.1 hv1 (by omega)
  have h4 := hP.nonroot_indegree _ hv1
  have hnc' : ¬ ((offNet hN hD).graph.indegree v = 1 ∧ (offNet hN hD).graph.outdegree v = 1) := hnc
  omega

variable [Fintype E]

/-- **The map of parameters to `𝒩ᵢ⁺`**: restrict, add lengths along a suppressed path, and forget the stem. -/
def deletedParams (θ : MetricData E) : MetricData {e // ¬ (HasStem (offSuppressed hN hD) ∧ (offSuppressed hN hD).graph.source e = (offSuppressed hN hD).root)} :=
  have : Fintype (offArcs N D) := Fintype.ofFinite _
  stemMetric (offSuppressed hN hD) ((offNet hN hD).suppressMetric (offParams N D θ))

end Deleted

/-! ### The concordance factors of `𝒩ᵢ⁺` -/

section DeletedCF

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] [Nontrivial X] {N : RootedNetwork V E X} {D : Set E} {θ : MetricData E} {ρ : ℝ}

/-- **"Set `γᵢ = 0` ..., so that we effectively consider a network with one fewer hybrid nodes"**: at inheritance `0` on `D`, the concordance factors of `𝒩⁺` are those of `𝒩ᵢ⁺`. -/
theorem nmscCF_deleted (hN : IsBinaryNetwork N) (hD : N.IsDeletion D) (hθ : N.IsNormalized θ) (hD0 : ∀ f ∈ D, θ.inheritance f = 0) (hρ : 0 ≤ ρ)
    [Fintype {v // ¬ (HasStem (offSuppressed hN hD) ∧ v = (offSuppressed hN hD).root)}]
    [Fintype {e // ¬ (HasStem (offSuppressed hN hD) ∧ (offSuppressed hN hD).graph.source e = (offSuppressed hN hD).root)}] (s : QuartetTree X) :
    nmscCF (deleted hN hD) (deletedParams hN hD θ) ρ s = nmscCF N θ ρ s := by
  let _ : Fintype (offVertices N D) := Fintype.ofFinite _
  let _ : Fintype (offArcs N D) := Fintype.ofFinite _
  let _ : Fintype {v // ¬ (offNet hN hD).IsChainVertex v} := Fintype.ofFinite _
  let _ : Fintype {e // ¬ (offNet hN hD).IsChainVertex ((offNet hN hD).graph.source e)} := Fintype.ofFinite _
  have hR := offNet_isPhylogenetic hN hD
  have hθ₁ : (offNet hN hD).IsNormalized (offParams N D θ) := isNormalized_offParams hN.isPhylogenetic hθ hD0
  exact (nmscCF_suppressStem hR hθ₁ hρ s).trans (nmscCF_offNetwork hN.isPhylogenetic _ hD0 s)

end DeletedCF

/-! ### The mixture -/

section Mixture

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} {θ : MetricData E}

/-- **"Since `a` is the only taxon below the hybrid node `v`, `CF_abcd(𝒩⁺) = γ₁ CF_abcd(𝒩₂⁺) + γ₂ CF_abcd(𝒩₁⁺)`"** (`a:claim:mixture`, in the proof of Theorem 1 (b)), with `𝒩ᵢ⁺` as the two ends of `γ` on `𝒩⁺`: the library's `NMSC.nmscCF_withPair`. `InPassing.cf_mixture` is the same on the networks `deleted`. -/
theorem nmscCF_withPair_mixture (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) {k₁ k₂ : E} (hk : k₁ ≠ k₂) (ht : N.graph.target k₂ = N.graph.target k₁)
    (hpar : ∀ f, N.graph.target f = N.graph.target k₁ → f = k₁ ∨ f = k₂) (s : QuartetTree X) (a : X)
    (honly : ∀ x ∈ s.taxa, x ≠ a → ¬ N.graph.Reaches (N.graph.target k₁) (N.leaf x)) (γ : ℝ) :
    nmscCF N (θ.withPair k₁ k₂ γ) 0 s = γ * nmscCF N (θ.withPair k₁ k₂ 1) 0 s + (1 - γ) * nmscCF N (θ.withPair k₁ k₂ 0) 0 s :=
  NMSC.nmscCF_withPair (D := ∅) hN hθ le_rfl (fun f hf => absurd hf (Set.notMem_empty f)) hk ht (fun f hf _ => hpar f hf) s a
    (fun y hy hya hr => honly y hy hya (ReachesOff.reaches hr)) γ

end Mixture

/-! ### The cut edges of `𝒩ᵢ⁺` -/

section Cuts

variable {V E X : Type*} {N : RootedNetwork V E X} {D : Set E}

/-- An arc of `Nᵢ` dominates a taxon in `Nᵢ` exactly when it does off `D`. -/
theorem offNetwork_dominates_iff {hroot : N.root ∈ offVertices N D} (e : offArcs N D) (x : X) :
    (offNetwork N D hroot).Dominates e x ↔ N.DominatesOff D e.1 x := by
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · -- a path of `Nᵢ` avoiding `e`
    have key : ∀ {u w : offVertices N D}, (offNetwork N D hroot).AvoidingReach e u w → N.ReachesOff (insert e.1 D) u.1 w.1 := by
      intro u w h
      induction h with
      | refl => exact .refl
      | @tail a b _ hab ih =>
        obtain ⟨f, hfe, rfl, rfl⟩ := hab
        refine ih.tail ⟨f.1, ?_, rfl, rfl⟩
        rintro (hf | hf)
        · exact hfe (Subtype.ext hf)
        · exact f.2.1 hf
    exact key h
  · -- a path off `D` avoiding `e`, to a taxon
    have key : ∀ {u : V}, N.ReachesOff (insert e.1 D) u (N.leaf x) → ∃ hu : u ∈ offVertices N D,
        (offNetwork N D hroot).AvoidingReach e ⟨u, hu⟩ ((offNetwork N D hroot).leaf x) := by
      intro u h
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨⟨x, .refl⟩, .refl⟩
      | @head a b hab _ ih =>
        obtain ⟨f, hf, rfl, rfl⟩ := hab
        obtain ⟨hb, hr⟩ := ih
        have hfe : f ≠ e.1 := fun he => hf (Or.inl he)
        have hfD : f ∉ D := fun hd => hf (Or.inr hd)
        have hm : f ∈ offArcs N D := mem_offArcs_iff.2 ⟨hfD, hb⟩
        exact ⟨source_mem_offVertices hm, Relation.ReflTransGen.head ⟨⟨f, hm⟩, fun he => hfe (congrArg Subtype.val he), rfl, rfl⟩ hr⟩
    obtain ⟨_, hr⟩ := key h
    exact hr

/-- A taxon is below an arc of `Nᵢ` in `Nᵢ` exactly when it is off `D`. -/
theorem offNetwork_isBelow_iff {hroot : N.root ∈ offVertices N D} (e : offArcs N D) (x : X) :
    (offNetwork N D hroot).IsBelow e x ↔ N.IsBelowOff D e.1 x := by
  refine ⟨fun h => ⟨e.2.1, reachesOff_of_reaches_offNetwork (hroot := hroot) h⟩, fun h => ?_⟩
  obtain ⟨_, hr⟩ := reaches_offNetwork_of_reachesOff (hroot := hroot) h.2 ⟨x, .refl⟩
  exact hr

variable [Nontrivial X] (hN : IsBinaryNetwork N) (hD : N.IsDeletion D)

/-- **The cuts of `𝒩ᵢ⁺` are those of `Nᵢ`**, with a taxon on each side. -/
theorem deleted_hasCutSplit_iff {A : Set X} (h₁ : A.Nonempty) (h₂ : Aᶜ.Nonempty) : (deleted hN hD).HasCutSplit A ↔ (offNet hN hD).HasCutSplit A :=
  (Bridges.removeStem_hasCutSplit_iff (offSuppressed_isPhylogenetic hN hD) h₁ h₂).trans (suppress_hasCutSplit_iff (offNet_isPhylogenetic hN hD) A)

variable [Fintype X] [DecidableEq X]

/-- **The cut-edge splits of `𝒩ᵢ⁺`, on four taxa, are the splits off `D`.** -/
theorem deleted_inducedCutSplit_iff (hcard : Fintype.card X = 4) (s : QuartetTree X) : InducedCutSplit (deleted hN hD) s ↔ ∃ e, N.SplitOffAt D e s := by
  have hst : s.taxa = Finset.univ := Finset.eq_univ_of_card _ (s.card_taxa.trans hcard.symm)
  have hR := offNet_isPhylogenetic hN hD
  have hDel := deleted_isPhylogenetic hN hD
  have hne : ∀ {B : Finset X}, B ∈ s.val → (B : Set X).Nonempty ∧ (B : Set X)ᶜ.Nonempty := fun {B} hB => by
    have h2 := s.card_of_mem hB
    have h2' := s.card_of_mem (s.sdiff_mem hB)
    rw [hst] at h2'
    obtain ⟨y, hy⟩ : (Finset.univ \ B).Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨Finset.card_pos.mp (by omega), y, ?_⟩
    simpa using hy
  have hsep₁ : ∀ {e : offArcs N D} {P Q : Set X}, (offNet hN hD).Separates e P Q → N.SeparatesOff D e.1 P Q := fun {e _ _} h =>
    ⟨fun x hx => (offNetwork_dominates_iff e x).mp (h.1 x hx), fun x hx hb => h.2 x hx ((offNetwork_isBelow_iff e x).mpr hb)⟩
  have hsep₂ : ∀ {e : offArcs N D} {P Q : Set X}, N.SeparatesOff D e.1 P Q → (offNet hN hD).Separates e P Q := fun {e _ _} h =>
    ⟨fun x hx => (offNetwork_dominates_iff e x).mpr (h.1 x hx), fun x hx hb => h.2 x hx ((offNetwork_isBelow_iff e x).mp hb)⟩
  have hinter : ∀ B : Finset X, (Set.univ : Set X) ∩ B = B := fun B => Set.univ_inter _
  have hdiff : ∀ B : Finset X, (Set.univ : Set X) \ B = ((Finset.univ \ B : Finset X) : Set X) := fun B => by
    ext x
    simp
  constructor
  · rintro ⟨B, hB, hc⟩
    obtain ⟨h₁, h₂⟩ := hne hB
    rw [hst, Finset.coe_univ, ← hasCutSplit_iff_hasCutSplitOn_univ hDel, deleted_hasCutSplit_iff hN hD h₁ h₂, hasCutSplit_iff_hasCutSplitOn_univ hR,
      hasCutSplitOn_iff_separates hR, hinter, hdiff] at hc
    obtain ⟨e, ⟨-, hd⟩ | ⟨-, hd⟩⟩ := hc
    · refine ⟨e.1, B, hB, ?_⟩
      rw [hst]
      exact hsep₁ hd
    · refine ⟨e.1, s.taxa \ B, s.sdiff_mem hB, ?_⟩
      rw [hst, Finset.sdiff_sdiff_eq_self (Finset.subset_univ B)]
      exact hsep₁ hd
  · rintro ⟨e, P, hP, hsep⟩
    obtain ⟨h₁, h₂⟩ := hne hP
    obtain ⟨x, hx⟩ := h₁
    have he : e ∈ offArcs N D := by
      obtain ⟨heD, hr⟩ := (hsep.1 x hx).isBelowOff hN.isPhylogenetic hD
      exact ⟨heD, x, Set.mem_univ x, hr⟩
    refine ⟨P, hP, ?_⟩
    rw [hst, Finset.coe_univ, ← hasCutSplit_iff_hasCutSplitOn_univ hDel, deleted_hasCutSplit_iff hN hD ⟨x, hx⟩ h₂, hasCutSplit_iff_hasCutSplitOn_univ hR,
      hasCutSplitOn_iff_separates hR, hinter, hdiff]
    refine ⟨⟨e, he⟩, Or.inl ⟨⟨x, hx⟩, hsep₂ ?_⟩⟩
    rw [hst] at hsep
    exact hsep

/-- **`T_rd` of `𝒩ᵢ⁺`**, by the splits off `D`. -/
theorem deleted_hasQuartetTopology_iff (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    (Trd (deleted_isBinaryNetwork hN hD) (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d ↔ ∃ e, N.SplitOffAt D e (quartetTree a b c d h) :=
  (hasQuartetTopology_iff_inducedCutSplit _ hcard h).trans (deleted_inducedCutSplit_iff hN hD hcard _)

end Cuts

/-! ### The map of parameters is onto -/

section Lift

variable {V E X : Type*}

/-- Step 1 of the map of parameters is onto valid boundary parameters: "set `γᵢ = 0` and lengths for the removed edges to be arbitrary". -/
theorem exists_off_lift [Fintype E] {N : RootedNetwork V E X} {D : Set E} [Fintype (offArcs N D)] {hroot : N.root ∈ offVertices N D} (hN : N.IsPhylogenetic) (hD : N.IsDeletion D)
    {θ' : MetricData (offArcs N D)} (hθ' : (offNetwork N D hroot).IsWeakMetric θ') :
    ∃ θ, N.IsWeakMetric θ ∧ (∀ f ∈ D, θ.inheritance f = 0) ∧ offParams N D θ = θ' := by
  have hR := offNetwork_isPhylogenetic hN hD hroot
  let θ : MetricData E :=
    { length := fun e => if h : e ∈ offArcs N D then θ'.length ⟨e, h⟩ else 0
      inheritance := fun e => if e ∈ D then 0 else if h : e ∈ offArcs N D then θ'.inheritance ⟨e, h⟩ else
        ((univ.filter fun f => N.graph.target f = N.graph.target e ∧ f ∉ D).card : ℝ)⁻¹ }
  have hinhD : ∀ f ∈ D, θ.inheritance f = 0 := fun f hf => ite_eq_left hf
  have hinhA : ∀ e : offArcs N D, θ.inheritance e.1 = θ'.inheritance e := fun e => by
    change (if e.1 ∈ D then 0 else if h : e.1 ∈ offArcs N D then θ'.inheritance ⟨e.1, h⟩ else _) = _
    rw [ite_eq_right e.2.1, dite_eq_left_of_eq_true (eq_true e.2)]
  have hinhO : ∀ e, e ∉ D → e ∉ offArcs N D → θ.inheritance e = ((univ.filter fun f => N.graph.target f = N.graph.target e ∧ f ∉ D).card : ℝ)⁻¹ := fun e h₁ h₂ => by
    change (if e ∈ D then 0 else if h : e ∈ offArcs N D then θ'.inheritance ⟨e, h⟩ else _) = _
    rw [ite_eq_right h₁, dite_eq_right_of_eq_false (eq_false h₂)]
  have hlenA : ∀ e : offArcs N D, θ.length e.1 = θ'.length e := fun e => dite_eq_left_of_eq_true (eq_true e.2)
  have hnorm : N.IsNormalized θ := by
    refine ⟨fun e he => ?_, fun v hv => ?_⟩
    · have heD : e ∉ D := fun h => by
        have h2 := hD.hybrid e h
        unfold IsTreeArc at he
        unfold IsHybridArc at h2
        omega
      by_cases hm : e ∈ offArcs N D
      · rw [hinhA ⟨e, hm⟩]
        refine hθ'.2.2.1 ⟨e, hm⟩ ?_
        have hle : (offNetwork N D hroot).graph.indegree ((offNetwork N D hroot).graph.target ⟨e, hm⟩) ≤ N.graph.indegree (N.graph.target e) := offNetwork_indegree_le _
        have hge := hR.nonroot_indegree ((offNetwork N D hroot).graph.target ⟨e, hm⟩) (fun h => target_ne_root hN e (congrArg Subtype.val h))
        unfold IsTreeArc at he ⊢
        omega
      · rw [hinhO e heD hm]
        obtain ⟨g, hg⟩ := (N.graph.indegree_eq_one_iff _).mp he
        have hc : (univ.filter fun f => N.graph.target f = N.graph.target e ∧ f ∉ D) = {e} := by
          ext f
          simp only [mem_filter, mem_univ, true_and, mem_singleton]
          constructor
          · rintro ⟨hf, -⟩
            rw [(hg f).mp hf, (hg e).mp rfl]
          · rintro rfl
            exact ⟨rfl, heD⟩
        rw [hc]
        simp
    · by_cases hva : v ∈ offVertices N D
      · -- a node of `Nᵢ`
        have hs := sum_offParams_inheritance (θ := θ) (hroot := hroot) hinhD ⟨v, hva⟩
        rw [← hs]
        have hvr : (⟨v, hva⟩ : offVertices N D) ≠ (offNetwork N D hroot).root := fun h => by
          have h' : v = N.root := congrArg Subtype.val h
          rw [h', hN.root_indegree] at hv
          omega
        have hge := hR.nonroot_indegree _ hvr
        have hinh' : ∀ e : offArcs N D, (offParams N D θ).inheritance e = θ'.inheritance e := hinhA
        by_cases h2 : 2 ≤ (offNetwork N D hroot).graph.indegree ⟨v, hva⟩
        · refine Eq.trans (Finset.sum_congr rfl fun e _ => ?_) (hθ'.2.2.2 _ h2)
          rw [hinh']
        · obtain ⟨g, hg⟩ := ((offNetwork N D hroot).graph.indegree_eq_one_iff _).mp (by omega : (offNetwork N D hroot).graph.indegree ⟨v, hva⟩ = 1)
          have hgt := (hg g).mpr rfl
          refine (Finset.sum_eq_single_of_mem g (mem_univ _) fun f _ hne => ite_eq_right fun hf => hne ((hg f).mp hf)).trans ?_
          rw [ite_eq_left hgt, hinh']
          refine hθ'.2.2.1 g ?_
          unfold IsTreeArc
          rw [hgt]
          omega
      · -- a node off `Nᵢ`: its parents off `D` share its inheritance equally
        have hvr : v ≠ N.root := fun h => by
          rw [h, hN.root_indegree] at hv
          omega
        obtain ⟨f₀, hf₀, hf₀v⟩ := hD.parent v hvr
        set C := univ.filter fun f => N.graph.target f = v ∧ f ∉ D with hC
        have hCpos : (C.card : ℝ) ≠ 0 := by
          have : 0 < C.card := card_pos.2 ⟨f₀, by simp [hC, hf₀, hf₀v]⟩
          positivity
        have hterm : ∀ e, (if N.graph.target e = v then θ.inheritance e else 0) = if e ∈ C then (C.card : ℝ)⁻¹ else 0 := by
          intro e
          by_cases he : N.graph.target e = v
          · by_cases heD : e ∈ D
            · simp [he, heD, hC, hinhD]
            · have hm : e ∉ offArcs N D := fun hm => hva (he ▸ (mem_offArcs_iff.1 hm).2)
              rw [ite_eq_left he, hinhO e heD hm, he]
              simp [hC, he, heD]
          · simp [he, hC]
        simp only [hterm, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
        exact mul_inv_cancel₀ hCpos
  refine ⟨θ, ⟨fun e => ?_, fun e he => ?_, hnorm⟩, hinhD, ?_⟩
  · by_cases hm : e ∈ offArcs N D
    · rw [hlenA ⟨e, hm⟩]
      exact hθ'.1 _
    · have : θ.length e = 0 := dite_eq_right_of_eq_false (eq_false hm)
      rw [this]
  · by_cases heD : e ∈ D
    · rw [hinhD e heD]
    by_cases hm : e ∈ offArcs N D
    · rw [hinhA ⟨e, hm⟩]
      by_cases h2 : (offNetwork N D hroot).IsHybridArc ⟨e, hm⟩
      · exact hθ'.2.1 _ h2
      · have htree : (offNetwork N D hroot).IsTreeArc ⟨e, hm⟩ := by
          have hge := hR.nonroot_indegree ((offNetwork N D hroot).graph.target ⟨e, hm⟩) (fun h => target_ne_root hN e (congrArg Subtype.val h))
          unfold IsHybridArc at h2
          unfold IsTreeArc
          omega
        rw [hθ'.2.2.1 _ htree]
        exact zero_le_one
    · rw [hinhO e heD hm]
      positivity
  · have h₁ : (offParams N D θ).length = θ'.length := funext hlenA
    have h₂ : (offParams N D θ).inheritance = θ'.inheritance := funext hinhA
    cases hc : offParams N D θ with
    | mk l i =>
      cases θ' with
      | mk l' i' =>
        rw [hc] at h₁ h₂
        exact congrArg₂ MetricData.mk h₁ h₂

variable [Fintype E] [Nontrivial X] {N : RootedNetwork V E X} {D : Set E}

/-- **The map of parameters to `𝒩ᵢ⁺` is onto valid boundary parameters**, at inheritance `0` on `D`. -/
theorem exists_deleted_lift (hN : IsBinaryNetwork N) (hD : N.IsDeletion D)
    [Fintype {e // ¬ (HasStem (offSuppressed hN hD) ∧ (offSuppressed hN hD).graph.source e = (offSuppressed hN hD).root)}] {θ' : MetricData {e // ¬ (HasStem (offSuppressed hN hD) ∧ (offSuppressed hN hD).graph.source e = (offSuppressed hN hD).root)}}
    (hθ' : (deleted hN hD).IsWeakMetric θ') : ∃ θ, N.IsWeakMetric θ ∧ (∀ f ∈ D, θ.inheritance f = 0) ∧ deletedParams hN hD θ = θ' := by
  let _ : Fintype (offArcs N D) := Fintype.ofFinite _
  let _ : Fintype {e // ¬ (offNet hN hD).IsChainVertex ((offNet hN hD).graph.source e)} := Fintype.ofFinite _
  obtain ⟨θ₁, hθ₁, h₁⟩ := exists_suppressStem_lift (offNet_isPhylogenetic hN hD) hθ'
  obtain ⟨θ, hθ, hD0, h₀⟩ := exists_off_lift hN.isPhylogenetic hD hθ₁
  refine ⟨θ, hθ, hD0, ?_⟩
  change stemMetric (offSuppressed hN hD) ((offNet hN hD).suppressMetric (offParams N D θ)) = θ'
  rw [h₀, h₁]

end Lift

/-! ### Valid parameters of `𝒩ᵢ⁺` -/

section Valid

variable {V E X : Type*} [Fintype E] [Nontrivial X] {N : RootedNetwork V E X} {D : Set E} {θ : MetricData E}

/-- **Valid parameters of `𝒩ᵢ⁺`**: from parameters of `𝒩⁺` with positive lengths, inheritance `0` on `D`, and positive inheritance on the other hybrid arcs. -/
theorem isMetric_deletedParams (hN : IsBinaryNetwork N) (hD : N.IsDeletion D) [Fintype {e // ¬ (HasStem (offSuppressed hN hD) ∧ (offSuppressed hN hD).graph.source e = (offSuppressed hN hD).root)}]
    (hlen : ∀ e, 0 < θ.length e) (hpos : ∀ e, e ∉ D → N.IsHybridArc e → 0 < θ.inheritance e) (hθ : N.IsNormalized θ) (hD0 : ∀ f ∈ D, θ.inheritance f = 0) :
    (deleted hN hD).IsMetric (deletedParams hN hD θ) := by
  let _ : Fintype (offArcs N D) := Fintype.ofFinite _
  let _ : Fintype {e // ¬ (offNet hN hD).IsChainVertex ((offNet hN hD).graph.source e)} := Fintype.ofFinite _
  have hn₁ : (offNet hN hD).IsNormalized (offParams N D θ) := isNormalized_offParams hN.isPhylogenetic hθ hD0
  have hm₁ : (offNet hN hD).IsMetric (offParams N D θ) := by
    refine ⟨fun e _ => hlen e.1, fun e _ => (hlen e.1).le, hn₁.1, fun e he => hpos e.1 e.2.1 ?_, hn₁.2⟩
    exact he.trans (offNetwork_indegree_le _)
  exact isMetric_suppressStem (offNet_isPhylogenetic hN hD) hm₁

omit [Fintype E] [Nontrivial X] in
/-- A deletion of one of two parents. -/
theorem isDeletion_singleton (hN : N.IsPhylogenetic) {k k' : E} (hne : k ≠ k') (ht : N.graph.target k = N.graph.target k') : N.IsDeletion {k} := by
  have h := (isDeletion_empty hN).insert hN hne ht (Set.notMem_empty k')
  rwa [insert_empty_eq] at h

end Valid

end AllmanEtAl2023
