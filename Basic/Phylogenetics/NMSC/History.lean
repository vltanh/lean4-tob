module

public import Basic.Phylogenetics.Coalescent.BinaryForest
public import Basic.Phylogenetics.NMSC.Inheritance
public import Basic.Phylogenetics.Network
public import Mathlib.Order.WellFoundedSet

/-!
# Histories of the network multispecies coalescent

`historyWeight` is a product over the vertices of a network, which mentions no processing order. It
is the law of a Markov chain along any linear extension of the network, from the taxa to the root: a
vertex needs only the forests at the top of its child arcs. This file proves what that gives, one
vertex at a time.

Going up from the taxa through a set `D` of vertices closed under children, with `vertexWeight` the
factor of a vertex:

* `frontier_of_prod_ne_zero`: on a history of nonzero weight all forests are binary forests, and the
  lineages at the top of the arcs leaving `D` partition the taxa of `D`.
* `sum_sum_prod_vertexWeight`: summing out the arcs entering the topmost vertex of `D` leaves the
  same sum for one vertex fewer (`sum_step`, from `card_pow_mul_sum_mul_eq`).

## Main results

* `sum_sum_historyWeight`: the weights of the histories sum to one.
* `historyWeight_nonneg`, `good_arrivingForest_root`: the forest arriving at the root of a history
  of nonzero weight is a binary forest on all the taxa.
* `exists_chain_history`: a history of positive weight in which no lineages coalesce.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

namespace NMSC

/-! ### Summing out some coordinates of a function -/

section Elimination

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

/-- The function `x` with its coordinates in `S` replaced by those of `y`. -/
def overwrite (S : Finset ι) (x y : ι → β) : ι → β := fun i => if i ∈ S then y i else x i

omit [Fintype ι] [Fintype β] in
theorem overwrite_of_mem {S : Finset ι} {i : ι} (h : i ∈ S) (x y : ι → β) :
    overwrite S x y i = y i := ite_eq_left h

omit [Fintype ι] [Fintype β] in
theorem overwrite_of_notMem {S : Finset ι} {i : ι} (h : i ∉ S) (x y : ι → β) :
    overwrite S x y i = x i := ite_eq_right h

/-- A sum over all functions of a product over the coordinates in `S`, whose factors sum to one over
each coordinate: the other coordinates are free. -/
theorem sum_prod_of_sum_eq_one (S : Finset ι) (φ : ι → β → ℝ) (h : ∀ i ∈ S, ∑ t, φ i t = 1) :
    ∑ y : ι → β, ∏ i ∈ S, φ i (y i) = (Fintype.card β : ℝ) ^ #Sᶜ := by
  have h1 : ∀ y : ι → β, ∏ i ∈ S, φ i (y i) = ∏ i, if i ∈ S then φ i (y i) else 1 := by
    intro y
    rw [prod_ite_mem, univ_inter]
  simp_rw [h1]
  rw [← Fintype.piFinset_univ,
    ← prod_univ_sum (fun _ => univ) (fun i t => if i ∈ S then φ i t else 1)]
  rw [← prod_mul_prod_compl S, prod_eq_one (s := S), one_mul, ← prod_const]
  · refine prod_congr rfl fun i hi => ?_
    have hi' : i ∉ S := mem_compl.1 hi
    simp [hi']
  · intro i hi
    simp only [hi, ↓reduceIte, h i hi]

/-- The number of functions with given values on `S`, times `w`. -/
theorem sum_ite_forall_eq (S : Finset ι) (C : ι → β) (w : ℝ) :
    ∑ y : ι → β, (if ∀ i ∈ S, y i = C i then w else 0) = w * (Fintype.card β : ℝ) ^ #Sᶜ := by
  have h := sum_prod_of_sum_eq_one S (fun i t => if t = C i then (1 : ℝ) else 0)
    (fun i _ => by simp)
  rw [← h, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [prod_ite_zero]
  simp only [prod_const_one]
  split_ifs <;> simp

/-- **Summing out the coordinates in `S`.** If `g` does not depend on them, and `κ` has total mass
`|β|^|Sᶜ|` over them where `g ≠ 0`, then the sum of `g κ` over all functions is the sum of `g` up to
a factor `|β|^|S|`, the number of values of the coordinates in `S`. The proof applies to the sum over
pairs of functions the involution `(x, y) ↦ (overwrite S x y, overwrite S y x)`. -/
theorem card_pow_mul_sum_mul_eq [Nonempty β] (S : Finset ι) (g κ : (ι → β) → ℝ)
    (hg : ∀ x y, g (overwrite S x y) = g x)
    (hκ : ∀ x, g x ≠ 0 → ∑ y, κ (overwrite S x y) = (Fintype.card β : ℝ) ^ #Sᶜ) :
    (Fintype.card β : ℝ) ^ #S * ∑ x, g x * κ x = ∑ x, g x := by
  have hB : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  let Φ : (ι → β) × (ι → β) → (ι → β) × (ι → β) := fun p =>
    (overwrite S p.1 p.2, overwrite S p.2 p.1)
  have hΦ : Function.Involutive Φ := by
    rintro ⟨x, y⟩
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> by_cases hi : i ∈ S <;>
      simp [Φ, overwrite, hi]
  have hM : ((Fintype.card (ι → β) : ℕ) : ℝ) =
      (Fintype.card β : ℝ) ^ #S * (Fintype.card β : ℝ) ^ #Sᶜ := by
    rw [← pow_add, card_add_card_compl, Fintype.card_fun, Nat.cast_pow]
  have h1 : ∑ p : (ι → β) × (ι → β), g p.1 * κ p.1 =
      (Fintype.card (ι → β) : ℝ) * ∑ x, g x * κ x := by
    rw [Fintype.sum_prod_type]
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_sum]
  have h2 : ∑ p : (ι → β) × (ι → β), g (Φ p).1 * κ (Φ p).1 =
      ∑ p : (ι → β) × (ι → β), g p.1 * κ p.1 :=
    Equiv.sum_comp hΦ.toPerm fun p => g p.1 * κ p.1
  have h3 : ∑ p : (ι → β) × (ι → β), g (Φ p).1 * κ (Φ p).1 =
      (Fintype.card β : ℝ) ^ #Sᶜ * ∑ x, g x := by
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    simp only [Φ, hg, ← mul_sum]
    by_cases hx : g x = 0
    · simp [hx]
    · rw [hκ x hx, mul_comm]
  rw [h3, h1, hM, mul_assoc, mul_left_comm] at h2
  exact mul_left_cancel₀ (pow_ne_zero _ hB.ne') h2.symm

end Elimination

/-! ### The network -/

section Network

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

/-- The arcs entering a vertex. -/
def arcsInto (N : RootedNetwork V E X) (v : V) : Finset E :=
  univ.filter fun e => N.graph.target e = v

omit [Fintype V] [DecidableEq X] [Fintype X] in
@[simp] theorem mem_arcsInto {v : V} {e : E} : e ∈ arcsInto N v ↔ N.graph.target e = v := by
  simp [arcsInto]

omit [Fintype V] [DecidableEq X] [Fintype X] in
theorem indegree_eq_card (v : V) : N.graph.indegree v = #(arcsInto N v) := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp

omit [Fintype V] [DecidableEq X] [Fintype X] in
theorem target_ne_root (hN : N.IsPhylogenetic) (e : E) : N.graph.target e ≠ N.root := by
  intro h
  have h0 := hN.root_indegree
  rw [indegree_eq_card, card_eq_zero] at h0
  have : e ∈ arcsInto N N.root := mem_arcsInto.2 h
  simp [h0] at this

omit [Fintype V] [Fintype E] [DecidableEq X] [Fintype X] in
theorem source_ne_target (hN : N.IsPhylogenetic) (e : E) : N.graph.source e ≠ N.graph.target e := by
  intro h
  exact hN.acyclic _ (Relation.TransGen.single ⟨e, h, rfl⟩)

omit [Fintype V] [DecidableEq X] [Fintype X] in
theorem exists_arc_into (hN : N.IsPhylogenetic) {v : V} (hv : v ≠ N.root) :
    ∃ e, N.graph.target e = v := by
  have h := hN.nonroot_indegree v hv
  rw [indegree_eq_card] at h
  obtain ⟨e, he⟩ := card_pos.1 h
  exact ⟨e, mem_arcsInto.1 he⟩

omit [Fintype V] [Fintype E] [DecidableEq X] [Fintype X] in
theorem nonempty_arcs (hN : N.IsPhylogenetic) : Nonempty E := by
  have h : N.graph.outdegree N.root ≠ 0 := fun h0 => by
    obtain ⟨x, hx⟩ := (hN.leaves N.root).1 h0
    exact N.leaf_ne_root hN x hx
  unfold DirectedMultigraph.outdegree at h
  obtain ⟨e, -⟩ := Set.nonempty_of_ncard_ne_zero h
  exact ⟨e⟩

omit [Fintype V] [DecidableEq X] [Fintype X] in
/-- Each arc is a tree arc or a hybrid arc. -/
theorem isTreeArc_or_isHybridArc (e : E) : N.IsTreeArc e ∨ N.IsHybridArc e := by
  unfold RootedNetwork.IsTreeArc RootedNetwork.IsHybridArc
  have h : 1 ≤ N.graph.indegree (N.graph.target e) := by
    rw [indegree_eq_card]
    exact card_pos.2 ⟨e, mem_arcsInto.2 rfl⟩
  omega

omit [Fintype V] [DecidableEq X] [Fintype X] in
theorem length_nonneg (hθ : N.IsMetric θ) (e : E) : 0 ≤ θ.length e := by
  rcases isTreeArc_or_isHybridArc (N := N) e with h | h
  · exact (hθ.1 e h).le
  · exact hθ.2.1 e h

omit [Fintype V] [DecidableEq X] [Fintype X] in
theorem inheritance_pos (hθ : N.IsMetric θ) (e : E) : 0 < θ.inheritance e := by
  rcases isTreeArc_or_isHybridArc (N := N) e with h | h
  · rw [hθ.2.2.1 e h]
    exact one_pos
  · exact hθ.2.2.2.1 e h

omit [Fintype V] [DecidableEq X] [Fintype X] in
/-- The inheritance probabilities of the arcs entering a non-root vertex sum to one. -/
theorem sum_inheritance (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) {v : V} (hv : v ≠ N.root) :
    ∑ e : {e // N.graph.target e = v}, θ.inheritance e.val = 1 := by
  have hsum : ∑ e : {e // N.graph.target e = v}, θ.inheritance e.val =
      ∑ e, if N.graph.target e = v then θ.inheritance e else 0 := by
    rw [← sum_filter]
    exact (sum_subtype _ (fun e => by simp) _).symm
  rw [hsum]
  have hi := hN.nonroot_indegree v hv
  rcases Nat.lt_or_ge (N.graph.indegree v) 2 with h | h
  · have h1 : #(arcsInto N v) = 1 := by
      rw [← indegree_eq_card]
      omega
    obtain ⟨e, he⟩ := card_eq_one.1 h1
    have hev : N.graph.target e = v := mem_arcsInto.1 (he ▸ mem_singleton_self e)
    rw [← sum_filter]
    change ∑ f ∈ arcsInto N v, θ.inheritance f = 1
    rw [he, sum_singleton]
    refine hθ.2.2.1 e ?_
    unfold RootedNetwork.IsTreeArc
    rw [hev]
    omega
  · exact hθ.2.2.2.2 v h

variable (N) in
/-- A set of vertices closed under children. -/
def DownClosed (D : Finset V) : Prop := ∀ e, N.graph.source e ∈ D → N.graph.target e ∈ D

omit [Fintype E] [Fintype X] [DecidableEq X] in
/-- A nonempty set of vertices closed under children has a vertex without an ancestor in it;
removing it leaves a set closed under children. -/
theorem exists_top_vertex (hN : N.IsPhylogenetic) {D : Finset V} (hD : DownClosed N D)
    (hne : D.Nonempty) :
    ∃ v ∈ D, DownClosed N (D.erase v) ∧
      ∀ e, N.graph.source e = v → N.graph.target e ∈ D.erase v := by
  have : IsTrans V (Relation.TransGen N.graph.Adj) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen N.graph.Adj) := ⟨hN.acyclic⟩
  have hwf : WellFounded (Relation.TransGen N.graph.Adj) :=
    Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨v, hv, hmin⟩ := hwf.has_min (D : Set V) hne
  have hv' : v ∈ D := hv
  refine ⟨v, hv', fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨hne', hs⟩ := mem_erase.1 he
    refine mem_erase.2 ⟨fun ht => ?_, hD e hs⟩
    exact hmin _ hs (Relation.TransGen.single ⟨e, rfl, ht⟩)
  · refine mem_erase.2 ⟨fun ht => ?_, hD e (he ▸ hv')⟩
    exact source_ne_target hN e (he.trans ht.symm)

end Network

/-! ### The weights of a history -/

section Weights

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

variable (N θ ρ) in
/-- The factor of a vertex in the weight of a history: its roots choose parents, and the lineages
coalesce along the arcs entering it. -/
def vertexWeight (v : V) (bot top : E → Finset (Finset X)) : ℝ :=
  allocationFactor N θ ρ (arrivingForest N top v) v bot *
    ∏ e ∈ arcsInto N v, kingmanTransition (θ.length e) (bot e) (top e)

/-- The weight of a history is the product of the factors of the non-root vertices. -/
theorem historyWeight_eq_prod (hN : N.IsPhylogenetic) (bot top : E → Finset (Finset X)) :
    historyWeight N θ ρ bot top = ∏ v ∈ univ.erase N.root, vertexWeight N θ ρ v bot top := by
  unfold historyWeight vertexWeight
  rw [prod_mul_distrib]
  congr 1
  exact (prod_fiberwise_of_maps_to (g := N.graph.target)
    (fun e _ => mem_erase.2 ⟨target_ne_root hN e, mem_univ _⟩) _).symm

omit [Fintype V] in
theorem arrivingForest_congr {v : V} {top top' : E → Finset (Finset X)}
    (h : ∀ e, N.graph.source e = v → top e = top' e) :
    arrivingForest N top v = arrivingForest N top' v := by
  unfold arrivingForest
  congr 1
  refine biUnion_congr rfl fun e he => h e (mem_filter.1 he).2

omit [Fintype V] in
theorem allocationFactor_congr {F : Finset (Finset X)} {v : V} {bot bot' : E → Finset (Finset X)}
    (h : ∀ e, N.graph.target e = v → bot e = bot' e) :
    allocationFactor N θ ρ F v bot = allocationFactor N θ ρ F v bot' := by
  unfold allocationFactor
  refine sum_congr rfl fun a _ => ?_
  have hc : (∀ e : {e // N.graph.target e = v},
        bot e.val = forestBelow F ((univ.filter fun r => a r = e).image Subtype.val)) ↔
      (∀ e : {e // N.graph.target e = v},
        bot' e.val = forestBelow F ((univ.filter fun r => a r = e).image Subtype.val)) :=
    forall_congr' fun e => by rw [h e.val e.property]
  simp only [hc]

omit [Fintype V] in
theorem vertexWeight_congr {u : V} {bot bot' top top' : E → Finset (Finset X)}
    (h1 : ∀ e, N.graph.target e = u → bot e = bot' e)
    (h2 : ∀ e, N.graph.target e = u → top e = top' e)
    (h3 : ∀ e, N.graph.source e = u → top e = top' e) :
    vertexWeight N θ ρ u bot top = vertexWeight N θ ρ u bot' top' := by
  unfold vertexWeight
  rw [arrivingForest_congr h3, allocationFactor_congr h1]
  congr 1
  refine prod_congr rfl fun e he => ?_
  rw [h1 e (mem_arcsInto.1 he), h2 e (mem_arcsInto.1 he)]

omit [Fintype V] in
theorem allocationFactor_nonneg (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (F : Finset (Finset X))
    (v : V) (bot : E → Finset (Finset X)) : 0 ≤ allocationFactor N θ ρ F v bot := by
  refine sum_nonneg fun a _ => ?_
  split_ifs
  · exact allocationWeight_nonneg hρ.1 hρ.2 (fun e => (inheritance_pos hθ e.val).le) a
  · exact le_rfl

theorem historyWeight_nonneg (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (bot top : E → Finset (Finset X)) : 0 ≤ historyWeight N θ ρ bot top :=
  mul_nonneg (prod_nonneg fun _ _ => allocationFactor_nonneg hθ hρ _ _ _)
    (prod_nonneg fun e _ => kingmanTransition_nonneg (length_nonneg hθ e) _ _)

omit [Fintype V] in
/-- A nonzero allocation comes from an assignment of the roots to the arcs. -/
theorem exists_assignment {F : Finset (Finset X)} {v : V} {bot : E → Finset (Finset X)}
    (h : allocationFactor N θ ρ F v bot ≠ 0) :
    ∃ a : {A // A ∈ roots F} → {e // N.graph.target e = v}, ∀ e : {e // N.graph.target e = v},
      bot e.val = forestBelow F ((univ.filter fun r => a r = e).image Subtype.val) := by
  obtain ⟨a, -, ha⟩ := exists_ne_zero_of_sum_ne_zero h
  refine ⟨a, ?_⟩
  by_contra hne
  exact ha (ite_eq_right hne)

omit [Fintype V] in
/-- The allocations of the roots of `F` at `v` have total mass one over the arcs entering `v`. -/
theorem sum_allocationFactor (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {v : V} (hv : v ≠ N.root) (F : Finset (Finset X)) :
    ∑ y : E → Finset (Finset X), allocationFactor N θ ρ F v y =
      (Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ := by
  unfold allocationFactor
  rw [sum_comm]
  have hkey : ∀ a : {A // A ∈ roots F} → {e // N.graph.target e = v},
      ∑ y : E → Finset (Finset X), (if ∀ e : {e // N.graph.target e = v},
          y e.val = forestBelow F ((univ.filter fun r => a r = e).image Subtype.val) then
        allocationWeight ρ (fun e : {e // N.graph.target e = v} => θ.inheritance e.val) a else 0) =
        allocationWeight ρ (fun e : {e // N.graph.target e = v} => θ.inheritance e.val) a *
          (Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ := by
    intro a
    let C : E → Finset (Finset X) := fun e =>
      if h : N.graph.target e = v then
        forestBelow F ((univ.filter fun r => a r = ⟨e, h⟩).image Subtype.val)
      else ∅
    rw [← sum_ite_forall_eq (arcsInto N v) C]
    refine sum_congr rfl fun y _ => ?_
    have hiff : (∀ e : {e // N.graph.target e = v},
          y e.val = forestBelow F ((univ.filter fun r => a r = e).image Subtype.val)) ↔
        ∀ e ∈ arcsInto N v, y e = C e := by
      constructor
      · intro h e he
        have he' := mem_arcsInto.1 he
        simp only [C, he', ↓reduceDIte]
        exact h ⟨e, he'⟩
      · intro h e
        have := h e.val (mem_arcsInto.2 e.property)
        simp only [C, e.property, ↓reduceDIte] at this
        exact this
    simp only [hiff]
    congr
  simp_rw [hkey]
  rw [← sum_mul, sum_allocationWeight hρ.1 (sum_inheritance hN hθ hv), one_mul]

end Weights

/-! ### Histories of nonzero weight -/

section Frontier

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

variable (N) in
/-- The state of a history after the vertices of `D`: all forests so far are binary forests, and the
lineages at the top of the arcs leaving `D` partition the taxa of `D`. -/
structure Frontier (D : Finset V) (bot top : E → Finset (Finset X)) : Prop where
  good_bot : ∀ e, N.graph.target e ∈ D → IsGoodForest (bot e)
  good_top : ∀ e, N.graph.target e ∈ D → IsGoodForest (top e)
  disj : ∀ e f, N.graph.target e ∈ D → N.graph.source e ∉ D → N.graph.target f ∈ D →
    N.graph.source f ∉ D → e ≠ f → Disjoint (lineages (top e)) (lineages (top f))
  mem : ∀ x, (∃ e, N.graph.target e ∈ D ∧ N.graph.source e ∉ D ∧ x ∈ lineages (top e)) ↔
    N.leaf x ∈ D

omit [Fintype V] in
theorem mem_lineages_arrivingForest (top : E → Finset (Finset X)) (v : V) (x : X) :
    x ∈ lineages (arrivingForest N top v) ↔
      N.leaf x = v ∨ ∃ e, N.graph.source e = v ∧ x ∈ lineages (top e) := by
  unfold arrivingForest
  rw [lineages_union, mem_union, lineages_image_singleton, mem_filter]
  simp only [mem_univ, true_and]
  refine or_congr Iff.rfl ?_
  rw [mem_lineages]
  constructor
  · rintro ⟨A, hA, hx⟩
    obtain ⟨e, he, hAe⟩ := mem_biUnion.1 hA
    exact ⟨e, (mem_filter.1 he).2, mem_lineages.2 ⟨A, hAe, hx⟩⟩
  · rintro ⟨e, he, hx⟩
    obtain ⟨A, hA, hxA⟩ := mem_lineages.1 hx
    exact ⟨A, mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, he⟩, hA⟩, hxA⟩

omit [Fintype V] in
/-- The forest arriving at a vertex all of whose children have been processed is a binary forest. -/
theorem Frontier.good_arrivingForest {D : Finset V} {bot top : E → Finset (Finset X)}
    (hF : Frontier N D bot top) {v : V} (hv : v ∉ D)
    (hch : ∀ e, N.graph.source e = v → N.graph.target e ∈ D) :
    IsGoodForest (arrivingForest N top v) := by
  unfold arrivingForest
  refine IsGoodForest.union (isGoodForest_singletons _) (IsGoodForest.biUnion _ _ ?_ ?_) ?_
  · intro e he
    exact hF.good_top e (hch e (mem_filter.1 he).2)
  · intro e he f hf hef
    have he' := (mem_filter.1 he).2
    have hf' := (mem_filter.1 hf).2
    exact hF.disj e f (hch e he') (he' ▸ hv) (hch f hf') (hf' ▸ hv) hef
  · rw [lineages_image_singleton, disjoint_left]
    intro x hx hx'
    obtain ⟨A, hA, hxA⟩ := mem_lineages.1 hx'
    obtain ⟨e, he, hAe⟩ := mem_biUnion.1 hA
    have he' := (mem_filter.1 he).2
    have hxl := (hF.mem x).1 ⟨e, hch e he', he' ▸ hv, mem_lineages.2 ⟨A, hAe, hxA⟩⟩
    exact hv ((mem_filter.1 hx).2 ▸ hxl)

omit [Fintype V] in
/-- The forests at the bottom and at the top of the arcs entering a vertex of nonzero factor: binary
forests; each lineage arriving at `v` is at the top of exactly one of them. -/
theorem good_of_vertexWeight_ne_zero {v : V} {bot top : E → Finset (Finset X)}
    (hg : IsGoodForest (arrivingForest N top v)) (hw : vertexWeight N θ ρ v bot top ≠ 0) :
    (∀ e, N.graph.target e = v → IsGoodForest (bot e) ∧ IsGoodForest (top e)) ∧
    (∀ e f, N.graph.target e = v → N.graph.target f = v → e ≠ f →
      Disjoint (lineages (top e)) (lineages (top f))) ∧
    (∀ x, (∃ e, N.graph.target e = v ∧ x ∈ lineages (top e)) ↔
      x ∈ lineages (arrivingForest N top v)) := by
  set F := arrivingForest N top v with hFdef
  have halloc := left_ne_zero_of_mul hw
  have hprod := right_ne_zero_of_mul hw
  obtain ⟨a, ha⟩ := exists_assignment halloc
  have hK : ∀ e, N.graph.target e = v →
      kingmanTransition (θ.length e) (bot e) (top e) ≠ 0 := fun e he =>
    prod_ne_zero_iff.1 hprod e (mem_arcsInto.2 he)
  have hbot : ∀ e, (he : N.graph.target e = v) →
      bot e = forestBelow F ((univ.filter fun r => a r = ⟨e, he⟩).image Subtype.val) :=
    fun e he => ha ⟨e, he⟩
  have hgoodb : ∀ e, N.graph.target e = v → IsGoodForest (bot e) := fun e he => by
    rw [hbot e he]
    exact isGoodForest_forestBelow hg
  have hlin : ∀ e, (he : N.graph.target e = v) → ∀ x,
      x ∈ lineages (top e) ↔ ∃ r : {A // A ∈ roots F}, a r = ⟨e, he⟩ ∧ x ∈ r.val := by
    intro e he x
    rw [(kingmanTransition_support_good (hgoodb e he) (hK e he)).2.2, hbot e he,
      lineages_forestBelow (fun A hA => by
        obtain ⟨r, -, rfl⟩ := mem_image.1 hA
        exact r.property), mem_sup]
    constructor
    · rintro ⟨A, hA, hx⟩
      obtain ⟨r, hr, rfl⟩ := mem_image.1 hA
      exact ⟨r, (mem_filter.1 hr).2, hx⟩
    · rintro ⟨r, hr, hx⟩
      exact ⟨r.val, mem_image.2 ⟨r, mem_filter.2 ⟨mem_univ _, hr⟩, rfl⟩, hx⟩
  refine ⟨fun e he => ⟨hgoodb e he, (kingmanTransition_support_good (hgoodb e he) (hK e he)).1⟩,
    fun e f he hf hef => ?_, fun x => ⟨?_, ?_⟩⟩
  · rw [disjoint_left]
    intro x hxe hxf
    obtain ⟨r, hr, hxr⟩ := (hlin e he x).1 hxe
    obtain ⟨s, hs, hxs⟩ := (hlin f hf x).1 hxf
    have hrs : r = s := Subtype.ext (hg.1.eq_of_mem_roots_of_mem r.property s.property hxr hxs)
    rw [hrs, hs] at hr
    exact hef (congrArg Subtype.val hr).symm
  · rintro ⟨e, he, hx⟩
    obtain ⟨r, -, hxr⟩ := (hlin e he x).1 hx
    exact mem_lineages.2 ⟨r.val, roots_subset F r.property, hxr⟩
  · intro hx
    obtain ⟨R, hR, hxR⟩ := exists_mem_roots_of_mem_lineages hx
    let r : {A // A ∈ roots F} := ⟨R, hR⟩
    exact ⟨(a r).val, (a r).property, (hlin _ (a r).property x).2 ⟨r, rfl, hxR⟩⟩

omit [Fintype V] in
/-- One more vertex. -/
theorem Frontier.insert (hN : N.IsPhylogenetic) {D : Finset V} {bot top : E → Finset (Finset X)}
    (hF : Frontier N D bot top) (hD : DownClosed N D) {v : V} (hv : v ∉ D)
    (hch : ∀ e, N.graph.source e = v → N.graph.target e ∈ D)
    (hw : vertexWeight N θ ρ v bot top ≠ 0) : Frontier N (insert v D) bot top := by
  have hg := hF.good_arrivingForest hv hch
  obtain ⟨hgood, hdisj, hmem⟩ := good_of_vertexWeight_ne_zero hg hw
  -- the arcs entering `v` leave the new set
  have hleave : ∀ e, N.graph.target e = v → N.graph.source e ∉ Insert.insert v D :=
      fun e he hs => by
    rcases mem_insert.1 hs with h | h
    · exact source_ne_target hN e (h.trans he.symm)
    · exact hv (he ▸ hD e h)
  -- a lineage arriving at `v` was at the top of a child arc of `v`, or labels `v`
  have harr : ∀ f x, N.graph.target f ∈ D → N.graph.source f ∉ D → N.graph.source f ≠ v →
      x ∈ lineages (top f) → x ∉ lineages (arrivingForest N top v) := by
    intro f x hft hfs hfv hxf hx
    rcases (mem_lineages_arrivingForest top v x).1 hx with h | ⟨g, hg1, hg2⟩
    · exact hv (h ▸ (hF.mem x).1 ⟨f, hft, hfs, hxf⟩)
    · have hgf : g ≠ f := fun h => hfv (h ▸ hg1)
      exact disjoint_left.1 (hF.disj g f (hch g hg1) (hg1 ▸ hv) hft hfs hgf) hg2 hxf
  refine ⟨fun e he => ?_, fun e he => ?_, fun e f he hes hf hfs hef => ?_, fun x => ⟨?_, ?_⟩⟩
  · rcases mem_insert.1 he with h | h
    · exact (hgood e h).1
    · exact hF.good_bot e h
  · rcases mem_insert.1 he with h | h
    · exact (hgood e h).2
    · exact hF.good_top e h
  · have hes' : N.graph.source e ∉ D := fun h => hes (mem_insert_of_mem h)
    have hfs' : N.graph.source f ∉ D := fun h => hfs (mem_insert_of_mem h)
    have hev : N.graph.source e ≠ v := fun h => hes (h ▸ mem_insert_self _ _)
    have hfv : N.graph.source f ≠ v := fun h => hfs (h ▸ mem_insert_self _ _)
    rcases mem_insert.1 he with h | h <;> rcases mem_insert.1 hf with h' | h'
    · exact hdisj e f h h' hef
    · rw [disjoint_right]
      intro x hxf hxe
      exact harr f x h' hfs' hfv hxf ((hmem x).1 ⟨e, h, hxe⟩)
    · rw [disjoint_left]
      intro x hxe hxf
      exact harr e x h hes' hev hxe ((hmem x).1 ⟨f, h', hxf⟩)
    · exact hF.disj e f h hes' h' hfs' hef
  · rintro ⟨e, he, hes, hx⟩
    rcases mem_insert.1 he with h | h
    · rcases (mem_lineages_arrivingForest top v x).1 ((hmem x).1 ⟨e, h, hx⟩) with h' | ⟨g, hg1, hg2⟩
      · exact h' ▸ mem_insert_self _ _
      · exact mem_insert_of_mem ((hF.mem x).1 ⟨g, hch g hg1, hg1 ▸ hv, hg2⟩)
    · exact mem_insert_of_mem ((hF.mem x).1 ⟨e, h, fun hs => hes (mem_insert_of_mem hs), hx⟩)
  · intro hx
    have hfromArr : x ∈ lineages (arrivingForest N top v) →
        ∃ e, N.graph.target e ∈ Insert.insert v D ∧ N.graph.source e ∉ Insert.insert v D ∧
          x ∈ lineages (top e) := by
      intro hxa
      obtain ⟨e, he, hxe⟩ := (hmem x).2 hxa
      exact ⟨e, he ▸ mem_insert_self _ _, hleave e he, hxe⟩
    rcases mem_insert.1 hx with h | h
    · exact hfromArr ((mem_lineages_arrivingForest top v x).2 (Or.inl h))
    · obtain ⟨e, het, hes, hxe⟩ := (hF.mem x).2 h
      by_cases hev : N.graph.source e = v
      · exact hfromArr ((mem_lineages_arrivingForest top v x).2 (Or.inr ⟨e, hev, hxe⟩))
      · refine ⟨e, mem_insert_of_mem het, fun hs => ?_, hxe⟩
        rcases mem_insert.1 hs with h' | h'
        · exact hev h'
        · exact hes h'

omit [Fintype V] [Fintype E] [Fintype X] in
theorem frontier_empty (bot top : E → Finset (Finset X)) : Frontier N ∅ bot top :=
  ⟨fun e he => absurd he (notMem_empty _), fun e he => absurd he (notMem_empty _),
    fun e _ he => absurd he (notMem_empty _), fun x => by simp⟩

/-- A history of nonzero weight on `D` is in the state `Frontier`. -/
theorem frontier_of_prod_ne_zero (hN : N.IsPhylogenetic) {D : Finset V} (hD : DownClosed N D)
    {bot top : E → Finset (Finset X)} (h : ∏ v ∈ D, vertexWeight N θ ρ v bot top ≠ 0) :
    Frontier N D bot top := by
  induction D using Finset.strongInduction with
  | H D ih =>
    rcases D.eq_empty_or_nonempty with rfl | hne
    · exact frontier_empty bot top
    · obtain ⟨v, hv, hD', hch⟩ := exists_top_vertex hN hD hne
      rw [← mul_prod_erase D _ hv] at h
      have hF := ih (D.erase v) (erase_ssubset hv) hD' (right_ne_zero_of_mul h)
      have := hF.insert hN hD' (notMem_erase v D) hch (left_ne_zero_of_mul h)
      rwa [insert_erase hv] at this

/-- The forest arriving at the root of a history of nonzero weight is a binary forest on all the
taxa. -/
theorem good_arrivingForest_root (hN : N.IsPhylogenetic) {bot top : E → Finset (Finset X)}
    (h : historyWeight N θ ρ bot top ≠ 0) :
    IsGoodForest (arrivingForest N top N.root) ∧ lineages (arrivingForest N top N.root) = univ := by
  rw [historyWeight_eq_prod hN] at h
  have hD : DownClosed N (univ.erase N.root) := fun e _ =>
    mem_erase.2 ⟨target_ne_root hN e, mem_univ _⟩
  have hF := frontier_of_prod_ne_zero hN hD h
  refine ⟨hF.good_arrivingForest (notMem_erase _ _) fun e _ =>
    mem_erase.2 ⟨target_ne_root hN e, mem_univ _⟩, eq_univ_of_forall fun x => ?_⟩
  obtain ⟨e, -, hes, hx⟩ := (hF.mem x).2 (mem_erase.2 ⟨N.leaf_ne_root hN x, mem_univ _⟩)
  have hs : N.graph.source e = N.root := by
    by_contra hne
    exact hes (mem_erase.2 ⟨hne, mem_univ _⟩)
  exact (mem_lineages_arrivingForest top _ x).2 (Or.inr ⟨e, hs, hx⟩)

end Frontier

/-! ### The total mass -/

section Mass

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

/-- The sum over the histories of the factors of `insert v D`, with the arcs entering `v` summed
out: the sum for `D`, up to the number of values of these arcs. -/
theorem sum_step (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {D : Finset V}
    (hD : DownClosed N D) {v : V} (hvD : v ∉ D) (hv : v ≠ N.root)
    (hch : ∀ e, N.graph.source e = v → N.graph.target e ∈ D) :
    ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)) ^ 2 *
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          ∏ u ∈ insert v D, vertexWeight N θ ρ u bot top =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        ∏ u ∈ D, vertexWeight N θ ρ u bot top := by
  set S := arcsInto N v with hS
  set B : ℝ := (Fintype.card (Finset (Finset X)) : ℝ) with hB
  -- the factors of `D` do not see the arcs entering `v`
  have hnot : ∀ e, N.graph.target e ∈ D → e ∉ S := fun e he hes =>
    hvD (mem_arcsInto.1 hes ▸ he)
  have hgbot : ∀ (top bot y : E → Finset (Finset X)),
      ∏ u ∈ D, vertexWeight N θ ρ u (overwrite S bot y) top =
        ∏ u ∈ D, vertexWeight N θ ρ u bot top := by
    intro top bot y
    refine prod_congr rfl fun u hu => vertexWeight_congr (fun e he => ?_) (fun _ _ => rfl)
      (fun _ _ => rfl)
    exact overwrite_of_notMem (hnot e (he ▸ hu)) _ _
  have hgtop : ∀ (bot top y : E → Finset (Finset X)),
      ∏ u ∈ D, vertexWeight N θ ρ u bot (overwrite S top y) =
        ∏ u ∈ D, vertexWeight N θ ρ u bot top := by
    intro bot top y
    refine prod_congr rfl fun u hu => vertexWeight_congr (fun _ _ => rfl) (fun e he => ?_)
      (fun e he => ?_)
    · exact overwrite_of_notMem (hnot e (he ▸ hu)) _ _
    · exact overwrite_of_notMem (hnot e (hD e (he ▸ hu))) _ _
  have harr : ∀ (top y : E → Finset (Finset X)),
      arrivingForest N (overwrite S top y) v = arrivingForest N top v := by
    intro top y
    refine arrivingForest_congr fun e he => ?_
    exact overwrite_of_notMem (hnot e (hch e he)) _ _
  -- summing out the tops of the arcs entering `v`
  have htop : ∀ bot : E → Finset (Finset X),
      B ^ #S * ∑ top : E → Finset (Finset X), ∏ u ∈ insert v D, vertexWeight N θ ρ u bot top =
        ∑ top : E → Finset (Finset X), (∏ u ∈ D, vertexWeight N θ ρ u bot top) *
          allocationFactor N θ ρ (arrivingForest N top v) v bot := by
    intro bot
    have := card_pow_mul_sum_mul_eq S
      (fun top : E → Finset (Finset X) => (∏ u ∈ D, vertexWeight N θ ρ u bot top) *
        allocationFactor N θ ρ (arrivingForest N top v) v bot)
      (fun top => ∏ e ∈ S, kingmanTransition (θ.length e) (bot e) (top e))
      (fun top y => by simp only [hgtop, harr])
      (fun top htop => by
        have hprod := left_ne_zero_of_mul htop
        have hall := right_ne_zero_of_mul htop
        have hF := frontier_of_prod_ne_zero hN hD hprod
        have hg := hF.good_arrivingForest hvD hch
        obtain ⟨a, ha⟩ := exists_assignment hall
        have hsimp : ∀ y : E → Finset (Finset X),
            ∏ e ∈ S, kingmanTransition (θ.length e) (bot e) (overwrite S top y e) =
              ∏ e ∈ S, kingmanTransition (θ.length e) (bot e) (y e) := fun y =>
          prod_congr rfl fun e he => by rw [overwrite_of_mem he]
        simp only [hsimp]
        refine sum_prod_of_sum_eq_one S _ fun e he => ?_
        refine kingmanTransition_sum ?_ _
        rw [ha ⟨e, mem_arcsInto.1 he⟩]
        exact (isGoodForest_forestBelow hg).1)
    rw [← this]
    congr 1
    refine sum_congr rfl fun top _ => ?_
    rw [prod_insert hvD]
    unfold vertexWeight
    ring
  -- summing out the bottoms of the arcs entering `v`
  have hbot : ∀ top : E → Finset (Finset X),
      B ^ #S * ∑ bot : E → Finset (Finset X), (∏ u ∈ D, vertexWeight N θ ρ u bot top) *
          allocationFactor N θ ρ (arrivingForest N top v) v bot =
        ∑ bot : E → Finset (Finset X), ∏ u ∈ D, vertexWeight N θ ρ u bot top := by
    intro top
    refine card_pow_mul_sum_mul_eq S _ _ (fun bot y => hgbot top bot y) fun bot _ => ?_
    have hsimp : ∀ y : E → Finset (Finset X),
        allocationFactor N θ ρ (arrivingForest N top v) v (overwrite S bot y) =
          allocationFactor N θ ρ (arrivingForest N top v) v y := fun y =>
      allocationFactor_congr fun e he => overwrite_of_mem (mem_arcsInto.2 he) _ _
    simp only [hsimp]
    exact sum_allocationFactor hN hθ hρ hv _
  calc (B ^ #S) ^ 2 * ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          ∏ u ∈ insert v D, vertexWeight N θ ρ u bot top
      = B ^ #S * ∑ bot : E → Finset (Finset X), (B ^ #S *
          ∑ top : E → Finset (Finset X), ∏ u ∈ insert v D, vertexWeight N θ ρ u bot top) := by
        rw [← mul_sum, ← mul_assoc, sq]
    _ = B ^ #S * ∑ top : E → Finset (Finset X), ∑ bot : E → Finset (Finset X),
          (∏ u ∈ D, vertexWeight N θ ρ u bot top) *
            allocationFactor N θ ρ (arrivingForest N top v) v bot := by
        simp only [htop]
        rw [sum_comm]
    _ = ∑ top : E → Finset (Finset X), ∑ bot : E → Finset (Finset X),
          ∏ u ∈ D, vertexWeight N θ ρ u bot top := by
        rw [mul_sum]
        exact sum_congr rfl fun top _ => hbot top
    _ = _ := sum_comm

/-- The sum over the histories of the factors of a set `D` closed under children, up to the number
of values of the arcs not entering `D`. -/
theorem sum_sum_prod_vertexWeight (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {D : Finset V} (hD : DownClosed N D) (hroot : N.root ∉ D) :
    ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 *
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          ∏ u ∈ D, vertexWeight N θ ρ u bot top =
      ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card E) ^ 2 := by
  induction D using Finset.strongInduction with
  | H D ih =>
    rcases D.eq_empty_or_nonempty with rfl | hne
    · simp [sum_const, sq]
    · obtain ⟨v, hv, hD', hch⟩ := exists_top_vertex hN hD hne
      have hvr : v ≠ N.root := fun h => hroot (h ▸ hv)
      have hstep := sum_step hN hθ hρ hD' (notMem_erase v D) hvr hch
      rw [insert_erase hv] at hstep
      have hih := ih (D.erase v) (erase_ssubset hv) hD' fun h => hroot (mem_of_mem_erase h)
      rw [← hih, ← hstep, ← mul_assoc, ← mul_pow, ← pow_add]
      congr 3
      have hdis : Disjoint (univ.filter fun e => N.graph.target e ∈ D.erase v) (arcsInto N v) :=
        disjoint_left.2 fun e he he' =>
          notMem_erase v D (mem_arcsInto.1 he' ▸ (mem_filter.1 he).2)
      rw [← card_union_of_disjoint hdis]
      congr 1
      ext e
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_arcsInto, mem_erase]
      constructor
      · intro he
        by_cases h : N.graph.target e = v
        · exact Or.inr h
        · exact Or.inl ⟨h, he⟩
      · rintro (⟨-, he⟩ | he)
        · exact he
        · exact he ▸ hv

/-- **The histories of the network multispecies coalescent have total mass one.** -/
theorem sum_sum_historyWeight (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      historyWeight N θ ρ bot top = 1 := by
  have hD : DownClosed N (univ.erase N.root) := fun e _ =>
    mem_erase.2 ⟨target_ne_root hN e, mem_univ _⟩
  have h := sum_sum_prod_vertexWeight (θ := θ) (ρ := ρ) hN hθ hρ hD (notMem_erase _ _)
  have hall : (univ.filter fun e => N.graph.target e ∈ univ.erase N.root) = univ :=
    filter_true_of_mem fun e _ => mem_erase.2 ⟨target_ne_root hN e, mem_univ _⟩
  rw [hall, card_univ] at h
  have hB : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
  have h' := mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero _ hB.ne')) (h.trans (mul_one _).symm)
  simp only [historyWeight_eq_prod hN]
  exact h'

end Mass

/-! ### A history of positive weight -/

section Chain

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

variable (N) in
/-- One step up the chosen parent arcs. -/
def StepUp (p : V → E) (u w : V) : Prop := u ≠ N.root ∧ w = N.graph.source (p u)

variable (N) in
/-- The taxa whose lineage reaches `v` along the chosen parent arcs. -/
def chainTaxa (p : V → E) (v : V) : Finset X :=
  univ.filter fun x => Relation.ReflTransGen (StepUp N p) (N.leaf x) v

variable (N) in
/-- The forest at the arc `e` when every lineage takes the chosen parent arc and none coalesce. -/
def chainForest (p : V → E) (e : E) : Finset (Finset X) :=
  if p (N.graph.target e) = e then
    (chainTaxa N p (N.graph.target e)).image fun x => ({x} : Finset X)
  else ∅

omit [Fintype V] [Fintype E] in
theorem isGoodForest_chainForest (p : V → E) (e : E) :
    IsGoodForest (chainForest N p e) := by
  unfold chainForest
  split_ifs
  · exact isGoodForest_singletons _
  · exact isGoodForest_empty

omit [Fintype V] in
theorem arrivingForest_chain (hN : N.IsPhylogenetic) {p : V → E}
    (hp : ∀ v, v ≠ N.root → N.graph.target (p v) = v) (v : V) :
    arrivingForest N (chainForest N p) v =
      (chainTaxa N p v).image fun x => ({x} : Finset X) := by
  ext A
  unfold arrivingForest
  simp only [mem_union, mem_image, mem_filter, mem_univ, true_and, mem_biUnion, chainTaxa]
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨e, he, hA⟩)
    · exact ⟨x, hx ▸ Relation.ReflTransGen.refl, rfl⟩
    · unfold chainForest at hA
      split_ifs at hA with hpe
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hA
        refine ⟨x, ?_, rfl⟩
        refine Relation.ReflTransGen.tail (mem_filter.1 hx).2 ⟨target_ne_root hN e, ?_⟩
        rw [hpe, he]
      · exact absurd hA (notMem_empty _)
  · rintro ⟨x, hx, rfl⟩
    rcases Relation.ReflTransGen.cases_tail hx with h | ⟨u, hu, hne, hs⟩
    · exact Or.inl ⟨x, h.symm, rfl⟩
    · refine Or.inr ⟨p u, hs.symm, ?_⟩
      unfold chainForest
      rw [hp u hne, ite_eq_left rfl]
      exact mem_image.2 ⟨x, mem_filter.2 ⟨mem_univ _, hu⟩, rfl⟩

omit [Fintype V] [Fintype E] [DecidableEq X] [Fintype X] in
/-- Every vertex reaches the root along the chosen parent arcs. -/
theorem stepUp_reaches_root (hN : N.IsPhylogenetic) {p : V → E}
    (hp : ∀ v, v ≠ N.root → N.graph.target (p v) = v) (v : V) :
    Relation.ReflTransGen (StepUp N p) v N.root := by
  have : Finite V := hN.finite_vertices
  have : IsTrans V (Relation.TransGen N.graph.Adj) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen N.graph.Adj) := ⟨hN.acyclic⟩
  have hwf : WellFounded (Relation.TransGen N.graph.Adj) :=
    Finite.wellFounded_of_trans_of_irrefl _
  induction v using hwf.induction with
  | _ v ih =>
    by_cases hv : v = N.root
    · exact hv ▸ Relation.ReflTransGen.refl
    · have hadj : N.graph.Adj (N.graph.source (p v)) v := ⟨p v, rfl, hp v hv⟩
      exact Relation.ReflTransGen.head ⟨hv, rfl⟩ (ih _ (Relation.TransGen.single hadj))

omit [Fintype V] in
/-- The forest of all taxa arrives at the root. -/
theorem arrivingForest_chain_root (hN : N.IsPhylogenetic) {p : V → E}
    (hp : ∀ v, v ≠ N.root → N.graph.target (p v) = v) :
    arrivingForest N (chainForest N p) N.root = univ.image fun x => ({x} : Finset X) := by
  rw [arrivingForest_chain hN hp]
  congr 1
  exact filter_true_of_mem fun x _ => stepUp_reaches_root hN hp _

omit [Fintype V] in
/-- All lineages take the chosen parent arc: a term of the allocation factor. -/
theorem allocationFactor_chain_pos (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {p : V → E} (hp : ∀ v, v ≠ N.root → N.graph.target (p v) = v) {v : V}
    (hv : v ≠ N.root) :
    0 < allocationFactor N θ ρ (arrivingForest N (chainForest N p) v) v (chainForest N p) := by
  rw [arrivingForest_chain hN hp]
  set F := (chainTaxa N p v).image fun x => ({x} : Finset X) with hFdef
  let e₀ : {e // N.graph.target e = v} := ⟨p v, hp v hv⟩
  let a₀ : {A // A ∈ roots F} → {e // N.graph.target e = v} := fun _ => e₀
  have hmatch : ∀ e : {e // N.graph.target e = v},
      chainForest N p e.val =
        forestBelow F ((univ.filter fun r => a₀ r = e).image Subtype.val) := by
    intro e
    unfold chainForest
    rw [e.property]
    by_cases he : e₀ = e
    · have hval : p v = e.val := congrArg Subtype.val he
      rw [ite_eq_left hval]
      have hfil : (univ.filter fun r : {A // A ∈ roots F} => a₀ r = e) = univ :=
        filter_true_of_mem fun _ _ => he
      rw [hfil]
      ext A
      rw [mem_forestBelow]
      constructor
      · intro hA
        obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
        exact ⟨hA, R, mem_image.2 ⟨⟨R, hR⟩, mem_univ _, rfl⟩, hAR⟩
      · exact fun h => h.1
    · have hval : p v ≠ e.val := fun h => he (Subtype.ext h)
      rw [ite_eq_right hval]
      have hfil : (univ.filter fun r : {A // A ∈ roots F} => a₀ r = e) = ∅ :=
        filter_false_of_mem fun _ _ => he
      rw [hfil, image_empty]
      ext A
      simp [mem_forestBelow]
  have hpos : 0 < allocationWeight ρ
      (fun e : {e // N.graph.target e = v} => θ.inheritance e.val) a₀ :=
    allocationWeight_const_pos hρ.1 hρ.2 (inheritance_pos hθ e₀.val)
  refine lt_of_lt_of_le hpos ?_
  unfold allocationFactor
  have h := single_le_sum (s := univ) (a := a₀)
    (f := fun a => if ∀ e : {e // N.graph.target e = v},
        chainForest N p e.val =
          forestBelow F ((univ.filter fun r => a r = e).image Subtype.val) then
      allocationWeight ρ (fun e : {e // N.graph.target e = v} => θ.inheritance e.val) a else 0)
    (fun a _ => by
      split_ifs
      · exact allocationWeight_nonneg hρ.1 hρ.2 (fun e => (inheritance_pos hθ e.val).le) a
      · exact le_rfl) (mem_univ _)
  simpa only [hmatch, implies_true, ↓reduceIte] using h

/-- **A history without coalescence** has positive weight, and all the taxa arrive at the root
uncoalesced. -/
theorem exists_chain_history (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    ∃ top : E → Finset (Finset X), 0 < historyWeight N θ ρ top top ∧
      arrivingForest N top N.root = univ.image fun x => ({x} : Finset X) := by
  have : Nonempty E := nonempty_arcs hN
  obtain ⟨p, hp⟩ : ∃ p : V → E, ∀ v, v ≠ N.root → N.graph.target (p v) = v := by
    have h : ∀ v, ∃ e, v ≠ N.root → N.graph.target e = v := by
      intro v
      by_cases hv : v = N.root
      · exact ⟨Classical.arbitrary E, fun h => absurd hv h⟩
      · obtain ⟨e, he⟩ := exists_arc_into hN hv
        exact ⟨e, fun _ => he⟩
    exact Classical.axiomOfChoice h
  refine ⟨chainForest N p, ?_, arrivingForest_chain_root hN hp⟩
  refine mul_pos (prod_pos fun v hv => ?_) (prod_pos fun e _ => ?_)
  · exact allocationFactor_chain_pos hN hθ hρ hp (ne_of_mem_erase hv)
  · rw [kingmanTransition_apply_self (isGoodForest_chainForest p e).1]
    exact Real.exp_pos _

end Chain

end NMSC

end Phylogenetics
