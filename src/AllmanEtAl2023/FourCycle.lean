module

public import AllmanEtAl2023.CFGeometry
public import AllmanEtAl2023.BlobStructure
public import Basic.NMSCChain

/-!
# Allman, Baños, Mitchell, Rhodes 2023: "all points off the line segments arise from level-1 networks with 4-cycles"

"By Baños (2019), all points off the line segments arise from level-1 networks with 4-cycles. Although a network with a more complicated 4-blob may produce a CF on the line segments for certain numerical
parameters, this cannot happen for generic parameters by Theorem 1" (after Proposition 1).

Baños's theorem is cited, and the proof here is ours. `network a b c d` is a 4-cycle `top, left, hybrid, right`, with a taxon at each of `left`, `right`, `hybrid`, and the root above `top`, with the taxon `d`. It is level 1:
`isBridge_network_iff`.

Since `a` is the only taxon below the hybrid node, the `CF` is a mixture of two trees: `nmscCF_network`. If the `CF` is `(B + s, A + s, s)`, with `A, B, s > 0`, the mixing parameter can be any `γ` in `(A, 1 - B)`, and the lengths
of the edges from `top` follow: `exists_params`. `exists_cfTriple_eq` is the statement of the paper, and `exists_isCutCF` says that this network itself can have a `CF` on the line segments.

The computation follows the chain on the network, with the lemmas of `Basic.NMSCChain`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open Phylogenetics.NMSC.Chain
open scoped Classical

namespace AllmanEtAl2023.FourCycle

/-- The nodes of the network: `hybrid` is the hybrid node of the 4-cycle `top, left, hybrid, right`. -/
inductive Vertex (X : Type*)
  | root | top | left | right | hybrid
  | taxon (x : X)

/-- The edges of the network. -/
inductive Edge
  | rootTaxon | rootTop | topLeft | topRight | leftTaxon | leftHybrid | rightTaxon | rightHybrid | hybridTaxon
  deriving DecidableEq

instance : Fintype Edge :=
  ⟨{.rootTaxon, .rootTop, .topLeft, .topRight, .leftTaxon, .leftHybrid, .rightTaxon, .rightHybrid, .hybridTaxon}, fun e => by cases e <;> decide⟩

variable {X : Type*}

instance [Fintype X] : Fintype (Vertex X) :=
  ⟨({.root, .top, .left, .right, .hybrid} : Finset (Vertex X)) ∪ univ.image .taxon, fun v => by cases v <;> simp⟩

/-- **A level-1 network with a 4-cycle.** The taxon `a` is below the hybrid node, `c` at `left`, `b` at `right`, and `d` at the root. -/
def network (a b c d : X) : RootedNetwork (Vertex X) Edge X where
  graph :=
    { source := fun
        | .rootTaxon => .root | .rootTop => .root | .topLeft => .top | .topRight => .top | .leftTaxon => .left
        | .leftHybrid => .left | .rightTaxon => .right | .rightHybrid => .right | .hybridTaxon => .hybrid
      target := fun
        | .rootTaxon => .taxon d | .rootTop => .top | .topLeft => .left | .topRight => .right | .leftTaxon => .taxon c
        | .leftHybrid => .hybrid | .rightTaxon => .taxon b | .rightHybrid => .hybrid | .hybridTaxon => .taxon a }
  root := .root
  leaf := .taxon

variable {a b c d : X}

@[simp] theorem source_rootTaxon : (network a b c d).graph.source .rootTaxon = .root := rfl
@[simp] theorem source_rootTop : (network a b c d).graph.source .rootTop = .root := rfl
@[simp] theorem source_topLeft : (network a b c d).graph.source .topLeft = .top := rfl
@[simp] theorem source_topRight : (network a b c d).graph.source .topRight = .top := rfl
@[simp] theorem source_leftTaxon : (network a b c d).graph.source .leftTaxon = .left := rfl
@[simp] theorem source_leftHybrid : (network a b c d).graph.source .leftHybrid = .left := rfl
@[simp] theorem source_rightTaxon : (network a b c d).graph.source .rightTaxon = .right := rfl
@[simp] theorem source_rightHybrid : (network a b c d).graph.source .rightHybrid = .right := rfl
@[simp] theorem source_hybridTaxon : (network a b c d).graph.source .hybridTaxon = .hybrid := rfl
@[simp] theorem target_rootTaxon : (network a b c d).graph.target .rootTaxon = .taxon d := rfl
@[simp] theorem target_rootTop : (network a b c d).graph.target .rootTop = .top := rfl
@[simp] theorem target_topLeft : (network a b c d).graph.target .topLeft = .left := rfl
@[simp] theorem target_topRight : (network a b c d).graph.target .topRight = .right := rfl
@[simp] theorem target_leftTaxon : (network a b c d).graph.target .leftTaxon = .taxon c := rfl
@[simp] theorem target_leftHybrid : (network a b c d).graph.target .leftHybrid = .hybrid := rfl
@[simp] theorem target_rightTaxon : (network a b c d).graph.target .rightTaxon = .taxon b := rfl
@[simp] theorem target_rightHybrid : (network a b c d).graph.target .rightHybrid = .hybrid := rfl
@[simp] theorem target_hybridTaxon : (network a b c d).graph.target .hybridTaxon = .taxon a := rfl

section Graph

variable [Fintype X] [DecidableEq X] (h : ({a, b, c, d} : Finset X).card = 4) (hcard : Fintype.card X = 4)

include h hcard in
/-- It is a phylogenetic network. -/
theorem isPhylogenetic_network : (network a b c d).IsPhylogenetic := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hall := Bridges.forall_eq_of_card_four hcard h
  refine isPhylogenetic_of_rank (fun | .root => 0 | .top => 1 | .left => 2 | .right => 2 | .hybrid => 3 | .taxon _ => 4) (fun e => by cases e <;> simp)
    (fun e => by cases e <;> simp [network]) (fun v hv => ?_) (fun x y hxy => Vertex.taxon.inj hxy) (fun x => ?_) (fun x e => ?_) (fun v hv => ?_)
  · cases v with
    | root => exact absurd rfl hv
    | top => exact ⟨.rootTop, rfl⟩
    | left => exact ⟨.topLeft, rfl⟩
    | right => exact ⟨.topRight, rfl⟩
    | hybrid => exact ⟨.leftHybrid, rfl⟩
    | taxon x =>
      rcases hall x with rfl | rfl | rfl | rfl
      · exact ⟨.hybridTaxon, rfl⟩
      · exact ⟨.rightTaxon, rfl⟩
      · exact ⟨.leftTaxon, rfl⟩
      · exact ⟨.rootTaxon, rfl⟩
  · rcases hall x with rfl | rfl | rfl | rfl
    · exact ⟨.hybridTaxon, rfl, fun f hf => by cases f <;> simp_all [network]⟩
    · exact ⟨.rightTaxon, rfl, fun f hf => by cases f <;> simp_all [network]⟩
    · exact ⟨.leftTaxon, rfl, fun f hf => by cases f <;> simp_all [network]⟩
    · exact ⟨.rootTaxon, rfl, fun f hf => by cases f <;> simp_all [network]⟩
  · cases e <;> simp [network]
  · cases v with
    | root => exact ⟨.rootTop, rfl⟩
    | top => exact ⟨.topLeft, rfl⟩
    | left => exact ⟨.leftTaxon, rfl⟩
    | right => exact ⟨.rightTaxon, rfl⟩
    | hybrid => exact ⟨.hybridTaxon, rfl⟩
    | taxon x => exact absurd rfl (hv x)

end Graph

/-! ### Where the lineages go -/

section Chain

variable {L : Type*} [DecidableEq L]

/-- A cherry with singletons is a good forest. -/
theorem isGoodForest_insert_pair {T P : Finset L} (hP : P ⊆ T) (hc : #P = 2) : IsGoodForest (insert P (T.image fun x => ({x} : Finset L))) := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hc
  refine ⟨⟨fun A hA => ?_, fun A hA B hB => ?_⟩, fun A hA h2 => ?_⟩
  · rcases mem_insert.1 hA with rfl | hA
    · exact ⟨x, by simp⟩
    · obtain ⟨z, -, rfl⟩ := mem_image.1 hA
      exact singleton_nonempty z
  · rcases mem_insert.1 hA with rfl | hA <;> rcases mem_insert.1 hB with rfl | hB
    · exact Or.inl (Subset.refl _)
    · obtain ⟨z, -, rfl⟩ := mem_image.1 hB
      by_cases hz : z ∈ ({x, y} : Finset L)
      · exact Or.inr (Or.inl (singleton_subset_iff.2 hz))
      · exact Or.inr (Or.inr (disjoint_singleton_right.2 hz))
    · obtain ⟨z, -, rfl⟩ := mem_image.1 hA
      by_cases hz : z ∈ ({x, y} : Finset L)
      · exact Or.inl (singleton_subset_iff.2 hz)
      · exact Or.inr (Or.inr (disjoint_singleton_left.2 hz))
    · obtain ⟨z, -, rfl⟩ := mem_image.1 hA
      obtain ⟨w, -, rfl⟩ := mem_image.1 hB
      by_cases hz : z = w
      · exact Or.inl (by rw [hz])
      · exact Or.inr (Or.inr (disjoint_singleton.2 hz))
  · rcases mem_insert.1 hA with rfl | hA
    · exact ⟨{x}, mem_insert_of_mem (mem_image.2 ⟨x, hP (by simp), rfl⟩), {y}, mem_insert_of_mem (mem_image.2 ⟨y, hP (by simp), rfl⟩), disjoint_singleton.2 hxy, rfl⟩
    · obtain ⟨z, -, rfl⟩ := mem_image.1 hA
      simp at h2

/-- The lineages of a cherry with singletons. -/
theorem lineages_insert_pair [Fintype L] {T P : Finset L} (hP : P ⊆ T) : lineages (insert P (T.image fun x => ({x} : Finset L))) = T := by
  ext z
  rw [mem_lineages]
  constructor
  · rintro ⟨A, hA, hz⟩
    rcases mem_insert.1 hA with rfl | hA
    · exact hP hz
    · obtain ⟨w, hw, rfl⟩ := mem_image.1 hA
      rwa [mem_singleton.1 hz]
  · exact fun hz => ⟨{z}, mem_insert_of_mem (mem_image.2 ⟨z, hz, rfl⟩), mem_singleton_self z⟩

variable [Fintype X] [DecidableEq X]

/-- The forests `F` at `top` and `G` at the root. -/
def twoInj (F G : Finset (Finset X)) : Vertex X → Finset (Finset X) := fun
  | .top => F
  | .root => G
  | _ => ∅

omit [Fintype X] in
theorem validInj_twoInj {F G : Finset (Finset X)} (hF : IsGoodForest F) (hG : IsGoodForest G) (hd : Disjoint (lineages F) (lineages G)) : ValidInj (twoInj F G) := by
  refine ⟨fun v => ?_, fun p v huv => ?_⟩
  · cases v <;> first | exact hF | exact hG | exact isGoodForest_empty
  · cases p <;> cases v <;> first
      | exact absurd rfl huv
      | exact hd
      | exact hd.symm
      | simp [twoInj]

variable (h : ({a, b, c, d} : Finset X).card = 4) (hcard : Fintype.card X = 4)

/-- The nodes of the taxa. -/
def D₀ (a b c d : X) : Finset (Vertex X) := {.taxon a, .taxon b, .taxon c, .taxon d}

/-- The nodes below `top`. -/
def D₃ (a b c d : X) : Finset (Vertex X) := insert .right (insert .left (insert .hybrid (D₀ a b c d)))

omit [Fintype X] [DecidableEq X] in
theorem mem_D₀ {v : Vertex X} : v ∈ D₀ a b c d ↔ v = .taxon a ∨ v = .taxon b ∨ v = .taxon c ∨ v = .taxon d := by
  simp [D₀]

omit [Fintype X] [DecidableEq X] in
theorem downClosed_D₀ : DownClosed (network a b c d) (D₀ a b c d) := fun e he => by
  cases e <;> simp [mem_D₀, network] at he ⊢

omit [Fintype X] [DecidableEq X] in
theorem root_notMem_D₀ : (network a b c d).root ∉ D₀ a b c d := by
  simp [mem_D₀, network]

include h hcard in
/-- The lineages in `D₃` lifted to `top` and to the root. -/
theorem liftSet_D₃ (τ : Edge → Finset (Finset X)) :
    liftSet (network a b c d) (D₃ a b c d) (taxaInj (network a b c d) univ) τ = twoInj (τ .topLeft ∪ τ .topRight) (τ .rootTaxon) := by
  have hall := Bridges.forall_eq_of_card_four hcard h
  have hemp : ∀ {v : Vertex X}, (∀ x, Vertex.taxon x ≠ v) → taxaInj (network a b c d) univ v = ∅ := fun hv => taxaInj_eq_empty hv
  funext v
  unfold liftSet
  cases v with
  | root =>
    rw [ite_eq_right (by simp [D₃, mem_D₀]), hemp (by simp)]
    have : (univ.filter fun f => (network a b c d).graph.source f = .root ∧ (network a b c d).graph.target f ∈ D₃ a b c d) = {.rootTaxon} := by
      ext f
      cases f <;> simp [D₃, mem_D₀]
    rw [this]
    simp [twoInj]
  | top =>
    rw [ite_eq_right (by simp [D₃, mem_D₀]), hemp (by simp)]
    have : (univ.filter fun f => (network a b c d).graph.source f = .top ∧ (network a b c d).graph.target f ∈ D₃ a b c d) = {.topLeft, .topRight} := by
      ext f
      cases f <;> simp [D₃, mem_D₀]
    rw [this]
    simp [twoInj, biUnion_insert]
  | left => rw [ite_eq_left (by simp [D₃])]; rfl
  | right => rw [ite_eq_left (by simp [D₃])]; rfl
  | hybrid => rw [ite_eq_left (by simp [D₃])]; rfl
  | taxon x =>
    rw [ite_eq_left (by
      rcases hall x with rfl | rfl | rfl | rfl <;> simp [D₃, mem_D₀])]
    rfl

end Chain

section CF

variable [Fintype X] [DecidableEq X] (h : ({a, b, c, d} : Finset X).card = 4) (hcard : Fintype.card X = 4) {θ : MetricData Edge}

local notation "𝐍" => network a b c d
local notation "inj" => taxaInj (network a b c d) (univ : Finset X)

omit [Fintype X] [DecidableEq X] in
theorem hu_hybrid {f : Edge} : (𝐍).graph.target f = .hybrid → f = .leftHybrid ∨ f = .rightHybrid := by
  cases f <;> simp

omit [Fintype X] [DecidableEq X] in
theorem hu_left {f : Edge} : (𝐍).graph.target f = .left → f = .topLeft := by
  cases f <;> simp

omit [Fintype X] [DecidableEq X] in
theorem hu_right {f : Edge} : (𝐍).graph.target f = .right → f = .topRight := by
  cases f <;> simp

theorem arriving_hybrid (top : Edge → Finset (Finset X)) : arriving 𝐍 inj top .hybrid = top .hybridTaxon := by
  rw [arriving_eq_biUnion (S := {.hybridTaxon}) (fun f => by cases f <;> simp), taxaInj_eq_empty (by simp [network])]
  simp

theorem arriving_left (top : Edge → Finset (Finset X)) : arriving 𝐍 inj top .left = top .leftTaxon ∪ top .leftHybrid := by
  rw [arriving_eq_biUnion (S := {.leftTaxon, .leftHybrid}) (fun f => by cases f <;> simp), taxaInj_eq_empty (by simp [network])]
  simp [biUnion_insert]

theorem arriving_right (top : Edge → Finset (Finset X)) : arriving 𝐍 inj top .right = top .rightTaxon ∪ top .rightHybrid := by
  rw [arriving_eq_biUnion (S := {.rightTaxon, .rightHybrid}) (fun f => by cases f <;> simp), taxaInj_eq_empty (by simp [network])]
  simp [biUnion_insert]

/-- The hybrid node, with one lineage. -/
theorem step_hybrid (Ψ : (Edge → Finset (Finset X)) → ℝ) (top : Edge → Finset (Finset X)) {x : X} (ht : top .hybridTaxon = {{x}}) :
    stepKernel 𝐍 θ 0 inj .hybrid Ψ top =
      θ.inheritance .leftHybrid * Ψ (ow (arcsInto 𝐍 .hybrid) top (pairFn .leftHybrid {{x}} .rightHybrid ∅)) +
        θ.inheritance .rightHybrid * Ψ (ow (arcsInto 𝐍 .hybrid) top (pairFn .leftHybrid ∅ .rightHybrid {{x}})) := by
  unfold stepKernel
  rw [arriving_hybrid, ht]
  exact stepOf_two_one (N := 𝐍) (θ := θ) (ρ := 0) (k₁ := Edge.leftHybrid) (k₂ := Edge.rightHybrid) rfl rfl (by decide) (fun f => hu_hybrid) (isForest_singleton_singleton x) (roots_singleton_singleton x)
    (fun t => Ψ (ow (arcsInto 𝐍 .hybrid) top t)) (ow_dep (arcsInto 𝐍 .hybrid) top Ψ)

/-- A node with one parent `e`, and two lineages. -/
theorem step_two {v : Vertex X} {e : Edge} (he : (𝐍).graph.target e = v) (hu : ∀ f, (𝐍).graph.target f = v → f = e) (hγ : θ.inheritance e = 1) {P : Finset X} (hP : #P = 2)
    (Φ : (Edge → Finset (Finset X)) → ℝ) (top : Edge → Finset (Finset X)) (ht : arriving 𝐍 inj top v = P.image fun x => ({x} : Finset X)) :
    stepKernel 𝐍 θ 0 inj v Φ top =
      Real.exp (-θ.length e) * Φ (ow (arcsInto 𝐍 v) top fun _ => P.image fun x => ({x} : Finset X)) +
        (1 - Real.exp (-θ.length e)) * Φ (ow (arcsInto 𝐍 v) top fun _ => insert P (P.image fun x => ({x} : Finset X))) := by
  unfold stepKernel
  rw [ht]
  exact stepOf_unique_two (N := 𝐍) (θ := θ) (e := e) le_rfl he hu hγ hP (fun t => Φ (ow (arcsInto 𝐍 v) top t)) (ow_dep (arcsInto 𝐍 v) top Φ)

/-- A node with one parent `e`, and one lineage. -/
theorem step_one {v : Vertex X} {e : Edge} (he : (𝐍).graph.target e = v) (hu : ∀ f, (𝐍).graph.target f = v → f = e) (hγ : θ.inheritance e = 1) {x : X}
    (Φ : (Edge → Finset (Finset X)) → ℝ) (top : Edge → Finset (Finset X)) (ht : arriving 𝐍 inj top v = {{x}}) :
    stepKernel 𝐍 θ 0 inj v Φ top = Φ (ow (arcsInto 𝐍 v) top fun _ => {{x}}) := by
  unfold stepKernel
  rw [ht]
  refine stepOf_unique_det (N := 𝐍) (θ := θ) (e := e) le_rfl he hu hγ (isForest_singleton_singleton x) ?_ (fun t => Φ (ow (arcsInto 𝐍 v) top t)) (ow_dep (arcsInto 𝐍 v) top Φ)
  rw [roots_singleton_singleton]
  simp

omit [Fintype X] in
/-- The forests of the singletons of `{x, y}`. -/
theorem union_singletons {x y : X} : ({{x}} ∪ {{y}} : Finset (Finset X)) = ({y, x} : Finset X).image fun z => ({z} : Finset X) := by
  ext A
  simp [or_comm]

omit [Fintype X] in
theorem subset_pair_three {x y z : X} : ({x, y} : Finset X) ⊆ {x, y, z} := by
  intro w hw
  simp only [mem_insert, mem_singleton] at hw ⊢
  tauto

omit [Fintype X] in
theorem union_e₁ {x y z : X} : ((({x, y} : Finset X).image fun w => ({w} : Finset X)) ∪ {{z}}) = ({x, y, z} : Finset X).image fun w => ({w} : Finset X) := by
  ext A
  simp only [mem_union, mem_image, mem_insert, mem_singleton]
  grind

omit [Fintype X] in
theorem union_e₂ {x y z : X} : (insert ({x, y} : Finset X) (({x, y} : Finset X).image fun w => ({w} : Finset X)) ∪ {{z}}) = insert ({x, y} : Finset X) (({x, y, z} : Finset X).image fun w => ({w} : Finset X)) := by
  ext A
  simp only [mem_union, mem_image, mem_insert, mem_singleton]
  grind

omit [Fintype X] in
theorem union_e₃ {x y z : X} : (({{x}} : Finset (Finset X)) ∪ (({y, z} : Finset X).image fun w => ({w} : Finset X))) = ({x, y, z} : Finset X).image fun w => ({w} : Finset X) := by
  ext A
  simp only [mem_union, mem_image, mem_insert, mem_singleton]
  grind

omit [Fintype X] in
theorem union_e₄ {x y z : X} : (({{x}} : Finset (Finset X)) ∪ insert ({y, z} : Finset X) (({y, z} : Finset X).image fun w => ({w} : Finset X))) = insert ({y, z} : Finset X) (({x, y, z} : Finset X).image fun w => ({w} : Finset X)) := by
  ext A
  simp only [mem_union, mem_image, mem_insert, mem_singleton]
  grind

include h hcard in
/-- Three lineages at `top`. -/
theorem cherryMass_three (hθ : (𝐍).IsMetric θ) {x y z : X} (hset : ∀ w, w = d ∨ w = x ∨ w = y ∨ w = z) (hd : d ∉ ({x, y, z} : Finset X)) (r : QuartetTree X) :
    cherryMass 𝐍 θ 0 (twoInj (({x, y, z} : Finset X).image fun w => ({w} : Finset X)) {{d}}) r = 1 / 3 := by
  have hP := isPhylogenetic_network h hcard
  have hq : (univ : Finset X).card = 4 := by rw [card_univ, hcard]
  have heq : twoInj (({x, y, z} : Finset X).image fun w => ({w} : Finset X)) {{d}} = placeInj univ (fun w : X => if w = d then Vertex.root else Vertex.top) := by
    funext v
    unfold placeInj
    have hT : ∀ w, w ≠ d ↔ w ∈ ({x, y, z} : Finset X) := fun w => by
      simp only [mem_insert, mem_singleton]
      constructor
      · intro hw
        exact (hset w).resolve_left hw
      · rintro hw rfl
        exact hd (by simpa using hw)
    cases v with
    | top =>
      have : (univ.filter fun w : X => (if w = d then Vertex.root else Vertex.top) = (Vertex.top : Vertex X)) = {x, y, z} := by
        ext w
        rw [← hT]
        by_cases hw : w = d <;> simp [hw]
      rw [this]
      rfl
    | root =>
      have : (univ.filter fun w : X => (if w = d then Vertex.root else Vertex.top) = (Vertex.root : Vertex X)) = {d} := by
        ext w
        by_cases hw : w = d <;> simp [hw]
      rw [this]
      simp [twoInj]
    | left =>
      have : (univ.filter fun w : X => (if w = d then Vertex.root else Vertex.top) = (Vertex.left : Vertex X)) = ∅ := by
        ext w
        by_cases hw : w = d <;> simp [hw]
      rw [this]
      simp [twoInj]
    | right =>
      have : (univ.filter fun w : X => (if w = d then Vertex.root else Vertex.top) = (Vertex.right : Vertex X)) = ∅ := by
        ext w
        by_cases hw : w = d <;> simp [hw]
      rw [this]
      simp [twoInj]
    | hybrid =>
      have : (univ.filter fun w : X => (if w = d then Vertex.root else Vertex.top) = (Vertex.hybrid : Vertex X)) = ∅ := by
        ext w
        by_cases hw : w = d <;> simp [hw]
      rw [this]
      simp [twoInj]
    | taxon t =>
      have : (univ.filter fun w : X => (if w = d then Vertex.root else Vertex.top) = (Vertex.taxon t : Vertex X)) = ∅ := by
        ext w
        by_cases hw : w = d <;> simp [hw]
      rw [this]
      simp [twoInj]
  rw [heq]
  refine cherryMass_placeInj_eq_third hP hθ ⟨le_rfl, zero_le_one⟩ (q := univ) hq (a := d) (mem_univ _) (v := .top) (fun w _ hw => ?_) ?_
  · simp [hw]
  · exact mem_treesOn.2 (eq_univ_of_card _ (r.card_taxa.trans hcard.symm))

include h hcard in
/-- A cherry at `top` decides. -/
theorem cherryMass_cherry (hθ : (𝐍).IsMetric θ) {T P : Finset X} (hPT : P ⊆ T) (hP2 : #P = 2) (hd : d ∉ T) (r : QuartetTree X) :
    cherryMass 𝐍 θ 0 (twoInj (insert P (T.image fun w => ({w} : Finset X))) {{d}}) r = if P ∈ r.val then 1 else 0 := by
  have hPh := isPhylogenetic_network h hcard
  have hs := isGoodForest_singletons ({d} : Finset X)
  rw [image_singleton] at hs
  have hdis : Disjoint (lineages (insert P (T.image fun w => ({w} : Finset X)))) (lineages ({{d}} : Finset (Finset X))) := by
    rw [lineages_insert_pair hPT]
    have : lineages ({{d}} : Finset (Finset X)) = {d} := by
      ext z
      simp
    rw [this]
    exact disjoint_singleton_right.2 hd
  have hv := validInj_twoInj (isGoodForest_insert_pair hPT hP2) hs hdis
  have htax : r.taxa = univ := eq_univ_of_card _ (r.card_taxa.trans hcard.symm)
  exact cherryMass_of_mem hPh hθ ⟨le_rfl, zero_le_one⟩ hv (v := .top) (C := P) (mem_insert_self _ _) hP2 (by rw [htax]; exact subset_univ _)

include h hcard in
/-- **The concordance factors of the 4-cycle**, a mixture of the trees `((a, c), b), d)` and `((a, b), c), d)`: only the edge of the cycle to each side counts, since the fourth lineage is at the root. -/
theorem nmscCF_network (hθ : (𝐍).IsMetric θ) (r : QuartetTree X) :
    nmscCF 𝐍 θ 0 r =
      θ.inheritance .leftHybrid * (Real.exp (-θ.length .topLeft) * (1 / 3) + (1 - Real.exp (-θ.length .topLeft)) * (if ({a, c} : Finset X) ∈ r.val then 1 else 0)) +
        θ.inheritance .rightHybrid * (Real.exp (-θ.length .topRight) * (1 / 3) + (1 - Real.exp (-θ.length .topRight)) * (if ({a, b} : Finset X) ∈ r.val then 1 else 0)) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hall := Bridges.forall_eq_of_card_four hcard h
  have hP := isPhylogenetic_network h hcard
  have htax : r.taxa = univ := eq_univ_of_card _ (r.card_taxa.trans hcard.symm)
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hdown₁ : DownClosed 𝐍 (insert .hybrid (D₀ a b c d)) := fun e he => by
    cases e <;> simp [mem_D₀] at he ⊢
  have hdown₂ : DownClosed 𝐍 (insert .left (insert .hybrid (D₀ a b c d))) := fun e he => by
    cases e <;> simp [mem_D₀] at he ⊢
  have hdown₃ : DownClosed 𝐍 (D₃ a b c d) := fun e he => by
    cases e <;> simp [D₃, mem_D₀] at he ⊢
  have hroot : (𝐍).root ∉ D₃ a b c d := by
    simp [D₃, mem_D₀, network]
  rw [nmscCF_eq_cherryMass hP hθ hρ r, htax, cherryMass_eq_meanOn_lift hP hθ.isNormalized le_rfl (validInj_taxaInj univ) hdown₃ hroot r]
  simp only [liftSet_D₃ h hcard]
  unfold D₃
  rw [meanOn_insert hdown₂ (by simp [mem_D₀]) (fun e he => by cases e <;> simp [mem_D₀] at he ⊢),
    meanOn_insert hdown₁ (by simp [mem_D₀]) (fun e he => by cases e <;> simp [mem_D₀] at he ⊢),
    meanOn_insert downClosed_D₀ (by simp [mem_D₀]) (fun e he => by cases e <;> simp [mem_D₀] at he ⊢)]
  refine meanOn_eq_const hP hθ.isNormalized le_rfl (validInj_taxaInj univ) downClosed_D₀ root_notMem_D₀ fun bot top hw => ?_
  have hs : ∀ (x : X) (e : Edge), (𝐍).graph.source e ≠ (𝐍).leaf x := fun x e => by
    cases e <;> simp [network]
  have hta : top .hybridTaxon = {{a}} := top_eq_of_leaf hP a (p := Edge.hybridTaxon) (fun f hf => by cases f <;> simp_all [network]) rfl (hs a) (by simp [mem_D₀, network]) hw
  have htb : top .rightTaxon = {{b}} := top_eq_of_leaf hP b (p := Edge.rightTaxon) (fun f hf => by cases f <;> simp_all [network]) rfl (hs b) (by simp [mem_D₀, network]) hw
  have htc : top .leftTaxon = {{c}} := top_eq_of_leaf hP c (p := Edge.leftTaxon) (fun f hf => by cases f <;> simp_all [network]) rfl (hs c) (by simp [mem_D₀, network]) hw
  have htd : top .rootTaxon = {{d}} := top_eq_of_leaf hP d (p := Edge.rootTaxon) (fun f hf => by cases f <;> simp_all [network]) rfl (hs d) (by simp [mem_D₀, network]) hw
  -- the edges from `top` have parameter one
  have hγl : θ.inheritance .topLeft = 1 := hθ.2.2.1 .topLeft (isTreeArc_of_unique fun f hf => hu_left hf)
  have hγr : θ.inheritance .topRight = 1 := hθ.2.2.1 .topRight (isTreeArc_of_unique fun f hf => hu_right hf)
  set Φ₀ : (Edge → Finset (Finset X)) → ℝ := fun τ => cherryMass 𝐍 θ 0 (twoInj (τ .topLeft ∪ τ .topRight) (τ .rootTaxon)) r with hΦ₀
  have hnr : ∀ {f : Edge} {v : Vertex X}, (𝐍).graph.target f ≠ v → f ∉ arcsInto 𝐍 v := fun hf hm => hf (mem_arcsInto.1 hm)
  have hmr : (Edge.topRight : Edge) ∈ arcsInto 𝐍 Vertex.right := mem_arcsInto.2 rfl
  have hml : (Edge.topLeft : Edge) ∈ arcsInto 𝐍 Vertex.left := mem_arcsInto.2 rfl
  have owR₁ : ∀ τ t : Edge → Finset (Finset X), ow (arcsInto 𝐍 Vertex.right) τ t .topLeft = τ .topLeft := fun τ t => ow_of_notMem (hnr (by simp)) τ t
  have owR₂ : ∀ τ t : Edge → Finset (Finset X), ow (arcsInto 𝐍 Vertex.right) τ t .topRight = t .topRight := fun τ t => ow_of_mem hmr τ t
  have owR₃ : ∀ τ t : Edge → Finset (Finset X), ow (arcsInto 𝐍 Vertex.right) τ t .rootTaxon = τ .rootTaxon := fun τ t => ow_of_notMem (hnr (by simp)) τ t
  have owL₁ : ∀ τ t : Edge → Finset (Finset X), ow (arcsInto 𝐍 Vertex.left) τ t .topLeft = t .topLeft := fun τ t => ow_of_mem hml τ t
  have owL₂ : ∀ τ t : Edge → Finset (Finset X), ow (arcsInto 𝐍 Vertex.left) τ t .rightHybrid = τ .rightHybrid := fun τ t => ow_of_notMem (hnr (by simp)) τ t
  have owL₃ : ∀ τ t : Edge → Finset (Finset X), ow (arcsInto 𝐍 Vertex.left) τ t .rightTaxon = τ .rightTaxon := fun τ t => ow_of_notMem (hnr (by simp)) τ t
  have owL₄ : ∀ τ t : Edge → Finset (Finset X), ow (arcsInto 𝐍 Vertex.left) τ t .rootTaxon = τ .rootTaxon := fun τ t => ow_of_notMem (hnr (by simp)) τ t
  -- the right node
  have hR₁ : ∀ (T : Edge → Finset (Finset X)) (G : Finset (Finset X)), T .rightHybrid = ∅ → T .rightTaxon = {{b}} → T .topLeft = G → T .rootTaxon = {{d}} →
      stepKernel 𝐍 θ 0 inj .right Φ₀ T = cherryMass 𝐍 θ 0 (twoInj (G ∪ {{b}}) {{d}}) r := by
    intro T G h₁ h₂ h₃ h₄
    rw [step_one (a := a) (b := b) (c := c) (d := d) (v := .right) (e := Edge.topRight) rfl (fun f => hu_right) hγr (x := b) Φ₀ T (by rw [arriving_right, h₁, h₂, union_empty])]
    simp only [hΦ₀, owR₁, owR₂, owR₃, h₃, h₄]
  have hR₂ : ∀ (T : Edge → Finset (Finset X)) (G : Finset (Finset X)), T .rightHybrid = {{a}} → T .rightTaxon = {{b}} → T .topLeft = G → T .rootTaxon = {{d}} →
      stepKernel 𝐍 θ 0 inj .right Φ₀ T =
        Real.exp (-θ.length .topRight) * cherryMass 𝐍 θ 0 (twoInj (G ∪ ({b, a} : Finset X).image fun z => ({z} : Finset X)) {{d}}) r +
          (1 - Real.exp (-θ.length .topRight)) * cherryMass 𝐍 θ 0 (twoInj (G ∪ insert ({b, a} : Finset X) (({b, a} : Finset X).image fun z => ({z} : Finset X))) {{d}}) r := by
    intro T G h₁ h₂ h₃ h₄
    have hc : #({b, a} : Finset X) = 2 := card_pair hab.symm
    rw [step_two (a := a) (b := b) (c := c) (d := d) (v := .right) (e := Edge.topRight) rfl (fun f => hu_right) hγr hc Φ₀ T (by rw [arriving_right, h₁, h₂, union_singletons, pair_comm a b])]
    simp only [hΦ₀, owR₁, owR₂, owR₃, h₃, h₄]
  -- the left node
  have hL₁ : ∀ T : Edge → Finset (Finset X), T .leftHybrid = {{a}} → T .leftTaxon = {{c}} → T .rightHybrid = ∅ → T .rightTaxon = {{b}} → T .rootTaxon = {{d}} →
      stepKernel 𝐍 θ 0 inj .left (stepKernel 𝐍 θ 0 inj .right Φ₀) T =
        Real.exp (-θ.length .topLeft) * cherryMass 𝐍 θ 0 (twoInj ((({c, a} : Finset X).image fun z => ({z} : Finset X)) ∪ {{b}}) {{d}}) r +
          (1 - Real.exp (-θ.length .topLeft)) * cherryMass 𝐍 θ 0 (twoInj (insert ({c, a} : Finset X) (({c, a} : Finset X).image fun z => ({z} : Finset X)) ∪ {{b}}) {{d}}) r := by
    intro T h₁ h₂ h₃ h₄ h₅
    have hc : #({c, a} : Finset X) = 2 := card_pair hac.symm
    rw [step_two (a := a) (b := b) (c := c) (d := d) (v := .left) (e := Edge.topLeft) rfl (fun f => hu_left) hγl hc _ T (by rw [arriving_left, h₁, h₂, union_singletons, pair_comm a c])]
    rw [hR₁ _ _ (by rw [owL₂, h₃]) (by rw [owL₃, h₄]) (owL₁ _ _) (by rw [owL₄, h₅]),
      hR₁ _ _ (by rw [owL₂, h₃]) (by rw [owL₃, h₄]) (owL₁ _ _) (by rw [owL₄, h₅])]
  have hL₂ : ∀ T : Edge → Finset (Finset X), T .leftHybrid = ∅ → T .leftTaxon = {{c}} → T .rightHybrid = {{a}} → T .rightTaxon = {{b}} → T .rootTaxon = {{d}} →
      stepKernel 𝐍 θ 0 inj .left (stepKernel 𝐍 θ 0 inj .right Φ₀) T =
        Real.exp (-θ.length .topRight) * cherryMass 𝐍 θ 0 (twoInj ({{c}} ∪ ({b, a} : Finset X).image fun z => ({z} : Finset X)) {{d}}) r +
          (1 - Real.exp (-θ.length .topRight)) * cherryMass 𝐍 θ 0 (twoInj ({{c}} ∪ insert ({b, a} : Finset X) (({b, a} : Finset X).image fun z => ({z} : Finset X))) {{d}}) r := by
    intro T h₁ h₂ h₃ h₄ h₅
    rw [step_one (a := a) (b := b) (c := c) (d := d) (v := .left) (e := Edge.topLeft) rfl (fun f => hu_left) hγl (x := c) _ T (by rw [arriving_left, h₁, h₂, union_empty])]
    exact hR₂ _ _ (by rw [owL₂, h₃]) (by rw [owL₃, h₄]) (owL₁ _ _) (by rw [owL₄, h₅])
  -- the hybrid node
  have hlh : (Edge.leftHybrid : Edge) ∈ arcsInto 𝐍 Vertex.hybrid := mem_arcsInto.2 rfl
  have hrh : (Edge.rightHybrid : Edge) ∈ arcsInto 𝐍 Vertex.hybrid := mem_arcsInto.2 rfl
  have hne : (Edge.leftHybrid : Edge) ≠ .rightHybrid := by decide
  have owH₁ : ∀ τ t : Edge → Finset (Finset X), ow (arcsInto 𝐍 Vertex.hybrid) τ t .leftTaxon = τ .leftTaxon := fun τ t => ow_of_notMem (hnr (by simp)) τ t
  have owH₂ : ∀ τ t : Edge → Finset (Finset X), ow (arcsInto 𝐍 Vertex.hybrid) τ t .rightTaxon = τ .rightTaxon := fun τ t => ow_of_notMem (hnr (by simp)) τ t
  have owH₃ : ∀ τ t : Edge → Finset (Finset X), ow (arcsInto 𝐍 Vertex.hybrid) τ t .rootTaxon = τ .rootTaxon := fun τ t => ow_of_notMem (hnr (by simp)) τ t
  rw [step_hybrid _ top hta,
    hL₁ _ (by rw [ow_of_mem hlh, pairFn_left]) (by rw [owH₁, htc]) (by rw [ow_of_mem hrh, pairFn_right hne]) (by rw [owH₂, htb]) (by rw [owH₃, htd]),
    hL₂ _ (by rw [ow_of_mem hlh, pairFn_left]) (by rw [owH₁, htc]) (by rw [ow_of_mem hrh, pairFn_right hne]) (by rw [owH₂, htb]) (by rw [owH₃, htd])]
  -- the values at `top`
  have hset₁ : ∀ w, w = d ∨ w = c ∨ w = a ∨ w = b := fun w => by
    rcases hall w with rfl | rfl | rfl | rfl <;> simp
  have hset₂ : ∀ w, w = d ∨ w = c ∨ w = b ∨ w = a := fun w => by
    rcases hall w with rfl | rfl | rfl | rfl <;> simp
  have hd₁ : d ∉ ({c, a, b} : Finset X) := by simp [hcd.symm, had.symm, hbd.symm]
  have hd₂ : d ∉ ({c, b, a} : Finset X) := by simp [hcd.symm, had.symm, hbd.symm]
  have hsub₁ : ({c, a} : Finset X) ⊆ {c, a, b} := subset_pair_three
  have hsub₂ : ({b, a} : Finset X) ⊆ {c, b, a} := subset_insert _ _
  rw [union_e₁, union_e₂, union_e₃, union_e₄, cherryMass_three h hcard hθ hset₁ hd₁, cherryMass_three h hcard hθ hset₂ hd₂,
    cherryMass_cherry h hcard hθ hsub₁ (card_pair hac.symm) hd₁, cherryMass_cherry h hcard hθ hsub₂ (card_pair hab.symm) hd₂, pair_comm c a, pair_comm b a]

end CF

/-! ### The degrees, the cut edges and the blob -/

section Structure

variable [Fintype X] [DecidableEq X] (h : ({a, b, c, d} : Finset X).card = 4) (hcard : Fintype.card X = 4)

omit [Fintype X] [DecidableEq X] in
theorem indegree_eq {v : Vertex X} (S : Finset Edge) (hS : ∀ e, (network a b c d).graph.target e = v ↔ e ∈ S) : (network a b c d).graph.indegree v = S.card := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_coe_finset S]
  congr 1
  ext e
  exact hS e

omit [Fintype X] [DecidableEq X] in
theorem outdegree_eq {v : Vertex X} (S : Finset Edge) (hS : ∀ e, (network a b c d).graph.source e = v ↔ e ∈ S) : (network a b c d).graph.outdegree v = S.card := by
  unfold DirectedMultigraph.outdegree
  rw [← Set.ncard_coe_finset S]
  congr 1
  ext e
  exact hS e

include h hcard in
/-- It is binary. -/
theorem isBinaryNetwork_network : IsBinaryNetwork (network a b c d) := by
  refine isBinaryNetwork_iff.mpr ⟨isPhylogenetic_network h hcard, ?_, fun v hv h0 => ?_⟩
  · rw [outdegree_eq {.rootTaxon, .rootTop} (fun e => by cases e <;> simp [network])]
    rfl
  · cases v with
    | root => exact absurd rfl hv
    | top =>
      rw [indegree_eq {.rootTop} (fun e => by cases e <;> simp), outdegree_eq {.topLeft, .topRight} (fun e => by cases e <;> simp)]
      rfl
    | left =>
      rw [indegree_eq {.topLeft} (fun e => by cases e <;> simp), outdegree_eq {.leftTaxon, .leftHybrid} (fun e => by cases e <;> simp)]
      rfl
    | right =>
      rw [indegree_eq {.topRight} (fun e => by cases e <;> simp), outdegree_eq {.rightTaxon, .rightHybrid} (fun e => by cases e <;> simp)]
      rfl
    | hybrid =>
      rw [indegree_eq {.leftHybrid, .rightHybrid} (fun e => by cases e <;> simp), outdegree_eq {.hybridTaxon} (fun e => by cases e <;> simp)]
      rfl
    | taxon x =>
      exact absurd (outdegree_eq ∅ (fun e => by cases e <;> simp)) h0

/-- The edges of the 4-cycle. -/
def cycleEdges : Finset Edge := {.topLeft, .topRight, .leftHybrid, .rightHybrid}

omit [Fintype X] in
include h in
/-- **It is level-1, with a 4-cycle**: the edges that are not cut edges are those of the cycle. -/
theorem isBridge_network_iff (e : Edge) : (network a b c d).graph.underlying.IsBridge e ↔ e ∉ cycleEdges := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hstep : ∀ {f g : Edge}, f ≠ g → (network a b c d).graph.Walks {g}ᶜ ((network a b c d).graph.source f) ((network a b c d).graph.target f) := fun hfg =>
    Relation.ReflTransGen.single ⟨_, hfg, Or.inl ⟨rfl, rfl⟩⟩
  have hsym := fun {u v : Vertex X} {F : Set Edge} (hw : (network a b c d).graph.Walks F u v) => (network a b c d).graph.walks_symm hw
  constructor
  · intro hb hm
    rw [(network a b c d).graph.isBridge_iff_not_walks_delete] at hb
    refine hb ?_
    simp only [cycleEdges, mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact (hstep (f := .topRight) (by decide)).trans ((hstep (f := .rightHybrid) (by decide)).trans (hsym (hstep (f := .leftHybrid) (by decide))))
    · exact (hstep (f := .topLeft) (by decide)).trans ((hstep (f := .leftHybrid) (by decide)).trans (hsym (hstep (f := .rightHybrid) (by decide))))
    · exact (hsym (hstep (f := .topLeft) (by decide))).trans ((hstep (f := .topRight) (by decide)).trans (hstep (f := .rightHybrid) (by decide)))
    · exact (hsym (hstep (f := .topRight) (by decide))).trans ((hstep (f := .topLeft) (by decide)).trans (hstep (f := .leftHybrid) (by decide)))
  · intro hm
    rw [(network a b c d).graph.isBridge_iff]
    cases e with
    | rootTaxon =>
      refine ⟨{.taxon d}, fun f => ?_⟩
      cases f <;> simp [DirectedMultigraph.Crosses, network, hcd, hbd, had]
    | rootTop =>
      refine ⟨{.root, .taxon d}, fun f => ?_⟩
      cases f <;> simp [DirectedMultigraph.Crosses, network, hcd, hbd, had]
    | leftTaxon =>
      refine ⟨{.taxon c}, fun f => ?_⟩
      cases f <;> simp [DirectedMultigraph.Crosses, network, hcd.symm, hbc, hac]
    | rightTaxon =>
      refine ⟨{.taxon b}, fun f => ?_⟩
      cases f <;> simp [DirectedMultigraph.Crosses, network, hbd.symm, hbc.symm, hab]
    | hybridTaxon =>
      refine ⟨{.taxon a}, fun f => ?_⟩
      cases f <;> simp [DirectedMultigraph.Crosses, network, had.symm, hac.symm, hab.symm]
    | topLeft => exact absurd (by simp [cycleEdges]) hm
    | topRight => exact absurd (by simp [cycleEdges]) hm
    | leftHybrid => exact absurd (by simp [cycleEdges]) hm
    | rightHybrid => exact absurd (by simp [cycleEdges]) hm

end Structure

/-! ### The parameters -/

section Params

variable [Fintype X] [DecidableEq X] (h : ({a, b, c, d} : Finset X).card = 4) (hcard : Fintype.card X = 4)

/-- The parameters: `γ` on the hybrid edge from `left`, lengths `x`, `x'` of the edges from `top`, and `w` of the pendant edge from the root. The other lengths don't count. -/
def metric (γ x x' w : ℝ) : MetricData Edge where
  length := fun
    | .topLeft => x
    | .topRight => x'
    | .rootTaxon => w
    | _ => 1
  inheritance := fun
    | .leftHybrid => γ
    | .rightHybrid => 1 - γ
    | _ => 1

include h hcard in
theorem isMetric_metric {γ x x' w : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) (hx : 0 < x) (hx' : 0 < x') (hw : 0 < w) : (network a b c d).IsMetric (metric γ x x' w) := by
  have hP := isPhylogenetic_network h hcard
  have hinl : (network a b c d).graph.indegree .hybrid = 2 := by
    rw [indegree_eq {.leftHybrid, .rightHybrid} (fun e => by cases e <;> simp)]
    rfl
  have hlen : ∀ e, 0 < (metric γ x x' w).length e := fun e => by
    cases e <;> first | exact hx | exact hx' | exact hw | exact one_pos
  refine ⟨fun e _ => hlen e, fun e _ => (hlen e).le, fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩
  · cases e
    case leftHybrid => exact absurd he (by change (network a b c d).graph.indegree .hybrid ≠ 1; omega)
    case rightHybrid => exact absurd he (by change (network a b c d).graph.indegree .hybrid ≠ 1; omega)
    all_goals rfl
  · cases e
    case leftHybrid => exact hγ
    case rightHybrid => exact sub_pos.2 hγ₁
    all_goals exact one_pos
  · have hv' : v = .hybrid := by
      cases v with
      | hybrid => rfl
      | root =>
        have h0 : (network a b c d).graph.indegree Vertex.root = 0 := hP.root_indegree
        omega
      | top => rw [indegree_eq {.rootTop} (fun e => by cases e <;> simp)] at hv; simp at hv
      | left => rw [indegree_eq {.topLeft} (fun e => by cases e <;> simp)] at hv; simp at hv
      | right => rw [indegree_eq {.topRight} (fun e => by cases e <;> simp)] at hv; simp at hv
      | taxon t =>
        have := hP.leaf_indegree t
        change (network a b c d).graph.indegree (.taxon t) = 1 at this
        omega
    subst hv'
    have hs := sum_ite_target_pair (N := network a b c d) (v := Vertex.hybrid) (metric γ x x' w).inheritance (k₁ := Edge.leftHybrid) (k₂ := Edge.rightHybrid) rfl rfl (by decide) (fun f => hu_hybrid)
    have hone : (metric γ x x' w).inheritance Edge.leftHybrid + (metric γ x x' w).inheritance Edge.rightHybrid = 1 := by
      change γ + (1 - γ) = 1
      ring
    rw [← hone, ← hs]

include h hcard in
/-- **The parameters giving a point**: a mixing parameter in `(A, 1 - B)`, and the lengths of the edges from `top` that follow from it. -/
theorem exists_params {A B s : ℝ} (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) (hsum : A + B + 3 * s = 1) :
    ∃ θ, (network a b c d).IsMetric θ ∧ ∀ r : QuartetTree X,
      nmscCF (network a b c d) θ 0 r = s + (if ({a, c} : Finset X) ∈ r.val then A else 0) + (if ({a, b} : Finset X) ∈ r.val then B else 0) := by
  set γ : ℝ := (1 + A - B) / 2 with hγ
  have hAγ : A < γ := by rw [hγ]; linarith
  have hBγ : B < 1 - γ := by rw [hγ]; linarith
  have hγ₀ : 0 < γ := hA.trans hAγ
  have hγ₁ : 0 < 1 - γ := hB.trans hBγ
  have hu : 0 < 1 - A / γ := sub_pos.2 ((div_lt_one hγ₀).2 hAγ)
  have hu₁ : 1 - A / γ < 1 := sub_lt_self _ (div_pos hA hγ₀)
  have hv : 0 < 1 - B / (1 - γ) := sub_pos.2 ((div_lt_one hγ₁).2 hBγ)
  have hv₁ : 1 - B / (1 - γ) < 1 := sub_lt_self _ (div_pos hB hγ₁)
  have hx : 0 < -Real.log (1 - A / γ) := neg_pos.2 (Real.log_neg hu hu₁)
  have hx' : 0 < -Real.log (1 - B / (1 - γ)) := neg_pos.2 (Real.log_neg hv hv₁)
  have hθ := isMetric_metric (a := a) (b := b) (c := c) (d := d) h hcard hγ₀ (sub_pos.1 hγ₁) hx hx' one_pos
  refine ⟨_, hθ, fun r => ?_⟩
  rw [nmscCF_network h hcard hθ r]
  change γ * (Real.exp (- -Real.log (1 - A / γ)) * (1 / 3) + (1 - Real.exp (- -Real.log (1 - A / γ))) * _) + (1 - γ) * (Real.exp (- -Real.log (1 - B / (1 - γ))) * (1 / 3) + (1 - Real.exp (- -Real.log (1 - B / (1 - γ)))) * _) = _
  rw [neg_neg, neg_neg, Real.exp_log hu, Real.exp_log hv]
  have h₁ : γ * (1 - A / γ) = γ - A := by field_simp
  have h₂ : (1 - γ) * (1 - B / (1 - γ)) = 1 - γ - B := by field_simp
  have e₁ : ∀ δ : ℝ, (if ({a, c} : Finset X) ∈ r.val then A else 0) = A * (if ({a, c} : Finset X) ∈ r.val then 1 else 0) := fun _ => by
    split_ifs <;> simp
  have e₂ : (if ({a, b} : Finset X) ∈ r.val then B else 0) = B * (if ({a, b} : Finset X) ∈ r.val then 1 else 0) := by
    split_ifs <;> simp
  rw [e₁ 0, e₂]
  generalize (if ({a, c} : Finset X) ∈ r.val then (1 : ℝ) else 0) = δ₁
  generalize (if ({a, b} : Finset X) ∈ r.val then (1 : ℝ) else 0) = δ₂
  linear_combination (1 / 3 - δ₁) * h₁ + (1 / 3 - δ₂) * h₂ - (1 / 3) * hsum

end Params

/-! ### The theorem -/

section Main

variable [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- A pair is not among two others, when one of its elements is not in each. -/
theorem pair_notMem {x y u v s t : X} (h₁ : x ∉ ({u, v} : Finset X) ∨ y ∉ ({u, v} : Finset X)) (h₂ : x ∉ ({s, t} : Finset X) ∨ y ∉ ({s, t} : Finset X)) :
    ({x, y} : Finset X) ∉ ({{u, v}, {s, t}} : Finset (Finset X)) := by
  have hx : x ∈ ({x, y} : Finset X) := by simp
  have hy : y ∈ ({x, y} : Finset X) := by simp
  simp only [mem_insert, mem_singleton, not_or]
  constructor
  · intro he
    rw [he] at hx hy
    exact h₁.elim (· hx) (· hy)
  · intro he
    rw [he] at hx hy
    exact h₂.elim (· hx) (· hy)

/-- **"By Baños (2019), all points off the line segments arise from level-1 networks with 4-cycles"** (`a:claim:cf-banos`, after Proposition 1): every non-cut point of the simplex is the `CF` of `network` for a labelling of its taxa. By `hasStarTopology_of_isNonCutCF` its reduced
tree of blobs is unresolved, and by `isBridge_network_iff` it is a network with one 4-cycle. -/
theorem exists_cfTriple_eq (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hsum : p + q + r = 1)
    (hnc : IsNonCutCF (p, q, r)) :
    ∃ (a' b' c' d' : X) (_ : ({a', b', c', d'} : Finset X).card = 4) (θ : MetricData Edge), (network a' b' c' d').IsMetric θ ∧ cfTriple (network a' b' c' d') θ a b c d h = (p, q, r) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hpq : p ≠ q := fun he => hnc (Or.inl he)
  have hpr : p ≠ r := fun he => hnc (Or.inr (Or.inl he))
  have hqr : q ≠ r := fun he => hnc (Or.inr (Or.inr he))
  have mem₁ : ({a, b} : Finset X) ∈ (quartetTree a b c d h).val := by simp [quartetTree_val]
  have mem₂ : ({a, c} : Finset X) ∈ (quartetTree a c b d (card_acbd h)).val := by simp [quartetTree_val]
  have mem₃ : ({a, d} : Finset X) ∈ (quartetTree a d b c (card_adbc h)).val := by simp [quartetTree_val]
  have nac₁ : ({a, c} : Finset X) ∉ (quartetTree a b c d h).val := by
    rw [quartetTree_val]
    exact pair_notMem (Or.inr (by simp [hac.symm, hbc.symm])) (Or.inl (by simp [hac, had]))
  have nad₁ : ({a, d} : Finset X) ∉ (quartetTree a b c d h).val := by
    rw [quartetTree_val]
    exact pair_notMem (Or.inr (by simp [had.symm, hbd.symm])) (Or.inl (by simp [hac, had]))
  have nab₂ : ({a, b} : Finset X) ∉ (quartetTree a c b d (card_acbd h)).val := by
    rw [quartetTree_val]
    exact pair_notMem (Or.inr (by simp [hab.symm, hbc])) (Or.inl (by simp [hab, had]))
  have nad₂ : ({a, d} : Finset X) ∉ (quartetTree a c b d (card_acbd h)).val := by
    rw [quartetTree_val]
    exact pair_notMem (Or.inr (by simp [had.symm, hcd.symm])) (Or.inl (by simp [hab, had]))
  have nab₃ : ({a, b} : Finset X) ∉ (quartetTree a d b c (card_adbc h)).val := by
    rw [quartetTree_val]
    exact pair_notMem (Or.inr (by simp [hab.symm, hbd])) (Or.inl (by simp [hab, hac]))
  have nac₃ : ({a, c} : Finset X) ∉ (quartetTree a d b c (card_adbc h)).val := by
    rw [quartetTree_val]
    exact pair_notMem (Or.inr (by simp [hac.symm, hcd])) (Or.inl (by simp [hab, hac]))
  by_cases h₁ : r < p ∧ r < q
  · -- `ad|bc` has the smallest entry
    obtain ⟨θ, hθ, hF⟩ := exists_params (a := a) (b := b) (c := c) (d := d) h hcard (A := q - r) (B := p - r) (s := r) (sub_pos.2 h₁.2) (sub_pos.2 h₁.1) hr (by linarith)
    refine ⟨a, b, c, d, h, θ, hθ, ?_⟩
    unfold cfTriple quartetCF
    rw [hF, hF, hF]
    simp only [mem₁, mem₂, nac₁, nab₂, nab₃, nac₃, ↓reduceIte, Prod.mk.injEq]
    exact ⟨by ring, by ring, by ring⟩
  by_cases h₂ : q < p ∧ q < r
  · -- `ac|bd` has the smallest entry
    have hc' := card_acbd (card_adbc h)
    obtain ⟨θ, hθ, hF⟩ := exists_params (a := a) (b := b) (c := d) (d := c) hc' hcard (A := r - q) (B := p - q) (s := q) (sub_pos.2 h₂.2) (sub_pos.2 h₂.1) hq (by linarith)
    refine ⟨a, b, d, c, hc', θ, hθ, ?_⟩
    unfold cfTriple quartetCF
    rw [hF, hF, hF]
    simp only [mem₁, mem₃, nad₁, nad₂, nab₂, nab₃, ↓reduceIte, Prod.mk.injEq]
    exact ⟨by ring, by ring, by ring⟩
  · -- `ab|cd` has the smallest entry
    have hlt : p < q := by
      by_contra hc
      have hq' : q < p := lt_of_le_of_ne (not_lt.1 hc) hpq.symm
      by_cases hqr' : q < r
      · exact h₂ ⟨hq', hqr'⟩
      · have hr' : r < q := lt_of_le_of_ne (not_lt.1 hqr') hqr.symm
        exact h₁ ⟨hr'.trans hq', hr'⟩
    have hlt' : p < r := by
      by_contra hc
      have hr' : r < p := lt_of_le_of_ne (not_lt.1 hc) hpr.symm
      exact h₁ ⟨hr', hr'.trans hlt⟩
    have hmin : p < q ∧ p < r := ⟨hlt, hlt'⟩
    have hc' := card_adbc (card_adbc h)
    obtain ⟨θ, hθ, hF⟩ := exists_params (a := a) (b := c) (c := d) (d := b) hc' hcard (A := r - p) (B := q - p) (s := p) (sub_pos.2 hmin.2) (sub_pos.2 hmin.1) hp (by linarith)
    refine ⟨a, c, d, b, hc', θ, hθ, ?_⟩
    unfold cfTriple quartetCF
    rw [hF, hF, hF]
    simp only [mem₂, mem₃, nac₁, nad₁, nad₂, nac₃, ↓reduceIte, Prod.mk.injEq]
    exact ⟨by ring, by ring, by ring⟩

/-- **"A network with a more complicated 4-blob may produce a CF on the line segments for certain numerical parameters"** (`a:claim:cf-banos`, after Proposition 1): already the 4-cycle does, with `γ = 1/2` and equal lengths of the edges from `top`, though
its reduced tree of blobs is unresolved. So `IsNonCutCF` holds only for generic parameters in Theorem 1 (b), and all parameters is false. -/
theorem exists_isCutCF (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    (Trd (isBinaryNetwork_network h hcard) (nontrivial_of_card_four hcard)).HasStarTopology a b c d ∧ ∃ θ, (network a b c d).IsMetric θ ∧ IsCutCF (cfTriple (network a b c d) θ a b c d h) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have mem₁ : ({a, b} : Finset X) ∈ (quartetTree a b c d h).val := by simp [quartetTree_val]
  have mem₂ : ({a, c} : Finset X) ∈ (quartetTree a c b d (card_acbd h)).val := by simp [quartetTree_val]
  have nac₁ : ({a, c} : Finset X) ∉ (quartetTree a b c d h).val := by
    rw [quartetTree_val]
    exact pair_notMem (Or.inr (by simp [hac.symm, hbc.symm])) (Or.inl (by simp [hac, had]))
  have nab₂ : ({a, b} : Finset X) ∉ (quartetTree a c b d (card_acbd h)).val := by
    rw [quartetTree_val]
    exact pair_notMem (Or.inr (by simp [hab.symm, hbc])) (Or.inl (by simp [hab, had]))
  have nab₃ : ({a, b} : Finset X) ∉ (quartetTree a d b c (card_adbc h)).val := by
    rw [quartetTree_val]
    exact pair_notMem (Or.inr (by simp [hab.symm, hbd])) (Or.inl (by simp [hab, hac]))
  have nac₃ : ({a, c} : Finset X) ∉ (quartetTree a d b c (card_adbc h)).val := by
    rw [quartetTree_val]
    exact pair_notMem (Or.inr (by simp [hac.symm, hcd])) (Or.inl (by simp [hab, hac]))
  constructor
  · -- a non-cut point, on this network
    obtain ⟨θ, hθ, hF⟩ := exists_params (a := a) (b := b) (c := c) (d := d) h hcard (A := 1 / 2) (B := 1 / 4) (s := 1 / 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine hasStarTopology_of_isNonCutCF _ hcard h hθ ?_
    unfold IsNonCutCF IsCutCF cfTriple quartetCF
    rw [hF, hF, hF]
    simp only [mem₁, mem₂, nac₁, nab₂, nab₃, nac₃, ↓reduceIte]
    norm_num
  · obtain ⟨θ, hθ, hF⟩ := exists_params (a := a) (b := b) (c := c) (d := d) h hcard (A := 1 / 4) (B := 1 / 4) (s := 1 / 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨θ, hθ, Or.inl ?_⟩
    unfold cfTriple quartetCF
    rw [hF, hF]
    simp only [mem₁, mem₂, nac₁, nab₂, ↓reduceIte]
    norm_num

/-- **A pendant edge between trivial blobs whose length is not identifiable**, against the literal reading of "for edges between trivial blobs, it is straightforward to see that edge lengths are identifiable" (`a:claim:trivial-edges`, Section 5): the edge from the root to `d` joins two trivial blobs, and no `CF` depends on its
length. So that sentence is about internal edges (`TrivialEdges.semidirected_length_eq`). -/
theorem pendant_not_identifiable (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) {w w' : ℝ} (hw : 0 < w) (hw' : 0 < w') (r : QuartetTree X) :
    nmscCF (network a b c d) (metric (1 / 2) 1 1 w) 0 r = nmscCF (network a b c d) (metric (1 / 2) 1 1 w') 0 r := by
  rw [nmscCF_network h hcard (isMetric_metric h hcard (by norm_num) (by norm_num) one_pos one_pos hw) r, nmscCF_network h hcard (isMetric_metric h hcard (by norm_num) (by norm_num) one_pos one_pos hw') r]
  rfl

/-- The edge from the root to `d` in `pendant_not_identifiable` joins two trivial blobs: the root has only cut edges, and the taxon has one. -/
theorem isTrivialBlob_root_taxon (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    IsTrivialBlob (network a b c d).graph (blobOf (network a b c d).graph .root) ∧ IsTrivialBlob (network a b c d).graph (blobOf (network a b c d).graph (.taxon d)) := by
  have hP := isPhylogenetic_network h hcard
  have hbr : ∀ e, e ∉ cycleEdges → (network a b c d).graph.underlying.IsBridge e := fun e he => (isBridge_network_iff h e).mpr he
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  constructor
  · refine ⟨.root, Set.eq_singleton_iff_unique_mem.mpr ⟨rfl, fun w hw => ?_⟩⟩
    have hw' : (network a b c d).graph.Walks {e | ¬ (network a b c d).graph.underlying.IsBridge e} .root w := (network a b c d).graph.blobSetoid.symm (Quotient.exact hw)
    have key : ∀ z, (network a b c d).graph.Walks {e | ¬ (network a b c d).graph.underlying.IsBridge e} .root z → z = Vertex.root := by
      intro z hz
      induction hz with
      | refl => rfl
      | tail _ hstep ih =>
        subst ih
        obtain ⟨g, hg, (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)⟩ := hstep
        · by_cases hgc : g ∈ cycleEdges
          · simp only [cycleEdges, mem_insert, mem_singleton] at hgc
            rcases hgc with rfl | rfl | rfl | rfl <;> exact absurd h₁ (by simp)
          · exact absurd (hbr g hgc) hg
        · cases g <;> exact absurd h₂ (by simp)
    exact key w hw'
  · refine ⟨.taxon d, Set.eq_singleton_iff_unique_mem.mpr ⟨rfl, fun w hw => ?_⟩⟩
    have hw' : (network a b c d).graph.Walks {e | ¬ (network a b c d).graph.underlying.IsBridge e} (.taxon d) w := (network a b c d).graph.blobSetoid.symm (Quotient.exact hw)
    have key : ∀ z, (network a b c d).graph.Walks {e | ¬ (network a b c d).graph.underlying.IsBridge e} (.taxon d) z → z = Vertex.taxon d := by
      intro z hz
      induction hz with
      | refl => rfl
      | tail _ hstep ih =>
        subst ih
        obtain ⟨g, hg, (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)⟩ := hstep
        · cases g <;> exact absurd h₁ (by simp)
        · by_cases hgc : g ∈ cycleEdges
          · simp only [cycleEdges, mem_insert, mem_singleton] at hgc
            rcases hgc with rfl | rfl | rfl | rfl <;> exact absurd h₂ (by simp)
          · exact absurd (hbr g hgc) hg
    exact key w hw'

end Main

end AllmanEtAl2023.FourCycle
