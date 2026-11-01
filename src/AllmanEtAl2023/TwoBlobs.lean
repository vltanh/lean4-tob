module

public import AllmanEtAl2023.Lemma1
public import AllmanEtAl2023.InPassing

/-!
# Allman, Baños, Mitchell, Rhodes 2023: any number of 2-blobs

"In either case, `𝒩⁻` may have any number of 2-blobs" (Lemma 1; `a:claim:two-blobs-any`). `exists_network_star` and `exists_network_resolved` say that every number arises, in each of the two cases of Lemma 1. The paper doesn't prove this.

The proof counts. `T(𝒩⁻)` is a tree, whose edges are the cut edges of `𝒩⁻`, and whose nodes of degree other than 2 are the four taxa, and one node of degree 4, or two of degree 3 (`trd_cases`). So the number of 2-blobs is the number
of cut edges of `𝒩⁻`, less 4 or 5 (`ncard_cutDegree_two_of_isBlobQuartet`, `ncard_cutDegree_two_of_isTreeQuartet`). An edge of `𝒩⁻` is a cut edge exactly when it is one of `𝒩⁺`, if the LSA is the root (`isBridge_unrootAt_iff`,
`isBridge_lsaPlus_iff`). Inserting a 2-cycle above a taxon (`insertCycle`) adds one cut edge and changes nothing else that matters. The two families start at a tree and at a 4-cycle.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph
open scoped Classical

namespace AllmanEtAl2023.InPassing

variable {V E X : Type*}

/-! ### Cut edges, from `𝒩⁺` to `𝒩⁻` -/

section Unroot

variable {M : RootedNetwork V E X}

/-- **An edge of the network with the root suppressed is a cut edge exactly when it is one of the network.** -/
theorem isBridge_unrootAt_iff (hM : M.IsPhylogenetic) {e₀ : E} (he₀ : M.graph.source e₀ = M.root) (hout : M.graph.outdegree M.root = 2) (f : {e // e ≠ e₀}) :
    (unrootAt M hM e₀).graph.underlying.IsBridge f ↔ M.graph.underlying.IsBridge f.1 := by
  have hsrc₁ : ∀ f : {e // e ≠ e₀}, M.graph.source f.1 = M.root →
      ((unrootAt M hM e₀).graph.source f).1 = M.graph.target e₀ := fun f hf => by
    simp only [unrootAt, dite_eq_left hf]
  have hsrc₂ : ∀ f : {e // e ≠ e₀}, M.graph.source f.1 ≠ M.root →
      ((unrootAt M hM e₀).graph.source f).1 = M.graph.source f.1 := fun f hf => by
    simp only [unrootAt, dite_eq_right hf]
  have htgt : ∀ f : {e // e ≠ e₀}, ((unrootAt M hM e₀).graph.target f).1 = M.graph.target f.1 := fun _ => rfl
  rw [DirectedMultigraph.isBridge_iff, DirectedMultigraph.isBridge_iff]
  constructor
  · rintro ⟨T', hT'⟩
    -- the root goes with the child of `e₀`
    let T : Set V := {v | if h : v = M.root then
      (⟨M.graph.target e₀, target_ne_root hM e₀⟩ : {v // v ≠ M.root}) ∈ T' else (⟨v, h⟩ : {v // v ≠ M.root}) ∈ T'}
    have hmem : ∀ v (hv : v ≠ M.root), v ∈ T ↔ (⟨v, hv⟩ : {v // v ≠ M.root}) ∈ T' := fun v hv => by
      simp only [T, Set.mem_ofPred_eq, dite_eq_right hv]
    have hroot : M.root ∈ T ↔ (⟨M.graph.target e₀, target_ne_root hM e₀⟩ : {v // v ≠ M.root}) ∈ T' := by
      change (if h : M.root = M.root then _ else _) ↔ _
      rw [dite_eq_left rfl]
    have hsrc : ∀ g : {e // e ≠ e₀}, M.graph.source g.1 ∈ T ↔ (unrootAt M hM e₀).graph.source g ∈ T' := by
      intro g
      by_cases hg : M.graph.source g.1 = M.root
      · rw [hg, hroot]
        have : (unrootAt M hM e₀).graph.source g = (⟨M.graph.target e₀, target_ne_root hM e₀⟩ : {v // v ≠ M.root}) := Subtype.ext (hsrc₁ g hg)
        rw [this]
      · rw [hmem _ hg]
        have : (unrootAt M hM e₀).graph.source g = (⟨M.graph.source g.1, hg⟩ : {v // v ≠ M.root}) := Subtype.ext (hsrc₂ g hg)
        rw [this]
    have htg : ∀ g : {e // e ≠ e₀}, M.graph.target g.1 ∈ T ↔ (unrootAt M hM e₀).graph.target g ∈ T' := fun g =>
      hmem _ (target_ne_root hM g.1)
    refine ⟨T, fun g => ?_⟩
    by_cases hg : g = e₀
    · subst hg
      have hne : g ≠ f.1 := fun h => f.2 h.symm
      have hs : M.graph.source g ∈ T ↔ M.graph.target g ∈ T := by
        rw [he₀, hroot, hmem _ (target_ne_root hM g)]
      simp only [DirectedMultigraph.Crosses, hne, iff_false]
      tauto
    · have hc := hT' ⟨g, hg⟩
      simp only [DirectedMultigraph.Crosses] at hc ⊢
      have h₁ := hsrc ⟨g, hg⟩
      have h₂ := htg ⟨g, hg⟩
      rw [show (M.graph.source g ∈ T) = _ from propext h₁, show (M.graph.target g ∈ T) = _ from propext h₂]
      exact hc.trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · rintro ⟨T, hT⟩
    obtain ⟨e₁, hne₁, hroot⟩ := exists_other_root_arc hout he₀
    have hcr : ∀ g : {e // e ≠ e₀}, M.graph.source g.1 ≠ M.root →
        ((unrootAt M hM e₀).graph.Crosses g (Subtype.val ⁻¹' T) ↔ M.graph.Crosses g.1 T) := by
      intro g hg
      simp only [DirectedMultigraph.Crosses, Set.mem_preimage, hsrc₂ g hg, htgt]
    have hcr₁ : (unrootAt M hM e₀).graph.Crosses ⟨e₁, hne₁⟩ (Subtype.val ⁻¹' T) ↔
        (M.graph.target e₀ ∈ T ∧ M.graph.target e₁ ∉ T) ∨ (M.graph.target e₁ ∈ T ∧ M.graph.target e₀ ∉ T) := by
      have he₁ : M.graph.source e₁ = M.root := (hroot e₁).mpr (Or.inr rfl)
      simp only [DirectedMultigraph.Crosses, Set.mem_preimage, hsrc₁ ⟨e₁, hne₁⟩ he₁, htgt]
    have hc₀ := hT e₀
    have hc₁ := hT e₁
    have hs₁ : M.graph.source e₁ = M.root := (hroot e₁).mpr (Or.inr rfl)
    simp only [DirectedMultigraph.Crosses] at hc₀ hc₁
    rw [he₀] at hc₀
    rw [hs₁] at hc₁
    have hfe₀ : e₀ ≠ f.1 := fun h => f.2 h.symm
    refine ⟨Subtype.val ⁻¹' T, fun g => ?_⟩
    by_cases hg : M.graph.source g.1 = M.root
    · have hge : g = ⟨e₁, hne₁⟩ := Subtype.ext (((hroot g.1).mp hg).resolve_left g.2)
      subst hge
      rw [hcr₁]
      by_cases hfe : f.1 = e₁
      · have h₁ := hc₁.mpr hfe.symm
        have h₂ : ¬ _ := fun h => hfe₀ (hc₀.mp h)
        have hfg : (⟨e₁, hne₁⟩ : {e // e ≠ e₀}) = f := Subtype.ext hfe.symm
        simp only [hfg, iff_true]
        tauto
      · have hfg : (⟨e₁, hne₁⟩ : {e // e ≠ e₀}) ≠ f := fun h => hfe (congrArg Subtype.val h).symm
        have h₁ : ¬ _ := fun h => hfe₀ (hc₀.mp h)
        have h₂ : ¬ _ := fun h => hfe (hc₁.mp h).symm
        simp only [hfg, iff_false]
        tauto
    · exact (hcr g hg).trans ((hT g.1).trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)

end Unroot

section LSA

variable {N : RootedNetwork V E X}

/-- The LSA is the root. -/
def HasRootLSA (N : RootedNetwork V E X) : Prop := ∀ w, N.IsStableAncestor Set.univ w → w = N.root

theorem lsaNode_eq_root (hN : IsBinaryNetwork N) (hX : Nontrivial X) (hL : HasRootLSA N) : lsaNode hN hX = N.root :=
  hL _ (lsa_spec hN.isPhylogenetic Set.univ Set.univ_nonempty).1

theorem mem_belowVertices_of_root (hN : IsBinaryNetwork N) (hX : Nontrivial X) (hL : HasRootLSA N) (v : V) : v ∈ N.belowVertices (lsaNode hN hX) Set.univ := by
  rw [lsaNode_eq_root hN hX hL]
  exact ⟨hN.isPhylogenetic.root_reaches v, mem_ancestralVertices_univ hN v⟩

theorem mem_belowArcs_of_root (hN : IsBinaryNetwork N) (hX : Nontrivial X) (hL : HasRootLSA N) (e : E) : e ∈ N.belowArcs (lsaNode hN hX) Set.univ := by
  rw [lsaNode_eq_root hN hX hL]
  exact ⟨hN.isPhylogenetic.root_reaches _, mem_ancestralVertices_univ hN _⟩

/-- **If the LSA is the root, an edge of the LSA network is a cut edge exactly when it is one of the network.** -/
theorem isBridge_lsaPlus_iff (hN : IsBinaryNetwork N) (hX : Nontrivial X) (hL : HasRootLSA N) (f : N.belowArcs (lsaNode hN hX) Set.univ) :
    (lsaPlus hN hX).graph.underlying.IsBridge f ↔ N.graph.underlying.IsBridge f.1 := by
  rw [DirectedMultigraph.isBridge_iff, DirectedMultigraph.isBridge_iff]
  constructor
  · rintro ⟨S', hS'⟩
    have hval : ∀ x (hx : x ∈ N.belowVertices (lsaNode hN hX) Set.univ), x ∈ Subtype.val '' S' ↔ (⟨x, hx⟩ : N.belowVertices (lsaNode hN hX) Set.univ) ∈ S' := fun x hx => by
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · exact fun hm => ⟨_, hm, rfl⟩
    refine ⟨Subtype.val '' S', fun g => ?_⟩
    have hc := hS' ⟨g, mem_belowArcs_of_root hN hX hL g⟩
    simp only [DirectedMultigraph.Crosses, hval _ (mem_belowVertices_of_root hN hX hL _)]
    exact hc.trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · rintro ⟨S, hS⟩
    refine ⟨Subtype.val ⁻¹' S, fun g => ?_⟩
    exact (hS g.1).trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- **The cut edges of `𝒩⁻`**, when the LSA is the root: those of `𝒩⁺`, other than the edge of the root merged into the other. -/
theorem card_bridgeArc_semidirected (hN : IsBinaryNetwork N) (hX : Nontrivial X) (hL : HasRootLSA N) :
    Nat.card (semidirected hN hX).graph.BridgeArc = ({e | N.graph.underlying.IsBridge e} \ {(rootTreeArc hN hX).1}).ncard := by
  rw [← Nat.card_coe_set_eq]
  have hbr := fun f : SemiE hN hX => (isBridge_unrootAt_iff (lsaPlus_isPhylogenetic hN hX) (rootTreeArc_spec hN hX).1 (lsaPlus_outdegree_root hN hX) f).trans
    (isBridge_lsaPlus_iff hN hX hL f.1)
  refine Nat.card_congr ⟨fun f => ⟨f.1.1.1, (hbr f.1).mp f.2, fun h => f.1.2 (Subtype.ext h)⟩,
    fun f => ⟨⟨⟨f.1, mem_belowArcs_of_root hN hX hL f.1⟩, fun h => f.2.2 (congrArg Subtype.val h)⟩, (hbr _).mpr f.2.1⟩, fun _ => rfl, fun _ => rfl⟩

end LSA

/-! ### The count of 2-blobs -/

section Count

variable [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

omit [DecidableEq X] in
/-- The blobs of degree 2 are those other than the taxa and the blobs given. -/
theorem card_cutDegree_two (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {S : Finset (semidirected hN (nontrivial_of_card_four hcard)).graph.BlobVertex}
    (hS₁ : ∀ z ∈ S, ∀ x, blobOf (semidirected hN (nontrivial_of_card_four hcard)).graph ((semidirected hN (nontrivial_of_card_four hcard)).leaf x) ≠ z)
    (hS₂ : ∀ z ∈ S, nodeDegree (semidirected hN (nontrivial_of_card_four hcard)).treeOfBlobs z ≠ 2)
    (hS₃ : ∀ w, (∀ x, blobOf (semidirected hN (nontrivial_of_card_four hcard)).graph ((semidirected hN (nontrivial_of_card_four hcard)).leaf x) ≠ w) → w ∉ S →
      nodeDegree (semidirected hN (nontrivial_of_card_four hcard)).treeOfBlobs w = 2) :
    {b | cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 2}.ncard + 4 + S.card =
      Nat.card (semidirected hN (nontrivial_of_card_four hcard)).graph.BridgeArc + 1 := by
  have hX := nontrivial_of_card_four hcard
  have : Finite V := hN.finite_vertices
  have : Finite E := hN.finite_arcs
  have hTree := treeOfBlobs_semidirected_isTree hN hX
  let _ : Fintype (semidirected hN hX).graph.BlobVertex := Fintype.ofFinite _
  let _ : Fintype (semidirected hN hX).graph.BridgeArc := Fintype.ofFinite _
  obtain ⟨x₀⟩ := hX.to_nonempty
  have : Nonempty (semidirected hN hX).graph.BlobVertex := ⟨blobOf _ ((semidirected hN hX).leaf x₀)⟩
  have hinj : Function.Injective fun x => blobOf (semidirected hN hX).graph ((semidirected hN hX).leaf x) := fun x y hxy =>
    Bridges.Trd_leaf_injective hN hX (Subtype.ext hxy)
  let L : Finset (semidirected hN hX).graph.BlobVertex := Finset.univ.image fun x => blobOf (semidirected hN hX).graph ((semidirected hN hX).leaf x)
  have hLcard : L.card = 4 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard]
  have hdisj : Disjoint L S := by
    refine Finset.disjoint_left.mpr fun z hz hzS => ?_
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
    exact hS₁ _ hzS x rfl
  have hset : {b | cutDegree (semidirected hN hX).graph b = 2} = ((L ∪ S)ᶜ : Finset _) := by
    ext b
    simp only [Set.mem_ofPred_eq, Finset.coe_compl, Finset.coe_union, Set.mem_compl_iff, Set.mem_union, Finset.mem_coe, not_or]
    rw [← nodeDegree_bridgeQuotient]
    constructor
    · intro hb
      refine ⟨fun hL => ?_, fun hSb => hS₂ b hSb hb⟩
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hL
      have := nodeDegree_treeOfBlobs_leaf hN hX x
      change nodeDegree (semidirected hN hX).treeOfBlobs _ = 2 at hb
      omega
    · rintro ⟨h₁, h₂⟩
      exact hS₃ b (fun x hx => h₁ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩)) h₂
  rw [hset, Set.ncard_coe_finset, Finset.card_compl, Finset.card_union_of_disjoint hdisj, hLcard, Nat.card_eq_fintype_card,
    TreeSuppression.card_arcs_add_one hTree]
  have hle := Finset.card_le_univ (L ∪ S)
  rw [Finset.card_union_of_disjoint hdisj, hLcard] at hle
  omega

/-- **The number of 2-blobs of `𝒩⁻`, in the first case of Lemma 1**: the number of cut edges less 4. -/
theorem ncard_cutDegree_two_of_isBlobQuartet (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) (hB : IsBlobQuartet N Finset.univ) :
    {b | cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 2}.ncard + 4 = Nat.card (semidirected hN (nontrivial_of_card_four hcard)).graph.BridgeArc := by
  rcases trd_cases hN hcard with ⟨⟨z, hz, hd, hrest⟩, -⟩ | ⟨-, a, b, c, d, h, hT⟩
  · have := card_cutDegree_two hN hcard (S := {z}) (fun y hy => by rw [Finset.mem_singleton.mp hy]; exact hz)
      (fun y hy => by rw [Finset.mem_singleton.mp hy, hd]; omega) (fun w hw hS => hrest w hw (by simpa using hS))
    simp only [Finset.card_singleton] at this
    omega
  · exact absurd hB (isTreeQuartet_univ_of_hasQuartetTopology hN hcard h hT).2

/-- **The number of 2-blobs of `𝒩⁻`, in the second case of Lemma 1**: the number of cut edges less 5. -/
theorem ncard_cutDegree_two_of_isTreeQuartet (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) (hT : IsTreeQuartet N Finset.univ) :
    {b | cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 2}.ncard + 5 = Nat.card (semidirected hN (nontrivial_of_card_four hcard)).graph.BridgeArc := by
  rcases trd_cases hN hcard with ⟨-, hS⟩ | ⟨⟨z₁, z₂, hne, hz₁, hz₂, hd₁, hd₂, hrest⟩, -⟩
  · obtain ⟨a, b, c, d, h⟩ := exists_names_of_card_four hcard
    have hu : ({a, b, c, d} : Finset X) = Finset.univ := Finset.eq_univ_of_card _ (h.trans hcard.symm)
    exact absurd (hu ▸ isBlobQuartet_univ_of_hasStarTopology hN hcard h (hS a b c d h)) hT.2
  · have := card_cutDegree_two hN hcard (S := {z₁, z₂}) (fun y hy => by
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hz₁
        · rw [Finset.mem_singleton.mp hy]; exact hz₂)
      (fun y hy => by
        rcases Finset.mem_insert.mp hy with rfl | hy
        · rw [hd₁]; omega
        · rw [Finset.mem_singleton.mp hy, hd₂]; omega)
      (fun w hw hS => hrest w hw (fun h' => hS (by simp [h'])) (fun h' => hS (by simp [h'])))
    rw [Finset.card_pair hne] at this
    omega

end Count

/-! ### Inserting a 2-cycle above a taxon -/

/-- The two new nodes: the top of the 2-cycle and the bottom. -/
inductive CycleNode
  | top | bottom

/-- The three new edges: the two edges of the 2-cycle, and the edge from it to the taxon. -/
inductive CycleArc
  | left | right | out

instance : Finite CycleNode :=
  Finite.of_injective (fun t => match t with | CycleNode.top => (0 : Fin 2) | CycleNode.bottom => 1) (by
    intro x y h
    cases x <;> cases y <;> first | rfl | exact absurd h (by decide))

instance : Finite CycleArc :=
  Finite.of_injective (fun t => match t with | CycleArc.left => (0 : Fin 3) | CycleArc.right => 1 | CycleArc.out => 2) (by
    intro x y h
    cases x <;> cases y <;> first | rfl | exact absurd h (by decide))

/-- **A 2-cycle inserted above the taxon `a`**, whose edge is `g₀`. -/
def insertCycle (N : RootedNetwork V E X) (a : X) (g₀ : E) : RootedNetwork (V ⊕ CycleNode) (E ⊕ CycleArc) X where
  graph :=
    { source := fun f => match f with
        | .inl e => .inl (N.graph.source e)
        | .inr .left => .inr .top
        | .inr .right => .inr .top
        | .inr .out => .inr .bottom
      target := fun f => match f with
        | .inl e => if e = g₀ then .inr .top else .inl (N.graph.target e)
        | .inr .left => .inr .bottom
        | .inr .right => .inr .bottom
        | .inr .out => .inl (N.leaf a) }
  root := .inl N.root
  leaf x := .inl (N.leaf x)

section Insert

variable {N : RootedNetwork V E X} {a : X} {g₀ : E}

@[simp] theorem source_inl (e : E) : (insertCycle N a g₀).graph.source (.inl e) = .inl (N.graph.source e) := rfl
@[simp] theorem source_left : (insertCycle N a g₀).graph.source (.inr .left) = .inr .top := rfl
@[simp] theorem source_right : (insertCycle N a g₀).graph.source (.inr .right) = .inr .top := rfl
@[simp] theorem source_out : (insertCycle N a g₀).graph.source (.inr .out) = .inr .bottom := rfl
@[simp] theorem target_left : (insertCycle N a g₀).graph.target (.inr .left) = .inr .bottom := rfl
@[simp] theorem target_right : (insertCycle N a g₀).graph.target (.inr .right) = .inr .bottom := rfl
@[simp] theorem target_out : (insertCycle N a g₀).graph.target (.inr .out) = .inl (N.leaf a) := rfl
theorem target_inl_of_ne {e : E} (he : e ≠ g₀) : (insertCycle N a g₀).graph.target (.inl e) = .inl (N.graph.target e) := ite_eq_right he
theorem target_inl_self : (insertCycle N a g₀).graph.target (.inl g₀) = .inr .top := ite_eq_left rfl

/-- The node of the network that a node goes to, removing the 2-cycle. -/
def collapse (N : RootedNetwork V E X) (a : X) : V ⊕ CycleNode → V
  | .inl v => v
  | .inr _ => N.leaf a

variable (hg₀ : ∀ f, N.graph.target f = N.leaf a ↔ f = g₀)

include hg₀

/-- **A cut edge of the network is a cut edge with the 2-cycle inserted.** -/
theorem crosses_collapse_iff {S : Set V} {e : E} (hS : ∀ f, N.graph.Crosses f S ↔ f = e) (f : E ⊕ CycleArc) :
    (insertCycle N a g₀).graph.Crosses f (collapse N a ⁻¹' S) ↔ f = .inl e := by
  have hg : N.graph.target g₀ = N.leaf a := (hg₀ g₀).mpr rfl
  rcases f with f | f
  · have hc : (insertCycle N a g₀).graph.Crosses (.inl f) (collapse N a ⁻¹' S) ↔ N.graph.Crosses f S := by
      by_cases hf : f = g₀
      · subst hf
        simp only [DirectedMultigraph.Crosses, source_inl, target_inl_self, Set.mem_preimage, collapse, hg]
      · simp only [DirectedMultigraph.Crosses, source_inl, target_inl_of_ne hf, Set.mem_preimage, collapse]
    rw [hc, hS f]
    exact ⟨fun h => congrArg _ h, fun h => Sum.inl_injective h⟩
  · have hnc : ¬ (insertCycle N a g₀).graph.Crosses (.inr f) (collapse N a ⁻¹' S) := by
      cases f <;> simp [DirectedMultigraph.Crosses, collapse]
    simp [hnc]

omit hg₀ in
/-- An edge other than the cut edge has its ends on one side. -/
theorem mem_iff_mem_of_ne {S' : Set (V ⊕ CycleNode)} {e' f' : E ⊕ CycleArc} (hS' : ∀ f, (insertCycle N a g₀).graph.Crosses f S' ↔ f = e') (hne : f' ≠ e') :
    (insertCycle N a g₀).graph.source f' ∈ S' ↔ (insertCycle N a g₀).graph.target f' ∈ S' := by
  have := (hS' f').not.mpr hne
  simp only [DirectedMultigraph.Crosses] at this
  tauto

/-- **A cut edge with the 2-cycle inserted, other than the edge to the taxon, is one of the network.** -/
theorem crosses_of_insertCycle {S' : Set (V ⊕ CycleNode)} {e : E} (hS' : ∀ f, (insertCycle N a g₀).graph.Crosses f S' ↔ f = .inl e) (f : E) :
    N.graph.Crosses f (Sum.inl ⁻¹' S') ↔ f = e := by
  have hg : N.graph.target g₀ = N.leaf a := (hg₀ g₀).mpr rfl
  have hl : Sum.inr CycleNode.top ∈ S' ↔ Sum.inr CycleNode.bottom ∈ S' := mem_iff_mem_of_ne hS' (f' := .inr .left) (by simp)
  have ho : Sum.inr CycleNode.bottom ∈ S' ↔ Sum.inl (N.leaf a) ∈ S' := mem_iff_mem_of_ne hS' (f' := .inr .out) (by simp)
  have hc : N.graph.Crosses f (Sum.inl ⁻¹' S') ↔ (insertCycle N a g₀).graph.Crosses (.inl f) S' := by
    by_cases hf : f = g₀
    · subst hf
      simp only [DirectedMultigraph.Crosses, source_inl, target_inl_self, Set.mem_preimage, hg, hl, ho]
    · simp only [DirectedMultigraph.Crosses, source_inl, target_inl_of_ne hf, Set.mem_preimage]
  rw [hc, hS' (.inl f)]
  exact ⟨fun h => Sum.inl_injective h, fun h => congrArg _ h⟩

/-- **The edge to the taxon, as a cut edge, is the edge `g₀` of the network.** -/
theorem crosses_of_insertCycle_out {S' : Set (V ⊕ CycleNode)} (hS' : ∀ f, (insertCycle N a g₀).graph.Crosses f S' ↔ f = .inr .out) (f : E) :
    N.graph.Crosses f (Sum.inl ⁻¹' S') ↔ f = g₀ := by
  have hg : N.graph.target g₀ = N.leaf a := (hg₀ g₀).mpr rfl
  have hl : Sum.inr CycleNode.top ∈ S' ↔ Sum.inr CycleNode.bottom ∈ S' := mem_iff_mem_of_ne hS' (f' := .inr .left) (by simp)
  have hg' : Sum.inl (N.graph.source g₀) ∈ S' ↔ Sum.inr CycleNode.top ∈ S' := by
    have := mem_iff_mem_of_ne hS' (f' := .inl g₀) (by simp)
    rwa [source_inl, target_inl_self] at this
  have ho : (Sum.inr CycleNode.bottom ∈ S' ∧ Sum.inl (N.leaf a) ∉ S') ∨ (Sum.inl (N.leaf a) ∈ S' ∧ Sum.inr CycleNode.bottom ∉ S') := (hS' (.inr .out)).mpr rfl
  by_cases hf : f = g₀
  · subst hf
    simp only [DirectedMultigraph.Crosses, Set.mem_preimage, hg, iff_true]
    tauto
  · have hc := mem_iff_mem_of_ne hS' (f' := .inl f) (by simp)
    rw [source_inl, target_inl_of_ne hf] at hc
    simp only [DirectedMultigraph.Crosses, Set.mem_preimage, hf, iff_false]
    tauto

/-- **Cut edges.** -/
theorem isBridge_inl_iff (e : E) : (insertCycle N a g₀).graph.underlying.IsBridge (.inl e) ↔ N.graph.underlying.IsBridge e := by
  rw [DirectedMultigraph.isBridge_iff, DirectedMultigraph.isBridge_iff]
  exact ⟨fun ⟨S', hS'⟩ => ⟨_, crosses_of_insertCycle hg₀ hS'⟩, fun ⟨S, hS⟩ => ⟨_, crosses_collapse_iff hg₀ hS⟩⟩

omit hg₀ in
theorem not_isBridge_left : ¬ (insertCycle N a g₀).graph.underlying.IsBridge (.inr .left) :=
  (insertCycle N a g₀).graph.not_isBridge_of_parallel (e := Sum.inr CycleArc.left) (f := Sum.inr CycleArc.right) (by simp) rfl rfl

omit hg₀ in
theorem not_isBridge_right : ¬ (insertCycle N a g₀).graph.underlying.IsBridge (.inr .right) :=
  (insertCycle N a g₀).graph.not_isBridge_of_parallel (e := Sum.inr CycleArc.right) (f := Sum.inr CycleArc.left) (by simp) rfl rfl

theorem isBridge_out (hno : ∀ e, N.graph.source e ≠ N.leaf a) : (insertCycle N a g₀).graph.underlying.IsBridge (.inr .out) := by
  rw [DirectedMultigraph.isBridge_iff]
  refine ⟨{.inl (N.leaf a)}, fun f => ⟨fun hc => ?_, ?_⟩⟩
  · rcases f with e | i
    · exfalso
      rcases hc with ⟨h₁, -⟩ | ⟨h₁, -⟩
      · exact hno e (Sum.inl_injective h₁)
      · by_cases he : e = g₀
        · subst he
          rw [target_inl_self] at h₁
          cases h₁
        · rw [target_inl_of_ne he] at h₁
          exact he ((hg₀ e).mp (Sum.inl_injective h₁))
    · cases i
      · rcases hc with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;> cases h₁
      · rcases hc with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;> cases h₁
      · rfl
  · rintro rfl
    refine Or.inr ⟨rfl, ?_⟩
    rintro h
    cases h

/-- **The cut edges with the 2-cycle inserted**: those of the network, and the edge to the taxon. -/
theorem ncard_isBridge_insertCycle [Finite E] (hno : ∀ e, N.graph.source e ≠ N.leaf a) :
    {f | (insertCycle N a g₀).graph.underlying.IsBridge f}.ncard = {e | N.graph.underlying.IsBridge e}.ncard + 1 := by
  have hset : {f | (insertCycle N a g₀).graph.underlying.IsBridge f} = Sum.inl '' {e | N.graph.underlying.IsBridge e} ∪ {.inr .out} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
    constructor
    · intro hf
      rcases f with e | i
      · exact Or.inl ⟨e, (isBridge_inl_iff hg₀ e).mp hf, rfl⟩
      · cases i
        · exact absurd hf not_isBridge_left
        · exact absurd hf not_isBridge_right
        · exact Or.inr rfl
    · rintro (⟨e, he, rfl⟩ | rfl)
      · exact (isBridge_inl_iff hg₀ e).mpr he
      · exact isBridge_out hg₀ hno
  have hdisj : Disjoint (Sum.inl '' {e | N.graph.underlying.IsBridge e}) ({.inr .out} : Set (E ⊕ CycleArc)) := by
    refine Set.disjoint_singleton_right.mpr ?_
    rintro ⟨e, -, h⟩
    cases h
  rw [hset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_singleton]

/-- **The cut-edge splits are unchanged.** -/
theorem hasCutSplit_insertCycle_iff (A : Set X) : (insertCycle N a g₀).HasCutSplit A ↔ N.HasCutSplit A := by
  constructor
  · rintro ⟨e', S', hS', rfl⟩
    rcases e' with e | i
    · exact ⟨e, Sum.inl ⁻¹' S', crosses_of_insertCycle hg₀ hS', rfl⟩
    · cases i
      · exact absurd ((insertCycle N a g₀).graph.isBridge_iff _ |>.mpr ⟨S', hS'⟩) not_isBridge_left
      · exact absurd ((insertCycle N a g₀).graph.isBridge_iff _ |>.mpr ⟨S', hS'⟩) not_isBridge_right
      · exact ⟨g₀, Sum.inl ⁻¹' S', crosses_of_insertCycle_out hg₀ hS', rfl⟩
  · rintro ⟨e, S, hS, rfl⟩
    exact ⟨.inl e, collapse N a ⁻¹' S, crosses_collapse_iff hg₀ hS, rfl⟩

/-- **The tree of blobs is unchanged.** -/
theorem treeOfBlobs_insertCycle [Fintype X] [DecidableEq X] : treeOfBlobs (insertCycle N a g₀) = treeOfBlobs N := by
  ext A
  rw [mem_treeOfBlobs_iff, mem_treeOfBlobs_iff, hasCutSplit_insertCycle_iff hg₀]

/-! #### It is a network -/

omit hg₀ in
/-- A path of the network gives a path with the 2-cycle inserted. -/
theorem insertCycle_reaches (hg₀ : ∀ f, N.graph.target f = N.leaf a ↔ f = g₀) {u w : V} (h : N.graph.Reaches u w) :
    (insertCycle N a g₀).graph.Reaches (.inl u) (.inl w) := by
  have hg : N.graph.target g₀ = N.leaf a := (hg₀ g₀).mpr rfl
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨e, rfl, rfl⟩ := hbc
    by_cases he : e = g₀
    · subst he
      refine ih.tail ⟨.inl e, rfl, target_inl_self⟩ |>.tail ⟨.inr .left, rfl, rfl⟩ |>.tail ⟨.inr .out, rfl, ?_⟩
      rw [target_out, hg]
    · exact ih.tail ⟨.inl e, rfl, target_inl_of_ne he⟩

omit hg₀ in
/-- A path with the 2-cycle inserted gives a path of the network, removing the 2-cycle. -/
theorem collapse_reaches (hg₀ : ∀ f, N.graph.target f = N.leaf a ↔ f = g₀) {u w : V ⊕ CycleNode} (h : (insertCycle N a g₀).graph.Reaches u w) :
    N.graph.Reaches (collapse N a u) (collapse N a w) := by
  have hg : N.graph.target g₀ = N.leaf a := (hg₀ g₀).mpr rfl
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨f, rfl, rfl⟩ := hbc
    rcases f with e | i
    · by_cases he : e = g₀
      · subst he
        rw [target_inl_self]
        exact ih.tail ⟨e, rfl, hg⟩
      · rw [target_inl_of_ne he]
        exact ih.tail ⟨e, rfl, rfl⟩
    · cases i <;> exact ih

/-- **With a 2-cycle inserted above a taxon, a network is still a network of Definition 1.** -/
theorem isBinaryNetwork_insertCycle (hN : IsBinaryNetwork N) : IsBinaryNetwork (insertCycle N a g₀) := by
  have hP := hN.isPhylogenetic
  have hB := hN.isBinary
  have : Finite V := hP.finite_vertices
  have : Finite E := hP.finite_arcs
  have hg : N.graph.target g₀ = N.leaf a := (hg₀ g₀).mpr rfl
  have hno : ∀ x (e : E), N.graph.source e ≠ N.leaf x := fun x => (N.graph.outdegree_eq_zero_iff _).mp ((hP.leaves _).mpr ⟨x, rfl⟩)
  have hnoT : ∀ e : E, N.graph.target e ≠ N.root := target_ne_root hP
  -- degrees
  have hout : ∀ v : V, (insertCycle N a g₀).graph.outdegree (.inl v) = N.graph.outdegree v := fun v => by
    have hset : {f | (insertCycle N a g₀).graph.source f = .inl v} = Sum.inl '' {e | N.graph.source e = v} := by
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rcases f with e | i
        · exact fun hf => ⟨e, Sum.inl_injective hf, rfl⟩
        · cases i <;> exact fun hf => by cases hf
      · rintro ⟨e, he, rfl⟩
        exact congrArg _ he
    change {f | (insertCycle N a g₀).graph.source f = .inl v}.ncard = _
    rw [hset, Set.ncard_image_of_injective _ Sum.inl_injective]
    rfl
  have hin : ∀ v : V, v ≠ N.leaf a → (insertCycle N a g₀).graph.indegree (.inl v) = N.graph.indegree v := fun v hv => by
    have hset : {f | (insertCycle N a g₀).graph.target f = .inl v} = Sum.inl '' {e | N.graph.target e = v} := by
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rcases f with e | i
        · intro hf
          by_cases he : e = g₀
          · subst he
            rw [target_inl_self] at hf
            cases hf
          · rw [target_inl_of_ne he] at hf
            exact ⟨e, Sum.inl_injective hf, rfl⟩
        · cases i
          · exact fun hf => by cases hf
          · exact fun hf => by cases hf
          · exact fun hf => absurd (Sum.inl_injective hf).symm hv
      · rintro ⟨e, he, rfl⟩
        have hne : e ≠ g₀ := fun h => hv (by rw [← he, h, hg])
        rw [target_inl_of_ne hne, he]
    change {f | (insertCycle N a g₀).graph.target f = .inl v}.ncard = _
    rw [hset, Set.ncard_image_of_injective _ Sum.inl_injective]
    rfl
  have hntop : (insertCycle N a g₀).graph.outdegree (.inr .top) = 2 := by
    refine Set.ncard_eq_two.mpr ⟨.inr .left, .inr .right, by simp, ?_⟩
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases f with e | i
    · simp
    · cases i <;> simp
  have hintop : (insertCycle N a g₀).graph.indegree (.inr .top) = 1 := by
    refine (DirectedMultigraph.indegree_eq_one_iff _ _).mpr ⟨.inl g₀, fun f => ⟨fun hf => ?_, ?_⟩⟩
    · rcases f with e | i
      · by_cases he : e = g₀
        · rw [he]
        · rw [target_inl_of_ne he] at hf
          cases hf
      · cases i <;> cases hf
    · rintro rfl
      exact target_inl_self
  have hinbot : (insertCycle N a g₀).graph.indegree (.inr .bottom) = 2 := by
    refine Set.ncard_eq_two.mpr ⟨.inr .left, .inr .right, by simp, ?_⟩
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases f with e | i
    · by_cases he : e = g₀
      · subst he
        simp [target_inl_self]
      · simp [target_inl_of_ne he]
    · cases i <;> simp
  have hnbot : (insertCycle N a g₀).graph.outdegree (.inr .bottom) = 1 := by
    refine (DirectedMultigraph.outdegree_eq_one_iff _ _).mpr ⟨.inr .out, fun f => ⟨fun hf => ?_, ?_⟩⟩
    · rcases f with e | i
      · cases hf
      · cases i
        · cases hf
        · cases hf
        · rfl
    · rintro rfl
      rfl
  have hinleaf : (insertCycle N a g₀).graph.indegree (.inl (N.leaf a)) = 1 := by
    refine (DirectedMultigraph.indegree_eq_one_iff _ _).mpr ⟨.inr .out, fun f => ⟨fun hf => ?_, ?_⟩⟩
    · rcases f with e | i
      · exfalso
        by_cases he : e = g₀
        · subst he
          rw [target_inl_self] at hf
          cases hf
        · rw [target_inl_of_ne he] at hf
          exact he ((hg₀ e).mp (Sum.inl_injective hf))
      · cases i
        · cases hf
        · cases hf
        · rfl
    · rintro rfl
      rfl
  have hA : (insertCycle N a g₀).graph.IsAcyclic := by
    intro x hx
    obtain ⟨y, ⟨f, rfl, rfl⟩, hr⟩ := Relation.TransGen.head'_iff.mp hx
    have hcol := collapse_reaches hg₀ hr
    rcases f with e | i
    · by_cases he : e = g₀
      · subst he
        rw [target_inl_self] at hr hcol
        -- the source of `g₀` would be below the taxon
        have hcol' : N.graph.Reaches (N.leaf a) (N.graph.source e) := hcol
        have hle := N.graph.eq_of_reaches_of_outdegree_eq_zero hcol' ((hP.leaves _).mpr ⟨a, rfl⟩)
        exact hno a e hle
      · rw [target_inl_of_ne he] at hcol
        exact not_reaches_target_source hP.acyclic e hcol
    · have hstay : ∀ z, (insertCycle N a g₀).graph.Reaches (.inr .bottom) z → z = .inr .bottom ∨ z = .inl (N.leaf a) := by
        intro z hz
        induction hz with
        | refl => exact Or.inl rfl
        | @tail b c _ hbc ih =>
          obtain ⟨f, rfl, rfl⟩ := hbc
          rcases ih with ih | ih
          · rcases f with e | j
            · cases ih
            · cases j
              · cases ih
              · cases ih
              · exact Or.inr rfl
          · rcases f with e | j
            · exact absurd (Sum.inl_injective ih) (hno a e)
            · cases j <;> cases ih
      have hleafstay : ∀ z, (insertCycle N a g₀).graph.Reaches (.inl (N.leaf a)) z → z = .inl (N.leaf a) := by
        intro z hz
        induction hz with
        | refl => rfl
        | @tail b c _ hbc ih =>
          obtain ⟨f, rfl, rfl⟩ := hbc
          rcases f with e | j
          · exact absurd (Sum.inl_injective ih) (hno a e)
          · cases j <;> cases ih
      cases i
      · rcases hstay _ hr with h' | h' <;> cases h'
      · rcases hstay _ hr with h' | h' <;> cases h'
      · have := hleafstay _ hr
        cases this
  have hreach : ∀ v, (insertCycle N a g₀).graph.Reaches (.inl N.root) v := by
    rintro (v | t)
    · exact insertCycle_reaches hg₀ (hP.root_reaches v)
    · have htop : (insertCycle N a g₀).graph.Reaches (.inl N.root) (.inr .top) :=
        (insertCycle_reaches hg₀ (hP.root_reaches (N.graph.source g₀))).tail ⟨.inl g₀, rfl, target_inl_self⟩
      cases t
      · exact htop
      · exact htop.tail ⟨.inr .left, rfl, rfl⟩
  refine isBinaryNetwork_iff.mpr ⟨⟨inferInstance, inferInstance, hP.finite_taxa, hA, hreach, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [DirectedMultigraph.indegree_eq_zero_iff]
    rintro (e | i) hf
    · by_cases he : e = g₀
      · subst he
        rw [target_inl_self] at hf
        cases hf
      · rw [target_inl_of_ne he] at hf
        exact hnoT e (Sum.inl_injective hf)
    · cases i
      · cases hf
      · cases hf
      · exact N.leaf_ne_root hP a (Sum.inl_injective hf)
  · rintro (v | t) hv
    · have hv' : v ≠ N.root := fun h => hv (congrArg _ h)
      by_cases hva : v = N.leaf a
      · rw [hva, hinleaf]
      · rw [hin v hva]
        exact hP.nonroot_indegree v hv'
    · cases t
      · rw [hintop]
      · rw [hinbot]
        omega
  · intro x y hxy
    exact hP.leaf_injective (Sum.inl_injective hxy)
  · intro x
    by_cases hx : x = a
    · subst hx
      exact hinleaf
    · have hne : N.leaf x ≠ N.leaf a := fun h => hx (hP.leaf_injective h)
      change (insertCycle N a g₀).graph.indegree (.inl (N.leaf x)) = 1
      rw [hin _ hne]
      exact hP.leaf_indegree x
  · rintro (v | t)
    · rw [hout v, hP.leaves v]
      exact ⟨fun ⟨x, hx⟩ => ⟨x, congrArg _ hx⟩, fun ⟨x, hx⟩ => ⟨x, Sum.inl_injective hx⟩⟩
    · cases t
      · rw [hntop]
        simp only [OfNat.ofNat_ne_zero, false_iff, not_exists]
        intro x h
        cases h
      · rw [hnbot]
        simp only [one_ne_zero, false_iff, not_exists]
        intro x h
        cases h
  · change (insertCycle N a g₀).graph.outdegree (.inl N.root) = 2
    rw [hout]
    exact hB.1
  · rintro (v | t) hv h0
    · have hv' : v ≠ N.root := fun h => hv (congrArg _ h)
      rw [hout] at h0 ⊢
      have hva : v ≠ N.leaf a := fun h => h0 (h ▸ (hP.leaves _).mpr ⟨a, rfl⟩)
      rw [hin v hva]
      exact hB.2 v hv' h0
    · cases t
      · rw [hintop, hntop]
      · rw [hinbot, hnbot]

/-! #### The LSA stays the root -/

omit hg₀ in
/-- A path avoiding a node, with the 2-cycle inserted. -/
theorem insertCycle_hasPathAvoiding (hg₀ : ∀ f, N.graph.target f = N.leaf a ↔ f = g₀) {u t v : V} (h : N.HasPathAvoiding u t v) :
    (insertCycle N a g₀).HasPathAvoiding (.inl u) (.inl t) (.inl v) := by
  have hg : N.graph.target g₀ = N.leaf a := (hg₀ g₀).mpr rfl
  obtain ⟨h₁, h₂, hp⟩ := h
  refine ⟨fun h' => h₁ (Sum.inl_injective h'), fun h' => h₂ (Sum.inl_injective h'), ?_⟩
  clear h₂
  induction hp with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨⟨e, rfl, rfl⟩, hb, hc⟩ := hbc
    have hb' : (Sum.inl (N.graph.source e) : V ⊕ CycleNode) ≠ .inl v := fun h' => hb (Sum.inl_injective h')
    have hc' : (Sum.inl (N.graph.target e) : V ⊕ CycleNode) ≠ .inl v := fun h' => hc (Sum.inl_injective h')
    by_cases he : e = g₀
    · subst he
      refine (ih.tail ⟨⟨.inl e, rfl, target_inl_self⟩, hb', by simp⟩).tail ⟨⟨.inr .left, rfl, rfl⟩, by simp, by simp⟩ |>.tail ⟨⟨.inr .out, rfl, ?_⟩, by simp, hc'⟩
      rw [target_out, hg]
    · exact ih.tail ⟨⟨.inl e, rfl, target_inl_of_ne he⟩, hb', hc'⟩

/-- **The LSA stays the root.** No node of the 2-cycle is a stable ancestor, since a path to another taxon doesn't go there. -/
theorem hasRootLSA_insertCycle (hN : IsBinaryNetwork N) (hL : HasRootLSA N) {y : X} (hy : y ≠ a) : HasRootLSA (insertCycle N a g₀) := by
  have hP := hN.isPhylogenetic
  have hg : N.graph.target g₀ = N.leaf a := (hg₀ g₀).mpr rfl
  have hf : Finite E := hP.finite_arcs
  rintro (v | t) hw
  · have hv : v = N.root := hL v fun x hx hp => hw x hx (insertCycle_hasPathAvoiding hg₀ hp)
    exact congrArg _ hv
  · exfalso
    have hav : N.AvoidingReach g₀ N.root (N.leaf y) := by
      by_contra hno
      have hr := target_reaches_of_not_avoidingReach (hP.root_reaches _) hno
      rw [hg] at hr
      exact hy (hP.leaf_injective (N.graph.eq_of_reaches_of_outdegree_eq_zero hr ((hP.leaves _).mpr ⟨a, rfl⟩)))
    have key : ∀ z, N.AvoidingReach g₀ N.root z → Relation.ReflTransGen (fun x w => (insertCycle N a g₀).graph.Adj x w ∧ x ≠ .inr t ∧ w ≠ .inr t) (.inl N.root) (.inl z) := by
      intro z hz
      induction hz with
      | refl => exact .refl
      | @tail b c _ hbc ih =>
        obtain ⟨e, he, rfl, rfl⟩ := hbc
        exact ih.tail ⟨⟨.inl e, rfl, target_inl_of_ne he⟩, by simp, by simp⟩
    exact hw y (Set.mem_univ y) ⟨by simp [insertCycle], by simp [insertCycle], key _ hav⟩

end Insert

/-! ### The invariant, along the family -/

/-- What the count needs of a network: it is a network of Definition 1 with the LSA at the root, with `n` cut edges, whose edges at the root are all cut edges, or none of them (`P`). -/
structure IsFamily (N : RootedNetwork V E X) (n : ℕ) (P : Prop) : Prop where
  isBinaryNetwork : IsBinaryNetwork N
  hasRootLSA : HasRootLSA N
  card_bridges : {e | N.graph.underlying.IsBridge e}.ncard = n
  root_arcs : ∀ e, N.graph.source e = N.root → (N.graph.underlying.IsBridge e ↔ P)

/-- **Inserting a 2-cycle above a taxon adds one cut edge, and leaves the B-quartets.** -/
theorem IsFamily.insertCycle [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} {n : ℕ} {P : Prop} (h : IsFamily N n P) {a y : X} (hy : y ≠ a) :
    ∃ g₀, IsFamily (insertCycle N a g₀) (n + 1) P ∧ (IsBlobQuartet (insertCycle N a g₀) Finset.univ ↔ IsBlobQuartet N Finset.univ) := by
  have hN := h.isBinaryNetwork
  have hP := hN.isPhylogenetic
  have : Finite E := hP.finite_arcs
  obtain ⟨g₀, hg₀⟩ := (N.graph.indegree_eq_one_iff _).mp (hP.leaf_indegree a)
  have hno : ∀ e : E, N.graph.source e ≠ N.leaf a := (N.graph.outdegree_eq_zero_iff _).mp ((hP.leaves _).mpr ⟨a, rfl⟩)
  have hN' := isBinaryNetwork_insertCycle hg₀ hN
  refine ⟨g₀, ⟨hN', hasRootLSA_insertCycle hg₀ hN h.hasRootLSA hy, ?_, ?_⟩, ?_⟩
  · rw [ncard_isBridge_insertCycle hg₀ hno, h.card_bridges]
  · rintro (e | i) hf
    · exact (isBridge_inl_iff hg₀ e).trans (h.root_arcs e (Sum.inl_injective hf))
    · cases i <;> cases hf
  · have hc : (Finset.univ : Finset X).card = 4 ∨ (Finset.univ : Finset X).card ≠ 4 := Decidable.em _
    rcases hc with hc | hc
    · rw [Bridges.isBlobQuartet_iff_isBQuartet hN'.isPhylogenetic hc, Bridges.isBlobQuartet_iff_isBQuartet hP hc]
      unfold IsBQuartet
      rw [treeOfBlobs_insertCycle hg₀]
    · exact ⟨fun h' => absurd h'.1 hc, fun h' => absurd h'.1 hc⟩

/-- The family, by induction. -/
theorem exists_isFamily {V₀ E₀ : Type} {N₀ : RootedNetwork V₀ E₀ (Fin 4)} {n₀ : ℕ} {P Q : Prop} (h₀ : IsFamily N₀ n₀ P) (hQ : IsBlobQuartet N₀ Finset.univ ↔ Q) (k : ℕ) :
    ∃ (V E : Type) (N : RootedNetwork V E (Fin 4)), IsFamily N (n₀ + k) P ∧ (IsBlobQuartet N Finset.univ ↔ Q) := by
  induction k with
  | zero => exact ⟨V₀, E₀, N₀, h₀, hQ⟩
  | succ k ih =>
    obtain ⟨V, E, N, h, hq⟩ := ih
    obtain ⟨g₀, h', hq'⟩ := h.insertCycle (a := 0) (y := 1) (by decide)
    exact ⟨_, _, _, h', hq'.trans hq⟩

section Final

variable {N : RootedNetwork V E (Fin 4)}

/-- The edge of the root merged away is at the root of `𝒩⁺`. -/
theorem source_rootTreeArc {V E X : Type*} {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) (hX : Nontrivial X) (hL : HasRootLSA N) :
    N.graph.source (rootTreeArc hN hX).1 = N.root :=
  (congrArg Subtype.val (rootTreeArc_spec hN hX).1).trans (lsaNode_eq_root hN hX hL)

/-- The number of 2-blobs, when no edge at the root is a cut edge. -/
theorem ncard_of_isFamily_false {n k : ℕ} (h : IsFamily N (4 + k) False) (hn : n = k) (hB : IsBlobQuartet N Finset.univ) :
    {b | cutDegree (semidirected h.isBinaryNetwork (nontrivial_of_card_four (Fintype.card_fin 4))).graph b = 2}.ncard = n := by
  have hN := h.isBinaryNetwork
  have hX := nontrivial_of_card_four (Fintype.card_fin 4)
  have hc := ncard_cutDegree_two_of_isBlobQuartet hN (Fintype.card_fin 4) hB
  rw [card_bridgeArc_semidirected hN hX h.hasRootLSA] at hc
  have hnot : (rootTreeArc hN hX).1 ∉ {e | N.graph.underlying.IsBridge e} := fun hb =>
    (h.root_arcs _ (source_rootTreeArc hN hX h.hasRootLSA)).mp hb
  rw [Set.sdiff_singleton_eq_self hnot, h.card_bridges] at hc
  omega

/-- The number of 2-blobs, when every edge at the root is a cut edge. -/
theorem ncard_of_isFamily_true {n k : ℕ} (h : IsFamily N (6 + k) True) (hn : n = k) (hT : IsTreeQuartet N Finset.univ) :
    {b | cutDegree (semidirected h.isBinaryNetwork (nontrivial_of_card_four (Fintype.card_fin 4))).graph b = 2}.ncard = n := by
  have hN := h.isBinaryNetwork
  have hX := nontrivial_of_card_four (Fintype.card_fin 4)
  have : Finite E := hN.finite_arcs
  have hc := ncard_cutDegree_two_of_isTreeQuartet hN (Fintype.card_fin 4) hT
  rw [card_bridgeArc_semidirected hN hX h.hasRootLSA] at hc
  have hmem : (rootTreeArc hN hX).1 ∈ {e | N.graph.underlying.IsBridge e} :=
    (h.root_arcs _ (source_rootTreeArc hN hX h.hasRootLSA)).mpr trivial
  rw [Set.ncard_sdiff_singleton_of_mem hmem, h.card_bridges] at hc
  omega

end Final

/-! ### The two networks to start from -/

section Base

variable {n m : ℕ}

/-- A network on numbered nodes and edges. -/
def finNetwork {k : ℕ} (src tgt : Fin m → Fin n) (r : Fin n) (ℓ : Fin k → Fin n) : RootedNetwork (Fin n) (Fin m) (Fin k) :=
  ⟨⟨src, tgt⟩, r, ℓ⟩

variable {k : ℕ} {src tgt : Fin m → Fin n} {r : Fin n} {ℓ : Fin k → Fin n}

theorem indegree_finNetwork (v : Fin n) : (finNetwork src tgt r ℓ).graph.indegree v = (Finset.univ.filter fun e => tgt e = v).card := by
  rw [indegree, Set.ncard_eq_toFinset_card']
  congr 1
  ext e
  simp only [finNetwork, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Set.mem_toFinset

theorem outdegree_finNetwork (v : Fin n) : (finNetwork src tgt r ℓ).graph.outdegree v = (Finset.univ.filter fun e => src e = v).card := by
  rw [outdegree, Set.ncard_eq_toFinset_card']
  congr 1
  ext e
  simp only [finNetwork, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Set.mem_toFinset

/-- **A network on numbered nodes, with edges going down in the numbering, is a network of Definition 1** if its degrees are right. -/
theorem isBinaryNetwork_finNetwork (hlt : ∀ e, tgt e < src e) (hpar : ∀ v, v ≠ r → ∃ e, tgt e = v) (htr : ∀ e, tgt e ≠ r) (hinj : Function.Injective ℓ)
    (hleaf : ∀ x, (Finset.univ.filter fun e => tgt e = ℓ x).card = 1) (hleaves : ∀ v, (Finset.univ.filter fun e => src e = v).card = 0 ↔ ∃ x, ℓ x = v)
    (hroot : (Finset.univ.filter fun e => src e = r).card = 2)
    (hbin : ∀ v, v ≠ r → (Finset.univ.filter fun e => src e = v).card ≠ 0 → (Finset.univ.filter fun e => tgt e = v).card + (Finset.univ.filter fun e => src e = v).card = 3) :
    IsBinaryNetwork (finNetwork src tgt r ℓ) := by
  have hA : (finNetwork src tgt r ℓ).graph.IsAcyclic := by
    refine DirectedMultigraph.isAcyclic_of_rank _ (fun v => n - v.1) fun e => ?_
    have := hlt e
    have h₂ := (src e).2
    change n - (src e).1 < n - (tgt e).1
    have : (tgt e).1 < (src e).1 := this
    omega
  have hreach : ∀ v, (finNetwork src tgt r ℓ).graph.Reaches r v := by
    intro v
    induction hk : n - v.1 using Nat.strong_induction_on generalizing v with
    | _ k ih =>
      by_cases hv : v = r
      · rw [hv]
        exact .refl
      · obtain ⟨e, he⟩ := hpar v hv
        have hl : (tgt e).1 < (src e).1 := hlt e
        have h₂ := (src e).2
        have hve : v.1 = (tgt e).1 := by rw [he]
        exact (ih (n - (src e).1) (by omega) (src e) rfl).tail ⟨e, rfl, he⟩
  refine isBinaryNetwork_iff.mpr ⟨⟨inferInstance, inferInstance, inferInstance, hA, hreach, ?_, ?_, hinj, ?_, ?_⟩, ?_, ?_⟩
  · exact (DirectedMultigraph.indegree_eq_zero_iff _ _).mpr htr
  · intro v hv
    exact (DirectedMultigraph.one_le_indegree_iff _ _).mpr (hpar v hv)
  · intro x
    rw [indegree_finNetwork]
    exact hleaf x
  · intro v
    rw [outdegree_finNetwork]
    exact hleaves v
  · rw [outdegree_finNetwork]
    exact hroot
  · intro v hv h0
    rw [outdegree_finNetwork] at h0 ⊢
    rw [indegree_finNetwork]
    exact hbin v hv h0

/-- A cut edge given by a set of nodes. -/
theorem isBridge_finNetwork {e : Fin m} (S : Finset (Fin n)) (h : ∀ f, ((src f ∈ S ∧ tgt f ∉ S) ∨ (tgt f ∈ S ∧ src f ∉ S)) ↔ f = e) :
    (finNetwork src tgt r ℓ).graph.underlying.IsBridge e :=
  ((finNetwork src tgt r ℓ).graph.isBridge_iff e).mpr ⟨(S : Set (Fin n)), fun f => by simpa [DirectedMultigraph.Crosses, finNetwork] using h f⟩

/-- A function constant along edges of `F` is constant along walks of `F`. -/
theorem eq_of_walks_finNetwork {α : Type*} (f : Fin n → α) {F : Set (Fin m)} (hF : ∀ e ∈ F, f (src e) = f (tgt e)) {u w : Fin n}
    (h : (finNetwork src tgt r ℓ).graph.Walks F u w) : f u = f w := by
  induction h with
  | refl => rfl
  | tail _ hab ih =>
    obtain ⟨e, he, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ := hab
    · exact ih.trans (hs ▸ ht ▸ hF e he)
    · exact ih.trans (ht ▸ hs ▸ (hF e he).symm)

/-- A path of two edges, from the root to a taxon, avoiding a node. -/
theorem hasPathAvoiding_two {e₁ e₂ : Fin m} {x : Fin k} {w : Fin n} (h₁ : src e₁ = r) (h₂ : tgt e₁ = src e₂) (h₃ : tgt e₂ = ℓ x) (hw₁ : w ≠ r) (hw₂ : w ≠ tgt e₁)
    (hw₃ : w ≠ ℓ x) : (finNetwork src tgt r ℓ).HasPathAvoiding r (ℓ x) w := by
  refine ⟨hw₁.symm, hw₃.symm, Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨⟨e₁, h₁, rfl⟩, hw₁.symm, hw₂.symm⟩) ⟨⟨e₂, h₂.symm, h₃⟩, hw₂.symm, hw₃.symm⟩⟩

end Base

/-! #### A tree: `((a, b), (c, d))` -/

/-- The sources of the edges of the tree: the taxa are `0, 1, 2, 3`, and then the parent of `a, b`, the parent of `c, d`, and the root. -/
def srcTree : Fin 6 → Fin 7 := ![6, 6, 4, 4, 5, 5]

/-- The targets of the edges of the tree. -/
def tgtTree : Fin 6 → Fin 7 := ![4, 5, 0, 1, 2, 3]

/-- The taxa. -/
def leafBase (n : ℕ) (h : 4 ≤ n) : Fin 4 → Fin n := Fin.castLE h

/-- The tree `((a, b), (c, d))`. -/
def treeBase : RootedNetwork (Fin 7) (Fin 6) (Fin 4) := finNetwork srcTree tgtTree 6 (leafBase 7 (by norm_num))

theorem isBinaryNetwork_treeBase : IsBinaryNetwork treeBase :=
  isBinaryNetwork_finNetwork (by decide) (by decide) (by decide) (Fin.castLE_injective _) (by decide) (by decide) (by decide) (by decide)

theorem hasRootLSA_treeBase : HasRootLSA treeBase := by
  intro w hw
  by_contra hne
  by_cases hw₂ : w = 5 ∨ w = 2
  · have hne₄ : w ≠ 4 := by rcases hw₂ with rfl | rfl <;> decide
    have hne₀ : w ≠ 0 := by rcases hw₂ with rfl | rfl <;> decide
    exact hw 0 (Set.mem_univ _) (hasPathAvoiding_two (e₁ := 0) (e₂ := 2) rfl rfl rfl hne hne₄ hne₀)
  · push Not at hw₂
    exact hw 2 (Set.mem_univ _) (hasPathAvoiding_two (e₁ := 1) (e₂ := 4) rfl rfl rfl hne hw₂.1 hw₂.2)

theorem isBridge_treeBase (e : Fin 6) : treeBase.graph.underlying.IsBridge e := by
  fin_cases e
  · exact isBridge_finNetwork {4, 0, 1} (by decide)
  · exact isBridge_finNetwork {5, 2, 3} (by decide)
  · exact isBridge_finNetwork {0} (by decide)
  · exact isBridge_finNetwork {1} (by decide)
  · exact isBridge_finNetwork {2} (by decide)
  · exact isBridge_finNetwork {3} (by decide)

theorem isFamily_treeBase : IsFamily treeBase 6 True where
  isBinaryNetwork := isBinaryNetwork_treeBase
  hasRootLSA := hasRootLSA_treeBase
  card_bridges := by
    have hset : {e | treeBase.graph.underlying.IsBridge e} = Set.univ := Set.eq_univ_of_forall isBridge_treeBase
    rw [hset, Set.ncard_univ, Nat.card_fin]
  root_arcs e _ := iff_true_intro (isBridge_treeBase e)

/-- The tree has a cut edge separating `a, b` from `c, d`. -/
theorem not_isBlobQuartet_treeBase : ¬ IsBlobQuartet treeBase Finset.univ := by
  rintro ⟨-, b, hb⟩
  induction b using Quotient.inductionOn with
  | h v =>
    obtain ⟨-, hd⟩ := isDeterminedBy_blobOf_iff.mp hb
    have hP := isBinaryNetwork_treeBase.isPhylogenetic
    have hw : ∀ x, treeBase.graph.Walks Set.univ v x := fun x => treeBase.graph_connected hP v x
    let T : Set (Fin 7) := {u | u ∈ ({4, 0, 1} : Finset (Fin 7))}
    have hO : OnlyCrosses treeBase.graph Set.univ 0 T := by
      intro f _ hc
      have hd' : ∀ f : Fin 6, (srcTree f ∈ ({4, 0, 1} : Finset (Fin 7)) ∧ tgtTree f ∉ ({4, 0, 1} : Finset (Fin 7))) ∨
          (tgtTree f ∈ ({4, 0, 1} : Finset (Fin 7)) ∧ srcTree f ∉ ({4, 0, 1} : Finset (Fin 7))) → f = 0 := by
        decide
      exact hd' f hc
    by_cases hv : v ∈ T
    · have hT' : v ∉ Tᶜ := not_not.mpr hv
      have : (2 : Fin 4) = 3 := hd.eq_of_mem_side hO.compl hT' (Finset.mem_univ _) (Finset.mem_univ _) (hw _) (hw _)
        (by simp [T, treeBase, finNetwork, leafBase]) (by simp [T, treeBase, finNetwork, leafBase])
      exact absurd this (by decide)
    · have : (0 : Fin 4) = 1 := hd.eq_of_mem_side hO hv (Finset.mem_univ _) (Finset.mem_univ _) (hw _) (hw _)
        (by simp [T, treeBase, finNetwork, leafBase]) (by simp [T, treeBase, finNetwork, leafBase])
      exact absurd this (by decide)

/-! #### A 4-cycle -/

/-- The sources of the edges of the 4-cycle: the taxa are `0, 1, 2, 3`, then the hybrid node `4`, the nodes `5, 6, 7` of the cycle, and the root `8`. -/
def srcCycle : Fin 9 → Fin 9 := ![8, 8, 7, 7, 6, 6, 5, 5, 4]

/-- The targets of the edges of the 4-cycle. -/
def tgtCycle : Fin 9 → Fin 9 := ![4, 7, 1, 6, 2, 5, 3, 4, 0]

/-- The network with a 4-blob on the taxa: a cycle through the root, which `𝒩⁻` suppresses. -/
def cycleBase : RootedNetwork (Fin 9) (Fin 9) (Fin 4) := finNetwork srcCycle tgtCycle 8 (leafBase 9 (by norm_num))

theorem isBinaryNetwork_cycleBase : IsBinaryNetwork cycleBase :=
  isBinaryNetwork_finNetwork (by decide) (by decide) (by decide) (Fin.castLE_injective _) (by decide) (by decide) (by decide) (by decide)

theorem hasRootLSA_cycleBase : HasRootLSA cycleBase := by
  intro w hw
  by_contra hne
  by_cases hw₂ : w = 4 ∨ w = 0
  · have hne₄ : w ≠ 7 := by rcases hw₂ with rfl | rfl <;> decide
    have hne₀ : w ≠ 1 := by rcases hw₂ with rfl | rfl <;> decide
    exact hw 1 (Set.mem_univ _) (hasPathAvoiding_two (e₁ := 1) (e₂ := 2) rfl rfl rfl hne hne₄ hne₀)
  · push Not at hw₂
    exact hw 0 (Set.mem_univ _) (hasPathAvoiding_two (e₁ := 0) (e₂ := 8) rfl rfl rfl hne hw₂.1 hw₂.2)

/-- The edges of the cycle aren't cut edges: the other four go around. -/
theorem not_isBridge_cycleBase {e : Fin 9} (he : e = 0 ∨ e = 1 ∨ e = 3 ∨ e = 5 ∨ e = 7) : ¬ cycleBase.graph.underlying.IsBridge e := by
  rw [DirectedMultigraph.isBridge_iff_not_walks_delete, not_not]
  have fwd : ∀ f : Fin 9, f ≠ e → cycleBase.graph.AdjOn {e}ᶜ (srcCycle f) (tgtCycle f) := fun f hf => ⟨f, hf, Or.inl ⟨rfl, rfl⟩⟩
  have bwd : ∀ f : Fin 9, f ≠ e → cycleBase.graph.AdjOn {e}ᶜ (tgtCycle f) (srcCycle f) := fun f hf => ⟨f, hf, Or.inr ⟨rfl, rfl⟩⟩
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact (((Relation.ReflTransGen.single (fwd 1 (by decide))).tail (fwd 3 (by decide))).tail (fwd 5 (by decide))).tail (fwd 7 (by decide))
  · exact (((Relation.ReflTransGen.single (fwd 0 (by decide))).tail (bwd 7 (by decide))).tail (bwd 5 (by decide))).tail (bwd 3 (by decide))
  · exact (((Relation.ReflTransGen.single (bwd 1 (by decide))).tail (fwd 0 (by decide))).tail (bwd 7 (by decide))).tail (bwd 5 (by decide))
  · exact (((Relation.ReflTransGen.single (bwd 3 (by decide))).tail (bwd 1 (by decide))).tail (fwd 0 (by decide))).tail (bwd 7 (by decide))
  · exact (((Relation.ReflTransGen.single (bwd 5 (by decide))).tail (bwd 3 (by decide))).tail (bwd 1 (by decide))).tail (fwd 0 (by decide))

theorem isBridge_cycleBase {e : Fin 9} (he : e = 2 ∨ e = 4 ∨ e = 6 ∨ e = 8) : cycleBase.graph.underlying.IsBridge e := by
  rcases he with rfl | rfl | rfl | rfl
  · exact isBridge_finNetwork {1} (by decide)
  · exact isBridge_finNetwork {2} (by decide)
  · exact isBridge_finNetwork {3} (by decide)
  · exact isBridge_finNetwork {0} (by decide)

theorem isFamily_cycleBase : IsFamily cycleBase 4 False where
  isBinaryNetwork := isBinaryNetwork_cycleBase
  hasRootLSA := hasRootLSA_cycleBase
  card_bridges := by
    have hset : {e | cycleBase.graph.underlying.IsBridge e} = (({2, 4, 6, 8} : Finset (Fin 9)) : Set (Fin 9)) := by
      ext e
      simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hb
        by_contra hno
        have hc : ∀ e : Fin 9, ¬ (e = 2 ∨ e = 4 ∨ e = 6 ∨ e = 8) → e = 0 ∨ e = 1 ∨ e = 3 ∨ e = 5 ∨ e = 7 := by decide
        exact not_isBridge_cycleBase (hc e hno) hb
      · exact isBridge_cycleBase
    rw [hset, Set.ncard_coe_finset]
    rfl
  root_arcs e he := by
    have hcase : srcCycle e = 8 → e = 0 ∨ e = 1 := by
      revert e
      decide
    have := not_isBridge_cycleBase (e := e) ((hcase he).elim Or.inl (fun h => Or.inr (Or.inl h)))
    exact iff_false_intro this

/-- **The taxa form a B-quartet on the 4-cycle**: deleting the edges of the blob of the cycle leaves each with its own node. -/
theorem isBlobQuartet_cycleBase : IsBlobQuartet cycleBase Finset.univ := by
  refine (isBlobQuartet_iff_deletion isBinaryNetwork_cycleBase).mpr ⟨rfl, blobOf cycleBase.graph 4, fun s _ t _ hst hw => hst ?_⟩
  have hb : ∀ {f : Fin 9}, (f = 0 ∨ f = 1 ∨ f = 3 ∨ f = 5 ∨ f = 7) →
      blobOf cycleBase.graph (cycleBase.graph.source f) = blobOf cycleBase.graph (cycleBase.graph.target f) := fun hf =>
    cycleBase.graph.quotient_eq_of_not_isBridge (not_isBridge_cycleBase hf)
  have h₀ : blobOf cycleBase.graph 8 = blobOf cycleBase.graph 4 := hb (f := 0) (by decide)
  have h₁ : blobOf cycleBase.graph 8 = blobOf cycleBase.graph 7 := hb (f := 1) (by decide)
  have h₃ : blobOf cycleBase.graph 7 = blobOf cycleBase.graph 6 := hb (f := 3) (by decide)
  have h₅ : blobOf cycleBase.graph 6 = blobOf cycleBase.graph 5 := hb (f := 5) (by decide)
  have h₇ : blobOf cycleBase.graph 5 = blobOf cycleBase.graph 4 := hb (f := 7) (by decide)
  have hmem : ∀ f : Fin 9, f = 0 ∨ f = 1 ∨ f = 3 ∨ f = 5 ∨ f = 7 → f ∈ blobEdges cycleBase.graph (blobOf cycleBase.graph 4) := by
    have h₆ : blobOf cycleBase.graph 6 = blobOf cycleBase.graph 4 := h₅.trans h₇
    have h₇' : blobOf cycleBase.graph 7 = blobOf cycleBase.graph 4 := h₃.trans h₆
    rintro f (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨h₀, rfl⟩
    · exact ⟨h₀, h₇'⟩
    · exact ⟨h₇', h₆⟩
    · exact ⟨h₆, h₇⟩
    · exact ⟨h₇, rfl⟩
  let col : Fin 9 → Fin 5 := ![0, 1, 2, 3, 0, 3, 2, 1, 4]
  have hF : ∀ e ∈ (blobEdges cycleBase.graph (blobOf cycleBase.graph 4))ᶜ, col (srcCycle e) = col (tgtCycle e) := by
    intro e he
    have hd : ∀ e : Fin 9, ¬ (e = 0 ∨ e = 1 ∨ e = 3 ∨ e = 5 ∨ e = 7) → col (srcCycle e) = col (tgtCycle e) := by decide
    exact hd e fun h => he (hmem e h)
  have hc : col (leafBase 9 (by norm_num) s) = col (leafBase 9 (by norm_num) t) := eq_of_walks_finNetwork col hF hw
  have hcol : ∀ x : Fin 4, col (leafBase 9 (by norm_num) x) = Fin.castLE (by norm_num) x := by decide
  rw [hcol s, hcol t] at hc
  exact Fin.castLE_injective _ hc

/-! ### Any number of 2-blobs -/

/-- **"In either case, `𝒩⁻` may have any number of 2-blobs"** (`a:claim:two-blobs-any`, in Lemma 1), in the first case: for every `k`, a 4-taxon network whose taxa form a B-quartet, with exactly `k` 2-blobs on `𝒩⁻`. The network is
the 4-cycle, with `k` 2-cycles inserted above a taxon. -/
theorem exists_network_star (k : ℕ) :
    ∃ (V E : Type) (N : RootedNetwork V E (Fin 4)) (hN : IsBinaryNetwork N), IsBlobQuartet N Finset.univ ∧
      {b | cutDegree (semidirected hN (nontrivial_of_card_four (Fintype.card_fin 4))).graph b = 2}.ncard = k := by
  obtain ⟨V, E, N, h, hq⟩ := exists_isFamily isFamily_cycleBase (Q := True) (iff_true_intro isBlobQuartet_cycleBase) k
  have hB := hq.mpr trivial
  exact ⟨V, E, N, h.isBinaryNetwork, hB, ncard_of_isFamily_false h rfl hB⟩

/-- **"In either case, `𝒩⁻` may have any number of 2-blobs"** (`a:claim:two-blobs-any`, in Lemma 1), in the second case: for every `k`, a 4-taxon network whose taxa form a T-quartet, with exactly `k` 2-blobs on `𝒩⁻`. The network is
the tree `((a, b), (c, d))`, with `k` 2-cycles inserted above a taxon. -/
theorem exists_network_resolved (k : ℕ) :
    ∃ (V E : Type) (N : RootedNetwork V E (Fin 4)) (hN : IsBinaryNetwork N), IsTreeQuartet N Finset.univ ∧
      {b | cutDegree (semidirected hN (nontrivial_of_card_four (Fintype.card_fin 4))).graph b = 2}.ncard = k := by
  obtain ⟨V, E, N, h, hq⟩ := exists_isFamily isFamily_treeBase (Q := False) (iff_false_intro not_isBlobQuartet_treeBase) k
  have hT : IsTreeQuartet N Finset.univ := ⟨rfl, fun hB => hq.mp hB⟩
  exact ⟨V, E, N, h.isBinaryNetwork, hT, ncard_of_isFamily_true h rfl hT⟩

end AllmanEtAl2023.InPassing
