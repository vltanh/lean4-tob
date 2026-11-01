module

public import Gusfield2007.DecompNet
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum

/-!
# Gusfield et al. 2007: a rooted tree with its central nodes inflated to blobs

The end of the proof of Theorem 1 (lines 299 to 303), as a construction on networks. It takes a rooted tree on the type `W`, by its parent map; a node `center C` of it for
each non-trivial component `C` of a graph `G` on the sites; and a network `P C` on the sites of `C`. Each central node is replaced by its network: an edge into the node arrives at
the root of `P C`, and an edge out of it leaves from the node `exit C b` of `P C`. The result is `GlueData.net`. What's proved about it doesn't use the tree any
further, except for the labels on its edges (`GlueData.Valid`).
-/

@[expose] public noncomputable section

open scoped Classical

namespace Gusfield2007

namespace Decomp

universe u v w

variable {ι : Type u} {G : SimpleGraph ι}

/-- The non-trivial components of `G`. -/
abbrev Cent (G : SimpleGraph ι) : Type u := {c : G.ConnectedComponent // c.supp.Nontrivial}

/-- The data for gluing: a rooted tree on `W`, its central nodes, the labels of its nodes, the nodes from which edges leave a network `P C`, and the edge of `W` for each site
out of the non-trivial components. -/
structure GlueData {Vp Ep : Cent G → Type w} (P : ∀ C : Cent G, Network C.1.supp (Vp C) (Ep C)) (W : Type v) where
  /-- The root. -/
  ρ : W
  /-- The parent. -/
  par : W → W
  /-- The depth. -/
  depth : W → ℕ
  depth_par : ∀ b, b ≠ ρ → depth (par b) < depth b
  /-- The central node of a non-trivial component. -/
  center : Cent G → W
  center_inj : Function.Injective center
  center_ne : ∀ C, center C ≠ ρ
  /-- The label of a node of the tree. -/
  lam : W → ι → Bool
  /-- The node of `P C` that the edge into `b` leaves from, when the parent of `b` is the central node of `C`. -/
  exit : ∀ C : Cent G, W → Vp C
  /-- The node of the tree whose incoming edge has a given site, out of the non-trivial components. -/
  treeSite : ι → W
  treeSite_ne : ∀ i, ¬ (G.connectedComponentMk i).supp.Nontrivial → treeSite i ≠ ρ

namespace GlueData

variable {Vp Ep : Cent G → Type w} {P : ∀ C : Cent G, Network C.1.supp (Vp C) (Ep C)} {W : Type v} (D : GlueData P W)

/-- The nodes of the glued network: the non-central nodes of the tree, and the nodes of the networks. -/
abbrev Vtx : Type (max u v w) := {v : W // v ∉ Set.range D.center} ⊕ Σ C, Vp C

/-- The arcs of the glued network: the edges of the tree, by their lower ends, and the arcs of the networks. -/
abbrev Arcs : Type (max u v w) := {b : W // b ≠ D.ρ} ⊕ Σ C, Ep C

/-- Where an edge into `b` arrives. -/
def inNode (b : W) : D.Vtx :=
  if h : b ∈ Set.range D.center then .inr ⟨h.choose, (P h.choose).root⟩ else .inl ⟨b, h⟩

/-- Where the edge into `b` leaves from. -/
def outNode (b : W) : D.Vtx :=
  if h : D.par b ∈ Set.range D.center then .inr ⟨h.choose, D.exit h.choose b⟩ else .inl ⟨D.par b, h⟩

theorem inNode_center (C : Cent G) : D.inNode (D.center C) = .inr ⟨C, (P C).root⟩ := by
  have hex : D.center C ∈ Set.range D.center := ⟨C, rfl⟩
  have hC : hex.choose = C := D.center_inj hex.choose_spec
  rw [inNode, dite_eq_left hex, hC]

theorem inNode_of_not {b : W} (h : b ∉ Set.range D.center) : D.inNode b = .inl ⟨b, h⟩ := by
  rw [inNode, dite_eq_right h]

theorem outNode_center {C : Cent G} {b : W} (h : D.par b = D.center C) : D.outNode b = .inr ⟨C, D.exit C b⟩ := by
  have hex : D.par b ∈ Set.range D.center := ⟨C, h.symm⟩
  have hC : hex.choose = C := D.center_inj (hex.choose_spec.trans h)
  rw [outNode, dite_eq_left hex, hC]

theorem outNode_of_not {b : W} (h : D.par b ∉ Set.range D.center) : D.outNode b = .inl ⟨D.par b, h⟩ := by
  rw [outNode, dite_eq_right h]

/-- The source of an arc. -/
def arcSrc : D.Arcs → D.Vtx
  | .inl b => D.outNode b.1
  | .inr ⟨C, e⟩ => .inr ⟨C, (P C).src e⟩

/-- The target of an arc. -/
def arcTgt : D.Arcs → D.Vtx
  | .inl b => D.inNode b.1
  | .inr ⟨C, e⟩ => .inr ⟨C, (P C).tgt e⟩

/-- The label of a node. On the sites of `C`, a node of `P C` has its label in `P C`. On the other sites, it has the label of the central node. -/
def nodeLabel : D.Vtx → ι → Bool
  | .inl v, i => D.lam v.1 i
  | .inr ⟨C, x⟩, i => if h : i ∈ C.1.supp then (P C).label x ⟨i, h⟩ else D.lam (D.center C) i

/-- The arc of a site. -/
def siteArc (i : ι) : D.Arcs :=
  if h : (G.connectedComponentMk i).supp.Nontrivial then .inr ⟨⟨_, h⟩, (P ⟨_, h⟩).site ⟨i, rfl⟩⟩
  else .inl ⟨D.treeSite i, D.treeSite_ne i h⟩

/-- The labels at the two ends of the edges of the tree agree, but for the sites on them. -/
structure Valid : Prop where
  label_site : ∀ (b : W) (hb : b ≠ D.ρ) (i : ι), D.siteArc i = .inl ⟨b, hb⟩ → D.nodeLabel (D.inNode b) i = !D.nodeLabel (D.outNode b) i
  label_other : ∀ (b : W) (hb : b ≠ D.ρ) (i : ι), D.siteArc i ≠ .inl ⟨b, hb⟩ → D.nodeLabel (D.inNode b) i = D.nodeLabel (D.outNode b) i

variable {D}

theorem inr_fst {α : Type*} {F : Cent G → Type*} {C C' : Cent G} {x : F C} {y : F C'}
    (h : (Sum.inr ⟨C, x⟩ : α ⊕ Σ C, F C) = Sum.inr ⟨C', y⟩) : C = C' := by
  cases h
  rfl

theorem inr_snd {α : Type*} {F : Cent G → Type*} {C : Cent G} {x y : F C}
    (h : (Sum.inr ⟨C, x⟩ : α ⊕ Σ C, F C) = Sum.inr ⟨C, y⟩) : x = y := by
  cases h
  rfl

theorem inNode_eq_inr {b : W} {C : Cent G} {x : Vp C} (h : D.inNode b = .inr ⟨C, x⟩) : b = D.center C ∧ x = (P C).root := by
  by_cases hb : b ∈ Set.range D.center
  · obtain ⟨C', rfl⟩ := hb
    rw [D.inNode_center] at h
    obtain rfl := inr_fst h
    have h' := inr_snd h
    exact ⟨rfl, Eq.symm h'⟩
  · rw [D.inNode_of_not hb] at h
    simp at h

theorem inNode_inj {b b' : W} (h : D.inNode b = D.inNode b') : b = b' := by
  by_cases hb : b ∈ Set.range D.center
  · obtain ⟨C, rfl⟩ := hb
    rw [D.inNode_center] at h
    exact (inNode_eq_inr h.symm).1.symm
  · by_cases hb' : b' ∈ Set.range D.center
    · obtain ⟨C, rfl⟩ := hb'
      rw [D.inNode_center] at h
      exact (inNode_eq_inr h).1
    · rw [D.inNode_of_not hb, D.inNode_of_not hb'] at h
      simpa using h

theorem arcTgt_inl (b : {b : W // b ≠ D.ρ}) {f : D.Arcs} (h : D.arcTgt f = D.arcTgt (.inl b)) : f = .inl b := by
  cases f with
  | inl b' =>
    have : b'.1 = b.1 := inNode_inj h
    rw [Subtype.ext this]
  | inr f =>
    obtain ⟨C, f⟩ := f
    exfalso
    obtain ⟨-, h₂⟩ := inNode_eq_inr (D := D) (b := b.1) (C := C) (x := (P C).tgt f) (Eq.symm h)
    exact (P C).root_iff _ |>.2 h₂ f rfl

variable (D)

/-- The projection to the tree. -/
def toTree : D.Vtx → W
  | .inl v => v.1
  | .inr ⟨C, _⟩ => D.center C

theorem toTree_inNode (b : W) : D.toTree (D.inNode b) = b := by
  by_cases hb : b ∈ Set.range D.center
  · obtain ⟨C, rfl⟩ := hb
    rw [D.inNode_center]
    rfl
  · rw [D.inNode_of_not hb]
    rfl

theorem toTree_outNode (b : W) : D.toTree (D.outNode b) = D.par b := by
  by_cases hb : D.par b ∈ Set.range D.center
  · obtain ⟨C, hC⟩ := hb
    rw [D.outNode_center hC.symm]
    exact hC
  · rw [D.outNode_of_not hb]
    rfl

variable {D}

/-- An arc goes down in the tree, or stays within one of the networks. -/
theorem arc_cases {a c : D.Vtx} (h : ∃ e, D.arcSrc e = a ∧ D.arcTgt e = c) :
    D.depth (D.toTree a) < D.depth (D.toTree c) ∨ ∃ C x y, a = .inr ⟨C, x⟩ ∧ c = .inr ⟨C, y⟩ ∧ (P C).Arc x y := by
  obtain ⟨e, rfl, rfl⟩ := h
  cases e with
  | inl b =>
    left
    change D.depth (D.toTree (D.outNode b.1)) < D.depth (D.toTree (D.inNode b.1))
    rw [toTree_outNode, toTree_inNode]
    exact D.depth_par b.1 b.2
  | inr e =>
    obtain ⟨C, e⟩ := e
    right
    exact ⟨C, _, _, rfl, rfl, e, rfl, rfl⟩

theorem transGen_cases {a c : D.Vtx} (h : Relation.TransGen (fun a b => ∃ e, D.arcSrc e = a ∧ D.arcTgt e = b) a c) :
    D.depth (D.toTree a) < D.depth (D.toTree c) ∨ ∃ C x y, a = .inr ⟨C, x⟩ ∧ c = .inr ⟨C, y⟩ ∧ Relation.TransGen (P C).Arc x y := by
  induction h with
  | single h =>
    rcases arc_cases h with h' | ⟨C, x, y, rfl, rfl, hxy⟩
    · exact Or.inl h'
    · exact Or.inr ⟨C, x, y, rfl, rfl, Relation.TransGen.single hxy⟩
  | tail _ h ih =>
    rcases arc_cases h with h' | ⟨C, x, y, rfl, rfl, hxy⟩
    · rcases ih with h₁ | ⟨C, x, y, rfl, rfl, -⟩
      · exact Or.inl (h₁.trans h')
      · exact Or.inl h'
    · rcases ih with h₁ | ⟨C', x', y', rfl, hy', hxy'⟩
      · exact Or.inl h₁
      · obtain rfl := inr_fst hy'
        have h₂ := inr_snd hy'
        subst h₂
        exact Or.inr ⟨_, x', y, rfl, rfl, hxy'.tail hxy⟩

variable (D)

/-- The glued network. -/
def net (hD : D.Valid) : Network ι D.Vtx D.Arcs where
  src := D.arcSrc
  tgt := D.arcTgt
  root := .inl ⟨D.ρ, fun ⟨C, hC⟩ => D.center_ne C hC⟩
  site := D.siteArc
  label := D.nodeLabel
  simple e f h₁ h₂ := by
    cases e with
    | inl b => exact (arcTgt_inl b h₂.symm).symm
    | inr e =>
      cases f with
      | inl b => exact arcTgt_inl b h₂
      | inr f =>
        obtain ⟨C, e⟩ := e
        obtain ⟨C', f⟩ := f
        obtain rfl := inr_fst h₂
        have h₃ := inr_snd h₂
        have h₄ := inr_snd h₁
        rw [(P C).simple e f h₄ h₃]
  acyclic v hv := by
    rcases transGen_cases hv with h | ⟨C, x, y, rfl, hy, hxy⟩
    · exact lt_irrefl _ h
    · have h₂ := inr_snd hy
      have h₂' : x = y := h₂
      subst h₂'
      exact (P C).acyclic x hxy
  root_iff v := by
    constructor
    · intro hv
      cases v with
      | inl v =>
        by_cases hρ : v.1 = D.ρ
        · congr 1
          exact Subtype.ext hρ
        · refine absurd ?_ (hv (.inl ⟨v.1, hρ⟩))
          change D.inNode v.1 = _
          rw [D.inNode_of_not v.2]
      | inr v =>
        obtain ⟨C, x⟩ := v
        exfalso
        by_cases hx : x = (P C).root
        · subst hx
          refine hv (.inl ⟨D.center C, D.center_ne C⟩) ?_
          exact D.inNode_center C
        · have : ¬ ∀ e, (P C).tgt e ≠ x := fun h => hx (((P C).root_iff x).1 h)
          push Not at this
          obtain ⟨e, he⟩ := this
          exact hv (.inr ⟨C, e⟩) (by simp [arcTgt, he])
    · rintro rfl e he
      cases e with
      | inl b =>
        by_cases hb : b.1 ∈ Set.range D.center
        · obtain ⟨C, hC⟩ := hb
          have : D.arcTgt (.inl b) = .inr ⟨C, (P C).root⟩ := by
            change D.inNode b.1 = _
            rw [← hC, D.inNode_center]
          rw [this] at he
          simp at he
        · have : D.arcTgt (.inl b) = .inl ⟨b.1, hb⟩ := D.inNode_of_not hb
          rw [this] at he
          simp only [Sum.inl.injEq, Subtype.mk.injEq] at he
          exact b.2 he
      | inr e =>
        obtain ⟨C, e⟩ := e
        simp [arcTgt] at he
  inDegree_le_two e f g h₁ h₂ := by
    cases e with
    | inl b => exact Or.inl (arcTgt_inl b h₁.symm).symm
    | inr e =>
      cases f with
      | inl b => exact Or.inl (arcTgt_inl b h₁)
      | inr f =>
        cases g with
        | inl b => exact Or.inr (Or.inr (arcTgt_inl b h₂))
        | inr g =>
          obtain ⟨C, e⟩ := e
          obtain ⟨C₁, f⟩ := f
          obtain ⟨C₂, g⟩ := g
          obtain rfl := inr_fst h₁
          have h₃ := inr_snd h₁
          obtain rfl := inr_fst h₂
          have h₄ := inr_snd h₂
          rcases (P C).inDegree_le_two e f g h₃ h₄ with h | h | h
          · exact Or.inl (by rw [h])
          · exact Or.inr (Or.inl (by rw [h]))
          · exact Or.inr (Or.inr (by rw [h]))
  site_not_recomb i f hf := by
    unfold siteArc at hf ⊢
    split_ifs at hf ⊢ with h
    · cases f with
      | inl b => exact arcTgt_inl b hf.symm |>.symm
      | inr f =>
        obtain ⟨C, f⟩ := f
        obtain rfl := inr_fst hf
        have h₃ := inr_snd hf
        rw [(P _).site_not_recomb _ f h₃]
    · exact arcTgt_inl _ hf
  label_tree e he i := by
    cases e with
    | inl b =>
      by_cases hs : D.siteArc i = .inl b
      · rw [ite_eq_left hs]
        exact hD.label_site b.1 b.2 i hs
      · rw [ite_eq_right hs]
        exact hD.label_other b.1 b.2 i hs
    | inr e =>
      obtain ⟨C, e⟩ := e
      have hu : ∀ f, (P C).tgt f = (P C).tgt e → f = e := fun f hf => by
        have := he (.inr ⟨C, f⟩) (by simp [arcTgt, hf])
        have h₃ := inr_snd this
        exact h₃
      by_cases hi : i ∈ C.1.supp
      · have hl := (P C).label_tree e hu ⟨i, hi⟩
        have hsite : D.siteArc i = .inr ⟨C, (P C).site ⟨i, hi⟩⟩ := by
          obtain ⟨c, hc⟩ := C
          obtain rfl : G.connectedComponentMk i = c := hi
          unfold siteArc
          rw [dite_eq_left hc]
        have hiff : D.siteArc i = .inr ⟨C, e⟩ ↔ (P C).site ⟨i, hi⟩ = e := by
          rw [hsite]
          constructor
          · intro h
            have h₃ := inr_snd h
            exact h₃
          · intro h
            rw [h]
        simp only [hiff, arcTgt, arcSrc, nodeLabel, hi, ↓reduceDIte]
        exact hl
      · have hne : D.siteArc i ≠ .inr ⟨C, e⟩ := by
          intro h
          unfold siteArc at h
          split_ifs at h with h₁
          obtain rfl := inr_fst h
          exact hi rfl
        simp only [hne, arcTgt, arcSrc, nodeLabel, hi, ↓reduceDIte, ↓reduceIte]
  label_recomb e f hne ht i := by
    cases e with
    | inl b => exact absurd (arcTgt_inl b ht.symm).symm hne
    | inr e =>
      cases f with
      | inl b => exact absurd (arcTgt_inl b ht) hne
      | inr f =>
        obtain ⟨C, e⟩ := e
        obtain ⟨C', f⟩ := f
        obtain rfl := inr_fst ht
        have h₃ := inr_snd ht
        by_cases hi : i ∈ C.1.supp
        · have := (P C).label_recomb e f (fun h => hne (by rw [h])) h₃ ⟨i, hi⟩
          simpa only [arcTgt, arcSrc, nodeLabel, hi, ↓reduceDIte] using this
        · left
          simp only [arcTgt, arcSrc, nodeLabel, hi, ↓reduceDIte]

variable {D} (hD : D.Valid)

include hD

theorem isRecomb_net {x : D.Vtx} : (D.net hD).IsRecomb x ↔ ∃ C y, x = .inr ⟨C, y⟩ ∧ (P C).IsRecomb y := by
  constructor
  · rintro ⟨e, f, hne, rfl, hf⟩
    change D.arcTgt f = D.arcTgt e at hf
    cases e with
    | inl b => exact absurd (arcTgt_inl b hf).symm hne
    | inr e =>
      cases f with
      | inl b => exact absurd (arcTgt_inl b hf.symm) hne
      | inr f =>
        obtain ⟨C, e⟩ := e
        obtain ⟨C', f⟩ := f
        obtain rfl := inr_fst hf
        have h₃ := inr_snd hf
        refine ⟨C', _, rfl, e, f, fun h => hne (by rw [h]), rfl, h₃⟩
  · rintro ⟨C, y, rfl, e, f, hne, rfl, hf⟩
    refine ⟨.inr ⟨C, e⟩, .inr ⟨C, f⟩, fun h => hne ?_, rfl, ?_⟩
    · have h₃ := inr_snd h
      exact h₃
    · change (Sum.inr ⟨C, (P C).tgt f⟩ : D.Vtx) = _
      rw [hf]

theorem net_obeys [LinearOrder ι] {c : Crossover} (hP : ∀ C, (P C).Obeys c) : (D.net hD).Obeys c := by
  cases c with
  | single =>
    intro x hx
    obtain ⟨C, y, rfl, hy⟩ := (isRecomb_net hD).1 hx
    obtain ⟨e, f, hne, rfl, hf, L₀, hl⟩ := hP C y hy
    refine ⟨.inr ⟨C, e⟩, .inr ⟨C, f⟩, fun h => hne ?_, rfl, ?_, ⟨{i | ∃ j : C.1.supp, j ∈ L₀ ∧ i ≤ j.1}, ?_⟩, fun i => ?_⟩
    · have h₃ := inr_snd h
      exact h₃
    · change (Sum.inr ⟨C, (P C).tgt f⟩ : D.Vtx) = _
      rw [hf]
    · rintro a b hba ⟨j, hj, haj⟩
      exact ⟨j, hj, hba.trans haj⟩
    · by_cases hi : i ∈ C.1.supp
      · have hmem : i ∈ (⟨{i | ∃ j : C.1.supp, j ∈ L₀ ∧ i ≤ j.1}, by
            rintro a b hba ⟨j, hj, haj⟩
            exact ⟨j, hj, hba.trans haj⟩⟩ : LowerSet ι) ↔ (⟨i, hi⟩ : C.1.supp) ∈ L₀ := by
          constructor
          · rintro ⟨j, hj, hij⟩
            exact L₀.lower (show (⟨i, hi⟩ : C.1.supp) ≤ j from hij) hj
          · intro h
            exact ⟨⟨i, hi⟩, h, le_rfl⟩
        have h₀ := hl ⟨i, hi⟩
        by_cases h₁ : (⟨i, hi⟩ : C.1.supp) ∈ L₀
        · rw [ite_eq_left h₁] at h₀
          rw [ite_eq_left (hmem.2 h₁)]
          simpa only [net, arcTgt, arcSrc, nodeLabel, hi, ↓reduceDIte] using h₀
        · rw [ite_eq_right h₁] at h₀
          rw [ite_eq_right (fun h => h₁ (hmem.1 h))]
          simpa only [net, arcTgt, arcSrc, nodeLabel, hi, ↓reduceDIte] using h₀
      · simp only [net, arcSrc, nodeLabel, hi, ↓reduceDIte, ite_self]
  | multiple => trivial
  | pointwise =>
    intro x hx
    obtain ⟨C, y, rfl, hy⟩ := (isRecomb_net hD).1 hx
    obtain ⟨e, f, hne, rfl, hf, j, hl⟩ := hP C y hy
    refine ⟨.inr ⟨C, e⟩, .inr ⟨C, f⟩, fun h => hne ?_, rfl, ?_, j.1, fun i => ?_⟩
    · have h₃ := inr_snd h
      exact h₃
    · change (Sum.inr ⟨C, (P C).tgt f⟩ : D.Vtx) = _
      rw [hf]
    · by_cases hi : i ∈ C.1.supp
      · have h₀ := hl ⟨i, hi⟩
        by_cases h₁ : (⟨i, hi⟩ : C.1.supp) = j
        · rw [ite_eq_left h₁] at h₀
          rw [ite_eq_left (congrArg Subtype.val h₁)]
          simpa only [net, arcTgt, arcSrc, nodeLabel, hi, ↓reduceDIte] using h₀
        · rw [ite_eq_right h₁] at h₀
          rw [ite_eq_right (fun h => h₁ (Subtype.ext h))]
          simpa only [net, arcTgt, arcSrc, nodeLabel, hi, ↓reduceDIte] using h₀
      · simp only [net, arcSrc, nodeLabel, hi, ↓reduceDIte, ite_self]

theorem net_recombCount [Fintype (Cent G)] [∀ C, Finite (Vp C)] : (D.net hD).recombCount = ∑ C, (P C).recombCount := by
  have hbij : Function.Bijective (fun y : Σ C, {x // (P C).IsRecomb x} =>
      (⟨.inr ⟨y.1, y.2.1⟩, (isRecomb_net hD).2 ⟨y.1, y.2.1, rfl, y.2.2⟩⟩ : {x // (D.net hD).IsRecomb x})) := by
    constructor
    · rintro ⟨C, y, hy⟩ ⟨C', y', hy'⟩ hab
      have := congrArg (fun z : {x // (D.net hD).IsRecomb x} => z.1) hab
      obtain rfl := inr_fst this
      have h₃ := inr_snd this
      have h₃' : y = y' := h₃
      subst h₃'
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨C, y, rfl, hy⟩ := (isRecomb_net hD).1 hx
      exact ⟨⟨C, y, hy⟩, rfl⟩
  have h₁ := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Network.recombCount, ← h₁, Nat.card_sigma]
  rfl

theorem isLeaf_net_inl (v : {v : W // v ∉ Set.range D.center}) :
    (D.net hD).IsLeaf (.inl v) ↔ ∀ b, b ≠ D.ρ → D.par b ≠ v.1 := by
  constructor
  · intro h b hb hpar
    refine h (.inl ⟨b, hb⟩) ?_
    change D.outNode b = _
    have : D.par b ∉ Set.range D.center := hpar ▸ v.2
    rw [D.outNode_of_not this]
    congr 1
    exact Subtype.ext hpar
  · intro h e he
    cases e with
    | inl b =>
      refine h b.1 b.2 ?_
      have h₁ := congrArg D.toTree he
      change D.toTree (D.outNode b.1) = v.1 at h₁
      rwa [toTree_outNode] at h₁
    | inr e =>
      obtain ⟨C, e⟩ := e
      simp [net, arcSrc] at he

theorem isLeaf_net_inr {C : Cent G} {x : Vp C} (hx : (D.net hD).IsLeaf (.inr ⟨C, x⟩)) : (P C).IsLeaf x ∧
    ∀ b, b ≠ D.ρ → D.par b = D.center C → D.exit C b ≠ x := by
  refine ⟨fun e he => hx (.inr ⟨C, e⟩) (by simp [net, arcSrc, he]), fun b hb hpar hex => ?_⟩
  refine hx (.inl ⟨b, hb⟩) ?_
  change D.outNode b = _
  rw [D.outNode_center hpar, hex]

/-- The embedding of a network `P C`. -/
theorem emb_piece (C : Cent G) : Network.Emb (P C) (D.net hD) (fun x => .inr ⟨C, x⟩) (fun e => .inr ⟨C, e⟩) where
  f_inj a b hab := by
    have h₃ := inr_snd hab
    exact h₃
  g_inj a b hab := by
    have h₃ := inr_snd hab
    exact h₃
  src _ := rfl
  tgt _ := rfl

/-- The arcs of the tree aren't on a recombination cycle. -/
theorem not_mem_cycle_inl {w x : D.Vtx} {p q : List D.Arcs} (hc : (D.net hD).IsCycleOn w x p q) (b : {b : W // b ≠ D.ρ}) :
    Sum.inl b ∉ p ∧ Sum.inl b ∉ q := by
  obtain ⟨hrec, hp, hq, -, hd⟩ := id hc
  -- `y` is below `b` in the tree.
  let Bel : W → Prop := Relation.ReflTransGen (fun a c => c ≠ D.ρ ∧ a = D.par c) b.1
  let Below : D.Vtx → Prop := fun y => Bel (D.toTree y)
  have hdepth : ∀ {y}, Bel y → D.depth b.1 ≤ D.depth y := by
    intro y hy
    induction hy with
    | refl => exact le_rfl
    | tail _ h ih =>
      obtain ⟨h₁, rfl⟩ := h
      exact ih.trans (D.depth_par _ h₁).le
  have hclosed : ∀ e, Below (D.arcSrc e) → Below (D.arcTgt e) := by
    intro e he
    cases e with
    | inl c =>
      change Bel (D.toTree (D.inNode c.1))
      rw [toTree_inNode]
      have h₁ : Bel (D.toTree (D.outNode c.1)) := he
      rw [toTree_outNode] at h₁
      exact h₁.tail ⟨c.2, rfl⟩
    | inr e =>
      obtain ⟨C, e⟩ := e
      exact he
  have hreach : ∀ {l : List D.Arcs} {u v : D.Vtx}, (D.net hD).IsPath u v l → Below u → Below v := by
    intro l
    induction l with
    | nil =>
      intro u v h hu
      rwa [← show u = v from h]
    | cons a t ih =>
      rintro u v ⟨h₁, h₂⟩ hu
      have h₃ : D.arcSrc a = u := h₁
      exact ih h₂ (hclosed a (by rw [h₃]; exact hu))
  have hentry : ∀ {l : List D.Arcs} {u v : D.Vtx}, (D.net hD).IsPath u v l → ¬ Below u → Below v → Sum.inl b ∈ l := by
    intro l
    induction l with
    | nil =>
      intro u v h hu hv
      have h' : u = v := h
      rw [← h'] at hv
      exact absurd hv hu
    | cons a t ih =>
      rintro u v ⟨h₁, h₂⟩ hu hv
      by_cases hta : Below ((D.net hD).tgt a)
      · have h₃ : D.arcSrc a = u := h₁
        have hs : ¬ Below (D.arcSrc a) := by
          rw [h₃]
          exact hu
        cases a with
        | inl c =>
          have h₃ : Bel (D.toTree (D.inNode c.1)) := hta
          rw [toTree_inNode] at h₃
          have h₄ : ¬ Bel (D.toTree (D.outNode c.1)) := hs
          rw [toTree_outNode] at h₄
          cases Relation.ReflTransGen.cases_tail h₃ with
          | inl h₅ =>
            have : c = b := Subtype.ext h₅
            rw [this]
            exact List.mem_cons_self
          | inr h₅ =>
            obtain ⟨a', ha', h₆, rfl⟩ := h₅
            exact absurd ha' h₄
        | inr e =>
          obtain ⟨C, e⟩ := e
          exact absurd hta hs
      · exact List.mem_cons_of_mem _ (ih h₂ hta hv)
  have hnotout : ¬ Below (D.outNode b.1) := by
    intro h₁
    change Bel (D.toTree (D.outNode b.1)) at h₁
    rw [toTree_outNode] at h₁
    have := hdepth h₁
    have := D.depth_par b.1 b.2
    omega
  have hin : Below (D.inNode b.1) := by
    change Bel (D.toTree (D.inNode b.1))
    rw [toTree_inNode]
  have hnotrec : ¬ (D.net hD).IsRecomb (D.inNode b.1) := by
    rintro ⟨e, f, hne, h₁, h₂⟩
    have h₃ := arcTgt_inl (D := D) b (f := e) h₁
    have h₄ := arcTgt_inl (D := D) b (f := f) h₂
    exact hne (h₃.trans h₄.symm)
  -- On one path, then on the other, and so their common target is the recombination node.
  have key : ∀ {l l' : List D.Arcs}, (D.net hD).IsPath w x l → (D.net hD).IsPath w x l' → Sum.inl b ∈ l → Sum.inl b ∈ l' := by
    intro l l' hl hl' hb
    have h₁ := hl.reach_src_of_mem hb
    have h₂ := hl.reach_tgt_of_mem hb
    -- The path `h₂`, from the target of the arc, shows that `x` is below `b`.
    obtain ⟨t₂, ht₂⟩ := h₂.exists_isPath
    have hxb : Below x := hreach ht₂ hin
    have hwb : ¬ Below w := fun hw => by
      obtain ⟨t₁, ht₁⟩ := h₁.exists_isPath
      exact hnotout (hreach ht₁ hw)
    exact hentry hl' hwb hxb
  constructor
  · intro hb
    have hbq := key hp hq hb
    have hx := hd _ hb _ hbq rfl
    have hrec' := hrec
    rw [← hx] at hrec'
    exact hnotrec hrec'
  · intro hb
    have hbp := key hq hp hb
    have hx := hd _ hbp _ hb rfl
    have hrec' := hrec
    rw [← hx] at hrec'
    exact hnotrec hrec'

/-- A recombination cycle of the glued network is a recombination cycle of one of the networks. -/
theorem cycle_piece {Q' : Set D.Arcs} (hQ' : (D.net hD).IsCycle Q') :
    ∃ C Q, (P C).IsCycle Q ∧ Q' = (fun e => (.inr ⟨C, e⟩ : D.Arcs)) '' Q := by
  obtain ⟨w, x, p, q, hc, hQeq⟩ := id hQ'
  obtain ⟨hrec, hp, hq, hpq, -⟩ := id hc
  obtain ⟨hinlp, hinlq⟩ : (∀ b, Sum.inl b ∉ p) ∧ ∀ b, Sum.inl b ∉ q :=
    ⟨fun b => (not_mem_cycle_inl hD hc b).1, fun b => (not_mem_cycle_inl hD hc b).2⟩
  have hstay : ∀ {l : List D.Arcs} {C : Cent G} {u : Vp C} {v : D.Vtx}, (D.net hD).IsPath (.inr ⟨C, u⟩) v l → (∀ b, Sum.inl b ∉ l) →
      ∀ a ∈ l, a ∈ Set.range (fun e => (.inr ⟨C, e⟩ : D.Arcs)) := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
      rintro C u v ⟨h₁, h₂⟩ hb a' ha'
      cases a with
      | inl c => exact absurd List.mem_cons_self (hb c)
      | inr e =>
        obtain ⟨C', e⟩ := e
        obtain rfl := inr_fst h₁
        rcases List.mem_cons.1 ha' with rfl | ha'
        · exact ⟨e, rfl⟩
        · exact ih h₂ (fun c hc' => hb c (List.mem_cons_of_mem _ hc')) a' ha'
  -- The first arc is in a network.
  obtain ⟨C, u, rfl⟩ : ∃ C u, w = .inr ⟨C, u⟩ := by
    cases p with
    | cons a t =>
      cases a with
      | inl c => exact absurd List.mem_cons_self (hinlp c)
      | inr e =>
        obtain ⟨C, e⟩ := e
        exact ⟨C, _, Eq.symm hp.1⟩
    | nil =>
      cases q with
      | cons a t =>
        cases a with
        | inl c => exact absurd List.mem_cons_self (hinlq c)
        | inr e =>
          obtain ⟨C, e⟩ := e
          exact ⟨C, _, Eq.symm hq.1⟩
      | nil => exact absurd rfl hpq
  obtain ⟨Q, hQ, hQ₂⟩ := (emb_piece hD C).cycle_back (fun y hy => by
      obtain ⟨C', y', hy', hr⟩ := (isRecomb_net hD).1 hy
      obtain rfl := inr_fst hy'
      have h₃ := inr_snd hy'
      rwa [h₃]) hQ' (by
    rw [hQeq]
    rintro a (ha | ha)
    · exact hstay hp hinlp a ha
    · exact hstay hq hinlq a ha)
  exact ⟨C, Q, hQ, hQ₂⟩

/-- The glued network is fully decomposed, when each network has one blob with all its sites. -/
theorem net_fullyDecomposed (hP : ∀ C, (∃! B, (P C).IsBlob B) ∧ ∀ i, ∃ B, (P C).IsBlob B ∧ (P C).site i ∈ B) :
    (D.net hD).IsFullyDecomposedFor G := by
  have hback : ∀ (C : Cent G) (Q' : Set D.Arcs), (D.net hD).IsCycle Q' →
      (∃ e ∈ Q', e ∈ Set.range (fun e => (.inr ⟨C, e⟩ : D.Arcs))) → ∃ Q, (P C).IsCycle Q ∧ Q' = (fun e => (.inr ⟨C, e⟩ : D.Arcs)) '' Q := by
    intro C Q' hQ' hex
    obtain ⟨C', Q, hQ, rfl⟩ := cycle_piece hD hQ'
    obtain ⟨a, ⟨e, -, ha⟩, ⟨e', he'⟩⟩ := hex
    have hh : (Sum.inr ⟨C, e'⟩ : D.Arcs) = Sum.inr ⟨C', e⟩ := he'.trans ha.symm
    obtain rfl := inr_fst hh
    exact ⟨Q, hQ, rfl⟩
  -- A blob of the glued network is the image of the blob of one of the networks.
  have hblob : ∀ {B'}, (D.net hD).IsBlob B' → ∃ C B, (P C).IsBlob B ∧ B' = (fun e => (.inr ⟨C, e⟩ : D.Arcs)) '' B := by
    rintro B' ⟨Q', hQ', rfl⟩
    obtain ⟨C, Q, hQ, rfl⟩ := cycle_piece hD hQ'
    exact ⟨C, _, ⟨Q, hQ, rfl⟩, (emb_piece hD C).blob_image (hback C) hQ⟩
  have hsite : ∀ (C : Cent G) (i : ι) (hi : i ∈ C.1.supp), D.siteArc i = .inr ⟨C, (P C).site ⟨i, hi⟩⟩ := by
    rintro ⟨c, hc⟩ i hi
    obtain rfl : G.connectedComponentMk i = c := hi
    unfold siteArc
    rw [dite_eq_left hc]
  have hsite' : ∀ {C : Cent G} {i : ι} {e : Ep C}, D.siteArc i = .inr ⟨C, e⟩ → i ∈ C.1.supp := by
    intro C i e h
    unfold siteArc at h
    split_ifs at h with h₁
    obtain rfl := inr_fst h
    rfl
  have hverts : ∀ (C : Cent G) (B : Set (Ep C)) (v : D.Vtx), v ∈ (D.net hD).blobVerts ((fun e => (.inr ⟨C, e⟩ : D.Arcs)) '' B) →
      ∃ y : Vp C, v = .inr ⟨C, y⟩ := by
    rintro C B v (⟨a, ⟨e, -, rfl⟩, rfl⟩ | ⟨a, ⟨e, -, rfl⟩, rfl⟩)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  refine ⟨fun B' hB' => ?_, fun i hi => ?_, fun B₁ B₂ h₁ h₂ hne => ?_⟩
  · obtain ⟨C, B, hB, rfl⟩ := hblob hB'
    refine ⟨C.1, C.2, fun i => ?_⟩
    constructor
    · rintro ⟨e, -, heq⟩
      exact hsite' heq.symm
    · intro hi
      obtain ⟨⟨B₀, hB₀, huniq⟩, hall⟩ := hP C
      obtain ⟨B₁, hB₁, hs⟩ := hall ⟨i, hi⟩
      rw [huniq B hB, ← huniq B₁ hB₁]
      exact ⟨_, hs, (hsite C i hi).symm⟩
  · -- A site alone in its component is on an edge of the tree.
    have hnt : ¬ (G.connectedComponentMk i).supp.Nontrivial := by
      rintro ⟨a, ha, b, hb, hab⟩
      have hr : ∀ j, j ∈ (G.connectedComponentMk i).supp → j = i := by
        intro j hj
        by_contra hji
        have hreach : G.Reachable j i := SimpleGraph.ConnectedComponent.eq.1 hj
        obtain ⟨p⟩ := SimpleGraph.Reachable.symm hreach
        cases p with
        | nil => exact hji rfl
        | cons h _ => exact hi _ h
      exact hab ((hr a ha).trans (hr b hb).symm)
    rintro ⟨Q', hQ', hmem⟩
    obtain ⟨w, x, p, q, hc, rfl⟩ := id hQ'
    have hs : (D.net hD).site i = .inl ⟨D.treeSite i, D.treeSite_ne i hnt⟩ := by
      change D.siteArc i = _
      unfold siteArc
      rw [dite_eq_right hnt]
    rw [hs] at hmem
    obtain ⟨h₁, h₂⟩ := not_mem_cycle_inl hD hc ⟨D.treeSite i, D.treeSite_ne i hnt⟩
    rcases hmem with h | h
    · exact h₁ h
    · exact h₂ h
  · obtain ⟨C, B, hB, rfl⟩ := hblob h₁
    obtain ⟨C', B', hB', rfl⟩ := hblob h₂
    by_cases hCC : C = C'
    · subst hCC
      obtain ⟨⟨B₀, -, huniq⟩, -⟩ := hP C
      exact absurd (by rw [huniq B hB, huniq B' hB']) hne
    · rw [Set.disjoint_left]
      intro v hv hv'
      obtain ⟨y, rfl⟩ := hverts C B v hv
      obtain ⟨y', hy'⟩ := hverts C' B' _ hv'
      have h₃ := inr_fst hy'
      exact hCC h₃

end GlueData

end Decomp

end Gusfield2007
