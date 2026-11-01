module

public import Gusfield2007.Realizability
public import Gusfield2007.SameCycles

/-!
# Gusfield et al. 2007: line 299 with the root at any node of `T̄`

Line 299: "we arbitrarily select a node `v_r` of `T̄` to be the root and direct all the edges in `T̄` away from that chosen root." `Gusfield2007.TBarFrame` selects a row, and `exists_realization` the neighbour of a row. Here it's any node (`exists_network_rooted_at`): the network has `T′ = T̄`, with its root at the selected node, and so it has all that `theorem4_entry` asks for.

* If the node isn't a row, it's as in line 299. If it's the central node of `C`, the root is the root of the network of `C`. Line 299 says that "`S(C)` is the ancestral sequence of `v_r = v_C`", and line 416 that "the label on `v` can be used": but the node `v_C` is on the `0`-side of every character from `C`, by Lemma 4, so the labels of `T̄` give no sequence on `C`. Any sequence can be used, so that `S₀` is a parameter, and the network of `C` then derives all the super-characters of `C`.
* If the node is a row `S`, the row is at the root, so it has no leaf: the network derives the other rows (`exists_network_rooted_at_row`). A network deriving all the rows can't have its root at a row and `T′ = T̄` (`root_not_mem_range`).

The construction adds a node above the selected node, which makes it the data for `GlueData` in the same way for all the nodes, and removes it at the end (`Network.dropRoot`).
-/

@[expose] public noncomputable section

open scoped Classical

namespace Gusfield2007

universe u v w

/-! ### Removing the root -/

namespace Network

variable {ι : Type u} {V E : Type*}

/-- The root has one arc out of it, with no site, and that arc is the only arc into its target. -/
structure DropCond (N : Network ι V E) (a : E) : Prop extends N.RerootCond a where
  no_site : ∀ i, N.site i ≠ a

variable [Finite V]

/-- The network without its root and the arc out of it. -/
def dropRoot (N : Network ι V E) (a : E) (ha : N.DropCond a) : Network ι {v // v ≠ N.root} {e // e ≠ a} where
  src e := ⟨N.src e.1, fun h => e.2 (ha.uniq_out e.1 h)⟩
  tgt e := ⟨N.tgt e.1, N.tgt_ne_root e.1⟩
  root := ⟨N.tgt a, N.tgt_ne_root a⟩
  site i := ⟨N.site i, ha.no_site i⟩
  label v := N.label v.1
  simple e f h₁ h₂ := Subtype.ext (N.simple e.1 f.1 (congrArg Subtype.val h₁) (congrArg Subtype.val h₂))
  acyclic := by
    obtain ⟨ρ, hρ⟩ := N.exists_rank
    exact acyclic_of_rank (fun v => ρ v.1) fun e => hρ e.1
  root_iff v := by
    constructor
    · intro h
      have hex : ∃ g, N.tgt g = v.1 := by
        by_contra hno
        push Not at hno
        exact v.2 ((N.root_iff v.1).1 hno)
      obtain ⟨g, hg⟩ := hex
      by_cases hga : g = a
      · exact Subtype.ext (by rw [← hg, hga])
      · exact absurd (Subtype.ext hg) (h ⟨g, hga⟩)
    · rintro rfl e he
      exact e.2 (ha.uniq_in e.1 (congrArg Subtype.val he))
  inDegree_le_two e f g h₁ h₂ := by
    rcases N.inDegree_le_two e.1 f.1 g.1 (congrArg Subtype.val h₁) (congrArg Subtype.val h₂) with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  site_not_recomb i f h := Subtype.ext (N.site_not_recomb i f.1 (congrArg Subtype.val h))
  label_tree e he i := by
    have huniq : ∀ f, N.tgt f = N.tgt e.1 → f = e.1 := fun f hf => by
      have hfa : f ≠ a := fun h' => e.2 (ha.uniq_in e.1 (by rw [← hf, h']))
      exact congrArg Subtype.val (he ⟨f, hfa⟩ (Subtype.ext hf))
    have := N.label_tree e.1 huniq i
    simp only [Subtype.ext_iff]
    exact this
  label_recomb e f hef h i := N.label_recomb e.1 f.1 (fun h' => hef (Subtype.ext h')) (congrArg Subtype.val h) i

variable {N : Network ι V E} {a : E}

/-- **The cycles of `N` are those of `dropRoot`.** -/
theorem dropRoot_sameCycles (ha : N.DropCond a) : SameCycles (N.dropRoot a ha) N Subtype.val Subtype.val where
  f_inj := Subtype.val_injective
  g_inj := Subtype.val_injective
  src _ _ := rfl
  tgt _ _ := rfl
  recomb e' h' hne ht := by
    have he : e' ≠ a := fun h => hne (by rw [h, ha.uniq_in h' (by rw [← ht, h])])
    have hh : h' ≠ a := fun h => hne (by rw [h, ha.uniq_in e' (by rw [ht, h])])
    exact ⟨⟨e', he⟩, ⟨h', hh⟩, fun h => hne (congrArg Subtype.val h), Subtype.ext ht, rfl, rfl⟩

theorem dropRoot_isLeaf (ha : N.DropCond a) (v : {v // v ≠ N.root}) : (N.dropRoot a ha).IsLeaf v ↔ N.IsLeaf v.1 := by
  constructor
  · intro h e he
    have hea : e ≠ a := fun h' => v.2 (by rw [← he, h', ha.src_root])
    exact h ⟨e, hea⟩ (Subtype.ext he)
  · intro h e he
    exact h e.1 (congrArg Subtype.val he)

theorem dropRoot_derives (ha : N.DropCond a) {M : Finset (ι → Bool)} (hd : N.Derives M) : (N.dropRoot a ha).Derives M := by
  have hroot : ¬ N.IsLeaf N.root := fun h => h a ha.src_root
  refine ⟨fun v hv => hd.mapsTo ((dropRoot_isLeaf ha v).1 hv), fun u hu v hv huv => Subtype.ext (hd.injOn ((dropRoot_isLeaf ha u).1 hu) ((dropRoot_isLeaf ha v).1 hv) huv), fun r hr => ?_⟩
  obtain ⟨l, hl, rfl⟩ := hd.surjOn hr
  have hne : l ≠ N.root := fun h => hroot (h ▸ hl)
  exact ⟨⟨l, hne⟩, (dropRoot_isLeaf ha _).2 hl, rfl⟩

theorem dropRoot_ancestral (ha : N.DropCond a) : (N.dropRoot a ha).ancestral = N.ancestral := by
  funext i
  have := N.label_tree a ha.uniq_in i
  rw [ha.src_root, ite_eq_right (ha.no_site i)] at this
  exact this

end Network

/-- `N` obeys the crossover models of `N'`, if the labels agree on the nodes that correspond. -/
theorem Network.SameCycles.obeys_back {ι : Type u} [LinearOrder ι] {V E V' E' : Type*} [Finite V] {N : Network ι V E} {N' : Network ι V' E'} {f : V → V'} {g : E → E'} (h : Network.SameCycles N N' f g)
    (hl : ∀ x, N'.label (f x) = N.label x) {c : Crossover} (hc : N'.Obeys c) : N.Obeys c := by
  have key : ∀ {x : V} {e' h' : E'}, e' ≠ h' → N'.tgt e' = f x → N'.tgt h' = f x → ∃ e l, e ≠ l ∧ N.tgt e = x ∧ N.tgt l = x ∧ N'.src e' = f (N.src e) ∧ N'.src h' = f (N.src l) := by
    intro x e' h' hne h₁ h₂
    obtain ⟨e, l, hel, htt, rfl, rfl⟩ := h.recomb e' h' hne (h₁.trans h₂.symm)
    have he := Network.onCycle_of_tgt_eq hel htt
    have hl' := Network.onCycle_of_tgt_eq hel.symm htt.symm
    rw [h.tgt e he] at h₁
    rw [h.tgt l hl'] at h₂
    exact ⟨e, l, hel, h.f_inj h₁, h.f_inj h₂, h.src e he, h.src l hl'⟩
  cases c with
  | single =>
    intro x hx
    obtain ⟨e', h', hne, h₁, h₂, L, hL⟩ := hc (f x) (h.isRecomb_image hx)
    obtain ⟨e, l, hel, he, hl', hs₁, hs₂⟩ := key hne h₁ h₂
    refine ⟨e, l, hel, he, hl', L, fun i => ?_⟩
    have := hL i
    rw [hs₁, hs₂, hl, hl, hl] at this
    exact this
  | multiple => trivial
  | pointwise =>
    intro x hx
    obtain ⟨e', h', hne, h₁, h₂, j, hL⟩ := hc (f x) (h.isRecomb_image hx)
    obtain ⟨e, l, hel, he, hl', hs₁, hs₂⟩ := key hne h₁ h₂
    refine ⟨e, l, hel, he, hl', j, fun i => ?_⟩
    have := hL i
    rw [hs₁, hs₂, hl, hl, hl] at this
    exact this

/-! ### `T̄` with its root at a node -/

variable {ι : Type u} {M : Finset (ι → Bool)} {W : Type v} [Finite W] {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W}

namespace IsTBar

variable (h : IsTBar M T φ edge)

open Decomp

/-- The label of the root, when the root is at the node `ρ`: the label of `ρ` in `T̄`, and `S₀` on the sites of the component of which `ρ` is the central node. -/
def rootLabel (ρ : W) (S₀ : ι → Bool) (i : ι) : Bool :=
  if ∃ C : Cent (incompatGraph M), h.center C.1 = ρ ∧ i ∈ C.1.supp then S₀ i else h.lam ρ i

/-- What the network of a central node has to derive: all the super-characters, for the central node at the root, and otherwise all but the one on the side of the root. -/
def pieceRows (ρ : W) (S₀ : ι → Bool) (C : Cent (incompatGraph M)) : Finset (C.1.supp → Bool) :=
  if h.center C.1 = ρ then restrictRows C.1.supp M else (restrictRows C.1.supp M).erase (C.1.supp.domRestrict (h.rootLabel ρ S₀))

variable {ρ : W} {S₀ : ι → Bool}

theorem pieceRows_subset (C : Cent (incompatGraph M)) : h.pieceRows ρ S₀ C ⊆ restrictRows C.1.supp M := by
  unfold pieceRows
  split_ifs
  · exact subset_rfl
  · exact Finset.erase_subset _ _

/-- The label of the root is the label of `ρ` in `T̄`, for a node that isn't central: "let `S` be the label written at node `v_r`" (line 299). -/
theorem rootLabel_eq_lam (hρ : ∀ C : Cent (incompatGraph M), h.center C.1 ≠ ρ) : h.rootLabel ρ S₀ = h.lam ρ := by
  funext i
  unfold rootLabel
  rw [ite_eq_right]
  rintro ⟨C, h₁, -⟩
  exact hρ C h₁

/-- A character whose 1-side has the root gives the label of the root. -/
theorem rootLabel_eq_valueAt {C : Cent (incompatGraph M)} {k : SuperChar M} (hk : k.1 = C.1) (hv : h.side k ρ = true) {i : ι} (hi : i ∈ C.1.supp) :
    h.rootLabel ρ S₀ i = valueAt k i := by
  have hno : ¬ ∃ C' : Cent (incompatGraph M), h.center C'.1 = ρ ∧ i ∈ C'.1.supp := by
    rintro ⟨C', hc, hi'⟩
    have hCC : C' = C := Subtype.ext ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hi' |>.symm.trans ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hi))
    subst hCC
    have := h.side_center C'.2 hk
    rw [hc, hv] at this
    exact absurd this (by simp)
  unfold rootLabel
  rw [ite_eq_right hno]
  exact h.lam_eq (hk.trans ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hi).symm) hv

/-- A super-character with the root on its 0-side is one that the network of a central node derives. -/
theorem mem_pieceRows_of_side {C : Cent (incompatGraph M)} (hC : NoConstantColumn M) (t : {S // S ∈ restrictRows C.1.supp M}) (hρ : h.side ⟨C.1, t⟩ ρ = false) : t.1 ∈ h.pieceRows ρ S₀ C := by
  unfold pieceRows
  by_cases hc : h.center C.1 = ρ
  · rw [ite_eq_left hc]
    exact t.2
  · rw [ite_eq_right hc]
    refine Finset.mem_erase.2 ⟨fun heq => ?_, t.2⟩
    obtain ⟨k₀, hk₀, hs₀⟩ := h.exists_side_true hC C.1 (v := ρ) (fun _ => Ne.symm hc)
    have hsame : (⟨C.1, t⟩ : SuperChar M) = k₀ := by
      obtain ⟨c₀, t₀⟩ := k₀
      obtain rfl : c₀ = C.1 := hk₀
      congr 1
      refine Subtype.ext (funext fun j => ?_)
      rw [heq]
      change h.rootLabel ρ S₀ j.1 = _
      rw [h.rootLabel_eq_valueAt (C := C) rfl hs₀ j.2]
      unfold valueAt
      simp only [j.2, ↓reduceDIte]
    rw [hsame, hs₀] at hρ
    exact absurd hρ (by simp)

/-- A super-character that the network of a central node derives has the root on its 0-side. -/
theorem side_eq_false_of_mem_pieceRows {C : Cent (incompatGraph M)} {t : {S // S ∈ restrictRows C.1.supp M}} (ht : t.1 ∈ h.pieceRows ρ S₀ C) : h.side ⟨C.1, t⟩ ρ = false := by
  by_cases hc : h.center C.1 = ρ
  · rw [← hc]
    exact h.side_center C.2 rfl
  · unfold pieceRows at ht
    rw [ite_eq_right hc] at ht
    cases hs : h.side ⟨C.1, t⟩ ρ
    · rfl
    · exfalso
      refine (Finset.mem_erase.1 ht).1 (funext fun j => ?_)
      change t.1 j = h.rootLabel ρ S₀ j.1
      rw [h.rootLabel_eq_valueAt (C := C) (k := ⟨C.1, t⟩) rfl hs j.2]
      unfold valueAt
      simp only [j.2, ↓reduceDIte]

variable (ρ S₀)

/-- The parent in the tree with a new root above `ρ`. -/
def rootPar : Option W → Option W
  | none => none
  | some b => if b = ρ then none else some (h.par ρ b)

variable {Vp Ep : Cent (incompatGraph M) → Type w} (P : ∀ C : Cent (incompatGraph M), Network C.1.supp (Vp C) (Ep C)) (S₁ : ι → Bool) (hS₁ : S₁ ∈ M)

/-- `T̄`, with a new root above `ρ`, as data for gluing. The row `S₁` is only used to name the edge of a site. -/
def rootFrame : GlueData P (Option W) where
  ρ := none
  par := h.rootPar ρ
  depth
    | none => 0
    | some b => T.dist b ρ + 1
  depth_par := by
    rintro (_ | b) hb
    · exact absurd rfl hb
    · by_cases hbρ : b = ρ
      · simp [rootPar, hbρ]
      · simp only [rootPar, hbρ, ite_false]
        have := (h.par_spec hbρ).2.2
        omega
  center C := some (h.center C.1)
  center_inj C C' heq := h.center_injective C C' (Option.some.inj heq)
  center_ne C := by simp
  lam
    | none => h.rootLabel ρ S₀
    | some v => h.lam v
  exit C
    | none => (P C).root
    | some b => h.exitNode P C b
  treeSite i := some (h.siteNode S₁ hS₁ ρ i)
  treeSite_ne i _ := by simp

variable {ρ S₀}

/-- The characters of the edge from a central node to a child: they have the 1-side of the child. -/
theorem exists_exit_char' {C : Cent (incompatGraph M)} {b : W} (hb : b ≠ ρ) (hpar : h.par ρ b = h.center C.1) :
    ∃ k : SuperChar M, k.1 = C.1 ∧ edge k = s(h.center C.1, b) ∧ h.side k b = true ∧ h.side k ρ = false := by
  obtain ⟨hadj, hsep, -⟩ := h.par_spec hb
  rw [hpar] at hadj hsep
  obtain ⟨k, hk, he⟩ := adj_center_labelled h C.2 (fun k hk => h.center_mem hk) (fun k hk r hr => h.center_zero C.2 hk hr) hadj.symm
  have hz := h.side_center C.2 hk
  have hcut : IsCut T s(h.center C.1, b) (h.side k) := he ▸ h.side_cut k
  have hne := hcut.ne_self hadj.symm
  have hb₁ : h.side k b = true := by
    rw [hz] at hne
    cases h₁ : h.side k b
    · simp [h₁] at hne
    · rfl
  refine ⟨k, hk, he, hb₁, ?_⟩
  cases h₁ : h.side k ρ
  · rfl
  · exfalso
    apply hsep
    rw [Sym2.eq_swap]
    exact hcut.sameSide_of_eq h.isTree.connected.preconnected hadj.symm (hb₁.trans h₁.symm)

variable {P}

/-- A central node's exits are leaves with the super-characters of their edges. -/
theorem exitNode_spec' (hC : NoConstantColumn M) (hder : ∀ C, (P C).Derives (h.pieceRows ρ S₀ C)) {C : Cent (incompatGraph M)} {b : W} (hb : b ≠ ρ) (hpar : h.par ρ b = h.center C.1) :
    (P C).IsLeaf (h.exitNode P C b) ∧ ∃ k : SuperChar M, k.1 = C.1 ∧ edge k = s(h.center C.1, b) ∧
      ∀ j : C.1.supp, (P C).label (h.exitNode P C b) j = valueAt k j.1 := by
  obtain ⟨k, hk, he, -, hρ⟩ := h.exists_exit_char' hb hpar
  have hex : ∃ l, (P C).IsLeaf l ∧ ∃ k : SuperChar M, k.1 = C.1 ∧ edge k = s(h.center C.1, b) ∧
      ∀ j : C.1.supp, (P C).label l j = valueAt k j.1 := by
    obtain ⟨c, t⟩ := k
    obtain rfl : c = C.1 := hk
    obtain ⟨l, hl, hlab⟩ := (hder C).surjOn (Finset.mem_coe.2 (h.mem_pieceRows_of_side hC t hρ))
    refine ⟨l, hl, ⟨C.1, t⟩, rfl, he, fun j => ?_⟩
    rw [hlab]
    unfold valueAt
    simp only [j.2, ↓reduceDIte]
  unfold exitNode
  rw [dite_eq_left hex]
  exact hex.choose_spec

section Valid

variable {S₁ hS₁}

/-- The labels agree at the ends of the edges of `T̄`, but for the sites on them. This is `IsTBar.frame_valid`, with the root at `ρ`. -/
theorem rootFrame_valid (hC : NoConstantColumn M) (hanc : ∀ C, (P C).ancestral = C.1.supp.domRestrict (h.rootLabel ρ S₀))
    (hder : ∀ C, (P C).Derives (h.pieceRows ρ S₀ C)) : (h.rootFrame ρ S₀ P S₁ hS₁).Valid := by
  have hT := h.isTree
  have hconn := hT.connected.preconnected
  set D := h.rootFrame ρ S₀ P S₁ hS₁ with hD
  have hparsome : ∀ {b : W}, b ≠ ρ → D.par (some b) = some (h.par ρ b) := fun {b} hb => by
    change h.rootPar ρ (some b) = _
    simp [rootPar, hb]
  have hparρ : D.par (some ρ) = none := by
    change h.rootPar ρ (some ρ) = _
    simp [rootPar]
  have hcen : ∀ {b : W} {C : Cent (incompatGraph M)}, some b = D.center C ↔ b = h.center C.1 := fun {b C} => by
    change some b = some (h.center C.1) ↔ _
    simp
  -- The labels at the two ends of an edge of the tree.
  have hin : ∀ b i, D.nodeLabel (D.inNode (some b)) i =
      if ∃ C : Cent (incompatGraph M), b = h.center C.1 ∧ i ∈ C.1.supp then h.rootLabel ρ S₀ i else h.lam b i := by
    intro b i
    by_cases hbc : ∃ C : Cent (incompatGraph M), b = h.center C.1
    · obtain ⟨C, rfl⟩ := hbc
      rw [show some (h.center C.1) = D.center C from rfl, D.inNode_center]
      by_cases hi : i ∈ C.1.supp
      · have h₁ : ∃ C' : Cent (incompatGraph M), h.center C.1 = h.center C'.1 ∧ i ∈ C'.1.supp := ⟨C, rfl, hi⟩
        rw [ite_eq_left h₁]
        simp only [GlueData.nodeLabel, hi, ↓reduceDIte]
        have := congrFun (hanc C) ⟨i, hi⟩
        exact this
      · have h₁ : ¬ ∃ C' : Cent (incompatGraph M), h.center C.1 = h.center C'.1 ∧ i ∈ C'.1.supp := by
          rintro ⟨C', h₂, h₃⟩
          obtain rfl := h.center_injective C C' h₂
          exact hi h₃
        rw [ite_eq_right h₁]
        simp only [GlueData.nodeLabel, hi, ↓reduceDIte]
        rfl
    · have h₁ : ¬ ∃ C : Cent (incompatGraph M), b = h.center C.1 ∧ i ∈ C.1.supp := by
        rintro ⟨C, rfl, -⟩
        exact hbc ⟨C, rfl⟩
      have hbn : some b ∉ Set.range D.center := by
        rintro ⟨C, hC'⟩
        exact hbc ⟨C, hcen.1 hC'.symm⟩
      rw [D.inNode_of_not hbn, ite_eq_right h₁]
      rfl
  have hout₁ : ∀ {b i} {C : Cent (incompatGraph M)}, b ≠ ρ → h.par ρ b = h.center C.1 → i ∈ C.1.supp →
      ∃ k : SuperChar M, k.1 = C.1 ∧ edge k = s(h.center C.1, b) ∧ D.nodeLabel (D.outNode (some b)) i = valueAt k i := by
    intro b i C hb hpar hi
    obtain ⟨-, k, hk, he, hl⟩ := h.exitNode_spec' hC hder hb hpar
    refine ⟨k, hk, he, ?_⟩
    rw [D.outNode_center (C := C) ((hparsome hb).trans (congrArg some hpar))]
    simp only [GlueData.nodeLabel, hi, ↓reduceDIte]
    exact hl ⟨i, hi⟩
  have hout₂ : ∀ {b i}, b ≠ ρ → (¬ ∃ C : Cent (incompatGraph M), h.par ρ b = h.center C.1 ∧ i ∈ C.1.supp) →
      D.nodeLabel (D.outNode (some b)) i = h.lam (h.par ρ b) i := by
    intro b i hb hno
    by_cases hbc : D.par (some b) ∈ Set.range D.center
    · obtain ⟨C, hC'⟩ := hbc
      rw [D.outNode_center hC'.symm]
      have hpar : h.par ρ b = h.center C.1 := by
        rw [hparsome hb] at hC'
        exact Option.some.inj hC'.symm
      have hi : i ∉ C.1.supp := fun hi => hno ⟨C, hpar, hi⟩
      simp only [GlueData.nodeLabel, hi, ↓reduceDIte]
      exact congrArg (fun v => h.lam v i) hpar.symm
    · rw [D.outNode_of_not hbc]
      change D.lam (D.par (some b)) i = _
      rw [hparsome hb]
      rfl
  have hroot : ∀ i, D.nodeLabel (D.outNode (some ρ)) i = h.rootLabel ρ S₀ i := by
    intro i
    have hn : D.par (some ρ) ∉ Set.range D.center := by
      rw [hparρ]
      rintro ⟨C, hC'⟩
      exact absurd hC' (by simp [hD, rootFrame])
    rw [D.outNode_of_not hn]
    change D.lam (D.par (some ρ)) i = _
    rw [hparρ]
    rfl
  -- At the new root.
  have hatroot : ∀ i, D.nodeLabel (D.inNode (some ρ)) i = D.nodeLabel (D.outNode (some ρ)) i := by
    intro i
    rw [hin, hroot]
    by_cases h₁ : ∃ C : Cent (incompatGraph M), ρ = h.center C.1 ∧ i ∈ C.1.supp
    · rw [ite_eq_left h₁]
    · rw [ite_eq_right h₁]
      unfold rootLabel
      rw [ite_eq_right]
      rintro ⟨C, h₂, h₃⟩
      exact h₁ ⟨C, h₂.symm, h₃⟩
  -- The other sites of a component.
  have hnontriv : ∀ (b : W) (_ : b ≠ ρ) (i : ι), ((incompatGraph M).connectedComponentMk i).supp.Nontrivial →
      D.nodeLabel (D.inNode (some b)) i = D.nodeLabel (D.outNode (some b)) i := by
    intro b hb i hnt
    obtain ⟨hadj, hsep, -⟩ := h.par_spec hb
    let C : Cent (incompatGraph M) := ⟨_, hnt⟩
    have hiC : i ∈ C.1.supp := rfl
    have honly : ∀ (C' : Cent (incompatGraph M)), i ∈ C'.1.supp → C' = C := fun C' hi => Subtype.ext (Eq.symm hi)
    rw [hin]
    by_cases ha : h.par ρ b = h.center C.1
    · -- The parent is the central node.
      obtain ⟨k, hk, he, hl⟩ := hout₁ hb ha hiC
      rw [hl]
      have hbne : b ≠ h.center C.1 := fun heq => T.ne_of_adj hadj (heq.trans ha.symm)
      have h₁ : ¬ ∃ C' : Cent (incompatGraph M), b = h.center C'.1 ∧ i ∈ C'.1.supp := by
        rintro ⟨C', h₂, h₃⟩
        rw [honly C' h₃] at h₂
        exact hbne h₂
      rw [ite_eq_right h₁]
      have hz := h.side_center C.2 hk
      have hcut : IsCut T s(h.center C.1, b) (h.side k) := he ▸ h.side_cut k
      have hadj' : T.Adj (h.center C.1) b := ha ▸ hadj.symm
      have hne := hcut.ne_self hadj'
      rw [hz] at hne
      have hbt : h.side k b = true := by
        cases h₃ : h.side k b
        · simp [h₃] at hne
        · rfl
      exact h.lam_eq hk hbt
    · rw [hout₂ hb (by
        rintro ⟨C', h₂, h₃⟩
        rw [honly C' h₃] at h₂
        exact ha h₂)]
      by_cases hbc : b = h.center C.1
      · -- The child is the central node: the edge has the character on the side of the root.
        have h₁ : ∃ C' : Cent (incompatGraph M), b = h.center C'.1 ∧ i ∈ C'.1.supp := ⟨C, hbc, hiC⟩
        rw [ite_eq_left h₁]
        have hρne : ρ ≠ h.center C.1 := fun heq => hb (hbc.trans heq.symm)
        obtain ⟨k₀, hk₀, hρ⟩ := h.exists_side_true hC C.1 (v := ρ) (fun _ => hρne)
        have hzero : h.side k₀ (h.center C.1) = false := h.side_center C.2 hk₀
        obtain ⟨a', b', he', hab', ha', hb'⟩ := h.exists_ends k₀ (h.side_cut _)
        -- The end on the 0-side is the central node.
        have hcen₀ : a' = h.center C.1 := by
          have hmem : h.center C.1 ∈ edge k₀ := h.center_mem hk₀
          rw [he'] at hmem
          rcases Sym2.mem_iff.1 hmem with h₃ | h₃
          · exact h₃.symm
          · rw [← h₃, hzero] at hb'
            exact absurd hb' (by simp)
        subst hcen₀
        have hsep' : ¬ SameSide T s(h.center C.1, b') (h.center C.1) ρ := by
          intro hsame
          have hcut : IsCut T s(h.center C.1, b') (h.side k₀) := he' ▸ h.side_cut _
          have := hcut.eq_of_sameSide hsame
          rw [ha', hρ] at this
          exact absurd this (by simp)
        have hpar := h.par_unique hab' hsep'
        have h₂ : b' = h.par ρ b := by rw [hbc]; exact hpar
        rw [← h₂, h.lam_eq (hk₀.trans (by rfl)) hb']
        exact h.rootLabel_eq_valueAt (C := C) hk₀ hρ hiC
      · -- Neither end is the central node.
        have h₁ : ¬ ∃ C' : Cent (incompatGraph M), b = h.center C'.1 ∧ i ∈ C'.1.supp := by
          rintro ⟨C', h₂, h₃⟩
          rw [honly C' h₃] at h₂
          exact hbc h₂
        rw [ite_eq_right h₁]
        obtain ⟨k, hk, hk₁⟩ := h.exists_side_true hC C.1 (v := h.par ρ b) (fun _ => ha)
        have hne : s(b, h.par ρ b) ≠ edge k := by
          intro heq
          have hmem := h.center_mem hk
          rw [← heq] at hmem
          rcases Sym2.mem_iff.1 hmem with h₃ | h₃
          · exact hbc h₃.symm
          · exact ha h₃.symm
        have hbt : h.side k b = true := by
          rw [(h.side_cut k).eq_of_ne hadj hne]
          exact hk₁
        rw [h.lam_eq hk hbt, h.lam_eq hk hk₁]
  -- A site in a trivial component.
  have hsiteval : ∀ i, D.siteArc i = (if hi : ((incompatGraph M).connectedComponentMk i).supp.Nontrivial then
      .inr ⟨⟨_, hi⟩, (P ⟨_, hi⟩).site ⟨i, rfl⟩⟩ else .inl ⟨D.treeSite i, D.treeSite_ne i hi⟩) := fun _ => rfl
  have htrivial : ∀ (b : W) (_ : b ≠ ρ) (i : ι), ¬ ((incompatGraph M).connectedComponentMk i).supp.Nontrivial →
      (D.nodeLabel (D.inNode (some b)) i = h.lam b i) ∧ D.nodeLabel (D.outNode (some b)) i = h.lam (h.par ρ b) i := by
    intro b hb i hnt
    have hno : ∀ C : Cent (incompatGraph M), i ∉ C.1.supp := fun C hi => hnt (by
      have : (incompatGraph M).connectedComponentMk i = C.1 := hi
      rw [this]
      exact C.2)
    constructor
    · rw [hin, ite_eq_right]
      rintro ⟨C, -, h₃⟩
      exact hno C h₃
    · exact hout₂ hb (by
        rintro ⟨C, -, h₃⟩
        exact hno C h₃)
  -- The two characters of a trivial component.
  have htwo : ∀ (i : ι), ¬ ((incompatGraph M).connectedComponentMk i).supp.Nontrivial →
      ∃ k' : SuperChar M, k' ≠ charOf ((incompatGraph M).connectedComponentMk i) hS₁ ∧ k'.1 = (incompatGraph M).connectedComponentMk i ∧
        valueAt k' i = !valueAt (charOf ((incompatGraph M).connectedComponentMk i) hS₁) i := by
    intro i _
    obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ := hC i
    have hr : ∃ r ∈ M, r i ≠ S₁ i := by
      by_cases h₁ : r₁ i = S₁ i
      · refine ⟨r₂, hr₂, fun h₂ => hne (h₁.trans h₂.symm)⟩
      · exact ⟨r₁, hr₁, h₁⟩
    obtain ⟨r, hrM, hrS⟩ := hr
    have hv₁ := valueAt_of_charValue (charValue_charOf ((incompatGraph M).connectedComponentMk i) hrM) (i := i) rfl
    have hv₂ := valueAt_of_charValue (charValue_charOf ((incompatGraph M).connectedComponentMk i) hS₁) (i := i) rfl
    refine ⟨charOf ((incompatGraph M).connectedComponentMk i) hrM, fun heq => ?_, rfl, ?_⟩
    · rw [heq, hv₂] at hv₁
      exact hrS hv₁.symm
    · rw [hv₁, hv₂]
      revert hrS
      cases r i <;> cases S₁ i <;> simp
  constructor
  · -- The site's edge.
    rintro (_ | b) hb i hsite
    · exact absurd rfl hb
    have hnt : ¬ ((incompatGraph M).connectedComponentMk i).supp.Nontrivial := by
      intro hnt
      rw [hsiteval, dite_eq_left hnt] at hsite
      simp at hsite
    have hb₀ : D.treeSite i = some b := by
      rw [hsiteval, dite_eq_right hnt] at hsite
      simpa using hsite
    have hb₀' : h.siteNode S₁ hS₁ ρ i = b := Option.some.inj hb₀
    have hspec := (h.exists_child ρ (h.edge_mem (charOf ((incompatGraph M).connectedComponentMk i) hS₁))).choose_spec
    have hbρ : b ≠ ρ := hb₀' ▸ hspec.1
    obtain ⟨h₁, h₂⟩ := htrivial b hbρ i hnt
    rw [h₁, h₂]
    obtain ⟨k', hk', hk'c, hval⟩ := htwo i hnt
    have he : edge (charOf ((incompatGraph M).connectedComponentMk i) hS₁) = s(h.par ρ b, b) := by
      rw [← hb₀']
      exact hspec.2
    obtain ⟨hadj, -, -⟩ := h.par_spec hbρ
    have hcut : IsCut T s(h.par ρ b, b) (h.side (charOf ((incompatGraph M).connectedComponentMk i) hS₁)) := he ▸ h.side_cut _
    have hne := hcut.ne_self hadj.symm
    have hopp : ∀ v, h.side k' v = !h.side (charOf ((incompatGraph M).connectedComponentMk i) hS₁) v :=
      h.side_ne_of_trivial hk' hk'c (by rw [hk'c]; exact hnt)
    cases h₃ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS₁) (h.par ρ b)
    · -- The parent is on the other character's 1-side.
      have h₄ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS₁) b = true := by
        rw [h₃] at hne
        cases h₅ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS₁) b
        · simp [h₅] at hne
        · rfl
      rw [h.lam_eq (k := charOf ((incompatGraph M).connectedComponentMk i) hS₁) rfl h₄, h.lam_eq hk'c (by rw [hopp, h₃]; rfl), hval]
      simp
    · have h₄ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS₁) b = false := by
        rw [h₃] at hne
        cases h₅ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS₁) b
        · rfl
        · simp [h₅] at hne
      rw [h.lam_eq (k := charOf ((incompatGraph M).connectedComponentMk i) hS₁) rfl h₃, h.lam_eq hk'c (by rw [hopp, h₄]; rfl), hval]
  · rintro (_ | b) hb i hsite
    · exact absurd rfl hb
    by_cases hbρ : b = ρ
    · subst hbρ
      exact hatroot i
    by_cases hnt : ((incompatGraph M).connectedComponentMk i).supp.Nontrivial
    · exact hnontriv b hbρ i hnt
    · obtain ⟨h₁, h₂⟩ := htrivial b hbρ i hnt
      rw [h₁, h₂]
      have hb₀ : h.siteNode S₁ hS₁ ρ i ≠ b := by
        intro heq
        apply hsite
        rw [hsiteval, dite_eq_right hnt]
        congr 1
        exact Subtype.ext (congrArg some heq)
      obtain ⟨k', hk', hk'c, -⟩ := htwo i hnt
      have hspec := (h.exists_child ρ (h.edge_mem (charOf ((incompatGraph M).connectedComponentMk i) hS₁))).choose_spec
      obtain ⟨hadj, -, hdist⟩ := h.par_spec hbρ
      have hne : s(b, h.par ρ b) ≠ edge (charOf ((incompatGraph M).connectedComponentMk i) hS₁) := by
        intro heq
        rw [hspec.2] at heq
        change s(b, h.par ρ b) = s(h.par ρ (h.siteNode S₁ hS₁ ρ i), h.siteNode S₁ hS₁ ρ i) at heq
        rcases Sym2.eq_iff.1 heq with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
        · have h₅ := (h.par_spec (b := h.siteNode S₁ hS₁ ρ i) hspec.1).2.2
          rw [← h₃, ← h₄] at h₅
          exact lt_asymm hdist h₅
        · exact hb₀ h₃.symm
      have heq := (h.side_cut (charOf ((incompatGraph M).connectedComponentMk i) hS₁)).eq_of_ne hadj hne
      have hopp : ∀ v, h.side k' v = !h.side (charOf ((incompatGraph M).connectedComponentMk i) hS₁) v :=
        h.side_ne_of_trivial hk' hk'c (by rw [hk'c]; exact hnt)
      cases h₃ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS₁) (h.par ρ b)
      · have h₄ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS₁) b = false := heq.trans h₃
        rw [h.lam_eq hk'c (by rw [hopp, h₄]; rfl), h.lam_eq hk'c (by rw [hopp, h₃]; rfl)]
      · have h₄ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS₁) b = true := heq.trans h₃
        rw [h.lam_eq (k := charOf ((incompatGraph M).connectedComponentMk i) hS₁) rfl h₄, h.lam_eq (k := charOf ((incompatGraph M).connectedComponentMk i) hS₁) rfl h₃]

end Valid

section Derives

variable {S₁ hS₁}

theorem rootFrame_par_some {b : W} (hb : b ≠ ρ) : (h.rootFrame ρ S₀ P S₁ hS₁).par (some b) = some (h.par ρ b) := by
  change h.rootPar ρ (some b) = _
  simp [rootPar, hb]

theorem rootFrame_par_root : (h.rootFrame ρ S₀ P S₁ hS₁).par (some ρ) = none := by
  change h.rootPar ρ (some ρ) = _
  simp [rootPar]

/-- A row isn't a central node. -/
theorem row_notMem_center (r : M) : some (φ r) ∉ Set.range (h.rootFrame ρ S₀ P S₁ hS₁).center := by
  rintro ⟨C, hC'⟩
  have hz : h.side (charOf C.1 r.2) (h.center C.1) = false := h.side_center C.2 rfl
  have hC'' : h.center C.1 = φ r := Option.some.inj hC'
  rw [hC'', h.side_row] at hz
  rw [show charValue (charOf C.1 r.2) (r : ι → Bool) = true from charValue_charOf C.1 r.2] at hz
  exact absurd hz (by simp)

/-- A row other than the root is a leaf. -/
theorem rootFrame_row_isLeaf (hD : (h.rootFrame ρ S₀ P S₁ hS₁).Valid) (r : M) (hr : φ r ≠ ρ) :
    ((h.rootFrame ρ S₀ P S₁ hS₁).net hD).IsLeaf (.inl ⟨some (φ r), h.row_notMem_center r⟩) := by
  refine (Decomp.GlueData.isLeaf_net_inl hD _).2 ?_
  rintro (_ | b) hb hpar
  · exact absurd rfl hb
  · by_cases hbρ : b = ρ
    · subst hbρ
      rw [rootFrame_par_root] at hpar
      simp at hpar
    · rw [rootFrame_par_some h hbρ] at hpar
      have hpar' : h.par ρ b = φ r := Option.some.inj hpar
      obtain ⟨hadj, -, hdist⟩ := h.par_spec hbρ
      obtain ⟨hadj₁, -, hdist₁⟩ := h.par_spec hr
      rw [hpar'] at hadj hdist
      have hbeq : b = h.par ρ (φ r) :=
        (Set.ncard_le_one_iff (Set.toFinite _)).1 ((h.mem_range_iff _).1 ⟨_, rfl⟩) hadj.symm hadj₁
      rw [← hbeq] at hdist₁
      exact lt_asymm hdist hdist₁

theorem rootFrame_row_label (hD : (h.rootFrame ρ S₀ P S₁ hS₁).Valid) (r : M) :
    ((h.rootFrame ρ S₀ P S₁ hS₁).net hD).label (.inl ⟨some (φ r), h.row_notMem_center r⟩) = (r : ι → Bool) := by
  funext i
  exact h.lam_row r i

/-- The leaves of the glued network are the rows other than the root. -/
theorem rootFrame_derives (hC : NoConstantColumn M) (hder : ∀ C, (P C).Derives (h.pieceRows ρ S₀ C)) (hD : (h.rootFrame ρ S₀ P S₁ hS₁).Valid) (hnb : ∃ z, T.Adj ρ z)
    {M' : Finset (ι → Bool)} (hM' : ∀ r, r ∈ M' ↔ ∃ hr : r ∈ M, φ ⟨r, hr⟩ ≠ ρ) : ((h.rootFrame ρ S₀ P S₁ hS₁).net hD).Derives M' := by
  have hT := h.isTree
  set D := h.rootFrame ρ S₀ P S₁ hS₁ with hDdef
  -- A node with no child is a row.
  have hchild : ∀ v, v ≠ ρ → (∀ b, b ≠ ρ → h.par ρ b ≠ v) → v ∈ Set.range φ := by
    intro v hv hno
    rw [h.mem_range_iff, Set.ncard_le_one (Set.toFinite _)]
    intro a ha c hc
    have hval : ∀ {u}, T.Adj v u → u = h.par ρ v := by
      intro u hu
      rcases h.adj_cases (ρ := ρ) hu with ⟨h₁, h₂⟩ | ⟨-, h₂⟩
      · exact absurd h₂.symm (hno u h₁)
      · exact h₂
    rw [hval ha, hval hc]
  -- The node of the root has a child.
  have hroot : ∃ b, b ≠ ρ ∧ h.par ρ b = ρ := by
    obtain ⟨z, hz⟩ := hnb
    rcases h.adj_cases (ρ := ρ) hz with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
    · exact ⟨z, h₁, h₂.symm⟩
    · exact absurd rfl h₁
  -- A leaf of a network has an exit.
  have hnoinr : ∀ (C : Cent (incompatGraph M)) (x : Vp C), ¬ (D.net hD).IsLeaf (.inr ⟨C, x⟩) := by
    intro C x hx
    obtain ⟨hl, hexit⟩ := Decomp.GlueData.isLeaf_net_inr hD hx
    have hmem := (hder C).mapsTo hl
    have hmem₁ : (P C).label x ∈ restrictRows C.1.supp M := h.pieceRows_subset C (Finset.mem_coe.1 hmem)
    let k : SuperChar M := ⟨C.1, ⟨(P C).label x, hmem₁⟩⟩
    have hk : k.1 = C.1 := rfl
    obtain ⟨a', b', he', hab', ha', hb'⟩ := h.exists_ends k (h.side_cut k)
    have hzero : h.side k (h.center C.1) = false := h.side_center C.2 hk
    have hcen : a' = h.center C.1 := by
      have hmem₂ : h.center C.1 ∈ edge k := h.center_mem hk
      rw [he'] at hmem₂
      rcases Sym2.mem_iff.1 hmem₂ with h₃ | h₃
      · exact h₃.symm
      · rw [← h₃, hzero] at hb'
        exact absurd hb' (by simp)
    subst hcen
    have hρ : h.side k ρ = false := h.side_eq_false_of_mem_pieceRows (t := ⟨(P C).label x, hmem₁⟩) (Finset.mem_coe.1 hmem)
    have hcut : IsCut T s(h.center C.1, b') (h.side k) := he' ▸ h.side_cut k
    have hsep : ¬ SameSide T s(b', h.center C.1) b' ρ := by
      rw [Sym2.eq_swap]
      intro hsame
      have := hcut.eq_of_sameSide hsame
      rw [hb', hρ] at this
      exact absurd this (by simp)
    have hbne : b' ≠ ρ := by
      rintro rfl
      exact hsep (SimpleGraph.Reachable.refl _)
    have hpar : h.par ρ b' = h.center C.1 := (h.par_unique hab'.symm hsep).symm
    obtain ⟨hl₂, k', hk', he₂, hval⟩ := h.exitNode_spec' hC hder hbne hpar
    have hkk : k' = k := by
      by_contra hne₂
      exact h.edge_ne hne₂ hk' (hk' ▸ C.2) (he₂.trans he'.symm)
    subst hkk
    have hlab : (P C).label (h.exitNode P C b') = (P C).label x := by
      funext j
      rw [hval j]
      unfold valueAt
      rw [dite_eq_left (show j.1 ∈ k.1.supp from j.2)]
    refine hexit (some b') (by simp [hDdef, rootFrame]) ?_ ((hder C).injOn hl₂ hl hlab)
    rw [rootFrame_par_some h hbne]
    exact congrArg some hpar
  have hleaf : ∀ y, (D.net hD).IsLeaf y → ∃ r : M, φ r ≠ ρ ∧ y = .inl ⟨some (φ r), h.row_notMem_center r⟩ := by
    intro y hy
    cases y with
    | inl v =>
      obtain ⟨v, hvc⟩ := v
      have hno := (Decomp.GlueData.isLeaf_net_inl hD ⟨v, hvc⟩).1 hy
      rcases v with _ | v
      · exact absurd (rootFrame_par_root h) (hno (some ρ) (by simp [hDdef, rootFrame]))
      · have hvρ : v ≠ ρ := by
          rintro rfl
          obtain ⟨b, hb, hpar⟩ := hroot
          refine hno (some b) (by simp [hDdef, rootFrame]) ?_
          rw [rootFrame_par_some h hb, hpar]
        obtain ⟨r, hr⟩ := hchild v hvρ fun b hb hpar => hno (some b) (by simp [hDdef, rootFrame]) (by rw [rootFrame_par_some h hb, hpar])
        refine ⟨r, hr ▸ hvρ, ?_⟩
        congr 1
        exact Subtype.ext (congrArg some hr.symm)
    | inr y =>
      obtain ⟨C, x⟩ := y
      exact absurd hy (hnoinr C x)
  refine ⟨fun y hy => ?_, fun a ha b hb hab => ?_, fun r hr => ?_⟩
  · obtain ⟨r, hrS, rfl⟩ := hleaf y hy
    rw [rootFrame_row_label]
    exact Finset.mem_coe.2 ((hM' _).2 ⟨r.2, hrS⟩)
  · obtain ⟨r, -, rfl⟩ := hleaf a ha
    obtain ⟨r', -, rfl⟩ := hleaf b hb
    rw [rootFrame_row_label, rootFrame_row_label] at hab
    rw [Subtype.ext hab]
  · obtain ⟨hrM, hne⟩ := (hM' r).1 (Finset.mem_coe.1 hr)
    exact ⟨_, h.rootFrame_row_isLeaf hD ⟨r, hrM⟩ hne, h.rootFrame_row_label hD ⟨r, hrM⟩⟩

end Derives

end IsTBar

/-! ### The network -/

section Network

variable [LinearOrder ι] [Finite ι]

open IsTBar Decomp

/-- The network for the root at `ρ`, on any finite types. -/
theorem exists_rooted_aux (c : Crossover) (hC : NoConstantColumn M) (h : IsTBar M T φ edge) {ρ : W} (S₀ : ι → Bool) (hnb : ∃ z, T.Adj ρ z)
    {S₁ : ι → Bool} (hS₁ : S₁ ∈ M) {M' : Finset (ι → Bool)} (hM' : ∀ r, r ∈ M' ↔ ∃ hr : r ∈ M, φ ⟨r, hr⟩ ≠ ρ) :
    ∃ (V E : Type (max u v)) (_ : Finite V) (_ : Finite E) (N : Network ι V E), N.Obeys c ∧ N.Derives M' ∧ N.ancestral = h.rootLabel ρ S₀ ∧ N.IsFullyDecomposedFor (incompatGraph M) ∧
      ∃ f : N.blobbedTree ≃g T, (∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) ∧ f (N.toBlobNode N.root) = ρ := by
  -- The networks for the central nodes.
  have hinf : ∀ C : Cent (incompatGraph M), ∃ (a b : ℕ) (N : Network C.1.supp (Fin a) (Fin b)), N.Obeys c ∧ N.ancestral = C.1.supp.domRestrict (h.rootLabel ρ S₀) ∧
      N.Derives (h.pieceRows ρ S₀ C) ∧ (∀ e, N.OnCycle e) ∧ ∃! B, N.IsBlob B := by
    intro C
    have hne : (h.pieceRows ρ S₀ C).Nonempty := by
      have h₄ := four_le_card_restrictRows C.2
      unfold pieceRows
      split_ifs
      · rw [← Finset.card_pos]
        omega
      · have h₅ := Finset.pred_card_le_card_erase (s := restrictRows C.1.supp M) (a := C.1.supp.domRestrict (h.rootLabel ρ S₀))
        rw [← Finset.card_pos]
        omega
    have : Fintype C.1.supp := Fintype.ofFinite _
    have hnt : Nontrivial C.1.supp := Set.nontrivial_coe_sort.2 C.2
    exact inflate c (Fintype.one_lt_card_iff_nontrivial.2 hnt) _ hne _
  choose a b P hob hanc hder hall huniq using hinf
  have : Finite (incompatGraph M).ConnectedComponent :=
    Finite.of_surjective (incompatGraph M).connectedComponentMk fun c => c.exists_rep
  have hD := h.rootFrame_valid hC (S₁ := S₁) (hS₁ := hS₁) (P := P) hanc hder
  set D := h.rootFrame ρ S₀ P S₁ hS₁ with hDdef
  have hderives : (D.net hD).Derives M' := h.rootFrame_derives hC hder hD hnb hM'
  have hne_none : (some ρ : Option W) ≠ D.ρ := by simp [hDdef, rootFrame]
  let a₀ : D.Arcs := .inl ⟨some ρ, hne_none⟩
  have hparρ : D.par (some ρ) = none := rootFrame_par_root h
  have hparsome : ∀ {b : W}, b ≠ ρ → D.par (some b) = some (h.par ρ b) := fun hb => rootFrame_par_some h hb
  have hpar_iff : ∀ c : Option W, c ≠ D.ρ → D.par c = none → c = some ρ := by
    rintro (_ | b) hc hp
    · exact absurd rfl hc
    · by_cases hb : b = ρ
      · rw [hb]
      · rw [hparsome hb] at hp
        simp at hp
  have hdrop : (D.net hD).DropCond a₀ := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · have hn : D.par (some ρ) ∉ Set.range D.center := by
        rw [hparρ]
        rintro ⟨C, hC'⟩
        exact absurd hC' (by simp [hDdef, rootFrame])
      change D.outNode (some ρ) = _
      rw [D.outNode_of_not hn]
      congr 1
      exact Subtype.ext (hparρ)
    · intro f hf
      cases f with
      | inl c =>
        have ht := congrArg D.toTree hf
        change D.toTree (D.outNode c.1) = D.ρ at ht
        rw [D.toTree_outNode] at ht
        exact congrArg Sum.inl (Subtype.ext (hpar_iff c.1 c.2 ht))
      | inr f =>
        obtain ⟨C, e⟩ := f
        exact absurd hf (by simp [GlueData.net, GlueData.arcSrc])
    · exact fun f hf => GlueData.arcTgt_inl _ hf
    · intro i
      by_cases hi : ((incompatGraph M).connectedComponentMk i).supp.Nontrivial
      · change D.siteArc i ≠ _
        unfold GlueData.siteArc
        rw [dite_eq_left hi]
        simp [a₀]
      · change D.siteArc i ≠ _
        unfold GlueData.siteArc
        rw [dite_eq_right hi]
        intro heq
        have h₁ : D.treeSite i = some ρ := congrArg Subtype.val (Sum.inl.inj heq)
        have h₂ : h.siteNode S₁ hS₁ ρ i = ρ := Option.some.inj h₁
        exact (h.exists_child ρ (h.edge_mem (charOf ((incompatGraph M).connectedComponentMk i) hS₁))).choose_spec.1 h₂
  have hSC := Network.dropRoot_sameCycles hdrop
  -- The arcs on cycles are those of the networks.
  have hinl : ∀ c : {c : Option W // c ≠ D.ρ}, ¬ (D.net hD).OnCycle (.inl c) := by
    rintro c ⟨Q, ⟨w, x, p, q, hc, rfl⟩, hm⟩
    rcases hm with hm | hm
    · exact (GlueData.not_mem_cycle_inl hD hc c).1 hm
    · exact (GlueData.not_mem_cycle_inl hD hc c).2 hm
  have hinr : ∀ C (e : Fin (b C)), (D.net hD).OnCycle (.inr ⟨C, e⟩) := by
    intro C e
    obtain ⟨Q, hQ, hm⟩ := hall C e
    exact ⟨_, (GlueData.emb_piece hD C).isCycle_image hQ, ⟨e, hm, rfl⟩⟩
  have hP : ∀ C, (∃! B, (P C).IsBlob B) ∧ ∀ i, ∃ B, (P C).IsBlob B ∧ (P C).site i ∈ B := fun C =>
    ⟨huniq C, fun i => (P C).exists_isBlob_of_onCycle (hall C _)⟩
  -- The projection to `T̄`.
  let τ : {v // v ≠ (D.net hD).root} → W := fun x => (D.toTree x.1).getD ρ
  have hτ_inl : ∀ (v : {v : Option W // v ∉ Set.range D.center}) (z : W) (hz : (.inl v : D.Vtx) ≠ (D.net hD).root), v.1 = some z → τ ⟨.inl v, hz⟩ = z := by
    rintro ⟨_, _⟩ z hz rfl
    rfl
  have hτ_inr : ∀ (C : Cent (incompatGraph M)) (x : Fin (a C)) (hz : (.inr ⟨C, x⟩ : D.Vtx) ≠ (D.net hD).root), τ ⟨.inr ⟨C, x⟩, hz⟩ = h.center C.1 := fun _ _ _ => rfl
  have hinr_ne : ∀ (C : Cent (incompatGraph M)) (x : Fin (a C)), (.inr ⟨C, x⟩ : D.Vtx) ≠ (D.net hD).root := fun _ _ => by simp [GlueData.net]
  have hinl_ne : ∀ (v : {v : Option W // v ∉ Set.range D.center}) (z : W), v.1 = some z → (.inl v : D.Vtx) ≠ (D.net hD).root := by
    rintro v z hz heq
    have : v.1 = D.ρ := congrArg Subtype.val (Sum.inl.inj heq)
    rw [hz] at this
    exact absurd this (by simp [hDdef, rootFrame])
  have htoTree : ∀ (x : {v // v ≠ (D.net hD).root}), D.toTree x.1 = some (τ x) := by
    rintro ⟨x | ⟨C, y⟩, hx⟩
    · obtain ⟨_ | z, hv⟩ := x
      · exact absurd (by congr 1) hx
      · rfl
    · rfl
  set N₀ := (D.net hD).dropRoot a₀ hdrop with hN₀
  have hpiece : ∀ C (x : Fin (a C)), N₀.toBlobNode ⟨.inr ⟨C, x⟩, hinr_ne C x⟩ = N₀.toBlobNode ⟨.inr ⟨C, (P C).root⟩, hinr_ne C _⟩ := by
    intro C x
    have hr := (P C).reach_root x
    induction hr with
    | refl => rfl
    | tail _ hs ih =>
      obtain ⟨g, hg, hg'⟩ := hs
      subst hg
      subst hg'
      rw [← ih]
      have hne : (.inr ⟨C, g⟩ : D.Arcs) ≠ a₀ := by simp [a₀]
      have hg₀ : N₀.OnCycle ⟨.inr ⟨C, g⟩, hne⟩ := hSC.onCycle_iff.1 (hinr C g)
      exact (Network.toBlobNode_eq_of_onCycle hg₀).symm
  have hτ₁ : ∀ e, N₀.OnCycle e → τ (N₀.src e) = τ (N₀.tgt e) := by
    rintro ⟨e | ⟨C, e⟩, he⟩ hc
    · exact absurd (hSC.onCycle_iff.2 hc) (hinl e)
    · rfl
  have hτ₂ : ∀ u v, τ u = τ v → N₀.toBlobNode u = N₀.toBlobNode v := by
    rintro ⟨u | ⟨C, x⟩, hu⟩ ⟨v | ⟨C', x'⟩, hv⟩ huv
    · have h₁ := htoTree ⟨.inl u, hu⟩
      have h₂ := htoTree ⟨.inl v, hv⟩
      have h₃ : (Sum.inl u : D.Vtx) = Sum.inl v := by
        congr 1
        refine Subtype.ext ?_
        change u.1 = some _ at h₁
        change v.1 = some _ at h₂
        rw [h₁, h₂, huv]
      simp only [h₃]
    · have h₁ := htoTree ⟨.inl u, hu⟩
      change u.1 = some _ at h₁
      rw [huv] at h₁
      exact absurd ⟨C', h₁.symm⟩ u.2
    · have h₂ := htoTree ⟨.inl v, hv⟩
      change v.1 = some _ at h₂
      rw [← huv] at h₂
      exact absurd ⟨C, h₂.symm⟩ v.2
    · obtain rfl : C = C' := h.center_injective C C' huv
      rw [hpiece C x, hpiece C x']
  have hsurj : Function.Surjective τ := by
    intro w
    have hne : D.inNode (some w) ≠ (D.net hD).root := by
      intro heq
      have := congrArg D.toTree heq
      rw [D.toTree_inNode] at this
      exact absurd this (by simp [GlueData.net, GlueData.toTree, hDdef, rootFrame])
    refine ⟨⟨_, hne⟩, ?_⟩
    change (D.toTree (D.inNode (some w))).getD ρ = w
    rw [D.toTree_inNode]
    rfl
  have harc : ∀ (y : W) (hy : y ≠ ρ), ∃ e : {e // e ≠ a₀}, N₀.IsTreeArc e ∧ τ (N₀.src e) = h.par ρ y ∧ τ (N₀.tgt e) = y := by
    intro y hy
    have hcne : (some y : Option W) ≠ D.ρ := by simp [hDdef, rootFrame]
    have hne : (.inl ⟨some y, hcne⟩ : D.Arcs) ≠ a₀ := by
      intro heq
      exact hy (Option.some.inj (congrArg Subtype.val (Sum.inl.inj heq)))
    refine ⟨⟨_, hne⟩, fun hc => hinl _ (hSC.onCycle_iff.2 hc), ?_, ?_⟩
    · change (D.toTree (D.outNode (some y))).getD ρ = _
      rw [D.toTree_outNode, hparsome hy]
      rfl
    · change (D.toTree (D.inNode (some y))).getD ρ = _
      rw [D.toTree_inNode]
      rfl
  have hτ₄ : ∀ e, N₀.IsTreeArc e → T.Adj (τ (N₀.src e)) (τ (N₀.tgt e)) := by
    rintro ⟨e | ⟨C, e⟩, he⟩ ht
    · obtain ⟨_ | y, hy⟩ := e
      · exact absurd rfl hy
      · have hyρ : y ≠ ρ := by
          rintro rfl
          exact he rfl
        have h₁ : τ (N₀.src ⟨.inl ⟨some y, hy⟩, he⟩) = h.par ρ y := by
          change (D.toTree (D.outNode (some y))).getD ρ = _
          rw [D.toTree_outNode, hparsome hyρ]
          rfl
        have h₂ : τ (N₀.tgt ⟨.inl ⟨some y, hy⟩, he⟩) = y := by
          change (D.toTree (D.inNode (some y))).getD ρ = _
          rw [D.toTree_inNode]
          rfl
        rw [h₁, h₂]
        exact (h.par_spec hyρ).1.symm
    · exact absurd (hSC.onCycle_iff.1 (hinr C e)) ht
  have hτ₅ : ∀ x y, T.Adj x y → ∃ e, N₀.IsTreeArc e ∧ s(τ (N₀.src e), τ (N₀.tgt e)) = s(x, y) := by
    intro x₁ x₂ hx
    rcases h.adj_cases (ρ := ρ) hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · obtain ⟨e, he, h₃, h₄⟩ := harc x₂ h₁
      exact ⟨e, he, by rw [h₃, h₄, ← h₂]⟩
    · obtain ⟨e, he, h₃, h₄⟩ := harc x₁ h₁
      exact ⟨e, he, by rw [h₃, h₄, ← h₂, Sym2.eq_swap]⟩
  obtain ⟨f, hf⟩ := Network.exists_blobbedTree_iso_of_proj (N := N₀) (T := T) τ hτ₁ hτ₂ hsurj hτ₄ hτ₅
  refine ⟨_, _, inferInstance, inferInstance, N₀, hSC.obeys_back (fun _ => rfl) (GlueData.net_obeys hD hob), Network.dropRoot_derives hdrop hderives,
    (Network.dropRoot_ancestral hdrop), (hSC.isFullyDecomposedFor_iff fun _ => rfl).1 (GlueData.net_fullyDecomposed hD hP), f, fun v r hr hv hvr => ?_, ?_⟩
  · have hdN₀ : N₀.Derives M' := Network.dropRoot_derives hdrop hderives
    have hrM' : r ∈ M' := by
      rw [← hvr]
      exact Finset.mem_coe.1 (hdN₀.mapsTo hv)
    obtain ⟨_, hne⟩ := (hM' r).1 hrM'
    have hvne := hinl_ne ⟨some (φ ⟨r, hr⟩), h.row_notMem_center ⟨r, hr⟩⟩ _ rfl
    have hrl : N₀.IsLeaf ⟨_, hvne⟩ := (Network.dropRoot_isLeaf hdrop _).2 (h.rootFrame_row_isLeaf hD ⟨r, hr⟩ hne)
    have heq := hdN₀.injOn hv hrl (hvr.trans (h.rootFrame_row_label hD ⟨r, hr⟩).symm)
    rw [hf, heq]
    rfl
  · rw [hf]
    change (D.toTree (D.inNode (some ρ))).getD ρ = ρ
    rw [D.toTree_inNode]
    rfl

/-- **Line 299, with the root at any node of `T̄`** (`g:root_any_node`). "We arbitrarily select a node `v_r` of `T̄` to be the root and direct all the edges in `T̄` away from that chosen root. Let `S` be the label written at node `v_r`." For a node `ρ` of `T̄` that isn't a row, there's an efficient fully decomposed network for `M`, in any model, whose `T′` is `T̄`, respecting the rows, with its root at `ρ`, and with all of the hypotheses of `theorem4_entry`. Its ancestral sequence is the label of `ρ`, `IsTBar.rootLabel`, with any sequence `S₀` on the sites of the component of which `ρ` is the central node, if there's one.

Departure from the paper: line 299 takes `S(C)` as the ancestral sequence of a central root, and line 416 says that "the label on `v` can be used". The labels of `T̄` give no sequence on `C` there, by Lemma 4, since the node is on the `0`-side of every character from `C`. So `S₀` is any sequence: the network of `C` then derives all the super-characters of `C`. A row needs `exists_network_rooted_at_row`. -/
theorem exists_network_rooted_at (c : Crossover) (hC : NoConstantColumn M) (h : IsTBar M T φ edge) {ρ : W} (hρ : ρ ∉ Set.range φ) (S₀ : ι → Bool) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = h.rootLabel ρ S₀ ∧ N.IsFullyDecomposedFor (incompatGraph M) ∧
      N.IsEfficient ∧ N.IsEfficientAtEntry ∧ N.RegularArcs ∧ N.DegreeCond ∧
      ∃ f : N.blobbedTree ≃g T, (∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) ∧ f (N.toBlobNode N.root) = ρ := by
  have hnb : ∃ z, T.Adj ρ z := by
    have hdeg : ¬ (T.neighborSet ρ).ncard ≤ 1 := fun hle => hρ ((h.mem_range_iff ρ).2 hle)
    have hpos : 0 < (T.neighborSet ρ).ncard := by omega
    obtain ⟨z, hz⟩ := (Set.ncard_pos (Set.toFinite _)).1 hpos
    exact ⟨z, hz⟩
  obtain ⟨⟨S₁, hS₁⟩, -⟩ := exists_label_sameSide h.isTree h.labelled s(ρ, ρ) s(ρ, ρ) ρ
  obtain ⟨V, E, _, _, N₀, h₁, h₂, h₃, h₄, f₀, hrow, hroot⟩ := exists_rooted_aux c hC h S₀ hnb hS₁ (M' := M) (fun r => ⟨fun hr => ⟨hr, fun heq => hρ ⟨_, heq⟩⟩, fun ⟨hr, _⟩ => hr⟩)
  obtain ⟨a, b, N, eV, eE, hiso⟩ := N₀.exists_fin_iso
  obtain ⟨-, k₂, k₃, k₄, k₅⟩ := hiso.invariants
  obtain ⟨g, hg⟩ := hiso.exists_blobbedTree_iso
  have hd := (k₃ M).2 h₂
  have hfd := (k₅ _).2 h₄
  have hiso' : ∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩ := by
    refine ⟨g.trans f₀, fun v r hr hv hvr => ?_⟩
    obtain ⟨v, rfl⟩ := eV.surjective v
    change f₀ (g (N.toBlobNode (eV v))) = _
    rw [hg]
    refine hrow v r hr ((hiso.isLeaf v).1 hv) ?_
    rw [← hvr, hiso.label]
  obtain ⟨he, -, -⟩ := (theorem4_iff hd hfd h).1 hiso'
  obtain ⟨hee, hr, hdeg⟩ := (theorem4_entry hd hfd h).1 hiso'
  refine ⟨a, b, N, (k₂ c).2 h₁, hd, k₄.trans h₃, hfd, he, hee, hr, hdeg, g.trans f₀, fun v r hr hv hvr => ?_, ?_⟩
  · obtain ⟨v, rfl⟩ := eV.surjective v
    change f₀ (g (N.toBlobNode (eV v))) = _
    rw [hg]
    refine hrow v r hr ((hiso.isLeaf v).1 hv) ?_
    rw [← hvr, hiso.label]
  · have hrt : N.root = eV N₀.root := hiso.root
    change f₀ (g (N.toBlobNode N.root)) = _
    rw [hrt, hg, hroot]

/-- **Line 299, with the root at a row** (`g:root_row`). "Let `S` be the label written at node `v_r`": the row `S` is at the root, and it has no leaf, so the network derives the other rows. `T′` is `T̄`, respecting the rows, with the root at the node of `S`. A network deriving all the rows can't do this: `root_not_mem_range`. -/
theorem exists_network_rooted_at_row (c : Crossover) (hC : NoConstantColumn M) (h : IsTBar M T φ edge) {S : ι → Bool} (hS : S ∈ M) (hne : ∃ r ∈ M, r ≠ S) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives (M.erase S) ∧ N.ancestral = S ∧ N.IsFullyDecomposedFor (incompatGraph M) ∧
      ∃ f : N.blobbedTree ≃g T, (∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) ∧ f (N.toBlobNode N.root) = φ ⟨S, hS⟩ := by
  have hinj : ∀ {r r' : M}, (r : ι → Bool) ≠ r' → φ r ≠ φ r' := fun {r r'} hr heq => hr (congrArg Subtype.val (h.label_injective heq))
  obtain ⟨r₁, hr₁, hr₁S⟩ := hne
  obtain ⟨y, hy, -⟩ := exists_adj_separating h.isTree (hinj (r := ⟨S, hS⟩) (r' := ⟨r₁, hr₁⟩) (Ne.symm hr₁S))
  have hlab : h.rootLabel (φ ⟨S, hS⟩) S = S := by
    funext i
    unfold rootLabel
    rw [ite_eq_right, h.lam_row ⟨S, hS⟩ i]
    rintro ⟨C, h₁, -⟩
    exact h.center_ne_root S hS C h₁
  obtain ⟨V, E, _, _, N₀, h₁, h₂, h₃, h₄, f₀, hrow, hroot⟩ := exists_rooted_aux c hC h (ρ := φ ⟨S, hS⟩) S ⟨y, hy⟩ hS (M' := M.erase S) (fun r => by
    rw [Finset.mem_erase]
    constructor
    · rintro ⟨hrS, hr⟩
      exact ⟨hr, hinj hrS⟩
    · rintro ⟨hr, hne⟩
      exact ⟨fun heq => hne (by subst heq; rfl), hr⟩)
  obtain ⟨a, b, N, eV, eE, hiso⟩ := N₀.exists_fin_iso
  obtain ⟨-, k₂, k₃, k₄, k₅⟩ := hiso.invariants
  obtain ⟨g, hg⟩ := hiso.exists_blobbedTree_iso
  refine ⟨a, b, N, (k₂ c).2 h₁, (k₃ _).2 h₂, k₄.trans (h₃.trans hlab), (k₅ _).2 h₄, g.trans f₀, fun v r hr hv hvr => ?_, ?_⟩
  · obtain ⟨v, rfl⟩ := eV.surjective v
    change f₀ (g (N.toBlobNode (eV v))) = _
    rw [hg]
    refine hrow v r hr ((hiso.isLeaf v).1 hv) ?_
    rw [← hvr, hiso.label]
  · have hrt : N.root = eV N₀.root := hiso.root
    change f₀ (g (N.toBlobNode N.root)) = _
    rw [hrt, hg, hroot]

omit [Finite ι] in
/-- **A network deriving all the rows can't have its root at a row** (`g:root_not_row`), if `T′` is `T̄`: the row's leaf would be on a blob with the root, or be the root. This is why `exists_network_rooted_at` excludes a row, and why `exists_network_rooted_at_row` derives the other rows. -/
theorem root_not_mem_range {V E : Type*} [Finite V] [Finite E] {N : Network ι V E} (hd : N.Derives M) (hf : N.IsFullyDecomposedFor (incompatGraph M)) (h : IsTBar M T φ edge)
    (h2 : 2 ≤ M.card) (f : N.blobbedTree ≃g T) (hfr : ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) : f (N.toBlobNode N.root) ∉ Set.range φ := by
  rintro ⟨⟨r, hr⟩, hrt⟩
  obtain ⟨l, hl, rfl⟩ := hd.surjOn hr
  have hclass : N.toBlobNode l = N.toBlobNode N.root := f.injective ((hfr l _ hr hl rfl).trans hrt)
  obtain ⟨-, hreg, -⟩ := (theorem4_entry hd hf h).1 ⟨f, hfr⟩
  rcases Network.eq_or_exists_isBlob_of_toBlobNode_eq hf.nodeDisjoint hclass with hlr | ⟨B, hB, hlB, -⟩
  · -- The root is a leaf, and so it's the only node.
    obtain ⟨r', hr', hne⟩ := Finset.exists_mem_ne (show 1 < M.card by omega) (N.label l)
    obtain ⟨l', hl', rfl⟩ := hd.surjOn hr'
    have hreach := N.reach_root l'
    rcases Relation.ReflTransGen.cases_head hreach with h₁ | ⟨b, ⟨e, he, -⟩, -⟩
    · rw [hlr, h₁] at hne
      exact hne rfl
    · exact hl e (he.trans hlr.symm)
  · exact hreg.recomb_not_leaf l (hB.isRecomb_of_isLeaf hlB hl) hl

end Network

end Gusfield2007
