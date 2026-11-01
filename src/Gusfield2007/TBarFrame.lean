module

public import Gusfield2007.SuperCharacters
public import Gusfield2007.GlueNet

/-!
# Gusfield et al. 2007: `T̄`, rooted at a row, as a frame for inflating its central nodes

Line 299: "we arbitrarily select a node `v_r` of `T̄` to be the root and direct all the edges in `T̄` away from that chosen root. Let `S` be the label written at node `v_r`."
This file gives each node of `T̄` its label (`IsTBar.lam`), directs the edges away from a row `S` (`IsTBar.par`), and makes `T̄` the data for `GlueData`, once each non-trivial
component has a network with ancestral sequence `S(C)` deriving the other super-characters. `IsTBar.exists_glued` is the network of the end of line 299.

The paper selects the root among all the nodes of `T̄`. Here it's always a row, which is a selection that the paper's proof allows, and it's what the rooted results need. It avoids
what line 416 notes: `S(C)` isn't defined when the root is the central node of `C`.

That each central node is the central node of one component, and that it's incident only to the edges of its component (line 277), is used here, where the paper takes both for granted.
-/

@[expose] public noncomputable section

open scoped Classical

namespace Gusfield2007

universe u v w

variable {ι : Type u} {M : Finset (ι → Bool)} {W : Type v} [Finite W] {T : SimpleGraph W} {φ : M → W}
  {edge : SuperChar M → Sym2 W}

namespace IsTBar

variable (h : IsTBar M T φ edge)

/-- The side function of a character: its "1-side" (line 271). -/
def side (k : SuperChar M) : W → Bool := (h.exists_side k).choose

theorem side_cut (k : SuperChar M) : IsCut T (edge k) (h.side k) := (h.exists_side k).choose_spec.1

theorem side_row (k : SuperChar M) (r : M) : h.side k (φ r) = charValue k (r : ι → Bool) := (h.exists_side k).choose_spec.2 r

/-- The central node of a component (Lemma 4). -/
def center (c : (incompatGraph M).ConnectedComponent) : W := (lemma4 h c).choose

theorem center_mem {c : (incompatGraph M).ConnectedComponent} {k : SuperChar M} (hk : k.1 = c) : h.center c ∈ edge k :=
  (lemma4 h c).choose_spec.1 k hk

theorem center_zero {c : (incompatGraph M).ConnectedComponent} (hc : c.supp.Nontrivial) {k : SuperChar M} (hk : k.1 = c) {r : M}
    (hr : charValue k (r : ι → Bool) = true) : ¬ SameSide T (edge k) (φ r) (h.center c) :=
  (lemma4 h c).choose_spec.2.1 hc k hk r hr

theorem side_center {c : (incompatGraph M).ConnectedComponent} (hc : c.supp.Nontrivial) {k : SuperChar M} (hk : k.1 = c) :
    h.side k (h.center c) = false := by
  obtain ⟨r, hr⟩ := exists_charValue_eq_true k
  have hne := fun heq => h.center_zero hc hk hr ((IsCut.sameSide_iff h.isTree.connected.preconnected (h.edge_mem k) (h.side_cut k)).2 heq)
  rw [h.side_row, hr] at hne
  cases h₁ : h.side k (h.center c)
  · rfl
  · simp [h₁] at hne

include h in
/-- Two characters from a trivial component label one edge. -/
theorem edge_eq_of_trivial {k k' : SuperChar M} (hne : k ≠ k') (hc : k.1 = k'.1) (ht : ¬ k.1.supp.Nontrivial) : edge k = edge k' := by
  refine h.edge_eq_of_split (h.edge_mem _) (h.edge_mem _) (h.side_cut k) (h.side_cut k') fun x y => ?_
  rw [h.side_row, h.side_row, h.side_row, h.side_row]
  have hx := charValue_ne_of_trivial hne hc ht (x : ι → Bool)
  have hy := charValue_ne_of_trivial hne hc ht (y : ι → Bool)
  revert hx hy
  cases charValue k (x : ι → Bool) <;> cases charValue k' (x : ι → Bool) <;>
    cases charValue k (y : ι → Bool) <;> cases charValue k' (y : ι → Bool) <;> simp

/-- Two characters from a trivial component have opposite sides. -/
theorem side_ne_of_trivial {k k' : SuperChar M} (hne : k ≠ k') (hc : k.1 = k'.1) (ht : ¬ k.1.supp.Nontrivial) (v : W) :
    h.side k v = !h.side k' v := by
  have hcut := h.side_cut k'
  rw [← edge_eq_of_trivial h hne hc ht] at hcut
  rcases IsCut.eq_or_eq_not h.isTree (h.edge_mem k) (h.side_cut k) hcut with hall | hall
  · exfalso
    obtain ⟨r, hr⟩ := exists_charValue_eq_true k
    have h₁ := hall (φ r)
    rw [h.side_row, h.side_row, hr] at h₁
    exact charValue_disjoint hne hc hr h₁.symm
  · exact hall v

/-- Two sides of one component don't meet (line 283), for a node as for a row. -/
theorem side_unique {k k' : SuperChar M} (hc : k.1 = k'.1) {v : W} (h₁ : h.side k v = true) (h₂ : h.side k' v = true) : k = k' := by
  by_contra hne
  exact h.not_both_one hne hc (h.side_cut k) (h.side_cut k') (h.side_row k) (h.side_row k') v ⟨h₁, h₂⟩

/-- Each node other than the central one of a component is on the 1-side of a character of the component. -/
theorem exists_side_true (hC : NoConstantColumn M) (c : (incompatGraph M).ConnectedComponent) {v : W}
    (hv : c.supp.Nontrivial → v ≠ h.center c) : ∃ k : SuperChar M, k.1 = c ∧ h.side k v = true := by
  have hconn := h.isTree.connected.preconnected
  by_cases hnt : c.supp.Nontrivial
  · obtain ⟨w, hw, hsep, -⟩ := exists_adj_separating h.isTree (hv hnt).symm
    obtain ⟨k, hk, he⟩ := adj_center_labelled h hnt (fun k hk => h.center_mem hk)
      (fun k hk r hr => h.center_zero hnt hk hr) hw
    refine ⟨k, hk, ?_⟩
    have hz := h.side_center hnt hk
    have hcut : IsCut T s(h.center c, w) (h.side k) := he ▸ h.side_cut k
    cases h₁ : h.side k v
    · exact absurd (hcut.sameSide_of_eq hconn hw (hz.trans h₁.symm)) hsep
    · rfl
  · obtain ⟨i, rfl⟩ := c.exists_rep
    obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ := hC i
    have hm₁ : ((incompatGraph M).connectedComponentMk i).supp.domRestrict r₁ ∈ restrictRows ((incompatGraph M).connectedComponentMk i).supp M :=
      mem_restrictRows.2 ⟨r₁, hr₁, rfl⟩
    have hm₂ : ((incompatGraph M).connectedComponentMk i).supp.domRestrict r₂ ∈ restrictRows ((incompatGraph M).connectedComponentMk i).supp M :=
      mem_restrictRows.2 ⟨r₂, hr₂, rfl⟩
    have hkk : (⟨_, ⟨_, hm₁⟩⟩ : SuperChar M) ≠ ⟨_, ⟨_, hm₂⟩⟩ := by
      intro heq
      have h₃ := eq_of_heq (Sigma.mk.inj_iff.1 heq).2
      have h₄ := congrFun (congrArg Subtype.val h₃) ⟨i, rfl⟩
      exact hne h₄
    have hs := h.side_ne_of_trivial hkk rfl hnt v
    cases h₁ : h.side ⟨_, ⟨_, hm₂⟩⟩ v
    · rw [h₁] at hs
      exact ⟨_, rfl, hs⟩
    · exact ⟨_, rfl, h₁⟩

/-- The state of a character's super-character at a site. -/
def valueAt (k : SuperChar M) (i : ι) : Bool := if hi : i ∈ k.1.supp then k.2.1 ⟨i, hi⟩ else false

theorem valueAt_of_charValue {k : SuperChar M} {r : ι → Bool} (hr : charValue k r = true) {i : ι} (hi : i ∈ k.1.supp) : valueAt k i = r i := by
  obtain ⟨c, S⟩ := k
  have h₁ := charValue_mk_iff.1 hr
  unfold valueAt
  simp only [hi, ↓reduceDIte]
  rw [← h₁]
  rfl

/-- The label of a node of `T̄`, on a site `i`: the state at `i` of the super-character of the component of `i` whose 1-side contains the node. So it's the row, at a row (line 299: "a
perfect phylogeny is a phylogenetic network and so each node is labeled"). -/
def lam (v : W) (i : ι) : Bool :=
  if hk : ∃ k : SuperChar M, k.1 = (incompatGraph M).connectedComponentMk i ∧ h.side k v = true then valueAt hk.choose i else false

theorem lam_eq {k : SuperChar M} {i : ι} {v : W} (hk : k.1 = (incompatGraph M).connectedComponentMk i) (hv : h.side k v = true) :
    h.lam v i = valueAt k i := by
  have hex : ∃ k : SuperChar M, k.1 = (incompatGraph M).connectedComponentMk i ∧ h.side k v = true := ⟨k, hk, hv⟩
  have heq : hex.choose = k := h.side_unique (hex.choose_spec.1.trans hk.symm) hex.choose_spec.2 hv
  unfold lam
  rw [dite_eq_left hex, heq]

/-- The super-character of a row, as a character. -/
def charOf (c : (incompatGraph M).ConnectedComponent) {r : ι → Bool} (hr : r ∈ M) : SuperChar M :=
  ⟨c, ⟨c.supp.domRestrict r, mem_restrictRows.2 ⟨r, hr, rfl⟩⟩⟩

theorem charValue_charOf (c : (incompatGraph M).ConnectedComponent) {r : ι → Bool} (hr : r ∈ M) : charValue (charOf c hr) r = true :=
  charValue_mk_iff.2 rfl

theorem lam_row (r : M) (i : ι) : h.lam (φ r) i = (r : ι → Bool) i := by
  have hk := charValue_charOf ((incompatGraph M).connectedComponentMk i) r.2
  rw [h.lam_eq (k := charOf _ r.2) rfl (by rw [h.side_row]; exact hk)]
  exact valueAt_of_charValue hk rfl

/-! ### The tree rooted at a node -/

variable (ρ : W)

/-- The parent, towards the root. -/
def par (b : W) : W := if hb : b = ρ then ρ else (exists_adj_separating h.isTree hb).choose

variable {ρ}

omit [Finite W] in
theorem par_spec {b : W} (hb : b ≠ ρ) : T.Adj b (h.par ρ b) ∧ ¬ SameSide T s(b, h.par ρ b) b ρ ∧ T.dist (h.par ρ b) ρ < T.dist b ρ := by
  have hspec := (exists_adj_separating h.isTree hb).choose_spec
  have heq : h.par ρ b = (exists_adj_separating h.isTree hb).choose := by
    unfold par
    rw [dite_eq_right hb]
  rw [heq]
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.2⟩

omit [Finite W] in
theorem par_unique {a b : W} (hab : T.Adj b a) (hsep : ¬ SameSide T s(b, a) b ρ) : a = h.par ρ b := by
  have hconn := h.isTree.connected.preconnected
  have nb : ∀ {α β : Bool}, α ≠ β → β = !α := by decide
  have hb : b ≠ ρ := by
    rintro rfl
    exact hsep (SimpleGraph.Reachable.refl _)
  obtain ⟨hp, hpsep, -⟩ := h.par_spec hb
  by_contra hne
  obtain ⟨c, hc⟩ := exists_isCut h.isTree (show s(b, a) ∈ T.edgeSet from hab)
  obtain ⟨c', hc'⟩ := exists_isCut h.isTree (show s(b, h.par ρ b) ∈ T.edgeSet from hp)
  have hee : s(b, a) ≠ s(b, h.par ρ b) := by
    intro heq
    rcases Sym2.eq_iff.1 heq with ⟨-, h'⟩ | ⟨h₁, -⟩
    · exact hne h'
    · exact T.ne_of_adj hp h₁
  have h₁ : c b ≠ c a := hc.ne_self hab
  have h₂ : c' b ≠ c' (h.par ρ b) := hc'.ne_self hp
  have h₃ : c' b = c' a := hc'.eq_of_ne hab hee
  have h₄ : c b = c (h.par ρ b) := hc.eq_of_ne hp (Ne.symm hee)
  have h₅ : c b ≠ c ρ := fun heq => hsep (hc.sameSide_of_eq hconn hab heq)
  have h₆ : c' b ≠ c' ρ := fun heq => hpsep (hc'.sameSide_of_eq hconn hp heq)
  exact IsCut.not_fourth hconn hc hc' hab hp hee (a := c b) (b := c' b) (x := b) (y := h.par ρ b) (z := a) (w := ρ)
    ⟨rfl, rfl⟩ ⟨h₄.symm, nb h₂⟩ ⟨nb h₁, h₃.symm⟩ ⟨nb h₅, nb h₆⟩

omit [Finite W] in
/-- An edge joins a node and its parent. -/
theorem adj_cases {x y : W} (hxy : T.Adj x y) : (y ≠ ρ ∧ x = h.par ρ y) ∨ (x ≠ ρ ∧ y = h.par ρ x) := by
  have hconn := h.isTree.connected.preconnected
  obtain ⟨c, hc⟩ := exists_isCut h.isTree (show s(x, y) ∈ T.edgeSet from hxy)
  have hne := hc.ne_self hxy
  have hcs : c x = c ρ ∨ c y = c ρ := by
    revert hne
    cases c x <;> cases c y <;> cases c ρ <;> simp
  rcases hcs with hx | hy
  · left
    have hy₁ : ¬ SameSide T s(y, x) y ρ := by
      rw [Sym2.eq_swap]
      intro hsame
      have h₁ := hc.eq_of_sameSide hsame
      exact hne (hx.trans h₁.symm)
    refine ⟨?_, h.par_unique hxy.symm hy₁⟩
    rintro rfl
    exact hy₁ (SimpleGraph.Reachable.refl _)
  · right
    have hx₁ : ¬ SameSide T s(x, y) x ρ := fun hsame => hne ((hc.eq_of_sameSide hsame).trans hy.symm)
    refine ⟨?_, h.par_unique hxy hx₁⟩
    rintro rfl
    exact hx₁ (SimpleGraph.Reachable.refl _)

/-! ### The frame -/

section Frame

open Decomp

variable {Vp Ep : Cent (incompatGraph M) → Type w}
  (P : ∀ C : Cent (incompatGraph M), Network C.1.supp (Vp C) (Ep C)) (S : ι → Bool) (hS : S ∈ M)

/-- The arc into `b` leaves the network of its parent from a leaf with the super-character of that edge. -/
def exitNode (C : Cent (incompatGraph M)) (b : W) : Vp C :=
  if hx : ∃ l, (P C).IsLeaf l ∧ ∃ k : SuperChar M, k.1 = C.1 ∧ edge k = s(h.center C.1, b) ∧
      ∀ j : C.1.supp, (P C).label l j = valueAt k j.1 then hx.choose else (P C).root

omit [Finite W] in
/-- The lower end of an edge. -/
theorem exists_child (ρ : W) {e : Sym2 W} (he : e ∈ T.edgeSet) : ∃ b, b ≠ ρ ∧ e = s(h.par ρ b, b) := by
  induction e with
  | h x y =>
    rcases h.adj_cases (ρ := ρ) he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨y, h₁, by rw [← h₂]⟩
    · exact ⟨x, h₁, by rw [← h₂, Sym2.eq_swap]⟩

/-- The node of `T̄` below the edge of the character of a site, with the state of `S`. -/
def siteNode (ρ : W) (i : ι) : W :=
  (h.exists_child ρ (h.edge_mem (charOf ((incompatGraph M).connectedComponentMk i) hS))).choose

include hS in
theorem center_ne_root (C : Cent (incompatGraph M)) : h.center C.1 ≠ φ ⟨S, hS⟩ := by
  intro heq
  have h₁ := h.side_center C.2 (k := charOf C.1 hS) rfl
  rw [heq, h.side_row] at h₁
  rw [show charValue (charOf C.1 hS) S = true from charValue_charOf C.1 hS] at h₁
  exact absurd h₁ (by simp)

theorem center_injective (C C' : Cent (incompatGraph M)) (heq : h.center C.1 = h.center C'.1) : C = C' := by
  by_contra hne
  have hne' : C.1 ≠ C'.1 := fun h' => hne (Subtype.ext h')
  refine h.center_ne hne' C.2 (v := h.center C.1) (fun k hk => h.center_mem hk) (fun k hk r hr => h.center_zero C.2 hk hr)
    (fun k hk => heq ▸ h.center_mem hk) (fun k hk r hr => heq ▸ h.center_zero C'.2 hk hr)

/-- `T̄`, rooted at `S`, as data for gluing. -/
def frame : GlueData P W where
  ρ := φ ⟨S, hS⟩
  par := h.par (φ ⟨S, hS⟩)
  depth b := T.dist b (φ ⟨S, hS⟩)
  depth_par _ hb := (h.par_spec hb).2.2
  center C := h.center C.1
  center_inj C C' heq := h.center_injective C C' heq
  center_ne C := h.center_ne_root S hS C
  lam := h.lam
  exit C b := h.exitNode P C b
  treeSite i := h.siteNode S hS (φ ⟨S, hS⟩) i
  treeSite_ne i _ := (h.exists_child (φ ⟨S, hS⟩) (h.edge_mem (charOf ((incompatGraph M).connectedComponentMk i) hS))).choose_spec.1

/-- The characters of the edge from a central node to a child: they have the 1-side of the child. -/
theorem exists_exit_char {C : Cent (incompatGraph M)} {b : W} (hb : b ≠ φ ⟨S, hS⟩) (hpar : h.par (φ ⟨S, hS⟩) b = h.center C.1) :
    ∃ k : SuperChar M, k.1 = C.1 ∧ edge k = s(h.center C.1, b) ∧ h.side k b = true ∧ h.side k (φ ⟨S, hS⟩) = false := by
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
  cases h₁ : h.side k (φ ⟨S, hS⟩)
  · rfl
  · exfalso
    apply hsep
    rw [Sym2.eq_swap]
    exact hcut.sameSide_of_eq h.isTree.connected.preconnected hadj.symm (hb₁.trans h₁.symm)

variable (hanc : ∀ C, (P C).ancestral = C.1.supp.domRestrict S)
  (hder : ∀ C, (P C).Derives ((restrictRows C.1.supp M).erase (C.1.supp.domRestrict S)))

include hder in
/-- A central node's exits are leaves with the super-characters of their edges. -/
theorem exitNode_spec {C : Cent (incompatGraph M)} {b : W} (hb : b ≠ φ ⟨S, hS⟩) (hpar : h.par (φ ⟨S, hS⟩) b = h.center C.1) :
    (P C).IsLeaf (h.exitNode P C b) ∧ ∃ k : SuperChar M, k.1 = C.1 ∧ edge k = s(h.center C.1, b) ∧
      ∀ j : C.1.supp, (P C).label (h.exitNode P C b) j = valueAt k j.1 := by
  obtain ⟨k, hk, he, -, hρ⟩ := h.exists_exit_char S hS hb hpar
  have hex : ∃ l, (P C).IsLeaf l ∧ ∃ k : SuperChar M, k.1 = C.1 ∧ edge k = s(h.center C.1, b) ∧
      ∀ j : C.1.supp, (P C).label l j = valueAt k j.1 := by
    obtain ⟨c, t⟩ := k
    obtain rfl : c = C.1 := hk
    have hne : t.1 ≠ C.1.supp.domRestrict S := by
      intro heq
      rw [h.side_row] at hρ
      have := charValue_mk_iff (M := M) (c := C.1) (S := t) (r := S) |>.2 heq.symm
      change charValue (⟨C.1, t⟩ : SuperChar M) S = false at hρ
      rw [this] at hρ
      exact absurd hρ (by simp)
    obtain ⟨l, hl, hlab⟩ := (hder C).surjOn (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hne, t.2⟩))
    refine ⟨l, hl, ⟨C.1, t⟩, rfl, he, fun j => ?_⟩
    rw [hlab]
    unfold valueAt
    simp only [j.2, ↓reduceDIte]
  unfold exitNode
  rw [dite_eq_left hex]
  exact hex.choose_spec

include hder hanc in
/-- The labels agree at the ends of the edges of `T̄`, but for the sites on them. -/
theorem frame_valid (hC : NoConstantColumn M) : (h.frame P S hS).Valid := by
  have hT := h.isTree
  have hconn := hT.connected.preconnected
  set D := h.frame P S hS with hD
  -- The labels at the two ends of an edge of the tree.
  have hin : ∀ b i, D.nodeLabel (D.inNode b) i =
      if ∃ C : Cent (incompatGraph M), b = h.center C.1 ∧ i ∈ C.1.supp then S i else h.lam b i := by
    intro b i
    by_cases hbc : b ∈ Set.range D.center
    · obtain ⟨C, rfl⟩ := hbc
      rw [D.inNode_center]
      by_cases hi : i ∈ C.1.supp
      · have h₁ : ∃ C' : Cent (incompatGraph M), D.center C = h.center C'.1 ∧ i ∈ C'.1.supp := ⟨C, rfl, hi⟩
        rw [ite_eq_left h₁]
        simp only [GlueData.nodeLabel, hi, ↓reduceDIte]
        have := congrFun (hanc C) ⟨i, hi⟩
        exact this
      · have h₁ : ¬ ∃ C' : Cent (incompatGraph M), D.center C = h.center C'.1 ∧ i ∈ C'.1.supp := by
          rintro ⟨C', h₂, h₃⟩
          obtain rfl := h.center_injective C C' h₂
          exact hi h₃
        rw [ite_eq_right h₁]
        simp only [GlueData.nodeLabel, hi, ↓reduceDIte]
        rfl
    · have h₁ : ¬ ∃ C : Cent (incompatGraph M), b = h.center C.1 ∧ i ∈ C.1.supp := by
        rintro ⟨C, rfl, -⟩
        exact hbc ⟨C, rfl⟩
      rw [D.inNode_of_not hbc, ite_eq_right h₁]
      rfl
  have hout₁ : ∀ {b i} {C : Cent (incompatGraph M)}, b ≠ φ ⟨S, hS⟩ → h.par (φ ⟨S, hS⟩) b = h.center C.1 → i ∈ C.1.supp →
      ∃ k : SuperChar M, k.1 = C.1 ∧ edge k = s(h.center C.1, b) ∧ D.nodeLabel (D.outNode b) i = valueAt k i := by
    intro b i C hb hpar hi
    obtain ⟨-, k, hk, he, hl⟩ := h.exitNode_spec P S hS hder hb hpar
    refine ⟨k, hk, he, ?_⟩
    rw [D.outNode_center hpar]
    simp only [GlueData.nodeLabel, hi, ↓reduceDIte]
    exact hl ⟨i, hi⟩
  have hout₂ : ∀ {b i}, (¬ ∃ C : Cent (incompatGraph M), h.par (φ ⟨S, hS⟩) b = h.center C.1 ∧ i ∈ C.1.supp) →
      D.nodeLabel (D.outNode b) i = h.lam (h.par (φ ⟨S, hS⟩) b) i := by
    intro b i hno
    by_cases hbc : D.par b ∈ Set.range D.center
    · obtain ⟨C, hC'⟩ := hbc
      rw [D.outNode_center hC'.symm]
      have hi : i ∉ C.1.supp := fun hi => hno ⟨C, hC'.symm, hi⟩
      simp only [GlueData.nodeLabel, hi, ↓reduceDIte]
      exact congrArg (fun v => h.lam v i) hC'
    · rw [D.outNode_of_not hbc]
      rfl
  -- The other sites of a component.
  have hnontriv : ∀ (b : W) (hb : b ≠ φ ⟨S, hS⟩) (i : ι), ((incompatGraph M).connectedComponentMk i).supp.Nontrivial →
      D.nodeLabel (D.inNode b) i = D.nodeLabel (D.outNode b) i := by
    intro b hb i hnt
    obtain ⟨hadj, hsep, -⟩ := h.par_spec hb
    let C : Cent (incompatGraph M) := ⟨_, hnt⟩
    have hiC : i ∈ C.1.supp := rfl
    have honly : ∀ (C' : Cent (incompatGraph M)), i ∈ C'.1.supp → C' = C := fun C' hi => Subtype.ext (Eq.symm hi)
    rw [hin]
    by_cases ha : h.par (φ ⟨S, hS⟩) b = h.center C.1
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
    · rw [hout₂ (by
        rintro ⟨C', h₂, h₃⟩
        rw [honly C' h₃] at h₂
        exact ha h₂)]
      by_cases hbc : b = h.center C.1
      · -- The child is the central node: the edge has the character of `S`.
        have h₁ : ∃ C' : Cent (incompatGraph M), b = h.center C'.1 ∧ i ∈ C'.1.supp := ⟨C, hbc, hiC⟩
        rw [ite_eq_left h₁]
        have hrow := charValue_charOf C.1 hS
        have hzero : h.side (charOf C.1 hS) (h.center C.1) = false := h.side_center C.2 rfl
        have hρ : h.side (charOf C.1 hS) (φ ⟨S, hS⟩) = true := by
          rw [h.side_row]
          exact hrow
        obtain ⟨a', b', he', hab', ha', hb'⟩ := h.exists_ends (charOf C.1 hS) (h.side_cut _)
        -- The end on the 0-side is the central node.
        have hcen : a' = h.center C.1 := by
          have hmem : h.center C.1 ∈ edge (charOf C.1 hS) := h.center_mem rfl
          rw [he'] at hmem
          rcases Sym2.mem_iff.1 hmem with h₃ | h₃
          · exact h₃.symm
          · rw [← h₃, hzero] at hb'
            exact absurd hb' (by simp)
        subst hcen
        have hsep' : ¬ SameSide T s(h.center C.1, b') (h.center C.1) (φ ⟨S, hS⟩) := by
          intro hsame
          have hcut : IsCut T s(h.center C.1, b') (h.side (charOf C.1 hS)) := he' ▸ h.side_cut _
          have := hcut.eq_of_sameSide hsame
          rw [ha', hρ] at this
          exact absurd this (by simp)
        have hpar := h.par_unique hab' hsep'
        have h₂ : b' = h.par (φ ⟨S, hS⟩) b := by rw [hbc]; exact hpar
        rw [← h₂, h.lam_eq (k := charOf C.1 hS) rfl hb']
        exact (valueAt_of_charValue hrow hiC).symm
      · -- Neither end is the central node.
        have h₁ : ¬ ∃ C' : Cent (incompatGraph M), b = h.center C'.1 ∧ i ∈ C'.1.supp := by
          rintro ⟨C', h₂, h₃⟩
          rw [honly C' h₃] at h₂
          exact hbc h₂
        rw [ite_eq_right h₁]
        obtain ⟨k, hk, hk₁⟩ := h.exists_side_true hC C.1 (v := h.par (φ ⟨S, hS⟩) b) (fun _ => ha)
        have hne : s(b, h.par (φ ⟨S, hS⟩) b) ≠ edge k := by
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
  have htrivial : ∀ (b : W) (hb : b ≠ φ ⟨S, hS⟩) (i : ι), ¬ ((incompatGraph M).connectedComponentMk i).supp.Nontrivial →
      (D.nodeLabel (D.inNode b) i = h.lam b i) ∧ D.nodeLabel (D.outNode b) i = h.lam (h.par (φ ⟨S, hS⟩) b) i := by
    intro b hb i hnt
    have hno : ∀ C : Cent (incompatGraph M), i ∉ C.1.supp := fun C hi => hnt (by
      have : (incompatGraph M).connectedComponentMk i = C.1 := hi
      rw [this]
      exact C.2)
    constructor
    · rw [hin, ite_eq_right]
      rintro ⟨C, -, h₃⟩
      exact hno C h₃
    · exact hout₂ (by
        rintro ⟨C, -, h₃⟩
        exact hno C h₃)
  -- The two characters of a trivial component.
  have htwo : ∀ (i : ι), ¬ ((incompatGraph M).connectedComponentMk i).supp.Nontrivial →
      ∃ k' : SuperChar M, k' ≠ charOf ((incompatGraph M).connectedComponentMk i) hS ∧ k'.1 = (incompatGraph M).connectedComponentMk i ∧
        valueAt k' i = !valueAt (charOf ((incompatGraph M).connectedComponentMk i) hS) i := by
    intro i hnt
    obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ := hC i
    have hr : ∃ r ∈ M, r i ≠ S i := by
      by_cases h₁ : r₁ i = S i
      · refine ⟨r₂, hr₂, fun h₂ => hne (h₁.trans h₂.symm)⟩
      · exact ⟨r₁, hr₁, h₁⟩
    obtain ⟨r, hrM, hrS⟩ := hr
    have hv₁ := valueAt_of_charValue (charValue_charOf ((incompatGraph M).connectedComponentMk i) hrM) (i := i) rfl
    have hv₂ := valueAt_of_charValue (charValue_charOf ((incompatGraph M).connectedComponentMk i) hS) (i := i) rfl
    refine ⟨charOf ((incompatGraph M).connectedComponentMk i) hrM, fun heq => ?_, rfl, ?_⟩
    · rw [heq, hv₂] at hv₁
      exact hrS hv₁.symm
    · rw [hv₁, hv₂]
      revert hrS
      cases r i <;> cases S i <;> simp
  constructor
  · -- The site's edge.
    intro b hb i hsite
    have hnt : ¬ ((incompatGraph M).connectedComponentMk i).supp.Nontrivial := by
      intro hnt
      rw [hsiteval, dite_eq_left hnt] at hsite
      simp at hsite
    obtain ⟨h₁, h₂⟩ := htrivial b hb i hnt
    rw [h₁, h₂]
    rw [hsiteval, dite_eq_right hnt] at hsite
    have hb₀ : D.treeSite i = b := by
      simpa using hsite
    obtain ⟨k', hk', hk'c, hval⟩ := htwo i hnt
    have hspec := (h.exists_child (φ ⟨S, hS⟩) (h.edge_mem (charOf ((incompatGraph M).connectedComponentMk i) hS))).choose_spec
    have he : edge (charOf ((incompatGraph M).connectedComponentMk i) hS) = s(h.par (φ ⟨S, hS⟩) b, b) := by
      rw [← hb₀]
      exact hspec.2
    obtain ⟨hadj, -, -⟩ := h.par_spec hb
    have hcut : IsCut T s(h.par (φ ⟨S, hS⟩) b, b) (h.side (charOf ((incompatGraph M).connectedComponentMk i) hS)) := he ▸ h.side_cut _
    have hne := hcut.ne_self hadj.symm
    have hopp : ∀ v, h.side k' v = !h.side (charOf ((incompatGraph M).connectedComponentMk i) hS) v :=
      h.side_ne_of_trivial hk' hk'c (by rw [hk'c]; exact hnt)
    cases h₃ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS) (h.par (φ ⟨S, hS⟩) b)
    · -- The parent is on the other character's 1-side.
      have h₄ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS) b = true := by
        rw [h₃] at hne
        cases h₅ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS) b
        · simp [h₅] at hne
        · rfl
      rw [h.lam_eq (k := charOf ((incompatGraph M).connectedComponentMk i) hS) rfl h₄, h.lam_eq hk'c (by rw [hopp, h₃]; rfl), hval]
      simp
    · have h₄ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS) b = false := by
        rw [h₃] at hne
        cases h₅ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS) b
        · rfl
        · simp [h₅] at hne
      rw [h.lam_eq (k := charOf ((incompatGraph M).connectedComponentMk i) hS) rfl h₃, h.lam_eq hk'c (by rw [hopp, h₄]; rfl), hval]
  · intro b hb i hsite
    by_cases hnt : ((incompatGraph M).connectedComponentMk i).supp.Nontrivial
    · exact hnontriv b hb i hnt
    · obtain ⟨h₁, h₂⟩ := htrivial b hb i hnt
      rw [h₁, h₂]
      have hb₀ : D.treeSite i ≠ b := by
        intro heq
        apply hsite
        rw [hsiteval, dite_eq_right hnt]
        congr 1
        exact Subtype.ext heq
      obtain ⟨k', hk', hk'c, -⟩ := htwo i hnt
      have hspec := (h.exists_child (φ ⟨S, hS⟩) (h.edge_mem (charOf ((incompatGraph M).connectedComponentMk i) hS))).choose_spec
      obtain ⟨hadj, -, hdist⟩ := h.par_spec hb
      have hne : s(b, h.par (φ ⟨S, hS⟩) b) ≠ edge (charOf ((incompatGraph M).connectedComponentMk i) hS) := by
        intro heq
        rw [hspec.2] at heq
        change s(b, h.par (φ ⟨S, hS⟩) b) = s(h.par (φ ⟨S, hS⟩) (D.treeSite i), D.treeSite i) at heq
        rcases Sym2.eq_iff.1 heq with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
        · have h₅ := (h.par_spec (b := D.treeSite i) hspec.1).2.2
          rw [← h₃, ← h₄] at h₅
          exact lt_asymm hdist h₅
        · exact hb₀ h₃.symm
      have heq := (h.side_cut (charOf ((incompatGraph M).connectedComponentMk i) hS)).eq_of_ne hadj hne
      have hopp : ∀ v, h.side k' v = !h.side (charOf ((incompatGraph M).connectedComponentMk i) hS) v :=
        h.side_ne_of_trivial hk' hk'c (by rw [hk'c]; exact hnt)
      cases h₃ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS) (h.par (φ ⟨S, hS⟩) b)
      · have h₄ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS) b = false := heq.trans h₃
        rw [h.lam_eq hk'c (by rw [hopp, h₄]; rfl), h.lam_eq hk'c (by rw [hopp, h₃]; rfl)]
      · have h₄ : h.side (charOf ((incompatGraph M).connectedComponentMk i) hS) b = true := heq.trans h₃
        rw [h.lam_eq (k := charOf ((incompatGraph M).connectedComponentMk i) hS) rfl h₄, h.lam_eq (k := charOf ((incompatGraph M).connectedComponentMk i) hS) rfl h₃]

include hder in
/-- The leaves of the glued network are the rows other than `S`. -/
theorem frame_derives (hD : (h.frame P S hS).Valid) (hne : ∃ r ∈ M, r ≠ S) :
    ((h.frame P S hS).net hD).Derives (M.erase S) := by
  have hT := h.isTree
  have hconn := hT.connected.preconnected
  have hρS : ∀ {r : M}, (r : ι → Bool) ≠ S → φ r ≠ φ ⟨S, hS⟩ := fun {r} hr heq => hr (congrArg Subtype.val (h.label_injective heq))
  set D := h.frame P S hS with hDdef
  have hnotcen : ∀ r : M, φ r ∉ Set.range D.center := by
    rintro r ⟨C, hC'⟩
    have hz : h.side (charOf C.1 r.2) (h.center C.1) = false := h.side_center C.2 rfl
    have hC'' : h.center C.1 = φ r := hC'
    rw [hC'', h.side_row] at hz
    rw [show charValue (charOf C.1 r.2) (r : ι → Bool) = true from charValue_charOf C.1 r.2] at hz
    exact absurd hz (by simp)
  -- A node with no child is a row.
  have hchild : ∀ v, v ≠ φ ⟨S, hS⟩ → (∀ b, b ≠ φ ⟨S, hS⟩ → h.par (φ ⟨S, hS⟩) b ≠ v) → v ∈ Set.range φ := by
    intro v hv hno
    rw [h.mem_range_iff, Set.ncard_le_one (Set.toFinite _)]
    intro a ha c hc
    have hval : ∀ {u}, T.Adj v u → u = h.par (φ ⟨S, hS⟩) v := by
      intro u hu
      rcases h.adj_cases (ρ := φ ⟨S, hS⟩) hu with ⟨h₁, h₂⟩ | ⟨-, h₂⟩
      · exact absurd h₂.symm (hno u h₁)
      · exact h₂
    rw [hval ha, hval hc]
  -- The root has a child.
  have hroot : ∃ b, b ≠ φ ⟨S, hS⟩ ∧ h.par (φ ⟨S, hS⟩) b = φ ⟨S, hS⟩ := by
    obtain ⟨r, hr, hrS⟩ := hne
    obtain ⟨w, hw, -⟩ := exists_adj_separating hT (hρS (r := ⟨r, hr⟩) hrS).symm
    rcases h.adj_cases (ρ := φ ⟨S, hS⟩) hw with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
    · exact ⟨w, h₁, h₂.symm⟩
    · exact absurd rfl h₁
  -- A leaf of a network has an exit.
  have hnoinr : ∀ (C : Cent (incompatGraph M)) (x : Vp C), ¬ (D.net hD).IsLeaf (.inr ⟨C, x⟩) := by
    intro C x hx
    obtain ⟨hl, hexit⟩ := Decomp.GlueData.isLeaf_net_inr hD hx
    have hmem := (hder C).mapsTo hl
    obtain ⟨hne₁, hmem₁⟩ := Finset.mem_erase.1 (Finset.mem_coe.1 hmem)
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
    have hρ : h.side k (φ ⟨S, hS⟩) = false := by
      rw [h.side_row]
      cases h₁ : charValue k S
      · rfl
      · exact absurd (charValue_mk_iff.1 h₁).symm hne₁
    have hcut : IsCut T s(h.center C.1, b') (h.side k) := he' ▸ h.side_cut k
    have hsep : ¬ SameSide T s(b', h.center C.1) b' (φ ⟨S, hS⟩) := by
      rw [Sym2.eq_swap]
      intro hsame
      have := hcut.eq_of_sameSide hsame
      rw [hb', hρ] at this
      exact absurd this (by simp)
    have hbne : b' ≠ φ ⟨S, hS⟩ := by
      rintro rfl
      exact hsep (SimpleGraph.Reachable.refl _)
    have hpar : h.par (φ ⟨S, hS⟩) b' = h.center C.1 := (h.par_unique hab'.symm hsep).symm
    obtain ⟨hl₂, k', hk', he₂, hval⟩ := h.exitNode_spec P S hS hder hbne hpar
    have hkk : k' = k := by
      by_contra hne₂
      exact h.edge_ne hne₂ hk' (hk' ▸ C.2) (he₂.trans he'.symm)
    subst hkk
    have hlab : (P C).label (h.exitNode P C b') = (P C).label x := by
      funext j
      rw [hval j]
      unfold valueAt
      rw [dite_eq_left (show j.1 ∈ k.1.supp from j.2)]
    exact hexit b' hbne hpar ((hder C).injOn hl₂ hl hlab)
  have hleaf : ∀ y, (D.net hD).IsLeaf y → ∃ r : M, (r : ι → Bool) ≠ S ∧ y = .inl ⟨φ r, hnotcen r⟩ := by
    intro y hy
    cases y with
    | inl v =>
      have hno := (Decomp.GlueData.isLeaf_net_inl hD v).1 hy
      have hvρ : v.1 ≠ φ ⟨S, hS⟩ := by
        intro heq
        obtain ⟨b, hb, hpar⟩ := hroot
        exact hno b hb (hpar.trans heq.symm)
      obtain ⟨r, hr⟩ := hchild v.1 hvρ hno
      refine ⟨r, fun hrS => hvρ ?_, ?_⟩
      · rw [← hr]
        congr 1
        exact Subtype.ext hrS
      · congr 1
        exact Subtype.ext hr.symm
    | inr y =>
      obtain ⟨C, x⟩ := y
      exact absurd hy (hnoinr C x)
  have hlabel : ∀ r : M, (D.net hD).label (.inl ⟨φ r, hnotcen r⟩) = (r : ι → Bool) := fun r => by
    funext i
    exact h.lam_row r i
  refine ⟨fun y hy => ?_, fun a ha b hb hab => ?_, fun r hr => ?_⟩
  · obtain ⟨r, hrS, rfl⟩ := hleaf y hy
    rw [hlabel]
    exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hrS, r.2⟩)
  · obtain ⟨r, -, rfl⟩ := hleaf a ha
    obtain ⟨r', -, rfl⟩ := hleaf b hb
    rw [hlabel, hlabel] at hab
    rw [Subtype.ext hab]
  · obtain ⟨hrS, hrM⟩ := Finset.mem_erase.1 (Finset.mem_coe.1 hr)
    refine ⟨.inl ⟨φ ⟨r, hrM⟩, hnotcen _⟩, ?_, hlabel ⟨r, hrM⟩⟩
    refine (Decomp.GlueData.isLeaf_net_inl hD _).2 fun b hb hpar => ?_
    change h.par (φ ⟨S, hS⟩) b = φ ⟨r, hrM⟩ at hpar
    have hne₁ : φ ⟨r, hrM⟩ ≠ φ ⟨S, hS⟩ := hρS hrS
    obtain ⟨hadj, -, hdist⟩ := h.par_spec (ρ := φ ⟨S, hS⟩) hb
    obtain ⟨hadj₁, -, hdist₁⟩ := h.par_spec (ρ := φ ⟨S, hS⟩) hne₁
    rw [hpar] at hadj hdist
    have hbeq : b = h.par (φ ⟨S, hS⟩) (φ ⟨r, hrM⟩) :=
      (Set.ncard_le_one_iff (Set.toFinite _)).1 ((h.mem_range_iff _).1 ⟨_, rfl⟩) hadj.symm hadj₁
    rw [← hbeq] at hdist₁
    exact lt_asymm hdist hdist₁

end Frame

include h in
/-- **Line 299**, the end of the proof of Theorem 1, for a row `S` as root: the central nodes of `T̄` inflated to networks for the super-characters other than `S(C)`,
each with ancestral sequence `S(C)`. -/
theorem exists_glued [LinearOrder ι] [Finite ι] {Vp Ep : Decomp.Cent (incompatGraph M) → Type w} [∀ C, Finite (Vp C)] [∀ C, Finite (Ep C)]
    (P : ∀ C : Decomp.Cent (incompatGraph M), Network C.1.supp (Vp C) (Ep C)) {S : ι → Bool} (hS : S ∈ M) (hC : NoConstantColumn M)
    (hanc : ∀ C, (P C).ancestral = C.1.supp.domRestrict S)
    (hder : ∀ C, (P C).Derives ((restrictRows C.1.supp M).erase (C.1.supp.domRestrict S))) (hne : ∃ r ∈ M, r ≠ S) :
    ∃ (V E : Type (max u v w)) (_ : Finite V) (_ : Finite E) (N : Network ι V E),
      (∀ c, (∀ C, (P C).Obeys c) → N.Obeys c) ∧ N.ancestral = S ∧ N.Derives (M.erase S) ∧ ¬ N.IsLeaf N.root ∧
      ((∀ C, (∃! B, (P C).IsBlob B) ∧ ∀ i, ∃ B, (P C).IsBlob B ∧ (P C).site i ∈ B) → N.IsFullyDecomposedFor (incompatGraph M)) ∧
      N.recombCount = ∑ᶠ C, (P C).recombCount := by
  have : Finite (incompatGraph M).ConnectedComponent :=
    Finite.of_surjective (incompatGraph M).connectedComponentMk fun c => c.exists_rep
  have hD := h.frame_valid P S hS hanc hder hC
  have hrow : (h.frame P S hS).lam (φ ⟨S, hS⟩) = S := by
    funext i
    exact h.lam_row ⟨S, hS⟩ i
  refine ⟨(h.frame P S hS).Vtx, (h.frame P S hS).Arcs, inferInstance, inferInstance, (h.frame P S hS).net hD,
    fun c hc => Decomp.GlueData.net_obeys hD hc, hrow, h.frame_derives P S hS hder hD hne, ?_,
    fun hP => Decomp.GlueData.net_fullyDecomposed hD hP, ?_⟩
  · obtain ⟨r, hr, hrS⟩ := hne
    have hne₁ : φ ⟨r, hr⟩ ≠ φ ⟨S, hS⟩ := fun heq => hrS (congrArg Subtype.val (h.label_injective heq))
    obtain ⟨w, hw, -⟩ := exists_adj_separating h.isTree hne₁.symm
    rcases h.adj_cases (ρ := φ ⟨S, hS⟩) hw with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
    · intro hleaf
      exact (Decomp.GlueData.isLeaf_net_inl hD _).1 hleaf w h₁ h₂.symm
    · exact absurd rfl h₁
  · have : Fintype (Decomp.Cent (incompatGraph M)) := Fintype.ofFinite _
    rw [Decomp.GlueData.net_recombCount hD, finsum_eq_sum_of_fintype]

end IsTBar

end Gusfield2007
