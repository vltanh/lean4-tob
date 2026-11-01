module

public import External.AllmanBanosRhodes2019.Proposition9Part2
public import External.AllmanBanosRhodes2019.QuartetForm

/-!
# `networkClass`, `rho` and `networkDistance` are the source's

The bridges of the definitions of `NANUQ.lean`, stated by cut edges and the grove, with the source's definitions by contraction
(`QuartetContract.lean`).

* `rhoTilde`: `ρ_xy` of Definition 20 (line 1026), with the source's extension to a star tree (lines 1964-1968), on the graph `Q̃`.
* `sourceDistance`: the distance `d_{Q,N⁻}` of Definition 22 (line 1125) with this `ρ_xy`.
* `networkClass_eq_tree_iff`, `networkClass_eq_cycle_iff`: **`networkClass N q` is `.tree s` when `Q̃` is the tree `s`, and `.cycle s` when
  `Q̃` is the 4-cycle with the cherries of `s` opposite.**
* `qTilde_tree_or_cycle`: "a network `Q̃_xyzw` that is either a tree or has a single 4-cycle".
* `rho_networkClass_eq`, `networkDistance_eq_sourceDistance`: the indicators and the distances agree.
* `hasCycleType_four_one_iff`: the source's `4₁`-cycle is the absence of a cut-edge split on the induced network.
* `proposition9_source`: **Proposition 9 of the source, all three parts, in its own terms**: the types of cycle of the quartet network, and
  the form of `Q̃`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open TOBQMC TOBQMC.Level1
open AllmanEtAl2023 AllmanEtAl2023.TreeSuppression
open scoped Classical

namespace External.AllmanBanosRhodes2019.Quartet

variable {V E X : Type*}

/-! ### The source's definitions -/

/-- **Definition 20** (`nanuq:definition20`), `ρ_xy(Q_xyzw)`, read on `Q̃`: `0` if `Q̃` "has form `xy|zw`", `1/2` if `Q̃` "has a 4-cycle with `x, y` adjacent", and
`1` otherwise; so also on a star tree, by the extension at lines 1964-1968. -/
def rhoTilde {W Y : Type*} (T : LabelledGraph W Y) (x y : Y) : ℝ :=
  if ∃ z w, T.HasQuartetTopology x y z w then 0 else if ∃ z w, HasFourCycleTopology T x y z w then 1 / 2 else 1

/-- `ρ_xy` on the set of four taxa `q`. -/
def rhoOn {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) (q : Finset X) (x y : X) : ℝ :=
  if h : 2 ≤ #q ∧ x ∈ q ∧ y ∈ q then rhoTilde (qTilde hN h.1) ⟨x, h.2.1⟩ ⟨y, h.2.2⟩ else 1

/-- **Definition 22** (`nanuq:definition22`), the quartet distance `d_{Q,N⁻}` (line 1125): for `x ≠ y`, `2 ∑_{z,w} ρ_xy(Q_xyzw) + 2n - 4`. -/
def sourceDistance [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) (x y : X) : ℝ :=
  if x = y then 0 else
    2 * ∑ q ∈ univ.filter (fun q : Finset X => q.card = 4 ∧ x ∈ q ∧ y ∈ q), rhoOn hN q x y + 2 * (Fintype.card X : ℝ) - 4

/-! ### Literal forms -/

section Forms

variable {W Y : Type*} {T : LabelledGraph W Y}

/-- A list with no repetition inside a shorter one is impossible. -/
theorem false_of_nodup_of_subset {α : Type*} {l l' : List α} (hl : l.Nodup) (hs : ∀ v, v ∈ l → v ∈ l') (hlen : l'.length < l.length) : False := by
  have := (List.subperm_of_subset hl hs).length_le
  omega

theorem HasFourCycleTopology.not_hasQuartetTopology {a b c d a' b' c' d' : Y} (h : HasFourCycleTopology T a b c d) :
    ¬ T.HasQuartetTopology a' b' c' d' := by
  obtain ⟨ua, ub, uc, ud, hnd, -, -⟩ := h
  rintro ⟨u, w, -, hall, -⟩
  exact false_of_nodup_of_subset hnd (fun v _ => hall v) (by simp)

theorem HasFourCycleTopology.not_hasStarTopology {a b c d a' b' c' d' : Y} (h : HasFourCycleTopology T a b c d) :
    ¬ T.HasStarTopology a' b' c' d' := by
  obtain ⟨ua, ub, uc, ud, hnd, -, -⟩ := h
  rintro ⟨u, -, hall, -⟩
  exact false_of_nodup_of_subset hnd (fun v _ => hall v) (by simp)

theorem AdjTaxa.symm {x y : Y} (h : AdjTaxa T x y) : AdjTaxa T y x := by
  obtain ⟨u, v, hu, hv, huv⟩ := h
  exact ⟨v, u, hv, hu, huv.symm⟩

end Forms

/-! ### The bridges -/

section Bridges

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} {q : Finset X}

omit [Fintype X] in
theorem card_labels {a b c d : {x // x ∈ q}} (h : ({a.1, b.1, c.1, d.1} : Finset X).card = 4) :
    ({a, b, c, d} : Finset {x // x ∈ q}).card = 4 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hne' : ∀ {u v : {x // x ∈ q}}, u.1 ≠ v.1 → u ≠ v := fun h' he => h' (congrArg Subtype.val he)
  rw [card_insert_of_notMem (by simp [hne' hab, hne' hac, hne' had]), card_insert_of_notMem (by simp [hne' hbc, hne' hbd]),
    card_pair (hne' hcd)]

omit [Fintype X] in
/-- Four labels of `q` with no repetition make a set of four. -/
theorem card_of_nodup_leaf {W : Type*} {T : LabelledGraph W {x // x ∈ q}} {a b c d : {x // x ∈ q}} {l : List W}
    (hnd : (T.leaf a :: T.leaf b :: T.leaf c :: T.leaf d :: l).Nodup) : ({a.1, b.1, c.1, d.1} : Finset X).card = 4 := by
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  obtain ⟨⟨hab, hac, had, -⟩, ⟨hbc, hbd, -⟩, ⟨hcd, -⟩, -⟩ := hnd
  have hne' : ∀ {u v : {x // x ∈ q}}, T.leaf u ≠ T.leaf v → u.1 ≠ v.1 := fun h' he => h' (congrArg T.leaf (Subtype.ext he))
  rw [card_insert_of_notMem (by simp [hne' hab, hne' hac, hne' had]), card_insert_of_notMem (by simp [hne' hbc, hne' hbd]),
    card_pair (hne' hcd)]

/-- On a treelike set, `Q̃` has no 4-cycle: it has at most six vertices. -/
theorem not_hasFourCycleTopology_of_isTreelike (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4)
    (ht : IsTreelike N q) {a b c d : {x // x ∈ q}} (hf : HasFourCycleTopology (qTilde hN (by omega : 2 ≤ #q)) a b c d) : False := by
  obtain ⟨_, _, _, _, hnd, _, _⟩ := id hf
  have hc := card_of_nodup_leaf hnd
  rcases qTilde_hasStar_or_hasQuartet hN hBin hLevel hq ht (card_labels hc) with h' | h' | h' | h'
  · exact hf.not_hasStarTopology h'
  · exact hf.not_hasQuartetTopology h'
  · exact hf.not_hasQuartetTopology h'
  · exact hf.not_hasQuartetTopology h'

omit [Fintype X] in
/-- The set of the four labels. -/
theorem eq_of_labels (hq : #q = 4) {a b c d : {x // x ∈ q}} (h : ({a.1, b.1, c.1, d.1} : Finset X).card = 4) : q = {a.1, b.1, c.1, d.1} := by
  refine (eq_of_subset_of_card_le (fun z hz => ?_) (by rw [h, hq])).symm
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact a.2
  · exact b.2
  · exact c.2
  · exact d.2

omit [Fintype E] in
/-- The class of a set of four taxa, on a cut-edge split. -/
theorem networkClass_eq_tree_of_inducedCutSplit [Nonempty X] (hN : N.IsPhylogenetic) {s : QuartetTree X} (hs : InducedCutSplit N s)
    (hsq : s.taxa = q) : networkClass N q = .tree s := by
  rw [← hsq]
  exact networkClass_eq_tree hN hs

omit [Fintype V] [Fintype E] in
/-- What the class `.tree` says. -/
theorem inducedCutSplit_of_networkClass_eq_tree {s : QuartetTree X} (h : networkClass N q = .tree s) :
    s ∈ treesOn q ∧ InducedCutSplit N s := by
  unfold networkClass at h
  by_cases h₁ : ∃ r ∈ treesOn q, InducedCutSplit N r
  · rw [dite_eq_left h₁] at h
    have := QuartetClass.tree.inj h
    rw [← this]
    exact h₁.choose_spec
  · rw [dite_eq_right h₁] at h
    split_ifs at h

omit [Fintype V] [Fintype E] [Fintype X] in
/-- A quartet tree, from one of its cherries. -/
theorem exists_of_cherry {s : QuartetTree X} (hst : s.taxa = q) {x y : X} (hA : ({x, y} : Finset X) ∈ s.val) :
    ∃ (z w : X) (h : ({x, y, z, w} : Finset X).card = 4), s = quartetTree x y z w h ∧ x ∈ q ∧ y ∈ q ∧ z ∈ q ∧ w ∈ q := by
  have hxy : x ≠ y := by
    rintro rfl
    have := s.card_of_mem hA
    rw [pair_eq_singleton, card_singleton] at this
    omega
  obtain ⟨z, w, hzw, hE⟩ := card_eq_two.1 (s.card_of_mem (s.sdiff_mem hA))
  have hzm : z ∈ s.taxa \ ({x, y} : Finset X) := by rw [hE]; simp
  have hwm : w ∈ s.taxa \ ({x, y} : Finset X) := by rw [hE]; simp
  obtain ⟨hzq, hzA⟩ := mem_sdiff.1 hzm
  obtain ⟨hwq, hwA⟩ := mem_sdiff.1 hwm
  simp only [mem_insert, mem_singleton, not_or] at hzA hwA
  have h4 : ({x, y, z, w} : Finset X).card = 4 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_pair hzw]
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨Ne.symm hzA.2, Ne.symm hwA.2⟩
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hxy, Ne.symm hzA.1, Ne.symm hwA.1⟩
  have hxq := s.subset_taxa hA (show x ∈ ({x, y} : Finset X) by simp)
  have hyq := s.subset_taxa hA (show y ∈ ({x, y} : Finset X) by simp)
  refine ⟨z, w, h4, QuartetTree.eq_of_taxa_eq_of_mem ?_ hA (by simp), hst ▸ hxq, hst ▸ hyq, hst ▸ hzq, hst ▸ hwq⟩
  rw [quartetTree_taxa]
  refine (eq_of_subset_of_card_le (fun t ht' => ?_) (by rw [s.card_taxa, h4])).symm
  simp only [mem_insert, mem_singleton] at ht'
  rcases ht' with rfl | rfl | rfl | rfl
  · exact hxq
  · exact hyq
  · exact hzq
  · exact hwq

/-- **`networkClass` is the tree of `Q̃`**: on a set of four taxa of a binary level-1 network, `networkClass N q` is the quartet tree
`ab|cd` exactly when `Q̃` "has form `ab|cd`" (Definition 20), the literal tree with these cherries. -/
theorem networkClass_eq_tree_iff (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4)
    {a b c d : {x // x ∈ q}} (h : ({a.1, b.1, c.1, d.1} : Finset X).card = 4) :
    networkClass N q = .tree (quartetTree a.1 b.1 c.1 d.1 h) ↔
      (qTilde hN (by omega : 2 ≤ #q)).HasQuartetTopology a b c d := by
  have hne : Nonempty X := ⟨a.1⟩
  have hqe := eq_of_labels hq h
  have hsq : (quartetTree a.1 b.1 c.1 d.1 h).taxa = q := (quartetTree_taxa _ _ _ _ _).trans hqe.symm
  constructor
  · intro hc
    obtain ⟨hm, hs⟩ := inducedCutSplit_of_networkClass_eq_tree hc
    exact (qTilde_hasQuartetTopology_iff hN hBin hLevel hq ⟨_, hm, hs⟩ h).2 hs
  · intro hT
    have ht : IsTreelike N q := by
      by_contra hnt
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, D, -, -⟩ := exists_cycleData hN hBin hLevel hq hnt
      exact (D.hasFourCycleTopology hN hBin hLevel).not_hasQuartetTopology hT
    exact networkClass_eq_tree_of_inducedCutSplit hN ((qTilde_hasQuartetTopology_iff hN hBin hLevel hq ht h).1 hT) hsq

/-- The class on a 4-cycle, with the labels of `CycleData`. -/
theorem CycleData.networkClass_eq {a : X} {h T : V} {k₁ k₂ : E} {pL pR : List E} {y : Fin 4 → X} {b : Fin 4 → V} {P : Fin 4 → List (E × V)}
    {s : Fin 4 → E} (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (D : CycleData N q a h T k₁ k₂ pL pR y b P s)
    (H₁₂ : List.Sublist [b 1, b 2] ((pL.map N.graph.target).reverse ++ T :: pR.map N.graph.target))
    (H₂₃ : List.Sublist [b 2, b 3] ((pL.map N.graph.target).reverse ++ T :: pR.map N.graph.target))
    (hc : ({y 0, y 2, y 1, y 3} : Finset X).card = 4) (hnt : ¬ IsTreelike N q) :
    networkClass N q = .cycle (quartetTree (y 0) (y 2) (y 1) (y 3) hc) := by
  have hsq : (quartetTree (y 0) (y 2) (y 1) (y 3) hc).taxa = q := by
    rw [quartetTree_taxa]
    refine eq_of_subset_of_card_le (fun z hz => ?_) (by rw [D.frame.card, hc])
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> exact D.y_mem _
  rw [← hsq] at hnt ⊢
  exact networkClass_eq_cycle hN hBin hLevel hnt (not_groveDisplays_of_cycle hN hBin hLevel D H₁₂ H₂₃ hc)

/-- **`networkClass` is the 4-cycle of `Q̃`**: on a set of four taxa of a binary level-1 network, `networkClass N q` is `.cycle` of `ac|bd`
exactly when `Q̃` is the 4-cycle "joining taxa in circular order `a, b, c, d`" (line 491). -/
theorem networkClass_eq_cycle_iff (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4)
    {a b c d : {x // x ∈ q}} (h : ({a.1, c.1, b.1, d.1} : Finset X).card = 4) :
    networkClass N q = .cycle (quartetTree a.1 c.1 b.1 d.1 h) ↔
      HasFourCycleTopology (qTilde hN (by omega : 2 ≤ #q)) a b c d := by
  have hq2 : 2 ≤ #q := by omega
  have hne : Nonempty X := ⟨a.1⟩
  have hqe : q = {a.1, c.1, b.1, d.1} := eq_of_labels hq h
  -- the case with no cut-edge split
  have main : ¬ IsTreelike N q → (networkClass N q = .cycle (quartetTree a.1 c.1 b.1 d.1 h) ↔
      HasFourCycleTopology (qTilde hN hq2) a b c d) := by
    intro hnt
    obtain ⟨a₀, h₀, T₀, k₁, k₂, pL, pR, y, b', P, s', D, H₁₂, H₂₃⟩ := exists_cycleData hN hBin hLevel hq hnt
    let l : Fin 4 → {x // x ∈ q} := fun i => ⟨y i, D.y_mem i⟩
    have hF₀ : HasFourCycleTopology (qTilde hN hq2) (l 0) (l 1) (l 2) (l 3) := D.hasFourCycleTopology hN hBin hLevel
    have hF₁ := hF₀.rotate
    have hF₂ := hF₁.rotate
    have hF₃ := hF₂.rotate
    have hc₀ : ({y 0, y 2, y 1, y 3} : Finset X).card = 4 := by
      have hne' : ∀ {i j : Fin 4}, i ≠ j → y i ≠ y j := fun hij he => hij (D.y_inj he)
      rw [card_insert_of_notMem (by simp [hne' (show (0 : Fin 4) ≠ 2 by decide), hne' (show (0 : Fin 4) ≠ 1 by decide), hne' (show (0 : Fin 4) ≠ 3 by decide)]),
        card_insert_of_notMem (by simp [hne' (show (2 : Fin 4) ≠ 1 by decide), hne' (show (2 : Fin 4) ≠ 3 by decide)]),
        card_pair (hne' (show (1 : Fin 4) ≠ 3 by decide))]
    have hcl := D.networkClass_eq hN hBin hLevel H₁₂ H₂₃ hc₀ hnt
    have hsur : ∀ x : {x // x ∈ q}, ∃ i, x = l i := fun x => by
      obtain ⟨i, hi⟩ := D.y_surj x.1 x.2
      exact ⟨i, Subtype.ext hi⟩
    have hlne : ∀ {i j : Fin 4}, i ≠ j → l i ≠ l j := fun hij he => hij (D.y_inj (congrArg Subtype.val he))
    rw [hcl]
    constructor
    · intro he
      have heq := QuartetClass.cycle.inj he
      -- the cherries agree
      have hv : ({{y 0, y 2}, {y 1, y 3}} : Finset (Finset X)) = {{a.1, c.1}, {b.1, d.1}} := congrArg Subtype.val heq
      obtain ⟨i, rfl⟩ := hsur a
      obtain ⟨j, rfl⟩ := hsur b
      obtain ⟨k, rfl⟩ := hsur c
      obtain ⟨m, rfl⟩ := hsur d
      obtain ⟨hne₁, hne₂, hne₃, hne₄, hne₅, hne₆⟩ := ne_of_card_four h
      have hij : ∀ {i j : Fin 4}, y i ≠ y j → i ≠ j := fun h' he => h' (he ▸ rfl)
      have hm₁ : ({y i, y k} : Finset X) ∈ ({{y 0, y 2}, {y 1, y 3}} : Finset (Finset X)) := by
        rw [hv]
        exact mem_insert_self _ _
      have hm₂ : ({y j, y m} : Finset X) ∈ ({{y 0, y 2}, {y 1, y 3}} : Finset (Finset X)) := by
        rw [hv]
        exact mem_insert_of_mem (mem_singleton_self _)
      have hpair : ∀ {u v u' v' : Fin 4}, ({y u, y v} : Finset X) = {y u', y v'} → (u = u' ∧ v = v') ∨ (u = v' ∧ v = u') := by
        intro u v u' v' he
        have h₁ : y u ∈ ({y u', y v'} : Finset X) := he ▸ (by simp)
        have h₂ : y v ∈ ({y u', y v'} : Finset X) := he ▸ (by simp)
        have h₃ : y u' ∈ ({y u, y v} : Finset X) := he ▸ (by simp)
        have h₄ : y v' ∈ ({y u, y v} : Finset X) := he ▸ (by simp)
        simp only [mem_insert, mem_singleton, D.y_inj.eq_iff] at h₁ h₂ h₃ h₄
        grind
      simp only [mem_insert, mem_singleton] at hm₁ hm₂
      have hik := hij hne₁
      have hjm := hij hne₆
      have hdisj₁ := hij hne₂
      have hdisj₂ := hij hne₃
      rcases hm₁ with h₁ | h₁ <;> rcases hm₂ with h₂ | h₂ <;> rcases hpair h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hpair h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> first
        | exact absurd rfl hdisj₁
        | exact absurd rfl hdisj₂
        | exact hF₀
        | exact hF₁
        | exact hF₂
        | exact hF₃
        | exact hF₀.reflect
        | exact hF₁.reflect
        | exact hF₂.reflect
        | exact hF₃.reflect
    · intro hf
      -- `a`, `c` are opposite on the cycle of `y`
      have hna := hf.not_adjTaxa
      obtain ⟨i, hi⟩ := hsur a
      obtain ⟨k, hk⟩ := hsur c
      have hik : i ≠ k := by
        rintro rfl
        obtain ⟨hne₁, -⟩ := ne_of_card_four h
        exact hne₁ (by rw [hi, hk])
      have hadj : ∀ i : Fin 4, AdjTaxa (qTilde hN hq2) (l i) (l (i + 1)) := by
        intro i
        fin_cases i
        · exact hF₀.adjTaxa
        · exact hF₁.adjTaxa
        · exact hF₂.adjTaxa
        · exact hF₃.adjTaxa
      have hkey : ∀ i k : Fin 4, i ≠ k → k = i + 1 ∨ i = k + 1 ∨ k = i + 2 := by decide
      have hki : k = i + 2 := by
        rcases hkey i k hik with h' | h' | h'
        · exact absurd (by rw [hi, hk, h']; exact hadj i) hna
        · exact absurd (by rw [hi, hk, h']; exact (hadj k).symm) hna
        · exact h'
      -- so they are a cherry of the quartet tree of `y`
      have hmem : ({a.1, c.1} : Finset X) ∈ (quartetTree (y 0) (y 2) (y 1) (y 3) hc₀).val := by
        rw [hi, hk, hki]
        simp only [quartetTree_val, mem_insert, mem_singleton, l]
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inl (pair_comm _ _)
        · exact Or.inr (pair_comm _ _)
      have ht : (quartetTree (y 0) (y 2) (y 1) (y 3) hc₀).taxa = (quartetTree a.1 c.1 b.1 d.1 h).taxa := by
        rw [quartetTree_taxa, quartetTree_taxa, ← hqe]
        refine eq_of_subset_of_card_le (fun z hz => ?_) (by rw [hq, hc₀])
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> exact D.y_mem _
      have heq := QuartetTree.eq_of_taxa_eq_of_mem ht hmem (show ({a.1, c.1} : Finset X) ∈ (quartetTree a.1 c.1 b.1 d.1 h).val by simp)
      rw [heq]
  by_cases ht : IsTreelike N q
  · constructor
    · intro he
      obtain ⟨s₁, hs₁, hcut⟩ := ht
      have hc₁ := networkClass_eq_tree_of_inducedCutSplit hN hcut (mem_treesOn.1 hs₁)
      rw [hc₁] at he
      exact absurd he (by simp)
    · intro hf
      exact (not_hasFourCycleTopology_of_isTreelike hN hBin hLevel hq ht hf).elim
  · exact main ht

/-- **"We obtain a network `Q̃_xyzw` that is either a tree or has a single 4-cycle"** (Definition 20, line 1026), on a binary level-1
network. -/
theorem qTilde_tree_or_cycle (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4) :
    (∃ a b c d, (qTilde hN (by omega : 2 ≤ #q)).HasQuartetTopology a b c d) ∨
      ∃ a b c d, HasFourCycleTopology (qTilde hN (by omega : 2 ≤ #q)) a b c d := by
  by_cases ht : IsTreelike N q
  · left
    obtain ⟨s, hs, hcut⟩ := id ht
    have hst := mem_treesOn.1 hs
    obtain ⟨A, hA, -⟩ := id hcut
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 (s.card_of_mem hA)
    have hne : Nonempty X := ⟨x⟩
    obtain ⟨z, w, h4, hsqt, hx, hy, hz, hw⟩ := exists_of_cherry hst hA
    subst hsqt
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩, ⟨w, hw⟩, (networkClass_eq_tree_iff hN hBin hLevel hq h4).1
      (networkClass_eq_tree_of_inducedCutSplit hN hcut hst)⟩
  · right
    obtain ⟨_, _, _, _, _, _, _, y, _, _, _, D, -, -⟩ := exists_cycleData hN hBin hLevel hq ht
    exact ⟨_, _, _, _, D.hasFourCycleTopology hN hBin hLevel⟩

/-- **`ρ_xy` of `NANUQ.lean` on `networkClass` is the source's on `Q̃`.** -/
theorem rho_networkClass_eq (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4) {x y : X} (hx : x ∈ q)
    (hy : y ∈ q) (hxy : x ≠ y) :
    rho (networkClass N q) x y = rhoTilde (qTilde hN (by omega : 2 ≤ #q)) ⟨x, hx⟩ ⟨y, hy⟩ := by
  have hq2 : 2 ≤ #q := by omega
  have hne : Nonempty X := ⟨x⟩
  by_cases ht : IsTreelike N q
  · -- a cut-edge split
    obtain ⟨s, hs, hcut⟩ := id ht
    have hst := mem_treesOn.1 hs
    rw [networkClass_eq_tree_of_inducedCutSplit hN hcut hst]
    have hnF : ¬ ∃ z w, HasFourCycleTopology (qTilde hN hq2) ⟨x, hx⟩ ⟨y, hy⟩ z w := by
      rintro ⟨z, w, hf⟩
      exact not_hasFourCycleTopology_of_isTreelike hN hBin hLevel hq ht hf
    simp only [rho, rhoTilde, hnF, ite_false]
    by_cases hsep : Separated s x y
    · rw [ite_eq_left hsep, ite_eq_right]
      rintro ⟨z, w, u, w', hnd, hall, hE⟩
      have hc := card_of_nodup_leaf (q := q) (T := qTilde hN hq2) (l := [u, w']) hnd
      have hT : (qTilde hN hq2).HasQuartetTopology ⟨x, hx⟩ ⟨y, hy⟩ z w := ⟨u, w', hnd, hall, hE⟩
      have hs₂ := (qTilde_hasQuartetTopology_iff hN hBin hLevel hq ht hc).1 hT
      have hqe := eq_of_labels (a := ⟨x, hx⟩) (b := ⟨y, hy⟩) hq hc
      have heq := eq_of_inducedCutSplit hN hcut hs₂ (by rw [hst, quartetTree_taxa]; exact hqe)
      refine hsep.2.2 {x, y} ?_ (by simp)
      rw [heq]
      simp
    · rw [ite_eq_right hsep, ite_eq_left]
      -- `x, y` are a cherry
      have hxs : x ∈ s.taxa := hst ▸ hx
      have hys : y ∈ s.taxa := hst ▸ hy
      have hcherry : ∃ B ∈ s.val, x ∈ B ∧ y ∈ B := by
        by_contra hno
        push Not at hno
        exact hsep ⟨hxs, hys, fun B hB hc => hno B hB hc.1 hc.2⟩
      obtain ⟨B, hB, hxB, hyB⟩ := hcherry
      have hBe : B = {x, y} := by
        symm
        refine eq_of_subset_of_card_le (fun z hz => ?_) (by rw [s.card_of_mem hB, card_pair hxy])
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hxB
        · exact hyB
      subst hBe
      obtain ⟨z, w, h4, hsqt, -, -, hz, hw⟩ := exists_of_cherry hst hB
      subst hsqt
      exact ⟨⟨z, hz⟩, ⟨w, hw⟩, (qTilde_hasQuartetTopology_iff hN hBin hLevel hq ht h4).2 hcut⟩
  · -- a 4-cycle
    obtain ⟨a₀, h₀, T₀, k₁, k₂, pL, pR, l₀, b', P, s', D, H₁₂, H₂₃⟩ := exists_cycleData hN hBin hLevel hq ht
    let l : Fin 4 → {x // x ∈ q} := fun i => ⟨l₀ i, D.y_mem i⟩
    have hF₀ : HasFourCycleTopology (qTilde hN hq2) (l 0) (l 1) (l 2) (l 3) := D.hasFourCycleTopology hN hBin hLevel
    have hF₁ := hF₀.rotate
    have hF₂ := hF₁.rotate
    have hF₃ := hF₂.rotate
    have hne' : ∀ {i j : Fin 4}, i ≠ j → l₀ i ≠ l₀ j := fun hij he => hij (D.y_inj he)
    have hc₀ : ({l₀ 0, l₀ 2, l₀ 1, l₀ 3} : Finset X).card = 4 := by
      rw [card_insert_of_notMem (by simp [hne' (show (0 : Fin 4) ≠ 2 by decide), hne' (show (0 : Fin 4) ≠ 1 by decide), hne' (show (0 : Fin 4) ≠ 3 by decide)]),
        card_insert_of_notMem (by simp [hne' (show (2 : Fin 4) ≠ 1 by decide), hne' (show (2 : Fin 4) ≠ 3 by decide)]),
        card_pair (hne' (show (1 : Fin 4) ≠ 3 by decide))]
    rw [D.networkClass_eq hN hBin hLevel H₁₂ H₂₃ hc₀ ht]
    obtain ⟨i, rfl⟩ := D.y_surj x hx
    obtain ⟨j, rfl⟩ := D.y_surj y hy
    have hij : i ≠ j := fun he => hxy (he ▸ rfl)
    have hnQ : ¬ ∃ z w, (qTilde hN hq2).HasQuartetTopology (l i) (l j) z w := fun ⟨_, _, hT⟩ => hF₀.not_hasQuartetTopology hT
    have hsepiff : Separated (quartetTree (l₀ 0) (l₀ 2) (l₀ 1) (l₀ 3) hc₀) (l₀ i) (l₀ j) ↔ j ≠ i + 2 := by
      have hty : ∀ t, l₀ t ∈ (quartetTree (l₀ 0) (l₀ 2) (l₀ 1) (l₀ 3) hc₀).taxa := by
        intro t
        rw [quartetTree_taxa]
        fin_cases t <;> simp
      have hiffm : ∀ u v : Fin 4, (l₀ u = l₀ v) ↔ u = v := fun u v => D.y_inj.eq_iff
      simp only [Separated, hty, true_and, quartetTree_val, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, hiffm]
      have key : ∀ i j : Fin 4, i ≠ j → (¬((i = 0 ∨ i = 2) ∧ (j = 0 ∨ j = 2)) ∧ ¬((i = 1 ∨ i = 3) ∧ (j = 1 ∨ j = 3)) ↔ j ≠ i + 2) := by
        decide
      exact key i j hij
    have hrhoLHS : rhoTilde (qTilde hN hq2) (l i) (l j) = if j ≠ i + 2 then 1 / 2 else 1 := by
      unfold rhoTilde
      rw [ite_eq_right hnQ]
      have hkey : ∀ i j : Fin 4, i ≠ j → j ≠ i + 2 → j = i + 1 ∨ i = j + 1 := by decide
      by_cases hji : j ≠ i + 2
      · rw [ite_eq_left hji, ite_eq_left]
        rcases hkey i j hij hji with rfl | rfl
        · fin_cases i
          · exact ⟨_, _, hF₀⟩
          · exact ⟨_, _, hF₁⟩
          · exact ⟨_, _, hF₂⟩
          · exact ⟨_, _, hF₃⟩
        · fin_cases j
          · exact ⟨_, _, hF₁.reflect⟩
          · exact ⟨_, _, hF₂.reflect⟩
          · exact ⟨_, _, hF₃.reflect⟩
          · exact ⟨_, _, hF₀.reflect⟩
      · rw [ite_eq_right hji, ite_eq_right]
        push Not at hji
        subst hji
        rintro ⟨z, w, hf⟩
        have hadj := hf.adjTaxa
        fin_cases i
        · exact hF₀.not_adjTaxa hadj
        · exact hF₁.not_adjTaxa hadj
        · exact hF₂.not_adjTaxa hadj
        · exact hF₃.not_adjTaxa hadj
    have hright : rhoTilde (qTilde hN hq2) ⟨l₀ i, hx⟩ ⟨l₀ j, hy⟩ = rhoTilde (qTilde hN hq2) (l i) (l j) := rfl
    rw [hright, hrhoLHS]
    simp only [rho, hsepiff]

/-- **The theoretical distance of `NANUQ.lean` is the source's `d_{Q,N⁻}` of Definition 22.** -/
theorem networkDistance_eq_sourceDistance (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (x y : X) :
    networkDistance N x y = sourceDistance hN x y := by
  unfold networkDistance nanuqDistance sourceDistance
  split_ifs with hxy
  · rfl
  · have hsum : ∑ q ∈ univ.filter (fun q : Finset X => q.card = 4 ∧ x ∈ q ∧ y ∈ q), rho (networkClass N q) x y =
        ∑ q ∈ univ.filter (fun q : Finset X => q.card = 4 ∧ x ∈ q ∧ y ∈ q), rhoOn hN q x y := by
      refine Finset.sum_congr rfl fun q hq => ?_
      obtain ⟨-, hq4, hx, hy⟩ := mem_filter.1 hq
      rw [rho_networkClass_eq hN hBin hLevel hq4 hx hy hxy, rhoOn, dite_eq_left ⟨by omega, hx, hy⟩]
    rw [hsum]

/-- **The source's `4₁`-cycle** is the absence of a cut-edge split on the induced network. -/
theorem hasCycleType_four_one_iff (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4) :
    HasCycleType N q 4 1 ↔ ¬ IsTreelike N q := by
  constructor
  · rintro ⟨h, hQ, hsize, -⟩
    obtain ⟨⟨a, ha, hr⟩, -⟩ := (isQuartetCycle_iff hN hBin hLevel hQ.1).1 hQ
    exact not_isTreelike_of_distinct hN hBin hLevel (v := h) .refl hQ.1 hq
      (fun x hx y hy hxy => not_blockWalk_of_four_le hN hBin hLevel hq hQ (by omega) hx hy hxy) ha hr
  · intro hnt
    obtain ⟨a, h, T, k₁, k₂, pL, pR, _, _, _, _, D, -, -⟩ := exists_cycleData hN hBin hLevel hq hnt
    have F := D.frame
    refine ⟨h, frame_hQ hN hBin hLevel F, cycleSize_eq_four hN hBin hLevel F, ?_⟩
    have : (q.filter fun x => N.graph.Reaches h (N.leaf x)) = {a} := by
      ext z
      simp only [mem_filter, mem_singleton]
      exact ⟨fun ⟨hz, hr⟩ => by_contra fun hne => F.only z hz hne hr, fun hz => hz ▸ ⟨F.mem, F.below⟩⟩
    unfold cycleDescendants
    rw [this, card_singleton]

omit [DecidableEq X] in
/-- **"In a level-1 quartet network, there are exactly 6 types of cycles that may appear: `2₁`, `2₂`, `2₃`, `3₁`, `3₂`, and `4₁`"** (line 401): `1 ≤ k`,
`2 ≤ m`, `m + k ≤ 5`. The taxa below the hybrid node attach at it, and each other taxon attaches elsewhere. -/
theorem cycleType_bounds (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4) {h : V} (hQ : IsQuartetCycle N q h) :
    1 ≤ cycleDescendants N q h ∧ 2 ≤ cycleSize N q h ∧ cycleSize N q h + cycleDescendants N q h ≤ 5 := by
  have hh₂ := hQ.1
  obtain ⟨⟨a, ha, har⟩, c, hc, hcr⟩ := (isQuartetCycle_iff hN hBin hLevel hh₂).1 hQ
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl hh₂
  have hex : ∀ z, ∃ b, IsAttachment N h z b := fun z => exists_isAttachment hN (hx' z)
  choose att hatt using hex
  set Fq := q.filter fun x => N.graph.Reaches h (N.leaf x) with hFq
  set Gq := q.filter fun x => ¬ N.graph.Reaches h (N.leaf x) with hGq
  have hcard : #Fq + #Gq = 4 := by
    rw [← hq]
    exact card_filter_add_card_filter_not _
  have hk₁ : 1 ≤ #Fq := card_pos.2 ⟨a, mem_filter.2 ⟨ha, har⟩⟩
  have hsize := cycleSize_eq hN hBin hLevel hQ
  have hsub : {u | ∃ z ∈ q, IsAttachment N h z u} ⊆ insert h (att '' (Gq : Set X)) := by
    rintro u ⟨z, hz, hzu⟩
    by_cases hr : N.graph.Reaches h (N.leaf z)
    · exact Or.inl (IsAttachment.eq_of_isAttachment (hx' z) hzu (isAttachment_of_below hN hBin hLevel hh₂ hr))
    · exact Or.inr ⟨z, mem_coe.2 (mem_filter.2 ⟨hz, hr⟩), IsAttachment.eq_of_isAttachment (hx' z) (hatt z) hzu⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hins := Set.ncard_insert_le h (att '' (Gq : Set X))
  have him := Set.ncard_image_le (f := att) (Set.toFinite (Gq : Set X))
  rw [Set.ncard_coe_finset] at him
  have htwo : ({h, att c} : Set V) ⊆ {u | ∃ z ∈ q, IsAttachment N h z u} := by
    rintro u (rfl | rfl)
    · exact ⟨a, ha, isAttachment_of_below hN hBin hLevel hh₂ har⟩
    · exact ⟨c, hc, hatt c⟩
  have hne := IsAttachment.ne_of_not_below hN hBin hLevel hh₂ (hatt c) hcr
  have hge := Set.ncard_le_ncard htwo (Set.toFinite _)
  rw [Set.ncard_pair hne.symm] at hge
  unfold cycleDescendants
  rw [← hFq, hsize]
  omega

/-- **"`Q_abcd` might have a `4₁`-cycle or a `3₂`-cycle, but not both"** (line 406). -/
theorem not_hasCycleType_four_one_and_three_two (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4)
    (h₁ : HasCycleType N q 4 1) (h₂ : HasCycleType N q 3 2) : False :=
  (hasCycleType_four_one_iff hN hBin hLevel hq).1 h₁
    (isTreelike_of_hasThreeTwoCycle hN hBin hLevel hq ((hasThreeTwoCycle_iff hN hBin hLevel hq).2 h₂))

/-- A concordance factor with a strict minimum is not tree-like. -/
theorem not_isT3Null_of_isStrictMin {p : QuartetTree X → ℝ} {s : QuartetTree X} (hmin : IsStrictMin p s) : ¬ IsT3Null p s.taxa := by
  rintro ⟨s', hs', hle, heq⟩
  have hst' : s'.taxa = s.taxa := mem_treesOn.1 hs'
  obtain ⟨r₁, r₂, hne, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s'
  have hmem₁ : r₁ ∈ s'.alternatives := by rw [ha]; simp
  have hmem₂ : r₂ ∈ s'.alternatives := by rw [ha]; simp
  by_cases hss : s = s'
  · subst hss
    exact absurd (hle r₁ hmem₁) (not_le.2 (hmin r₁ hmem₁))
  · have hmemS : s ∈ s'.alternatives := QuartetTree.mem_alternatives.2 ⟨hst'.symm, hss⟩
    have key : ∀ u ∈ s'.alternatives, u ≠ s → False := fun u hu hne' =>
      (hmin u (QuartetTree.mem_alternatives.2
        ⟨(QuartetTree.mem_alternatives.1 hu).1.trans hst', hne'⟩)).ne (heq s hmemS u hu)
    by_cases h' : r₁ = s
    · exact key r₂ hmem₂ fun he => hne (h'.trans he.symm)
    · exact key r₁ hmem₁ h'

/-- **Proposition 9 of NANUQ** (`nanuq:proposition9-source`), in the source's own terms, on a set of four taxa of a binary level-1 network,
for the network multispecies coalescent at any `0 ≤ ρ ≤ 1`. `Q̃` is `qTilde`, and `m_k`-cycles are `HasCycleType`.

1. "If `N⁻` has no cycle of type `4₁` or `3₂`, then its concordance factor `CF` is tree-like, and supports the quartet `N_c⁻`. That is, if
   `N_c⁻ = ab|cd`, then `CF_AB|CD > CF_AC|BD = CF_AD|BC`."
2. "If `N⁻` has a `3₂`-cycle, [...] `CF` is on the extended line segment [...]. Specifically, if `N_c⁻ = ab|cd`, then `CF_AB|CD ≥ 1/6`, and
   `CF_AC|BD = CF_AD|BC`, and any such tree-like `CF` supports `ab|cd`."
3. "If `N⁻` has a `4₁`-cycle, then its concordance factor `CF` is not tree-like, and if `N_c⁻` displays a 4-cycle joining taxa in circular
   order `a, b, c, d`, then `CF_AB|CD > CF_AC|BD` and `CF_AD|BC > CF_AC|BD`."

The statement is on four taxa of a whole network, the concordance factor being the marginal of the gene tree on all the taxa, as in
`proposition9`. The source prints no proof: see `Proposition9.lean` and `Proposition9Part2.lean`. -/
theorem proposition9_source (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hq : #q = 4) {a b c d : {x // x ∈ q}} (h : ({a.1, b.1, c.1, d.1} : Finset X).card = 4)
    (h' : ({a.1, c.1, b.1, d.1} : Finset X).card = 4) (h'' : ({a.1, d.1, b.1, c.1} : Finset X).card = 4) :
    (¬ HasCycleType N q 4 1 → ¬ HasCycleType N q 3 2 → (qTilde hN (by omega : 2 ≤ #q)).HasQuartetTopology a b c d →
      nmscCF N θ ρ (quartetTree a.1 c.1 b.1 d.1 h') < nmscCF N θ ρ (quartetTree a.1 b.1 c.1 d.1 h) ∧
      nmscCF N θ ρ (quartetTree a.1 c.1 b.1 d.1 h') = nmscCF N θ ρ (quartetTree a.1 d.1 b.1 c.1 h'')) ∧
    (HasCycleType N q 3 2 → (qTilde hN (by omega : 2 ≤ #q)).HasQuartetTopology a b c d →
      1 / 6 ≤ nmscCF N θ ρ (quartetTree a.1 b.1 c.1 d.1 h) ∧
      nmscCF N θ ρ (quartetTree a.1 c.1 b.1 d.1 h') = nmscCF N θ ρ (quartetTree a.1 d.1 b.1 c.1 h'') ∧
      (IsT3Null (nmscCF N θ ρ) q →
        nmscCF N θ ρ (quartetTree a.1 c.1 b.1 d.1 h') < nmscCF N θ ρ (quartetTree a.1 b.1 c.1 d.1 h) ∨
          ∀ r ∈ treesOn q, nmscCF N θ ρ r = 1 / 3)) ∧
    (HasCycleType N q 4 1 → (¬ IsT3Null (nmscCF N θ ρ) q) ∧
      (HasFourCycleTopology (qTilde hN (by omega : 2 ≤ #q)) a b c d →
        nmscCF N θ ρ (quartetTree a.1 c.1 b.1 d.1 h') < nmscCF N θ ρ (quartetTree a.1 b.1 c.1 d.1 h) ∧
        nmscCF N θ ρ (quartetTree a.1 c.1 b.1 d.1 h') < nmscCF N θ ρ (quartetTree a.1 d.1 b.1 c.1 h''))) := by
  have hne : Nonempty X := ⟨a.1⟩
  have hqe := eq_of_labels hq h
  have hqe' := eq_of_labels hq h'
  have hqe'' := eq_of_labels hq h''
  have hst : (quartetTree a.1 b.1 c.1 d.1 h).taxa = q := (quartetTree_taxa _ _ _ _ _).trans hqe.symm
  have hst' : (quartetTree a.1 c.1 b.1 d.1 h').taxa = q := (quartetTree_taxa _ _ _ _ _).trans hqe'.symm
  have hst'' : (quartetTree a.1 d.1 b.1 c.1 h'').taxa = q := (quartetTree_taxa _ _ _ _ _).trans hqe''.symm
  have halt₁ : quartetTree a.1 c.1 b.1 d.1 h' ∈ (quartetTree a.1 b.1 c.1 d.1 h).alternatives :=
    QuartetTree.mem_alternatives.2 ⟨hst'.trans hst.symm, (quartetTree_ne_acbd h).symm⟩
  have halt₂ : quartetTree a.1 d.1 b.1 c.1 h'' ∈ (quartetTree a.1 b.1 c.1 d.1 h).alternatives :=
    QuartetTree.mem_alternatives.2 ⟨hst''.trans hst.symm, (quartetTree_ne_adbc h).symm⟩
  have hcut : (qTilde hN (by omega : 2 ≤ #q)).HasQuartetTopology a b c d → InducedCutSplit N (quartetTree a.1 b.1 c.1 d.1 h) := by
    intro hT
    by_cases ht : IsTreelike N q
    · exact (qTilde_hasQuartetTopology_iff hN hBin hLevel hq ht h).1 hT
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, D, -, -⟩ := exists_cycleData hN hBin hLevel hq ht
      exact ((D.hasFourCycleTopology hN hBin hLevel).not_hasQuartetTopology hT).elim
  refine ⟨fun _ h32 hT => ?_, fun h32 hT => ?_, fun h41 => ?_⟩
  · have hs := hcut hT
    have hno : ¬ HasThreeTwoCycle N (quartetTree a.1 b.1 c.1 d.1 h).taxa := by
      rw [hst, hasThreeTwoCycle_iff hN hBin hLevel hq]
      exact h32
    exact ⟨nmscCF_lt_of_no_three_two hN hBin hLevel hθ hρ hs hno halt₁, NMSC.cut_alternatives hN hθ hρ _ hs _ halt₁ _ halt₂⟩
  · have hs := hcut hT
    have h3 : HasThreeTwoCycle N q := (hasThreeTwoCycle_iff hN hBin hLevel hq).2 h32
    obtain ⟨s, hsm, hscut, -, h6, heq, hsup⟩ := proposition9_part2 hN hBin hLevel hθ hρ hq h3
    have hse : s = quartetTree a.1 b.1 c.1 d.1 h :=
      eq_of_inducedCutSplit hN hscut hs ((mem_treesOn.1 hsm).trans hst.symm)
    subst hse
    refine ⟨h6, heq _ halt₁ _ halt₂, fun hnull => ?_⟩
    rcases hsup hnull with hlt | hun
    · exact Or.inl (hlt _ halt₁)
    · exact Or.inr hun
  · have hnt := (hasCycleType_four_one_iff hN hBin hLevel hq).1 h41
    obtain ⟨a₀, h₀, T₀, k₁, k₂, pL, pR, l₀, b', P, s', D, H₁₂, H₂₃⟩ := exists_cycleData hN hBin hLevel hq hnt
    have hne' : ∀ {i j : Fin 4}, i ≠ j → l₀ i ≠ l₀ j := fun hij he => hij (D.y_inj he)
    have hc₀ : ({l₀ 0, l₀ 2, l₀ 1, l₀ 3} : Finset X).card = 4 := by
      rw [card_insert_of_notMem (by simp [hne' (show (0 : Fin 4) ≠ 2 by decide), hne' (show (0 : Fin 4) ≠ 1 by decide), hne' (show (0 : Fin 4) ≠ 3 by decide)]),
        card_insert_of_notMem (by simp [hne' (show (2 : Fin 4) ≠ 1 by decide), hne' (show (2 : Fin 4) ≠ 3 by decide)]),
        card_pair (hne' (show (1 : Fin 4) ≠ 3 by decide))]
    have hng := not_groveDisplays_of_cycle hN hBin hLevel D H₁₂ H₂₃ hc₀
    have hst₀ : (quartetTree (l₀ 0) (l₀ 2) (l₀ 1) (l₀ 3) hc₀).taxa = q := by
      rw [quartetTree_taxa]
      refine eq_of_subset_of_card_le (fun z hz => ?_) (by rw [hq, hc₀])
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> exact D.y_mem _
    have hnt' : ¬ IsTreelike N (quartetTree (l₀ 0) (l₀ 2) (l₀ 1) (l₀ 3) hc₀).taxa := by rwa [hst₀]
    have hmin := isStrictMin_of_not_groveDisplays hN hBin hLevel hθ hρ hnt' hng
    refine ⟨?_, fun hf => ?_⟩
    · have := not_isT3Null_of_isStrictMin hmin
      rwa [hst₀] at this
    · have hcl := (networkClass_eq_cycle_iff hN hBin hLevel hq h').2 hf
      rw [D.networkClass_eq hN hBin hLevel H₁₂ H₂₃ hc₀ hnt] at hcl
      have hse := QuartetClass.cycle.inj hcl
      rw [hse] at hmin
      have halt₃ : quartetTree a.1 b.1 c.1 d.1 h ∈ (quartetTree a.1 c.1 b.1 d.1 h').alternatives :=
        QuartetTree.mem_alternatives.2 ⟨hst.trans hst'.symm, quartetTree_ne_acbd h⟩
      have hne₃ : quartetTree a.1 d.1 b.1 c.1 h'' ≠ quartetTree a.1 c.1 b.1 d.1 h' := by
        intro he
        have hv : ({{a.1, d.1}, {b.1, c.1}} : Finset (Finset X)) = {{a.1, c.1}, {b.1, d.1}} := congrArg Subtype.val he
        have hm : ({a.1, d.1} : Finset X) ∈ ({{a.1, c.1}, {b.1, d.1}} : Finset (Finset X)) := hv ▸ by simp
        obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
        simp only [mem_insert, mem_singleton] at hm
        rcases hm with hm | hm
        · have : d.1 ∈ ({a.1, c.1} : Finset X) := hm ▸ by simp
          simp only [mem_insert, mem_singleton] at this
          rcases this with he' | he'
          · exact had he'.symm
          · exact hcd he'.symm
        · have : a.1 ∈ ({b.1, d.1} : Finset X) := hm ▸ by simp
          simp only [mem_insert, mem_singleton] at this
          rcases this with he' | he'
          · exact hab he'
          · exact had he'
      have halt₄ : quartetTree a.1 d.1 b.1 c.1 h'' ∈ (quartetTree a.1 c.1 b.1 d.1 h').alternatives :=
        QuartetTree.mem_alternatives.2 ⟨hst''.trans hst'.symm, hne₃⟩
      exact ⟨hmin _ halt₃, hmin _ halt₄⟩

end Bridges

end External.AllmanBanosRhodes2019.Quartet
