module

public import Mathlib.Data.List.Infix

/-!
# Gene trees as sets of addresses, and quartet topologies

A rooted binary tree is given here by the addresses of its leaves, as words in `Bool`: the address of a vertex is the path to it from
the root. A cluster of the tree is the set of leaves with a given prefix. `Pat a b c d` says that the four leaves with these addresses
have the unrooted topology `ab|cd`: some cluster contains two of them, and not the other two.

* `not_pat_of_pat`: the three topologies exclude each other.
* `bal_ab`, `bal_ac`, `bal_ad`, `pat_lift`: the cases in the proof of Theorem 1 of Legried, Molloy, Warnow and Roch, for a balanced
  species quartet.
* `cat_ab`, `cat_ac`, `cat_ad`, `pat_lift_three`: the same for a caterpillar.
-/

@[expose] public section

namespace External.LegriedEtAl2021

/-- Addresses of vertices of a binary tree. -/
abbrev Path := List Bool

/-- **The unrooted topology `ab|cd` of four leaves**: a vertex has `a`, `b` below it and not `c`, `d`, or `c`, `d` and not `a`, `b`. -/
def Pat (a b c d : Path) : Prop :=
  ∃ r : Path, (r <+: a ∧ r <+: b ∧ ¬ r <+: c ∧ ¬ r <+: d) ∨ (r <+: c ∧ r <+: d ∧ ¬ r <+: a ∧ ¬ r <+: b)

theorem pat_swap_left {a b c d : Path} : Pat a b c d ↔ Pat b a c d := by
  unfold Pat
  refine exists_congr fun r => ?_
  tauto

theorem pat_swap_right {a b c d : Path} : Pat a b c d ↔ Pat a b d c := by
  unfold Pat
  refine exists_congr fun r => ?_
  tauto

theorem pat_swap_pair {a b c d : Path} : Pat a b c d ↔ Pat c d a b := by
  unfold Pat
  refine exists_congr fun r => ?_
  tauto

/-- **The topologies exclude each other**: the clusters of a tree are nested or disjoint. -/
theorem not_pat_of_pat {a b c d : Path} (h : Pat a b c d) : ¬ Pat a c b d := by
  have key : ∀ {a b c : Path} {r r' : Path}, r <+: a → r <+: b → ¬ r <+: c → r' <+: a → r' <+: c → ¬ r' <+: b → False := by
    intro a b c r r' h₁ h₂ h₃ h₄ h₅ h₆
    rcases List.prefix_or_prefix_of_prefix h₁ h₄ with h | h
    · exact h₃ (h.trans h₅)
    · exact h₆ (h.trans h₂)
  rintro ⟨r', h'⟩
  obtain ⟨r, h⟩ := h
  rcases h with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ <;> rcases h' with ⟨h₅, h₆, h₇, h₈⟩ | ⟨h₅, h₆, h₇, h₈⟩
  · exact key h₁ h₂ h₃ h₅ h₆ h₇
  · exact key h₂ h₁ h₄ h₅ h₆ h₇
  · exact key h₁ h₂ h₃ h₆ h₅ h₈
  · exact key h₂ h₁ h₄ h₆ h₅ h₈

/-- The topology `ad|bc` excludes `ab|cd`. -/
theorem not_pat_of_pat_ad {a b c d : Path} (h : Pat a d b c) : ¬ Pat a b c d :=
  fun h' => not_pat_of_pat h (pat_swap_right.1 h')

/-- The topology `ad|bc` excludes `ac|bd`. -/
theorem not_pat_of_pat_ad' {a b c d : Path} (h : Pat a d b c) : ¬ Pat a c b d :=
  fun h' => not_pat_of_pat (pat_swap_right.1 h) (pat_swap_right.1 h')

section Antichain

variable {J : Type*} {ρ : J → Path}

/-- The vertices `ρ j` are an antichain, and distinct. -/
def IsAnti (ρ : J → Path) : Prop := ∀ i j, ρ i <+: ρ j → i = j

/-- Two vertices of an antichain above one leaf are equal. -/
theorem IsAnti.eq_of_prefix (h : IsAnti ρ) {i j : J} {a : Path} (hi : ρ i <+: a) (hj : ρ j <+: a) : i = j := by
  rcases List.prefix_or_prefix_of_prefix hi hj with h' | h'
  · exact h i j h'
  · exact (h j i h').symm

/-- The two sides below vertices of an antichain have no leaf in common. -/
theorem not_side_prefix (h : IsAnti ρ) {w y : J} {e e' : Bool} (hee : e ≠ e') {c : Path} (hw : ρ w ++ [e] <+: c)
    (hy : ρ y ++ [e'] <+: c) : False := by
  have heq : w = y := h.eq_of_prefix ((List.prefix_append _ _).trans hw) ((List.prefix_append _ _).trans hy)
  subst heq
  have hle : (ρ w ++ [e]).length ≤ (ρ w ++ [e']).length := by simp
  have h₂ := List.prefix_of_prefix_length_le hw hy hle
  have h₃ := (List.prefix_append_right_inj (ρ w)).1 h₂
  rw [List.cons_prefix_cons] at h₃
  exact hee h₃.1

/-- A vertex of an antichain is above no leaf below another one. -/
theorem not_prefix_of_ne (h : IsAnti ρ) {w x : J} (hwx : w ≠ x) {b : Path} (hb : ρ x <+: b) : ¬ ρ w <+: b :=
  fun h' => hwx (h.eq_of_prefix h' hb)

/-- The addresses just below the vertices of an antichain, on one side, are an antichain. -/
theorem IsAnti.append_singleton (h : IsAnti ρ) (e : Bool) : IsAnti fun j => ρ j ++ [e] := by
  intro i j hij
  rcases List.prefix_concat_iff.1 hij with h' | h'
  · exact h i j (by rw [List.append_cancel_right h'])
  · exact h i j ((List.prefix_append _ _).trans h')

/-- A vertex above a leaf `r <+: a`, with `a` below `ρ i`, and above a leaf below another vertex, is above `ρ i`. -/
theorem prefix_of_two (h : IsAnti ρ) {i j : J} {p q r : Path} (hij : i ≠ j) (hp : ρ i <+: p) (hq : ρ j <+: q)
    (hrp : r <+: p) (hrq : r <+: q) : r <+: ρ i := by
  rcases List.prefix_or_prefix_of_prefix hrp hp with h₁ | h₁
  · exact h₁
  · exact absurd (h.eq_of_prefix (h₁.trans hrq) hq) hij

/-- A vertex above `ρ i` and not above `ρ j` is not above any leaf below `ρ j`. -/
theorem not_prefix_below (h : IsAnti ρ) {i j : J} {p r : Path} (hij : i ≠ j) (hp : ρ j <+: p) (hr : r <+: ρ i)
    (hnr : ¬ r <+: ρ j) : ¬ r <+: p := by
  intro hrp
  rcases List.prefix_or_prefix_of_prefix hrp hp with h₁ | h₁
  · exact hnr h₁
  · exact hij (h j i (h₁.trans hr)).symm

/-- **On leaves below four distinct vertices of an antichain, the topology is that of these vertices.** -/
theorem pat_lift (h : IsAnti ρ) {w x y z : J} (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) (hxy : x ≠ y) (hyz : y ≠ z)
    {a b c d : Path} (ha : ρ w <+: a) (hb : ρ x <+: b) (hc : ρ y <+: c) (hd : ρ z <+: d) :
    Pat a b c d ↔ Pat (ρ w) (ρ x) (ρ y) (ρ z) := by
  constructor
  · rintro ⟨r, ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩⟩
    · exact ⟨r, Or.inl ⟨prefix_of_two h hwx ha hb h₁ h₂, prefix_of_two h hwx.symm hb ha h₂ h₁,
        fun h' => h₃ (h'.trans hc), fun h' => h₄ (h'.trans hd)⟩⟩
    · exact ⟨r, Or.inr ⟨prefix_of_two h hyz hc hd h₁ h₂, prefix_of_two h hyz.symm hd hc h₂ h₁,
        fun h' => h₃ (h'.trans ha), fun h' => h₄ (h'.trans hb)⟩⟩
  · rintro ⟨r, ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩⟩
    · exact ⟨r, Or.inl ⟨h₁.trans ha, h₂.trans hb, not_prefix_below h hwy hc h₁ h₃, not_prefix_below h hwz hd h₁ h₄⟩⟩
    · exact ⟨r, Or.inr ⟨h₁.trans hc, h₂.trans hd, not_prefix_below h hwy.symm ha h₁ h₃,
        not_prefix_below h hxy.symm hb h₁ h₄⟩⟩

/-- **On leaves below three distinct vertices of an antichain, and a fourth leaf below none of them, the topology is that of these
vertices and the leaf.** -/
theorem pat_lift_three (h : IsAnti ρ) {w x y : J} (hwx : w ≠ x) (hwy : w ≠ y) (hxy : x ≠ y) {a b c d : Path}
    (hdρ : ∀ j, ¬ ρ j <+: d) (ha : ρ w <+: a) (hb : ρ x <+: b) (hc : ρ y <+: c) :
    Pat a b c d ↔ Pat (ρ w) (ρ x) (ρ y) d := by
  have hup : ∀ {i : J} {p r : Path}, ρ i <+: p → r <+: p → r <+: d → r <+: ρ i := by
    intro i p r hp hrp hrd
    rcases List.prefix_or_prefix_of_prefix hrp hp with h₁ | h₁
    · exact h₁
    · exact absurd (h₁.trans hrd) (hdρ i)
  constructor
  · rintro ⟨r, ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩⟩
    · exact ⟨r, Or.inl ⟨prefix_of_two h hwx ha hb h₁ h₂, prefix_of_two h hwx.symm hb ha h₂ h₁,
        fun h' => h₃ (h'.trans hc), h₄⟩⟩
    · exact ⟨r, Or.inr ⟨hup hc h₁ h₂, h₂, fun h' => h₃ (h'.trans ha), fun h' => h₄ (h'.trans hb)⟩⟩
  · rintro ⟨r, ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩⟩
    · exact ⟨r, Or.inl ⟨h₁.trans ha, h₂.trans hb, not_prefix_below h hwy hc h₁ h₃, h₄⟩⟩
    · exact ⟨r, Or.inr ⟨h₁.trans hc, h₂, not_prefix_below h hwy.symm ha h₁ h₃, not_prefix_below h hxy.symm hb h₁ h₄⟩⟩

/-! ### Balanced: `a, b` on side `e` of their vertices, `c, d` on the other -/

section Balanced

variable {w x y z : J} {a b c d : Path} {e : Bool}

/-- Two of the leaves below the same vertex and on the same side: the species quartet. -/
theorem bal_ab (h : IsAnti ρ) (ha : ρ w ++ [e] <+: a) (hb : ρ x ++ [e] <+: b) (hc : ρ y ++ [!e] <+: c)
    (hd : ρ z ++ [!e] <+: d) (hE : w = x ∨ y = z) : Pat a b c d := by
  rcases hE with rfl | rfl
  · exact ⟨ρ w ++ [e], Or.inl ⟨ha, hb, fun h' => not_side_prefix h (by simp) h' hc,
      fun h' => not_side_prefix h (by simp) h' hd⟩⟩
  · exact ⟨ρ y ++ [!e], Or.inr ⟨hc, hd, fun h' => not_side_prefix h (by simp) h' ha,
      fun h' => not_side_prefix h (by simp) h' hb⟩⟩

/-- `a`, `c` below one vertex, apart from `b`, `d`: the quartet `ac|bd`. -/
theorem bal_ac (h : IsAnti ρ) (ha : ρ w <+: a) (hb : ρ x <+: b) (hc : ρ y <+: c) (hd : ρ z <+: d) (hwx : w ≠ x)
    (hyz : y ≠ z) (hs : w = y ∨ x = z) : Pat a c b d := by
  rcases hs with rfl | rfl
  · exact ⟨ρ w, Or.inl ⟨ha, hc, not_prefix_of_ne h hwx hb, not_prefix_of_ne h hyz hd⟩⟩
  · exact ⟨ρ x, Or.inr ⟨hb, hd, not_prefix_of_ne h hwx.symm ha, not_prefix_of_ne h hyz.symm hc⟩⟩

/-- `a`, `d` below one vertex, apart from `b`, `c`: the quartet `ad|bc`. -/
theorem bal_ad (h : IsAnti ρ) (ha : ρ w <+: a) (hb : ρ x <+: b) (hc : ρ y <+: c) (hd : ρ z <+: d) (hwx : w ≠ x)
    (hyz : y ≠ z) (hs : w = z ∨ x = y) : Pat a d b c :=
  bal_ac h ha hb hd hc hwx hyz.symm hs

end Balanced

/-! ### Caterpillar: `a, b` on side `e`, `c` on the other, and `d` below no vertex -/

section Caterpillar

variable {w x y : J} {a b c d : Path} {e : Bool}

/-- `a`, `b` below one vertex: the species quartet. -/
theorem cat_ab (h : IsAnti ρ) (hdρ : ∀ j, ¬ ρ j <+: d) (ha : ρ w ++ [e] <+: a) (hb : ρ x ++ [e] <+: b)
    (hc : ρ y ++ [!e] <+: c) (hE : w = x) : Pat a b c d := by
  subst hE
  exact ⟨ρ w ++ [e], Or.inl ⟨ha, hb, fun h' => not_side_prefix h (by simp) h' hc,
    fun h' => hdρ w ((List.prefix_append _ _).trans h')⟩⟩

/-- `a`, `c` below one vertex, apart from `b`, and `d`: the quartet `ac|bd`. -/
theorem cat_ac (h : IsAnti ρ) (hdρ : ∀ j, ¬ ρ j <+: d) (ha : ρ w <+: a) (hb : ρ x <+: b) (hc : ρ y <+: c)
    (hwx : w ≠ x) (hy : y = w) : Pat a c b d := by
  subst hy
  exact ⟨ρ y, Or.inl ⟨ha, hc, not_prefix_of_ne h hwx hb, hdρ y⟩⟩

/-- `b`, `c` below one vertex, apart from `a`, and `d`: the quartet `ad|bc`. -/
theorem cat_ad (h : IsAnti ρ) (hdρ : ∀ j, ¬ ρ j <+: d) (ha : ρ w <+: a) (hb : ρ x <+: b) (hc : ρ y <+: c)
    (hwx : w ≠ x) (hy : y = x) : Pat a d b c := by
  subst hy
  exact ⟨ρ y, Or.inr ⟨hb, hc, not_prefix_of_ne h hwx.symm ha, hdρ y⟩⟩

end Caterpillar

end Antichain

end External.LegriedEtAl2021
