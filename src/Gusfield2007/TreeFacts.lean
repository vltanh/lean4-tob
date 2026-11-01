module

public import Gusfield2007.Defs
public import External.SempleSteel2003.Support
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Trees, sides of edges, and labelled nodes

General facts about `SameSide`, for the proof of Theorem 4 and Section 5.1, beyond those of `External.SempleSteel2003.Support`, which `SameSide` unfolds to. The main ones:

* `exists_label_sameSide`: if every node of degree at most two is labelled, then what's left of a tree on removing two edges has a label in each part.
* `edge_eq_of_sameSide_iff`: in such a tree, two edges with the same split on the labels are equal.
* `sameSide_left_of_sameSide`: an edge can't have on one side two labels from two branches at a node, and that node on the other.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

variable {W X : Type*} {T : SimpleGraph W}

theorem SameSide.symm {e : Sym2 W} {a b : W} (h : SameSide T e a b) : SameSide T e b a := SimpleGraph.Reachable.symm h

theorem SameSide.trans {e : Sym2 W} {a b c : W} (h : SameSide T e a b) (h' : SameSide T e b c) : SameSide T e a c :=
  SimpleGraph.Reachable.trans h h'

/-- An edge of a tree has two sides: two nodes on neither side of the third are on one side. -/
theorem sameSide_of_not_sameSide (hT : T.Connected) {e : Sym2 W} {x y z : W} (hx : ¬ SameSide T e x z) (hy : ¬ SameSide T e y z) :
    SameSide T e x y := by
  induction e using Sym2.ind with
  | _ a b =>
    rcases SempleSteel2003.reachable_deleteEdges_or hT a b x with h₁ | h₁ <;> rcases SempleSteel2003.reachable_deleteEdges_or hT a b y with h₂ | h₂ <;>
      rcases SempleSteel2003.reachable_deleteEdges_or hT a b z with h₃ | h₃
    · exact h₁.symm.trans h₂
    · exact h₁.symm.trans h₂
    · exact absurd (h₁.symm.trans h₃) hx
    · exact absurd (h₂.symm.trans h₃) hy
    · exact absurd (h₂.symm.trans h₃) hy
    · exact absurd (h₁.symm.trans h₃) hx
    · exact h₁.symm.trans h₂
    · exact h₁.symm.trans h₂

/-- A walk avoiding the end `b` of an edge `s(b, y)`, and on the side of `y`, doesn't meet `b`. So a walk on a side of an edge at `b` isn't affected by removing another edge at `b`. -/
theorem sameSide_edge_of_sameSide (hT : T.IsAcyclic) {b y y' c : W} (hy : T.Adj b y) (h : SameSide T s(b, y) y c) :
    SameSide T s(b, y') y c := by
  obtain ⟨p⟩ := h
  have hb : b ∉ p.support := fun hb =>
    SempleSteel2003.not_reachable_deleteEdges hT hy (SimpleGraph.Reachable.symm ⟨p.takeUntil b hb⟩)
  have hmem : ∀ e ∈ p.edges, e ∈ (T.deleteEdges {s(b, y')}).edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_deleteEdges]
    have he₁ := p.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_deleteEdges] at he₁
    refine ⟨he₁.1, fun h => hb ?_⟩
    have h' : e = s(b, y') := h
    subst h'
    exact p.fst_mem_support_of_mem_edges he
  exact ⟨p.transfer _ hmem⟩

/-- Two labels on the far sides of two different edges at `b` are joined only through `b`. So if an edge doesn't separate them, it doesn't separate them from `b`. -/
theorem sameSide_left_of_sameSide (hT : T.IsTree) {b y₀ y₁ l₀ l₁ : W} (h₀ : T.Adj b y₀) (h₁ : T.Adj b y₁) (hne : y₀ ≠ y₁)
    (hl₀ : SameSide T s(b, y₀) y₀ l₀) (hl₁ : SameSide T s(b, y₁) y₁ l₁) {e : Sym2 W} (h : SameSide T e l₀ l₁) :
    SameSide T e b l₀ := by
  obtain ⟨p⟩ := h
  by_cases hb : b ∈ p.support
  · exact SimpleGraph.Reachable.symm ⟨p.takeUntil b hb⟩
  · exfalso
    have hmem : ∀ a ∈ p.edges, a ∈ (T.deleteEdges {s(b, y₀)}).edgeSet := by
      intro a ha
      have ha₁ := p.edges_subset_edgeSet ha
      rw [SimpleGraph.edgeSet_deleteEdges] at ha₁ ⊢
      refine ⟨ha₁.1, fun h' => hb ?_⟩
      have h'' : a = s(b, y₀) := h'
      subst h''
      exact p.fst_mem_support_of_mem_edges ha
    have h₂ : SameSide T s(b, y₀) l₀ l₁ := ⟨p.transfer _ hmem⟩
    have h₃ : SameSide T s(b, y₀) y₁ l₁ := sameSide_edge_of_sameSide hT.isAcyclic h₁ hl₁
    have h₄ : SameSide T s(b, y₀) b y₁ := (SempleSteel2003.deleteEdges_adj_of_ne h₁ fun h' => hne (Sym2.congr_right.1 h').symm).reachable
    exact SempleSteel2003.not_reachable_deleteEdges hT.isAcyclic h₀ (h₄.trans (h₃.trans (h₂.symm.trans hl₀.symm)))

/-- Each pair of labels is on one side or not by whether each is on the side of a fixed one. -/
theorem sameSide_iff_mem_edgeSide (hT : T.Connected) {φ : X → W} (e : Sym2 W) (x₀ x z : X) :
    SameSide T e (φ x) (φ z) ↔ (SameSide T e (φ x₀) (φ x) ↔ SameSide T e (φ x₀) (φ z)) := by
  constructor
  · intro h
    exact ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩
  · intro h
    by_cases hx : SameSide T e (φ x₀) (φ x)
    · exact hx.symm.trans (h.1 hx)
    · exact sameSide_of_not_sameSide hT (fun h' => hx h'.symm) (fun h' => hx (h.2 h'.symm))

/-- An isomorphism of graphs preserves the number of edges. -/
theorem ncard_edgeSet_iso {W' : Type*} {T' : SimpleGraph W'} (f : T ≃g T') : T'.edgeSet.ncard = T.edgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr f.mapEdgeSet.symm

/-- At a node with one neighbour, nothing else is on the node's side of that edge. -/
theorem sameSide_pendant {a b z : W} (ha : ∀ c, T.Adj a c → c = b) (h : SameSide T s(a, b) a z) : z = a := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons h _ =>
    rw [SimpleGraph.deleteEdges_adj] at h
    exact absurd (by rw [ha _ h.1]; exact Set.mem_singleton _) h.2

section Far

variable [Finite W]

/-- A node of degree at most one is alone on its side of its edge. -/
theorem eq_of_sameSide_of_ncard_le_one {a u c : W} (hdeg : (T.neighborSet a).ncard ≤ 1) (hu : T.Adj a u) (h : SameSide T s(a, u) a c) :
    c = a :=
  sameSide_pendant (fun _ hk => Set.ncard_le_one_iff_subsingleton.1 hdeg hk hu) h

/-- In a finite acyclic graph, the farthest node from `v` in its component has at most one neighbour, and if it's `v`, then none. -/
theorem exists_far {G : SimpleGraph W} (hG : G.IsAcyclic) (v : W) :
    ∃ y, G.Reachable v y ∧ (G.neighborSet y).Subsingleton ∧ (y = v → ∀ z, ¬ G.Adj v z) := by
  obtain ⟨y, hy, hmax⟩ := (Set.toFinite {y | G.Reachable v y}).exists_maximalFor (G.dist v) _
    ⟨v, SimpleGraph.Reachable.refl _⟩ |> fun ⟨y, hy⟩ => (⟨y, hy.1, fun z hz => not_lt.1 fun hlt => absurd (hy.2 hz hlt.le) (not_le.2 hlt)⟩ :
      ∃ y, G.Reachable v y ∧ ∀ z, G.Reachable v z → G.dist v z ≤ G.dist v y)
  have hd : ∀ z, G.Adj y z → G.dist v z + 1 = G.dist v y := by
    intro z hz
    rcases hG.dist_eq_dist_add_one_of_adj_of_reachable v hz hy with h | h
    · exact h.symm
    · have := hmax z (SimpleGraph.Reachable.trans hy hz.reachable)
      omega
  refine ⟨y, hy, ?_, ?_⟩
  · obtain ⟨p, hp, hpl⟩ := SimpleGraph.Reachable.exists_path_of_dist hy
    have hkey : ∀ z, G.Adj y z → z = p.penultimate := by
      intro z hz
      have hzr : G.Reachable v z := SimpleGraph.Reachable.trans hy hz.reachable
      obtain ⟨q, hq, hql⟩ := SimpleGraph.Reachable.exists_path_of_dist hzr
      have hy' : y ∉ q.support := by
        intro hmem
        have h₁ : G.dist v y ≤ (q.takeUntil y hmem).length := SimpleGraph.dist_le _
        have h₂ := q.length_takeUntil_le_length hmem
        have h₃ := hd z hz
        omega
      exact hG.eq_penultimate_of_adj_end hp hz (hG.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq hz hy')
    intro z₁ h₁ z₂ h₂
    exact (hkey z₁ h₁).trans (hkey z₂ h₂).symm
  · rintro rfl z hz
    have := hd z hz
    rw [SimpleGraph.dist_self] at this
    omega

/-- **The labels in a part of a tree.** If each node of degree at most two is labelled, then for two edges and a node `v`, some label is on the side of `v` of both. Taking the
two edges equal, both sides of each edge have a label. It's the reason that a middle part of a tree, between two edges, has a label: otherwise every node in it has degree at least three, and two of its nodes meet both edges. -/
theorem exists_label_sameSide (hT : T.IsTree) {φ : X → W} (hφ : ∀ v, (T.neighborSet v).ncard ≤ 2 → v ∈ Set.range φ) (e₁ e₂ : Sym2 W) (v : W) :
    ∃ x, SameSide T e₁ v (φ x) ∧ SameSide T e₂ v (φ x) := by
  set G := T.deleteEdges {e₁, e₂} with hG
  have hle : G ≤ T := SimpleGraph.deleteEdges_le _
  have hle₁ : G ≤ T.deleteEdges {e₁} := SimpleGraph.deleteEdges_anti (by simp)
  have hle₂ : G ≤ T.deleteEdges {e₂} := SimpleGraph.deleteEdges_anti (by simp)
  have hac : G.IsAcyclic := hT.isAcyclic.anti hle
  have hdone : ∀ y, G.Reachable v y → y ∈ Set.range φ → ∃ x, SameSide T e₁ v (φ x) ∧ SameSide T e₂ v (φ x) := by
    rintro _ h ⟨x, rfl⟩
    exact ⟨x, h.mono hle₁, h.mono hle₂⟩
  have hsub : ∀ (e : Sym2 W) (y : W), {z | s(y, z) = e}.Subsingleton := by
    intro e y a ha b hb
    have hab : s(y, a) = s(y, b) := by
      have ha' : s(y, a) = e := ha
      have hb' : s(y, b) = e := hb
      rw [ha', hb']
    exact (Sym2.congr_right.1 hab)
  have hdeg : ∀ y, (G.neighborSet y).Subsingleton → y ∉ Set.range φ →
      (∃ z, s(y, z) = e₁) ∧ (∃ z, s(y, z) = e₂) ∧ e₁ ≠ e₂ ∧ (G.neighborSet y).Nonempty := by
    intro y hy hy'
    have hcover : T.neighborSet y ⊆ G.neighborSet y ∪ ({z | s(y, z) = e₁} ∪ {z | s(y, z) = e₂}) := by
      intro z hz
      by_cases h₁ : s(y, z) = e₁
      · exact Or.inr (Or.inl h₁)
      · by_cases h₂ : s(y, z) = e₂
        · exact Or.inr (Or.inr h₂)
        · refine Or.inl ?_
          rw [SimpleGraph.mem_neighborSet, hG, SimpleGraph.deleteEdges_adj]
          exact ⟨hz, by simp [h₁, h₂]⟩
    have h3 : 3 ≤ (T.neighborSet y).ncard := by
      by_contra hlt
      exact hy' (hφ y (by omega))
    have hcard : ∀ s : Set W, s.Subsingleton → s.ncard ≤ 1 := fun s hs => Set.ncard_le_one_iff_subsingleton.2 hs
    have hle' := Set.ncard_le_ncard hcover (Set.toFinite _)
    have hu₁ := Set.ncard_union_le (G.neighborSet y) ({z | s(y, z) = e₁} ∪ {z | s(y, z) = e₂})
    have hu₂ := Set.ncard_union_le {z | s(y, z) = e₁} {z | s(y, z) = e₂}
    have c₀ := hcard _ hy
    have c₁ := hcard _ (hsub e₁ y)
    have c₂ := hcard _ (hsub e₂ y)
    have hne : ∀ s : Set W, s.ncard = 1 → s.Nonempty := fun s hs =>
      Set.nonempty_of_ncard_ne_zero (by omega)
    refine ⟨hne {z | s(y, z) = e₁} (by omega), hne {z | s(y, z) = e₂} (by omega), ?_, hne (G.neighborSet y) (by omega)⟩
    rintro rfl
    have hU : {z | s(y, z) = e₁} ∪ {z | s(y, z) = e₁} = {z | s(y, z) = e₁} := Set.union_self _
    rw [hU] at hcover
    have hu₃ := Set.ncard_union_le (G.neighborSet y) {z | s(y, z) = e₁}
    have hle'' := Set.ncard_le_ncard hcover (Set.toFinite _)
    omega
  obtain ⟨y₁, hy₁, hs₁, hv₁⟩ := exists_far hac v
  by_cases hl₁ : y₁ ∈ Set.range φ
  · exact hdone y₁ hy₁ hl₁
  · obtain ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩, hne, hnon⟩ := hdeg y₁ hs₁ hl₁
    obtain ⟨y₂, hy₂, hs₂, hv₂⟩ := exists_far hac y₁
    by_cases hl₂ : y₂ ∈ Set.range φ
    · exact hdone y₂ (SimpleGraph.Reachable.trans hy₁ hy₂) hl₂
    · exfalso
      obtain ⟨⟨z₃, hz₃⟩, ⟨z₄, hz₄⟩, -, -⟩ := hdeg y₂ hs₂ hl₂
      have hy₁₂ : y₂ ≠ y₁ := by
        intro h
        obtain ⟨n, hn⟩ := hnon
        exact hv₂ h n hn
      have hend : ∀ {e : Sym2 W} {a b : W}, s(y₁, a) = e → s(y₂, b) = e → a = y₂ := by
        rintro e a b rfl h
        rcases Sym2.eq_iff.1 h with ⟨h₁, -⟩ | ⟨h₁, -⟩
        · exact absurd h₁ hy₁₂
        · exact h₁.symm
      have h₁ : z₁ = y₂ := hend hz₁ hz₃
      have h₂ : z₂ = y₂ := hend hz₂ hz₄
      exact hne (by rw [← hz₁, ← hz₂, h₁, h₂])

/-- **The splits of the edges determine the edges.** In a tree whose nodes of degree at most two are labelled, edges with the same split on the labels are equal. -/
theorem edge_eq_of_sameSide_iff (hT : T.IsTree) {φ : X → W} (hφ : ∀ v, (T.neighborSet v).ncard ≤ 2 → v ∈ Set.range φ) {e₁ e₂ : Sym2 W}
    (he₁ : e₁ ∈ T.edgeSet) (h : ∀ x y, SameSide T e₁ (φ x) (φ y) ↔ SameSide T e₂ (φ x) (φ y)) : e₁ = e₂ := by
  by_contra hne
  induction e₁ using Sym2.ind with
  | _ a b =>
    have hab : T.Adj a b := he₁
    obtain ⟨x₀, h₁, h₂⟩ := exists_label_sameSide hT hφ s(a, b) e₂ a
    obtain ⟨x₁, h₃, h₄⟩ := exists_label_sameSide hT hφ s(a, b) e₂ b
    have h₅ : SameSide T e₂ a b := (SempleSteel2003.deleteEdges_adj_of_ne hab hne).reachable
    have h₆ : SameSide T e₂ (φ x₀) (φ x₁) := h₂.symm.trans (h₅.trans h₄)
    have h₇ := (h x₀ x₁).2 h₆
    exact SempleSteel2003.not_reachable_deleteEdges hT.isAcyclic hab (h₁.trans (h₇.trans h₃.symm))

end Far

end Gusfield2007
