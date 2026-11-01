module

public import Phylogenetics.Network.Cuts
public import Phylogenetics.Network.PendantCuts

/-!
# Huber, van Iersel, Jones, Moulton, Veenema-Nipius 2025, Theorem 5.1

K. T. Huber, L. van Iersel, M. Jones, V. Moulton, L. Veenema-Nipius, *When are quarnets sufficient to
reconstruct semi-directed phylogenetic networks?*, Bull. Math. Biol. 87 (2025), 136.
-/

@[expose] public section

open Phylogenetics Phylogenetics.RootedNetwork

namespace External.HuberEtAl2025

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

omit [Fintype X] in
/-- **Theorem 5.1, forward direction.** If `A|B` is the split of a cut edge, then for all distinct
`a₁, a₂ ∈ A` and `b₁, b₂ ∈ B`, `a₁a₂|b₁b₂` is the split of a cut edge of the network induced on
these taxa. The source treats binary semi-directed networks; the binary condition is not needed. -/
theorem theorem5_1_forward (hN : N.IsPhylogenetic) {A : Finset X} (hA : N.HasCutSplit (A : Set X))
    {a₁ a₂ b₁ b₂ : X} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∉ A) (hb₂ : b₂ ∉ A) :
    N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X) :=
  HasCutSplit.hasCutSplitOn_quartet hN hA ha₁ ha₂ hb₁ hb₂

/-! ### The converse

Departure from the paper: the source proves the converse on binary semi-directed networks, by induction on the non-trivial cut-edge splits, whose base case is a simple network, with its Lemmas 5.2 to 5.5 on "excellent cycles": two overlapping cycles, each with a sink adjacent to a leaf, carrying a taxon of each side. The proof here is on rooted networks of any degrees, through domination: the arcs dominating a taxon are a chain, and domination goes up it (`dominates_of_above`), so the arcs dominating sets of taxa are the common ancestors in a tree, the dominator tree. On it a set of at least two taxa has the common dominators of two of them, one of which may be chosen (`exists_pair_dominators`). If `A|B` is no cut-edge split, every arc dominating `A` has a taxon `b` of `B` below it, which may be chosen once for all (`exists_isBelow_all`), and likewise `a` for `B`: the four taxa `a, a', b, b'` then have no cut-edge split. -/

variable {e e' : E} {x y : X}

omit [Fintype X] [DecidableEq X] in
/-- Domination goes up the chain of arcs dominating a taxon: if `e` is above `e'`, both dominating `x`, what `e'` dominates `e` dominates. -/
theorem dominates_of_above (hN : N.IsPhylogenetic) (he : N.Dominates e x) (he' : N.Dominates e' x) (habove : N.graph.Reaches (N.graph.target e) (N.graph.source e'))
    (hy : N.Dominates e' y) : N.Dominates e y := by
  intro h
  have hne : e' ≠ e := fun h₀ => not_reaches_target_source hN.acyclic e (h₀ ▸ habove)
  have h₁ : N.AvoidingReach e N.root (N.graph.source e') := h.source_of_not_avoidingReach hy
  have h₂ : N.AvoidingReach e N.root (N.graph.target e') := h₁.tail ⟨e', hne, rfl, rfl⟩
  have h₃ : N.graph.Reaches (N.graph.target e) (N.graph.target e') := habove.tail ⟨e', rfl, rfl⟩
  exact he (h₂.trans (avoidingReach_of_target_reaches hN.acyclic h₃ (he'.isBelow hN)))

omit [Fintype X] [DecidableEq X] in
/-- What is below a lower arc is below a higher one. -/
theorem IsBelow.of_above (habove : N.graph.Reaches (N.graph.target e) (N.graph.source e')) (hy : N.IsBelow e' y) : N.IsBelow e y :=
  (habove.tail ⟨e', rfl, rfl⟩).trans hy

omit [Fintype X] [DecidableEq X] in
/-- If every arc dominating `L` has a taxon of `Q` below it, one taxon of `Q` is below them all: they are a chain, and it is below the lowest. -/
theorem exists_isBelow_all (hN : N.IsPhylogenetic) {L Q : Finset X} (hL : L.Nonempty) (hQ : Q.Nonempty)
    (h : ∀ e, (∀ x ∈ L, N.Dominates e x) → ∃ y ∈ Q, N.IsBelow e y) : ∃ y ∈ Q, ∀ e, (∀ x ∈ L, N.Dominates e x) → N.IsBelow e y := by
  by_contra hcon
  simp only [not_exists, not_and, not_forall] at hcon
  obtain ⟨x₀, hx₀⟩ := hL
  have key : ∀ Q' : Finset X, Q'.Nonempty → Q' ⊆ Q → ∃ e, (∀ x ∈ L, N.Dominates e x) ∧ ∀ y ∈ Q', ¬ N.IsBelow e y := by
    intro Q' hQ'
    induction hQ' using Finset.Nonempty.cons_induction with
    | singleton y =>
      intro hs
      obtain ⟨e, h₁, h₂⟩ := hcon y (hs (Finset.mem_singleton_self y))
      exact ⟨e, h₁, fun z hz => by rwa [Finset.mem_singleton.1 hz]⟩
    | cons y s hy hs ih =>
      intro hsub
      obtain ⟨e₁, h₁, h₂⟩ := ih fun z hz => hsub (Finset.mem_cons_of_mem hz)
      obtain ⟨e₂, h₃, h₄⟩ := hcon y (hsub (Finset.mem_cons_self y s))
      by_cases he : e₁ = e₂
      · subst he
        refine ⟨e₁, h₁, fun z hz => ?_⟩
        rcases Finset.mem_cons.1 hz with rfl | hz
        · exact h₄
        · exact h₂ z hz
      · rcases (h₁ x₀ hx₀).reaches_or_reaches hN (h₃ x₀ hx₀) he with ha | ha
        · refine ⟨e₂, h₃, fun z hz hb => ?_⟩
          rcases Finset.mem_cons.1 hz with rfl | hz
          · exact h₄ hb
          · exact h₂ z hz (IsBelow.of_above ha hb)
        · refine ⟨e₁, h₁, fun z hz hb => ?_⟩
          rcases Finset.mem_cons.1 hz with rfl | hz
          · exact h₄ (IsBelow.of_above ha hb)
          · exact h₂ z hz hb
  obtain ⟨e, h₁, h₂⟩ := key Q hQ Finset.Subset.rfl
  obtain ⟨y, hy, hb⟩ := h e h₁
  exact h₂ y hy hb

omit [Fintype X] in
/-- Given a taxon `a₀`, the arcs dominating a set with at least one other taxon are those dominating `a₀` and one of them. -/
theorem exists_pair_dominators (hN : N.IsPhylogenetic) {A : Finset X} (a₀ : X) (hA : (A.erase a₀).Nonempty) :
    ∃ a' ∈ A, a' ≠ a₀ ∧ ∀ e, N.Dominates e a₀ → N.Dominates e a' → ∀ a ∈ A, N.Dominates e a := by
  have key : ∀ Q : Finset X, Q.Nonempty → ∃ a' ∈ Q, ∀ e, N.Dominates e a₀ → N.Dominates e a' → ∀ a ∈ Q, N.Dominates e a := by
    intro Q hQ
    induction hQ using Finset.Nonempty.cons_induction with
    | singleton y =>
      exact ⟨y, Finset.mem_singleton_self y, fun e _ h z hz => by rwa [Finset.mem_singleton.1 hz]⟩
    | cons y s hy hs ih =>
      obtain ⟨a', ha', h₁⟩ := ih
      by_cases hsub : ∀ e, N.Dominates e a₀ → N.Dominates e a' → N.Dominates e y
      · refine ⟨a', Finset.mem_cons_of_mem ha', fun e h₂ h₃ a ha => ?_⟩
        rcases Finset.mem_cons.1 ha with rfl | ha
        · exact hsub e h₂ h₃
        · exact h₁ e h₂ h₃ a ha
      · simp only [not_forall] at hsub
        obtain ⟨e₀, h₂, h₃, h₄⟩ := hsub
        have hup : ∀ e, N.Dominates e a₀ → N.Dominates e y → N.Dominates e a' := by
          intro e h₅ h₆
          have hne : e₀ ≠ e := fun h₀ => h₄ (h₀ ▸ h₆)
          rcases h₂.reaches_or_reaches hN h₅ hne with ha | ha
          · exact absurd (dominates_of_above hN h₂ h₅ ha h₆) h₄
          · exact dominates_of_above hN h₅ h₂ ha h₃
        refine ⟨y, Finset.mem_cons_self y s, fun e h₅ h₆ a ha => ?_⟩
        rcases Finset.mem_cons.1 ha with rfl | ha
        · exact h₆
        · exact h₁ e h₅ (hup e h₅ h₆) a ha
  obtain ⟨a', ha', h₁⟩ := key (A.erase a₀) hA
  refine ⟨a', Finset.mem_of_mem_erase ha', Finset.ne_of_mem_erase ha', fun e h₂ h₃ a ha => ?_⟩
  by_cases ha₀ : a = a₀
  · exact ha₀ ▸ h₂
  · exact h₁ e h₂ h₃ a (Finset.mem_erase.2 ⟨ha₀, ha⟩)

/-- **Theorem 5.1, converse.** If `A|B` is a non-trivial split of the taxa, and `a₁a₂|b₁b₂` is the split of a cut edge of the network induced on these taxa for all distinct `a₁, a₂ ∈ A` and `b₁, b₂ ∈ B`, then `A|B` is the split of a cut edge. The source treats binary semi-directed networks; the binary condition is not needed. -/
theorem theorem5_1_converse (hN : N.IsPhylogenetic) {A : Finset X} (hA : 2 ≤ A.card) (hB : 2 ≤ Aᶜ.card)
    (h : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ → ∀ b₁ ∉ A, ∀ b₂ ∉ A, b₁ ≠ b₂ →
      N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X)) :
    N.HasCutSplit (A : Set X) := by
  rw [hasCutSplit_iff_hasCutSplitOn_univ hN, hasCutSplitOn_iff_separates hN]
  by_contra hcon
  have hAne : A.Nonempty := Finset.card_pos.1 (by omega)
  have hBne : Aᶜ.Nonempty := Finset.card_pos.1 (by omega)
  have hi : ∀ e, (∀ x ∈ A, N.Dominates e x) → ∃ y ∈ Aᶜ, N.IsBelow e y := by
    intro e he
    by_contra hb
    refine hcon ⟨e, Or.inl ⟨?_, fun x hx => he x (by simpa using hx.2), fun x hx hbx => hb ⟨x, ?_, hbx⟩⟩⟩
    · obtain ⟨x, hx⟩ := hAne
      exact ⟨x, Set.mem_univ x, hx⟩
    · simpa using hx.2
  have hii : ∀ e, (∀ x ∈ Aᶜ, N.Dominates e x) → ∃ y ∈ A, N.IsBelow e y := by
    intro e he
    by_contra hb
    refine hcon ⟨e, Or.inr ⟨?_, fun x hx => he x (by simpa using hx.2), fun x hx hbx => hb ⟨x, ?_, hbx⟩⟩⟩
    · obtain ⟨x, hx⟩ := hBne
      exact ⟨x, Set.mem_univ x, by simpa using hx⟩
    · simpa using hx.2
  obtain ⟨b, hb, hbb⟩ := exists_isBelow_all hN hAne hBne hi
  obtain ⟨a, ha, hab⟩ := exists_isBelow_all hN hBne hAne hii
  have hb₀ : b ∉ A := by simpa using hb
  obtain ⟨a', ha', hne, hpa⟩ := exists_pair_dominators hN a (A := A) (Finset.card_pos.1 (by rw [Finset.card_erase_of_mem ha]; omega))
  obtain ⟨b', hb', hne', hpb⟩ := exists_pair_dominators hN b (A := Aᶜ) (Finset.card_pos.1 (by rw [Finset.card_erase_of_mem hb]; omega))
  have hb'₀ : b' ∉ A := by simpa using hb'
  have hq := h a ha a' ha' hne.symm b hb₀ b' hb'₀ hne'.symm
  rw [hasCutSplitOn_iff_separates hN] at hq
  obtain ⟨e, ⟨_, h₁, h₂⟩ | ⟨_, h₁, h₂⟩⟩ := hq
  · have hd : ∀ x ∈ A, N.Dominates e x := hpa e (h₁ a (by simp)) (h₁ a' (by simp))
    refine h₂ b ?_ (hbb e hd)
    have hba : b ≠ a := fun h₀ => hb₀ (h₀ ▸ ha)
    have hba' : b ≠ a' := fun h₀ => hb₀ (h₀ ▸ ha')
    simp [hba, hba']
  · have hba : b ≠ a := fun h₀ => hb₀ (h₀ ▸ ha)
    have hba' : b ≠ a' := fun h₀ => hb₀ (h₀ ▸ ha')
    have hb'a : b' ≠ a := fun h₀ => hb'₀ (h₀ ▸ ha)
    have hb'a' : b' ≠ a' := fun h₀ => hb'₀ (h₀ ▸ ha')
    have hd : ∀ x ∈ Aᶜ, N.Dominates e x := hpb e (h₁ b (by simp [hba, hba'])) (h₁ b' (by simp [hb'a, hb'a']))
    exact h₂ a (by simp) (hab e hd)

/-- **Theorem 5.1** (`ext:huber_thm5_1`). A split `A|B` of the taxa is the split of a cut edge exactly when it is trivial, or it is not and `a₁a₂|b₁b₂` is the split of a cut edge of the network induced on these taxa for all distinct `a₁, a₂ ∈ A` and `b₁, b₂ ∈ B`. -/
theorem theorem5_1 (hN : N.IsPhylogenetic) {A : Finset X} (hA : A.Nonempty) (hB : Aᶜ.Nonempty) :
    N.HasCutSplit (A : Set X) ↔ (A.card = 1 ∨ Aᶜ.card = 1) ∨ (2 ≤ A.card ∧ 2 ≤ Aᶜ.card ∧ ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ → ∀ b₁ ∉ A, ∀ b₂ ∉ A, b₁ ≠ b₂ →
      N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X)) := by
  have hA₁ := Finset.card_pos.2 hA
  have hB₁ := Finset.card_pos.2 hB
  constructor
  · intro h
    by_cases h₁ : A.card = 1 ∨ Aᶜ.card = 1
    · exact Or.inl h₁
    · refine Or.inr ⟨by omega, by omega, fun a₁ ha₁ a₂ ha₂ _ b₁ hb₁ b₂ hb₂ _ => theorem5_1_forward hN h ha₁ ha₂ hb₁ hb₂⟩
  · rintro ((h₁ | h₁) | ⟨h₂, h₃, h₄⟩)
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h₁
      simpa using hasSingletonCut N hN x
    · obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h₁
      have hs := hasSingletonCut N hN x
      rw [← hasCutSplit_compl] at hs
      have : (({x} : Set X)ᶜ) = (A : Set X) := by
        rw [← Finset.coe_singleton, ← hx, Finset.coe_compl, compl_compl]
      rwa [this] at hs
    · exact theorem5_1_converse hN h₂ h₃ h₄

end External.HuberEtAl2025
