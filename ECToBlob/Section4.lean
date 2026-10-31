module

public import Basic.Phylogenetics.NetworkCuts

/-!
# ECToBlob §4: combinatorics of quartets and cut-edge splits

Theorem 4.1 and Corollaries 4.2 and 4.3. A split of the taxa is given by one of its sides; a
cut-edge split of the induced 4-taxon network on `a₁, a₂, b₁, b₂` is
`N.HasCutSplitOn {a₁, a₂, b₁, b₂} {a₁, a₂}`.
-/

@[expose] public section

open Phylogenetics Phylogenetics.RootedNetwork

namespace ECToBlob

/-! ### The cut edges of a quartet, through domination -/

section QuartetCutArcs

variable {V E X : Type*} {N : RootedNetwork V E X}

/-- The arc `e` is a cut edge of the subgraph induced on `a₁, a₂, b₁, b₂` inducing `a₁a₂|b₁b₂`,
in the terms of `hasCutSplitOn_iff_separates`. The arcs satisfying this are the set `E` of the proof
of Theorem 4.1. -/
def QuartetCutArc (N : RootedNetwork V E X) (e : E) (a₁ a₂ b₁ b₂ : X) : Prop :=
  (N.Dominates e a₁ ∧ N.Dominates e a₂ ∧ ¬ N.IsBelow e b₁ ∧ ¬ N.IsBelow e b₂) ∨
    (N.Dominates e b₁ ∧ N.Dominates e b₂ ∧ ¬ N.IsBelow e a₁ ∧ ¬ N.IsBelow e a₂)

/-- The arc `e` is a cut edge of the subgraph `G̃₃` induced on `p, q, r` inducing `p|qr`. -/
def TripleCutArc (N : RootedNetwork V E X) (e : E) (p q r : X) : Prop :=
  (N.Dominates e p ∧ ¬ N.IsBelow e q ∧ ¬ N.IsBelow e r) ∨
    (N.Dominates e q ∧ N.Dominates e r ∧ ¬ N.IsBelow e p)

theorem QuartetCutArc.tripleCutArc {e : E} {z p q r : X} (h : QuartetCutArc N e z p q r) :
    TripleCutArc N e p q r := by
  rcases h with ⟨-, hp, hq, hr⟩ | ⟨hq, hr, -, hp⟩
  · exact Or.inl ⟨hp, hq, hr⟩
  · exact Or.inr ⟨hq, hr, hp⟩

theorem quartetCutArc_comm_left {e : E} {a₁ a₂ b₁ b₂ : X} :
    QuartetCutArc N e a₂ a₁ b₁ b₂ ↔ QuartetCutArc N e a₁ a₂ b₁ b₂ := by
  simp only [QuartetCutArc]
  tauto

theorem quartetCutArc_comm_right {e : E} {a₁ a₂ b₁ b₂ : X} :
    QuartetCutArc N e a₁ a₂ b₂ b₁ ↔ QuartetCutArc N e a₁ a₂ b₁ b₂ := by
  simp only [QuartetCutArc]
  tauto

theorem quartetCutArc_swap {e : E} {a₁ a₂ b₁ b₂ : X} :
    QuartetCutArc N e b₁ b₂ a₁ a₂ ↔ QuartetCutArc N e a₁ a₂ b₁ b₂ := by
  simp only [QuartetCutArc]
  tauto

/-- If `g`, below `g'`, dominates `z`, then so does `g'`, when `g'` dominates a taxon `p` that `g`
has below it. In the proof of Theorem 4.1, this is a funnel of `z` whose attachment on one side of
`g` is on the same side of `g'`, for two arcs above `p`. -/
theorem dominates_of_below_of_dominates (hN : N.IsPhylogenetic) {g g' : E} {z p : X}
    (hab : N.graph.Reaches (N.graph.target g') (N.graph.source g))
    (hz : N.Dominates g z) (hp : N.Dominates g' p) (hb : N.IsBelow g p) : N.Dominates g' z := by
  intro hav
  have hne : g ≠ g' := by
    rintro rfl
    exact not_reaches_target_source hN.acyclic _ hab
  have hb' : N.graph.Reaches (N.graph.target g') (N.graph.target g) := hab.tail ⟨g, rfl, rfl⟩
  exact hp (((hav.source_of_not_avoidingReach hz).tail ⟨g, hne, rfl, rfl⟩).trans
    (avoidingReach_of_target_reaches hN.acyclic hb' hb))

/-- If `g` dominates `z, p` and `g'` dominates `q`, while `q` is not below `g` nor `p` below `g'`,
then `z` is not below `g'`. This is the case of the proof of Theorem 4.1 where the root lies between
`g` and `g'` on `G̃₃`: a funnel of `z` attached on the `p`-side of `g` is on the `p`-side of `g'`.
-/
theorem not_isBelow_of_opposite (hN : N.IsPhylogenetic) {g g' : E} {z p q : X}
    (hz : N.Dominates g z) (hp : N.Dominates g p) (hq : ¬ N.IsBelow g q)
    (hq' : N.Dominates g' q) (hp' : ¬ N.IsBelow g' p) : ¬ N.IsBelow g' z := by
  intro hzb
  by_cases ha : N.AvoidingReach g (N.graph.target g') (N.leaf z)
  · by_cases hs : N.AvoidingReach g N.root (N.graph.source g')
    · have hne : g' ≠ g := by
        rintro rfl
        exact hp' (hp.isBelow hN)
      exact hz ((hs.tail ⟨g', hne, rfl, rfl⟩).trans ha)
    · have hr := target_reaches_of_not_avoidingReach (hN.root_reaches _) hs
      exact hq ((hr.tail ⟨g', rfl, rfl⟩).trans (hq'.isBelow hN))
  · have hr := reaches_source_of_not_avoidingReach hzb ha
    exact hp' ((hr.tail ⟨g, rfl, rfl⟩).trans (hp.isBelow hN))

/-- **The cut edges of `G̃₃` form a chain** (proof of Theorem 4.1), ordered by their sides
containing `p`, and the cut edges of `G̃₃` that remain cut edges after attaching the funnel of a
taxon `z` on the `p`-side form an up-set: for any two of them, one of `g`, `g'` is a cut edge after
attaching the funnel of `z` whenever the other is. -/
theorem TripleCutArc.up_or_up (hN : N.IsPhylogenetic) {p q r : X} {g g' : E}
    (hg : TripleCutArc N g p q r) (hg' : TripleCutArc N g' p q r) :
    (∀ z, QuartetCutArc N g z p q r → QuartetCutArc N g' z p q r) ∨
      ∀ z, QuartetCutArc N g' z p q r → QuartetCutArc N g z p q r := by
  by_cases hgg : g = g'
  · subst hgg
    exact Or.inl fun _ h => h
  rcases hg with ⟨hp, hq, hr⟩ | ⟨hq, hr, hp⟩ <;> rcases hg' with ⟨hp', hq', hr'⟩ | ⟨hq', hr', hp'⟩
  · -- both arcs are above `p`
    have up : ∀ {g g' : E}, N.Dominates g p → N.Dominates g' p → ¬ N.IsBelow g' q →
        ¬ N.IsBelow g' r → N.graph.Reaches (N.graph.target g') (N.graph.source g) →
        ∀ z, QuartetCutArc N g z p q r → QuartetCutArc N g' z p q r := by
      intro g g' hp hp' hq' hr' hab z hz
      rcases hz with ⟨hz, -, -, -⟩ | ⟨-, -, -, hnp⟩
      · exact Or.inl ⟨dominates_of_below_of_dominates hN hab hz hp' (hp.isBelow hN), hp', hq', hr'⟩
      · exact absurd (hp.isBelow hN) hnp
    rcases hp.reaches_or_reaches hN hp' hgg with h | h
    · exact Or.inr (up hp' hp hq hr h)
    · exact Or.inl (up hp hp' hq' hr' h)
  · -- `g` is above `p`, `g'` above `q` and `r`: the root is between them
    left
    intro z hz
    rcases hz with ⟨hz, -, -, -⟩ | ⟨-, -, -, hnp⟩
    · exact Or.inr ⟨hq', hr', not_isBelow_of_opposite hN hz hp hq hq' hp', hp'⟩
    · exact absurd (hp.isBelow hN) hnp
  · right
    intro z hz
    rcases hz with ⟨hz, -, -, -⟩ | ⟨-, -, -, hnp⟩
    · exact Or.inr ⟨hq, hr, not_isBelow_of_opposite hN hz hp' hq' hq hp, hp⟩
    · exact absurd (hp'.isBelow hN) hnp
  · -- both arcs are above `q` and `r`
    have up : ∀ {g g' : E}, N.Dominates g' q → N.Dominates g' r → ¬ N.IsBelow g p →
        ¬ N.IsBelow g' p → N.graph.Reaches (N.graph.target g) (N.graph.source g') →
        ∀ z, QuartetCutArc N g z p q r → QuartetCutArc N g' z p q r := by
      intro g g' hq' hr' hp hp' hab z hz
      rcases hz with ⟨-, hdp, -, -⟩ | ⟨-, -, hnz, -⟩
      · exact absurd (hdp.isBelow hN) hp
      · exact Or.inr ⟨hq', hr', fun hb => hnz ((hab.tail ⟨g', rfl, rfl⟩).trans hb), hp'⟩
    rcases hq.reaches_or_reaches hN hq' hgg with h | h
    · exact Or.inl (up hq' hr' hp hp' h)
    · exact Or.inr (up hq hr hp' hp h)

/-- For two taxa `z`, `z'`, the sets of cut edges `E(z, p, q, r)` and `E(z', p, q, r)` are up-sets
of the chain of cut edges of `G̃₃`, so they are comparable under inclusion. -/
theorem quartetCutArc_comparable (hN : N.IsPhylogenetic) (z z' p q r : X) :
    {e | QuartetCutArc N e z p q r} ⊆ {e | QuartetCutArc N e z' p q r} ∨
      {e | QuartetCutArc N e z' p q r} ⊆ {e | QuartetCutArc N e z p q r} := by
  by_contra hcon
  simp only [Set.not_subset, not_or, Set.mem_ofPred_eq] at hcon
  obtain ⟨⟨g, hg, hg'⟩, g', hh, hh'⟩ := hcon
  rcases hg.tripleCutArc.up_or_up hN hh.tripleCutArc with h | h
  · exact hh' (h z hg)
  · exact hg' (h z' hh)

/-- The minimality step of Theorem 4.1: of two comparable finite sets, the one that is not larger
is contained in the other. -/
theorem subset_of_comparable_of_ncard_le {α : Type*} [Finite α] {s t : Set α}
    (h : s ⊆ t ∨ t ⊆ s) (hc : s.ncard ≤ t.ncard) : s ⊆ t := by
  rcases h with h | h
  · exact h
  · exact (Set.eq_of_subset_of_ncard_le h hc).symm.subset

/-- The final assembly of Theorem 4.1 (the paper's "reasoning similarly"): if `e`, oriented so that
it dominates `a₁, a₂`, remains a cut edge after replacing any one of the four taxa by a taxon of its
block, then it dominates all taxa of the first two blocks and has no taxon of the last two below it.
-/
theorem separates_of_forall_quartetCutArc (hN : N.IsPhylogenetic) {e : E} {a₁ a₂ b₁ b₂ : X}
    (ha₁ : N.Dominates e a₁) (ha₂ : N.Dominates e a₂) {P₁ P₂ Q₁ Q₂ : Set X}
    (hP₁ : ∀ z ∈ P₁, QuartetCutArc N e z a₂ b₁ b₂) (hP₂ : ∀ z ∈ P₂, QuartetCutArc N e a₁ z b₁ b₂)
    (hQ₁ : ∀ z ∈ Q₁, QuartetCutArc N e a₁ a₂ z b₂) (hQ₂ : ∀ z ∈ Q₂, QuartetCutArc N e a₁ a₂ b₁ z) :
    (∀ z ∈ P₁ ∪ P₂, N.Dominates e z) ∧ ∀ z ∈ Q₁ ∪ Q₂, ¬ N.IsBelow e z := by
  have h₁ := ha₁.isBelow hN
  have h₂ := ha₂.isBelow hN
  constructor
  · rintro z (hz | hz)
    · rcases hP₁ z hz with ⟨h, -⟩ | ⟨-, -, -, h⟩
      · exact h
      · exact absurd h₂ h
    · rcases hP₂ z hz with ⟨-, h, -⟩ | ⟨-, -, h, -⟩
      · exact h
      · exact absurd h₁ h
  · rintro z (hz | hz)
    · rcases hQ₁ z hz with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩
      · exact h
      · exact absurd h₁ h
    · rcases hQ₂ z hz with ⟨-, -, -, h⟩ | ⟨-, -, h, -⟩
      · exact h
      · exact absurd h₁ h

end QuartetCutArcs

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

omit [Fintype X] in
/-- A cut-edge split of the induced 4-taxon network gives an arc of `E`. -/
theorem exists_quartetCutArc (hN : N.IsPhylogenetic) {a₁ a₂ b₁ b₂ : X}
    (h₁₁ : a₁ ≠ b₁) (h₁₂ : a₁ ≠ b₂) (h₂₁ : a₂ ≠ b₁) (h₂₂ : a₂ ≠ b₂)
    (h : N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X)) :
    ∃ e, QuartetCutArc N e a₁ a₂ b₁ b₂ := by
  rw [hasCutSplitOn_iff_separates hN] at h
  have m₁ : a₁ ∈ (({a₁, a₂, b₁, b₂} : Finset X) : Set X) ∩ (({a₁, a₂} : Finset X) : Set X) := by
    simp
  have m₂ : a₂ ∈ (({a₁, a₂, b₁, b₂} : Finset X) : Set X) ∩ (({a₁, a₂} : Finset X) : Set X) := by
    simp
  have m₃ : b₁ ∈ (({a₁, a₂, b₁, b₂} : Finset X) : Set X) \ (({a₁, a₂} : Finset X) : Set X) := by
    simp [h₁₁.symm, h₂₁.symm]
  have m₄ : b₂ ∈ (({a₁, a₂, b₁, b₂} : Finset X) : Set X) \ (({a₁, a₂} : Finset X) : Set X) := by
    simp [h₁₂.symm, h₂₂.symm]
  obtain ⟨e, ⟨-, hd, hn⟩ | ⟨-, hd, hn⟩⟩ := h
  · exact ⟨e, Or.inl ⟨hd _ m₁, hd _ m₂, hn _ m₃, hn _ m₄⟩⟩
  · exact ⟨e, Or.inr ⟨hd _ m₃, hd _ m₄, hn _ m₁, hn _ m₂⟩⟩

set_option linter.unusedVariables false in
/-- **Theorem 4.1** (`ecto:thm4_1`). Let `N` be a rooted network on `X`, not necessarily binary, and
`A|B` a split of `X`, with partitions `A = A₁ ⊔ A₂`, `B = B₁ ⊔ B₂` into nonempty sets. If for all
`aᵢ ∈ Aᵢ`, `bᵢ ∈ Bᵢ` the split `a₁a₂|b₁b₂` is a cut-edge split of the induced 4-taxon network, then
`A|B` is a cut-edge split of `N`.

The proof is the paper's minimal-count argument, with cut edges, nestedness and funnels expressed
through domination (`quartetCutArc_comparable`). Choose a quadruple with the fewest cut edges
inducing its split. For one taxon replaced by another of its block, the two sets of cut edges are
up-sets of the chain of cut edges of `G̃₃`, hence comparable, so by minimality an arc of the minimal
set remains a cut edge. The paper's "reasoning similarly" is `separates_of_forall_quartetCutArc`,
taxon by taxon. The disjointness of `A₁, A₂` and of `B₁, B₂` is not used. -/
theorem theorem4_1 (hN : N.IsPhylogenetic) (A₁ A₂ B₁ B₂ : Finset X)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂) (hAB : Disjoint (A₁ ∪ A₂) (B₁ ∪ B₂))
    (hcover : (A₁ ∪ A₂) ∪ (B₁ ∪ B₂) = Finset.univ)
    (h : ∀ a₁ ∈ A₁, ∀ a₂ ∈ A₂, ∀ b₁ ∈ B₁, ∀ b₂ ∈ B₂,
      N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X)) :
    N.HasCutSplit ((A₁ ∪ A₂ : Finset X) : Set X) := by
  have : Finite E := hN.finite_arcs
  have hne : ∀ {a b : X}, a ∈ A₁ ∪ A₂ → b ∈ B₁ ∪ B₂ → a ≠ b := fun ha hb hab =>
    Finset.disjoint_left.mp hAB ha (hab ▸ hb)
  -- the quadruple with the fewest cut edges
  let cuts : X × X × X × X → Set E := fun t => {e | QuartetCutArc N e t.1 t.2.1 t.2.2.1 t.2.2.2}
  obtain ⟨⟨a₁, a₂, b₁, b₂⟩, ht, hmin⟩ := Finset.exists_min_image (A₁ ×ˢ A₂ ×ˢ B₁ ×ˢ B₂)
    (fun t => (cuts t).ncard) (hA₁.product (hA₂.product (hB₁.product hB₂)))
  simp only [Finset.mem_product] at ht
  obtain ⟨ha₁, ha₂, hb₁, hb₂⟩ := ht
  have hmem₁ : ∀ {z}, z ∈ A₁ → z ∈ A₁ ∪ A₂ := fun hz => Finset.mem_union_left _ hz
  have hmem₂ : ∀ {z}, z ∈ A₂ → z ∈ A₁ ∪ A₂ := fun hz => Finset.mem_union_right _ hz
  have hmem₃ : ∀ {z}, z ∈ B₁ → z ∈ B₁ ∪ B₂ := fun hz => Finset.mem_union_left _ hz
  have hmem₄ : ∀ {z}, z ∈ B₂ → z ∈ B₁ ∪ B₂ := fun hz => Finset.mem_union_right _ hz
  obtain ⟨e, he⟩ := exists_quartetCutArc hN (hne (hmem₁ ha₁) (hmem₃ hb₁))
    (hne (hmem₁ ha₁) (hmem₄ hb₂)) (hne (hmem₂ ha₂) (hmem₃ hb₁)) (hne (hmem₂ ha₂) (hmem₄ hb₂))
    (h a₁ ha₁ a₂ ha₂ b₁ hb₁ b₂ hb₂)
  -- minimality: `e` remains a cut edge after replacing one taxon by another of its block
  have hP₁ : ∀ z ∈ (A₁ : Set X), QuartetCutArc N e z a₂ b₁ b₂ := fun z hz =>
    subset_of_comparable_of_ncard_le (quartetCutArc_comparable hN a₁ z a₂ b₁ b₂)
      (hmin (z, a₂, b₁, b₂) (by simp only [Finset.mem_product]; exact ⟨hz, ha₂, hb₁, hb₂⟩)) he
  have hP₂ : ∀ z ∈ (A₂ : Set X), QuartetCutArc N e a₁ z b₁ b₂ := fun z hz => by
    have hsub : {f | QuartetCutArc N f a₂ a₁ b₁ b₂} ⊆ {f | QuartetCutArc N f z a₁ b₁ b₂} := by
      refine subset_of_comparable_of_ncard_le (quartetCutArc_comparable hN a₂ z a₁ b₁ b₂) ?_
      have := hmin (a₁, z, b₁, b₂) (by simp only [Finset.mem_product]; exact ⟨ha₁, hz, hb₁, hb₂⟩)
      simpa only [cuts, Set.mem_ofPred_eq, quartetCutArc_comm_left] using this
    exact quartetCutArc_comm_left.mp (hsub (quartetCutArc_comm_left.mpr he))
  have hQ₁ : ∀ z ∈ (B₁ : Set X), QuartetCutArc N e a₁ a₂ z b₂ := fun z hz => by
    have hsub : {f | QuartetCutArc N f b₁ b₂ a₁ a₂} ⊆ {f | QuartetCutArc N f z b₂ a₁ a₂} := by
      refine subset_of_comparable_of_ncard_le (quartetCutArc_comparable hN b₁ z b₂ a₁ a₂) ?_
      have := hmin (a₁, a₂, z, b₂) (by simp only [Finset.mem_product]; exact ⟨ha₁, ha₂, hz, hb₂⟩)
      simpa only [cuts, Set.mem_ofPred_eq, quartetCutArc_swap] using this
    exact quartetCutArc_swap.mp (hsub (quartetCutArc_swap.mpr he))
  have hQ₂ : ∀ z ∈ (B₂ : Set X), QuartetCutArc N e a₁ a₂ b₁ z := fun z hz => by
    have hsub : {f | QuartetCutArc N f b₂ b₁ a₁ a₂} ⊆ {f | QuartetCutArc N f z b₁ a₁ a₂} := by
      refine subset_of_comparable_of_ncard_le (quartetCutArc_comparable hN b₂ z b₁ a₁ a₂) ?_
      have := hmin (a₁, a₂, b₁, z) (by simp only [Finset.mem_product]; exact ⟨ha₁, ha₂, hb₁, hz⟩)
      simpa only [cuts, Set.mem_ofPred_eq, quartetCutArc_swap, quartetCutArc_comm_right] using this
    exact quartetCutArc_comm_right.mp (quartetCutArc_swap.mp
      (hsub (quartetCutArc_comm_left.mpr (quartetCutArc_swap.mpr he))))
  -- every taxon is on the side of `e` given by its block
  have hcov : ∀ x, x ∉ A₁ ∪ A₂ → x ∈ B₁ ∪ B₂ := fun x hx => by
    have hxu : x ∈ (A₁ ∪ A₂) ∪ (B₁ ∪ B₂) := hcover ▸ Finset.mem_univ x
    exact (Finset.mem_union.mp hxu).resolve_left hx
  have hdisj : ∀ x, x ∈ B₁ ∪ B₂ → x ∉ A₁ ∪ A₂ := fun x hx hA' => hne hA' hx rfl
  have hsets₁ : ∀ x, x ∈ ((A₁ ∪ A₂ : Finset X) : Set X) ↔ x ∈ (A₁ : Set X) ∪ (A₂ : Set X) := by
    intro x
    simp only [Finset.coe_union]
  have hsets₂ : ∀ x, x ∈ B₁ ∪ B₂ ↔ x ∈ (B₁ : Set X) ∪ (B₂ : Set X) := by
    intro x
    simp only [Finset.mem_union, Set.mem_union, Finset.mem_coe]
  rw [hasCutSplit_iff_hasCutSplitOn_univ hN, hasCutSplitOn_iff_separates hN]
  refine ⟨e, ?_⟩
  rcases he with ⟨da₁, da₂, -, -⟩ | ⟨db₁, db₂, -, -⟩
  · obtain ⟨hdom, hnb⟩ := separates_of_forall_quartetCutArc hN da₁ da₂ hP₁ hP₂ hQ₁ hQ₂
    refine Or.inl ⟨⟨a₁, Set.mem_univ _, Finset.mem_coe.mpr (hmem₁ ha₁)⟩, ?_, ?_⟩
    · exact fun x hx => hdom x ((hsets₁ x).mp hx.2)
    · exact fun x hx => hnb x ((hsets₂ x).mp (hcov x hx.2))
  · obtain ⟨hdom, hnb⟩ := separates_of_forall_quartetCutArc hN db₁ db₂
      (fun z hz => quartetCutArc_swap.mp (hQ₁ z hz))
      (fun z hz => quartetCutArc_swap.mp (hQ₂ z hz))
      (fun z hz => quartetCutArc_swap.mp (hP₁ z hz))
      (fun z hz => quartetCutArc_swap.mp (hP₂ z hz))
    refine Or.inr ⟨⟨b₁, Set.mem_univ _, ?_⟩, ?_, ?_⟩
    · exact hdisj b₁ (hmem₃ hb₁)
    · exact fun x hx => hdom x ((hsets₂ x).mp (hcov x hx.2))
    · exact fun x hx => hnb x ((hsets₁ x).mp hx.2)

/-- **Corollary 4.2** (`ecto:cor4_2`). Let `A|B` be a non-trivial split of `X`. Either `A|B` is a
cut-edge split of `N`, or for any `a₁ ∈ A`, `b₁ ∈ B` there are distinct taxa `a₂ ∈ A`, `b₂ ∈ B` such
that `a₁a₂|b₁b₂` is not a cut-edge split of the induced network on `a₁, a₂, b₁, b₂`. -/
theorem corollary4_2 (hN : N.IsPhylogenetic) (A : Finset X) (hA : 2 ≤ A.card) (hB : 2 ≤ Aᶜ.card) :
    N.HasCutSplit (A : Set X) ∨ ∀ a₁ ∈ A, ∀ b₁ ∈ Aᶜ, ∃ a₂ ∈ A, ∃ b₂ ∈ Aᶜ, a₂ ≠ a₁ ∧ b₂ ≠ b₁ ∧
      ¬ N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hcut, a₁, ha₁, b₁, hb₁, hall⟩ := hcon
  have herase : ∀ {S : Finset X} {x : X}, x ∈ S → 2 ≤ S.card → (S.erase x).Nonempty := by
    intro S x hx hS
    rw [← Finset.card_pos, Finset.card_erase_of_mem hx]
    omega
  have hcoverA : {a₁} ∪ A.erase a₁ = A := by
    rw [← Finset.insert_eq, Finset.insert_erase ha₁]
  have hcoverB : {b₁} ∪ Aᶜ.erase b₁ = Aᶜ := by
    rw [← Finset.insert_eq, Finset.insert_erase hb₁]
  have key := theorem4_1 hN {a₁} (A.erase a₁) {b₁} (Aᶜ.erase b₁)
    (Finset.singleton_nonempty _) (herase ha₁ hA) (Finset.singleton_nonempty _) (herase hb₁ hB)
    (Finset.disjoint_singleton_left.mpr (Finset.notMem_erase _ _))
    (Finset.disjoint_singleton_left.mpr (Finset.notMem_erase _ _))
    (by rw [hcoverA, hcoverB]; exact disjoint_compl_right)
    (by rw [hcoverA, hcoverB]; exact Finset.union_compl A)
    (fun a ha a₂ ha₂ b hb b₂ hb₂ => by
      rw [Finset.mem_singleton] at ha hb
      subst ha hb
      exact hall a₂ (Finset.mem_of_mem_erase ha₂) b₂ (Finset.mem_of_mem_erase hb₂)
        (Finset.ne_of_mem_erase ha₂) (Finset.ne_of_mem_erase hb₂))
  rw [hcoverA] at key
  exact hcut key

/-- **Corollary 4.3** (`ecto:cor4_3`). Let `A|B` be a split of `X` with finer partitions `A = ⊔ᵢ
Aᵢ`, `B = ⊔ⱼ Bⱼ` into nonempty sets, at least two on each side. Either `A|B` is a cut-edge split of
`N`, or for any choice of `Aᵢ` and `Bⱼ` there are `a₁ ∈ Aᵢ`, `a₂ ∈ A \ Aᵢ`, `b₁ ∈ Bⱼ`, `b₂ ∈ B \ Bⱼ`
such that `a₁a₂|b₁b₂` is not a cut-edge split of the induced network. The printed proof takes `∪_{j'
≠ i} B_{j'}` as `B₂`: the index should be `j' ≠ j`. -/
theorem corollary4_3 (hN : N.IsPhylogenetic) (A : Finset X) {na nb : ℕ}
    (hna : 2 ≤ na) (hnb : 2 ≤ nb)
    (Ablock : Fin na → Finset X) (Bblock : Fin nb → Finset X)
    (hAne : ∀ i, (Ablock i).Nonempty) (hBne : ∀ j, (Bblock j).Nonempty)
    (hAdisj : ∀ i i', i ≠ i' → Disjoint (Ablock i) (Ablock i'))
    (hBdisj : ∀ j j', j ≠ j' → Disjoint (Bblock j) (Bblock j'))
    (hAcover : Finset.univ.biUnion Ablock = A) (hBcover : Finset.univ.biUnion Bblock = Aᶜ) :
    N.HasCutSplit (A : Set X) ∨ ∀ (i : Fin na) (j : Fin nb),
      ∃ a₁ ∈ Ablock i, ∃ a₂ ∈ A \ Ablock i, ∃ b₁ ∈ Bblock j, ∃ b₂ ∈ Aᶜ \ Bblock j,
        ¬ N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X)
          (({a₁, a₂} : Finset X) : Set X) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hcut, i, j, hall⟩ := hcon
  have hrest : ∀ {n : ℕ} (block : Fin n → Finset X) (S : Finset X) (k : Fin n), 2 ≤ n →
      (∀ k, (block k).Nonempty) → (∀ k k', k ≠ k' → Disjoint (block k) (block k')) →
      Finset.univ.biUnion block = S → (S \ block k).Nonempty := by
    intro n block S k hn hne hd hS
    obtain ⟨k', hk'⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) k
    obtain ⟨x, hx⟩ := hne k'
    refine ⟨x, Finset.mem_sdiff.mpr ⟨?_, fun hxk => ?_⟩⟩
    · rw [← hS]
      exact Finset.mem_biUnion.mpr ⟨k', Finset.mem_univ _, hx⟩
    · exact Finset.disjoint_left.mp (hd k' k hk') hx hxk
  have hsub : ∀ {n : ℕ} (block : Fin n → Finset X) (S : Finset X) (k : Fin n),
      Finset.univ.biUnion block = S → block k ⊆ S := by
    intro n block S k hS x hx
    rw [← hS]
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hx⟩
  have hcoverA : Ablock i ∪ (A \ Ablock i) = A :=
    Finset.union_sdiff_of_subset (hsub Ablock A i hAcover)
  have hcoverB : Bblock j ∪ (Aᶜ \ Bblock j) = Aᶜ :=
    Finset.union_sdiff_of_subset (hsub Bblock Aᶜ j hBcover)
  have key := theorem4_1 hN (Ablock i) (A \ Ablock i) (Bblock j) (Aᶜ \ Bblock j)
    (hAne i) (hrest Ablock A i hna hAne hAdisj hAcover)
    (hBne j) (hrest Bblock Aᶜ j hnb hBne hBdisj hBcover)
    Finset.disjoint_sdiff Finset.disjoint_sdiff
    (by rw [hcoverA, hcoverB]; exact disjoint_compl_right)
    (by rw [hcoverA, hcoverB]; exact Finset.union_compl A)
    hall
  rw [hcoverA] at key
  exact hcut key

end ECToBlob
