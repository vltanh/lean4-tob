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

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- **Theorem 4.1** (`ecto:thm4_1`). Let `N` be a rooted network on `X`, not necessarily binary, and
`A|B` a split of `X`, with partitions `A = A₁ ⊔ A₂`, `B = B₁ ⊔ B₂` into nonempty sets. If for all
`aᵢ ∈ Aᵢ`, `bᵢ ∈ Bᵢ` the split `a₁a₂|b₁b₂` is a cut-edge split of the induced 4-taxon network, then
`A|B` is a cut-edge split of `N`. -/
theorem theorem4_1 (hN : N.IsPhylogenetic) (A₁ A₂ B₁ B₂ : Finset X)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂) (hAB : Disjoint (A₁ ∪ A₂) (B₁ ∪ B₂))
    (hcover : (A₁ ∪ A₂) ∪ (B₁ ∪ B₂) = Finset.univ)
    (h : ∀ a₁ ∈ A₁, ∀ a₂ ∈ A₂, ∀ b₁ ∈ B₁, ∀ b₂ ∈ B₂,
      N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X)) :
    N.HasCutSplit ((A₁ ∪ A₂ : Finset X) : Set X) := by
  sorry

/-- **Corollary 4.2** (`ecto:cor4_2`). Let `A|B` be a non-trivial split of `X`. Either `A|B` is a
cut-edge split of `N`, or for any `a₁ ∈ A`, `b₁ ∈ B` there are distinct taxa `a₂ ∈ A`, `b₂ ∈ B` such
that `a₁a₂|b₁b₂` is not a cut-edge split of the induced network on `a₁, a₂, b₁, b₂`. -/
theorem corollary4_2 (hN : N.IsPhylogenetic) (A : Finset X) (hA : 2 ≤ A.card) (hB : 2 ≤ Aᶜ.card) :
    N.HasCutSplit (A : Set X) ∨ ∀ a₁ ∈ A, ∀ b₁ ∈ Aᶜ, ∃ a₂ ∈ A, ∃ b₂ ∈ Aᶜ, a₂ ≠ a₁ ∧ b₂ ≠ b₁ ∧
      ¬ N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X) := by
  sorry

/-- **Corollary 4.3** (`ecto:cor4_3`). Let `A|B` be a split of `X` with finer partitions
`A = ⊔ᵢ Aᵢ`, `B = ⊔ⱼ Bⱼ` into nonempty sets, at least two on each side. Either `A|B` is a cut-edge
split of `N`, or for any choice of `Aᵢ` and `Bⱼ` there are `a₁ ∈ Aᵢ`, `a₂ ∈ A \ Aᵢ`, `b₁ ∈ Bⱼ`,
`b₂ ∈ B \ Bⱼ` such that `a₁a₂|b₁b₂` is not a cut-edge split of the induced network. -/
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
  sorry

end ECToBlob
