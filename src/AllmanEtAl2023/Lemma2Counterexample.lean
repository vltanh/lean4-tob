module

public import AllmanEtAl2023.Lemma2

/-!
# Lemma 2 of Allman, Baños, Mitchell, Rhodes 2023 needs a connected subnetwork

Lemma 2 as printed says "a subnetwork `M` of `N`". If `M` may be disconnected, the lemma is false, on a caterpillar with five taxa: take `M`
to be the pendant edges of four of them, `{a, b, c, d}`. In `M` these four are in distinct components, so deleting the cut edges incident to any
blob leaves them there, and `{a, b, c, d}` determines every blob of `M`. In `N` a cut edge separates `a, b` from `c, d`, so `{a, b, c, d}` determines
no blob. The paper's proof begins "there exist undirected paths in `M` from `ℬ₀` to each `s ∈ S`", and the paper applies the lemma to connected
subnetworks, so `Printed.lemma2` reads `M` as connected.
-/

@[expose] public section

open Phylogenetics Phylogenetics.DirectedMultigraph

namespace AllmanEtAl2023.Printed.Lemma2Counterexample

/-- The source of the edges of the caterpillar `((((a, e), b), c), d)`, with the taxa `a, b, c, d, e = 0, 1, 2, 3, 4` and the internal nodes
`5, 6, 7, 8`, from the cherry to the root. -/
def src : Fin 8 → Fin 9 := ![5, 5, 6, 6, 7, 7, 8, 8]

/-- The target of the edges of the caterpillar. -/
def tgt : Fin 8 → Fin 9 := ![0, 4, 5, 1, 6, 2, 7, 3]

/-- The caterpillar. -/
def G : DirectedMultigraph (Fin 9) (Fin 8) := ⟨src, tgt⟩

/-- The taxa, labelling the leaves. -/
def ℓ : Fin 5 → Fin 9 := Fin.castLE (by norm_num)

/-- The pendant edges of `a, b, c, d`. -/
def M : Set (Fin 8) := {0, 3, 5, 7}

/-- The four taxa. -/
def S : Finset (Fin 5) := {0, 1, 2, 3}

theorem indegree_eq (v : Fin 9) : G.indegree v = (Finset.univ.filter fun e => tgt e = v).card := by
  rw [indegree, Set.ncard_eq_toFinset_card']
  congr 1
  ext e
  simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Set.mem_toFinset

theorem outdegree_eq (v : Fin 9) : G.outdegree v = (Finset.univ.filter fun e => src e = v).card := by
  rw [outdegree, Set.ncard_eq_toFinset_card']
  congr 1
  ext e
  simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Set.mem_toFinset

theorem isLabelledNetwork : IsLabelledNetwork G ℓ where
  injective := Fin.castLE_injective _
  degree_one_iff v := by
    rw [nodeDegree, indegree_eq, outdegree_eq]
    revert v
    decide

/-- The colour of a node in `M`: the taxon whose pendant edge it is on. -/
def col : Fin 9 → Fin 5 := ![0, 1, 2, 3, 4, 0, 1, 2, 3]

theorem col_eq_of_walks {u w : Fin 9} (h : G.Walks M u w) : col u = col w := by
  have hM : ∀ e ∈ M, col (src e) = col (tgt e) := by
    intro e he
    simp only [M, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl <;> decide
  induction h with
  | refl => rfl
  | tail _ hab ih =>
    obtain ⟨e, he, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ := hab
    · exact ih.trans (hs ▸ ht ▸ hM e he)
    · exact ih.trans (ht ▸ hs ▸ (hM e he).symm)

theorem col_ℓ (s : Fin 5) : col (ℓ s) = s := by
  revert s
  decide

theorem card_S : S.card = 4 := by decide

/-- `{a, b, c, d}` determines a blob of the disconnected `M`. -/
theorem isDeterminedBy_M :
    IsDeterminedBy (restrict G M) ℓ (blobOf (restrict G M) 5) S := by
  refine isDeterminedBy_blobOf_restrict_iff.mpr ⟨by rw [card_S]; omega, fun s _ t _ hne hw => hne ?_⟩
  have h := col_eq_of_walks (walks_mono (Set.sdiff_subset) hw)
  rwa [col_ℓ, col_ℓ] at h

theorem walks_root (v : Fin 9) : G.Walks Set.univ v 8 := by
  have step : ∀ e, G.Walks Set.univ (tgt e) (src e) := fun e =>
    Relation.ReflTransGen.single ⟨e, Set.mem_univ _, Or.inr ⟨rfl, rfl⟩⟩
  have h7 : G.Walks Set.univ 7 8 := step 6
  have h3 : G.Walks Set.univ 3 8 := step 7
  have h6 : G.Walks Set.univ 6 8 := (step 4).trans h7
  have h2 : G.Walks Set.univ 2 8 := (step 5).trans h7
  have h5 : G.Walks Set.univ 5 8 := (step 2).trans h6
  have h1 : G.Walks Set.univ 1 8 := (step 3).trans h6
  have h0 : G.Walks Set.univ 0 8 := (step 0).trans h5
  have h4 : G.Walks Set.univ 4 8 := (step 1).trans h5
  fin_cases v
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact .refl

/-- The side of the edge `7 → 6`, with the taxa `a, b`. -/
def T : Set (Fin 9) := {v | v ∈ ({0, 1, 4, 5, 6} : Finset (Fin 9))}

theorem onlyCrosses_T : OnlyCrosses G Set.univ 4 T := by
  intro f _ hc
  have hd : ∀ f : Fin 8, (src f ∈ ({0, 1, 4, 5, 6} : Finset (Fin 9)) ∧ tgt f ∉ ({0, 1, 4, 5, 6} : Finset (Fin 9))) ∨
      (tgt f ∈ ({0, 1, 4, 5, 6} : Finset (Fin 9)) ∧ src f ∉ ({0, 1, 4, 5, 6} : Finset (Fin 9))) → f = 4 := by
    decide
  exact hd f hc

/-- `{a, b, c, d}` determines no blob of the caterpillar. -/
theorem not_exists_isDeterminedBy : ¬ ∃ b, IsDeterminedBy G ℓ b S := by
  rintro ⟨b, hb⟩
  induction b using Quotient.inductionOn with
  | h v =>
    have hd := (isDeterminedBy_blobOf_iff (G := G) (v := v)).mp hb
    have hw : ∀ x, G.Walks Set.univ v x := fun x => (walks_root v).trans (G.walks_symm (walks_root x))
    by_cases hv : v ∈ T
    · have hT' : v ∉ Tᶜ := not_not.mpr hv
      have : (2 : Fin 5) = 3 := hd.2.eq_of_mem_side onlyCrosses_T.compl hT' (by decide) (by decide) (hw _) (hw _)
        (by simp [T, ℓ]) (by simp [T, ℓ])
      exact absurd this (by decide)
    · have : (0 : Fin 5) = 1 := hd.2.eq_of_mem_side onlyCrosses_T hv (by decide) (by decide) (hw _) (hw _)
        (by simp [T, ℓ]) (by simp [T, ℓ])
      exact absurd this (by decide)

end Lemma2Counterexample

/-- **Lemma 2 of the paper is false for a disconnected subnetwork** (`a:claim:lem2-connected`): all its hypotheses hold, with `S` on labelled nodes of `M`,
and no blob of the network is determined by `S`. -/
theorem lemma2_false_of_not_connected :
    ∃ (W F X : Type) (G : DirectedMultigraph W F) (ℓ : X → W) (M : Set F) (S : Finset X) (v : W),
      Finite F ∧ IsLabelledNetwork G ℓ ∧ (∀ s ∈ S, ℓ s ∈ nodesOf G M) ∧ v ∈ nodesOf G M ∧
        IsDeterminedBy (restrict G M) ℓ (blobOf (restrict G M) v) S ∧ ¬ ∃ b, IsDeterminedBy G ℓ b S := by
  open Lemma2Counterexample in
  refine ⟨Fin 9, Fin 8, Fin 5, G, ℓ, M, S, 5, inferInstance, isLabelledNetwork, ?_, ?_, isDeterminedBy_M,
    not_exists_isDeterminedBy⟩
  · intro s hs
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [M], Or.inr rfl⟩
    · exact ⟨3, by simp [M], Or.inr rfl⟩
    · exact ⟨5, by simp [M], Or.inr rfl⟩
    · exact ⟨7, by simp [M], Or.inr rfl⟩
  · exact ⟨0, by simp [M], Or.inl rfl⟩

end AllmanEtAl2023.Printed
