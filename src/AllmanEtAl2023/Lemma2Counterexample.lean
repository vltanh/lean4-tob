module

public import AllmanEtAl2023.Lemma2

/-!
# Lemma 2 of Allman, Baños, Mitchell, Rhodes 2023 needs a connected subnetwork

Lemma 2 needs `M` connected, or at least each `s` joined to `ℬ₀` in `M`. Its proof assumes this and all its uses satisfy it, but the word is missing. For disconnected `M`, Definition 8 can hold
vacuously and the conclusion fails. No result of the paper is affected.

Four taxa are enough: on the caterpillar `(((a, b), c), d)`, take `M` to be the pendant edges. In `M` the parent of `a, b` is a blob with `a, b` beyond its two cut edges, and `c, d` are in other
components, so `{a, b, c, d}` determines that blob. In `N` a cut edge separates `a, b` from `c, d`, so `{a, b, c, d}` determines no blob. `lemma2` takes `M` connected.
-/

@[expose] public section

open Phylogenetics Phylogenetics.DirectedMultigraph

namespace AllmanEtAl2023.Lemma2Counterexample

/-- The source of the edges of the caterpillar `(((a, b), c), d)`, with the taxa `a, b, c, d = 0, 1, 2, 3` and the internal nodes
`4, 5, 6`, from the cherry to the root. -/
def src : Fin 6 → Fin 7 := ![4, 4, 5, 5, 6, 6]

/-- The target of the edges of the caterpillar. -/
def tgt : Fin 6 → Fin 7 := ![0, 1, 4, 2, 5, 3]

/-- The caterpillar. -/
def G : DirectedMultigraph (Fin 7) (Fin 6) := ⟨src, tgt⟩

/-- The taxa, labelling the leaves. -/
def ℓ : Fin 4 → Fin 7 := Fin.castLE (by norm_num)

/-- The pendant edges. -/
def M : Set (Fin 6) := {0, 1, 3, 5}

/-- The four taxa. -/
def S : Finset (Fin 4) := Finset.univ

theorem indegree_eq (v : Fin 7) : G.indegree v = (Finset.univ.filter fun e => tgt e = v).card := by
  rw [indegree, Set.ncard_eq_toFinset_card']
  congr 1
  ext e
  simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Set.mem_toFinset

theorem outdegree_eq (v : Fin 7) : G.outdegree v = (Finset.univ.filter fun e => src e = v).card := by
  rw [outdegree, Set.ncard_eq_toFinset_card']
  congr 1
  ext e
  simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Set.mem_toFinset

theorem isLabelledNetwork : IsLabelledNetwork G ℓ where
  injective := Fin.castLE_injective _
  degree_one x := by
    rw [nodeDegree, indegree_eq, outdegree_eq]
    revert x
    decide

/-- A function constant along edges of `F` is constant along walks of `F`. -/
theorem eq_of_walks {α : Type*} (f : Fin 7 → α) {F : Set (Fin 6)} (hF : ∀ e ∈ F, f (src e) = f (tgt e)) {u w : Fin 7}
    (h : G.Walks F u w) : f u = f w := by
  induction h with
  | refl => rfl
  | tail _ hab ih =>
    obtain ⟨e, he, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ := hab
    · exact ih.trans (hs ▸ ht ▸ hF e he)
    · exact ih.trans (ht ▸ hs ▸ (hF e he).symm)

/-- The edge to `a` is a cut edge of `M`. -/
theorem isCutIn_zero : IsCutIn G M 0 := by
  refine ⟨by simp [M], fun hw => ?_⟩
  have h := eq_of_walks (fun v => decide (v = 0)) (F := M \ {0}) (fun e he => ?_) hw
  · exact absurd h (by decide)
  · obtain ⟨hM, hne⟩ := he
    simp only [M, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    all_goals decide

/-- The edge to `b` is a cut edge of `M`. -/
theorem isCutIn_one : IsCutIn G M 1 := by
  refine ⟨by simp [M], fun hw => ?_⟩
  have h := eq_of_walks (fun v => decide (v = 1)) (F := M \ {1}) (fun e he => ?_) hw
  · exact absurd h (by decide)
  · obtain ⟨hM, hne⟩ := he
    simp only [M, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl | rfl
    · decide
    · exact absurd rfl hne
    all_goals decide

/-- The component of a node in `M` without the two edges at the parent of `a, b`: a taxon of `S` for each. -/
def col : Fin 7 → Fin 4 := ![0, 1, 2, 3, 0, 2, 3]

theorem col_ℓ (s : Fin 4) : col (ℓ s) = s := by
  revert s
  decide

/-- `{a, b, c, d}` determines a blob of the disconnected `M`. -/
theorem isDeterminedBy_M : IsDeterminedBy (restrict G M) ℓ (blobOf (restrict G M) 4) S := by
  refine isDeterminedBy_blobOf_restrict_iff.mpr ⟨by decide, fun s _ t _ hne hw => hne ?_⟩
  have hF : ∀ e ∈ M \ incidentCuts G M (4 : Fin 7), col (src e) = col (tgt e) := by
    rintro e ⟨hM, hn⟩
    simp only [M, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl | rfl
    · exact absurd ⟨isCutIn_zero, Or.inl .refl⟩ hn
    · exact absurd ⟨isCutIn_one, Or.inl .refl⟩ hn
    · decide
    · decide
  have h := eq_of_walks col hF hw
  rwa [col_ℓ, col_ℓ] at h

theorem walks_root (v : Fin 7) : G.Walks Set.univ v 6 := by
  have step : ∀ e, G.Walks Set.univ (tgt e) (src e) := fun e =>
    Relation.ReflTransGen.single ⟨e, Set.mem_univ _, Or.inr ⟨rfl, rfl⟩⟩
  have h5 : G.Walks Set.univ 5 6 := step 4
  have h3 : G.Walks Set.univ 3 6 := step 5
  have h4 : G.Walks Set.univ 4 6 := (step 2).trans h5
  have h2 : G.Walks Set.univ 2 6 := (step 3).trans h5
  have h0 : G.Walks Set.univ 0 6 := (step 0).trans h4
  have h1 : G.Walks Set.univ 1 6 := (step 1).trans h4
  fin_cases v
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact .refl

/-- The side of the edge `5 → 4`, with the taxa `a, b`. -/
def T : Set (Fin 7) := {v | v ∈ ({0, 1, 4} : Finset (Fin 7))}

theorem onlyCrosses_T : OnlyCrosses G Set.univ 2 T := by
  intro f _ hc
  have hd : ∀ f : Fin 6, (src f ∈ ({0, 1, 4} : Finset (Fin 7)) ∧ tgt f ∉ ({0, 1, 4} : Finset (Fin 7))) ∨
      (tgt f ∈ ({0, 1, 4} : Finset (Fin 7)) ∧ src f ∉ ({0, 1, 4} : Finset (Fin 7))) → f = 2 := by
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
      have : (2 : Fin 4) = 3 := hd.2.eq_of_mem_side onlyCrosses_T.compl hT' (by decide) (by decide) (hw _) (hw _)
        (by simp [T, ℓ]) (by simp [T, ℓ])
      exact absurd this (by decide)
    · have : (0 : Fin 4) = 1 := hd.2.eq_of_mem_side onlyCrosses_T hv (by decide) (by decide) (hw _) (hw _)
        (by simp [T, ℓ]) (by simp [T, ℓ])
      exact absurd this (by decide)

end Lemma2Counterexample

/-- **Lemma 2 needs `M` connected, or at least each `s` joined to `ℬ₀` in `M`** (`a:claim:lem2-connected`). Its proof assumes this and all its uses satisfy it, but the word is missing. For disconnected `M`, Definition 8 can hold
vacuously and the conclusion fails, as here: all the hypotheses hold, with `S` on labelled nodes of `M`, and no blob of the network is determined by `S`. No result of the paper is affected. -/
theorem lemma2_needs_connected :
    ∃ (W F X : Type) (G : DirectedMultigraph W F) (ℓ : X → W) (M : Set F) (S : Finset X) (v : W),
      Finite F ∧ IsLabelledNetwork G ℓ ∧ (∀ s ∈ S, ℓ s ∈ nodesOf G M) ∧ v ∈ nodesOf G M ∧
        IsDeterminedBy (restrict G M) ℓ (blobOf (restrict G M) v) S ∧ ¬ ∃ b, IsDeterminedBy G ℓ b S := by
  open Lemma2Counterexample in
  refine ⟨Fin 7, Fin 6, Fin 4, G, ℓ, M, S, 4, inferInstance, isLabelledNetwork, ?_, ?_, isDeterminedBy_M,
    not_exists_isDeterminedBy⟩
  · intro s _
    fin_cases s
    · exact ⟨0, by simp [M], Or.inr rfl⟩
    · exact ⟨1, by simp [M], Or.inr rfl⟩
    · exact ⟨3, by simp [M], Or.inr rfl⟩
    · exact ⟨5, by simp [M], Or.inr rfl⟩
  · exact ⟨0, by simp [M], Or.inl rfl⟩

end AllmanEtAl2023
