module

public import ECToBlob.Section4Funnels

/-!
# ECToBlob §4: combinatorics of quartets and cut-edge splits

Theorem 4.1 and Corollaries 4.2 and 4.3, with the second sentences of the corollaries (`corollary4_2_second`,
`corollary4_3_second`). A split of the taxa is given by one of its sides; a
cut-edge split of the induced 4-taxon network on `a₁, a₂, b₁, b₂` is
`N.HasCutSplitOn {a₁, a₂, b₁, b₂} {a₁, a₂}`. The objects of the proof of Theorem 4.1, the funnels, the
subgraphs `G̃₃`, `G̃₄`, the set `E` and the sides of `G̃₃`, are in `ECToBlob/Section4Funnels.lean`.
-/

@[expose] public section

open Phylogenetics Phylogenetics.RootedNetwork External.AllmanEtAl2023

namespace ECToBlob

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- **Theorem 4.1** (`ecto:thm4_1`). Let `N` be a rooted network on `X`, not necessarily binary, and
`A|B` a split of `X`, with partitions `A = A₁ ⊔ A₂`, `B = B₁ ⊔ B₂` into nonempty sets. If for all
`aᵢ ∈ Aᵢ`, `bᵢ ∈ Bᵢ` the split `a₁a₂|b₁b₂` is a cut-edge split of the induced 4-taxon network, then
`A|B` is a cut-edge split of `N`.

The proof is the paper's, `notes/paper2026/paper.txt` lines 588-627, in its order. Choose
`ã₁, ã₂, b̃₁, b̃₂` so that the subgraph `G̃₄` induced on these taxa has the fewest cut edges inducing
`ã₁ã₂|b̃₁b̃₂`, the set `E` (`quartetCuts`), which is nonempty. The subgraph `G̃₃` induced on `ã₂, b̃₁, b̃₂`
also contains `E` (`Induces.threeTaxa`). By the minimality of `|E|`, the funnel of any `a₁ ∈ A₁` can only
attach to `G̃₃` on the `ã₂`-side (`funnel_attaches_side`), so the edges in `E` induce
`A₁ ∪ {ã₂}|{b̃₁, b̃₂}` on the subnetwork on those taxa (`induces_block`). The same holds for `ã₂, b̃₁, b̃₂`,
and so, attaching to `G̃₄` the funnels of all taxa, the edges in `E` induce `A|B` (`Induces.attach_funnels`).
The two 3-blobs of lines 591-595 are `exists_isTwoBlobs`, `IsTwoBlobs.exists_three_cuts`, `IsTwoBlobs.first_blob`, and
the chains of lines 596-597 are `chain_between`, `exists_blob_of_isNextCut` and `IsTwoBlobs.exists_two_blob` with its two
variants. The paper's proof doesn't refer to them afterwards, and this one uses only the linear order `chain_between`,
on `G̃₃`.

Departure from the paper: the paper states the 3-blobs and 2-blobs on the induced subnetwork, and they are stated here on
`G̃₄`, the graph which the rest of the proof uses. There a blob of a chain can have a third incident cut edge, the arc
coming down from the root to the LSA, which the induced subnetwork removes. So the degree of a blob is read as the
number of its incident cut edges with one of the four taxa beyond them. This is not forced: the literal statements would need
the same arguments on the induced subnetwork, for claims that nothing later uses.

What the paper leaves implicit (E4 in `REPORT.md`) is proved along its lines: the cut edges of `G̃₃`
between `ã₂` and `b̃₁` form a chain, and those of `G̃₄` an up-set of it, so two choices of `ã₁` are comparable
(`quartetCuts_subset_or_subset`); and the funnels of two taxa on opposite sides have no node in common, since
they would have a common node of attachment (`exists_common_node`, in `Induces.attach_funnels`). The
disjointness of `A₁, A₂` and of `B₁, B₂` is not used. -/
theorem theorem4_1 (hN : N.IsPhylogenetic) (A₁ A₂ B₁ B₂ : Finset X)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (hAB : Disjoint (A₁ ∪ A₂) (B₁ ∪ B₂))
    (hcover : (A₁ ∪ A₂) ∪ (B₁ ∪ B₂) = Finset.univ)
    (h : ∀ a₁ ∈ A₁, ∀ a₂ ∈ A₂, ∀ b₁ ∈ B₁, ∀ b₂ ∈ B₂,
      N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X)) :
    N.HasCutSplit ((A₁ ∪ A₂ : Finset X) : Set X) := by
  have hne : ∀ {a b : X}, a ∈ A₁ ∪ A₂ → b ∈ B₁ ∪ B₂ → a ≠ b := fun ha hb hab =>
    Finset.disjoint_left.mp hAB ha (hab ▸ hb)
  have hmem₁ : ∀ {z}, z ∈ A₁ → z ∈ A₁ ∪ A₂ := fun hz => Finset.mem_union_left _ hz
  have hmem₂ : ∀ {z}, z ∈ A₂ → z ∈ A₁ ∪ A₂ := fun hz => Finset.mem_union_right _ hz
  have hmem₃ : ∀ {z}, z ∈ B₁ → z ∈ B₁ ∪ B₂ := fun hz => Finset.mem_union_left _ hz
  have hmem₄ : ∀ {z}, z ∈ B₂ → z ∈ B₁ ∪ B₂ := fun hz => Finset.mem_union_right _ hz
  -- choose `ã₁, ã₂, b̃₁, b̃₂` with the fewest cut edges in `G̃₄` inducing `ã₁ã₂|b̃₁b̃₂` (lines 588-591)
  obtain ⟨⟨a₁, a₂, b₁, b₂⟩, ht, hmin⟩ := Finset.exists_min_image (A₁ ×ˢ A₂ ×ˢ B₁ ×ˢ B₂)
    (fun t => (quartetCuts N t.1 t.2.1 t.2.2.1 t.2.2.2).ncard)
    (hA₁.product (hA₂.product (hB₁.product hB₂)))
  simp only [Finset.mem_product] at ht
  obtain ⟨ha₁, ha₂, hb₁, hb₂⟩ := ht
  have hmin' : ∀ z₁ ∈ A₁, ∀ z₂ ∈ A₂, ∀ z₃ ∈ B₁, ∀ z₄ ∈ B₂,
      (quartetCuts N a₁ a₂ b₁ b₂).ncard ≤ (quartetCuts N z₁ z₂ z₃ z₄).ncard :=
    fun z₁ h₁ z₂ h₂ z₃ h₃ z₄ h₄ => hmin (z₁, z₂, z₃, z₄) (by
      simp only [Finset.mem_product]
      exact ⟨h₁, h₂, h₃, h₄⟩)
  -- `E` is nonempty (line 618)
  have hsplit : N.HasCutSplitOn {a₁, a₂, b₁, b₂} {a₁, a₂} := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using h a₁ ha₁ a₂ ha₂ b₁ hb₁ b₂ hb₂
  obtain ⟨e₀, he₀⟩ := exists_mem_quartetCuts hN (hne (hmem₁ ha₁) (hmem₃ hb₁))
    (hne (hmem₁ ha₁) (hmem₄ hb₂)) (hne (hmem₂ ha₂) (hmem₃ hb₁)) (hne (hmem₂ ha₂) (hmem₄ hb₂)) hsplit
  have hA₁q : ∀ {x}, x ∈ B₁ ∪ B₂ → x ∉ (A₁ : Set X) := fun hx hxA => hne (hmem₁ hxA) hx rfl
  have hA₂q : ∀ {x}, x ∈ B₁ ∪ B₂ → x ∉ (A₂ : Set X) := fun hx hxA => hne (hmem₂ hxA) hx rfl
  have hB₁q : ∀ {x}, x ∈ A₁ ∪ A₂ → x ∉ (B₁ : Set X) := fun hx hxB => hne hx (hmem₃ hxB) rfl
  have hB₂q : ∀ {x}, x ∈ A₁ ∪ A₂ → x ∉ (B₂ : Set X) := fun hx hxB => hne hx (hmem₄ hxB) rfl
  have hA : ((A₁ ∪ A₂ : Finset X) : Set X) = (A₁ : Set X) ∪ A₂ := Finset.coe_union _ _
  have hB : ((B₁ ∪ B₂ : Finset X) : Set X) = (B₁ : Set X) ∪ B₂ := Finset.coe_union _ _
  have hall : ∀ e ∈ quartetCuts N a₁ a₂ b₁ b₂,
      Induces N (N.ancestralArcs Set.univ) e ((A₁ : Set X) ∪ A₂) ((B₁ : Set X) ∪ B₂) := by
    intro e he
    -- the edges in `E` induce `A₁ ∪ {ã₂}|{b̃₁, b̃₂}`, and similarly with `ã₂, b̃₁, b̃₂` (lines 622-627)
    have hbl₁ := induces_block hN (block := (A₁ : Set X)) (z₀ := a₁) (p := a₂) (q := b₁) (r := b₂) ha₁
      (hA₁q (hmem₃ hb₁)) (hA₁q (hmem₄ hb₂)) (fun z hz => hmin' z hz a₂ ha₂ b₁ hb₁ b₂ hb₂) he
    have hbl₂ := induces_block hN (block := (A₂ : Set X)) (z₀ := a₂) (p := a₁) (q := b₁) (r := b₂) ha₂
      (hA₂q (hmem₃ hb₁)) (hA₂q (hmem₄ hb₂))
      (fun z hz => by
        rw [quartetCuts_comm_left (a₁ := a₁) (a₂ := a₂), quartetCuts_comm_left (a₁ := a₁) (a₂ := z)]
        exact hmin' a₁ ha₁ z hz b₁ hb₁ b₂ hb₂)
      (quartetCuts_comm_left.symm ▸ he)
    have hbl₃ := induces_block hN (block := (B₁ : Set X)) (z₀ := b₁) (p := b₂) (q := a₁) (r := a₂) hb₁
      (hB₁q (hmem₁ ha₁)) (hB₁q (hmem₂ ha₂))
      (fun z hz => by
        rw [quartetCuts_swap (a₁ := a₁) (b₁ := b₁), quartetCuts_swap (a₁ := a₁) (b₁ := z)]
        exact hmin' a₁ ha₁ a₂ ha₂ z hz b₂ hb₂)
      (quartetCuts_swap.symm ▸ he)
    have hbl₄ := induces_block hN (block := (B₂ : Set X)) (z₀ := b₂) (p := b₁) (q := a₁) (r := a₂) hb₂
      (hB₂q (hmem₁ ha₁)) (hB₂q (hmem₂ ha₂))
      (fun z hz => by
        rw [quartetCuts_swap (a₁ := a₁) (b₁ := b₂), quartetCuts_swap (a₁ := a₁) (b₁ := z),
          quartetCuts_comm_right (b₁ := b₁) (b₂ := b₂), quartetCuts_comm_right (b₁ := b₁) (b₂ := z)]
        exact hmin' a₁ ha₁ a₂ ha₂ b₁ hb₁ z hz)
      (quartetCuts_swap.symm ▸ quartetCuts_comm_right.symm ▸ he)
    -- `N⁺` is `G̃₄` with the funnels of all taxa attached, each on its side (lines 626-627)
    refine Induces.attach_funnels (Z := {a₁, a₂, b₁, b₂}) (P := {a₁, a₂}) (Q := {b₁, b₂}) (p := a₁)
      (q := b₁) hN he ?_ ?_ ?_ ?_ ?_ (Set.mem_insert _ _) (Set.mem_insert _ _) ?_ ?_
    · ext x
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    · refine (Set.eq_univ_of_forall fun x => ?_).symm
      have hx : x ∈ (A₁ ∪ A₂) ∪ (B₁ ∪ B₂) := hcover ▸ Finset.mem_univ x
      simpa only [Finset.mem_union, Set.mem_union, Finset.mem_coe] using hx
    · rintro x (rfl | rfl)
      · exact Or.inl ha₁
      · exact Or.inr ha₂
    · rintro x (rfl | rfl)
      · exact Or.inl hb₁
      · exact Or.inr hb₂
    · rw [← hA, ← hB]
      exact Finset.disjoint_coe.mpr hAB
    · rintro z (hz | hz) x hxZ hx
      · refine Induces.attaches hN hbl₁ ?_ (Or.inr hz) (Or.inl (Or.inr hz)) (Or.inr ha₁)
          (Set.mem_insert _ _) (Set.mem_insert _ _) (by simp) hxZ hx
        rintro y (rfl | rfl | rfl | rfl)
        · exact Or.inl (Or.inr ha₁)
        · exact Or.inl (Or.inl rfl)
        · simp
        · simp
      · refine Induces.attaches hN hbl₂ ?_ (Or.inr hz) (Or.inl (Or.inr hz)) (Or.inl rfl)
          (Set.mem_insert _ _) (Set.mem_insert _ _) (by simp) hxZ hx
        rintro y (rfl | rfl | rfl | rfl)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr ha₂)
        · simp
        · simp
    · rintro z (hz | hz) x hxZ hx
      · refine Induces.attaches hN hbl₃ ?_ (Or.inr hz) (Or.inl (Or.inr hz)) (Or.inr hb₁) (by simp)
          (Set.mem_insert _ _) (by simp) hxZ hx
        rintro y (rfl | rfl | rfl | rfl)
        · simp
        · simp
        · exact Or.inl (Or.inr hb₁)
        · exact Or.inl (Or.inl rfl)
      · refine Induces.attaches hN hbl₄ ?_ (Or.inr hz) (Or.inl (Or.inr hz)) (Or.inl rfl) (by simp)
          (Set.mem_insert _ _) (by simp) hxZ hx
        rintro y (rfl | rfl | rfl | rfl)
        · simp
        · simp
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr hb₂)
  rw [hasCutSplit_iff_hasCutSplitOn_univ hN, hA]
  refine (hall e₀ he₀).hasCutSplitOn hN (fun x _ => ?_) (Set.subset_univ _) (Set.subset_univ _)
    (Or.inl ha₁) (Or.inl hb₁)
  have hx : x ∈ (A₁ ∪ A₂) ∪ (B₁ ∪ B₂) := hcover ▸ Finset.mem_univ x
  simpa only [Finset.mem_union, Set.mem_union, Finset.mem_coe, or_assoc] using hx

/-- **Corollary 4.2** (`ecto:cor4_2`). Let `A|B` be a non-trivial split of `X`. Either `A|B` is a
cut-edge split of `N`, or for any `a₁ ∈ A`, `b₁ ∈ B` there are distinct taxa `a₂ ∈ A`, `b₂ ∈ B` such
that `a₁a₂|b₁b₂` is not a cut-edge split of the induced network on `a₁, a₂, b₁, b₂`. The paper's second sentence
("That is, ...") is `corollary4_2_second`. -/
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
≠ i} B_{j'}` as `B₂`: the index should be `j' ≠ j`. The paper's second sentence ("That is, ...") is
`corollary4_3_second`. -/
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
    (by rw [hcoverA, hcoverB]; exact disjoint_compl_right)
    (by rw [hcoverA, hcoverB]; exact Finset.union_compl A)
    hall
  rw [hcoverA] at key
  exact hcut key

/-! ### The second sentences of Corollaries 4.2 and 4.3 -/

/-- The conclusion of the second sentences of Corollaries 4.2 and 4.3 (lines 633-634, 669-670): "either
`N⁺_{a₁a₂b₁b₂}` has a 4-blob and thus no non-trivial cut-edge splits, or it has exactly one of the cut-edge splits
`a₁b₁|a₂b₂` or `a₁b₂|a₂b₁`". The first alternative is read as no cut-edge split, `¬ IsTreelike`, the 4-blob of the source's
Lemma 1 not being stated here (see `External/AllmanEtAl2023/Reduction.lean`). -/
def IsNoSplitOrCrossSplit (N : RootedNetwork V E X) (a₁ a₂ b₁ b₂ : X) : Prop :=
  ¬ IsTreelike N {a₁, a₂, b₁, b₂} ∨
    (N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, b₁} : Finset X) : Set X) ∧
      ¬ N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, b₂} : Finset X) : Set X)) ∨
    (¬ N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, b₁} : Finset X) : Set X) ∧
      N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, b₂} : Finset X) : Set X))

omit [Fintype X] in
/-- A quartet tree `xy|uv` is a cut-edge split of the network induced on its taxa exactly when `{x, y}` is a side of one. -/
theorem inducedCutSplit_quartetTree_iff {x y u v : X} (h : ({x, y, u, v} : Finset X).card = 4) :
    InducedCutSplit N (quartetTree x y u v h) ↔
      N.HasCutSplitOn (({x, y, u, v} : Finset X) : Set X) (({x, y} : Finset X) : Set X) := by
  obtain ⟨hxy, hxu, hxv, hyu, hyv, huv⟩ := TreeMetric.ne_of_card_four h
  unfold InducedCutSplit
  rw [TreeMetric.taxa_quartetTree]
  constructor
  · rintro ⟨B, hB, hc⟩
    simp only [TreeMetric.val_quartetTree, Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl
    · exact hc
    · rw [← hasCutSplitOn_compl]
      refine (hasCutSplitOn_congr ?_).mp hc
      ext z
      simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton,
        Set.mem_compl_iff]
      grind
  · exact fun hc => ⟨{x, y}, by simp, hc⟩

omit [Fintype X] in
/-- Two cherries of two different quartet trees on a set of four taxa, sharing a taxon, are not both cut-edge splits
(`inducedCutSplit_unique`). -/
theorem not_hasCutSplitOn_and_hasCutSplitOn (hN : N.IsPhylogenetic) {q : Finset X} {x y u v : X}
    (hq : q = {x, y, u, v}) (h : ({x, y, u, v} : Finset X).card = 4)
    (hxy : N.HasCutSplitOn (q : Set X) (({x, y} : Finset X) : Set X))
    (hxu : N.HasCutSplitOn (q : Set X) (({x, u} : Finset X) : Set X)) : False := by
  obtain ⟨hne₁, hne₂, hne₃, hne₄, hne₅, hne₆⟩ := TreeMetric.ne_of_card_four h
  have hq' : ({x, u, y, v} : Finset X) = {x, y, u, v} := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h' : ({x, u, y, v} : Finset X).card = 4 := hq' ▸ h
  have h₁ : InducedCutSplit N (quartetTree x y u v h) :=
    (inducedCutSplit_quartetTree_iff h).mpr (hq ▸ hxy)
  have h₂ : InducedCutSplit N (quartetTree x u y v h') :=
    (inducedCutSplit_quartetTree_iff h').mpr (by rw [hq']; exact hq ▸ hxu)
  have heq := inducedCutSplit_unique hN h₁ h₂ (by
    rw [TreeMetric.taxa_quartetTree, TreeMetric.taxa_quartetTree, hq'])
  have hmem : ({x, y} : Finset X) ∈ (quartetTree x u y v h').val := heq ▸ (by simp)
  simp only [TreeMetric.val_quartetTree, Finset.mem_insert, Finset.mem_singleton] at hmem
  have hyu' : y ∈ ({x, y} : Finset X) := by simp
  have hxm : x ∈ ({x, y} : Finset X) := by simp
  rcases hmem with hm | hm
  · rw [hm] at hyu'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyu'
    tauto
  · rw [hm] at hxm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxm
    tauto

omit [Fintype X] in
/-- A cut-edge split of a set `q` of four taxa, given by a quartet tree, has a side `{a, y}` for any taxon `a` of `q`. -/
theorem exists_hasCutSplitOn_pair {q : Finset X} {s : QuartetTree X} (hs : s.taxa = q)
    (hc : InducedCutSplit N s) {a : X} (ha : a ∈ q) :
    ∃ y ∈ q, y ≠ a ∧ N.HasCutSplitOn (q : Set X) (({a, y} : Finset X) : Set X) := by
  obtain ⟨B, hB, hcut⟩ := hc
  rw [hs] at hcut
  have hq4 : q.card = 4 := hs ▸ s.card_taxa
  have hBq : B ⊆ q := hs ▸ s.subset_taxa hB
  have hBc : B.card = 2 := s.card_of_mem hB
  obtain ⟨C, hCq, hCc, hCa, hCcut⟩ : ∃ C : Finset X, C ⊆ q ∧ C.card = 2 ∧ a ∈ C ∧
      N.HasCutSplitOn (q : Set X) (C : Set X) := by
    by_cases haB : a ∈ B
    · exact ⟨B, hBq, hBc, haB, hcut⟩
    · refine ⟨q \ B, Finset.sdiff_subset, ?_, Finset.mem_sdiff.mpr ⟨ha, haB⟩, ?_⟩
      · rw [Finset.card_sdiff_of_subset hBq, hq4, hBc]
      · rw [← hasCutSplitOn_compl]
        refine (hasCutSplitOn_congr ?_).mp hcut
        ext z
        simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_compl_iff, Finset.mem_sdiff]
        tauto
  obtain ⟨u, w, huw, hCuw⟩ := Finset.card_eq_two.mp hCc
  rw [hCuw, Finset.mem_insert, Finset.mem_singleton] at hCa
  rcases hCa with rfl | rfl
  · exact ⟨w, hCq (by simp [hCuw]), huw.symm, hCuw ▸ hCcut⟩
  · exact ⟨u, hCq (by simp [hCuw]), huw, by rw [Finset.pair_comm]; exact hCuw ▸ hCcut⟩

/-- **"That is, ..."** (lines 633-634, 669-670): on four distinct taxa, `a₁a₂|b₁b₂` fails to be a cut-edge split of the
induced network exactly when the network has no cut-edge split, or has exactly one of `a₁b₁|a₂b₂`, `a₁b₂|a₂b₁`. -/
theorem not_hasCutSplitOn_iff (hN : N.IsPhylogenetic) {a₁ a₂ b₁ b₂ : X}
    (h4 : ({a₁, a₂, b₁, b₂} : Finset X).card = 4) :
    ¬ N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X) ↔
      IsNoSplitOrCrossSplit N a₁ a₂ b₁ b₂ := by
  have hq₂ : ({a₁, a₂, b₁, b₂} : Finset X) = {a₁, a₂, b₂, b₁} := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hq₃ : ({a₁, a₂, b₁, b₂} : Finset X) = {a₁, b₁, b₂, a₂} := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h₁ := not_hasCutSplitOn_and_hasCutSplitOn (N := N) hN rfl h4
  have h₂ := not_hasCutSplitOn_and_hasCutSplitOn (N := N) hN hq₂ (hq₂ ▸ h4)
  have h₃ := not_hasCutSplitOn_and_hasCutSplitOn (N := N) hN hq₃ (hq₃ ▸ h4)
  constructor
  · intro hnot
    by_cases hT : IsTreelike N {a₁, a₂, b₁, b₂}
    · right
      obtain ⟨s, hs, hc⟩ := hT
      obtain ⟨y, hy, hya, hcut⟩ := exists_hasCutSplitOn_pair (mem_treesOn.mp hs) hc
        (a := a₁) (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact absurd rfl hya
      · exact absurd hcut hnot
      · exact Or.inl ⟨hcut, fun h => h₃ hcut h⟩
      · exact Or.inr ⟨fun h => h₃ h hcut, hcut⟩
    · exact Or.inl hT
  · rintro (hT | ⟨h, -⟩ | ⟨-, h⟩) hcut
    · have : InducedCutSplit N (quartetTree a₁ a₂ b₁ b₂ h4) :=
        (inducedCutSplit_quartetTree_iff h4).mpr hcut
      exact hT ⟨_, mem_treesOn.mpr (TreeMetric.taxa_quartetTree h4), this⟩
    · exact h₁ hcut h
    · exact h₂ hcut h

/-- **Corollary 4.2, second sentence** (lines 633-634), completing `corollary4_2`: either `A|B` is a cut-edge split of
`N`, or for any `a₁ ∈ A`, `b₁ ∈ B` there are distinct `a₂ ∈ A`, `b₂ ∈ B` such that the network induced on `a₁, a₂, b₁, b₂`
has no cut-edge split, or exactly one of `a₁b₁|a₂b₂`, `a₁b₂|a₂b₁`. The paper's "one of" is "exactly one of" here, as in
Corollary 4.3, by `inducedCutSplit_unique`. "Has a 4-blob" is read as no cut-edge split (`IsTreelike`). -/
theorem corollary4_2_second (hN : N.IsPhylogenetic) (A : Finset X) (hA : 2 ≤ A.card) (hB : 2 ≤ Aᶜ.card) :
    N.HasCutSplit (A : Set X) ∨ ∀ a₁ ∈ A, ∀ b₁ ∈ Aᶜ, ∃ a₂ ∈ A, ∃ b₂ ∈ Aᶜ, a₂ ≠ a₁ ∧ b₂ ≠ b₁ ∧
      IsNoSplitOrCrossSplit N a₁ a₂ b₁ b₂ := by
  refine (corollary4_2 hN A hA hB).imp_right fun h a₁ ha₁ b₁ hb₁ => ?_
  obtain ⟨a₂, ha₂, b₂, hb₂, hane, hbne, hnot⟩ := h a₁ ha₁ b₁ hb₁
  have hAB : ∀ {a b : X}, a ∈ A → b ∈ Aᶜ → a ≠ b := fun ha hb hab =>
    Finset.mem_compl.mp hb (hab ▸ ha)
  have h4 : ({a₁, a₂, b₁, b₂} : Finset X).card = 4 :=
    TreeMetric.card_four_of_ne hane.symm (hAB ha₁ hb₁) (hAB ha₁ hb₂) (hAB ha₂ hb₁) (hAB ha₂ hb₂) hbne.symm
  exact ⟨a₂, ha₂, b₂, hb₂, hane, hbne, (not_hasCutSplitOn_iff hN h4).mp hnot⟩

/-- **Corollary 4.3, second sentence** (lines 669-670), completing `corollary4_3`: either `A|B` is a cut-edge split of
`N`, or for any choice of `Aᵢ` and `Bⱼ` there are `a₁ ∈ Aᵢ`, `a₂ ∈ A \ Aᵢ`, `b₁ ∈ Bⱼ`, `b₂ ∈ B \ Bⱼ` such that the network
induced on `a₁, a₂, b₁, b₂` has no cut-edge split, or exactly one of `a₁b₁|a₂b₂`, `a₁b₂|a₂b₁`. "Has a 4-blob" is read as no
cut-edge split (`IsTreelike`). -/
theorem corollary4_3_second (hN : N.IsPhylogenetic) (A : Finset X) {na nb : ℕ}
    (hna : 2 ≤ na) (hnb : 2 ≤ nb)
    (Ablock : Fin na → Finset X) (Bblock : Fin nb → Finset X)
    (hAne : ∀ i, (Ablock i).Nonempty) (hBne : ∀ j, (Bblock j).Nonempty)
    (hAdisj : ∀ i i', i ≠ i' → Disjoint (Ablock i) (Ablock i'))
    (hBdisj : ∀ j j', j ≠ j' → Disjoint (Bblock j) (Bblock j'))
    (hAcover : Finset.univ.biUnion Ablock = A) (hBcover : Finset.univ.biUnion Bblock = Aᶜ) :
    N.HasCutSplit (A : Set X) ∨ ∀ (i : Fin na) (j : Fin nb),
      ∃ a₁ ∈ Ablock i, ∃ a₂ ∈ A \ Ablock i, ∃ b₁ ∈ Bblock j, ∃ b₂ ∈ Aᶜ \ Bblock j,
        IsNoSplitOrCrossSplit N a₁ a₂ b₁ b₂ := by
  refine (corollary4_3 hN A hna hnb Ablock Bblock hAne hBne hAdisj hBdisj hAcover hBcover).imp_right
    fun h i j => ?_
  obtain ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, hnot⟩ := h i j
  have hsub : ∀ {n : ℕ} (block : Fin n → Finset X) (S : Finset X) (k : Fin n),
      Finset.univ.biUnion block = S → block k ⊆ S := by
    intro n block S k hS x hx
    rw [← hS]
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hx⟩
  have ha₁A : a₁ ∈ A := hsub Ablock A i hAcover ha₁
  have hb₁B : b₁ ∈ Aᶜ := hsub Bblock Aᶜ j hBcover hb₁
  have ha₂A := (Finset.mem_sdiff.mp ha₂).1
  have hb₂B := (Finset.mem_sdiff.mp hb₂).1
  have hAB : ∀ {a b : X}, a ∈ A → b ∈ Aᶜ → a ≠ b := fun ha hb hab =>
    Finset.mem_compl.mp hb (hab ▸ ha)
  have h4 : ({a₁, a₂, b₁, b₂} : Finset X).card = 4 :=
    TreeMetric.card_four_of_ne (fun h => (Finset.mem_sdiff.mp ha₂).2 (h ▸ ha₁)) (hAB ha₁A hb₁B) (hAB ha₁A hb₂B)
      (hAB ha₂A hb₁B) (hAB ha₂A hb₂B) (fun h => (Finset.mem_sdiff.mp hb₂).2 (h ▸ hb₁))
  exact ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, (not_hasCutSplitOn_iff hN h4).mp hnot⟩

end ECToBlob
