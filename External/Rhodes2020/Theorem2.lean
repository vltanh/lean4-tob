module

public import Basic.Phylogenetics.TreeMetric

/-!
# Rhodes 2020: the quartet metrization of a tree

J. A. Rhodes, *Topological metrizations of trees, and new quartet methods of tree inference*, IEEE/ACM
Trans. Comput. Biol. Bioinform. 17 (2020), 2107–2118.

An edge with blocks `X₁, …, X_m` at one end and `Y₁, …, Y_{m'}` at the other has weight
`∑_{i<j} |Xᵢ||Xⱼ| + ∑_{i<j} |Yᵢ||Yⱼ|`. Theorem 2: the tree metric of these weights is
`d(x, y) = 2 |Q_{x,y}| + 2N - 4`, with `Q_{x,y}` the quartets displayed on the tree of the form `xz|yw`
or `xyzw`. Internal edges have weight at least `2`.
-/

@[expose] public noncomputable section

open Phylogenetics Finset
open scoped Classical

namespace External.Rhodes2020

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Two taxa on the side `A` lie in the same block of the edge when a split properly inside `A`
contains both; the blocks on that side are the maximal sides of `T` properly inside `A`, and single
taxa of `A` in no such side. The number of pairs in distinct blocks is
`∑_{i<j} |Xᵢ||Xⱼ|`. -/
def sidePairs (T : Finset (Finset X)) (A : Finset X) : ℕ :=
  (univ.filter fun p : Finset X =>
    p.card = 2 ∧ p ⊆ A ∧ ¬ ∃ C ∈ T, C ⊂ A ∧ p ⊆ C).card

/-- The quartet metrization `Q` of the tree `T`: the weight of the edge with side `A`. -/
def quartetWeight (T : Finset (Finset X)) (A : Finset X) : ℝ :=
  (sidePairs T A : ℝ) + (sidePairs T Aᶜ : ℝ)

/-- The two sides of an edge, containing `x` and `y`, form a chain. -/
private theorem side_chain {T : Finset (Finset X)} (hT : IsSplitFamily T) {x y : X} {A B : Finset X}
    (hA : A ∈ T) (hB : B ∈ T) (hxA : x ∈ A) (hxB : x ∈ B) (hyA : y ∉ A) (hyB : y ∉ B) :
    A ⊆ B ∨ B ⊆ A := by
  rcases hT.compatible A hA B hB with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hxB (Finset.disjoint_left.mp h hxA)
  · have : y ∈ A ∪ B := h ▸ Finset.mem_univ y
    rcases Finset.mem_union.mp this with h' | h'
    · exact absurd h' hyA
    · exact absurd h' hyB

/-- The pairs counted by `sidePairs T A`. -/
private def pairsAt (T : Finset (Finset X)) (A : Finset X) : Finset (Finset X) :=
  univ.filter fun p : Finset X => p.card = 2 ∧ p ⊆ A ∧ ¬ ∃ C ∈ T, C ⊂ A ∧ p ⊆ C

/-- The pairs counted over the edges on the path from `x` to `y`, on the sides of `x`. -/
private def goodPairs (T : Finset (Finset X)) (x y : X) : Finset (Finset X) :=
  univ.filter fun p : Finset X =>
    p.card = 2 ∧ y ∉ p ∧ (x ∈ p ∨ ¬ ∃ C ∈ T, p ⊆ C ∧ x ∉ C ∧ y ∉ C)

/-- The double count: each good pair is counted at exactly one edge on the path from `x` to `y`,
namely the first edge from `x` beyond which the pair lies on the side of `x`. -/
private theorem sum_sidePairs {T : Finset (Finset X)} (hT : IsSplitFamily T) {x y : X} (hxy : x ≠ y) :
    ∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T A = (goodPairs T x y).card := by
  have hdisj : ∀ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), ∀ B ∈ T.filter (fun A => x ∈ A ∧ y ∉ A),
      A ≠ B → Disjoint (pairsAt T A) (pairsAt T B) := by
    intro A hA B hB hAB
    obtain ⟨hAT, hxA, hyA⟩ := Finset.mem_filter.mp hA
    obtain ⟨hBT, hxB, hyB⟩ := Finset.mem_filter.mp hB
    refine Finset.disjoint_left.mpr fun p hpA hpB => ?_
    obtain ⟨-, -, hpA, hnA⟩ := Finset.mem_filter.mp hpA
    obtain ⟨-, -, hpB, hnB⟩ := Finset.mem_filter.mp hpB
    rcases side_chain hT hAT hBT hxA hxB hyA hyB with h | h
    · exact hnB ⟨A, hAT, ⟨h, fun h' => hAB (Finset.Subset.antisymm h h')⟩, hpA⟩
    · exact hnA ⟨B, hBT, ⟨h, fun h' => hAB (Finset.Subset.antisymm h' h)⟩, hpB⟩
  have hunion : (T.filter (fun A => x ∈ A ∧ y ∉ A)).biUnion (pairsAt T) = goodPairs T x y := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_filter, goodPairs, pairsAt, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨A, ⟨hAT, hxA, hyA⟩, hp2, hpA, hn⟩
      refine ⟨hp2, fun h => hyA (hpA h), ?_⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨hxp, C, hC, hpC, hxC, hyC⟩ := hcon
      obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < p.card)
      rcases hT.compatible C hC A hAT with h | h | h | h
      · exact hn ⟨C, hC, ⟨h, fun h' => hxC (h' hxA)⟩, hpC⟩
      · exact hxC (h hxA)
      · exact Finset.disjoint_left.mp h (hpC hu) (hpA hu)
      · have : y ∈ C ∪ A := h ▸ Finset.mem_univ y
        rcases Finset.mem_union.mp this with h' | h'
        · exact hyC h'
        · exact hyA h'
    · rintro ⟨hp2, hyp, hgood⟩
      -- the least side on the path containing `p`
      have hne : (T.filter fun A => x ∈ A ∧ y ∉ A ∧ p ⊆ A).Nonempty := by
        refine ⟨{y}ᶜ, Finset.mem_filter.mpr ⟨hT.compl_mem _ (hT.singleton_mem y), ?_, ?_, ?_⟩⟩
        · simpa using hxy
        · simp
        · intro u hu
          refine Finset.mem_compl.mpr fun h => hyp ?_
          rwa [Finset.mem_singleton.mp h] at hu
      obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image _ Finset.card hne
      obtain ⟨hAT, hxA, hyA, hpA⟩ := Finset.mem_filter.mp hA
      refine ⟨A, ⟨hAT, hxA, hyA⟩, hp2, hpA, ?_⟩
      rintro ⟨C, hC, hCA, hpC⟩
      by_cases hxC : x ∈ C
      · have := hmin C (Finset.mem_filter.mpr ⟨hC, hxC, fun h => hyA (hCA.1 h), hpC⟩)
        exact absurd (Finset.card_lt_card hCA) (not_lt.mpr this)
      · rcases hgood with h | h
        · exact hxC (hpC h)
        · exact h ⟨C, hC, hpC, hxC, fun h' => hyA (hCA.1 h')⟩
  rw [← hunion, Finset.card_biUnion hdisj]
  rfl

/-- The pairs containing `x` and not `y`. -/
private theorem card_pairs_with {x y : X} (hxy : x ≠ y) :
    (univ.filter fun p : Finset X => p.card = 2 ∧ y ∉ p ∧ x ∈ p).card = Fintype.card X - 2 := by
  have himg : (univ.filter fun p : Finset X => p.card = 2 ∧ y ∉ p ∧ x ∈ p) =
      (((univ : Finset X).erase x).erase y).image (fun u => ({x, u} : Finset X)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨hp, hyp, hxp⟩
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hp
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyp hxp
      rcases hxp with rfl | rfl
      · exact ⟨b, ⟨fun h => hyp.2 h.symm, hab.symm, trivial⟩, rfl⟩
      · exact ⟨a, ⟨fun h => hyp.1 h.symm, hab, trivial⟩, Finset.pair_comm _ _⟩
    · rintro ⟨u, ⟨huy, hux, -⟩, rfl⟩
      refine ⟨Finset.card_pair hux.symm, ?_, by simp⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy.symm, huy.symm⟩
  rw [himg, Finset.card_image_of_injOn, Finset.card_erase_of_mem, Finset.card_erase_of_mem,
    Finset.card_univ]
  · omega
  · exact Finset.mem_univ x
  · exact Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩
  · intro u hu v hv huv
    simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_singleton_iff,
      Set.mem_univ, true_and] at hu hv
    have : u ∈ ({x, v} : Finset X) := by
      rw [← show ({x, u} : Finset X) = {x, v} from huv]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact absurd h hu.1
    · exact h

/-- On the four taxa `x, y, u, v`: the set is unresolved or `x, y` are separated, exactly when no side
of the tree contains `u, v` and neither of `x, y`. -/
private theorem unresolved_or_separated_iff {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hS : IsSplitFamily T) {x y u v : X} (h : ({x, y, u, v} : Finset X).card = 4) :
    (({x, y, u, v} : Finset X) ∈ {q : Finset X | ∀ s ∈ treesOn q, ¬ Displays T s} ∨
      ∃ s ∈ {s : QuartetTree X | Displays T s}, s.taxa = {x, y, u, v} ∧ Separated s x y) ↔
      ¬ ∃ C ∈ T, u ∈ C ∧ v ∈ C ∧ x ∉ C ∧ y ∉ C := by
  obtain ⟨hxy, hxu, hxv, hyu, hyv, huv⟩ := TreeMetric.ne_of_card_four h
  have h' : ({u, v, x, y} : Finset X).card = 4 :=
    TreeMetric.card_four_of_ne huv hxu.symm hyu.symm hxv.symm hyv.symm hxy
  have hset : ({u, v, x, y} : Finset X) = {x, y, u, v} := by grind
  constructor
  · rintro hcon ⟨C, hC, huC, hvC, hxC, hyC⟩
    have hdisp : Displays T (quartetTree u v x y h') :=
      (TreeMetric.displays_quartetTree_iff hS h').mpr ⟨C, hC, huC, hvC, hxC, hyC⟩
    rcases hcon with hcon | ⟨s, hs, hst, hsep⟩
    · exact hcon _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hset]⟩) hdisp
    · have hss := hT.displays_unique hs hdisp (by simp [hst, hset])
      subst hss
      exact hsep.2.2 {x, y} (by simp) (by simp)
  · intro hno
    by_cases hd : ∃ s ∈ treesOn ({x, y, u, v} : Finset X), Displays T s
    · obtain ⟨s, hs, hsd⟩ := hd
      have hst : s.taxa = {x, y, u, v} := (Finset.mem_filter.mp hs).2
      refine Or.inr ⟨s, hsd, hst, by simp [hst], by simp [hst], ?_⟩
      obtain ⟨a, b, c, d, hq, rfl⟩ := TreeMetric.exists_eq_quartetTree s
      obtain ⟨A, hA, ha, hb, hc, hd⟩ := (TreeMetric.displays_quartetTree_iff hS hq).mp hsd
      rw [TreeMetric.taxa_quartetTree] at hst
      obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := TreeMetric.ne_of_card_four hq
      have hm : ∀ z, z = a ∨ z = b ∨ z = c ∨ z = d ↔ z = x ∨ z = y ∨ z = u ∨ z = v := by
        intro z
        have := Finset.ext_iff.mp hst z
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      intro B hB ⟨hxB, hyB⟩
      simp only [TreeMetric.val_quartetTree, Finset.mem_insert, Finset.mem_singleton] at hB
      apply hno
      have hu := (hm u).mpr (by simp)
      have hv := (hm v).mpr (by simp)
      clear hm hst hs hsd h h' hset hq hno
      rcases hB with rfl | rfl
      · -- `x, y` is the cherry `a, b`, and `u, v` the other
        refine ⟨Aᶜ, hS.compl_mem A hA, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxB hyB
        simp only [Finset.mem_compl]
        rcases hxB with rfl | rfl <;> rcases hyB with rfl | rfl <;> grind
      · refine ⟨A, hA, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxB hyB
        rcases hxB with rfl | rfl <;> rcases hyB with rfl | rfl <;> grind
    · refine Or.inl fun s hs hsd => hd ⟨s, hs, hsd⟩

/-- The sets `Q_{x,y}` of the theorem. -/
private def qSet (T : Finset (Finset X)) (x y : X) : Finset (Finset X) :=
  univ.filter fun q : Finset X => q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧
    (q ∈ {q : Finset X | ∀ s ∈ treesOn q, ¬ Displays T s} ∨
      ∃ s ∈ {s : QuartetTree X | Displays T s}, s.taxa = q ∧ Separated s x y)

/-- The good pairs avoiding `x` correspond to the sets `Q_{x,y}`. -/
private theorem card_pairs_without {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hS : IsSplitFamily T) {x y : X} (hxy : x ≠ y) :
    (univ.filter fun p : Finset X =>
      p.card = 2 ∧ y ∉ p ∧ x ∉ p ∧ ¬ ∃ C ∈ T, p ⊆ C ∧ x ∉ C ∧ y ∉ C).card = (qSet T x y).card := by
  refine Finset.card_nbij' (fun p => insert x (insert y p)) (fun q => (q.erase x).erase y) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp2, hyp, hxp, hno⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp) |>.2
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hp2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyp hxp
    have h4 : ({x, y, u, v} : Finset X).card = 4 :=
      TreeMetric.card_four_of_ne hxy (Ne.intro hxp.1) (Ne.intro hxp.2) (Ne.intro hyp.1)
        (Ne.intro hyp.2) huv
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h4, by simp, by simp, ?_⟩)
    refine (unresolved_or_separated_iff hT hS h4).mpr ?_
    rintro ⟨C, hC, huC, hvC, hxC, hyC⟩
    refine hno ⟨C, hC, ?_, hxC, hyC⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨hq4, hxq, hyq, hcond⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    have hp2 : ((q.erase x).erase y).card = 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, hyq⟩),
        Finset.card_erase_of_mem hxq, hq4]
    obtain ⟨u, v, huv, hp⟩ := Finset.card_eq_two.mp hp2
    have hqeq : q = {x, y, u, v} := by
      rw [← hp, Finset.insert_erase (Finset.mem_erase.mpr ⟨hxy.symm, hyq⟩), Finset.insert_erase hxq]
    have h4 : ({x, y, u, v} : Finset X).card = 4 := hqeq ▸ hq4
    subst hqeq
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp2, by simp, ?_, ?_⟩)
    · simp
    · beta_reduce
      rw [hp]
      rintro ⟨C, hC, hpC, hxC, hyC⟩
      exact (unresolved_or_separated_iff hT hS h4).mp hcond
        ⟨C, hC, hpC (by simp), hpC (by simp), hxC, hyC⟩
  · intro p hp
    obtain ⟨-, hyp, hxp, -⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
    simp only
    rw [Finset.erase_insert (fun h => ?_), Finset.erase_insert hyp]
    rcases Finset.mem_insert.mp h with h | h
    · exact hxy h
    · exact hxp h
  · intro q hq
    obtain ⟨-, hxq, hyq, -⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    simp only
    rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨hxy.symm, hyq⟩), Finset.insert_erase hxq]

private theorem card_goodPairs {T : Finset (Finset X)} (hT : IsUnrootedTree T) (hS : IsSplitFamily T)
    {x y : X} (hxy : x ≠ y) :
    (goodPairs T x y).card = (Fintype.card X - 2) + (qSet T x y).card := by
  rw [← card_pairs_with hxy, ← card_pairs_without hT hS hxy, ← Finset.card_union_of_disjoint]
  · congr 1
    ext p
    simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  · refine Finset.disjoint_left.mpr fun p hp hp' => ?_
    exact (Finset.mem_filter.mp hp').2.2.2.1 (Finset.mem_filter.mp hp).2.2.2

private theorem qSet_comm (T : Finset (Finset X)) (x y : X) : qSet T y x = qSet T x y := by
  ext q
  simp only [qSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsep : ∀ s : QuartetTree X, Separated s y x ↔ Separated s x y := by
    intro s
    simp only [Separated]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, h1, fun B hB h => h3 B hB h.symm⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, h1, fun B hB h => h3 B hB h.symm⟩
  simp only [hsep]
  tauto

/-- **Theorem 2.** The tree metric of the quartet metrization of an unrooted tree on `N` taxa is
`2 |Q_{x,y}| + 2N - 4`.

Departure from the source (a cited result): the source sums over the nodes on the path from `x` to `y`,
and counts for each node the quartets `xu|yz`, `xyuz` whose taxon `u` joins the path there. Here the
same count is a double count over the edges of the path: each pair of taxa other than `y`, unless it is
`uv` with `uv|xy` displayed, is counted at exactly one edge (`sum_sidePairs`). -/
theorem theorem2 {T : Finset (Finset X)} (hT : IsUnrootedTree T) (hX : 4 ≤ Fintype.card X)
    {x y : X} (hxy : x ≠ y) :
    treeMetric T (quartetWeight T) x y =
      quartetDistance {q | ∀ s ∈ treesOn q, ¬ Displays T s} {s | Displays T s} x y := by
  have hS : IsSplitFamily T := (isUnrootedTree_iff (by omega) T).mp hT
  have h1 := sum_sidePairs hS hxy
  have h2 := sum_sidePairs hS hxy.symm
  have hcompl : ∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T Aᶜ =
      ∑ A ∈ T.filter (fun A => y ∈ A ∧ x ∉ A), sidePairs T A := by
    refine Finset.sum_nbij' compl compl ?_ ?_ (by simp) (by simp) (by simp)
    · intro A hA
      obtain ⟨hAT, hxA, hyA⟩ := Finset.mem_filter.mp hA
      exact Finset.mem_filter.mpr ⟨hS.compl_mem A hAT, by simpa using hyA, by simpa using hxA⟩
    · intro A hA
      obtain ⟨hAT, hyA, hxA⟩ := Finset.mem_filter.mp hA
      exact Finset.mem_filter.mpr ⟨hS.compl_mem A hAT, by simpa using hxA, by simpa using hyA⟩
  rw [card_goodPairs hT hS hxy] at h1
  rw [card_goodPairs hT hS hxy.symm, qSet_comm] at h2
  have hN : ((Fintype.card X - 2 : ℕ) : ℝ) = (Fintype.card X : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hsum : treeMetric T (quartetWeight T) x y =
      ((∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T A : ℕ) : ℝ) +
        ((∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T Aᶜ : ℕ) : ℝ) := by
    simp only [treeMetric, quartetWeight, Finset.sum_add_distrib, Nat.cast_sum]
  have key : (((Fintype.card X - 2 + (qSet T x y).card : ℕ) : ℝ) +
      ((Fintype.card X - 2 + (qSet T x y).card : ℕ) : ℝ)) =
      2 * ((qSet T x y).card : ℝ) + 2 * (Fintype.card X : ℝ) - 4 := by
    push_cast
    rw [hN]
    ring
  rw [hsum, h1, hcompl, h2, key, quartetDistance, ite_eq_right hxy, qSet]
  congr!

/-- Two taxa on the side `B` on either side of a maximal side inside it are counted by `sidePairs`. -/
private theorem mem_pairsAt_of_maximal {T : Finset (Finset X)} (hS : IsSplitFamily T)
    {B C₀ : Finset X} (hB : B ∈ T) (hC₀ : C₀ ∈ T) (hlt : C₀ ⊂ B)
    (hmax : ∀ C ∈ T, C ⊂ B → C.card ≤ C₀.card) {u z : X} (hu : u ∈ C₀) (hz : z ∈ B) (hzC : z ∉ C₀) :
    ({u, z} : Finset X) ∈ pairsAt T B := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.card_pair (fun h => hzC (h ▸ hu)), ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hlt.1 hu
    · exact hz
  · rintro ⟨C, hC, hCB, hsub⟩
    exact TreeMetric.not_mem_proper_of_maximal hS hB hC₀ hlt hmax hu hzC C hC hCB
      ⟨hsub (by simp), hsub (by simp)⟩

/-- A maximal side properly inside a side with at least two taxa. -/
private theorem exists_maximal {T : Finset (Finset X)} (hS : IsSplitFamily T) {B : Finset X}
    (hB2 : 2 ≤ B.card) : ∃ C₀ ∈ T, C₀ ⊂ B ∧ ∀ C ∈ T, C ⊂ B → C.card ≤ C₀.card := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  have hne : (T.filter fun C => C ⊂ B).Nonempty := by
    refine ⟨{a}, Finset.mem_filter.mpr ⟨hS.singleton_mem a, ?_⟩⟩
    refine ⟨Finset.singleton_subset_iff.mpr ha, fun h => hab ?_⟩
    exact (Finset.mem_singleton.mp (h hb)).symm
  obtain ⟨C₀, hC₀, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  obtain ⟨hC₀T, hC₀B⟩ := Finset.mem_filter.mp hC₀
  exact ⟨C₀, hC₀T, hC₀B, fun C hC hCB => hmax C (Finset.mem_filter.mpr ⟨hC, hCB⟩)⟩

/-- A side with at least two taxa has a counted pair, and with at least three, two. -/
private theorem sidePairs_ge {T : Finset (Finset X)} (hS : IsSplitFamily T) {B : Finset X}
    (hB : B ∈ T) : (2 ≤ B.card → 1 ≤ sidePairs T B) ∧ (3 ≤ B.card → 2 ≤ sidePairs T B) := by
  refine ⟨fun h2 => ?_, fun h3 => ?_⟩
  · obtain ⟨C₀, hC₀, hlt, hmax⟩ := exists_maximal hS h2
    obtain ⟨u, hu⟩ := hS.nonempty C₀ hC₀
    obtain ⟨z, hz, hzC⟩ := Finset.exists_of_ssubset hlt
    exact Finset.card_pos.mpr ⟨_, mem_pairsAt_of_maximal hS hB hC₀ hlt hmax hu hz hzC⟩
  · obtain ⟨C₀, hC₀, hlt, hmax⟩ := exists_maximal hS (by omega : 2 ≤ B.card)
    obtain ⟨u, hu⟩ := hS.nonempty C₀ hC₀
    obtain ⟨z, hz, hzC⟩ := Finset.exists_of_ssubset hlt
    suffices 1 < (pairsAt T B).card from this
    refine Finset.one_lt_card.mpr ?_
    by_cases hC₂ : 2 ≤ C₀.card
    · obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < C₀.card)
      refine ⟨_, mem_pairsAt_of_maximal hS hB hC₀ hlt hmax hu₁ hz hzC, _,
        mem_pairsAt_of_maximal hS hB hC₀ hlt hmax hu₂ hz hzC, fun h => ?_⟩
      have : u₁ ∈ ({u₂, z} : Finset X) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h'
      · exact hne h'
      · exact hzC (h' ▸ hu₁)
    · have hcard : (B \ C₀).card = B.card - C₀.card := Finset.card_sdiff_of_subset hlt.1
      obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (B \ C₀).card)
      obtain ⟨hz₁B, hz₁C⟩ := Finset.mem_sdiff.mp hz₁
      obtain ⟨hz₂B, hz₂C⟩ := Finset.mem_sdiff.mp hz₂
      refine ⟨_, mem_pairsAt_of_maximal hS hB hC₀ hlt hmax hu hz₁B hz₁C, _,
        mem_pairsAt_of_maximal hS hB hC₀ hlt hmax hu hz₂B hz₂C, fun h => ?_⟩
      have : z₁ ∈ ({u, z₂} : Finset X) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h'
      · exact hz₁C (h' ▸ hu)
      · exact hne h'

/-- Edges have positive weight; internal edges have weight at least `2`, and for at least four taxa
so do pendant edges. -/
theorem quartetWeight_ge_two {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hX : 4 ≤ Fintype.card X) {A : Finset X} (hA : A ∈ T) : 2 ≤ quartetWeight T A := by
  have hS : IsSplitFamily T := (isUnrootedTree_iff (by omega) T).mp hT
  have hcard : A.card + Aᶜ.card = Fintype.card X := Finset.card_add_card_compl A
  have h1 := sidePairs_ge hS hA
  have h2 := sidePairs_ge hS (hS.compl_mem A hA)
  have : 2 ≤ sidePairs T A + sidePairs T Aᶜ := by
    by_cases h3 : 3 ≤ A.card
    · have := h1.2 h3; omega
    · by_cases h3' : 3 ≤ Aᶜ.card
      · have := h2.2 h3'; omega
      · have := h1.1 (by omega); have := h2.1 (by omega); omega
  have : (2 : ℝ) ≤ ((sidePairs T A + sidePairs T Aᶜ : ℕ) : ℝ) := by exact_mod_cast this
  simpa [quartetWeight] using this

theorem quartetWeight_compl (T : Finset (Finset X)) (A : Finset X) :
    quartetWeight T Aᶜ = quartetWeight T A := by
  rw [quartetWeight, quartetWeight, compl_compl, add_comm]

/-- A tree metric with positive weights determines the tree and its weights (Buneman 1971): so
exact distance-based tree builders exist. -/
theorem exists_isExactBuilder : ∃ M : TreeBuilder X, IsExactBuilder M := by
  let Valid : (X → X → ℝ) → Finset (Finset X) × (Finset X → ℝ) → Prop := fun d p =>
    IsUnrootedTree p.1 ∧ (∀ A ∈ p.1, 0 < p.2 A ∧ p.2 Aᶜ = p.2 A) ∧ treeMetric p.1 p.2 = d
  refine ⟨fun d => if h : ∃ p, Valid d p then h.choose else (∅, 0), fun T w hT hw => ?_⟩
  have hex : ∃ p, Valid (treeMetric T w) p := ⟨(T, w), hT, hw, rfl⟩
  simp only [dite_eq_left hex]
  obtain ⟨hT', hw', heq⟩ := hex.choose_spec
  by_cases hX : 2 ≤ Fintype.card X
  · obtain ⟨h1, h2⟩ := TreeMetric.eq_of_treeMetric_eq hX hT' hT hw' hw heq
    exact ⟨h1, fun A hA => h2 A (by rw [h1]; exact hA)⟩
  · have hT0 := TreeMetric.eq_empty_of_card_lt_two (by omega) hT
    have hT0' := TreeMetric.eq_empty_of_card_lt_two (by omega) hT'
    refine ⟨hT0'.trans hT0.symm, fun A hA => ?_⟩
    simp [hT0] at hA

end External.Rhodes2020
