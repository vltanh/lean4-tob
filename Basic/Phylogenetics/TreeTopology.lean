module

public import Basic.Phylogenetics.Hierarchy
public import Basic.Phylogenetics.Quartet

/-!
# Finite rooted and unrooted tree topologies

Rooted topologies are actual finite hierarchies. Unrooted topologies are split families
obtained from such hierarchies, rather than arbitrary collections of quartet resolutions.
These representations impose no network-level restriction. Equivalence with graph trees,
edge contraction, and degree-two suppression remains a separate representation theorem.
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset Classical

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A finite family of clusters satisfying the hierarchy laws. -/
abbrev RootedTopology (X : Type*) [Fintype X] [DecidableEq X] :=
  {H : Finset (Finset X) // IsHierarchy H}

/-- A valid unrooted split family is obtained from a valid rooted hierarchy. -/
abbrev IsUnrootedTopology (T : Finset (Finset X)) : Prop := IsUnrootedTree T

/-- An unrooted topology represented by both sides of each split, including trivial splits. -/
abbrev UnrootedTopology (X : Type*) [Fintype X] [DecidableEq X] :=
  {T : Finset (Finset X) // IsUnrootedTopology T}

instance : Fintype (RootedTopology X) := Fintype.ofFinite _
instance : Fintype (UnrootedTopology X) := Fintype.ofFinite _

/-- The finite collection of exactly the split families realized by hierarchies. -/
def unrootedTopologies : Finset (Finset (Finset X)) :=
  univ.filter IsUnrootedTopology

@[simp] theorem mem_unrootedTopologies (T : Finset (Finset X)) :
    T ∈ unrootedTopologies ↔ IsUnrootedTopology T := by
  simp [unrootedTopologies]

/-- Forget the root by taking non-root clusters and their complements. -/
def RootedTopology.toUnrooted (H : RootedTopology X) : UnrootedTopology X :=
  ⟨unroot H.val, H.val, H.property, rfl⟩

/-- Restrict the clusters to a nonempty set of taxa. -/
def RootedTopology.restrict (H : RootedTopology X) (S : Finset X) (hS : S.Nonempty) :
    RootedTopology S := ⟨restrictClusters S H.val, H.property.restrict S hS⟩

/-- Restrict the split family to a nonempty set of taxa. -/
def UnrootedTopology.restrict (T : UnrootedTopology X) (S : Finset X) (hS : S.Nonempty) :
    UnrootedTopology S :=
  ⟨restrictSplits S T.val, by
    obtain ⟨H, hH, hT⟩ := T.property
    refine ⟨restrictClusters S H, hH.restrict S hS, ?_⟩
    rw [unroot_restrictClusters, hT]⟩

/-- Forgetting the root commutes with restricting the taxa. -/
theorem RootedTopology.toUnrooted_restrict (H : RootedTopology X)
    (S : Finset X) (hS : S.Nonempty) :
    (H.restrict S hS).toUnrooted = H.toUnrooted.restrict S hS := by
  apply Subtype.ext
  exact unroot_restrictClusters H.val S

/-- An unrooted topology contains complementary split sides together. -/
theorem UnrootedTopology.compl_mem (T : UnrootedTopology X) (A : Finset X) :
    Aᶜ ∈ T.val ↔ A ∈ T.val := by
  obtain ⟨H, _, hH⟩ := T.property
  rw [← hH]
  exact compl_mem_unroot

/-- Any two split sides of one topology satisfy the ordinary split compatibility law. -/
theorem UnrootedTopology.compatible (T : UnrootedTopology X) {A B : Finset X}
    (hA : A ∈ T.val) (hB : B ∈ T.val) :
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ := by
  obtain ⟨H, hH, hT⟩ := T.property
  rw [← hT] at hA hB
  exact hH.compatible_of_mem_unroot hA hB

/-- Every internal cluster of a binary rooted topology, including the root, has exactly
two children. This is a degree property, separate from the hierarchy law. -/
def RootedTopology.IsBinary (H : RootedTopology X) : Prop :=
  ∀ A ∈ H.val, 2 ≤ A.card → (childClusters H.val A).card = 2

/-- An unrooted topology is binary if it has a rooted binary representative.
The graph-level equivalence uses rooting on an edge: rooting at an existing degree-three
vertex would give three children at the root. That equivalence is not asserted here. -/
def UnrootedTopology.IsBinary (T : UnrootedTopology X) : Prop :=
  ∃ H : RootedTopology X, H.IsBinary ∧ H.toUnrooted = T

/-- Binary unrooted topologies form a finite subtype of actual topologies. -/
abbrev BinaryTopology (X : Type*) [Fintype X] [DecidableEq X] :=
  {T : UnrootedTopology X // T.IsBinary}

instance : Fintype (BinaryTopology X) := Fintype.ofFinite _

/-- A topology displays a quartet split when both unordered pair blocks occur as split
sides after restriction to that quartet. -/
def UnrootedTopology.Displays (T : UnrootedTopology X) {q : Quartet X}
    (p : QuartetSplit q) : Prop :=
  ∀ B ∈ p.val, B.val ∈ restrictSplits q.val T.val

/-- Among the three resolutions on four standard labels, pairwise split compatibility
forces equality. This is a finite representation check, not a paper theorem. -/
private theorem standardPairings_eq_of_compatible : ∀ p r : Pairing (Fin 4),
    (∀ A ∈ p.val, ∀ B ∈ r.val,
      A.val ⊆ B.val ∨ B.val ⊆ A.val ∨ Disjoint A.val B.val ∨ A.val ∪ B.val = univ) →
    p = r := by decide

omit [Fintype X] in
/-- Two quartet resolutions whose pair blocks are all compatible must be the same. -/
theorem QuartetSplit.eq_of_compatible {q : Quartet X} (p r : QuartetSplit q)
    (hcompat : ∀ A ∈ p.val, ∀ B ∈ r.val,
      A.val ⊆ B.val ∨ B.val ⊆ A.val ∨ Disjoint A.val B.val ∨ A.val ∪ B.val = univ) :
    p = r := by
  let e : q.val ≃ Fin 4 := Finset.equivFinOfCardEq q.property
  apply (Pairing.congr e).injective
  apply standardPairings_eq_of_compatible
  intro A hA B hB
  change A ∈ p.val.map (TaxonPair.congr e).toEmbedding at hA
  change B ∈ r.val.map (TaxonPair.congr e).toEmbedding at hB
  obtain ⟨A₀, hA₀, hAA⟩ := Finset.mem_map.mp hA
  obtain ⟨B₀, hB₀, hBB⟩ := Finset.mem_map.mp hB
  subst A
  subst B
  change A₀.val.map e.toEmbedding ⊆ B₀.val.map e.toEmbedding ∨
    B₀.val.map e.toEmbedding ⊆ A₀.val.map e.toEmbedding ∨
    Disjoint (A₀.val.map e.toEmbedding) (B₀.val.map e.toEmbedding) ∨
    A₀.val.map e.toEmbedding ∪ B₀.val.map e.toEmbedding = univ
  rcases hcompat A₀ hA₀ B₀ hB₀ with h | h | h | h
  · exact Or.inl (map_subset_map.mpr h)
  · exact Or.inr (Or.inl (map_subset_map.mpr h))
  · exact Or.inr (Or.inr (Or.inl (by simpa only [disjoint_map] using h)))
  · exact Or.inr (Or.inr (Or.inr (by rw [← map_union, h, map_univ_equiv])))

/-- A valid unrooted topology displays at most one resolution of any quartet. -/
theorem UnrootedTopology.eq_of_displays (T : UnrootedTopology X) {q : Quartet X}
    {p r : QuartetSplit q} (hp : T.Displays p) (hr : T.Displays r) : p = r := by
  apply QuartetSplit.eq_of_compatible
  intro A hA B hB
  have hq : q.val.Nonempty := card_pos.mp (by rw [q.property]; decide)
  exact (T.restrict q.val hq).compatible (hp A hA) (hr B hB)

/-! The following hierarchy restriction helpers follow the corresponding proofs in
`lean4-phylogenetics`, commit `06f684e526e276ca2ccf668a1c3a808a2b8c181d` (Apache2.0).
They remove only the unused metric data. See `docs/ADAPTED_SOURCES.md`. -/

/-- The least cluster containing a set, expressed as an intersection of clusters. -/
def lca (H : Finset (Finset X)) (T : Finset X) : Finset X :=
  (H.filter (T ⊆ ·)).inf id

theorem subset_lca (H : Finset (Finset X)) (T : Finset X) : T ⊆ lca H T :=
  Finset.le_inf fun _ hC => (mem_filter.1 hC).2

theorem lca_subset {H : Finset (Finset X)} {T C : Finset X} (hC : C ∈ H) (hTC : T ⊆ C) :
    lca H T ⊆ C :=
  Finset.inf_le (f := id) (mem_filter.2 ⟨hC, hTC⟩)

private theorem hier_inf_mem {H : Finset (Finset X)} (hH : IsHierarchy H)
    (x : X) (p : Finset X → Prop) :
    ∀ C ∈ {C | C ∈ H ∧ x ∈ C ∧ p C}, ∀ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C},
      C ⊓ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C} := by
  rintro C hC D hD
  rcases hH.subset_or_subset_of_mem hC.1 hD.1 hC.2.1 hD.2.1 with h | h
  · rwa [inf_eq_left.2 h]
  · rwa [inf_eq_right.2 h]

/-- In a hierarchy, the least cluster containing a nonempty set is a cluster. -/
theorem IsHierarchy.lca_mem {H : Finset (Finset X)} (hH : IsHierarchy H)
    {T : Finset X} (hT : T.Nonempty) : lca H T ∈ H := by
  obtain ⟨t, ht⟩ := hT
  have := Finset.inf_mem {C | C ∈ H ∧ t ∈ C ∧ T ⊆ C}
    ⟨hH.1, mem_univ t, subset_univ T⟩ (hier_inf_mem hH t (T ⊆ ·))
    (H.filter (T ⊆ ·)) id
    (fun C hC => ⟨(mem_filter.1 hC).1, (mem_filter.1 hC).2 ht, (mem_filter.1 hC).2⟩)
  exact this.1

omit [Fintype X] in
/-- Mapping a trace from the taxon subtype back to the ambient type gives intersection. -/
theorem map_subtype_eq_inter (S A : Finset X) :
    (A.subtype (· ∈ S)).map (Function.Embedding.subtype _) = A ∩ S := by
  rw [subtype_map, filter_mem_eq_inter]

/-- Every restricted cluster is the trace of the least cluster containing it. -/
theorem subtype_lca_eq {S : Finset X} {H : Finset (Finset X)} {C : Finset S}
    (hC : C ∈ restrictClusters S H) :
    (lca H (C.map (Function.Embedding.subtype _))).subtype (· ∈ S) = C := by
  obtain ⟨A, hA, -, rfl⟩ := mem_restrictClusters.1 hC
  apply Subset.antisymm
  · intro x hx
    rw [mem_subtype] at hx ⊢
    apply lca_subset hA _ hx
    rw [map_subtype_eq_inter]
    exact inter_subset_left
  · intro x hx
    rw [mem_subtype]
    apply subset_lca
    exact mem_map_of_mem _ hx

/-- The two children of a binary hierarchy partition each internal cluster.
This is the cardinality-to-splitting direction of the upstream binary equivalence. -/
theorem RootedTopology.IsBinary.splits {H : RootedTopology X} (hH : H.IsBinary)
    {A : Finset X} (hA : A ∈ H.val) (hA2 : 2 ≤ A.card) :
    ∃ B ∈ H.val, ∃ C ∈ H.val, Disjoint B C ∧ B ∪ C = A := by
  obtain ⟨B, C, hBC, hch⟩ := card_eq_two.1 (hH A hA hA2)
  have hB : B ∈ childClusters H.val A := hch ▸ mem_insert_self _ _
  have hC : C ∈ childClusters H.val A := hch ▸ mem_insert_of_mem (mem_singleton_self _)
  refine ⟨B, (mem_childClusters.1 hB).1, C, (mem_childClusters.1 hC).1,
    H.property.disjoint_of_mem_childClusters hB hC hBC, ?_⟩
  have := H.property.sup_childClusters hA2
  rwa [hch, sup_insert, sup_singleton] at this

/-- Every internal cluster of a restricted binary hierarchy splits into two nonempty
disjoint clusters. The proof follows the upstream binary-restriction proof: lift the
restricted cluster to its least containing cluster, then trace that cluster's two children. -/
theorem RootedTopology.IsBinary.restrict_splits {H : RootedTopology X} (hH : H.IsBinary)
    (S : Finset X) {C : Finset S} (hC : C ∈ restrictClusters S H.val) (hC2 : 2 ≤ C.card) :
    ∃ B ∈ restrictClusters S H.val, ∃ D ∈ restrictClusters S H.val,
      Disjoint B D ∧ B ∪ D = C := by
  set T := C.map (Function.Embedding.subtype (· ∈ S))
  have hTC : #T = #C := card_map _
  have hT : T.Nonempty := card_pos.1 (by omega)
  have hTS : T ⊆ S := fun x hx => by
    obtain ⟨y, -, rfl⟩ := mem_map.1 hx
    exact y.2
  have hL : lca H.val T ∈ H.val := H.property.lca_mem hT
  have hLC : (lca H.val T).subtype (· ∈ S) = C := subtype_lca_eq hC
  have hL2 : 2 ≤ #(lca H.val T) := by
    have := card_le_card (subset_lca H.val T)
    omega
  obtain ⟨B, hB, D, hD, hBD, hBDL⟩ := hH.splits hL hL2
  have hnot : ∀ E ∈ H.val, E ⊆ lca H.val T → E ≠ lca H.val T → ¬ T ⊆ E :=
    fun E hE hEL hne hTE => hne (Subset.antisymm hEL (lca_subset hE hTE))
  have hBne : B ≠ lca H.val T := by
    intro e
    obtain ⟨d, hd⟩ := H.property.2.2.1 D hD
    exact disjoint_left.1 hBD (e ▸ hBDL ▸ mem_union_right B hd) hd
  have hDne : D ≠ lca H.val T := by
    intro e
    obtain ⟨b, hb⟩ := H.property.2.2.1 B hB
    exact disjoint_left.1 hBD hb (e ▸ hBDL ▸ mem_union_left D hb)
  have hBS : (B ∩ S).Nonempty := by
    obtain ⟨t, htT, htD⟩ := not_subset.1 (hnot D hD (hBDL ▸ subset_union_right) hDne)
    have htL : t ∈ B ∪ D := hBDL ▸ subset_lca _ T htT
    exact ⟨t, mem_inter.2 ⟨(mem_union.1 htL).resolve_right htD, hTS htT⟩⟩
  have hDS : (D ∩ S).Nonempty := by
    obtain ⟨t, htT, htB⟩ := not_subset.1 (hnot B hB (hBDL ▸ subset_union_left) hBne)
    have htL : t ∈ B ∪ D := hBDL ▸ subset_lca _ T htT
    exact ⟨t, mem_inter.2 ⟨(mem_union.1 htL).resolve_left htB, hTS htT⟩⟩
  refine ⟨B.subtype (· ∈ S), subtype_mem_restrictClusters hB hBS,
    D.subtype (· ∈ S), subtype_mem_restrictClusters hD hDS, ?_, ?_⟩
  · exact disjoint_left.2 fun x hxB hxD =>
      disjoint_left.1 hBD (mem_subtype.1 hxB) (mem_subtype.1 hxD)
  · rw [← hLC, ← hBDL]
    ext x
    simp only [mem_union, mem_subtype]

/-! A binary hierarchy on four taxa has a two-taxon cluster: its root splits as
two plus two, or one plus three, and in the latter case the three-cluster splits
as one plus two. This avoids enumerating all finite families of clusters. -/

private theorem pair_cluster_of_card_four (hX : Fintype.card X = 4)
    {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hsplit : ∀ A ∈ H, 2 ≤ A.card →
      ∃ B ∈ H, ∃ C ∈ H, Disjoint B C ∧ B ∪ C = A) :
    ∃ A ∈ H, A.card = 2 := by
  obtain ⟨B, hB, C, hC, hBC, hBCu⟩ :=
    hsplit univ hH.1 (by rw [card_univ, hX]; decide)
  have hBpos : 0 < B.card := card_pos.mpr (hH.2.2.1 B hB)
  have hCpos : 0 < C.card := card_pos.mpr (hH.2.2.1 C hC)
  have hsum : B.card + C.card = 4 := by
    rw [← card_union_of_disjoint hBC, hBCu, card_univ, hX]
  by_cases hB2 : B.card = 2
  · exact ⟨B, hB, hB2⟩
  by_cases hC2 : C.card = 2
  · exact ⟨C, hC, hC2⟩
  have hthree : ∃ D ∈ H, D.card = 3 := by
    have h : B.card = 3 ∨ C.card = 3 := by omega
    exact h.elim (fun h => ⟨B, hB, h⟩) (fun h => ⟨C, hC, h⟩)
  obtain ⟨D, hD, hD3⟩ := hthree
  obtain ⟨E, hE, F, hF, hEF, hEFD⟩ := hsplit D hD (by omega)
  have hEpos : 0 < E.card := card_pos.mpr (hH.2.2.1 E hE)
  have hFpos : 0 < F.card := card_pos.mpr (hH.2.2.1 F hF)
  have hsum3 : E.card + F.card = 3 := by
    rw [← card_union_of_disjoint hEF, hEFD, hD3]
  have h : E.card = 2 ∨ F.card = 2 := by omega
  exact h.elim (fun h => ⟨E, hE, h⟩) (fun h => ⟨F, hF, h⟩)

/-- Either pair of a quartet determines the pairing with its complementary pair. -/
def QuartetSplit.ofPair {q : Quartet X} (A : TaxonPair q.val) : QuartetSplit q := by
  let B : TaxonPair q.val := ⟨A.valᶜ, by
    rw [card_compl, Fintype.card_coe, q.property, A.property]⟩
  have hne : A ≠ B := by
    intro h
    have heq : A.val = A.valᶜ := congrArg Subtype.val h
    obtain ⟨a, ha⟩ := card_pos.mp (show 0 < A.val.card by rw [A.property]; decide)
    exact (mem_compl.mp (heq ▸ ha)) ha
  refine ⟨{A, B}, card_pair hne, ?_⟩
  simp [B]

omit [Fintype X] in
/-- The blocks in the constructed pairing are the chosen pair and its complement. -/
theorem QuartetSplit.ofPair_block {q : Quartet X} (A : TaxonPair q.val)
    (B : TaxonPair q.val) (hB : B ∈ (QuartetSplit.ofPair A).val) :
    B.val = A.val ∨ B.val = A.valᶜ := by
  simp only [QuartetSplit.ofPair, mem_insert, mem_singleton] at hB
  exact hB.elim (fun h => Or.inl (congrArg Subtype.val h))
    (fun h => Or.inr (congrArg Subtype.val h))

/-- Every binary unrooted topology displays a resolution of every quartet.
The argument restricts a binary hierarchy, finds its two-taxon cluster, and takes
that cluster together with its complement as the actual unordered quartet split. -/
theorem UnrootedTopology.IsBinary.exists_displays {T : UnrootedTopology X}
    (hT : T.IsBinary) (q : Quartet X) : ∃ p : QuartetSplit q, T.Displays p := by
  obtain ⟨H, hH, rfl⟩ := hT
  have hq : q.val.Nonempty := card_pos.mp (by rw [q.property]; decide)
  have hq4 : Fintype.card q.val = 4 := by rw [Fintype.card_coe, q.property]
  obtain ⟨A, hA, hA2⟩ := pair_cluster_of_card_four hq4 (H.property.restrict q.val hq)
    (fun C hC hC2 => hH.restrict_splits q.val hC hC2)
  let a : TaxonPair q.val := ⟨A, hA2⟩
  refine ⟨QuartetSplit.ofPair a, ?_⟩
  intro B hB
  change B.val ∈ restrictSplits q.val (unroot H.val)
  rw [← unroot_restrictClusters]
  have hAu : A ≠ univ := by
    intro h
    have : A.card = 4 := by rw [h, card_univ, hq4]
    omega
  have hAunroot : A ∈ unroot (restrictClusters q.val H.val) :=
    mem_unroot.mpr (Or.inl ⟨hA, hAu⟩)
  rcases QuartetSplit.ofPair_block a B hB with h | h
  · exact h ▸ hAunroot
  · exact h ▸ compl_mem_unroot.mpr hAunroot

/-- Binary unrooted topologies display exactly one resolution of each unordered quartet. -/
theorem BinaryTopology.existsUnique_displays (T : BinaryTopology X) (q : Quartet X) :
    ∃! p : QuartetSplit q, T.val.Displays p := by
  obtain ⟨p, hp⟩ := T.property.exists_displays q
  exact ⟨p, hp, fun r hr => T.val.eq_of_displays hr hp⟩

/-- The actual quartet resolution induced by a binary topology, selected from the proved
existence-and-uniqueness statement rather than supplied as independent data. -/
def BinaryTopology.quartetSplit (T : BinaryTopology X) (q : Quartet X) : QuartetSplit q :=
  (T.existsUnique_displays q).choose

/-- The selected quartet resolution is displayed by its binary topology. -/
theorem BinaryTopology.displays_quartetSplit (T : BinaryTopology X) (q : Quartet X) :
    T.val.Displays (T.quartetSplit q) := (T.existsUnique_displays q).choose_spec.1

/-- The display predicate agrees exactly with the induced-quartet function. -/
theorem BinaryTopology.displays_iff (T : BinaryTopology X) {q : Quartet X}
    (p : QuartetSplit q) : T.val.Displays p ↔ p = T.quartetSplit q := by
  constructor
  · intro hp
    exact T.val.eq_of_displays hp (T.displays_quartetSplit q)
  · rintro rfl
    exact T.displays_quartetSplit q

end Phylogenetics
