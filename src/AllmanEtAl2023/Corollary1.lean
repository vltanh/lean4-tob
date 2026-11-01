module

public import Phylogenetics.NMSC.Induced
public import Phylogenetics.NMSC.InducedParams
public import Phylogenetics.Tree.Splice
public import AllmanEtAl2023.Theorem1

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Corollary 1

For generic numerical parameters on a binary network, CF-detectability holds on all induced 4-taxon
networks (`notes/sources/allman2023.txt`, lines 154-157). The proof has the source's two sentences: "By Theorem 1, for
generic numerical parameter values on each induced 4-taxon network we have CF-detectability ... Since the
generic conditions only exclude a set of measure zero from the numerical parameter space of each 4-taxon
network, they give rise to a generic condition on numerical parameter values on the n-taxon network." But it applies
them to another induced network than the source's: see "Departure from the source" below.

The steps, for a set `Q` of four taxa and the network `M` induced on it:

1. `M` is a binary network on four taxa (`inducedNetwork_isBinary`), so Theorem 1 gives a null set of its
   parameters off which CF-detectability holds on `M`;
2. the preimage of that set under the map of parameters is null (`isGenericNull_inducedMetric`), and the
   map sends valid parameters to valid parameters (`isMetric_inducedMetric`);
3. the union over the finitely many `Q` is null (`IsGenericNull.iUnion`);
4. CF-detectability on `M` is CF-detectability of `N` on `Q`: the splits of `M` are those of `N` on `Q`
   (`inducedCutSplit_map_iff`, `isTreelike_iff_inducedNetwork`), and CFs do not change on passing to `M`
   (`NMSC.nmscCF_inducedNetwork`, `isStrictlyCut_map_iff`, `isNonCut_iff_of_map`).

The quartet trees on `Q` are those on the taxa `↥Q` of `M`, through `QuartetTree.map`
(`map_val_taxa`, `exists_map_val_eq`).

## Departure from the source

The source's induced network (Definition 6, line 58) keeps what lies above the LSA of the taxa, up to the root, and removes
only a stem above the root. Here `M` is `inducedNetwork` (ECToBlob §2), which cuts at the LSA. So step 4 needs more than the
source's remark on line 108, that "CFs remain unchanged": it needs that the part above the LSA does not change a quartet CF
(`NMSC.nmscCF_belowNetwork`), a four-taxon exchangeability fact which the source does not need. See the note at
`corollary1`. This is not forced.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset MeasureTheory
open scoped Classical

open Phylogenetics.DirectedMultigraph AllmanEtAl2023

open Phylogenetics.NMSC

namespace AllmanEtAl2023

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-! ### Quartet trees on a set of four taxa and on its subtype -/

section QuartetTrees

variable {Q : Finset X} [Fintype ↥(Q : Set X)] [DecidableEq ↥(Q : Set X)]

omit [Fintype X] [DecidableEq X] [DecidableEq ↥(Q : Set X)] in
/-- The subtype of a finite set of taxa has as many elements as the set. -/
theorem card_coe_finset (Q : Finset X) [Fintype ↥(Q : Set X)] :
    Fintype.card ↥(Q : Set X) = Q.card := by
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Set.ncard_coe_finset]

omit [Fintype X] [DecidableEq ↥(Q : Set X)] in
/-- The elements of the subtype of a finite set of taxa are its elements. -/
theorem image_val_univ_coe (Q : Finset X) [Fintype ↥(Q : Set X)] :
    (univ : Finset ↥(Q : Set X)).image Subtype.val = Q := by
  ext x
  simp

omit [Fintype X] [DecidableEq X] in
/-- A quartet tree on the subtype of a set of four taxa uses them all. -/
theorem taxa_eq_univ (hQ : Q.card = 4) (s : QuartetTree ↥(Q : Set X)) : s.taxa = univ :=
  eq_univ_of_card _ (s.card_taxa.trans ((card_coe_finset Q).trans hQ).symm)

omit [Fintype X] in
/-- The image of a quartet tree on `↥Q` has the taxa `Q`. -/
theorem map_val_taxa (hQ : Q.card = 4) (s : QuartetTree ↥(Q : Set X)) :
    (s.map Subtype.val_injective).taxa = Q := by
  rw [QuartetTree.map_taxa, taxa_eq_univ hQ, image_val_univ_coe]

/-- The alternatives of the image of a quartet tree on `↥Q` are the images of its alternatives. -/
theorem map_mem_alternatives_iff (hQ : Q.card = 4) {s r : QuartetTree ↥(Q : Set X)} :
    r.map Subtype.val_injective ∈ (s.map Subtype.val_injective).alternatives ↔
      r ∈ s.alternatives := by
  rw [QuartetTree.mem_alternatives, QuartetTree.mem_alternatives, map_val_taxa hQ, map_val_taxa hQ,
    taxa_eq_univ hQ, taxa_eq_univ hQ, (QuartetTree.map_injective Subtype.val_injective).ne_iff]
  simp

end QuartetTrees

/-! ### Transporting the properties of a concordance factor -/

section Transport

variable {Q : Finset X} [Fintype ↥(Q : Set X)] [DecidableEq ↥(Q : Set X)]
  {p' : QuartetTree ↥(Q : Set X) → ℝ} {p : QuartetTree X → ℝ}

/-- A weight that does not change on passing to `↥Q` is strictly `s`-cut on `X` exactly when it is on
`↥Q`. -/
theorem isStrictlyCut_map_iff (hQ : Q.card = 4)
    (hp : ∀ s', p' s' = p (s'.map Subtype.val_injective)) (s : QuartetTree ↥(Q : Set X)) :
    IsStrictlyCut p (s.map Subtype.val_injective) ↔ IsStrictlyCut p' s := by
  have hex : ∀ r ∈ (s.map Subtype.val_injective).alternatives,
      ∃ r' : QuartetTree ↥(Q : Set X), r' ∈ s.alternatives ∧ r'.map Subtype.val_injective = r := by
    intro r hr
    obtain ⟨r', rfl⟩ := exists_map_val_eq (Q := Q) ((QuartetTree.mem_alternatives.1 hr).1.trans
      (map_val_taxa hQ s))
    exact ⟨r', (map_mem_alternatives_iff hQ).1 hr, rfl⟩
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩
    · rw [hp, hp]
      exact h₁ _ ((map_mem_alternatives_iff hQ).2 hr)
    · rw [hp, hp]
      exact h₂ _ ((map_mem_alternatives_iff hQ).2 hr) _ ((map_mem_alternatives_iff hQ).2 hr')
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩
    · obtain ⟨t, ht, rfl⟩ := hex r hr
      rw [← hp, ← hp]
      exact h₁ t ht
    · obtain ⟨t, ht, rfl⟩ := hex r hr
      obtain ⟨t', ht', rfl⟩ := hex r' hr'
      rw [← hp, ← hp]
      exact h₂ t ht t' ht'

/-- A weight that does not change on passing to `↥Q` is non-cut on `Q` exactly when it is on `↥Q`. -/
theorem isNonCut_iff_of_map (hQ : Q.card = 4)
    (hp : ∀ s', p' s' = p (s'.map Subtype.val_injective)) : IsNonCut p Q ↔ IsNonCut p' univ := by
  constructor
  · intro h r _ r' _ hne
    rw [hp, hp]
    exact h _ (mem_treesOn.2 (map_val_taxa hQ r)) _ (mem_treesOn.2 (map_val_taxa hQ r'))
      ((QuartetTree.map_injective Subtype.val_injective).ne hne)
  · intro h r hr r' hr' hne
    obtain ⟨t, rfl⟩ := exists_map_val_eq (Q := Q) (mem_treesOn.1 hr)
    obtain ⟨t', rfl⟩ := exists_map_val_eq (Q := Q) (mem_treesOn.1 hr')
    rw [← hp, ← hp]
    exact h t (mem_treesOn.2 (taxa_eq_univ hQ t)) t' (mem_treesOn.2 (taxa_eq_univ hQ t'))
      fun e => hne (e ▸ rfl)

end Transport

/-! ### The cut-edge splits of the induced network -/

section Splits

variable {Q : Finset X} [Fintype ↥(Q : Set X)] [DecidableEq ↥(Q : Set X)]

omit [Fintype X] [Fintype ↥(Q : Set X)] in
/-- **A cherry of a quartet tree on `↥Q` is a cut-edge split on `Q` exactly when it is one of the network
induced on `Q`**, by `hasCutSplitOn_iff_inducedNetwork_hasCutSplit`. -/
theorem hasCutSplitOn_image_iff (hN : N.IsPhylogenetic)
    (hY : (Q : Set X).Nontrivial) (s : QuartetTree ↥(Q : Set X)) {B : Finset ↥(Q : Set X)}
    (hB : B ∈ s.val) :
    N.HasCutSplitOn (Q : Set X) (B.image Subtype.val : Finset X) ↔
      (inducedNetwork hN (Q : Set X) hY).HasCutSplitOn Set.univ (B : Set ↥(Q : Set X)) := by
  have hne : ∀ {C : Finset ↥(Q : Set X)}, C ∈ s.val → C.Nonempty := fun hC =>
    card_pos.1 (by rw [s.card_of_mem hC]; omega)
  have h₁ : ((Q : Set X) ∩ (B.image Subtype.val : Finset X)).Nonempty := by
    obtain ⟨y, hy⟩ := hne hB
    exact ⟨y.1, y.2, mem_coe.2 (mem_image_of_mem _ hy)⟩
  have h₂ : ((Q : Set X) \ (B.image Subtype.val : Finset X)).Nonempty := by
    obtain ⟨y, hy⟩ := hne (s.sdiff_mem hB)
    refine ⟨y.1, y.2, fun hyB => (mem_sdiff.1 hy).2 ?_⟩
    obtain ⟨z, hz, hzy⟩ := mem_image.1 (mem_coe.1 hyB)
    rwa [← Subtype.ext hzy]
  have hpre : Subtype.val ⁻¹' ((B.image Subtype.val : Finset X) : Set X) = (B : Set ↥(Q : Set X)) := by
    ext y
    simp
  rw [hasCutSplitOn_iff_inducedNetwork_hasCutSplit hN hY h₁ h₂, hpre,
    hasCutSplit_iff_hasCutSplitOn_univ (inducedNetwork_isPhylogenetic hN hY)]

omit [Fintype X] in
/-- **A quartet tree on `↥Q` is a cut-edge split of the network induced on `Q` exactly when its image is
one on `Q`.** -/
theorem inducedCutSplit_map_iff (hN : N.IsPhylogenetic) (hQ : Q.card = 4)
    (hY : (Q : Set X).Nontrivial) (s : QuartetTree ↥(Q : Set X)) :
    InducedCutSplit N (s.map Subtype.val_injective) ↔
      InducedCutSplit (inducedNetwork hN (Q : Set X) hY) s := by
  unfold InducedCutSplit
  rw [map_val_taxa hQ, taxa_eq_univ hQ, coe_univ (α := ↥(Q : Set X))]
  constructor
  · rintro ⟨B, hB, hc⟩
    obtain ⟨B', hB', rfl⟩ := mem_image.1 hB
    exact ⟨B', hB', (hasCutSplitOn_image_iff hN hY s hB').1 hc⟩
  · rintro ⟨B, hB, hc⟩
    exact ⟨_, mem_image_of_mem _ hB, (hasCutSplitOn_image_iff hN hY s hB).2 hc⟩

/-- **The induced network on `Q` has a cut-edge split exactly when `Q` is treelike.** -/
theorem isTreelike_iff_inducedNetwork (hN : N.IsPhylogenetic) (hQ : Q.card = 4)
    (hY : (Q : Set X).Nontrivial) :
    IsTreelike N Q ↔ IsTreelike (inducedNetwork hN (Q : Set X) hY) univ := by
  unfold IsTreelike
  constructor
  · rintro ⟨s, hs, hc⟩
    obtain ⟨s', rfl⟩ := exists_map_val_eq (Q := Q) (mem_treesOn.1 hs)
    exact ⟨s', mem_treesOn.2 (taxa_eq_univ hQ s'), (inducedCutSplit_map_iff hN hQ hY s').1 hc⟩
  · rintro ⟨s', -, hc⟩
    exact ⟨s'.map Subtype.val_injective, mem_treesOn.2 (map_val_taxa hQ s'),
      (inducedCutSplit_map_iff hN hQ hY s').2 hc⟩

end Splits

/-! ### Corollary 1 -/

variable [Fintype V] [Fintype E]

omit [Fintype X] [DecidableEq X] [Fintype V] [Fintype E] in
/-- A set of four taxa has at least two elements, so the network it induces is defined. -/
theorem nontrivial_coe_of_card {Q : Finset X} (hQ : Q.card = 4) : (Q : Set X).Nontrivial :=
  one_lt_card_iff_nontrivial.1 (by omega)

/-- CF-detectability of `N` from the conclusion of Theorem 1 on the networks induced on its 4-sets, given that
CFs do not change on passing to an induced network (`notes/sources/allman2023.txt`, line 108). A quartet tree
`s` of `N` lives on the network induced on its taxa, and a 4-set `q` is the set of all taxa of the network it
induces. -/
theorem cfDetectable_of_inducedNetwork (hN : N.IsPhylogenetic)
    (hCF : ∀ (Q : Finset X) (hQ : Q.card = 4) (θ : RootedNetwork.MetricData E), N.IsMetric θ →
      ∀ s' : QuartetTree ↥(Q : Set X),
        nmscCF (inducedNetwork hN (Q : Set X) (nontrivial_coe_of_card hQ))
          (inducedMetric hN (Q : Set X) (nontrivial_coe_of_card hQ).nonempty θ) 0 s' =
        nmscCF N θ 0 (s'.map Subtype.val_injective))
    {θ : RootedNetwork.MetricData E} (hθ : N.IsMetric θ)
    (hall : ∀ (Q : Finset X) (hQ : Q.card = 4),
      (∀ s' : QuartetTree ↥(Q : Set X),
        InducedCutSplit (inducedNetwork hN (Q : Set X) (nontrivial_coe_of_card hQ)) s' ↔
          IsStrictlyCut (nmscCF (inducedNetwork hN (Q : Set X) (nontrivial_coe_of_card hQ))
            (inducedMetric hN (Q : Set X) (nontrivial_coe_of_card hQ).nonempty θ) 0) s') ∧
        (¬ IsTreelike (inducedNetwork hN (Q : Set X) (nontrivial_coe_of_card hQ)) Finset.univ ↔
          IsNonCut (nmscCF (inducedNetwork hN (Q : Set X) (nontrivial_coe_of_card hQ))
            (inducedMetric hN (Q : Set X) (nontrivial_coe_of_card hQ).nonempty θ) 0) Finset.univ)) :
    CFDetectable N (nmscCF N θ 0) := by
  refine ⟨fun s hs => ?_, fun q hq hnt => ?_⟩
  · obtain ⟨s', hs'⟩ := exists_map_val_eq (Q := s.taxa) rfl
    have hQ := s.card_taxa
    rw [← hs'] at hs ⊢
    exact (isStrictlyCut_map_iff hQ (hCF _ hQ θ hθ) s').2
      (((hall _ hQ).1 s').1 ((inducedCutSplit_map_iff hN hQ _ s').1 hs))
  · exact (isNonCut_iff_of_map hq (hCF q hq θ hθ)).2
      ((hall q hq).2.1 fun h => hnt ((isTreelike_iff_inducedNetwork hN hq _).2 h))

/-- **Corollary 1 of the source** (`notes/sources/allman2023.txt`, lines 154-157): for a rooted binary
phylogenetic network, the numerical parameters at which the NMSC with independent inheritance fails
CF-detectability on some induced 4-taxon network form a null set. The proof has the source's two sentences: "By
Theorem 1, for generic numerical parameter values on each induced 4-taxon network we have CF-detectability ... Since the
generic conditions only exclude a set of measure zero from the numerical parameter space of each 4-taxon
network, they give rise to a generic condition on numerical parameter values on the n-taxon network." The
exclusion on each `Q` is the preimage under the map of parameters of the null set of Theorem 1 on the network
induced on `Q`, which is null by `isGenericNull_inducedMetric`.

Departure from the paper: the source's induced network (Definition 6, line 58) keeps what lies above the LSA of the four
taxa, up to the root, removing only a stem above the root. This proof applies Theorem 1 to `inducedNetwork` (ECToBlob §2),
which cuts at the LSA. The formalization has one induced network, whose cut-edge splits agree with `HasCutSplitOn`
(`hasCutSplitOn_iff_inducedNetwork_hasCutSplit`), and using it here avoids a second one. So the identity `hCF` says more
than the source's remark on line 108 that "CFs remain unchanged" on passing to an induced network: it also passes the part
above the LSA (`NMSC.nmscCF_inducedNetwork`, through `NMSC.nmscCF_belowNetwork`), and that is a four-taxon exchangeability
fact which the source's proof does not need. What is proved on the way is therefore stronger than what the source needs:
CFs do not change even on passing to the network cut at the LSA. This is not forced. With a network of Definition 6, which
would be a second induced network with its own cut-edge splits, `hCF` would need only the restriction to the arcs ancestral
to the taxa, the suppression step (`NMSC.geneTreeDist_suppress`), and the removal of the stem. -/
theorem corollary1 (hN : N.IsPhylogenetic) (hBin : N.IsBinary) :
    Corollary1 N := by
  have hCF : ∀ (Q : Finset X) (hQ : Q.card = 4) (θ : RootedNetwork.MetricData E), N.IsMetric θ →
      ∀ s' : QuartetTree ↥(Q : Set X),
        nmscCF (inducedNetwork hN (Q : Set X) (nontrivial_coe_of_card hQ))
          (inducedMetric hN (Q : Set X) (nontrivial_coe_of_card hQ).nonempty θ) 0 s' =
        nmscCF N θ 0 (s'.map Subtype.val_injective) :=
    fun Q hQ θ hθ s' => NMSC.nmscCF_inducedNetwork hN hθ ⟨le_rfl, zero_le_one⟩ hQ
      (nontrivial_coe_of_card hQ) s'
  refine (IsGenericNull.iUnion (ι := {Q : Finset X // Q.card = 4}) fun Q =>
    isGenericNull_inducedMetric hN (nontrivial_coe_of_card Q.2)
      (theorem1 (inducedNetwork_isPhylogenetic hN _) (inducedNetwork_isBinary hN hBin _)
        ((card_coe_finset Q.1).trans Q.2))).mono ?_
  rintro θ ⟨hθ, hnot⟩
  by_contra hall
  refine hnot (cfDetectable_of_inducedNetwork hN hCF hθ fun Q hQ => ?_)
  by_contra hbad
  exact hall (Set.mem_iUnion.2 ⟨⟨Q, hQ⟩, hθ,
    isMetric_inducedMetric hN (nontrivial_coe_of_card hQ) hθ, hbad⟩)

end AllmanEtAl2023
