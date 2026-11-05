module

public import External.GusfieldEtAl2004.Algorithm
public import External.GusfieldEtAl2004.Build
public import External.GusfieldEtAl2004.BuildCount
public import External.GusfieldEtAl2004.Elimination
public import External.GusfieldEtAl2004.GalledTree
public import External.GusfieldEtAl2004.Optimality
public import External.GusfieldEtAl2004.SameBlob
public import External.GusfieldEtAl2004.Theorem2_2
public import External.HudsonKaplan1985.Algorithm
public import External.MyersGriffiths2003.Algorithm1
public import External.MyersGriffiths2003.Composite
public import External.SongHein2005.BinaryPaths
public import Gusfield2007.CounterexampleNets
public import Gusfield2007.Counterexamples
public import Gusfield2007.Decomposition
public import Gusfield2007.Defs
public import Gusfield2007.EntryNet
public import Gusfield2007.Examples
public import Gusfield2007.HusonKloepper
public import Gusfield2007.MdLower
public import Gusfield2007.MergedTreeness
public import Gusfield2007.NetworkOps
public import Gusfield2007.OpenStatements
public import Gusfield2007.Realizability
public import Gusfield2007.SufficientConditions
public import Gusfield2007.SuperCharacters
public import Gusfield2007.Theorem10PrintedMultiple
public import Gusfield2007.TimeOrdered
public import Gusfield2007.Uniqueness

/-!
# The main results of Gusfield et al. 2007

Gusfield, Bansal, Bafna, Song, J. Comput. Biol. 14, 2007: Lemma 4, Theorems 1 and 3 to 11, Corollaries 2 and 3, the refutation of its conjectures, and the main results of the sources that only it uses: Gusfield, Eddhu, Langley 2004 (`galled_`), Myers, Griffiths 2003 (`myersGriffiths_`), Hudson, Kaplan 1985 (`hudsonKaplan_`) and Song, Hein 2005 (`songHein_`). The theorems are on sequences of binary sites, in `Gusfield2007`, whose `Defs` imports Mathlib only: a `Network` derives a set of rows `M` at its leaves, `Crossover` is the model of recombination, and `R`, `F` are the least numbers of recombination nodes in a network for `M` and in a fully decomposed one.

Each theorem is stated in plain terms and proved from the libraries. `docs/reports/Gusfield2007.md` lists every correction and departure, and `palomar/Gusfield2007/` has the paper's entry for Palomar. `MainResults` imports this module with those of the other papers.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace TreeOfBlobs

/-! ## Gusfield, Bansal, Bafna, Song 2007 -/

section

open Gusfield2007

/-- **Gusfield et al. 2007, Theorem 1**, the Decomposition Theorem. In any crossover model, a nonempty `M` with no constant column has a
network in which every blob contains all and only the sites of one non-trivial connected component of the incompatibility graph, and
every compatible site is on a tree edge. The paper assumes no constant column at line 112, and that `M` is nonempty implicitly. -/
theorem gusfield_theorem1 {ι : Type*} [LinearOrder ι] [Finite ι] (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧
      N.IsFullyDecomposedFor (incompatGraph M) := Gusfield2007.theorem1 c M hM hC

/-- **Gusfield et al. 2007, Theorem 3.** For any ancestral sequence `S` and crossover model, there is a network fully decomposed for the
conflict graph `G_S(M)`, with `S` at its root and exactly `Σ_C R_{S(C)}(M(C))` recombination nodes. -/
theorem gusfield_theorem3 {ι : Type*} [LinearOrder ι] [Finite ι] (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool)
    (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.IsFullyDecomposedFor (conflictGraph S M) ∧
      N.recombCount = ∑ᶠ C : (conflictGraph S M).ConnectedComponent,
        RS c (C.supp.domRestrict S) (restrictRows C.supp M) := Gusfield2007.theorem3 c M S hM hC

/-- **Gusfield et al. 2007, Lemma 4.** For a component `C` of `G(M)`, the tree `T̄` has a node `v_C` on all the edges labelled by characters
that originate from `C`, on the 0-side of each of their splits. A reading: a trivial `C` keeps both of its columns here, which label
one edge with opposite 0-sides, so the second clause is for a non-trivial `C`, and the third is what a trivial `C` has. -/
theorem gusfield_lemma4 {ι : Type*} {M : Finset (ι → Bool)} {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W}
    {edge : SuperChar M → Sym2 W} (h : IsTBar M T φ edge) (c : (incompatGraph M).ConnectedComponent) :
    ∃ v, (∀ k : SuperChar M, k.1 = c → v ∈ edge k) ∧
      (c.supp.Nontrivial → ∀ k : SuperChar M, k.1 = c → ∀ r : M, charValue k r = true →
        ¬ SameSide T (edge k) (φ r) v) ∧
      ∀ k : SuperChar M, k.1 = c → ∃ v ∈ edge k, ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v :=
  Gusfield2007.lemma4 h c

/-- **Gusfield et al. 2007, Theorem 4, with the entry node counted**, a correction. For a fully decomposed network, the blobbed tree `T′` is
`T̄` exactly when the network is efficient with the entry node of a blob counted, and it has `RegularArcs` and the degree condition.
The repair isn't ours: Gusfield, *ReCombinatorics* (MIT Press, 2014), Section 7.3.5, states the theorem for canonical networks, a stricter class, as its Theorem 7.3.3 (read only in snippets; `docs/reports/Gusfield2007.md`, E42). -/
theorem gusfield_theorem4_entry {ι : Type*} [LinearOrder ι] {V E : Type*} [Finite V] [Finite E] {N : Network ι V E}
    {M : Finset (ι → Bool)} (hd : N.Derives M) (hf : N.IsFullyDecomposedFor (incompatGraph M)) {W : Type*} [Finite W]
    {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W} (hT : IsTBar M T φ edge) :
    (∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) ↔
      N.IsEfficientAtEntry ∧ N.RegularArcs ∧ N.DegreeCond := Gusfield2007.theorem4_entry hd hf hT

/-- **Gusfield et al. 2007, Theorem 4, exactly**, a correction. With the printed definition of efficient, `T′` is `T̄` for a fully decomposed
network exactly when it is efficient, and it has `IsTreeNormalStructural` and the degree condition. -/
theorem gusfield_theorem4_iff {ι : Type*} [LinearOrder ι] {V E : Type*} [Finite V] [Finite E] {N : Network ι V E}
    {M : Finset (ι → Bool)} (hd : N.Derives M) (hf : N.IsFullyDecomposedFor (incompatGraph M)) {W : Type*} [Finite W]
    {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W} (hT : IsTBar M T φ edge) :
    (∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) ↔
      N.IsEfficient ∧ N.IsTreeNormalStructural ∧ N.DegreeCond := Gusfield2007.theorem4_iff hd hf hT

/-- **Gusfield et al. 2007, Theorem 4, its true forms are not vacuous.** For every `M` with at least three rows, in any crossover model,
some efficient fully decomposed network has `T′` equal to `T̄`, with all the hypotheses of the true forms, and its root at a node of `T′`
of degree at least three. This is not in the paper. -/
theorem gusfield_exists_realization {ι : Type*} [LinearOrder ι] [Finite ι] {M : Finset (ι → Bool)} {W : Type*} [Finite W]
    {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W} (c : Crossover) (hC : NoConstantColumn M)
    (h3 : 3 ≤ M.card) (h : IsTBar M T φ edge) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.IsFullyDecomposedFor (incompatGraph M) ∧
      N.IsEfficient ∧ N.IsEfficientAtEntry ∧ N.IsTreeNormalStructural ∧ N.DegreeCond ∧
      (∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) ∧
      3 ≤ (N.blobbedTree.neighborSet (N.toBlobNode N.root)).ncard := Gusfield2007.exists_realization c hC h3 h

/-- **Gusfield et al. 2007, Theorem 4 is false**: the printed definition of efficient omits the entry node of a blob. On `topRows`, in any
crossover model, the theorem fails even for a network with `RegularArcs` and the degree condition, so neither convention causes it. -/
theorem gusfield_theorem4_false_top (c : Crossover) :
    ¬ Theorem4Form c topRows fun {a b} (N : Network (Fin 5) (Fin a) (Fin b)) => N.IsRegular :=
  Gusfield2007.theorem4_false_top c

/-- **Gusfield et al. 2007, Theorem 4 is false on a site-free arc**, which the paper allows. On `fiveRows`, in any crossover model, it fails
for a perfect phylogeny, with no recombination node and no blob, so the entry node doesn't account for this failure. -/
theorem gusfield_theorem4_false_siteFree (c : Crossover) :
    ¬ Theorem4Form c fiveRows fun {a b} (N : Network (Fin 5) (Fin a) (Fin b)) =>
      (∀ x, N.IsRecomb x → ¬ N.IsLeaf x) ∧ N.NoAncestralExit ∧ N.DegreeCond :=
  Gusfield2007.theorem4_false_siteFree c

/-- **Gusfield et al. 2007, Theorem 5.** If an optimal network for `M` with ancestral sequence `S` has node labels `L` with `G_S(L)` and
`G_S(M)` having the same number of components, then `M` is S-min (or S-min-1) decomposable. -/
theorem gusfield_theorem5 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hN : N.IsOptimalRooted c S M)
    (h : Nat.card (conflictGraph S N.labelSet).ConnectedComponent = Nat.card (conflictGraph S M).ConnectedComponent) :
    SMinDecomposable c S M := Gusfield2007.theorem5 hC N hN h

/-- **Gusfield et al. 2007, Theorem 6.** If a network for `M` with ancestral sequence `S`, not necessarily optimal, has every node visible
and at most one site on each edge, then `M` is S-min (or S-min-1) decomposable. -/
theorem gusfield_theorem6 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hc : N.Obeys c) (hd : N.Derives M)
    (hS : N.ancestral = S) (hv : N.AllVisible M S) (he : Function.Injective N.site) : SMinDecomposable c S M :=
  Gusfield2007.theorem6 hC N hc hd hS hv he

/-- **Gusfield et al. 2007, Theorem 7.** If every recombination node of a network for `M` with ancestral sequence `S` is a 0- or 1-component
recombination for `G_S(M)`, then there is a fully decomposed network, in the same model, with at most as many recombination nodes. -/
theorem gusfield_theorem7 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hc : N.Obeys c) (hd : N.Derives M)
    (hS : N.ancestral = S)
    (h : ∀ x, N.IsRecomb x → N.IsZeroComponent (conflictGraph S M) x ∨ N.IsOneComponent (conflictGraph S M) x) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧
      N'.IsFullyDecomposedFor (conflictGraph S M) ∧ N'.recombCount ≤ N.recombCount :=
  Gusfield2007.theorem7 hC N hc hd hS h

/-- **Gusfield et al. 2007, Theorem 8.** Given `S`, if `M` is spatially disjoint then it is S-min-1 decomposable. -/
theorem gusfield_theorem8 {ι : Type*} [LinearOrder ι] [Finite ι] {M : Finset (ι → Bool)} {S : ι → Bool} (hM : M.Nonempty)
    (hC : NoConstantColumn M) (h : SpatiallyDisjoint S M) : SMinDecomposable .single S M :=
  Gusfield2007.theorem8 hM hC h

/-- **Gusfield et al. 2007, Theorem 9.** If the node labels of a network for `M` with ancestral sequence `S` respect `G_S(M)`, then there is a
fully decomposed network, in the same model, with at most as many recombination nodes. -/
theorem gusfield_theorem9 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hc : N.Obeys c) (hd : N.Derives M)
    (hS : N.ancestral = S) (h : Respects N.labelSet S M) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧
      N'.IsFullyDecomposedFor (conflictGraph S M) ∧ N'.recombCount ≤ N.recombCount :=
  Gusfield2007.theorem9 hC N hc hd hS h

/-- **Gusfield et al. 2007, Theorem 10**, with the rooted count. If `H(M + S) = R_S(M)`, or `R¹_S(M)`, then `M` is S-min, or S-min-1, decomposable. The paper prints `R(M + S)`, and uses that symbol at lines 525 and 560 for a network with ancestral sequence `S`, which suggests a slip for `R_S(M)`. Read by the definition of line 385, the statement is false for single crossovers (`gusfield_theorem10Printed_single_false`). -/
theorem gusfield_theorem10 {ι : Type*} [LinearOrder ι] [Finite ι] {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool}
    (hM : M.Nonempty) (hC : NoConstantColumn M)
    (h : haplotypeBound (addRow M S) = RS c S M) : SMinDecomposable c S M := Gusfield2007.theorem10 hM hC h

/-- **Gusfield et al. 2007, Theorem 11.** For any positive `d` there is a set of sequences `M` with `F¹(M) - R¹(M) ≥ d`, written as a sum so
that the truncation on `ℕ` plays no part. -/
theorem gusfield_theorem11 (d : ℕ) (hd : 0 < d) :
    ∃ (m : ℕ) (M : Finset (Fin m → Bool)), M.Nonempty ∧ NoConstantColumn M ∧ R .single M + d ≤ F .single M :=
  Gusfield2007.theorem11 d hd

/-- **Gusfield et al. 2007, Corollary 2.** If every node of an optimal network for `M` with ancestral sequence `S` is visible, then `M` is S-min (or
S-min-1) decomposable. -/
theorem gusfield_corollary2 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hN : N.IsOptimalRooted c S M)
    (h : N.AllVisible M S) : SMinDecomposable c S M := Gusfield2007.corollary2 hC N hN h

/-- **Gusfield et al. 2007, Corollary 3.** When recombinations only model back or recurrent mutations, the model `pointwise`, `M` is S-min decomposable
for any `S`, and the maximum parsimony score of `M` is the sum of the scores of the components of `G_S(M)`. -/
theorem gusfield_corollary3 {ι : Type*} [LinearOrder ι] [Finite ι] (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    SMinDecomposable .pointwise S M ∧
      parsimonyScore S M = ∑ᶠ C : (conflictGraph S M).ConnectedComponent,
        parsimonyScore (C.supp.domRestrict S) (restrictRows C.supp M) := Gusfield2007.corollary3 M S hM hC

/-- **Gusfield et al. 2007, Section 5.3.1.** The unrooted Full-Decomposition Optimality Conjecture is false for single crossovers: on Figure 6,
`F¹ ≥ 4` and `R¹ ≤ 3`. -/
theorem gusfield_unrootedConjecture_single_false :
    4 ≤ F .single fig6 ∧ R .single fig6 ≤ 3 ∧ ¬ UnrootedConjecture .single := Gusfield2007.unrootedConjecture_single_false

/-- **Gusfield et al. 2007, Section 5.3.2.** The unrooted Full-Decomposition Optimality Conjecture is false for multiple crossovers: on Figure 8,
`F ≥ 4` and `R ≤ 3`. -/
theorem gusfield_unrootedConjecture_multiple_false :
    4 ≤ F .multiple fig8 ∧ R .multiple fig8 ≤ 3 ∧ ¬ UnrootedConjecture .multiple :=
  Gusfield2007.unrootedConjecture_multiple_false

/-- **Gusfield et al. 2007, Section 5.3.1.** The rooted Full-Decomposition Optimality Conjecture is false for single crossovers. -/
theorem gusfield_rootedConjecture_single_false : ¬ RootedConjecture .single := Gusfield2007.rootedConjecture_single_false

/-- **Gusfield et al. 2007, Section 5.3.** The rooted Full-Decomposition Optimality Conjecture is false for multiple crossovers. -/
theorem gusfield_rootedConjecture_multiple_false : ¬ RootedConjecture .multiple := Gusfield2007.rootedConjecture_multiple_false

/-- **Gusfield et al. 2007, Theorem 10 without an ancestral sequence**, which isn't in the paper. If `H(M) = R(M)` then `M` is min decomposable, and if `H(M) = R¹(M)` then
`M` is min-1 decomposable. -/
theorem gusfield_theorem10_unrooted {ι : Type*} [LinearOrder ι] [Finite ι] {c : Crossover} {M : Finset (ι → Bool)} (hM : M.Nonempty)
    (hC : NoConstantColumn M) (h : haplotypeBound M = R c M) : MinDecomposable c M :=
  Gusfield2007.minDecomposable_of_haplotypeBound_eq hM hC h

/-- **Gusfield et al. 2007, Theorem 10 is false for single crossovers if `R¹(M + S)` is read by the definition of line 385**, the minimum over all ancestral sequences. The paper's own use of the symbol, at lines 525 and 560, suggests a slip for `R¹_S(M)`, and with that the statement is `gusfield_theorem10`. With the literal reading, it fails on `printedRows`, fourteen rows on eight sites, with
`S = printedRoot`, one of the rows: `H(M + S) = R¹(M + S)` and `R¹_S(M) = 6`, and `M` is not S-min-1 decomposable. -/
theorem gusfield_theorem10Printed_single_false : printedRows.Nonempty ∧ NoConstantColumn printedRows ∧
    haplotypeBound (addRow printedRows printedRoot) = R .single (addRow printedRows printedRoot) ∧
    RS .single printedRoot printedRows = 6 ∧ ¬ SMinDecomposable .single printedRoot printedRows ∧
    ¬ Theorem10Printed .single printedRows printedRoot := Gusfield2007.theorem10Printed_single_false

/-- **Gusfield et al. 2007, Theorem 10, if `R(M + S)` is read by the definition of line 385, for multiple crossovers: false, given one computation.** The paper's own use of the symbol, at lines 525 and 560, suggests a slip for `R_S(M)`, and with that the statement is `gusfield_theorem10`. This theorem is conditional. Its hypothesis `printedMSearch` is a
finite computation, a search showing that two extra labels never suffice on the second component of `printedMRows`, and it is not proved here: Lean's kernel hasn't completed it. Everything else
is proved: given it, the statement with that reading fails on `printedMRows`, seventy-four rows on thirty-four sites, with `S = printedMRoot`, one of the rows. -/
theorem gusfield_theorem10Printed_multiple_false_of_search (hs : printedMSearch) : printedMRows.Nonempty ∧ NoConstantColumn printedMRows ∧
    haplotypeBound (addRow printedMRows printedMRoot) = R .multiple (addRow printedMRows printedMRoot) ∧
    ¬ SMinDecomposable .multiple printedMRoot printedMRows ∧ ¬ Theorem10Printed .multiple printedMRows printedMRoot :=
  Gusfield2007.theorem10Printed_multiple_false_of_search hs

/-- **Gusfield et al. 2007, line 329, with the entry node counted.** A fully decomposed network can be made efficient, in the printed sense and with the entry node of a blob counted,
without increasing the number of recombination nodes, with the same ancestral sequence, staying fully decomposed. -/
theorem gusfield_exists_isEfficientAtEntry {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Finite V] [Finite E] (N : Network ι V E) {c : Crossover}
    {M : Finset (ι → Bool)} {G : SimpleGraph ι} (hC : NoConstantColumn M) (hc : N.Obeys c) (hd : N.Derives M)
    (hG : G = incompatGraph M ∨ G = conflictGraph N.ancestral M) (hf : N.IsFullyDecomposedFor G) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = N.ancestral ∧ N'.IsFullyDecomposedFor G ∧
      N'.IsEfficient ∧ N'.IsEfficientAtEntry ∧ N'.recombCount ≤ N.recombCount :=
  Gusfield2007.exists_isEfficientAtEntry_of_fullyDecomposed N hC hc hd hG hf

/-- **Gusfield et al. 2007, Section 4.2: the treeness inequality fails for a blob that merges two components.** `mergedNet` has every other condition of the true form, on rows with no
incompatible pair, its one blob has the sites `0` and `1`, its treeness is `5`, and `T̄` has `4` edges. -/
theorem gusfield_treeness_merged_false (c : Crossover) {W : Type*} [Finite W] {T : SimpleGraph W} {φ : starRows → W}
    {edge : SuperChar starRows → Sym2 W} (hT : IsTBar starRows T φ edge) :
    mergedNet.Obeys c ∧ mergedNet.Derives starRows ∧ NoConstantColumn starRows ∧ mergedNet.BlobsNodeDisjoint ∧ mergedNet.RegularArcs ∧
      mergedNet.NonPendantPortsDistinct ∧ mergedNet.DegreeCond ∧
      (∃ B, mergedNet.IsBlob B ∧ mergedNet.site 0 ∈ B ∧ mergedNet.site 1 ∈ B) ∧ (∀ i j, ¬ (incompatGraph starRows).Adj i j) ∧
      mergedNet.treeness = 5 ∧ T.edgeSet.ncard = 4 :=
  Gusfield2007.treeness_merged_false c hT

/-- **Gusfield et al. 2007, line 656, with equality.** `R¹(M_d) = 3d`; the paper claims the upper bound, and Theorem 11 needs only that. -/
theorem gusfield_Md_R_eq (d : ℕ) : R .single (Md d) = 3 * d := Gusfield2007.Md_R_eq d

/-- **Gusfield et al. 2007, line 590, the conjecture of Huson and Klöpper is false**, as the thesis of the second author states it, its Conjecture 2.2. -/
theorem gusfield_conjecture22_false : ¬ Conjecture22 := Gusfield2007.conjecture22_false

end

/-! ## Gusfield, Eddhu, Langley 2004 -/

section

open Gusfield2007 GusfieldEtAl2004

/-- **Gusfield, Eddhu, Langley 2004, in the proof of Theorem 2.2.** Two sites that conflict, in any set of rows labelling nodes of a network, are together on a recombination cycle. -/
theorem galled_exists_isCycle_of_conflict {ι V E : Type*} [Finite V] (N : Network ι V E) {L : Finset (ι → Bool)} (hL : ∀ r ∈ L, ∃ v, N.label v = r) {i j : ι}
    (h : Conflict N.ancestral L i j) : ∃ Q, N.IsCycle Q ∧ N.site i ∈ Q ∧ N.site j ∈ Q :=
  GusfieldEtAl2004.exists_isCycle_of_conflict N hL h

/-- **Gusfield, Eddhu, Langley 2004, Theorem 2.2.** On a galled tree with single crossovers, two sites `i < j` conflict exactly when they are together on a gall with recombination point
between them, arranged on it in one of the three ways `W1`, `W2`, `W3`. -/
theorem galled_theorem2_2 {ι V E : Type*} [LinearOrder ι] [Finite V] {N : Network ι V E} {M : Finset (ι → Bool)} (hG : IsGalledTree N) (hc₁ : N.Obeys .single)
    (hD : N.Derives M) {i j : ι} (hij : i < j) :
    Conflict N.ancestral M i j ↔ ∃ w x p q L₀, N.IsCycleOn w x p q ∧ IsRecombPoint N x p q L₀ ∧ i ∈ L₀ ∧ j ∉ L₀ ∧
      (W1 N w p q i j ∨ W2 N w p q i j ∨ W3 N w p q i j) :=
  GusfieldEtAl2004.theorem2_2 hG hc₁ hD hij

/-- **Gusfield, Eddhu, Langley 2004, Theorem 8.3.** A reduced galled tree for `M` has the least number of recombination nodes, in its model and even with multiple crossovers at each node,
and that number is the bound by removals. -/
theorem galled_theorem8_3 {ι V E : Type*} [LinearOrder ι] [Finite ι] [Finite V] [Finite E] {N : Network ι V E} {M : Finset (ι → Bool)}
    (h : IsReducedGalledTree N (conflictGraph N.ancestral M)) (hD : N.Derives M) {c : Crossover} (hc : N.Obeys c) :
    minRemovals N.ancestral M = N.recombCount ∧ RS c N.ancestral M = N.recombCount ∧ RS .multiple N.ancestral M = N.recombCount :=
  GusfieldEtAl2004.theorem8_3 h hD hc

/-- **Gusfield et al. 2007, line 381.** A galled tree reduced for `G(M)` makes `M` min decomposable, in its model and for multiple crossovers. -/
theorem galled_line381 {ι V E : Type*} [LinearOrder ι] [Finite ι] [Finite V] [Finite E] {N : Network ι V E} {M : Finset (ι → Bool)}
    (h : IsReducedGalledTree N (incompatGraph M)) (hD : N.Derives M) {c : Crossover} (hc : N.Obeys c) :
    MinDecomposable c M ∧ MinDecomposable .multiple M :=
  GusfieldEtAl2004.line381 h hD hc

open GusfieldEtAl2004.Algorithm in
/-- **Gusfield, Eddhu, Langley 2004, the algorithm: what it returns is a reduced galled tree** (Gusfield et al. 2007, line 180). If the computable function `galledBuild` returns a table, it is
the table of a network that derives `M` with ancestral sequence `S` and single crossovers, and that is a reduced galled tree. It's a departure from the source's Sections 3 to 7 in places, recorded in its docstrings. -/
theorem galled_galledBuild_correct {m : ℕ} {S : Row m} {M : List (Row m)} (hM : M ≠ []) (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) {t : GalledOut m} (ht : galledBuild S M = some t) :
    ∃ (f : Fin m → Fin m) (ar : Fin m → Arr m) (hs : Std S M f) (har : ∀ c, isNT f c = true → ArrOK S M f c (ar c)),
      t = (gTable S M f ar, List.ofFn (siteNode S f ar)) ∧ (gNet hs har).Obeys .single ∧ (gNet hs har).Derives M.toFinset ∧
      (gNet hs har).ancestral = S ∧ IsReducedGalledTree (gNet hs har) (conflictGraph S M.toFinset) :=
  GusfieldEtAl2004.Algorithm.galledBuild_correct hM h1 ht

open GusfieldEtAl2004.Algorithm in
/-- **Gusfield, Eddhu, Langley 2004, the algorithm, "polynomial time"** (Gusfield et al. 2007, line 180). On `n` rows and `m` sites, `galledBuildOps`, which returns the value of `galledBuild`, counts at most
`233 (n + m + 1)⁶` operations. This bound isn't the source's `O(nm + n³)`. -/
theorem galled_galledBuildOps_le {m : ℕ} (S : Row m) (M : List (Row m)) : (galledBuildOps S M).2 ≤ 233 * (M.length + m + 1) ^ 6 :=
  GusfieldEtAl2004.Algorithm.galledBuildOps_le S M

end

/-! ## Myers, Griffiths 2003; Hudson, Kaplan 1985; Song, Hein 2005 -/

section

open Gusfield2007

/-- **Myers, Griffiths 2003, Algorithm 1.** The matrix that the computable function `algorithm1` constructs is the matrix of optimal values of the integer program on regions: minimize
`Σ_{l=s}^{t-1} r_l` over nonnegative integers subject to the local bounds `B`. -/
theorem myersGriffiths_algorithm1_isOptimalValue (B : ℕ → ℕ → ℕ) {S s t : ℕ} (hst : s ≤ t) (ht : t < S) :
    MyersGriffiths2003.IsOptimalValue S B s t (MyersGriffiths2003.algorithm1 B S s t) :=
  MyersGriffiths2003.algorithm1_isOptimalValue B hst ht

/-- **Myers, Griffiths 2003, the bound `R_h`.** The haplotype bounds on regions, combined by Algorithm 1, are a lower bound on `R¹(M)`. -/
theorem myersGriffiths_Rh_le_R {S : ℕ} {M : Finset (Fin S → Bool)} (hM : M.Nonempty) (hS : 0 < S) : MyersGriffiths2003.Rh M ≤ R .single M :=
  MyersGriffiths2003.Rh_le_R hM hS

/-- **Hudson, Kaplan 1985, the algorithm of Appendix 2.** The final number of intervals on the list of the computable function `hudsonKaplan` is the optimal value of the program for the matrix `D`
of incompatible pairs: the bound `R_M`. -/
theorem hudsonKaplan_isOptimalValue {S : ℕ} {d : ℕ → ℕ → Bool} (hS : 0 < S) :
    MyersGriffiths2003.IsOptimalValue S (HudsonKaplan1985.incompatBounds d) 0 (S - 1) (HudsonKaplan1985.hudsonKaplan S d) :=
  HudsonKaplan1985.hudsonKaplan_isOptimalValue hS

/-- **Song, Hein 2005, equations (3), (5).** The minimum of `L(P)`, over sequences of binary trees with a total order on their internal nodes compatible with the columns, with the distance through such
trees, is `R¹(M)`, and it is attained. The columns aren't constant, as a constant column has no compatible tree here. -/
theorem songHein_exists_orderedLength_eq_R {m : ℕ} (M : Finset (Fin m → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ P : Fin m → TimeOrderedTree M, (∀ i, SongHein2005.IsOrdered (P i)) ∧ (∀ i, (P i).CompatibleWith fun r => (r : Fin m → Bool) i) ∧
      SongHein2005.orderedLength (List.ofFn P) = R .single M :=
  SongHein2005.exists_orderedLength_eq_R M hM hC

end

end TreeOfBlobs
