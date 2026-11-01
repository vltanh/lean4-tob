module

public import AllmanEtAl2023.Lemma2
public import AllmanEtAl2023.InPassing
public import AllmanEtAl2023.CycleLemma

/-!
# Allman, Baños, Mitchell, Rhodes 2023: what the paper says in passing about blobs and the LSA

The paper gives no proofs of these, and the proofs here are ours.

* "On a network `𝒩⁺` every subset of 3 taxa determines a blob" (after Definition 8): `existsUnique_isDeterminedBy_three`.
* "Every `m`-blob with `m ≥ 3` that is below the LSA of `𝒩⁺` is determined by one or more subsets of 3 taxa": `exists_isDeterminedBy_of_isBelowLSA`.
* "Blobs above the LSA are not determined by any subset of taxa": `not_isDeterminedBy_of_isAboveLSA`.
* "An `m`-blob containing the LSA is determined by 3 taxa if `m ≥ 4`": `exists_isDeterminedBy_lsaNode`.
* "All other blobs in the chain will be 2-blobs" (after Definition 9): `IsChainOfBlobs.deg_eq_two`.
* "A general phylogenetic network will have a (possibly empty) chain of blobs as the subnetwork between its root and LSA" (after Definition 9): `exists_chain_root_lsaNode`, with
  `blobDegree_eq_two_of_isAboveLSA`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph
open scoped Classical

namespace AllmanEtAl2023.BlobStructure

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### Directed paths and cut edges -/

/-- A directed path not going through `e` is a walk avoiding `e`. -/
theorem walks_diff_of_reaches {e : E} {u w : V} (h : N.graph.Reaches u w)
    (hn : ¬ (N.graph.Reaches u (N.graph.source e) ∧ N.graph.Reaches (N.graph.target e) w)) :
    N.graph.Walks (Set.univ \ {e}) u w := by
  induction h with
  | refl => exact .refl
  | @tail b c hb hbc ih =>
    obtain ⟨f, hfs, hft⟩ := hbc
    have hfe : f ≠ e := by
      rintro rfl
      exact hn ⟨hfs ▸ hb, hft ▸ .refl⟩
    exact (ih fun h => hn ⟨h.1, h.2.tail ⟨f, hfs, hft⟩⟩).tail ⟨f, ⟨Set.mem_univ f, hfe⟩, Or.inl ⟨hfs, hft⟩⟩

/-- A directed path from the head of an arc doesn't use the arc. -/
theorem walks_diff_target (hP : N.IsPhylogenetic) (e : E) {w : V} (h : N.graph.Reaches (N.graph.target e) w) :
    N.graph.Walks (Set.univ \ {e}) (N.graph.target e) w :=
  walks_diff_of_reaches h fun h' => not_reaches_target_source hP.acyclic e h'.1

/-- A directed path to the tail of an arc doesn't use the arc. -/
theorem walks_diff_source (hP : N.IsPhylogenetic) (e : E) {u : V} (h : N.graph.Reaches u (N.graph.source e)) :
    N.graph.Walks (Set.univ \ {e}) u (N.graph.source e) :=
  walks_diff_of_reaches h fun h' => not_reaches_target_source hP.acyclic e h'.2

/-- **A cut edge leaving a blob has a taxon beyond it**: a directed path from its head to a taxon doesn't come back. -/
theorem exists_leadsTo_leaf (hP : N.IsPhylogenetic) {v : V} {e : E} (he : e ∈ incidentCuts N.graph Set.univ v) (hs : SameBlobIn N.graph Set.univ v (N.graph.source e)) :
    ∃ x, LeadsTo N.graph Set.univ v e (N.leaf x) := by
  obtain ⟨x, hx⟩ := exists_reaches_leaf hP (N.graph.target e)
  refine ⟨x, he, fun hw => he.1.2 ?_⟩
  exact (N.graph.walks_symm (hs.walks_diff he.1)).trans (hw.trans (N.graph.walks_symm (walks_diff_target hP e hx)))

/-- **A cut edge entering a blob has the root beyond it.** -/
theorem leadsTo_root (hP : N.IsPhylogenetic) {v : V} {e : E} (he : e ∈ incidentCuts N.graph Set.univ v) (ht : SameBlobIn N.graph Set.univ v (N.graph.target e)) :
    LeadsTo N.graph Set.univ v e N.root := by
  refine ⟨he, fun hw => he.1.2 ?_⟩
  exact (N.graph.walks_symm (walks_diff_source hP e (hP.root_reaches _))).trans ((N.graph.walks_symm hw).trans (ht.walks_diff he.1))

/-- **At most one cut edge enters a blob.** -/
theorem eq_of_target_sameBlobIn (hP : N.IsPhylogenetic) {v : V} {e e' : E} (he : e ∈ incidentCuts N.graph Set.univ v) (ht : SameBlobIn N.graph Set.univ v (N.graph.target e))
    (he' : e' ∈ incidentCuts N.graph Set.univ v) (ht' : SameBlobIn N.graph Set.univ v (N.graph.target e')) : e = e' :=
  (leadsTo_root hP he ht).unique (leadsTo_root hP he' ht') (N.graph_connected hP v _)

/-- No cut edge enters the blob of the root. -/
theorem not_target_sameBlobIn_of_root (hP : N.IsPhylogenetic) {v : V} {e : E} (he : e ∈ incidentCuts N.graph Set.univ v) (ht : SameBlobIn N.graph Set.univ v (N.graph.target e))
    (hr : SameBlobIn N.graph Set.univ v N.root) : False :=
  (leadsTo_root hP he ht).2 (hr.walks_diff he.1)

/-- **A cut edge entering a blob with no taxon beyond it has a stable ancestor of all taxa as its head**: every directed path from the root to a taxon crosses it. -/
theorem isStableAncestor_target (hP : N.IsPhylogenetic) {v : V} {e : E} (he : e ∈ incidentCuts N.graph Set.univ v) (ht : SameBlobIn N.graph Set.univ v (N.graph.target e))
    (hno : ∀ x, ¬ LeadsTo N.graph Set.univ v e (N.leaf x)) : N.IsStableAncestor Set.univ (N.graph.target e) := by
  rintro x - ⟨-, -, hp⟩
  have hw : N.graph.Walks (Set.univ \ {e}) v (N.leaf x) := by_contra fun h => hno x ⟨he, h⟩
  have hroot : N.graph.Walks (Set.univ \ {e}) N.root (N.leaf x) := by
    refine Relation.ReflTransGen.mono ?_ _ _ hp
    rintro a b ⟨⟨f, hfs, hft⟩, -, hb⟩
    refine ⟨f, ⟨Set.mem_univ f, ?_⟩, Or.inl ⟨hfs, hft⟩⟩
    rintro rfl
    exact hb hft.symm
  exact (leadsTo_root hP he ht).2 (hw.trans (N.graph.walks_symm hroot))

/-- An arc between two blobs is a cut edge. -/
theorem isBridge_of_blobOf_ne {G : DirectedMultigraph V E} {f : E} (h : blobOf G (G.source f) ≠ blobOf G (G.target f)) : G.underlying.IsBridge f := by
  by_contra hb
  exact h (Quotient.sound (Relation.ReflTransGen.single ⟨f, hb, Or.inl ⟨rfl, rfl⟩⟩))

/-- A directed path out of a blob leaves by a cut edge. -/
theorem exists_exit {w u : V} (h : N.graph.Reaches w u) (hne : blobOf N.graph u ≠ blobOf N.graph w) :
    ∃ e, blobOf N.graph (N.graph.source e) = blobOf N.graph w ∧ blobOf N.graph (N.graph.target e) ≠ blobOf N.graph w ∧ N.graph.Reaches w (N.graph.source e) ∧ N.graph.Reaches (N.graph.target e) u := by
  induction h with
  | refl => exact absurd rfl hne
  | @tail b c hb hbc ih =>
    obtain ⟨f, hfs, hft⟩ := hbc
    by_cases hbw : blobOf N.graph b = blobOf N.graph w
    · exact ⟨f, hfs ▸ hbw, hft ▸ hne, hfs ▸ hb, hft ▸ .refl⟩
    · obtain ⟨e, h₁, h₂, h₃, h₄⟩ := ih hbw
      exact ⟨e, h₁, h₂, h₃, h₄.tail ⟨f, hfs, hft⟩⟩

/-- A directed path into a blob enters by a cut edge. -/
theorem exists_enter {w u : V} (h : N.graph.Reaches w u) (hne : blobOf N.graph w ≠ blobOf N.graph u) :
    ∃ e, blobOf N.graph (N.graph.source e) ≠ blobOf N.graph u ∧ blobOf N.graph (N.graph.target e) = blobOf N.graph u ∧ N.graph.Reaches w (N.graph.source e) ∧ N.graph.Reaches (N.graph.target e) u := by
  induction h with
  | refl => exact absurd rfl hne
  | @tail b c hb hbc ih =>
    obtain ⟨f, hfs, hft⟩ := hbc
    by_cases hbw : blobOf N.graph b = blobOf N.graph c
    · obtain ⟨e, h₁, h₂, h₃, h₄⟩ := ih (hbw ▸ hne)
      exact ⟨e, hbw ▸ h₁, hbw ▸ h₂, h₃, h₄.tail ⟨f, hfs, hft⟩⟩
    · exact ⟨f, hfs ▸ hbw, hft ▸ rfl, hfs ▸ hb, hft ▸ .refl⟩

/-- A cut edge with an end in a blob is one of the blob's incident cut edges. -/
theorem mem_incidentCuts_of_source {v : V} {e : E} (h₁ : blobOf N.graph (N.graph.source e) = blobOf N.graph v) (h₂ : blobOf N.graph (N.graph.target e) ≠ blobOf N.graph v) :
    e ∈ incidentCuts N.graph Set.univ v :=
  ⟨isCutIn_univ_iff.mpr (isBridge_of_blobOf_ne fun h => h₂ (h ▸ h₁)), Or.inl (sameBlobIn_univ_iff.mpr h₁.symm)⟩

theorem mem_incidentCuts_of_target {v : V} {e : E} (h₁ : blobOf N.graph (N.graph.source e) ≠ blobOf N.graph v) (h₂ : blobOf N.graph (N.graph.target e) = blobOf N.graph v) :
    e ∈ incidentCuts N.graph Set.univ v :=
  ⟨isCutIn_univ_iff.mpr (isBridge_of_blobOf_ne fun h => h₁ (h ▸ h₂)), Or.inr (sameBlobIn_univ_iff.mpr h₂.symm)⟩

/-- **Three cut edges at a blob with taxa beyond them** give three taxa determining the blob. -/
theorem exists_isDeterminedBy_of_leadsTo (hP : N.IsPhylogenetic) {v : V} {A : Set E} (hA : 3 ≤ A.ncard) (h : ∀ e ∈ A, ∃ x, LeadsTo N.graph Set.univ v e (N.leaf x)) :
    ∃ S : Finset X, S.card = 3 ∧ IsDeterminedBy N.graph N.leaf (blobOf N.graph v) S := by
  have : Finite E := hP.finite_arcs
  obtain ⟨e₁, e₂, e₃, h₁, h₂, h₃, h12, h13, h23⟩ := (Set.two_lt_ncard_iff (Set.toFinite A)).mp (by omega)
  obtain ⟨x₁, hx₁⟩ := h e₁ h₁
  obtain ⟨x₂, hx₂⟩ := h e₂ h₂
  obtain ⟨x₃, hx₃⟩ := h e₃ h₃
  have hw : ∀ u, N.graph.Walks Set.univ v u := fun u => N.graph_connected hP v u
  have hne : ∀ {e e' : E} {x y : X}, e ≠ e' → LeadsTo N.graph Set.univ v e (N.leaf x) → LeadsTo N.graph Set.univ v e' (N.leaf y) → x ≠ y := by
    rintro e e' x y hee hx hy rfl
    exact hee (hx.unique hy (hw _))
  have hc : ({x₁, x₂, x₃} : Finset X).card = 3 := Finset.card_eq_three.mpr ⟨x₁, x₂, x₃, hne h12 hx₁ hx₂, hne h13 hx₁ hx₃, hne h23 hx₂ hx₃, rfl⟩
  refine ⟨{x₁, x₂, x₃}, hc, isDeterminedBy_blobOf_iff.mpr ⟨hc.ge, fun s hs t ht hst => ?_⟩⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
  rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hst
    | exact not_walks_of_leadsTo hx₁ hx₂ h12 (hw _)
    | exact not_walks_of_leadsTo hx₁ hx₃ h13 (hw _)
    | exact not_walks_of_leadsTo hx₂ hx₃ h23 (hw _)
    | exact not_walks_of_leadsTo hx₂ hx₁ h12.symm (hw _)
    | exact not_walks_of_leadsTo hx₃ hx₁ h13.symm (hw _)
    | exact not_walks_of_leadsTo hx₃ hx₂ h23.symm (hw _)

/-- **An `m`-blob with `m ≥ 4` is determined by three taxa**: at most one of its cut edges enters it, none if the root is in it, and those leaving it have taxa beyond them. -/
theorem exists_isDeterminedBy_of_four (hP : N.IsPhylogenetic) {v : V} (hm : 4 ≤ blobDegree N (blobOf N.graph v)) :
    ∃ S : Finset X, S.card = 3 ∧ IsDeterminedBy N.graph N.leaf (blobOf N.graph v) S := by
  have : Finite E := hP.finite_arcs
  let In : Set E := {e | e ∈ incidentCuts N.graph Set.univ v ∧ SameBlobIn N.graph Set.univ v (N.graph.target e)}
  have hA : 3 ≤ (incidentCuts N.graph Set.univ v \ In).ncard := by
    have hle : (incidentCuts N.graph Set.univ v).ncard - In.ncard ≤ (incidentCuts N.graph Set.univ v \ In).ncard := Set.le_ncard_sdiff _ _
    have hd : cutDegree N.graph (blobOf N.graph v) = (incidentCuts N.graph Set.univ v).ncard := by rw [cutDegree, incidentCutEdges_blobOf]
    by_cases hr : blobOf N.graph N.root = blobOf N.graph v
    · have hIn : In = ∅ := Set.eq_empty_of_forall_notMem fun e he =>
        not_target_sameBlobIn_of_root hP he.1 he.2 (sameBlobIn_univ_iff.mpr hr.symm)
      simp only [blobDegree, hr, ↓reduceIte] at hm
      rw [hIn, Set.sdiff_empty] at *
      simp only [hd] at hm
      omega
    · have hIn : In.ncard ≤ 1 := (Set.ncard_le_one (Set.toFinite _)).mpr fun e he e' he' =>
        eq_of_target_sameBlobIn hP he.1 he.2 he'.1 he'.2
      simp only [blobDegree, hr, ↓reduceIte, hd] at hm
      omega
  refine exists_isDeterminedBy_of_leadsTo hP hA fun e he => ?_
  rcases he.1.2 with hs | ht
  · exact exists_leadsTo_leaf hP he.1 hs
  · exact absurd ⟨he.1, ht⟩ he.2

/-! ### The LSA -/

section LSA

variable (hN : IsBinaryNetwork N) (hX : Nontrivial X)

include hN hX in
/-- Every node is below the LSA, or strictly above it. -/
theorem reaches_lsaNode_or (v : V) : N.graph.Reaches (lsaNode hN hX) v ∨ (N.graph.Reaches v (lsaNode hN hX) ∧ v ≠ lsaNode hN hX) := by
  by_cases h : N.graph.Reaches v (lsaNode hN hX) ∧ v ≠ lsaNode hN hX
  · exact Or.inr h
  · exact Or.inl ((mem_belowVertices_univ_iff hN hX v).mpr h).1

include hN hX in
/-- The arcs entering what is below the LSA enter the LSA. -/
theorem target_eq_lsaNode {f : E} (hs : ¬ N.graph.Reaches (lsaNode hN hX) (N.graph.source f)) (ht : N.graph.Reaches (lsaNode hN hX) (N.graph.target f)) :
    N.graph.target f = lsaNode hN hX := by
  have hf : ¬ f ∈ N.belowArcs (lsaNode hN hX) Set.univ := fun h => hs h.1
  rw [mem_belowArcs_univ_iff, not_not] at hf
  exact eq_of_reaches_of_reaches hN.isPhylogenetic.acyclic hf ht

/-- The LSA has two children. -/
theorem two_le_outdegree_lsaNode : 2 ≤ N.graph.outdegree (lsaNode hN hX) := by
  have : Finite E := hN.isPhylogenetic.finite_arcs
  have h := lsaPlus_outdegree_root hN hX
  rw [← h]
  refine Set.ncard_le_ncard_of_injOn Subtype.val (fun e he => congrArg Subtype.val he) (fun _ _ _ _ h => Subtype.ext h) (Set.toFinite _)

include hN hX in
/-- At most one arc enters the LSA. -/
theorem eq_of_target_eq_lsaNode {f f' : E} (hf : N.graph.target f = lsaNode hN hX) (hf' : N.graph.target f' = lsaNode hN hX) : f = f' := by
  have hP := hN.isPhylogenetic
  have : Finite E := hP.finite_arcs
  have h2 := two_le_outdegree_lsaNode hN hX
  have hne : lsaNode hN hX ≠ N.root := hf ▸ target_ne_root hP f
  have h3 := hN.isBinary.2 _ hne (by omega)
  have hle : N.graph.indegree (lsaNode hN hX) ≤ 1 := by omega
  exact (Set.ncard_le_one (Set.toFinite _)).mp hle f hf f' hf'

include hN hX in
/-- **The arc entering the LSA is a cut edge**: it is the only arc entering what is below the LSA. -/
theorem crosses_reached_iff {e₀ : E} (he₀ : N.graph.target e₀ = lsaNode hN hX) (f : E) : N.graph.Crosses f {v | N.graph.Reaches (lsaNode hN hX) v} ↔ f = e₀ := by
  have hP := hN.isPhylogenetic
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact absurd (Relation.ReflTransGen.tail h₁ ⟨f, rfl, rfl⟩) h₂
    · exact eq_of_target_eq_lsaNode hN hX (target_eq_lsaNode hN hX h₂ h₁) he₀
  · rintro rfl
    refine Or.inr ⟨he₀ ▸ .refl, fun h => not_reaches_target_source hP.acyclic f (he₀ ▸ h)⟩

include hN hX in
/-- **Blobs do not straddle the LSA**: a blob is below the LSA as a whole, or not at all. -/
theorem reaches_lsaNode_iff_of_blobOf_eq {u w : V} (h : blobOf N.graph u = blobOf N.graph w) :
    N.graph.Reaches (lsaNode hN hX) u ↔ N.graph.Reaches (lsaNode hN hX) w := by
  have hP := hN.isPhylogenetic
  rcases Relation.ReflTransGen.cases_tail (hP.root_reaches (lsaNode hN hX)) with hr | ⟨b, -, f, -, hf⟩
  · rw [hr]
    exact ⟨fun _ => hP.root_reaches _, fun _ => hP.root_reaches _⟩
  · exact N.graph.mem_iff_of_blobSetoid (crosses_reached_iff hN hX hf) h

/-- A blob is *above the LSA*: it has a node strictly above the LSA. By `reaches_lsaNode_iff_of_blobOf_eq`, then all its nodes are. -/
def IsAboveLSA (b : N.graph.BlobVertex) : Prop :=
  ∃ v, blobOf N.graph v = b ∧ N.graph.Reaches v (lsaNode hN hX) ∧ v ≠ lsaNode hN hX

/-- A blob is *below the LSA*: it has a node below the LSA, and doesn't contain the LSA. -/
def IsBelowLSA (b : N.graph.BlobVertex) : Prop :=
  blobOf N.graph (lsaNode hN hX) ≠ b ∧ ∃ v, blobOf N.graph v = b ∧ N.graph.Reaches (lsaNode hN hX) v

include hN hX in
/-- A strictly-above node is not below the LSA. -/
theorem not_reaches_of_above {v : V} (h : N.graph.Reaches v (lsaNode hN hX) ∧ v ≠ lsaNode hN hX) : ¬ N.graph.Reaches (lsaNode hN hX) v :=
  fun h' => h.2 (eq_of_reaches_of_reaches hN.isPhylogenetic.acyclic h.1 h')

/-- **"Every `m`-blob with `m ≥ 3` that is below the LSA of `𝒩⁺` is determined by one or more subsets of 3 taxa"** (`a:claim:det-below`, after Definition 8). -/
theorem exists_isDeterminedBy_of_isBelowLSA {b : N.graph.BlobVertex} (hb : IsBelowLSA hN hX b) (hm : 3 ≤ blobDegree N b) :
    ∃ S : Finset X, S.card = 3 ∧ IsDeterminedBy N.graph N.leaf b S := by
  have hP := hN.isPhylogenetic
  have : Finite E := hP.finite_arcs
  obtain ⟨hL, v, rfl, hv⟩ := hb
  -- the root is not in the blob
  have hr : blobOf N.graph N.root ≠ blobOf N.graph v := by
    intro hr
    have hreach := (reaches_lsaNode_iff_of_blobOf_eq hN hX hr).mpr hv
    have := eq_of_reaches_of_reaches hP.acyclic hreach (hP.root_reaches _)
    exact hL (by rw [this, hr])
  simp only [blobDegree, hr, ↓reduceIte, cutDegree, incidentCutEdges_blobOf] at hm
  refine exists_isDeterminedBy_of_leadsTo hP hm fun e he => ?_
  rcases he.2 with hs | ht
  · exact exists_leadsTo_leaf hP he hs
  · by_contra hno
    push Not at hno
    have hstable := isStableAncestor_target hP he ht hno
    have h₁ := (lsa_spec hP Set.univ Set.univ_nonempty).2 _ hstable
    have hb := sameBlobIn_univ_iff.mp ht
    have h₂ := (reaches_lsaNode_iff_of_blobOf_eq hN hX hb).mp hv
    have hEq := eq_of_reaches_of_reaches hP.acyclic h₁ h₂
    exact hL (by rw [hb, hEq]; rfl)

/-- **"An `m`-blob containing the LSA is determined by 3 taxa if `m ≥ 4`"** (`a:claim:det-lsa`, after Definition 8). -/
theorem exists_isDeterminedBy_lsaNode (hm : 4 ≤ blobDegree N (blobOf N.graph (lsaNode hN hX))) :
    ∃ S : Finset X, S.card = 3 ∧ IsDeterminedBy N.graph N.leaf (blobOf N.graph (lsaNode hN hX)) S :=
  exists_isDeterminedBy_of_four hN.isPhylogenetic hm

/-- **"Blobs above the LSA are not determined by any subset of taxa"** (`a:claim:det-above`, after Definition 8): the arcs below the LSA keep all the taxa together when the cut edges of a blob above it are deleted. -/
theorem not_isDeterminedBy_of_isAboveLSA {b : N.graph.BlobVertex} (hb : IsAboveLSA hN hX b) (S : Finset X) : ¬ IsDeterminedBy N.graph N.leaf b S := by
  have hP := hN.isPhylogenetic
  obtain ⟨v, rfl, hv⟩ := hb
  rintro h
  obtain ⟨h3, hdet⟩ := isDeterminedBy_blobOf_iff.mp h
  have hv' := not_reaches_of_above hN hX hv
  have hwalk : ∀ w, N.graph.Reaches (lsaNode hN hX) w → N.graph.Walks (Set.univ \ incidentCuts N.graph Set.univ v) (lsaNode hN hX) w := by
    intro w hw
    induction hw with
    | refl => exact .refl
    | @tail a c ha hac ih =>
      obtain ⟨f, hfs, hft⟩ := hac
      refine ih.tail ⟨f, ⟨Set.mem_univ f, fun hf => ?_⟩, Or.inl ⟨hfs, hft⟩⟩
      rcases hf.2 with hb | hb
      · exact hv' ((reaches_lsaNode_iff_of_blobOf_eq hN hX (sameBlobIn_univ_iff.mp hb)).mpr (hfs ▸ ha))
      · exact hv' ((reaches_lsaNode_iff_of_blobOf_eq hN hX (sameBlobIn_univ_iff.mp hb)).mpr (hft ▸ ha.tail ⟨f, hfs, hft⟩))
  obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hst' := (lsa_spec hP Set.univ Set.univ_nonempty).1
  exact hdet s hs t ht hst ((N.graph.walks_symm (hwalk _ (hst'.reaches_leaf hP (Set.mem_univ s)))).trans (hwalk _ (hst'.reaches_leaf hP (Set.mem_univ t))))

end LSA

/-- **"On a network `𝒩⁺` every subset of 3 taxa determines a blob"** (`a:claim:three-taxa`, after Definition 8), and only one. -/
theorem existsUnique_isDeterminedBy_three (hN : IsBinaryNetwork N) {S : Finset X} (h3 : S.card = 3) : ∃! b : N.graph.BlobVertex, IsDeterminedBy N.graph N.leaf b S := by
  have hP := hN.isPhylogenetic
  have hF : N.ancestralArcs Set.univ = Set.univ := Set.eq_univ_of_forall fun e => mem_ancestralVertices_univ hN _
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h3
  obtain ⟨v, -, hv⟩ := exists_determines_three (Z := Set.univ) hP (Set.mem_univ a) (Set.mem_univ b) (Set.mem_univ c) hab hac hbc
  rw [hF] at hv
  refine ⟨blobOf N.graph v, isDeterminedBy_blobOf_iff.mpr ⟨h3.ge, hv⟩, fun b' hb' => ?_⟩
  induction b' using Quotient.inductionOn with
  | h w =>
    change IsDeterminedBy N.graph N.leaf (blobOf N.graph w) _ at hb'
    change blobOf N.graph w = _
    by_contra hne
    have hdet := (isDeterminedBy_blobOf_iff.mp hb').2
    have hconn := N.graph_connected hP
    obtain ⟨e, he⟩ := (exists_leadsTo (hconn v w)).resolve_left fun h => hne (sameBlobIn_univ_iff.mp h).symm
    -- at most one of the three taxa on each side of `e`
    have hT₁ : OnlyCrosses N.graph Set.univ e (far N.graph Set.univ e v) := onlyCrosses_far
    have hT₂ : OnlyCrosses N.graph Set.univ e (far N.graph Set.univ e v)ᶜ := hT₁.compl
    have h₁ : ∀ s ∈ ({a, b, c} : Finset X), ∀ t ∈ ({a, b, c} : Finset X), N.leaf s ∈ far N.graph Set.univ e v → N.leaf t ∈ far N.graph Set.univ e v → s = t := fun s hs t ht hsT htT =>
      hv.eq_of_mem_side hT₁ not_mem_far_self hs ht (hconn _ _) (hconn _ _) hsT htT
    have h₂ : ∀ s ∈ ({a, b, c} : Finset X), ∀ t ∈ ({a, b, c} : Finset X), N.leaf s ∉ far N.graph Set.univ e v → N.leaf t ∉ far N.graph Set.univ e v → s = t := fun s hs t ht hsT htT =>
      hdet.eq_of_mem_side hT₂ (not_not.mpr he.2) hs ht (hconn _ _) (hconn _ _) hsT htT
    have ha := Finset.mem_insert_self a {b, c}
    have hb : b ∈ ({a, b, c} : Finset X) := by simp
    have hc : c ∈ ({a, b, c} : Finset X) := by simp
    by_cases h_a : N.leaf a ∈ far N.graph Set.univ e v <;> by_cases h_b : N.leaf b ∈ far N.graph Set.univ e v <;> by_cases h_c : N.leaf c ∈ far N.graph Set.univ e v
    · exact hab (h₁ a ha b hb h_a h_b)
    · exact hab (h₁ a ha b hb h_a h_b)
    · exact hac (h₁ a ha c hc h_a h_c)
    · exact hbc (h₂ b hb c hc h_b h_c)
    · exact hbc (h₁ b hb c hc h_b h_c)
    · exact hac (h₂ a ha c hc h_a h_c)
    · exact hab (h₂ a ha b hb h_a h_b)
    · exact hab (h₂ a ha b hb h_a h_b)


/-! ### Chains of blobs -/

section Chain

/-- **"A chain of blobs will have 1- or 2-blobs at its ends, but all other blobs in the chain will be 2-blobs"** (`a:claim:chain-shape`, after Definition 9): a blob inside the chain has an
edge to each of its two neighbours. The degree `deg` is of the kind of network, `blobDegree` or `cutDegree`, and at least the number of incident cut edges. -/
theorem IsChainOfBlobs.deg_eq_two {W F : Type*} [Finite F] {G : DirectedMultigraph W F} {deg : G.BlobVertex → ℕ} (hdeg : ∀ b, cutDegree G b ≤ deg b) {c : List G.BlobVertex}
    (hc : IsChainOfBlobs G deg c) {l₁ l₂ : List G.BlobVertex} {a b d : G.BlobVertex} (h : c = l₁ ++ a :: b :: d :: l₂) : deg b = 2 := by
  subst h
  obtain ⟨hnd, hdg, hch⟩ := hc
  have hinf : (a :: b :: d :: []) <:+: (l₁ ++ a :: b :: d :: l₂) := ⟨l₁, l₂, by simp⟩
  have hnd' := hnd.sublist hinf.sublist
  have hch' := hch.infix hinf
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hab, had⟩, hbd⟩ := hnd'
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch'
  obtain ⟨⟨e, he, hea, he₁⟩, ⟨f, hf, hf₁, hfd⟩⟩ := hch'
  have hne : e ≠ f := by
    rintro rfl
    have hval : ∀ {x : G.BlobVertex}, IsIncidentToBlob G e x → blobOf G (G.source e) = x ∨ blobOf G (G.target e) = x := by
      rintro x (⟨h, -⟩ | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr h
    rcases hval hea with rfl | rfl <;> rcases hval he₁ with rfl | rfl <;> rcases hval hfd with h | h
    all_goals first
      | exact hab rfl
      | exact had h
      | exact hbd h
  have h2 : 1 < cutDegree G b := (Set.one_lt_ncard_iff (Set.toFinite _)).mpr ⟨e, f, ⟨he, he₁⟩, ⟨hf, hf₁⟩, hne⟩
  have h1 := hdeg b
  rcases hdg b (by simp) with h' | h' <;> omega

variable (hN : IsBinaryNetwork N) (hX : Nontrivial X)

include hN hX in
/-- **A blob above the LSA has one cut edge leaving it**: it has taxa beyond it, so the LSA, and they are all beyond it. -/
theorem leadsTo_lsaNode {v : V} (hv : ¬ N.graph.Reaches (lsaNode hN hX) v) {e : E} (he : e ∈ incidentCuts N.graph Set.univ v) (hs : SameBlobIn N.graph Set.univ v (N.graph.source e)) :
    LeadsTo N.graph Set.univ v e (lsaNode hN hX) := by
  have hP := hN.isPhylogenetic
  obtain ⟨x, hx⟩ := exists_leadsTo_leaf hP he hs
  refine ⟨he, fun hw => hx.2 (hw.trans ?_)⟩
  have hst := (lsa_spec hP Set.univ Set.univ_nonempty).1
  refine walks_diff_of_reaches (hst.reaches_leaf hP (Set.mem_univ x)) fun h => hv ?_
  exact (reaches_lsaNode_iff_of_blobOf_eq hN hX (sameBlobIn_univ_iff.mp hs)).mpr h.1

include hN hX in
/-- At most one cut edge leaves a blob above the LSA. -/
theorem eq_of_source_sameBlobIn {v : V} (hv : ¬ N.graph.Reaches (lsaNode hN hX) v) {e e' : E} (he : e ∈ incidentCuts N.graph Set.univ v) (hs : SameBlobIn N.graph Set.univ v (N.graph.source e))
    (he' : e' ∈ incidentCuts N.graph Set.univ v) (hs' : SameBlobIn N.graph Set.univ v (N.graph.source e')) : e = e' :=
  (leadsTo_lsaNode hN hX hv he hs).unique (leadsTo_lsaNode hN hX hv he' hs') (N.graph_connected hN.isPhylogenetic v _)

include hN hX in
/-- A blob above the LSA is not the blob of the LSA. -/
theorem blobOf_ne_lsaNode {v : V} (hv : ¬ N.graph.Reaches (lsaNode hN hX) v) : blobOf N.graph (lsaNode hN hX) ≠ blobOf N.graph v := fun h =>
  hv ((reaches_lsaNode_iff_of_blobOf_eq hN hX h).mp .refl)

include hN hX in
/-- **A blob strictly above the LSA has a cut edge leaving it.** -/
theorem exists_exit_of_above {v : V} (hv : ¬ N.graph.Reaches (lsaNode hN hX) v) :
    ∃ e, blobOf N.graph (N.graph.source e) = blobOf N.graph v ∧ blobOf N.graph (N.graph.target e) ≠ blobOf N.graph v ∧ N.graph.Reaches v (N.graph.source e) ∧ N.graph.Reaches (N.graph.target e) (lsaNode hN hX) := by
  have hr := (reaches_lsaNode_or hN hX v).resolve_left hv
  exact exists_exit hr.1 (blobOf_ne_lsaNode hN hX hv)

/-- **Every blob above the LSA is a 2-blob** (`a:claim:chain-above`, after Definition 9): one cut edge leaves it, and one enters it, unless the root is in it, which counts as one in Definition 7. -/
theorem blobDegree_eq_two_of_isAboveLSA {b : N.graph.BlobVertex} (hb : IsAboveLSA hN hX b) : blobDegree N b = 2 := by
  have hP := hN.isPhylogenetic
  have : Finite E := hP.finite_arcs
  obtain ⟨v, rfl, hv⟩ := hb
  have hv' := not_reaches_of_above hN hX hv
  obtain ⟨o, ho₁, ho₂, -, -⟩ := exists_exit_of_above hN hX hv'
  have hoI := mem_incidentCuts_of_source (N := N) ho₁ ho₂
  have hos : SameBlobIn N.graph Set.univ v (N.graph.source o) := sameBlobIn_univ_iff.mpr ho₁.symm
  rw [blobDegree, cutDegree, incidentCutEdges_blobOf]
  by_cases hr : blobOf N.graph N.root = blobOf N.graph v
  · -- only the edge leaving
    have hset : incidentCuts N.graph Set.univ v = {o} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨hoI, fun e he => ?_⟩
      rcases he.2 with hs | ht
      · exact eq_of_source_sameBlobIn hN hX hv' he hs hoI hos
      · exact (not_target_sameBlobIn_of_root hP he ht (sameBlobIn_univ_iff.mpr hr.symm)).elim
    simp only [hr, ↓reduceIte, hset, Set.ncard_singleton]
  · -- the edge entering, and the edge leaving
    obtain ⟨i, hi₁, hi₂, -, -⟩ := exists_enter (hP.root_reaches v) hr
    have hiI := mem_incidentCuts_of_target (N := N) hi₁ hi₂
    have hit : SameBlobIn N.graph Set.univ v (N.graph.target i) := sameBlobIn_univ_iff.mpr hi₂.symm
    have hne : i ≠ o := by
      rintro rfl
      exact ho₂ hi₂
    have hset : incidentCuts N.graph Set.univ v = {i, o} := by
      ext e
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro he
        rcases he.2 with hs | ht
        · exact Or.inr (eq_of_source_sameBlobIn hN hX hv' he hs hoI hos)
        · exact Or.inl (eq_of_target_sameBlobIn hP he ht hiI hit)
      · rintro (rfl | rfl)
        · exact hiI
        · exact hoI
    simp only [hr, ↓reduceIte, hset, Set.ncard_pair hne]

/-- The blobs above the LSA that a node reaches. -/
def IsAboveFrom (w : V) (b : N.graph.BlobVertex) : Prop :=
  ∃ u, blobOf N.graph u = b ∧ ¬ N.graph.Reaches (lsaNode hN hX) u ∧ N.graph.Reaches w u

/-- **The blobs above the LSA that a node reaches, in order.** -/
theorem exists_chain_from (w : V) :
    ∃ c : List N.graph.BlobVertex, c.Nodup ∧ c.IsChain (fun b b' => ∃ e, N.graph.underlying.IsBridge e ∧ IsIncidentToBlob N.graph e b ∧ IsIncidentToBlob N.graph e b') ∧
      (∀ b, b ∈ c ↔ IsAboveFrom hN hX w b) ∧ (¬ N.graph.Reaches (lsaNode hN hX) w → c.head? = some (blobOf N.graph w)) ∧ (N.graph.Reaches (lsaNode hN hX) w → c = []) ∧
      ∀ l, c.getLast? = some l → ∃ e, N.graph.underlying.IsBridge e ∧ IsIncidentToBlob N.graph e l ∧ N.graph.target e = lsaNode hN hX := by
  have hP := hN.isPhylogenetic
  have : Finite V := hP.finite_vertices
  let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj b a
  have : IsTrans V r := ⟨fun _ _ _ h h' => h'.trans h⟩
  have : Std.Irrefl r := ⟨fun a h => hP.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  induction w using hwf.induction with
  | _ w ih =>
    by_cases hw : N.graph.Reaches (lsaNode hN hX) w
    · -- nothing above the LSA is below `w`
      refine ⟨[], List.nodup_nil, List.isChain_nil, fun b => ?_, fun h => absurd hw h, fun _ => rfl, fun l hl => by simp at hl⟩
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨u, -, hu, hwu⟩
      exact hu (hw.trans hwu)
    · obtain ⟨o, ho₁, ho₂, ho₃, ho₄⟩ := exists_exit_of_above hN hX hw
      have hoI := mem_incidentCuts_of_source (N := N) ho₁ ho₂
      have hos : SameBlobIn N.graph Set.univ w (N.graph.source o) := sameBlobIn_univ_iff.mpr ho₁.symm
      have hbr : N.graph.underlying.IsBridge o := isCutIn_univ_iff.mp hoI.1
      have hlt : r (N.graph.target o) w := Relation.TransGen.tail' ho₃ ⟨o, rfl, rfl⟩
      obtain ⟨c', hnd, hch, hmem, hhead, hnil, hlast⟩ := ih _ hlt
      have hreach : N.graph.Reaches w (N.graph.target o) := ho₃.tail ⟨o, rfl, rfl⟩
      have hincS : IsIncidentToBlob N.graph o (blobOf N.graph w) := Or.inl ⟨ho₁, ho₂⟩
      have hincT : IsIncidentToBlob N.graph o (blobOf N.graph (N.graph.target o)) := Or.inr ⟨rfl, fun h => ho₂ (h.symm.trans ho₁)⟩
      refine ⟨blobOf N.graph w :: c', ?_, ?_, fun b => ?_, fun _ => rfl, fun h => absurd h hw, fun l hl => ?_⟩
      · refine List.nodup_cons.mpr ⟨fun hin => ?_, hnd⟩
        obtain ⟨u, hu, -, htu⟩ := (hmem _).mp hin
        refine hoI.1.2 ?_
        have h₁ : N.graph.Walks (Set.univ \ {o}) (N.graph.target o) u := walks_diff_target hP o htu
        have h₂ : SameBlobIn N.graph Set.univ u (N.graph.source o) := sameBlobIn_univ_iff.mpr (hu.trans ho₁.symm)
        exact N.graph.walks_symm (h₁.trans (h₂.walks_diff hoI.1))
      · rcases hc : c' with _ | ⟨d, c''⟩
        · exact List.isChain_singleton _
        · refine List.isChain_cons_cons.mpr ⟨?_, hc ▸ hch⟩
          by_cases htr : N.graph.Reaches (lsaNode hN hX) (N.graph.target o)
          · have := hnil htr
            simp [hc] at this
          · have := hhead htr
            rw [hc] at this
            simp only [List.head?_cons, Option.some.injEq] at this
            subst this
            exact ⟨o, hbr, hincS, hincT⟩
      · rw [List.mem_cons, hmem]
        constructor
        · rintro (rfl | ⟨u, hu, hul, htu⟩)
          · exact ⟨w, rfl, hw, .refl⟩
          · exact ⟨u, hu, hul, hreach.trans htu⟩
        · rintro ⟨u, rfl, hul, hwu⟩
          by_cases hb : blobOf N.graph u = blobOf N.graph w
          · exact Or.inl hb
          · obtain ⟨e, he₁, he₂, -, he₄⟩ := exists_exit hwu hb
            have heI := mem_incidentCuts_of_source (N := N) he₁ he₂
            have heq := eq_of_source_sameBlobIn hN hX hw heI (sameBlobIn_univ_iff.mpr he₁.symm) hoI hos
            subst heq
            exact Or.inr ⟨u, rfl, hul, he₄⟩
      · rcases hc : c' with _ | ⟨d, c''⟩
        · -- the last blob before the LSA
          simp only [hc, List.getLast?_singleton, Option.some.injEq] at hl
          subst hl
          refine ⟨o, hbr, hincS, ?_⟩
          by_cases htr : N.graph.Reaches (lsaNode hN hX) (N.graph.target o)
          · refine target_eq_lsaNode hN hX (fun hs => hw ?_) htr
            exact (reaches_lsaNode_iff_of_blobOf_eq hN hX ho₁).mp hs
          · have := hhead htr
            simp [hc] at this
        · refine hlast l ?_
          rw [hc]
          rw [hc, List.getLast?_cons_cons] at hl
          exact hl

/-- **"A general phylogenetic network will have a (possibly empty) chain of blobs as the subnetwork between its root and LSA"** (`a:claim:chain-root-lsa`, after Definition 9): the blobs above the
LSA, in order from the blob of the root, to the blob joined to the LSA by a cut edge. It is empty when the LSA is the root. -/
theorem exists_chain_root_lsaNode :
    ∃ c : List N.graph.BlobVertex, IsChainOfBlobs N.graph (blobDegree N) c ∧ (∀ b, b ∈ c ↔ IsAboveLSA hN hX b) ∧ (c = [] ↔ lsaNode hN hX = N.root) ∧
      (lsaNode hN hX ≠ N.root → c.head? = some (blobOf N.graph N.root)) ∧
      ∀ l, c.getLast? = some l → ∃ e, N.graph.underlying.IsBridge e ∧ IsIncidentToBlob N.graph e l ∧ N.graph.target e = lsaNode hN hX := by
  have hP := hN.isPhylogenetic
  obtain ⟨c, hnd, hch, hmem, hhead, hnil, hlast⟩ := exists_chain_from hN hX N.root
  have hiff : ∀ b, b ∈ c ↔ IsAboveLSA hN hX b := fun b => by
    rw [hmem]
    constructor
    · rintro ⟨u, hu, hul, -⟩
      obtain ⟨h₁, h₂⟩ := (reaches_lsaNode_or hN hX u).resolve_left hul
      exact ⟨u, hu, h₁, h₂⟩
    · rintro ⟨u, hu, hul⟩
      exact ⟨u, hu, not_reaches_of_above hN hX hul, hP.root_reaches u⟩
  have hroot : lsaNode hN hX = N.root ↔ N.graph.Reaches (lsaNode hN hX) N.root :=
    ⟨fun h => h ▸ .refl, fun h => eq_of_reaches_of_reaches hP.acyclic h (hP.root_reaches _)⟩
  refine ⟨c, ⟨hnd, fun b hb => Or.inr (blobDegree_eq_two_of_isAboveLSA hN hX ((hiff b).mp hb)), hch⟩, hiff, ?_, fun hne => hhead fun h => hne (hroot.mpr h), hlast⟩
  constructor
  · intro h
    by_contra hne
    have := hhead fun hr => hne (hroot.mpr hr)
    simp [h] at this
  · exact fun h => hnil (hroot.mp h)

end Chain

end AllmanEtAl2023.BlobStructure
