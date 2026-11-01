module

public import AllmanEtAl2023.TreeIso
public import AllmanEtAl2023.Bridges
public import AllmanEtAl2023.Reduction
public import AllmanEtAl2023.DeletedNetwork
public import Phylogenetics.NMSC.DisplayedTreeModel

/-!
# Allman, Baños, Mitchell, Rhodes 2023: what the paper says in passing

Statements of Section 2 that the paper doesn't prove, or proves in a sentence.

* "Hybrid edges ... are in blobs" (after Definition 11): `not_isBridge_of_isHybridEdge`.
* "If it does it must be an `m`-blob with `m ≥ k`" (after Definition 8): `card_le_blobDegree`.
* Equivalent condition (1) after Definition 12: `isBlobQuartet_iff_deletion`. It needs a binary network.
* "`T_rd(𝒩⁻)` can also be obtained from the rooted one" (after Definition 11): `trdFromRooted`, `isIso_trdFromRooted`.
* "`T_rd(𝒩⁻)`" is a tree (Definition 11): `Bridges.isTree_Trd`.
* "Equivalently, every tree displayed on the 4-taxon network has the same resolved quartet topology" (after Definition 13): `isTreelike_iff_forall_displays`, `isTreeQuartet_iff_forall_displays`. The trees
  displayed are the library's `displayedSides`, one for each choice of parents.
* "`𝒩⁻` may have any number of 2-blobs" (Lemma 1): `exists_network_star`, `exists_network_resolved`, in `AllmanEtAl2023.TwoBlobs`.
* "The distance between blobs cannot be identified" (Section 5): `blobDistance_not_identifiable`, in `AllmanEtAl2023.BlobDistance`.
* The mixture formula in the proof of Theorem 1 (b), `CF(𝒩⁺) = γ₁ CF(𝒩₂⁺) + γ₂ CF(𝒩₁⁺)`: `cf_mixture`, on the networks `deleted`. It is `nmscCF_withPair_mixture`, which the proof of Theorem 1 uses.
* `CF_abcd = α CF₁ + (1 - α) CF₂` in the proof of Proposition 1: `NetworkNk.nmscCF_eq_mixture`, in `AllmanEtAl2023.NetworkNkMixture`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph
open scoped Classical

namespace AllmanEtAl2023.InPassing

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### A hybrid edge is not a cut edge -/

/-- **"The only directed edges in `𝒩⁻` are hybrid edges, which are in blobs"** (`a:claim:hybrid-not-cut`, after Definition 11): a hybrid edge is never a cut edge. The root reaches its two parents, and the path to the other parent
doesn't use it, since the network is acyclic. -/
theorem not_isBridge_of_isHybridEdge (hN : IsBinaryNetwork N) {e : E} (he : IsHybridEdge N e) : ¬ N.graph.underlying.IsBridge e := by
  have hP := hN.isPhylogenetic
  rw [N.graph.isBridge_iff_not_walks_delete, not_not]
  obtain ⟨f, f', hne, hpar⟩ := IsHybridNode.exists_parents he
  obtain ⟨g, hge, hg⟩ : ∃ g, g ≠ e ∧ N.graph.target g = N.graph.target e := by
    rcases (hpar e).mp rfl with rfl | rfl
    · exact ⟨f', hne.symm, (hpar f').mpr (Or.inr rfl)⟩
    · exact ⟨f, hne, (hpar f).mpr (Or.inl rfl)⟩
  have h₁ : N.AvoidingReach e N.root (N.graph.source e) := avoidingReach_of_reaches_source hP.acyclic (hP.root_reaches _) .refl
  have h₂ : N.AvoidingReach e N.root (N.graph.source g) := by
    by_contra hno
    have hr := target_reaches_of_not_avoidingReach (hP.root_reaches _) hno
    rw [← hg] at hr
    exact not_reaches_target_source hP.acyclic g hr
  have hstep : N.graph.AdjOn {e}ᶜ (N.graph.source g) (N.graph.target e) := ⟨g, hge, Or.inl ⟨rfl, hg⟩⟩
  have hw : ∀ {v : V}, N.AvoidingReach e N.root v → N.graph.Walks {e}ᶜ N.root v := fun h =>
    walks_of_avoidingReach h fun _ hfe _ => hfe
  exact (N.graph.walks_symm (hw h₁)).trans ((hw h₂).tail hstep)

/-! ### `m ≥ k` -/

/-- **"A set of `k ≥ 4` taxa may or may not determine a blob, but if it does it must be an `m`-blob with `m ≥ k`"** (`a:claim:m-ge-k`, after Definition 8), on the incident cut edges: the path to each taxon leaves the blob by its own
cut edge. -/
theorem card_le_cutDegree (hN : N.IsPhylogenetic) {b : N.graph.BlobVertex} {S : Finset X} (h : IsDeterminedBy N.graph N.leaf b S) :
    S.card ≤ cutDegree N.graph b := by
  have : Finite E := hN.finite_arcs
  induction b using Quotient.inductionOn with
  | h v =>
    change IsDeterminedBy N.graph N.leaf (blobOf N.graph v) S at h
    change S.card ≤ cutDegree N.graph (blobOf N.graph v)
    obtain ⟨h3, hdet⟩ := isDeterminedBy_blobOf_iff.mp h
    have hconn := N.graph_connected hN
    have hw : ∀ u, N.graph.Walks Set.univ v u := fun u => hconn v u
    have hlead : ∀ s : X, s ∈ S → ∃ g, LeadsTo N.graph Set.univ v g (N.leaf s) := fun s _ =>
      (exists_leadsTo (hw _)).resolve_left fun hb =>
        hdet.ne_of_isPendantIn h3 (isPendantIn_leaf hN s _) (fun t _ => hw _)
          ((isPendantIn_leaf hN s _).eq_of_sameBlobIn hb)
    obtain ⟨s₀, hs₀⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have : Nonempty E := ⟨(hlead s₀ hs₀).choose⟩
    choose! g hg using hlead
    rw [cutDegree, incidentCutEdges_blobOf, ← Set.ncard_coe_finset S]
    refine Set.ncard_le_ncard_of_injOn g (fun s hs => (hg s hs).1) (fun s hs t ht hst => ?_) (Set.toFinite _)
    by_contra hne
    exact hdet.ne_of_leadsTo hs ht hne (hw _) (hw _) (hg s hs) (hg t ht) hst

/-- **"It must be an `m`-blob with `m ≥ k`"** (`a:claim:m-ge-k`, after Definition 8), with the degree of Definition 7. -/
theorem card_le_blobDegree (hN : N.IsPhylogenetic) {b : N.graph.BlobVertex} {S : Finset X} (h : IsDeterminedBy N.graph N.leaf b S) :
    S.card ≤ blobDegree N b := by
  have h' := card_le_cutDegree hN h
  unfold blobDegree
  split_ifs <;> omega

/-! ### Equivalent condition (1) after Definition 12 -/

/-- The edges of a blob. -/
def blobEdges (G : DirectedMultigraph V E) (b : G.BlobVertex) : Set E :=
  {e | blobOf G (G.source e) = b ∧ blobOf G (G.target e) = b}

/-- A node of a binary network has at most three edges. -/
theorem ncard_edgesAt_le_three (hN : IsBinaryNetwork N) (v : V) : (TreeSuppression.edgesAt N.graph v).ncard ≤ 3 := by
  have : Finite E := hN.finite_arcs
  have hun : TreeSuppression.edgesAt N.graph v = {g | N.graph.target g = v} ∪ {g | N.graph.source g = v} := by
    ext g
    simp only [TreeSuppression.edgesAt, Set.mem_ofPred_eq, Set.mem_union]
    exact or_comm
  have hle : (TreeSuppression.edgesAt N.graph v).ncard ≤ N.graph.indegree v + N.graph.outdegree v := by
    rw [hun]
    exact Set.ncard_union_le _ _
  rcases hN.node_cases v with rfl | ⟨x, rfl⟩ | h | h
  · rw [hN.root_in, hN.root_out] at hle
    omega
  · rw [hN.leaf_in, hN.leaf_out] at hle
    omega
  · rw [h.1, h.2] at hle
    omega
  · rw [h.1, h.2] at hle
    omega

/-- **A node of a blob with another node has two edges in the blob**: there is an edge to the rest of the blob, on a cycle, which comes back to the node by another edge. -/
theorem exists_two_nonCuts (hN : N.IsPhylogenetic) {p q : V} (hne : p ≠ q) (h : SameBlobIn N.graph Set.univ p q) :
    ∃ f₁ f₂, f₁ ≠ f₂ ∧ f₁ ∈ TreeSuppression.edgesAt N.graph p ∧ f₂ ∈ TreeSuppression.edgesAt N.graph p ∧
      f₁ ∈ nonCutsIn N.graph Set.univ ∧ f₂ ∈ nonCutsIn N.graph Set.univ := by
  rcases Relation.ReflTransGen.cases_head h with h' | ⟨c, ⟨f₁, hf₁, hl⟩, -⟩
  · exact absurd h' hne
  have hl' : Links N.graph f₁ p c := hl
  have hcp : c ≠ p := by
    rintro rfl
    rcases hl' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact NMSC.source_ne_target hN f₁ (h₁.trans h₂.symm)
    · exact NMSC.source_ne_target hN f₁ (h₁.trans h₂.symm)
  have hat₁ : f₁ ∈ TreeSuppression.edgesAt N.graph p := by
    rcases hl' with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact Or.inl h₁
    · exact Or.inr h₂
  have hw : N.graph.Walks (Set.univ \ {f₁}) c p := by
    by_contra hno
    refine hf₁.2 ⟨Set.mem_univ _, fun hc => hno ?_⟩
    rcases hl' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂] at hc
      exact N.graph.walks_symm hc
    · rw [h₁, h₂] at hc
      exact hc
  -- the first arrival at `p`
  have key : ∀ w, N.graph.Walks (Set.univ \ {f₁}) c w →
      (∃ y f, f ≠ f₁ ∧ Links N.graph f y p ∧ N.graph.Walks (Set.univ \ TreeSuppression.edgesAt N.graph p) c y) ∨
        (w ≠ p ∧ N.graph.Walks (Set.univ \ TreeSuppression.edgesAt N.graph p) c w) := by
    intro w hw
    induction hw with
    | refl => exact Or.inr ⟨hcp, .refl⟩
    | @tail a b _ hab ih =>
      rcases ih with ih | ⟨hap, hwa⟩
      · exact Or.inl ih
      · obtain ⟨e, he, hel⟩ := hab
        by_cases hbp : b = p
        · subst hbp
          exact Or.inl ⟨a, e, he.2, hel, hwa⟩
        · refine Or.inr ⟨hbp, hwa.tail ⟨e, ⟨Set.mem_univ _, ?_⟩, hel⟩⟩
          rintro (h₁ | h₁) <;> rcases hel with ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩
          · exact hap (h₂.symm.trans h₁)
          · exact hbp (h₂.symm.trans h₁)
          · exact hbp (h₃.symm.trans h₁)
          · exact hap (h₃.symm.trans h₁)
  rcases key p hw with ⟨y, f₂, hf₂, hl₂, hwy⟩ | ⟨hpp, -⟩
  · have hat₂ : f₂ ∈ TreeSuppression.edgesAt N.graph p := by
      rcases hl₂ with ⟨-, h₂⟩ | ⟨h₂, -⟩
      · exact Or.inr h₂
      · exact Or.inl h₂
    have hnc₂ : f₂ ∈ nonCutsIn N.graph Set.univ := by
      refine ⟨Set.mem_univ _, fun hcut => hcut.not_walks hl₂ ?_⟩
      have h₁ : N.graph.Walks (Set.univ \ {f₂}) y c := by
        refine N.graph.walks_symm (walks_mono ?_ hwy)
        rintro e ⟨-, he⟩
        exact ⟨Set.mem_univ _, fun hef => he (hef ▸ hat₂)⟩
      refine h₁.tail ⟨f₁, ⟨Set.mem_univ _, fun h' => hf₂ h'.symm⟩, Or.symm hl⟩
    exact ⟨f₁, f₂, hf₂.symm, hat₁, hat₂, hf₁, hnc₂⟩
  · exact absurd rfl hpp

/-- A non-cut edge has its ends in one blob. -/
theorem mem_blobEdges_of_nonCutsIn {G : DirectedMultigraph V E} {v p : V} (hp : blobOf G p = blobOf G v) {f : E}
    (hf : f ∈ nonCutsIn G Set.univ) (hat : f ∈ TreeSuppression.edgesAt G p) : f ∈ blobEdges G (blobOf G v) := by
  have hnb : ¬ G.underlying.IsBridge f := fun hb => hf.2 ⟨Set.mem_univ _, by
    rw [G.isBridge_iff_not_walks_delete, Set.compl_eq_univ_sdiff] at hb
    exact hb⟩
  have heq : blobOf G (G.source f) = blobOf G (G.target f) := G.quotient_eq_of_not_isBridge hnb
  rcases hat with h | h
  · exact ⟨h ▸ hp, heq ▸ h ▸ hp⟩
  · exact ⟨heq.symm ▸ h ▸ hp, h ▸ hp⟩

/-- **The forward direction of condition (1) after Definition 12.** In a binary network, a blob with four incident cut edges has two nodes at least, and each node has one more edge beside two in the blob. So
what is beyond a cut edge, with its end in the blob, is left only through the edges of the blob. -/
theorem not_walks_blobEdges (hN : IsBinaryNetwork N) {v : V} {Q : Finset X} (hQ : IsDeterminedBy N.graph N.leaf (blobOf N.graph v) Q)
    (h4 : Q.card = 4) {s t : X} (hs : s ∈ Q) (ht : t ∈ Q) (hst : s ≠ t) :
    ¬ N.graph.Walks (blobEdges N.graph (blobOf N.graph v))ᶜ (N.leaf s) (N.leaf t) := by
  have hP := hN.isPhylogenetic
  have : Finite E := hP.finite_arcs
  obtain ⟨h3, hdet⟩ := isDeterminedBy_blobOf_iff.mp hQ
  have hconn := N.graph_connected hP
  have hw : ∀ u, N.graph.Walks Set.univ v u := fun u => hconn v u
  obtain ⟨g, hg⟩ := (exists_leadsTo (hw (N.leaf s))).resolve_left fun hb =>
    hdet.ne_of_isPendantIn h3 (isPendantIn_leaf hP s _) (fun t _ => hw _) ((isPendantIn_leaf hP s _).eq_of_sameBlobIn hb)
  have hO : OnlyCrosses N.graph Set.univ g (far N.graph Set.univ g v) := onlyCrosses_far
  have hvT : v ∉ far N.graph Set.univ g v := not_mem_far_self
  have hsT : N.leaf s ∈ far N.graph Set.univ g v := hg.2
  have htT : N.leaf t ∉ far N.graph Set.univ g v := fun h =>
    hst (hdet.eq_of_mem_side hO hvT hs ht (hw _) (hw _) hsT h)
  -- the end `p` of `g` in the blob, and `q` beyond it
  obtain ⟨hcut, hb⟩ := hg.1
  obtain ⟨p, q, hl, hpv, hqT⟩ : ∃ p q, Links N.graph g p q ∧ SameBlobIn N.graph Set.univ v p ∧ q ∈ far N.graph Set.univ g v := by
    rcases hb with hb | hb
    · refine ⟨_, _, Or.inl ⟨rfl, rfl⟩, hb, ?_⟩
      refine fun hc => hcut.2 ?_
      exact (N.graph.walks_symm (hb.walks_diff hcut)).trans hc
    · refine ⟨_, _, Or.inr ⟨rfl, rfl⟩, hb, ?_⟩
      refine fun hc => hcut.2 ?_
      exact N.graph.walks_symm ((N.graph.walks_symm (hb.walks_diff hcut)).trans hc)
  have hpT : p ∉ far N.graph Set.univ g v := fun h => h (hpv.walks_diff hcut)
  have hpblob : blobOf N.graph p = blobOf N.graph v := by
    refine Quotient.sound (N.graph.blobSetoid.symm ?_)
    refine Relation.ReflTransGen.mono ?_ _ _ hpv
    rintro a c ⟨f, hf, hfl⟩
    refine ⟨f, fun hbf => hf.2 ⟨Set.mem_univ _, ?_⟩, hfl⟩
    rw [N.graph.isBridge_iff_not_walks_delete, Set.compl_eq_univ_sdiff] at hbf
    exact hbf
  have hgat : g ∈ TreeSuppression.edgesAt N.graph p := by
    rcases hl with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact Or.inl h₁
    · exact Or.inr h₂
  -- the blob has a node other than `p`
  obtain ⟨u, hup, hu⟩ : ∃ u, u ≠ p ∧ SameBlobIn N.graph Set.univ p u := by
    by_contra hno
    push Not at hno
    -- so all the incident cut edges are at `p`
    have hle := card_le_cutDegree hP hQ
    have hsub : incidentCutEdges N.graph (blobOf N.graph v) ⊆ TreeSuppression.edgesAt N.graph p := by
      rw [incidentCutEdges_blobOf]
      rintro e ⟨-, he | he⟩
      · exact Or.inl (by_contra fun hne => hno _ hne (hpv.symm.trans he))
      · exact Or.inr (by_contra fun hne => hno _ hne (hpv.symm.trans he))
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h₃ := ncard_edgesAt_le_three hN p
    unfold cutDegree at hle
    omega
  obtain ⟨f₁, f₂, hne, hat₁, hat₂, hnc₁, hnc₂⟩ := exists_two_nonCuts hP hup.symm hu
  -- the edges at `p` are `g`, and two in the blob
  have hne₁ : g ≠ f₁ := fun h => hnc₁.2 (h ▸ hcut)
  have hne₂ : g ≠ f₂ := fun h => hnc₂.2 (h ▸ hcut)
  have hall : ∀ f ∈ TreeSuppression.edgesAt N.graph p, f = g ∨ f = f₁ ∨ f = f₂ := by
    intro f hf
    by_contra hno
    push Not at hno
    have hsub : ({f, g, f₁, f₂} : Finset E) ⊆ (Set.toFinite (TreeSuppression.edgesAt N.graph p)).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Set.Finite.mem_toFinset]
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hc : ({f, g, f₁, f₂} : Finset E).card = 4 := TreeMetric.card_four_of_ne hno.1 hno.2.1 hno.2.2 hne₁ hne₂ hne
    have hle := Finset.card_le_card hsub
    rw [hc, ← Set.ncard_eq_toFinset_card _] at hle
    have := ncard_edgesAt_le_three hN p
    omega
  -- the walk stays beyond `g`, or at `p`
  intro hwalk
  have hstay : ∀ z, N.graph.Walks (blobEdges N.graph (blobOf N.graph v))ᶜ (N.leaf s) z → z ∈ far N.graph Set.univ g v ∨ z = p := by
    intro z hz
    induction hz with
    | refl => exact Or.inl hsT
    | @tail a c _ hac ih =>
      obtain ⟨e, he, hel⟩ := hac
      have hel' : Links N.graph e a c := hel
      by_cases hcT : c ∈ far N.graph Set.univ g v
      · exact Or.inl hcT
      · right
        rcases ih with haT | rfl
        · -- leaving the far side is by `g`
          have hee : e = g := hO e (Set.mem_univ _) (by
            rcases hel' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
            · exact Or.inl ⟨h₁ ▸ haT, h₂ ▸ hcT⟩
            · exact Or.inr ⟨h₂ ▸ haT, h₁ ▸ hcT⟩)
          subst hee
          rcases hl.eq_or_eq hel' with ⟨h₁, -⟩ | ⟨h₁, -⟩
          · exact absurd (h₁ ▸ haT) hpT
          · exact h₁.symm
        · -- at `p`, only `g` is not an edge of the blob
          have heat : e ∈ TreeSuppression.edgesAt N.graph a := by
            rcases hel' with ⟨h₁, -⟩ | ⟨-, h₂⟩
            · exact Or.inl h₁
            · exact Or.inr h₂
          rcases hall e heat with rfl | rfl | rfl
          · exfalso
            rcases hl.eq_or_eq hel' with ⟨-, h₂⟩ | ⟨-, h₂⟩
            · exact hcT (h₂ ▸ hqT)
            · exact hpT (h₂ ▸ hqT)
          · exact absurd (mem_blobEdges_of_nonCutsIn hpblob hnc₁ hat₁) he
          · exact absurd (mem_blobEdges_of_nonCutsIn hpblob hnc₂ hat₂) he
  rcases hstay _ hwalk with h | h
  · exact htT h
  · -- `t` would be `p`, but a taxon has one edge
    obtain ⟨g', -, hg'⟩ := isPendantIn_leaf hP t Set.univ
    rw [← h] at hgat hat₁
    exact hne₁ ((hg' g (Set.mem_univ _) hgat).trans (hg' f₁ (Set.mem_univ _) hat₁).symm)

/-- **The other direction of condition (1) after Definition 12.** A walk avoiding the incident cut edges of a blob never enters the blob, and doesn't use its edges. -/
theorem isDeterminedBy_of_not_walks_blobEdges (hN : N.IsPhylogenetic) {b : N.graph.BlobVertex} {Q : Finset X} (h3 : 3 ≤ Q.card)
    (h : ∀ s ∈ Q, ∀ t ∈ Q, s ≠ t → ¬ N.graph.Walks (blobEdges N.graph b)ᶜ (N.leaf s) (N.leaf t)) :
    IsDeterminedBy N.graph N.leaf b Q := by
  refine ⟨h3, fun s hs t ht hst hwalk => ?_⟩
  by_cases hsb : blobOf N.graph (N.leaf s) = b
  · -- the blob is the taxon, so it has no edges
    have hempty : blobEdges N.graph b = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro e ⟨h₁, h₂⟩
      have : Finite E := hN.finite_arcs
      have hg := nodeDegree_leaf hN s
      have hs' := Bridges.eq_of_blobOf_eq_of_nodeDegree_eq_one hg (h₁.trans hsb.symm)
      have ht' := Bridges.eq_of_blobOf_eq_of_nodeDegree_eq_one hg (h₂.trans hsb.symm)
      exact NMSC.source_ne_target hN e (hs'.trans ht'.symm)
    refine h s hs t ht hst ?_
    rw [hempty, Set.compl_empty]
    exact N.graph_connected hN _ _
  · have key : ∀ z, N.graph.Walks (incidentCutEdges N.graph b)ᶜ (N.leaf s) z →
        blobOf N.graph z ≠ b ∧ N.graph.Walks (blobEdges N.graph b)ᶜ (N.leaf s) z := by
      intro z hz
      induction hz with
      | refl => exact ⟨hsb, .refl⟩
      | @tail a c _ hac ih =>
        obtain ⟨hab, hw⟩ := ih
        obtain ⟨e, he, hel⟩ := hac
        have hel' : Links N.graph e a c := hel
        have hnb : blobOf N.graph c ≠ b := by
          intro hcb
          by_cases hbr : N.graph.underlying.IsBridge e
          · refine he ⟨hbr, ?_⟩
            rcases hel' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
            · exact Or.inr ⟨h₂ ▸ hcb, h₁ ▸ hab⟩
            · exact Or.inl ⟨h₁ ▸ hcb, h₂ ▸ hab⟩
          · have heq : blobOf N.graph (N.graph.source e) = blobOf N.graph (N.graph.target e) := N.graph.quotient_eq_of_not_isBridge hbr
            rcases hel' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
            · rw [h₁, h₂] at heq
              exact hab (heq.trans hcb)
            · rw [h₁, h₂] at heq
              exact hab (heq.symm.trans hcb)
        refine ⟨hnb, hw.tail ⟨e, fun hmem => ?_, hel⟩⟩
        rcases hel' with ⟨h₁, -⟩ | ⟨-, h₁⟩
        · exact hab (h₁ ▸ hmem.1)
        · exact hab (h₁ ▸ hmem.2)
    exact h s hs t ht hst (key _ hwalk).2

/-- **Equivalent condition (1) after Definition 12** (`a:claim:b-deletion`): `Q` is a B-quartet exactly when "the deletion of all edges in a single blob leaves the elements of `Q` in four distinct connected components". It needs a
binary network, which the paper assumes: the forward direction uses that a node has at most three edges. The paper doesn't prove this. -/
theorem isBlobQuartet_iff_deletion (hN : IsBinaryNetwork N) {Q : Finset X} :
    IsBlobQuartet N Q ↔ Q.card = 4 ∧ ∃ b, ∀ s ∈ Q, ∀ t ∈ Q, s ≠ t → ¬ N.graph.Walks (blobEdges N.graph b)ᶜ (N.leaf s) (N.leaf t) := by
  constructor
  · rintro ⟨h4, b, hb⟩
    refine ⟨h4, b, ?_⟩
    induction b using Quotient.inductionOn with
    | h v => exact fun s hs t ht hst => not_walks_blobEdges hN hb h4 hs ht hst
  · rintro ⟨h4, b, hb⟩
    exact ⟨h4, b, isDeterminedBy_of_not_walks_blobEdges hN.isPhylogenetic (by omega) hb⟩

/-! ### `T_rd(𝒩⁻)` from the rooted one -/

/-- A taxon has degree 1 in the reduced rooted tree of blobs, so isn't suppressed. -/
theorem nodeDegree_reducedRootedTree_leaf (hN : IsBinaryNetwork N) (hX : Nontrivial X) (x : X) :
    nodeDegree (reducedRootedTree hN hX).graph ((reducedRootedTree hN hX).leaf x) = 1 := by
  have hT : (reducedRootedTree hN hX).IsPhylogenetic := blobTree_isPhylogenetic (lsaPlus_isPhylogenetic hN hX)
  rw [nodeDegree, hT.leaf_indegree, (hT.leaves _).mpr ⟨x, rfl⟩]

/-- **"The reduced unrooted tree of blobs `T_rd(𝒩⁻)` can also be obtained from the rooted one `T_rd(𝒩⁺)` by undirecting all edges, and either suppressing the root if it has degree 2 (as a node) or dropping its
designation as the root if it has larger degree"** (after Definition 11). Every other node of the rooted tree has degree other than 2 (`suppress_degree_two_eq_root` of the library), so this is `suppressDegreeTwo`. -/
def trdFromRooted (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    LabelledGraph {w // nodeDegree (reducedRootedTree hN hX).graph w ≠ 2} X where
  graph := suppressDegreeTwo (reducedRootedTree hN hX).graph
  leaf x := ⟨(reducedRootedTree hN hX).leaf x, by
    rw [nodeDegree_reducedRootedTree_leaf hN hX x]
    omega⟩

/-- The only node of the rooted tree of blobs that `trdFromRooted` suppresses is the root. -/
theorem eq_root_of_nodeDegree_reducedRootedTree (hN : IsBinaryNetwork N) (hX : Nontrivial X) {v}
    (hv : nodeDegree (reducedRootedTree hN hX).graph v = 2) : v = (reducedRootedTree hN hX).root :=
  suppress_degree_two_eq_root (bridgeQuotientData_isPhylogenetic (lsaPlus_isPhylogenetic hN hX)) v hv

/-- The two ways give the same tree, as far as splits go. -/
theorem splits_trdFromRooted [Fintype X] [DecidableEq X] (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    (trdFromRooted hN hX).splits = (Trd hN hX).splits := by
  have hP := lsaPlus_isPhylogenetic hN hX
  have : Finite V := hN.finite_vertices
  have : Finite E := hN.finite_arcs
  have hTree : (reducedRootedTree hN hX).graph.IsTree := blobTree_isTree hP
  rw [Bridges.splits_Trd]
  ext A
  rw [mem_treeOfBlobs_iff]
  simp only [LabelledGraph.splits, Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun h₁ => and_congr_right fun h₂ => ?_
  have h₁' : (Set.univ ∩ (A : Set X)).Nonempty := by
    obtain ⟨x, hx⟩ := h₁
    exact ⟨x, Set.mem_univ x, hx⟩
  have h₂' : (Set.univ \ (A : Set X)).Nonempty := by
    obtain ⟨x, hx⟩ := h₂
    exact ⟨x, Set.mem_univ x, by simpa using hx⟩
  have hside := TreeSuppression.hasSide_iff hTree (trdFromRooted hN hX).leaf (A : Set X)
  refine hside.trans (Iff.trans ?_ ((Bridges.lsaPlus_hasCutSplit_iff hN hX _).trans
    ((hasCutSplitOn_iff_lsaNetwork_hasCutSplit hN.isPhylogenetic Set.nontrivial_univ h₁' h₂').symm.trans
      (hasCutSplit_iff_hasCutSplitOn_univ hN.isPhylogenetic _).symm)))
  exact blobTree_hasCutSplit_iff hP _

/-- The tree from the rooted tree of blobs is a reduced tree. The root isn't a leaf of the rooted tree of blobs, since a cut edge of `𝒩⊕` has a taxon on each side. -/
theorem isReducedTree_trdFromRooted (hN : IsBinaryNetwork N) (hX : Nontrivial X) : (trdFromRooted hN hX).IsReducedTree := by
  have hP := lsaPlus_isPhylogenetic hN hX
  have hB : (reducedRootedTree hN hX).IsPhylogenetic := blobTree_isPhylogenetic hP
  have : Finite V := hN.finite_vertices
  have : Finite E := hN.finite_arcs
  have hTree : (reducedRootedTree hN hX).graph.IsTree := blobTree_isTree hP
  obtain ⟨x₀⟩ : Nonempty X := hX.to_nonempty
  have : Nonempty {w // nodeDegree (reducedRootedTree hN hX).graph w ≠ 2} := ⟨(trdFromRooted hN hX).leaf x₀⟩
  refine ⟨TreeSuppression.isTree_suppressDegreeTwo hTree, inferInstance, fun x y hxy => hB.leaf_injective (congrArg Subtype.val hxy), fun x => ?_, fun v hv => ?_⟩
  · exact (TreeSuppression.ncard_neighborSet_suppressDegreeTwo hTree _).trans (nodeDegree_reducedRootedTree_leaf hN hX x)
  · change 3 ≤ ((suppressDegreeTwo (reducedRootedTree hN hX).graph).neighborSet v).ncard
    rw [TreeSuppression.ncard_neighborSet_suppressDegreeTwo hTree]
    have h2 := v.2
    have hnl : ∀ x, (reducedRootedTree hN hX).leaf x ≠ v.1 := fun x hx => hv x (Subtype.ext hx)
    have hout : (reducedRootedTree hN hX).graph.outdegree v.1 ≠ 0 := fun h0 => by
      obtain ⟨x, hx⟩ := (hB.leaves _).mp h0
      exact hnl x hx
    have h1 : nodeDegree (reducedRootedTree hN hX).graph v.1 ≠ 1 := by
      intro hd
      have hin : (reducedRootedTree hN hX).graph.indegree v.1 = 0 := by
        have hd' : (reducedRootedTree hN hX).graph.indegree v.1 + (reducedRootedTree hN hX).graph.outdegree v.1 = 1 := hd
        omega
      have hvr : v.1 = (reducedRootedTree hN hX).root := by
        by_contra hne
        have := hB.nonroot_indegree _ hne
        omega
      -- a root with one edge: no taxon on its side
      rw [TreeSuppression.nodeDegree_eq_ncard_edgesAt hTree] at hd
      obtain ⟨e, he⟩ := Set.ncard_eq_one.mp hd
      have hside : ∀ f, (reducedRootedTree hN hX).graph.Crosses f {v.1} ↔ f = e := by
        intro f
        have hat : f ∈ TreeSuppression.edgesAt (reducedRootedTree hN hX).graph v.1 ↔ f = e := by
          rw [he]
          rfl
        constructor
        · rintro (⟨hs, -⟩ | ⟨ht, -⟩)
          · exact hat.mp (Or.inl hs)
          · exact hat.mp (Or.inr ht)
        · rintro rfl
          rcases hat.mpr rfl with hs | ht
          · exact Or.inl ⟨hs, fun ht => TreeSuppression.source_ne_target hTree f (Eq.trans hs (Eq.symm ht))⟩
          · exact Or.inr ⟨ht, fun hs => TreeSuppression.source_ne_target hTree f (Eq.trans hs (Eq.symm ht))⟩
      have hcut : (reducedRootedTree hN hX).HasCutSplit (∅ : Set X) :=
        ⟨e, {v.1}, hside, Set.eq_empty_of_forall_notMem fun x hx => hnl x hx⟩
      exact Bridges.lsaPlus_not_hasCutSplit_empty hN hX ((blobTree_hasCutSplit_iff hP _).mp hcut)
    have hd0 : nodeDegree (reducedRootedTree hN hX).graph v.1 ≠ 0 := by
      unfold nodeDegree
      omega
    omega

/-- **"`T_rd(𝒩⁻)` can also be obtained from the rooted one `T_rd(𝒩⁺)`"** (`a:claim:trd-rooted`, after Definition 11), as labelled trees. -/
theorem isIso_trdFromRooted [Fintype X] [DecidableEq X] (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    (trdFromRooted hN hX).IsIso (Trd hN hX) := by
  obtain ⟨x⟩ : Nonempty X := hX.to_nonempty
  have : Nonempty X := ⟨x⟩
  exact LabelledGraph.isIso_of_splits_eq (isReducedTree_trdFromRooted hN hX) (Bridges.isReducedTree_Trd hN hX) (splits_trdFromRooted hN hX)

/-! ### Displayed trees -/

section Displayed

variable [Fintype V] [Fintype X] [DecidableEq X]

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- A set of deleted arcs leaving a parent at each node is inside the arcs left out by a choice of parents. -/
theorem exists_parentChoice {D : Set E} (hD : N.IsDeletion D) : ∃ c : N.ParentChoice, D ⊆ N.deletedArcs c := by
  have hp : ∀ v : {v : V // v ≠ N.root}, ∃ e : {e : E // N.graph.target e = v.val}, e.1 ∉ D := fun v => by
    obtain ⟨f, hf, hfv⟩ := hD.parent v.1 v.2
    exact ⟨⟨f, hfv⟩, hf⟩
  choose c hc using hp
  exact ⟨c, fun e he h' hEq => hc _ (hEq ▸ he)⟩

/-- **A cut edge off a set of deleted arcs is an edge of the displayed tree of each choice of parents leaving those arcs out**, so that tree displays its quartet. -/
theorem displays_displayedSides_of_splitOffAt (hN : N.IsPhylogenetic) (c : N.ParentChoice) {D : Set E} (hDc : D ⊆ N.deletedArcs c) {e : E}
    {s : QuartetTree X} (h : N.SplitOffAt D e s) : Displays (N.displayedSides c) s := by
  obtain ⟨P, hP, hd, hn⟩ := h
  have hdel := isDeletion_deletedArcs hN c
  have hbelow : ∀ x ∈ P, N.IsBelowOff (N.deletedArcs c) e x := by
    intro x hx
    refine DominatesOff.isBelowOff hN hdel fun hr => hd x (Finset.mem_coe.mpr hx) ?_
    exact hr.mono (Set.insert_subset_insert hDc)
  set A := N.displayedCluster c (N.graph.target e) with hA
  have hAq : A ∩ s.taxa = P := by
    ext x
    rw [Finset.mem_inter]
    constructor
    · rintro ⟨hxA, hxq⟩
      by_contra hxP
      obtain ⟨a, ha⟩ : P.Nonempty := Finset.card_pos.1 (by rw [s.card_of_mem hP]; omega)
      refine hn x (Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨hxq, hxP⟩)) ⟨fun heD => (hbelow a ha).1 (hDc heD), ?_⟩
      exact (mem_displayedCluster.1 hxA).mono hDc
    · exact fun hx => ⟨mem_displayedCluster.2 (hbelow x hx).2, s.subset_taxa hP hx⟩
  obtain ⟨a, ha⟩ : P.Nonempty := Finset.card_pos.1 (by rw [s.card_of_mem hP]; omega)
  obtain ⟨y, hy⟩ : (s.taxa \ P).Nonempty := Finset.card_pos.1 (by rw [s.card_of_mem (s.sdiff_mem hP)]; omega)
  have hAne : A ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨a, mem_displayedCluster.2 (hbelow a ha).2⟩
  have hAu : A ≠ Finset.univ := fun h' => by
    have hyA : y ∈ A := h' ▸ Finset.mem_univ y
    have hyq := Finset.mem_sdiff.mp hy
    have : y ∈ P := hAq ▸ Finset.mem_inter.mpr ⟨hyA, hyq.1⟩
    exact hyq.2 this
  refine ⟨A, mem_unroot.2 (Or.inl ⟨mem_displayedClusters.2 ⟨hAne, _, rfl⟩, hAu⟩), ?_⟩
  rw [hAq]
  exact hP

/-- **"Nonetheless this induced network is 'tree-like' in the sense that it will have a cut edge whose removal disconnects the four taxa into two groups of 2. Equivalently, every tree displayed on the 4-taxon network has
the same resolved quartet topology"** (`a:claim:displayed-trees`, after Definition 13). One direction is the library's `displays_displayedSides_of_inducedCutSplit`. The other is the reduction in the proof of Theorem 1 (b),
which the paper doesn't mention here: without a cut edge, two displayed trees have different quartet topologies. -/
theorem isTreelike_iff_forall_displays (hN : N.IsPhylogenetic) (hB : N.IsBinary) {q : Finset X} (hq : q.card = 4) :
    IsTreelike N q ↔ ∃ s ∈ treesOn q, ∀ c : N.ParentChoice, Displays (N.displayedSides c) s := by
  constructor
  · rintro ⟨s, hs, hc⟩
    exact ⟨s, hs, fun c => displays_displayedSides_of_inducedCutSplit hN c hc⟩
  · rintro ⟨s, hs, hall⟩
    by_contra hnt
    obtain ⟨a⟩ : Nonempty X := by
      obtain ⟨x, -⟩ := Finset.card_pos.mp (by omega : 0 < q.card)
      exact ⟨x⟩
    have hne : Nonempty X := ⟨a⟩
    obtain ⟨D, k₁, k₂, -, s₁, s₂, e₁, e₂, hD, hk, ht, hk₁, hk₂, -, -, -, -, hs₁, hs₂, hss, h₁, h₂⟩ := exists_reduction hN hB hq hnt
    have hD₁ : N.IsDeletion (insert k₂ D) := hD.insert hN hk.symm ht.symm hk₁
    have hD₂ : N.IsDeletion (insert k₁ D) := hD.insert hN hk ht hk₂
    obtain ⟨c₁, hc₁⟩ := exists_parentChoice hD₁
    obtain ⟨c₂, hc₂⟩ := exists_parentChoice hD₂
    have hu₁ := isUnrootedTree_displayedSides hN c₁
    have hu₂ := isUnrootedTree_displayedSides hN c₂
    have e₁s := hu₁.displays_unique (displays_displayedSides_of_splitOffAt hN c₁ hc₁ h₁) (hall c₁)
      ((mem_treesOn.1 hs₁).trans (mem_treesOn.1 hs).symm)
    have e₂s := hu₂.displays_unique (displays_displayedSides_of_splitOffAt hN c₂ hc₂ h₂) (hall c₂)
      ((mem_treesOn.1 hs₂).trans (mem_treesOn.1 hs).symm)
    exact hss (e₁s.trans e₂s.symm)

/-- **The same, for a 4-taxon network and its T-quartet.** -/
theorem isTreeQuartet_iff_forall_displays (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) :
    IsTreeQuartet N Finset.univ ↔ ∃ s ∈ treesOn (Finset.univ : Finset X), ∀ c : N.ParentChoice, Displays (N.displayedSides c) s := by
  have hc : (Finset.univ : Finset X).card = 4 := by rw [Finset.card_univ, hcard]
  rw [← isTreelike_iff_forall_displays hN.isPhylogenetic hN.isBinary hc, Bridges.isTreelike_iff_resolves hN.isPhylogenetic hc]
  have := Bridges.isBlobQuartet_iff_not_resolves hN hc
  exact ⟨fun h => by_contra fun hr => h.2 (this.mpr hr), fun h => ⟨hc, fun hB => this.mp hB h⟩⟩

end Displayed

/-! ### The mixture -/

/-- **"Since `a` is the only taxon below the hybrid node `v`, `CF_abcd(𝒩⁺) = γ₁ CF_abcd(𝒩₂⁺) + γ₂ CF_abcd(𝒩₁⁺)`"** (`a:claim:mixture`, in the proof of Theorem 1 (b)), on the networks of the paper: `𝒩ᵢ⁺` is `deleted`, the network with the hybrid edge `kᵢ` deleted and its degree-2 nodes suppressed. So `𝒩₂⁺` takes the parameters with `1` at `k₁`, and `𝒩₁⁺` those with `0` at `k₁`. -/
theorem cf_mixture [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] [Nontrivial X] (hN : IsBinaryNetwork N) {θ : MetricData E} (hθ : N.IsNormalized θ) {k₁ k₂ : E}
    (hk : k₁ ≠ k₂) (ht : N.graph.target k₂ = N.graph.target k₁) (hpar : ∀ f, N.graph.target f = N.graph.target k₁ → f = k₁ ∨ f = k₂) (s : QuartetTree X) (a : X)
    (honly : ∀ x ∈ s.taxa, x ≠ a → ¬ N.graph.Reaches (N.graph.target k₁) (N.leaf x)) (γ : ℝ) (hD₁ : N.IsDeletion {k₁}) (hD₂ : N.IsDeletion {k₂})
    [Fintype {v // ¬ (HasStem (offSuppressed hN hD₁) ∧ v = (offSuppressed hN hD₁).root)}]
    [Fintype {e // ¬ (HasStem (offSuppressed hN hD₁) ∧ (offSuppressed hN hD₁).graph.source e = (offSuppressed hN hD₁).root)}]
    [Fintype {v // ¬ (HasStem (offSuppressed hN hD₂) ∧ v = (offSuppressed hN hD₂).root)}]
    [Fintype {e // ¬ (HasStem (offSuppressed hN hD₂) ∧ (offSuppressed hN hD₂).graph.source e = (offSuppressed hN hD₂).root)}] :
    nmscCF N (θ.withPair k₁ k₂ γ) 0 s =
      γ * nmscCF (deleted hN hD₂) (deletedParams hN hD₂ (θ.withPair k₁ k₂ 1)) 0 s +
        (1 - γ) * nmscCF (deleted hN hD₁) (deletedParams hN hD₁ (θ.withPair k₁ k₂ 0)) 0 s := by
  have h0 : ∀ f, N.graph.target f = N.graph.target k₁ → f ≠ k₁ → f ≠ k₂ → θ.inheritance f = 0 := fun f hf h₁ h₂ =>
    absurd ((hpar f hf).resolve_left h₁) h₂
  rw [nmscCF_deleted hN hD₂ (NMSC.isNormalized_withPair hθ hk ht h0 1) (by
        rintro f rfl
        rw [NMSC.withPair_inheritance_right hk, sub_self]) le_rfl s,
    nmscCF_deleted hN hD₁ (NMSC.isNormalized_withPair hθ hk ht h0 0) (by
        rintro f rfl
        rw [NMSC.withPair_inheritance_left]) le_rfl s]
  exact nmscCF_withPair_mixture hN.isPhylogenetic hθ hk ht hpar s a honly γ

end AllmanEtAl2023.InPassing
