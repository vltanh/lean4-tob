module

public import External.GusfieldEtAl2004.Elimination
public import External.GusfieldEtAl2004.GalledTree
public import Gusfield2007.Decomposition

/-!
# A reduced galled tree minimizes the number of recombinations (Gusfield, Eddhu, Langley 2004)

See the `README.md` of this directory. This is what line 381 of Gusfield et al. 2007 cites: when `M` can be derived on a galled tree, restricting to fully-decomposed networks loses nothing, "even if the galled-tree must only use single-crossover recombinations, but
any competing phylogenetic network is allowed to use multiple-crossovers".

* Theorems 2.6 and 2.7 of the source, in their counting part: the non-trivial connected components of the conflict graph correspond to the galls with conflicted sites (`theorem2_6`), so a galled tree whose galls all have some has exactly as many recombination
  nodes (`theorem2_7_moreover`, `theorem2_7_moreover_incompatGraph`). The part of Theorem 2.7 about a minimum over galled trees needs a reduced galled tree to exist, and is in `ReducedExists.lean`.
* Section 8: a removal changes one component (`lemma8_5`, `lemma8_6`), so any execution of the Elimination Algorithm has as many removals as components (`card_cent_le_of_elim`, `theorem8_2`), and with Theorem 8.1 this gives `theorem8_3`.
* The connection with `R` and `RS` of `Gusfield2007`: `reducedGalledTree_recombCount_eq_RS` and `reducedGalledTree_recombCount_eq_R`, and line 381, `line381_rooted`, `line381`.

## The difference from the source

The source carries "a reduced galled-tree `T` that derives the current `M`" through the execution: Lemma 8.2 deletes a site, Lemma 8.4 a leaf and a path above it, Lemma 8.5 removes the edges above a leaf, and Lemma 8.6 goes back to a reduced galled tree with Corollary 5.1. The
claims about the conflict graph are what Theorem 8.2 uses: "Lemmas 8.2 and 8.4 show that row and column deletion operations do not result in the deletion of edges in any non-trivial connected component of the conflict graph. Lemma 8.5 shows that each sequence removal results in
the removal of edges in at most one non-trivial connected component."

Here those claims are proved on one galled tree `N`, the one given, and its node labels on the columns still there (`RowsOn`). Departure from the source, for two reasons. First, its Lemma 8.6 applies Corollary 5.1 after a removal, and the proof of that corollary uses the standing
assumption of distinct columns, which a removal doesn't keep: columns that differ only in the removed row become identical. Second, its proof of Lemma 8.5 says that a removed edge `(u, v)` on a gall has `v` the recombination node, since otherwise "`v` would be a branching
node". A node on a gall needn't be branching: an edge with no site, above a node with no edge off the gall, can be removed. On a fixed network neither matters. The columns of Lemma 8.2 and the rows of Lemma 8.4 change nothing in the graph, whatever the network (`incompatGraph_image_maskCol`, and the
rows are a `Finset`), and Lemma 8.5 is proved as the source's "only one gall is affected", with the source's Lemma 2.1 (`label_tgt_of_notMem`) on the two galls.
-/

@[expose] public noncomputable section

open scoped Classical

namespace GusfieldEtAl2004

open Gusfield2007 Gusfield2007.Network Gusfield2007.Decomp

variable {ι V E : Type*}

/-! ### Galls, recombination nodes and components -/

section Count

variable {N : Network ι V E} [Finite V] {w x w' x' : V} {p q p' q' : List E}

omit [Finite V] in
/-- The two last arcs of a recombination cycle are the two arcs into its recombination node. -/
theorem cycle_last_arcs (hc : N.IsCycleOn w x p q) : ∃ a b, a ∈ p ∧ b ∈ q ∧ a ≠ b ∧ N.tgt a = x ∧ N.tgt b = x := by
  obtain ⟨_, a, ha, -, hax⟩ := hc.2.1.exists_last_arc hc.ne_nil
  obtain ⟨_, b, hb, -, hbx⟩ := hc.2.2.1.exists_last_arc hc.symm.ne_nil
  have ha' : a ∈ p := by rw [ha]; simp
  have hb' : b ∈ q := by rw [hb]; simp
  exact ⟨a, b, ha', hb', fun hab => hc.notMem ha' (hab ▸ hb'), hax, hbx⟩

omit [Finite V] in
/-- Two recombination cycles with one recombination node share an arc. -/
theorem cycle_share_arc (hc : N.IsCycleOn w x p q) (hc' : N.IsCycleOn w' x p' q') : ∃ e, (e ∈ p ∨ e ∈ q) ∧ (e ∈ p' ∨ e ∈ q') := by
  obtain ⟨a, b, ha, hb, hab, hax, hbx⟩ := cycle_last_arcs hc
  obtain ⟨a', -, ha', -, -, hax', -⟩ := cycle_last_arcs hc'
  rcases eq_or_eq_of_tgt hab (hax.trans hbx.symm) (hax'.trans hax.symm) with rfl | rfl
  · exact ⟨a', Or.inl ha, Or.inl ha'⟩
  · exact ⟨a', Or.inr hb, Or.inl ha'⟩

omit [Finite V] in
/-- A recombination cycle has one recombination node, determined by its arcs. -/
theorem cycle_recomb_eq (hc : N.IsCycleOn w x p q) (hc' : N.IsCycleOn w' x' p' q') (h : {e | e ∈ p ∨ e ∈ q} = {e | e ∈ p' ∨ e ∈ q'}) : x = x' := by
  obtain ⟨a, -, ha, -, -, hax, -⟩ := cycle_last_arcs hc
  obtain ⟨a', -, ha', -, -, hax', -⟩ := cycle_last_arcs hc'
  have h₁ : a ∈ {e | e ∈ p' ∨ e ∈ q'} := h ▸ Or.inl ha
  have h₂ : a' ∈ {e | e ∈ p ∨ e ∈ q} := h.symm ▸ Or.inl ha'
  exact Reach.antisymm (hax ▸ cycle_reach_tgt hc' h₁) (hax' ▸ cycle_reach_tgt hc h₂)

/-- The two arcs into a recombination node are on a recombination cycle at the node. -/
theorem exists_isCycleOn_of_isRecomb (hx : N.IsRecomb x) : ∃ w p q, N.IsCycleOn w x p q := by
  obtain ⟨e, f, hef, rfl, hf⟩ := hx
  obtain ⟨w, p, q, -, -, hc⟩ := exists_isCycleOn_of_tgt_eq hef hf.symm
  exact ⟨w, _, _, hc⟩

/-- In a galled tree, the recombination nodes correspond to the recombination cycles, each cycle being a gall. -/
theorem IsGalledTree.card_recomb_eq (hG : IsGalledTree N) : N.recombCount = Nat.card {Q // N.IsCycle Q} := by
  choose wf pf qf hf using fun x : {x // N.IsRecomb x} => exists_isCycleOn_of_isRecomb x.2
  refine Nat.card_eq_of_bijective (fun x => (⟨{e | e ∈ pf x ∨ e ∈ qf x}, ⟨wf x, x.1, pf x, qf x, hf x, rfl⟩⟩ : {Q // N.IsCycle Q})) ⟨fun x y hxy => ?_, ?_⟩
  · exact Subtype.ext (cycle_recomb_eq (hf x) (hf y) (congrArg Subtype.val hxy))
  · rintro ⟨Q, w, x, p, q, hc, rfl⟩
    refine ⟨⟨x, hc.1⟩, Subtype.ext ?_⟩
    obtain ⟨e, he, he'⟩ := cycle_share_arc (hf ⟨x, hc.1⟩) hc
    exact hG.eq_of_inter ⟨_, _, _, _, hf ⟨x, hc.1⟩, rfl⟩ ⟨w, x, p, q, hc, rfl⟩ ⟨e, he, he'⟩ |>.symm

variable {L : Finset (ι → Bool)}

/-- A non-trivial component has an edge. -/
theorem Cent.exists_adj {G : SimpleGraph ι} (c : Cent G) : ∃ i j, i ∈ c.1.supp ∧ G.Adj i j := by
  obtain ⟨a, ha, b, hb, hab⟩ := c.2
  obtain ⟨k, hk⟩ := exists_adj_of_reachable (SimpleGraph.ConnectedComponent.exact (ha.trans hb.symm)) hab
  exact ⟨a, k, ha, hk⟩

/-- The component of a site with an edge is non-trivial. -/
theorem nontrivial_of_adj {G : SimpleGraph ι} {i j : ι} (h : G.Adj i j) : (G.connectedComponentMk i).supp.Nontrivial :=
  ⟨i, rfl, j, (SimpleGraph.ConnectedComponent.eq.2 h.reachable).symm, h.ne⟩

/-- **Theorem 2.6** (`ext:thm2_6`) of the source. "In any galled-tree `T` for `M`, there is a one-one correspondence between the non-trivial connected components of the conflict graph and the galls in `T` containing conflicted sites. Each such gall in `T` contains all the
sites of one non-trivial connected component (due to Theorem 2.4), and contains no sites from a different non-trivial connected component (due to Theorem 2.5)." For the rows `L` that label nodes: the conflict graph is `incompatGraph (addRow M S)`, and the
unrooted one is `incompatGraph M`. -/
theorem theorem2_6 (hG : IsGalledTree N) (hL : ∀ r ∈ L, ∃ v, N.label v = r) :
    ∃ f : Cent (incompatGraph L) ≃ {Q // N.IsCycle Q ∧ ∃ i j, N.site i ∈ Q ∧ (incompatGraph L).Adj i j},
      ∀ c i, (∃ j, (incompatGraph L).Adj i j) → (N.site i ∈ (f c).1 ↔ i ∈ c.1.supp) := by
  choose i₀ j₀ hi₀ hadj using fun c : Cent (incompatGraph L) => Cent.exists_adj c
  choose Q hQ hi hj using fun c => exists_isCycle_of_incompatible N hL (hadj c)
  have hiff : ∀ c i, (∃ j, (incompatGraph L).Adj i j) → (N.site i ∈ Q c ↔ i ∈ c.1.supp) := by
    rintro c i ⟨j, hij⟩
    constructor
    · intro hm
      have hr := theorem2_5_of_rows hG (hQ c) hL hm (hi c) hij (hadj c)
      exact (SimpleGraph.ConnectedComponent.eq.2 hr).trans (hi₀ c)
    · intro hm
      have hr : (incompatGraph L).Reachable (i₀ c) i := SimpleGraph.ConnectedComponent.exact ((hi₀ c).trans hm.symm)
      exact theorem2_4 hG (hQ c) hL (hi c) hr
  refine ⟨Equiv.ofBijective (fun c => ⟨Q c, hQ c, i₀ c, j₀ c, hi c, hadj c⟩) ⟨fun c c' hcc => ?_, ?_⟩, hiff⟩
  · have heq : Q c = Q c' := congrArg Subtype.val hcc
    have h₁ : i₀ c ∈ c'.1.supp := (hiff c' _ ⟨_, hadj c⟩).1 (heq ▸ hi c)
    exact Subtype.ext ((hi₀ c).symm.trans h₁)
  · rintro ⟨Q', hQ', i, j, hm, hij⟩
    let c : Cent (incompatGraph L) := ⟨_, nontrivial_of_adj hij⟩
    refine ⟨c, Subtype.ext ?_⟩
    have hmem : N.site i ∈ Q c := (hiff c i ⟨j, hij⟩).2 rfl
    exact hG.eq_of_inter hQ' (hQ c) ⟨_, hm, hmem⟩

/-- **Theorem 2.7** of the source, the count: a galled tree in which each gall has a conflicted site has one recombination node for each non-trivial component. -/
theorem recombCount_eq_card_cent (hG : IsGalledTree N) (hL : ∀ r ∈ L, ∃ v, N.label v = r)
    (hconf : ∀ Q, N.IsCycle Q → ∃ i j, N.site i ∈ Q ∧ (incompatGraph L).Adj i j) : N.recombCount = Nat.card (Cent (incompatGraph L)) := by
  obtain ⟨f, -⟩ := theorem2_6 hG hL
  rw [hG.card_recomb_eq, Nat.card_congr f]
  exact Nat.card_congr ⟨fun Q => ⟨Q.1, Q.2, hconf Q.1 Q.2⟩, fun Q => ⟨Q.1, Q.2.1⟩, fun _ => rfl, fun _ => rfl⟩

/-- A galled tree has a recombination node for each non-trivial component, at least. -/
theorem card_cent_le_recombCount (hG : IsGalledTree N) (hL : ∀ r ∈ L, ∃ v, N.label v = r) : Nat.card (Cent (incompatGraph L)) ≤ N.recombCount := by
  obtain ⟨f, -⟩ := theorem2_6 hG hL
  choose wf xf pf qf hf hQ using fun c => (f c).2.1
  have hinj : Function.Injective fun c => (⟨xf c, (hf c).1⟩ : {x // N.IsRecomb x}) := by
    intro c c' hcc
    have hx : xf c = xf c' := congrArg Subtype.val hcc
    obtain ⟨e, he, he'⟩ := cycle_share_arc (hf c) (hx ▸ hf c')
    have heq := hG.eq_of_inter ⟨_, _, _, _, hf c, rfl⟩ ⟨_, _, _, _, hf c', rfl⟩ ⟨e, he, he'⟩
    apply f.injective
    apply Subtype.ext
    rw [hQ, hQ, heq]
  exact Nat.card_le_card_of_injective _ hinj

variable {M : Finset (ι → Bool)}

omit [Finite V] in
/-- The rows of `M + S` label nodes of a network deriving `M` with ancestral sequence `S`. -/
theorem labels_addRow (hD : N.Derives M) : ∀ r ∈ addRow M N.ancestral, ∃ v, N.label v = r := fun r hr => by
  rcases mem_addRow.1 hr with rfl | hr
  · exact ⟨N.root, rfl⟩
  · exact hD.displays r hr

/-- **Theorem 2.7** (`ext:thm2_7`) of the source, its second sentence. "Any galled-tree for `M` where each gall contains some conflicted sites, uses exactly `k` recombinations", for the `k` non-trivial components of the conflict graph.
The first sentence is `theorem2_7`. -/
theorem theorem2_7_moreover (hG : IsGalledTree N) (hD : N.Derives M)
    (hconf : ∀ Q, N.IsCycle Q → ∃ i j, N.site i ∈ Q ∧ (conflictGraph N.ancestral M).Adj i j) : N.recombCount = Nat.card (Cent (conflictGraph N.ancestral M)) := by
  rw [conflictGraph_eq_incompatGraph_addRow] at hconf ⊢
  exact recombCount_eq_card_cent hG (labels_addRow hD) hconf

/-- `theorem2_7_moreover`, for the incompatibility graph of `M`, the unrooted form. -/
theorem theorem2_7_moreover_incompatGraph (hG : IsGalledTree N) (hD : N.Derives M)
    (hconf : ∀ Q, N.IsCycle Q → ∃ i j, N.site i ∈ Q ∧ (incompatGraph M).Adj i j) : N.recombCount = Nat.card (Cent (incompatGraph M)) :=
  recombCount_eq_card_cent hG hD.displays hconf

/-- A reduced galled tree has one recombination node for each non-trivial component of the conflict graph (Corollary 5.1 of the source). -/
theorem IsReducedGalledTree.recombCount_eq (h : IsReducedGalledTree N (conflictGraph N.ancestral M)) (hD : N.Derives M) :
    N.recombCount = Nat.card (Cent (conflictGraph N.ancestral M)) :=
  theorem2_7_moreover h.galled hD fun Q hQ => by
    obtain ⟨i, j, hi, -, hij⟩ := h.exists_conflict Q hQ
    exact ⟨i, j, hi, hij⟩

/-- A reduced galled tree, unrooted, has one recombination node for each non-trivial component of the incompatibility graph. -/
theorem IsReducedGalledTree.recombCount_eq_incompatGraph (h : IsReducedGalledTree N (incompatGraph M)) (hD : N.Derives M) :
    N.recombCount = Nat.card (Cent (incompatGraph M)) :=
  theorem2_7_moreover_incompatGraph h.galled hD fun Q hQ => by
    obtain ⟨i, j, hi, -, hij⟩ := h.exists_conflict Q hQ
    exact ⟨i, j, hi, hij⟩

end Count

/-! ### A removal changes one component -/

section Removal

variable {N : Network ι V E} [Finite V] {T : ι → Bool} {D : Set ι} {Y : Finset (ι → Bool)}

/-- Every row of `Y` is the label of a node of `N`, on the columns `D`, and the other columns are deleted. These are the matrices of an execution of the Elimination Algorithm on rows that `N` derives. -/
def RowsOn (N : Network ι V E) (T : ι → Bool) (D : Set ι) (Y : Finset (ι → Bool)) : Prop :=
  ∀ r ∈ Y, ∃ v, r = liveRow T D (N.label v)

omit [Finite V] in
theorem RowsOn.mono {Y' : Finset (ι → Bool)} (hY : RowsOn N T D Y) (h : Y' ⊆ Y) : RowsOn N T D Y' := fun r hr => hY r (h hr)

theorem liveRow_of_mem {r : ι → Bool} {i : ι} (hi : i ∈ D) : liveRow T D r i = r i := by
  simp [liveRow, hi]

omit [Finite V] in
/-- A column in an incompatibility hasn't been deleted. -/
theorem RowsOn.mem_of_incompatible (hY : RowsOn N T D Y) {i j : ι} (h : Incompatible Y i j) : i ∈ D := by
  by_contra hi
  obtain ⟨r, hr, h₁, -⟩ := h (!T i) true
  obtain ⟨v, rfl⟩ := hY r hr
  simp [liveRow, hi] at h₁

omit [Finite V] in
theorem incompatible_symm {i j : ι} (h : Incompatible Y i j) : Incompatible Y j i := fun a b => by
  obtain ⟨r, hr, h₁, h₂⟩ := h b a
  exact ⟨r, hr, h₂, h₁⟩

/-- The general fact of the proof of Theorem 2.2 of the source, for the matrices of an execution. -/
theorem RowsOn.exists_isCycle (hY : RowsOn N T D Y) {i j : ι} (h : Incompatible Y i j) : ∃ Q, N.IsCycle Q ∧ N.site i ∈ Q ∧ N.site j ∈ Q := by
  have : Fintype V := Fintype.ofFinite V
  refine exists_isCycle_of_incompatible N (L := Finset.univ.image N.label) (fun r hr => ?_) fun a b => ?_
  · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hr
    exact ⟨v, rfl⟩
  · obtain ⟨r, hr, h₁, h₂⟩ := h a b
    obtain ⟨v, rfl⟩ := hY r hr
    rw [liveRow_of_mem (hY.mem_of_incompatible h)] at h₁
    rw [liveRow_of_mem (hY.mem_of_incompatible (incompatible_symm h))] at h₂
    exact ⟨N.label v, Finset.mem_image_of_mem _ (Finset.mem_univ v), h₁, h₂⟩

/-- **Theorem 2.4** of the source, for the matrices of an execution. -/
theorem RowsOn.mem_of_reachable (hG : IsGalledTree N) (hY : RowsOn N T D Y) {Q : Set E} (hQ : N.IsCycle Q) {i k : ι} (hi : N.site i ∈ Q) (hr : (incompatGraph Y).Reachable i k) : N.site k ∈ Q := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => exact hi
  | tail _ hab ih =>
    obtain ⟨Q', hQ', ha, hb⟩ := hY.exists_isCycle hab
    rwa [hG.eq_of_inter hQ hQ' ⟨_, ih, ha⟩] at hb

/-- **Lemma 2.3 of the source**, for the matrices of an execution: two conflicted pairs on one gall are in one component. -/
theorem RowsOn.reachable_of_cycle (hG : IsGalledTree N) (hY : RowsOn N T D Y) {w x : V} {p q : List E} (hc : N.IsCycleOn w x p q) {i j k l : ι}
    (hi : N.site i ∈ {e | e ∈ p ∨ e ∈ q}) (hj : N.site j ∈ {e | e ∈ p ∨ e ∈ q}) (hk : N.site k ∈ {e | e ∈ p ∨ e ∈ q}) (hl : N.site l ∈ {e | e ∈ p ∨ e ∈ q})
    (hij : Incompatible Y i j) (hkl : Incompatible Y k l) : (incompatGraph Y).Reachable i k := by
  refine lemma2_3_of_rows hG hc (D := {s | s ∈ D ∧ N.site s ∈ {e | e ∈ p ∨ e ∈ q}}) (fun s hs => hs.2) (fun r hr => ?_) ⟨hY.mem_of_incompatible hij, hi⟩
    ⟨hY.mem_of_incompatible (incompatible_symm hij), hj⟩ ⟨hY.mem_of_incompatible hkl, hk⟩ ⟨hY.mem_of_incompatible (incompatible_symm hkl), hl⟩ hij hkl
  obtain ⟨v, rfl⟩ := hY r hr
  exact ⟨v, fun s hs => liveRow_of_mem hs.1⟩

variable {w x w' x' : V} {p q p' q' : List E}

omit [Finite V] in
theorem coalescent_mem (hc : N.IsCycleOn w x p q) : w ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q} := by
  cases hpe : p with
  | nil => exact absurd hpe hc.ne_nil
  | cons f l =>
    have hsrc : N.src f = w := by
      have := hc.2.1
      rw [hpe] at this
      exact this.1
    exact Or.inl ⟨f, Or.inl (by simp), hsrc⟩

omit [Finite V] in
/-- A node of a recombination cycle other than its coalescent node has an arc of the cycle into it. -/
theorem exists_arc_of_mem (hc : N.IsCycleOn w x p q) {z : V} (hz : z ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}) (hzw : z ≠ w) : ∃ g' ∈ {e | e ∈ p ∨ e ∈ q}, N.tgt g' = z := by
  have hlast : ∀ {l : List E} {c d : List E}, l = c ++ d → N.IsPath w z c → (∀ e ∈ l, e ∈ {e | e ∈ p ∨ e ∈ q}) → ∃ g' ∈ {e | e ∈ p ∨ e ∈ q}, N.tgt g' = z := by
    intro l c d hl hcv hall
    have hcne : c ≠ [] := by
      rintro rfl
      exact hzw (show w = z from hcv).symm
    obtain ⟨c', a, rfl, -, ha⟩ := hcv.exists_last_arc hcne
    exact ⟨a, hall a (by rw [hl]; simp), ha⟩
  rcases cycle_mem_cases hc hz with rfl | ⟨c, d, hp', -, hcv⟩ | ⟨c, d, hq', -, hcv⟩
  · obtain ⟨a, -, ha, -, -, hax, -⟩ := cycle_last_arcs hc
    exact ⟨a, Or.inl ha, hax⟩
  · exact hlast hp' hcv fun e he => Or.inl he
  · exact hlast hq' hcv fun e he => Or.inr he

/-- A path into a gall enters it at the coalescent node: it can't enter at another node, for the arc would be on a recombination cycle sharing an arc with the gall. The two cases in the proof of Lemma 2.1 of the source. -/
theorem reach_coalescent_of_reach_mem (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) {u v : V} (hu : u ∉ N.blobVerts {e | e ∈ p ∨ e ∈ q})
    (hv : v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}) (h : N.Reach u v) : N.Reach u w := by
  obtain ⟨l, hl⟩ := h.exists_isPath
  obtain ⟨z, p₁, p₂, -, hp₁, -, hz, hf⟩ := hl.exists_first (fun y => y ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}) hv
  have hne : p₁ ≠ [] := by
    rintro rfl
    exact hu ((show u = z from hp₁) ▸ hz)
  obtain ⟨p', g, rfl, -, hg⟩ := hp₁.exists_last_arc hne
  have hgQ : g ∉ {e | e ∈ p ∨ e ∈ q} := fun h' => hf g (by simp) (Or.inl ⟨g, h', rfl⟩)
  have hzw : z = w := by
    by_contra hzw
    obtain ⟨g', hg', hgt⟩ := exists_arc_of_mem hc hz hzw
    have hne' : g ≠ g' := fun h' => hgQ (h' ▸ hg')
    obtain ⟨Q', hQ', hgQ', hg'Q'⟩ := exists_isCycle_of_tgt_eq hne' (hg.trans hgt.symm)
    have heq := hG.eq_of_inter ⟨w, x, p, q, hc, rfl⟩ hQ' ⟨g', hg', hg'Q'⟩
    exact hgQ (heq ▸ hgQ')
  rw [← hzw]
  exact hp₁.reach

/-- **Lemma 2.1 of the source**, along a path off a gall: what is below a node from which no node of the gall is reached has that node's states on the gall. -/
theorem label_of_reach_off (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) {u y : V} (hu : N.Reach u y) (hoff : ∀ v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}, ¬ N.Reach u v) {s : ι}
    (hs : N.site s ∈ {e | e ∈ p ∨ e ∈ q}) : N.label y s = N.label u s := by
  induction hu with
  | refl => rfl
  | tail hb hbc ih =>
    obtain ⟨f, rfl, rfl⟩ := hbc
    have hf : N.tgt f ∉ N.blobVerts {e | e ∈ p ∨ e ∈ q} := fun hm => hoff _ hm (hb.trans (reach_src_tgt f))
    exact (label_tgt_of_notMem hG hc hf hs).trans ih

omit [Finite V] in
/-- A removal that breaks the conflict between `i` and `j` removes the only row with its pair at `i, j`. -/
theorem exists_unique_row {r : ι → Bool} {i j : ι} (h₁ : Incompatible Y i j) (h₂ : ¬ Incompatible (Y.erase r) i j) : r ∈ Y ∧ ∀ ρ ∈ Y, ρ i = r i → ρ j = r j → ρ = r := by
  unfold Incompatible at h₂
  push Not at h₂
  obtain ⟨a, b, hab⟩ := h₂
  obtain ⟨ρ₀, hρ₀, h₃, h₄⟩ := h₁ a b
  have hρr : ρ₀ = r := by
    by_contra hne
    exact hab ρ₀ (Finset.mem_erase.2 ⟨hne, hρ₀⟩) h₃ h₄
  subst hρr
  refine ⟨hρ₀, fun ρ hρ h₅ h₆ => ?_⟩
  by_contra hne
  exact hab ρ (Finset.mem_erase.2 ⟨hne, hρ⟩) (h₅.trans h₃) (h₆.trans h₄)

/-- The core of Lemma 8.5 of the source. Two galls, the second not above the first. All the rows that have a mutation of the second gall are below its coalescent node, so they have one pair at two sites of the first gall (Lemma 2.1). So one row can't be needed for a conflict
on each. -/
theorem removal_two_galls (hG : IsGalledTree N) (hY : RowsOn N T D Y) (hc : N.IsCycleOn w x p q) (hc' : N.IsCycleOn w' x' p' q')
    (hoff : ∀ v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}, ¬ N.Reach w' v) {r : ι → Bool} {i j i' j' : ι} (hi : N.site i ∈ {e | e ∈ p ∨ e ∈ q}) (hj : N.site j ∈ {e | e ∈ p ∨ e ∈ q})
    (hi' : N.site i' ∈ {e | e ∈ p' ∨ e ∈ q'}) (hj' : N.site j' ∈ {e | e ∈ p' ∨ e ∈ q'}) (h₁ : Incompatible Y i j) (h₂ : ¬ Incompatible (Y.erase r) i j) (h₃ : Incompatible Y i' j')
    (h₄ : ¬ Incompatible (Y.erase r) i' j') : False := by
  have hiD := hY.mem_of_incompatible h₁
  have hjD := hY.mem_of_incompatible (incompatible_symm h₁)
  have hiD' := hY.mem_of_incompatible h₃
  have hjD' := hY.mem_of_incompatible (incompatible_symm h₃)
  obtain ⟨hrY, hu⟩ := exists_unique_row h₁ h₂
  obtain ⟨-, hu'⟩ := exists_unique_row h₃ h₄
  have hbelow : ∀ ρ ∈ Y, (ρ i' ≠ N.label N.root i' ∨ ρ j' ≠ N.label N.root j') → ρ i = N.label w' i ∧ ρ j = N.label w' j := by
    intro ρ hρ hne
    obtain ⟨y, rfl⟩ := hY ρ hρ
    rw [liveRow_of_mem hiD, liveRow_of_mem hjD]
    rw [liveRow_of_mem hiD', liveRow_of_mem hjD'] at hne
    have hreach : N.Reach w' y := by
      rcases hne with h | h
      · exact (cycle_reach_src hc' hi').trans ((reach_src_tgt _).trans (N.reach_of_label_ne h))
      · exact (cycle_reach_src hc' hj').trans ((reach_src_tgt _).trans (N.reach_of_label_ne h))
    exact ⟨label_of_reach_off hG hc hreach hoff hi, label_of_reach_off hG hc hreach hoff hj⟩
  by_cases hrS : r i' = N.label N.root i' ∧ r j' = N.label N.root j'
  · -- `r` is the only row with the pair of the root at `i', j'`, and the others have one pair at `i, j`
    have hpair : ∀ p₁ p₂ q₁ q₂ : Bool, ∃ a b : Bool, (a ≠ p₁ ∨ b ≠ p₂) ∧ (a ≠ q₁ ∨ b ≠ q₂) := by decide
    obtain ⟨a, b, ha, hb⟩ := hpair (N.label w' i) (N.label w' j) (r i) (r j)
    obtain ⟨ρ, hρ, h₅, h₆⟩ := h₁ a b
    have hρr : ρ ≠ r := by
      rintro rfl
      rcases hb with h | h
      · exact h h₅.symm
      · exact h h₆.symm
    have hne : ρ i' ≠ N.label N.root i' ∨ ρ j' ≠ N.label N.root j' := by
      by_contra hcon
      push Not at hcon
      exact hρr (hu' ρ hρ (hcon.1.trans hrS.1.symm) (hcon.2.trans hrS.2.symm))
    obtain ⟨h₇, h₈⟩ := hbelow ρ hρ hne
    rcases ha with h | h
    · exact h (h₅.symm.trans h₇)
    · exact h (h₆.symm.trans h₈)
  · -- `r` has a mutation of the second gall, and another row with one has the same pair at `i, j`
    have hrne : r i' ≠ N.label N.root i' ∨ r j' ≠ N.label N.root j' := by
      by_contra hcon
      push Not at hcon
      exact hrS hcon
    obtain ⟨hπ₁, hπ₂⟩ := hbelow r hrY hrne
    have hpair : ∀ p₁ p₂ q₁ q₂ : Bool, ∃ a b : Bool, (a ≠ p₁ ∨ b ≠ p₂) ∧ (a ≠ q₁ ∨ b ≠ q₂) := by decide
    obtain ⟨a, b, ha, hb⟩ := hpair (N.label N.root i') (N.label N.root j') (r i') (r j')
    obtain ⟨ρ, hρ, h₅, h₆⟩ := h₃ a b
    have hρr : ρ ≠ r := by
      rintro rfl
      rcases hb with h | h
      · exact h h₅.symm
      · exact h h₆.symm
    have hne : ρ i' ≠ N.label N.root i' ∨ ρ j' ≠ N.label N.root j' := by
      rcases ha with h | h
      · exact Or.inl (by rwa [h₅])
      · exact Or.inr (by rwa [h₆])
    obtain ⟨h₇, h₈⟩ := hbelow ρ hρ hne
    exact hρr (hu ρ hρ (h₇.trans hπ₁.symm) (h₈.trans hπ₂.symm))

/-- **Lemma 8.5** (`ext:lem8_5`) of the source, in the part that its proof of Theorem 8.2 uses. "Edges in `G` are removed from at most one non-trivial connected component": two conflicts broken by the removal of one row are in one component of the conflict graph. They are on one gall, or
the removal would have to break a conflict on each of two galls (`removal_two_galls`). If they are on one, Lemma 2.3 of the source puts them in one component. -/
theorem lemma8_5 (hG : IsGalledTree N) (hY : RowsOn N T D Y) {r : ι → Bool} {i j i' j' : ι} (h₁ : Incompatible Y i j) (h₂ : ¬ Incompatible (Y.erase r) i j)
    (h₃ : Incompatible Y i' j') (h₄ : ¬ Incompatible (Y.erase r) i' j') : (incompatGraph Y).Reachable i i' := by
  obtain ⟨Q, hQ, hi, hj⟩ := hY.exists_isCycle h₁
  obtain ⟨Q', hQ', hi', hj'⟩ := hY.exists_isCycle h₃
  by_cases hQQ : Q' = Q
  · subst hQQ
    obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
    exact hY.reachable_of_cycle hG hc hi hj hi' hj' h₁ h₃
  · exfalso
    have hdisj := (hG Q hQ).2 Q' hQ' hQQ
    obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
    obtain ⟨w', x', p', q', hc', rfl⟩ := hQ'
    by_cases hoff : ∀ v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}, ¬ N.Reach w' v
    · exact removal_two_galls hG hY hc hc' hoff hi hj hi' hj' h₁ h₂ h₃ h₄
    · refine removal_two_galls hG hY hc' hc (fun v hv hr => hoff ?_) hi' hj' hi hj h₃ h₄ h₁ h₂
      -- if each coalescent node reached the other gall, they would reach each other
      intro u hu hr'
      have hw' : w' ∉ N.blobVerts {e | e ∈ p ∨ e ∈ q} := fun hm => Set.disjoint_left.1 hdisj hm (coalescent_mem hc')
      have hw : w ∉ N.blobVerts {e | e ∈ p' ∨ e ∈ q'} := fun hm => Set.disjoint_left.1 hdisj (coalescent_mem hc) hm
      have h₅ := reach_coalescent_of_reach_mem hG hc hw' hu hr'
      have h₆ := reach_coalescent_of_reach_mem hG hc' hw hv hr
      have heq : w' = w := Reach.antisymm h₅ h₆
      exact hw' (heq ▸ coalescent_mem hc)

omit [Finite V] in
theorem incompatGraph_mono {Y' : Finset (ι → Bool)} (h : Y' ⊆ Y) : incompatGraph Y' ≤ incompatGraph Y := fun i j hij a b => by
  obtain ⟨r, hr, h₁, h₂⟩ := hij a b
  exact ⟨r, h hr, h₁, h₂⟩

/-- If all the edges lost from `G` to `G'` are in one component of `G`, then `G'` has at most one non-trivial component fewer. -/
theorem card_cent_le_add_one [Finite ι] {G G' : SimpleGraph ι} (hle : G' ≤ G)
    (h : ∀ i j i' j', G.Adj i j → ¬ G'.Adj i j → G.Adj i' j' → ¬ G'.Adj i' j' → G.Reachable i i') : Nat.card (Cent G) ≤ Nat.card (Cent G') + 1 := by
  have : Finite G'.ConnectedComponent := Finite.of_surjective G'.connectedComponentMk fun c => c.exists_rep
  choose rep nb hrep hadj using fun c : Cent G => Cent.exists_adj c
  -- a component with a lost edge goes to `none`, and the others stay
  have hedge : ∀ c : Cent G, (¬ ∃ i j, i ∈ c.1.supp ∧ G.Adj i j ∧ ¬ G'.Adj i j) → G'.Adj (rep c) (nb c) := by
    intro c hc
    by_contra hno
    exact hc ⟨_, _, hrep c, hadj c, hno⟩
  let f : Cent G → Option (Cent G') := fun c =>
    if hc : ∃ i j, i ∈ c.1.supp ∧ G.Adj i j ∧ ¬ G'.Adj i j then none else some ⟨_, nontrivial_of_adj (hedge c hc)⟩
  have hinj : Function.Injective f := by
    intro c c' hcc
    by_cases hc : ∃ i j, i ∈ c.1.supp ∧ G.Adj i j ∧ ¬ G'.Adj i j <;> by_cases hc' : ∃ i j, i ∈ c'.1.supp ∧ G.Adj i j ∧ ¬ G'.Adj i j
    · obtain ⟨i, j, hi, hij, hno⟩ := hc
      obtain ⟨i', j', hi', hij', hno'⟩ := hc'
      have hr := h i j i' j' hij hno hij' hno'
      exact Subtype.ext (hi.symm.trans ((SimpleGraph.ConnectedComponent.eq.2 hr).trans hi'))
    · simp only [f, dite_eq_left hc, dite_eq_right hc', reduceCtorEq] at hcc
    · simp only [f, dite_eq_right hc, dite_eq_left hc', reduceCtorEq] at hcc
    · simp only [f, dite_eq_right hc, dite_eq_right hc', Option.some.injEq, Subtype.mk.injEq] at hcc
      have hr' : G'.Reachable (rep c) (rep c') := SimpleGraph.ConnectedComponent.exact hcc
      have hr : G.Reachable (rep c) (rep c') := hr'.mono hle
      exact Subtype.ext ((hrep c).symm.trans ((SimpleGraph.ConnectedComponent.eq.2 hr).trans (hrep c')))
  calc Nat.card (Cent G) ≤ Nat.card (Option (Cent G')) := Nat.card_le_card_of_injective f hinj
    _ = Nat.card (Cent G') + 1 := Finite.card_option

/-- **Lemma 8.6** (`ext:lem8_6`) of the source, in the part about the graph: "the conflict graph for the remaining sequences has either `k` or `k - 1` non-trivial connected components". The source goes on to say that a reduced galled tree with that many galls derives the remaining sequences.
That part isn't stated here, and isn't needed: see the head of this file. -/
theorem lemma8_6 [Finite ι] (hG : IsGalledTree N) (hY : RowsOn N T D Y) (r : ι → Bool) :
    Nat.card (Cent (incompatGraph (Y.erase r))) ≤ Nat.card (Cent (incompatGraph Y)) ∧ Nat.card (Cent (incompatGraph Y)) ≤ Nat.card (Cent (incompatGraph (Y.erase r))) + 1 := by
  have hY' : RowsOn N T D (Y.erase r) := hY.mono (Finset.erase_subset _ _)
  have hle : incompatGraph (Y.erase r) ≤ incompatGraph Y := incompatGraph_mono (Finset.erase_subset _ _)
  refine ⟨?_, card_cent_le_add_one hle fun i j i' j' h₁ h₂ h₃ h₄ => lemma8_5 hG hY h₁ h₂ h₃ h₄⟩
  -- two non-trivial components after the removal are on two galls, or Lemma 2.3 joins them
  have : Finite (incompatGraph Y).ConnectedComponent := Finite.of_surjective (incompatGraph Y).connectedComponentMk fun c => c.exists_rep
  choose rep nb hrep hadj using fun c : Cent (incompatGraph (Y.erase r)) => Cent.exists_adj c
  refine Nat.card_le_card_of_injective (fun c => (⟨_, nontrivial_of_adj (hle (hadj c))⟩ : Cent (incompatGraph Y))) fun c c' hcc => ?_
  have hcc' := congrArg Subtype.val hcc
  have hr : (incompatGraph Y).Reachable (rep c) (rep c') := SimpleGraph.ConnectedComponent.exact hcc'
  obtain ⟨Q, hQ, hi, hj⟩ := hY'.exists_isCycle (hadj c)
  have hi' : N.site (rep c') ∈ Q := hY.mem_of_reachable hG hQ hi hr
  obtain ⟨Q', hQ', hi'', hj'⟩ := hY'.exists_isCycle (hadj c')
  have heq := hG.eq_of_inter hQ hQ' ⟨_, hi', hi''⟩
  rw [heq] at hj'
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  have hreach := hY'.reachable_of_cycle hG hc hi hj hi' hj' (hadj c) (hadj c')
  exact Subtype.ext ((hrep c).symm.trans ((SimpleGraph.ConnectedComponent.eq.2 hreach).trans (hrep c')))

omit [Finite V] in
/-- **Lemma 8.1** (`ext:lem8_1`) of the source. "If there is only a single `1` entry in column `c` in `M`, then site `c` cannot be on a gall in `T`": a site on a gall of a reduced galled tree is conflicted, and "any conflicted site must have at least two `1`'s in its column". -/
theorem lemma8_1 {M : Finset (ι → Bool)} {G : SimpleGraph ι} {S : ι → Bool} (h : IsReducedGalledTree N G) (hG : G = conflictGraph S M) {Q : Set E} (hQ : N.IsCycle Q) {i : ι} (hi : N.site i ∈ Q) : ones S M i ≠ 1 := by
  obtain ⟨j, hj⟩ := h.no_unconflicted Q hQ i hi
  rw [hG] at hj
  have hne : ∀ b : Bool, (!b) ≠ b := fun b => by cases b <;> simp
  obtain ⟨r, hr, h₁, h₂⟩ := hj (!S i) (S j) (Or.inl (hne _))
  obtain ⟨r', hr', h₁', h₂'⟩ := hj (!S i) (!S j) (Or.inl (hne _))
  have hrr : r ≠ r' := by
    rintro rfl
    exact hne _ (h₂'.symm.trans h₂)
  intro hone
  have hmem : ∀ {s : ι → Bool}, s ∈ M → s i = !S i → s ∈ M.filter fun r => r i ≠ S i := fun {s} hs hs' =>
    Finset.mem_filter.2 ⟨hs, by rw [hs']; exact hne _⟩
  exact hrr (Finset.card_le_one.1 hone.le r (hmem hr h₁) r' (hmem hr' h₁'))

end Removal

/-! ### Any execution has a removal for each component -/

section Execution

variable {N : Network ι V E} [Finite V] {T : ι → Bool}

/-- **Theorem 8.2** of the source, the induction. Along an execution on rows of a galled tree, a column deletion changes nothing in the graph, and a removal lowers the number of non-trivial components by one at most. The rows `E` are either none, for the
incompatibility graph, or the root's sequence, for the conflict graph relative to it. -/
theorem card_cent_le_of_elim [Finite ι] (hG : IsGalledTree N) {R₀ : Finset (ι → Bool)} (hR₀ : ∀ r ∈ R₀, r = T ∧ T = N.ancestral) {X : Finset (ι → Bool)} {t : ℕ} (h : Elim T X t) :
    ∀ {D : Set ι}, RowsOn N T D X → Nat.card (Cent (incompatGraph (X ∪ R₀))) ≤ t := by
  have hroot : ∀ {D : Set ι} {X : Finset (ι → Bool)}, RowsOn N T D X → RowsOn N T D (X ∪ R₀) := by
    intro D X hX r hr
    rcases Finset.mem_union.1 hr with hr | hr
    · exact hX r hr
    · obtain ⟨rfl, hT⟩ := hR₀ r hr
      refine ⟨N.root, ?_⟩
      funext i
      by_cases hi : i ∈ D
      · simp only [liveRow, hi, ite_true]
        exact congrFun hT i
      · simp [liveRow, hi]
  induction h with
  | @eliminated X hX =>
    intro D _
    have hempty : IsEmpty (Cent (incompatGraph (X ∪ R₀))) := ⟨fun c => by
      obtain ⟨i, j, -, hij⟩ := Cent.exists_adj c
      obtain ⟨r, hr, h₁, -⟩ := hij (!T i) true
      have hrT : r = T := by
        rcases Finset.mem_union.1 hr with hr | hr
        · exact hX r hr
        · exact (hR₀ r hr).1
      rw [hrT] at h₁
      simp at h₁⟩
    simp
  | @columnDeletion X i k hi _ ih =>
    intro D hX
    have hX' : RowsOn N T (D \ {i}) (X.image (maskCol T i)) := by
      intro r hr
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hr
      obtain ⟨v, rfl⟩ := hX s hs
      exact ⟨v, maskCol_liveRow _ _ _ _⟩
    have hle : ones T (X ∪ R₀) i ≤ 1 := by
      rw [← hi]
      refine Finset.card_le_card fun r hr => ?_
      obtain ⟨hr₁, hr₂⟩ := Finset.mem_filter.1 hr
      rcases Finset.mem_union.1 hr₁ with h' | h'
      · exact Finset.mem_filter.2 ⟨h', hr₂⟩
      · rw [(hR₀ r h').1] at hr₂
        exact absurd rfl hr₂
    have himg : X.image (maskCol T i) ∪ R₀ = (X ∪ R₀).image (maskCol T i) := by
      rw [Finset.image_union]
      congr 1
      ext r
      constructor
      · intro hr
        refine Finset.mem_image.2 ⟨r, hr, ?_⟩
        rw [(hR₀ r hr).1]
        funext j
        by_cases hj : j = i
        · simp [maskCol, hj]
        · simp [maskCol, hj]
      · intro hr
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hr
        have hsT := (hR₀ s hs).1
        have heq : maskCol T i s = s := by
          rw [hsT]
          funext j
          by_cases hj : j = i
          · simp [maskCol, hj]
          · simp [maskCol, hj]
        rwa [heq]
    have := ih hX'
    rwa [himg, incompatGraph_image_maskCol hle] at this
  | @sequenceRemoval X r k _ _ _ ih =>
    intro D hX
    have hk := ih (hX.mono (Finset.erase_subset _ _))
    by_cases hrR : r ∈ R₀
    · have heq : X.erase r ∪ R₀ = X ∪ R₀ := by
        ext s
        simp only [Finset.mem_union, Finset.mem_erase]
        constructor
        · rintro (⟨-, h'⟩ | h')
          · exact Or.inl h'
          · exact Or.inr h'
        · rintro (h' | h')
          · by_cases hsr : s = r
            · exact Or.inr (hsr ▸ hrR)
            · exact Or.inl ⟨hsr, h'⟩
          · exact Or.inr h'
      rw [heq] at hk
      omega
    · have heq : X.erase r ∪ R₀ = (X ∪ R₀).erase r := by
        ext s
        simp only [Finset.mem_union, Finset.mem_erase]
        constructor
        · rintro (⟨hne, h'⟩ | h')
          · exact ⟨hne, Or.inl h'⟩
          · exact ⟨fun hsr => hrR (hsr ▸ h'), Or.inr h'⟩
        · rintro ⟨hne, h' | h'⟩
          · exact Or.inl ⟨hne, h'⟩
          · exact Or.inr h'
      rw [heq] at hk
      have := (lemma8_6 hG (hroot hX) r).2
      omega

variable {M : Finset (ι → Bool)}

omit [Finite V] in
/-- A network deriving `M` has rows on all the columns. -/
theorem rowsOn_univ (hD : N.Derives M) (T : ι → Bool) : RowsOn N T Set.univ M := by
  intro r hr
  obtain ⟨v, rfl⟩ := hD.displays r hr
  exact ⟨v, (liveRow_univ _ _).symm⟩

/-- Any execution on a matrix that has a galled tree has one removal for each non-trivial component of the incompatibility graph, whatever the sequence it is relative to. -/
theorem card_cent_incompatGraph_le [Finite ι] (hG : IsGalledTree N) (hD : N.Derives M) {T : ι → Bool} {t : ℕ} (h : Elim T M t) : Nat.card (Cent (incompatGraph M)) ≤ t := by
  have := card_cent_le_of_elim hG (R₀ := ∅) (by simp) h (rowsOn_univ hD T)
  rwa [Finset.union_empty] at this

/-- Any execution relative to the ancestral sequence of a galled tree has one removal for each non-trivial component of the conflict graph. -/
theorem card_cent_conflictGraph_le [Finite ι] (hG : IsGalledTree N) (hD : N.Derives M) {t : ℕ} (h : Elim N.ancestral M t) : Nat.card (Cent (conflictGraph N.ancestral M)) ≤ t := by
  have := card_cent_le_of_elim hG (R₀ := {N.ancestral}) (by simp) h (rowsOn_univ hD _)
  rwa [conflictGraph_eq_incompatGraph_addRow, addRow, Finset.insert_eq, Finset.union_comm]

/-- **Theorem 8.2** (`ext:thm8_2`) of the source. "Let `M` be a set of sequences that can be derived on a reduced galled-tree using `k` galls. Then `B ≥ k`": every execution has at least `k` removals. See the head of this file for the difference from the source. -/
theorem theorem8_2 [Finite ι] (h : IsReducedGalledTree N (conflictGraph N.ancestral M)) (hD : N.Derives M) {t : ℕ} (he : Elim N.ancestral M t) : N.recombCount ≤ t := by
  rw [h.recombCount_eq hD]
  exact card_cent_conflictGraph_le h.galled hD he

/-- `B ≥ k`, for the minimum `B`. -/
theorem le_minRemovals [Finite ι] (h : IsReducedGalledTree N (conflictGraph N.ancestral M)) (hD : N.Derives M) : N.recombCount ≤ minRemovals N.ancestral M := by
  obtain ⟨k, -, hE⟩ := theorem8_1 hD
  exact theorem8_2 h hD (Nat.sInf_mem (s := {k | Elim N.ancestral M k}) ⟨k, hE⟩)

end Execution

/-! ### `R` and `R_S` -/

section Optimal

variable [LinearOrder ι] [Finite ι] {N : Network ι V E} [Finite V] {M : Finset (ι → Bool)}

omit [LinearOrder ι] in
/-- If `M` can be derived on a galled tree, no network deriving `M`, with any ancestral sequence and any number of crossovers, has fewer recombination nodes than `G(M)` has non-trivial components. -/
theorem card_cent_incompatGraph_le_recombCount {V' E' : Type*} [Finite V'] (hG : IsGalledTree N) (hD : N.Derives M) (N' : Network ι V' E') (hD' : N'.Derives M) :
    Nat.card (Cent (incompatGraph M)) ≤ N'.recombCount := by
  obtain ⟨k, hk, hE⟩ := theorem8_1 hD'
  exact (card_cent_incompatGraph_le hG hD hE).trans hk

omit [LinearOrder ι] in
/-- If `M` can be derived on a galled tree with ancestral sequence `S`, no network deriving `M` with that sequence, with any number of crossovers, has fewer recombination nodes than `G_S(M)` has non-trivial components. -/
theorem card_cent_conflictGraph_le_recombCount {V' E' : Type*} [Finite V'] (hG : IsGalledTree N) (hD : N.Derives M) (N' : Network ι V' E') (hD' : N'.Derives M) (hS : N'.ancestral = N.ancestral) :
    Nat.card (Cent (conflictGraph N.ancestral M)) ≤ N'.recombCount := by
  obtain ⟨k, hk, hE⟩ := theorem8_1 hD'
  rw [hS] at hE
  exact (card_cent_conflictGraph_le hG hD hE).trans hk

/-- The lower bound for `R`: if `M` can be derived on a galled tree, then `G(M)` has at most `R c M` non-trivial components, in any crossover model `c`. -/
theorem card_cent_incompatGraph_le_R (hG : IsGalledTree N) (hD : N.Derives M) (c : Crossover) : Nat.card (Cent (incompatGraph M)) ≤ R c M := by
  obtain ⟨a, b, N', -, hD', hk⟩ := Nat.sInf_mem (recombSet_nonempty c hD.nonempty)
  exact (card_cent_incompatGraph_le_recombCount hG hD N' hD').trans_eq hk

/-- The lower bound for `R_S`: if `M` can be derived on a galled tree with ancestral sequence `S`, then `G_S(M)` has at most `RS c S M` non-trivial components, in any crossover model `c`. -/
theorem card_cent_conflictGraph_le_RS (hG : IsGalledTree N) (hD : N.Derives M) (c : Crossover) : Nat.card (Cent (conflictGraph N.ancestral M)) ≤ RS c N.ancestral M := by
  obtain ⟨a, b, N', -, hD', hS, hk⟩ := Nat.sInf_mem (rootedRecombSet_nonempty c N.ancestral hD.nonempty)
  exact (card_cent_conflictGraph_le_recombCount hG hD N' hD' hS).trans_eq hk

variable [Finite E]

/-- **Theorem 8.3** (`ext:thm8_3`) of the source. "When `M` can be derived on a reduced galled-tree using `k` galls, then `B = R_min = k`. Moreover, even if we allow a multiple-crossover event at any recombination node, there is no phylogenetic network deriving `M` that uses fewer than `k` recombination nodes. Hence, a reduced
galled-tree for `M` is optimal in this stronger way as well." Here `k` is the number of recombination nodes of `N`, which is the number of its galls (`IsGalledTree.card_recomb_eq`), and `R_min` is `RS c S M` in the model `c` of `N`, the source's being single crossovers, and multiple crossovers
being the stronger form. -/
theorem theorem8_3 (h : IsReducedGalledTree N (conflictGraph N.ancestral M)) (hD : N.Derives M) {c : Crossover} (hc : N.Obeys c) :
    minRemovals N.ancestral M = N.recombCount ∧ RS c N.ancestral M = N.recombCount ∧ RS .multiple N.ancestral M = N.recombCount := by
  have hlow : ∀ c', N.recombCount ≤ RS c' N.ancestral M := fun c' => by
    rw [h.recombCount_eq hD]
    exact card_cent_conflictGraph_le_RS h.galled hD c'
  exact ⟨le_antisymm (minRemovals_le_recombCount hD) (le_minRemovals h hD), le_antisymm (RS_le_recombCount N hc hD rfl) (hlow c),
    le_antisymm (RS_le_recombCount N trivial hD rfl) (hlow _)⟩

/-- **Gusfield et al. 2007, line 381**, the count (`g:reduced_optimal_rooted`): a reduced galled tree with ancestral sequence `S` minimizes the number of recombinations over all networks for `M` with that sequence, even if they use multiple crossovers. -/
theorem reducedGalledTree_recombCount_eq_RS (h : IsReducedGalledTree N (conflictGraph N.ancestral M)) (hD : N.Derives M) {c : Crossover} (hc : N.Obeys c) :
    N.recombCount = RS c N.ancestral M ∧ N.recombCount = RS .multiple N.ancestral M :=
  ⟨(theorem8_3 h hD hc).2.1.symm, (theorem8_3 h hD hc).2.2.symm⟩

/-- **Gusfield et al. 2007, line 381**, the count, unrooted (`g:reduced_optimal`): a galled tree reduced for `G(M)` minimizes the number of recombinations over all networks for `M`, with any ancestral sequence, even if they use multiple crossovers.

The source treats a known ancestral sequence. It says of the case where the sequence isn't given: "there are examples where one can find a different ancestral sequence that allows a galled-tree for `M`, using fewer than `R_min` recombinations", which is about `R_S` for one `S`, and doesn't touch
this statement. The same proof gives it, since a column with at most one `1` relative to any sequence is in no incompatibility. Line 381 also cites Gusfield 2005 for this case, which wasn't read. -/
theorem reducedGalledTree_recombCount_eq_R (h : IsReducedGalledTree N (incompatGraph M)) (hD : N.Derives M) {c : Crossover} (hc : N.Obeys c) :
    N.recombCount = R c M ∧ N.recombCount = R .multiple M := by
  have hlow : ∀ c', N.recombCount ≤ R c' M := fun c' => by
    rw [h.recombCount_eq_incompatGraph hD]
    exact card_cent_incompatGraph_le_R h.galled hD c'
  exact ⟨le_antisymm (hlow c) (R_le_recombCount N hc hD), le_antisymm (hlow _) (R_le_recombCount N trivial hD)⟩

/-- **Gusfield et al. 2007, line 381** (`g:line381_rooted`), with ancestral sequence `S`. "If our goal is to minimize the number of recombination nodes (events) is it effective to restrict ourselves [to fully-decomposed networks]? The answer is yes when `M` can be derived on a galled-tree, even if the galled-tree must only use
single-crossover recombinations, but any competing phylogenetic network is allowed to use multiple-crossovers": a reduced galled tree makes `M` S-min decomposable, in its model and for multiple crossovers. -/
theorem line381_rooted (h : IsReducedGalledTree N (conflictGraph N.ancestral M)) (hD : N.Derives M) {c : Crossover} (hc : N.Obeys c) :
    SMinDecomposable c N.ancestral M ∧ SMinDecomposable .multiple N.ancestral M := by
  obtain ⟨a, b, N', eV, eE, hiso⟩ := N.exists_fin_iso
  obtain ⟨i₁, i₂, i₃, i₄, i₅⟩ := hiso.invariants
  have hfd := h.isFullyDecomposedFor_conflictGraph hD
  obtain ⟨h₁, h₂⟩ := reducedGalledTree_recombCount_eq_RS h hD hc
  exact ⟨⟨a, b, N', (i₂ c).2 hc, (i₃ M).2 hD, i₄, (i₅ _).2 hfd, i₁.trans h₁⟩, ⟨a, b, N', (i₂ _).2 trivial, (i₃ M).2 hD, i₄, (i₅ _).2 hfd, i₁.trans h₂⟩⟩

/-- **Gusfield et al. 2007, line 381** (`g:line381`), unrooted: a galled tree reduced for `G(M)` makes `M` min decomposable, in its model and for multiple crossovers. The existence of such a tree is `exists_isReducedGalledTree_incompatGraph`, and so `minDecomposable_of_isGalledTree` is the statement for any galled tree. -/
theorem line381 (h : IsReducedGalledTree N (incompatGraph M)) (hD : N.Derives M) {c : Crossover} (hc : N.Obeys c) :
    MinDecomposable c M ∧ MinDecomposable .multiple M := by
  obtain ⟨a, b, N', eV, eE, hiso⟩ := N.exists_fin_iso
  obtain ⟨i₁, i₂, i₃, -, i₅⟩ := hiso.invariants
  have hfd := h.isFullyDecomposedFor_incompatGraph hD
  obtain ⟨h₁, h₂⟩ := reducedGalledTree_recombCount_eq_R h hD hc
  exact ⟨⟨a, b, N', (i₂ c).2 hc, (i₃ M).2 hD, (i₅ _).2 hfd, i₁.trans h₁⟩, ⟨a, b, N', (i₂ _).2 trivial, (i₃ M).2 hD, (i₅ _).2 hfd, i₁.trans h₂⟩⟩

end Optimal

end GusfieldEtAl2004
