module

public import External.AllmanBanosRhodes2019.QuartetContract

/-!
# The network `Q̃` on a set of four taxa with no cut-edge split

On a binary level-1 network, four taxa of `q` in distinct blocks at a blob, one of them below its reticulation, are a `4₁`-cycle
(`not_isTreelike_iff`). This module proves what `Q̃` is there: the literal cycle on four vertices, with a taxon at each.

* `cycleSize_eq_four`, `cycleSize_le_three_of_not_sameBlob`: the cycle has size four, and any other kept cycle is contracted.
* `exists_cut_off`: every other kept edge has a cut, in the graph without one reticulation arc.
* `card_tildeE`: that graph is a tree, so that the contracted graph has as many edges as vertices.
* `nodeDegree_eq`: by the sum of the degrees, the taxa have degree one, the attachments three, and the others two.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open TOBQMC TOBQMC.Level1
open AllmanEtAl2023 AllmanEtAl2023.TreeSuppression
open scoped Classical

namespace External.AllmanBanosRhodes2019.Quartet

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {q : Finset X} {a : X} {h T : V} {k₁ k₂ : E} {pL pR : List E}

/-! ### The cycle -/

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- What is in a blob is connected to it off another. -/
theorem blockWalk_of_sameBlob {h' w : V} (hb : ¬ N.graph.blobSetoid h h') (hw : N.graph.blobSetoid h' w) :
    BlockWalk N h h' w := by
  have hoff : ∀ {z : V}, N.graph.blobSetoid h' z → ¬ N.graph.blobSetoid h z := fun hz hz' =>
    hb (sameBlob_trans hz' (sameBlob_symm hz))
  induction hw with
  | refl => exact .refl
  | @tail c d hc hstep ih =>
    have hd : N.graph.blobSetoid h' d := hc.tail hstep
    obtain ⟨f, -, hf⟩ := hstep
    exact ih.tail ⟨hoff hc, hoff hd, f, hf⟩

section Frame

variable (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (F : CycleFrame N q a h h T k₁ k₂ pL pR)
include hN hBin hLevel F

omit [Fintype X] [DecidableEq X] in
theorem frame_hQ : IsQuartetCycle N q h := by
  refine (isQuartetCycle_iff hN hBin hLevel F.two_le).2 ⟨⟨a, F.mem, F.below⟩, ?_⟩
  obtain ⟨c, hc, hne⟩ := exists_mem_ne (by rw [F.card]; norm_num : 1 < #q) a
  exact ⟨c, hc, F.only c hc hne⟩

omit [Fintype X] in
/-- Taxa of `q` with one attachment are equal. -/
theorem frame_eq_of_attachment {x y : X} (hx : x ∈ q) (hy : y ∈ q) {b : V} (hxb : IsAttachment N h x b)
    (hyb : IsAttachment N h y b) : x = y := by
  by_contra hne
  exact F.distinct x hx y hy hne (IsAttachment.blockWalk_of_eq hN hBin hLevel F.two_le F.cycle hxb hyb)

/-- **The cycle has size four.** -/
theorem cycleSize_eq_four : cycleSize N q h = 4 := by
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl F.two_le
  have hex : ∀ z, ∃ b, IsAttachment N h z b := fun z => exists_isAttachment hN (hx' z)
  choose att hatt using hex
  have hQ := frame_hQ hN hBin hLevel F
  refine le_antisymm (cycleSize_le_four hN hBin hLevel F.card hQ) ?_
  rw [cycleSize_eq hN hBin hLevel hQ]
  have hinj : Set.InjOn att (q : Set X) := fun x hx y hy hxy =>
    frame_eq_of_attachment hN hBin hLevel F (mem_coe.1 hx) (mem_coe.1 hy) (hatt x) (hxy ▸ hatt y)
  have hsub : att '' (q : Set X) ⊆ {u | ∃ z ∈ q, IsAttachment N h z u} := by
    rintro u ⟨z, hz, rfl⟩
    exact ⟨z, mem_coe.1 hz, hatt z⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hinj.ncard_image, Set.ncard_coe_finset, F.card] at this
  exact this

omit hBin in
/-- The contracted edges are off the blob. -/
theorem contracted_off_blob (hBin : N.IsBinary) {f : E} (hf : f ∈ contractedArcs N q) :
    ¬ N.graph.blobSetoid h (N.graph.source f) ∧ ¬ N.graph.blobSetoid h (N.graph.target f) := by
  obtain ⟨h', hQ, hs, hb⟩ := hf
  obtain ⟨hb₁, hb₂⟩ := mem_blobArcs_iff.1 hb
  have key : ∀ {w : V}, N.graph.blobSetoid h' w → ¬ N.graph.blobSetoid h w := by
    intro w hw hw'
    have heq : h = h' := reticulation_unique hN hLevel (v := h) .refl F.two_le (sameBlob_trans hw' (sameBlob_symm hw)) hQ.1
    rw [← heq, cycleSize_eq_four hN hBin hLevel F] at hs
    omega
  exact ⟨key hb₁, key hb₂⟩

/-- **Any other kept cycle is contracted**: its blob is in one block at the cycle, and the three taxa or more outside that block are in
one block at it. -/
theorem cycleSize_le_three_of_not_sameBlob {h' : V} (hb : ¬ N.graph.blobSetoid h h') (hQ' : IsQuartetCycle N q h') :
    cycleSize N q h' ≤ 3 := by
  by_contra hc
  have hd : ∀ {x y : X}, x ∈ q → y ∈ q → x ≠ y → ¬ BlockWalk N h' (N.leaf x) (N.leaf y) := fun hx hy hxy =>
    not_blockWalk_of_four_le hN hBin hLevel F.card hQ' (by omega) hx hy hxy
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl F.two_le
  -- two taxa outside the block of `h'`
  obtain ⟨y, z, hy, hz, hyz, hyB, hzB⟩ : ∃ y z, y ∈ q ∧ z ∈ q ∧ y ≠ z ∧ ¬ BlockWalk N h h' (N.leaf y) ∧ ¬ BlockWalk N h h' (N.leaf z) := by
    have hle : #(q.filter fun x => BlockWalk N h h' (N.leaf x)) ≤ 1 := by
      refine card_le_one.2 fun x hx y hy => ?_
      obtain ⟨hxq, hxB⟩ := mem_filter.1 hx
      obtain ⟨hyq, hyB⟩ := mem_filter.1 hy
      by_contra hne
      exact F.distinct x hxq y hyq hne (blockWalk_trans (blockWalk_symm hxB) hyB)
    have hcard := card_filter_add_card_filter_not (s := q) fun x => BlockWalk N h h' (N.leaf x)
    rw [F.card] at hcard
    obtain ⟨y, hy, z, hz, hyz⟩ := one_lt_card.1 (show 1 < #(q.filter fun x => ¬ BlockWalk N h h' (N.leaf x)) by omega)
    exact ⟨y, z, (mem_filter.1 hy).1, (mem_filter.1 hz).1, hyz, (mem_filter.1 hy).2, (mem_filter.1 hz).2⟩
  -- each is in one block at `h'` with the reticulation `h`
  have hoffh' : ∀ {w : V}, N.graph.blobSetoid h w → ¬ N.graph.blobSetoid h' w := fun hw hw' =>
    hb (sameBlob_trans hw (sameBlob_symm hw'))
  have key : ∀ {x : X}, ¬ BlockWalk N h h' (N.leaf x) → BlockWalk N h' (N.leaf x) h := by
    intro x hxB
    -- off the block of `h'`, what is in the block of `x` at `h` is off the blob of `h'`
    have hoff : ∀ {w : V}, BlockWalk N h (N.leaf x) w → ¬ N.graph.blobSetoid h' w := fun hw hw' =>
      hxB (blockWalk_trans (blockWalk_of_sameBlob hb hw') (blockWalk_symm hw))
    have hlift : ∀ {w : V}, BlockWalk N h (N.leaf x) w → BlockWalk N h' (N.leaf x) w := by
      intro w hw
      induction hw with
      | refl => exact .refl
      | @tail c d hc hstep ih =>
        obtain ⟨_, _, f, hf⟩ := hstep
        exact ih.tail ⟨hoff hc, hoff (hc.tail ⟨‹_›, ‹_›, f, hf⟩), f, hf⟩
    obtain ⟨b, hb₁⟩ := exists_isAttachment hN (hx' x)
    obtain ⟨hbb, k, -, -, hcase⟩ := id hb₁
    -- from the attachment to the reticulation inside the blob
    have hbr : N.graph.Reaches b h := reaches_reticulation hN hLevel (v := h) .refl F.two_le hbb
    have hin : BlockWalk N h' b h := blockWalk_of_reaches hbr fun w hbw hwh =>
      hoffh' (sameBlob_of_reaches_of_reaches hN hbb .refl hbw hwh)
    rcases hcase with ⟨rfl, h₂⟩ | ⟨rfl, h₂⟩
    · exact (Relation.ReflTransGen.tail (hlift h₂) ⟨hoff h₂, hoffh' hbb, k, Or.inr ⟨rfl, rfl⟩⟩).trans hin
    · exact (Relation.ReflTransGen.tail (hlift h₂) ⟨hoff h₂, hoffh' hbb, k, Or.inl ⟨rfl, rfl⟩⟩).trans hin
  exact hd hy hz hyz (blockWalk_trans (key hyB) (blockWalk_symm (key hzB)))

/-! ### Cuts, without one reticulation arc -/

omit [Fintype X] [DecidableEq X] hBin in
/-- An arc on the way to `k₁` has a cut of what is below it, crossed only by itself and `k₂`. -/
theorem cut_left {e : E} (he : BlobCycle.Towards N k₁ e) {f : E} (hf : f ≠ e) (hf₂ : f ≠ k₂)
    (hc : N.graph.Crosses f {u | N.graph.Reaches (N.graph.target e) u}) (heb : e ∈ N.graph.blobArcs h) : False := by
  have C := F.cycle
  have hh₂ := F.two_le
  have htb : N.graph.blobSetoid h (N.graph.target e) := (mem_blobArcs_iff.1 heb).2
  rcases hc with ⟨h₁, h₂⟩ | ⟨hft, hfs⟩
  · exact h₂ (Relation.ReflTransGen.tail h₁ ⟨f, rfl, rfl⟩)
  have hft' : N.graph.Reaches (N.graph.target e) (N.graph.target f) := hft
  have hfs' : ¬ N.graph.Reaches (N.graph.target e) (N.graph.source f) := hfs
  have hk₁ : ∀ {g : E}, N.graph.target g = h → g ≠ k₂ → g = k₁ := fun {g} hg hne => (C.arcs g hg).resolve_right hne
  by_cases hfe : N.graph.target f = N.graph.target e
  · by_cases hdeg : 2 ≤ N.graph.indegree (N.graph.target e)
    · have hth : N.graph.target e = h := reticulation_unique hN hLevel htb hdeg (v := h) .refl hh₂
      have hfk := hk₁ (hfe.trans hth) hf₂
      rcases he with rfl | he
      · exact hf hfk
      · exact C.not_reaches_of_target₁ hN (hth ▸ he)
    · exact hf (eq_of_indegree_le_one hN (by omega) hfe)
  · obtain ⟨hb, h2⟩ := entering_of_strictBelow hN hft' hfe hfs'
    have hth : N.graph.target f = h := reticulation_unique hN hLevel (sameBlob_trans htb hb) h2 (v := h) .refl hh₂
    have hfk := hk₁ hth hf₂
    rcases he with rfl | he
    · exact hf hfk
    · exact hfs' (hfk ▸ he)

omit [Fintype X] [DecidableEq X] hBin in
/-- An arc on the way to `k₂`, other than `k₂`, has a cut of what is below it and not below the reticulation, crossed only by itself and
`k₂`. -/
theorem cut_right {e : E} (he : N.graph.Reaches (N.graph.target e) (N.graph.source k₂)) (heb : e ∈ N.graph.blobArcs h) {f : E}
    (hf : f ≠ e) (hf₂ : f ≠ k₂)
    (hc : N.graph.Crosses f {u | N.graph.Reaches (N.graph.target e) u ∧ ¬ N.graph.Reaches h u}) : False := by
  have C := F.cycle
  have hh₂ := F.two_le
  have htb : N.graph.blobSetoid h (N.graph.target e) := (mem_blobArcs_iff.1 heb).2
  have hsb : N.graph.blobSetoid h (N.graph.source e) := (mem_blobArcs_iff.1 heb).1
  have hteh : N.graph.target e ≠ h := fun hc' => C.swap.not_reaches_of_target₁ hN (hc' ▸ he)
  have hteT : N.graph.target e ≠ T := by
    intro hc'
    exact not_reaches_source hN e (hc' ▸ C.top_reaches _ hsb)
  rcases hc with ⟨⟨h₁, h₁'⟩, h₂⟩ | ⟨⟨h₁, h₁'⟩, h₂⟩
  · -- `f` leaves the set: it enters what is below the reticulation
    have hrt : N.graph.Reaches (N.graph.target e) (N.graph.target f) := h₁.tail ⟨f, rfl, rfl⟩
    have hht : N.graph.Reaches h (N.graph.target f) := by
      by_contra hn
      exact h₂ ⟨hrt, hn⟩
    by_cases hfh : N.graph.target f = h
    · have hfk : f = k₁ := (C.arcs f hfh).resolve_right hf₂
      subst hfk
      have hr₂ : N.graph.Reaches (N.graph.target e) (N.graph.source f) := h₁
      exact F.exclusive hN hLevel htb hteT hr₂ he
    · obtain ⟨hb, h2⟩ := entering_of_strictBelow hN hht hfh h₁'
      exact hfh (reticulation_unique hN hLevel hb h2 (v := h) .refl hh₂)
  · -- `f` enters the set: it is `e`
    have hs : ¬ N.graph.Reaches (N.graph.target e) (N.graph.source f) := by
      intro hr
      refine h₂ ⟨hr, fun hh => h₁' (Relation.ReflTransGen.tail hh ⟨f, rfl, rfl⟩)⟩
    by_cases hfe : N.graph.target f = N.graph.target e
    · by_cases hdeg : 2 ≤ N.graph.indegree (N.graph.target e)
      · exact hteh (reticulation_unique hN hLevel htb hdeg (v := h) .refl hh₂)
      · exact hf (eq_of_indegree_le_one hN (by omega) hfe)
    · obtain ⟨hb, h2⟩ := entering_of_strictBelow hN h₁ hfe hs
      have hth : N.graph.target f = h := reticulation_unique hN hLevel (sameBlob_trans htb hb) h2 (v := h) .refl hh₂
      exact h₁' (hth ▸ .refl)

/-- **A cut for every kept edge not contracted, other than `k₂`.** -/
theorem exists_cut_off {e : E} (hK : e ∈ trekArcs N q) (hnc : e ∉ contractedArcs N q) (hne : e ≠ k₂) :
    ∃ S : Set V, N.graph.Crosses e S ∧ ∀ f ∈ trekArcs N q, f ≠ e → f ≠ k₂ → ¬ N.graph.Crosses f S := by
  by_cases hb : N.graph.underlying.IsBridge e
  · obtain ⟨S, h₁, h₂⟩ := exists_cut_of_isBridge hN hb
    exact ⟨S, h₁, fun f _ hf _ => h₂ f hf⟩
  obtain ⟨h', hh', heb⟩ := exists_reticulation_of_not_isBridge hN hb
  by_cases hsame : N.graph.blobSetoid h h'
  · have heb' : e ∈ N.graph.blobArcs h := by
      obtain ⟨h₁, h₂⟩ := mem_blobArcs_iff.1 heb
      exact mem_blobArcs_iff.2 ⟨sameBlob_trans hsame h₁, sameBlob_trans hsame h₂⟩
    rcases F.cycle.towards_or hN hLevel F.two_le heb' with ht | ht
    · refine ⟨{u | N.graph.Reaches (N.graph.target e) u}, Or.inr ⟨.refl, not_reaches_source hN e⟩, fun f _ hf hf₂ hc => ?_⟩
      exact cut_left hN hLevel F ht hf hf₂ hc heb'
    · have hr : N.graph.Reaches (N.graph.target e) (N.graph.source k₂) := by
        rcases ht with rfl | hr
        · exact absurd rfl hne
        · exact hr
      refine ⟨{u | N.graph.Reaches (N.graph.target e) u ∧ ¬ N.graph.Reaches h u}, Or.inr ⟨⟨.refl, ?_⟩, fun hs => ?_⟩, fun f _ hf hf₂ hc => ?_⟩
      · intro hc'
        exact F.cycle.swap.not_reaches_of_target₁ hN (hc'.trans hr)
      · exact not_reaches_source hN e hs.1
      · exact cut_right hN hLevel F hr heb' hf hf₂ hc
  · refine (exists_cut_of_not_isQuartetCycle hN hBin hLevel hh' heb hK fun hQ => hnc ⟨h', hQ, ?_, heb⟩).imp fun S hS => ⟨hS.1, fun f hf hne' _ => hS.2 f hf hne'⟩
    exact cycleSize_le_three_of_not_sameBlob hN hBin hLevel F hsame hQ

end Frame

/-! ### The graph without a reticulation arc is a tree -/

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- The arcs of the blob are kept, and not contracted, given that the cycle is kept and it is not contracted. -/
theorem mem_tilde_of_blobArcs (hQ : IsQuartetCycle N q h)
    (hoff : ∀ {f : E}, f ∈ contractedArcs N q → ¬ N.graph.blobSetoid h (N.graph.source f)) {f : E} (hf : f ∈ N.graph.blobArcs h) :
    f ∈ trekArcs N q ∧ f ∉ contractedArcs N q :=
  ⟨hQ.2 f hf, fun hc => hoff hc (mem_blobArcs_iff.1 hf).1⟩

/-- The contracted graph without the edge `k`. -/
def offGraph (N : RootedNetwork V E X) (q : Finset X) (k : E) :
    DirectedMultigraph (TildeV N q) {e : TildeE N q // e.1 ≠ k} where
  source e := (tildeGraph N q).source e.1
  target e := (tildeGraph N q).target e.1

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A directed path of kept edges, not contracted and other than `k`, is a walk of the graph without `k`. -/
theorem walks_off_of_isDirPath {k : E} {a b : V} {p : List E} (hp : N.IsDirPath a p b)
    (hK : ∀ e ∈ p, e ∈ trekArcs N q ∧ e ∉ contractedArcs N q ∧ e ≠ k)
    (ha : IsKept N q a) (hb : IsKept N q b) : (offGraph N q k).Walks Set.univ (toV ha) (toV hb) := by
  induction p generalizing a with
  | nil =>
    obtain rfl : a = b := hp
    exact .refl
  | cons e p ih =>
    obtain ⟨rfl, hp⟩ := hp
    obtain ⟨he, hc, hne⟩ := hK e (by simp)
    refine Relation.ReflTransGen.head ?_ (ih hp (fun f hf => hK f (by simp [hf])) (isKept_target he))
    exact ⟨⟨⟨e, he, hc⟩, hne⟩, Set.mem_univ _, Or.inl ⟨rfl, rfl⟩⟩

section Tree

variable (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (F : CycleFrame N q a h h T k₁ k₂ pL pR)
include hN hBin hLevel F

/-- **The contracted graph without `k₂` is a tree.** -/
theorem isTree_offGraph : (offGraph N q k₂).IsTree := by
  have C := F.cycle
  have hQ := frame_hQ hN hBin hLevel F
  have hoff : ∀ {f : E}, f ∈ contractedArcs N q → ¬ N.graph.blobSetoid h (N.graph.source f) := fun hf =>
    (contracted_off_blob hN hLevel F hBin hf).1
  have hmem := fun {f : E} (hf : f ∈ N.graph.blobArcs h) => mem_tilde_of_blobArcs (q := q) hQ hoff hf
  -- `k₂` is not needed for connectedness
  have hk₂' : ∀ f ∈ pL ++ [k₁], f ≠ k₂ := by
    intro f hf hfe
    subst hfe
    simp only [List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | hf
    · exact C.reticulation_notMem_left hN (C.target₂ ▸ List.mem_map_of_mem hf)
    · exact C.ne hf.symm
  have hk₂r : ∀ f ∈ pR, f ≠ k₂ := by
    intro f hf hfe
    subst hfe
    exact C.swap.reticulation_notMem_left hN (C.target₂ ▸ List.mem_map_of_mem hf)
  have hL : N.IsDirPath T (pL ++ [k₁]) h := C.left.append ⟨rfl, C.target₁⟩
  have hLK : ∀ f ∈ pL ++ [k₁], f ∈ trekArcs N q ∧ f ∉ contractedArcs N q ∧ f ≠ k₂ := fun f hf =>
    ⟨(hmem (mem_blobArcs_iff.2 (C.sameBlob_of_mem hN hf))).1, (hmem (mem_blobArcs_iff.2 (C.sameBlob_of_mem hN hf))).2, hk₂' f hf⟩
  have hRK : ∀ f ∈ pR, f ∈ trekArcs N q ∧ f ∉ contractedArcs N q ∧ f ≠ k₂ := fun f hf =>
    have hb := mem_blobArcs_iff.2 (C.swap.sameBlob_of_mem hN (f := f) (by simp [hf]))
    ⟨(hmem hb).1, (hmem hb).2, hk₂r f hf⟩
  have hk₂b : k₂ ∈ N.graph.blobArcs h := mem_blobArcs_iff.2 ⟨C.swap.source₁_sameBlob hN, C.target₂ ▸ C.reticulation⟩
  have hk₂K := (hmem hk₂b).1
  have hkTk : IsKept N q T := by
    obtain ⟨g₁, g₂, -, hs₁, -, hb₁, -⟩ := C.exists_two_out_arcs hN
    exact ⟨g₁, (hmem ⟨hb₁, hs₁ ▸ C.top⟩).1, Or.inl hs₁⟩
  have hkh : IsKept N q h := ⟨k₂, hk₂K, Or.inr C.target₂⟩
  have hround : (offGraph N q k₂).Walks Set.univ (toV (isKept_source hk₂K)) (toV (isKept_target hk₂K)) := by
    have h₁ := walks_off_of_isDirPath (k := k₂) C.right hRK hkTk (isKept_source hk₂K)
    have h₂ := walks_off_of_isDirPath (k := k₂) (q := q) (hL.append (show N.IsDirPath h [] (N.graph.target k₂) from C.target₂.symm)) (by simpa using hLK) hkTk (isKept_target hk₂K)
    exact (DirectedMultigraph.walks_symm _ h₁).trans h₂
  refine ⟨fun a' b' => ?_, fun e => ?_⟩
  · have hw := tildeGraph_isConnected (N := N) (q := q) hN (by rw [F.card]; norm_num) a' b'
    induction hw with
    | refl => exact .refl
    | @tail b c _ hbc ih =>
      refine ih.trans ?_
      obtain ⟨g, -, hg⟩ := hbc
      by_cases hgk : g.1 = k₂
      · have hsrc : (tildeGraph N q).source g = toV (isKept_source hk₂K) := by
          simp only [tildeGraph_source]
          exact Subtype.ext (by simp [toV, hgk])
        have htgt : (tildeGraph N q).target g = toV (isKept_target hk₂K) := by
          simp only [tildeGraph_target]
          exact Subtype.ext (by simp [toV, hgk])
        rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hsrc, htgt]
          exact hround
        · rw [hsrc, htgt]
          exact DirectedMultigraph.walks_symm _ hround
      · exact .single ⟨⟨g, hgk⟩, Set.mem_univ _, hg⟩
  · obtain ⟨S, hcr, hS⟩ := exists_cut_off hN hBin hLevel F e.1.2.1 e.1.2.2 e.2
    have hC : ∀ f ∈ contractedArcs N q, ¬ N.graph.Crosses f S := by
      intro f hf
      obtain ⟨h', hQ', hs3, hb⟩ := id hf
      refine hS f (hQ'.2 f hb) (fun he => e.1.2.2 (he ▸ hf)) fun he => ?_
      exact (hmem hk₂b).2 (he ▸ hf)
    refine not_walks_of_isSideOf (T := tildeSide N q S) fun f => ?_
    have hiff : (offGraph N q k₂).Crosses f (tildeSide N q S) ↔ N.graph.Crosses f.1.1 S := crosses_tildeSide hC f.1
    rw [hiff]
    constructor
    · intro hc
      by_contra hne
      exact hS f.1.1 f.1.2.1 (fun h' => hne (Subtype.ext (Subtype.ext h'))) f.2 hc
    · rintro rfl
      exact hcr

end Tree


/-! ### The degrees -/

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem ncard_le_nodeDegree {W F : Type*} {G : DirectedMultigraph W F} [Finite F] {A : Set F} {w : W}
    (hA : ∀ e ∈ A, G.target e = w ∨ G.source e = w) : A.ncard ≤ nodeDegree G w := by
  have hsub : A ⊆ {e | G.target e = w} ∪ {e | G.source e = w} := fun e he => hA e he
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)

section Degrees

variable (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (F : CycleFrame N q a h h T k₁ k₂ pL pR)
include hN hBin hLevel F

/-- **The sum of the degrees of the contracted graph is twice its number of vertices.** -/
theorem sum_nodeDegree_tilde [Fintype (TildeV N q)] [Fintype (TildeE N q)] :
    ∑ w, nodeDegree (tildeGraph N q) w = 2 * Fintype.card (TildeV N q) := by
  have hoff : ∀ {f : E}, f ∈ contractedArcs N q → ¬ N.graph.blobSetoid h (N.graph.source f) := fun hf =>
    (contracted_off_blob hN hLevel F hBin hf).1
  have hk₂b : k₂ ∈ N.graph.blobArcs h :=
    mem_blobArcs_iff.2 ⟨F.cycle.swap.source₁_sameBlob hN, F.cycle.target₂ ▸ F.cycle.reticulation⟩
  have hm := mem_tilde_of_blobArcs (q := q) (frame_hQ hN hBin hLevel F) hoff hk₂b
  have hne : Nonempty (TildeV N q) := ⟨toV (isKept_source hm.1)⟩
  have hT := card_arcs_add_one (isTree_offGraph hN hBin hLevel F)
  have hc : Fintype.card {e : TildeE N q // e.1 ≠ k₂} + 1 = Fintype.card (TildeE N q) := by
    have h₁ := Fintype.card_subtype_compl (α := TildeE N q) (fun e => e.1 = k₂)
    have h₂ : Fintype.card {e : TildeE N q // e.1 = k₂} = 1 :=
      Fintype.card_eq_one_iff.2 ⟨⟨⟨k₂, hm⟩, rfl⟩, fun y => Subtype.ext (Subtype.ext y.2)⟩
    have h₃ : 0 < Fintype.card (TildeE N q) := Fintype.card_pos_iff.2 ⟨⟨k₂, hm⟩⟩
    have h₄ : Fintype.card {e : TildeE N q // e.1 ≠ k₂} = Fintype.card (TildeE N q) - Fintype.card {e : TildeE N q // e.1 = k₂} := h₁
    omega
  rw [sum_nodeDegree]
  omega

omit hBin in
/-- A vertex of the blob is alone in its class. -/
theorem eq_of_toV_blob_eq (hBin : N.IsBinary) {b v : V} (hb : N.graph.blobSetoid h b) {hk : IsKept N q b} {hv : IsKept N q v}
    (he : toV hv = toV hk) : v = b := by
  have hS : ∀ f ∈ contractedArcs N q, ¬ N.graph.Crosses f {b} := by
    intro f hf hc
    obtain ⟨h₁, h₂⟩ := contracted_off_blob hN hLevel F hBin hf
    rcases hc with ⟨h', -⟩ | ⟨h', -⟩
    · exact h₁ (by rw [show N.graph.source f = b from h']; exact hb)
    · exact h₂ (by rw [show N.graph.target f = b from h']; exact hb)
  exact (mem_iff_of_toV_eq hS he).2 rfl

omit [Fintype X] [DecidableEq X] in
/-- A vertex of the blob is kept. -/
theorem isKept_of_blob {b : V} (hb : N.graph.blobSetoid h b) : IsKept N q b := by
  obtain ⟨f, -, -, hf, -, hfu, -⟩ := exists_two_blobArcs hN hBin hLevel F.two_le hb
  exact ⟨f, (frame_hQ hN hBin hLevel F).2 f hf, hfu⟩

/-- An attachment has degree at least three: two edges of the cycle and the cut edge. -/
theorem three_le_nodeDegree_attachment {x : X} (hx : x ∈ q) {b : V} (hb : IsAttachment N h x b) (hk : IsKept N q b) :
    3 ≤ nodeDegree (tildeGraph N q) (toV hk) := by
  have hQ := frame_hQ hN hBin hLevel F
  have hbelow := (isQuartetCycle_iff (q := q) hN hBin hLevel F.two_le).1 hQ
  have hoff : ∀ {f : E}, f ∈ contractedArcs N q → ¬ N.graph.blobSetoid h (N.graph.source f) := fun hf =>
    (contracted_off_blob hN hLevel F hBin hf).1
  obtain ⟨f, g, hfg, hf, hg, hfu, hgu⟩ := exists_two_blobArcs hN hBin hLevel F.two_le hb.1
  obtain ⟨k, hkK, hkb, hkinc⟩ := IsAttachment.exists_arc_mem_wedgeArcs hN hBin hLevel F.two_le hbelow hx hb
  rw [← trekArcs_eq_wedgeArcs hN] at hkK
  have hkc : k ∉ contractedArcs N q := fun ⟨_, _, _, h'⟩ => h'.1 hkb
  have hmf := mem_tilde_of_blobArcs (q := q) hQ hoff hf
  have hmg := mem_tilde_of_blobArcs (q := q) hQ hoff hg
  have hF : Finite (TildeE N q) := Subtype.finite
  have hkf : k ≠ f := fun he => hf.1 (he ▸ hkb)
  have hkg : k ≠ g := fun he => hg.1 (he ▸ hkb)
  have hne₁ : (⟨k, hkK, hkc⟩ : TildeE N q) ≠ ⟨f, hmf⟩ := fun he => hkf (congrArg Subtype.val he)
  have hne₂ : (⟨k, hkK, hkc⟩ : TildeE N q) ≠ ⟨g, hmg⟩ := fun he => hkg (congrArg Subtype.val he)
  have hne₃ : (⟨f, hmf⟩ : TildeE N q) ≠ ⟨g, hmg⟩ := fun he => hfg (congrArg Subtype.val he)
  have hA : ∀ e ∈ ({⟨k, hkK, hkc⟩, ⟨f, hmf⟩, ⟨g, hmg⟩} : Set (TildeE N q)),
      (tildeGraph N q).target e = toV hk ∨ (tildeGraph N q).source e = toV hk := by
    have hinc : ∀ {e : TildeE N q}, (N.graph.source e.1 = b ∨ N.graph.target e.1 = b) →
        (tildeGraph N q).target e = toV hk ∨ (tildeGraph N q).source e = toV hk := by
      rintro e (h' | h')
      · exact Or.inr (Subtype.ext (by simp only [tildeGraph_source, toV, h']))
      · exact Or.inl (Subtype.ext (by simp only [tildeGraph_target, toV, h']))
    rintro e (rfl | rfl | rfl)
    · exact hinc hkinc
    · exact hinc hfu
    · exact hinc hgu
  have hc : ({⟨k, hkK, hkc⟩, ⟨f, hmf⟩, ⟨g, hmg⟩} : Set (TildeE N q)).ncard = 3 := by
    rw [Set.ncard_eq_toFinset_card']
    simp [hne₁, hne₂, hne₃]
  rw [← hc]
  exact ncard_le_nodeDegree hA

/-- **The degrees of the contracted graph.** By the sum of the degrees, a class that is neither a taxon of `q` nor an attachment has
degree two, and an attachment has degree three. -/
theorem nodeDegree_eq_of_frame :
    (∀ w : TildeV N q, (∀ x ∈ q, ∀ hx : IsKept N q (N.leaf x), toV hx ≠ w) →
      (∀ x ∈ q, ∀ b, IsAttachment N h x b → ∀ hb : IsKept N q b, toV hb ≠ w) → nodeDegree (tildeGraph N q) w = 2) ∧
    ∀ x ∈ q, ∀ b, IsAttachment N h x b → ∀ hb : IsKept N q b, nodeDegree (tildeGraph N q) (toV hb) = 3 := by
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl F.two_le
  have hq2 : 2 ≤ #q := by rw [F.card]; norm_num
  have hex : ∀ z, ∃ b, IsAttachment N h z b := fun z => exists_isAttachment hN (hx' z)
  choose att hatt using hex
  have hkatt : ∀ z, IsKept N q (att z) := fun z => isKept_of_blob hN hBin hLevel F (hatt z).1
  let ℓ' : {x // x ∈ q} → TildeV N q := fun x => toV (isKept_leaf' hN hq2 x.2)
  let u' : {x // x ∈ q} → TildeV N q := fun x => toV (hkatt x.1)
  have hℓinj : Function.Injective ℓ' := fun x y hxy =>
    Subtype.ext (hN.leaf_injective (eq_of_toV_leaf_eq hN hxy))
  have huinj : Function.Injective u' := fun x y hxy => by
    have hb := eq_of_toV_blob_eq hN hLevel F hBin (hatt y.1).1 hxy
    exact Subtype.ext (frame_eq_of_attachment hN hBin hLevel F x.2 y.2 (hatt x.1) (hb ▸ hatt y.1))
  have : Fintype (TildeV N q) := Fintype.ofFinite _
  let L : Finset (TildeV N q) := univ.image ℓ'
  let U : Finset (TildeV N q) := univ.image u'
  have hcL : #L = 4 := by
    rw [card_image_of_injective _ hℓinj, card_univ, Fintype.card_coe, F.card]
  have hcU : #U = 4 := by
    rw [card_image_of_injective _ huinj, card_univ, Fintype.card_coe, F.card]
  have hdisj : ∀ w, w ∈ L → w ∈ U → False := by
    intro w hl hu
    obtain ⟨x, -, rfl⟩ := mem_image.1 hl
    obtain ⟨y, -, hy⟩ := mem_image.1 hu
    have := eq_of_toV_leaf_eq hN hy
    exact hx' x.1 (this ▸ (hatt y.1).1)
  let f₀ : TildeV N q → ℕ := fun w => if w ∈ L then 1 else if w ∈ U then 3 else 2
  have hle : ∀ w ∈ (univ : Finset (TildeV N q)), f₀ w ≤ nodeDegree (tildeGraph N q) w := by
    intro w _
    simp only [f₀]
    split_ifs with h₁ h₂
    · obtain ⟨x, -, rfl⟩ := mem_image.1 h₁
      exact (nodeDegree_toV_leaf hN _).ge
    · obtain ⟨x, -, rfl⟩ := mem_image.1 h₂
      exact three_le_nodeDegree_attachment hN hBin hLevel F x.2 (hatt x.1) _
    · exact two_le_nodeDegree hN w fun x hx hk he => h₁ (mem_image.2 ⟨⟨x, hx⟩, mem_univ _, he⟩)
  have hsumf : ∑ w, f₀ w = 2 * Fintype.card (TildeV N q) := by
    have hpt : ∀ w, f₀ w + (if w ∈ L then 1 else 0) = 2 + (if w ∈ U then 1 else 0) := by
      intro w
      simp only [f₀]
      by_cases h₁ : w ∈ L
      · have h₂ : w ∉ U := fun h₂ => hdisj w h₁ h₂
        simp [h₁, h₂]
      · by_cases h₂ : w ∈ U <;> simp [h₁, h₂]
    have hsum : ∑ w, (f₀ w + (if w ∈ L then 1 else 0)) = ∑ w, (2 + (if w ∈ U then 1 else 0)) :=
      sum_congr rfl fun w _ => hpt w
    rw [sum_add_distrib, sum_add_distrib, sum_boole, sum_boole, sum_const, card_univ, smul_eq_mul] at hsum
    simp only [filter_mem_eq_inter, univ_inter] at hsum
    have h₁ : ((#L : ℕ) : ℕ) = 4 := hcL
    have h₂ : ((#U : ℕ) : ℕ) = 4 := hcU
    simp only [Nat.cast_id] at hsum
    omega
  have hsumd := sum_nodeDegree_tilde hN hBin hLevel F
  have heq := (sum_eq_sum_iff_of_le hle).1 (hsumf.trans hsumd.symm)
  refine ⟨fun w h₁ h₂ => ?_, fun x hx b hb hk => ?_⟩
  · have hL : w ∉ L := fun hm => by
      obtain ⟨x, -, hxw⟩ := mem_image.1 hm
      exact h₁ x.1 x.2 _ hxw
    have hU : w ∉ U := fun hm => by
      obtain ⟨x, -, hxw⟩ := mem_image.1 hm
      exact h₂ x.1 x.2 _ (hatt x.1) _ hxw
    have := heq w (mem_univ _)
    simp only [f₀, hL, hU, ite_false] at this
    exact this.symm
  · have hbe : b = att x := IsAttachment.eq_of_isAttachment (hx' x) hb (hatt x)
    subst hbe
    have hU : u' ⟨x, hx⟩ ∈ U := mem_image_of_mem _ (mem_univ _)
    have hL : u' ⟨x, hx⟩ ∉ L := fun hm => hdisj _ hm hU
    have := heq (u' ⟨x, hx⟩) (mem_univ _)
    simp only [f₀, hL, hU, ite_true, ite_false] at this
    exact this.symm

end Degrees

end External.AllmanBanosRhodes2019.Quartet
