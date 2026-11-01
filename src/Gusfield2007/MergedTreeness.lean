module

public import Gusfield2007.Uniqueness
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Gusfield et al. 2007, Section 4.2: the treeness inequality when blobs merge components

`treeness_le_and_eq_iff` asks each blob to have the sites of one component of `G(M)`. This module says what happens without that.

* **A blob that merges two trivial components breaks the inequality** (`treeness_merged_false`). The rows `1000, 0100, 0010, 0001` are compatible, and `T̄` is a star with `4` edges. In `mergedNet` the sites `0, 1` are on one blob, with an exit for each of the three sequences `10, 01, 00` of those sites, and the exit of `00` leads to the two rows `0010, 0001`. It has every other condition of `treeness_le_and_eq_iff`, and its treeness is `5`.
* **A blob with no site does no harm** (`treeness_le_and_eq_iff_of_siteFree`). Under the other conditions, such a blob has only pendant arcs, and it's at the root, so that the network is a star on it.
* **A blob with a site of a non-trivial component does no harm to the inequality** (`treeness_le_of_merged`). A new split of `T′` is the set of the rows with one sequence on the sites of a blob. In `T̄`, those rows hang from a node on the way to the central node of a non-trivial component of the blob, and the edge from that node towards the central node isn't in `T′`. So there's an injection from the edges of `T′` to those of `T̄`. With a merged blob, equality doesn't give `T′ = T̄` (`treeness_merged_tie`).

So the inequality can only fail for a blob with at least two sites, all of them isolated in `G(M)`.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

open Network

/-! ### The counterexample -/

/-- A blob with the two compatible sites `0, 1`, its three exits, and the rows `0010, 0001` below the exit of `00`. -/
def mergedNet : Network (Fin 4) (Fin 9) (Fin 9) :=
  mkNet (tbl [0, 0, 1, 2, 1, 2, 3, 6, 6]) (tbl [1, 2, 3, 3, 4, 5, 6, 7, 8]) 0 (tbl [0, 1, 7, 8])
    (bitsOf [[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def mergedAc : Fin 9 → Option (Fin 1) := colourOf [1, 1, 1, 1]
def mergedVc : Fin 9 → Option (Fin 1) := colourOf [1, 1, 1, 1]

theorem mergedNet_derives : mergedNet.Derives starRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem mergedNet_obeys (c : Crossover) : mergedNet.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem mergedNet_cover : GallCover mergedNet mergedAc mergedVc :=
  GallCover.of_decide (fun _ => 0) (fun _ => 2) (fun _ => 1) (fun _ => 3)
    (fun e v => if e = 6 then decide (6 ≤ v.val) else decide (v = mergedNet.tgt e)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem mergedNet_degree : mergedNet.DegreeCond :=
  mergedNet_cover.degree_cond₂ (tbl [4, 4, 4, 4, 0, 0, 6, 0, 0]) (tbl [5, 5, 5, 5, 0, 0, 7, 0, 0]) (tbl [6, 6, 6, 6, 0, 0, 8, 0, 0])
    (tbl [4, 4, 4, 4, 0, 0, 3, 0, 0]) (tbl [5, 5, 5, 5, 0, 0, 7, 0, 0]) (tbl [6, 6, 6, 6, 0, 0, 8, 0, 0]) (by decide +kernel)

theorem mergedNet_hr : ∀ e f, e ≠ f → mergedNet.tgt e = mergedNet.tgt f → ∃ g, mergedNet.src g = mergedNet.tgt e := by decide +kernel

theorem mergedNet_hl : ∀ e, mergedAc e = none → mergedVc (mergedNet.src e) = none → mergedVc (mergedNet.tgt e) = none →
    (∃ g, mergedNet.src g = mergedNet.tgt e) → ∃ i, mergedNet.site i = e := by
  decide +kernel

theorem starRows_compatible : ∀ i j, ¬ Incompatible starRows i j := by
  unfold Incompatible
  decide +kernel

theorem mergedAc_card : Fintype.card {e // mergedAc e = none} = 5 := by decide +kernel

/-- What an explicit network needs for `NonPendantPortsDistinct`, from its colours. -/
theorem GallCover.nonPendantPortsDistinct_of_decide {ι V E κ : Type*} {N : Network ι V E} {ac : E → Option κ} {vc : V → Option κ} (h : GallCover N ac vc)
    (hp : ∀ k e f u v, vc u = some k → vc v = some k → ((N.src e = u ∧ vc (N.tgt e) ≠ some k) ∨ (N.tgt e = u ∧ vc (N.src e) ≠ some k)) →
      ((N.src f = v ∧ vc (N.tgt f) ≠ some k) ∨ (N.tgt f = v ∧ vc (N.src f) ≠ some k)) → (∃ g, N.src g = N.tgt e) → N.label u = N.label v → e = f) :
    N.NonPendantPortsDistinct := by
  rintro B e f u v hB ⟨hu, h₁⟩ ⟨hv, h₂⟩ hl hlab
  obtain ⟨k, rfl⟩ := (h.isBlob_iff B).1 hB
  have hnot : ∀ {z}, z ∉ N.blobVerts {g | ac g = some k} → vc z ≠ some k := fun hz hk => hz (h.mem_blobVerts_iff.2 hk)
  refine hp k e f u v (h.mem_blobVerts_iff.1 hu) (h.mem_blobVerts_iff.1 hv) ?_ ?_ ?_ hlab
  · rcases h₁ with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
    · exact Or.inl ⟨h₃, hnot h₄⟩
    · exact Or.inr ⟨h₃, hnot h₄⟩
  · rcases h₂ with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
    · exact Or.inl ⟨h₃, hnot h₄⟩
    · exact Or.inr ⟨h₃, hnot h₄⟩
  · by_contra hne
    push Not at hne
    exact hl hne

theorem mergedNet_ports : mergedNet.NonPendantPortsDistinct :=
  mergedNet_cover.nonPendantPortsDistinct_of_decide (by decide +kernel)

/-- `T̄` for `starRows` has `4` edges. -/
theorem starRows_edgeSet {W : Type*} [Finite W] {T : SimpleGraph W} {φ : starRows → W} {edge : SuperChar starRows → Sym2 W} (hT : IsTBar starRows T φ edge) :
    T.edgeSet.ncard = 4 := by
  obtain ⟨f, -⟩ := starNet.exists_iso_of_isTreeNormalStructural starNet_derives (Network.isFullyDecomposedFor_of_tgt_injective starNet_tgt_injective _)
    (Network.isEfficient_of_tgt_injective starNet_tgt_injective).perBlob
    (starNet_cover.isTreeNormalStructural starNet_hr (fun k => k.elim) (fun e _ _ _ hg => starNet_hl e hg)) starNet_degree hT
  rw [ncard_edgeSet_iso f, ← Network.treeness_eq_ncard_edgeSet, starNet_cover.treeness_eq]
  decide +kernel

/-- **The treeness inequality fails for a blob that merges two components** (`g:treeness_merged_false`). `mergedNet` derives the compatible rows `1000, 0100, 0010, 0001`, in any crossover model. It has every condition of `treeness_le_and_eq_iff` except that its one blob has the two sites `0, 1`, which are two components of `G(M)`, each of one site. Its treeness is `5`, and `T̄` has `4` edges. The split `{0010, 0001} | {1000, 0100}` is in `T′` and not in `T̄`. -/
theorem treeness_merged_false (c : Crossover) {W : Type*} [Finite W] {T : SimpleGraph W} {φ : starRows → W} {edge : SuperChar starRows → Sym2 W} (hT : IsTBar starRows T φ edge) :
    mergedNet.Obeys c ∧ mergedNet.Derives starRows ∧ NoConstantColumn starRows ∧ mergedNet.BlobsNodeDisjoint ∧ mergedNet.RegularArcs ∧ mergedNet.NonPendantPortsDistinct ∧ mergedNet.DegreeCond ∧
      (∃ B, mergedNet.IsBlob B ∧ mergedNet.site 0 ∈ B ∧ mergedNet.site 1 ∈ B) ∧ (∀ i j, ¬ (incompatGraph starRows).Adj i j) ∧
      mergedNet.treeness = 5 ∧ T.edgeSet.ncard = 4 := by
  refine ⟨mergedNet_obeys c, mergedNet_derives, noConstantColumn_starRows, mergedNet_cover.nodeDisjoint, ⟨GallCover.recomb_not_leaf mergedNet_hr, mergedNet_cover.arc_labelled mergedNet_hl⟩, mergedNet_ports, mergedNet_degree,
    ⟨_, mergedNet_cover.isBlob_color 0, by decide +kernel, by decide +kernel⟩, starRows_compatible, ?_, starRows_edgeSet hT⟩
  rw [mergedNet_cover.treeness_eq, mergedAc_card]

/-! ### A blob with no site -/

section SiteFree

variable {ι : Type*} {V E : Type*} [Finite V] [Finite E] {N : Network ι V E}

omit [Finite V] [Finite E] in
/-- A blob has a node. -/
theorem Network.IsBlob.blobVerts_nonempty {B : Set E} (hB : N.IsBlob B) : (N.blobVerts B).Nonempty := by
  obtain ⟨Q, hQ, rfl⟩ := id hB
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  by_cases hp : p = []
  · have hq : q ≠ [] := fun h => hc.2.2.2.1 (by rw [hp, h])
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil q hq
    exact ⟨_, Network.src_mem_blobVerts (e := a) ⟨_, Relation.ReflTransGen.refl, Or.inr ha⟩⟩
  · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil p hp
    exact ⟨_, Network.src_mem_blobVerts (e := a) ⟨_, Relation.ReflTransGen.refl, Or.inl ha⟩⟩

/-- Under the conditions of `treeness_le_and_eq_iff`, a blob with no site has only pendant arcs, and it's at the root: so every tree arc of the network is pendant. -/
theorem Network.isLeaf_tgt_of_siteFree (hnd : N.BlobsNodeDisjoint) (hr : N.RegularArcs) (hp : N.NonPendantPortsDistinct) (hdeg : N.DegreeCond) {B : Set E} (hB : N.IsBlob B)
    (hs : ∀ i, N.site i ∉ B) {e : E} (he : N.IsTreeArc e) : N.IsLeaf (N.tgt e) := by
  obtain ⟨z, hz⟩ := hB.blobVerts_nonempty
  have hcls : ∀ {v}, N.toBlobNode v = N.toBlobNode z → v ∈ N.blobVerts B := fun {v} hv => by
    rcases Network.eq_or_exists_isBlob_of_toBlobNode_eq hnd hv with rfl | ⟨B', hB', h₁, h₂⟩
    · exact hz
    · by_cases hBB : B' = B
      · exact hBB ▸ h₁
      · exact absurd hz (Set.disjoint_left.1 (hnd B' B hB' hB hBB) h₂)
  have hlab : ∀ {u v}, u ∈ N.blobVerts B → v ∈ N.blobVerts B → N.label u = N.label v := fun hu hv =>
    hB.label_eq_of_forall hu hv fun i hi => absurd hi (hs i)
  have hcross : ∀ {k a}, N.IsTreeArc k → s(N.toBlobNode (N.src k), N.toBlobNode (N.tgt k)) = s(N.toBlobNode z, a) → ∃ u, N.CrossesAt B k u := by
    intro k a hk h₁
    rcases Sym2.eq_iff.1 h₁ with ⟨h₂, -⟩ | ⟨-, h₂⟩
    · have hsk := hcls h₂
      exact ⟨_, hsk, Or.inl ⟨rfl, hk.tgt_notMem_blobVerts hB hsk⟩⟩
    · have htk := hcls h₂
      exact ⟨_, htk, Or.inr ⟨rfl, hk.src_notMem_blobVerts hB htk⟩⟩
  have hA : ¬ ∀ k₁ k₂ u₁ u₂, N.CrossesAt B k₁ u₁ → N.CrossesAt B k₂ u₂ → k₁ = k₂ := by
    intro huq
    have hle : (N.blobbedTree.neighborSet (N.toBlobNode z)).ncard ≤ 1 := by
      rw [Set.ncard_le_one_iff (Set.toFinite _)]
      intro a b ha hb
      obtain ⟨k₁, hk₁, h₁⟩ := Network.exists_isTreeArc_of_adj ha
      obtain ⟨k₂, hk₂, h₂⟩ := Network.exists_isTreeArc_of_adj hb
      obtain ⟨u₁, hu₁⟩ := hcross hk₁ h₁
      obtain ⟨u₂, hu₂⟩ := hcross hk₂ h₂
      obtain rfl := huq k₁ k₂ u₁ u₂ hu₁ hu₂
      exact Sym2.congr_right.1 (h₁.symm.trans h₂)
    obtain ⟨l, hl, hlc⟩ := hdeg (N.toBlobNode z) (by omega)
    exact hr.recomb_not_leaf l (hB.isRecomb_of_isLeaf (hcls hlc) hl) hl
  have hpend : ∀ k u, N.CrossesAt B k u → N.IsLeaf (N.tgt k) := by
    intro k u hk
    by_contra hnl
    refine hA fun k₁ k₂ u₁ u₂ h₁ h₂ => ?_
    exact (hp B k k₁ u u₁ hB hk h₁ hnl (hlab hk.1 h₁.1)).symm.trans (hp B k k₂ u u₂ hB hk h₂ hnl (hlab hk.1 h₂.1))
  obtain ⟨w, hw, -⟩ := Network.exists_isBlobTop_reach hz
  have hroot : w = N.root := by
    rcases hw.eq_root_or_exists hnd hB with h | ⟨g, hg, hgw⟩
    · exact h
    · exfalso
      have hl := hpend g w ⟨hw.1, Or.inr ⟨hgw, hg.src_notMem_blobVerts hB (hgw ▸ hw.1)⟩⟩
      rw [hgw] at hl
      exact hr.recomb_not_leaf w (hB.isRecomb_of_isLeaf hw.1 hl) hl
  have hall : ∀ v, v ∈ N.blobVerts B ∨ N.IsLeaf v := by
    intro v
    rcases hw.position hnd hB (hroot ▸ N.reach_root v) with h | ⟨k, -, hk₂, hk₃, hk₄⟩
    · exact Or.inl h
    · have hl := hpend k _ ⟨hk₂, Or.inl ⟨rfl, hk₃⟩⟩
      rcases Relation.ReflTransGen.cases_head hk₄ with h | ⟨b, ⟨g, hg, -⟩, -⟩
      · exact Or.inr (h ▸ hl)
      · exact absurd hg (hl g)
  rcases hall (N.src e) with h | h
  · exact hpend e _ ⟨h, Or.inl ⟨rfl, he.tgt_notMem_blobVerts hB h⟩⟩
  · exact absurd rfl (h e)

omit [Finite V] [Finite E] in
/-- The rows below a pendant arc. -/
theorem Network.arcSide_eq_singleton {e : E} (hl : N.IsLeaf (N.tgt e)) : N.arcSide e = {N.label (N.tgt e)} := by
  ext r
  constructor
  · rintro ⟨v, hv, hr', rfl⟩
    rcases Relation.ReflTransGen.cases_head hr' with h | ⟨b, ⟨g, hg, -⟩, -⟩
    · rw [h]; rfl
    · exact absurd hg (hl g)
  · rintro rfl
    exact ⟨_, hl, Relation.ReflTransGen.refl, rfl⟩

variable [LinearOrder ι] {M : Finset (ι → Bool)} {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W}

/-- **The positive form of Section 4.2, with blobs that have no site** (`g:treeness_siteFree`). `treeness_le_and_eq_iff`, where a blob can also have no site. Such a blob makes the network a star, whose splits are all trivial. -/
theorem treeness_le_and_eq_iff_of_siteFree (N : Network ι V E) (hd : N.Derives M) (hnd : N.BlobsNodeDisjoint)
    (hone : ∀ B, N.IsBlob B → (∃ c : (incompatGraph M).ConnectedComponent, ∀ i, N.site i ∈ B ↔ i ∈ c.supp) ∨ ∀ i, N.site i ∉ B) (hr : N.RegularArcs) (hp : N.NonPendantPortsDistinct) (hdeg : N.DegreeCond)
    (hT : IsTBar M T φ edge) :
    N.treeness ≤ T.edgeSet.ncard ∧
      (N.treeness = T.edgeSet.ncard ↔
        ∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) := by
  by_cases hex : ∃ B, N.IsBlob B ∧ ∀ i, N.site i ∉ B
  · obtain ⟨B, hB, hs⟩ := hex
    refine treeness_le_of_charSplits N hd hdeg ?_ hT
    have hsing : ∀ {e}, N.IsTreeArc e → (N.arcSide e).encard = 1 := fun he => by
      rw [Network.arcSide_eq_singleton (N.isLeaf_tgt_of_siteFree hnd hr hp hdeg hB hs he), Set.encard_singleton]
    rintro A ⟨e, he, rfl | rfl⟩ h₁ h₂
    · rw [hsing he] at h₁
      simp at h₁
    · rw [Set.sdiff_sdiff_cancel_left (N.arcSide_subset hd e), hsing he] at h₂
      simp at h₂
  · push Not at hex
    refine treeness_le_and_eq_iff N hd hnd (fun B hB => (hone B hB).resolve_right fun h => ?_) hr hp hdeg hT
    obtain ⟨i, hi⟩ := hex B hB
    exact h i hi

end SiteFree

/-! ### `T̄` rooted at a central node -/

section Below

variable {ι : Type*} {M : Finset (ι → Bool)} {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W}

namespace IsTBar

variable (h : IsTBar M T φ edge)

/-- The rows below `b`, when `T̄` is rooted at `c`. -/
def rowsBelow (c b : W) : Set M := {y | ¬ SameSide T s(b, h.par c b) (φ y) c}

omit [Finite W] in
theorem mem_rowsBelow_iff {c b : W} (hb : b ≠ c) {s : W → Bool} (hs : IsCut T s(b, h.par c b) s) (y : M) : y ∈ h.rowsBelow c b ↔ s (φ y) ≠ s c := by
  change ¬ SameSide T s(b, h.par c b) (φ y) c ↔ _
  rw [hs.sameSide_iff h.isTree.connected.preconnected (h.par_spec hb).1]

omit [Finite W] in
/-- Two sets of rows below two nodes with a row in common are nested. -/
theorem rowsBelow_nested {c b₁ b₂ : W} (h₁ : b₁ ≠ c) (h₂ : b₂ ≠ c) {y : M} (hy₁ : y ∈ h.rowsBelow c b₁) (hy₂ : y ∈ h.rowsBelow c b₂) :
    h.rowsBelow c b₁ ⊆ h.rowsBelow c b₂ ∨ h.rowsBelow c b₂ ⊆ h.rowsBelow c b₁ := by
  by_contra hcon
  rw [not_or, Set.not_subset, Set.not_subset] at hcon
  obtain ⟨⟨y₁, hy₁₁, hy₁₂⟩, ⟨y₂, hy₂₁, hy₂₂⟩⟩ := hcon
  by_cases heq : s(b₁, h.par c b₁) = s(b₂, h.par c b₂)
  · have hD : h.rowsBelow c b₁ = h.rowsBelow c b₂ := by
      ext z
      change ¬ SameSide T s(b₁, h.par c b₁) (φ z) c ↔ ¬ SameSide T s(b₂, h.par c b₂) (φ z) c
      rw [heq]
    exact hy₁₂ (hD ▸ hy₁₁)
  have he₁ : s(b₁, h.par c b₁) ∈ T.edgeSet := (h.par_spec h₁).1
  have he₂ : s(b₂, h.par c b₂) ∈ T.edgeSet := (h.par_spec h₂).1
  obtain ⟨s₁, hs₁⟩ := exists_isCut h.isTree he₁
  obtain ⟨s₂, hs₂⟩ := exists_isCut h.isTree he₂
  have nb : ∀ {α β : Bool}, α ≠ β → α = !β := by decide
  rw [h.mem_rowsBelow_iff h₁ hs₁] at hy₁ hy₁₁ hy₂₂
  rw [h.mem_rowsBelow_iff h₂ hs₂] at hy₂ hy₁₂ hy₂₁
  push Not at hy₁₂ hy₂₂
  exact IsCut.not_fourth h.isTree.connected.preconnected hs₁ hs₂ he₁ he₂ heq (a := s₁ c) (b := s₂ c) (x := c) (y := φ y₂) (z := φ y₁) (w := φ y) ⟨rfl, rfl⟩ ⟨hy₂₂, nb hy₂₁⟩ ⟨nb hy₁₁, hy₁₂⟩ ⟨nb hy₁, nb hy₂⟩

/-- A character with `c` on its 0-side is the set of rows below a node. -/
theorem exists_below_of_side (k : SuperChar M) {c : W} (hc : h.side k c = false) :
    ∃ b, b ≠ c ∧ edge k = s(b, h.par c b) ∧ ∀ y : M, y ∈ h.rowsBelow c b ↔ charValue k (y : ι → Bool) = true := by
  obtain ⟨a', b', he, hab, -, hb'⟩ := h.exists_ends k (h.side_cut k)
  have hcut : IsCut T s(a', b') (h.side k) := he ▸ h.side_cut k
  have hsep : ¬ SameSide T s(b', a') b' c := by
    rw [Sym2.eq_swap]
    intro hsame
    have := hcut.eq_of_sameSide hsame
    rw [hb', hc] at this
    exact absurd this (by simp)
  have hbc : b' ≠ c := by
    rintro rfl
    rw [hb'] at hc
    exact absurd hc (by simp)
  have hpar := h.par_unique hab.symm hsep
  have hee : edge k = s(b', h.par c b') := by rw [he, ← hpar, Sym2.eq_swap]
  refine ⟨b', hbc, hee, fun y => ?_⟩
  have hcut' : IsCut T s(b', h.par c b') (h.side k) := hee ▸ h.side_cut k
  rw [h.mem_rowsBelow_iff hbc hcut', h.side_row, hc]
  cases charValue k (y : ι → Bool) <;> simp

/-- The rows below a node, for `T̄` rooted at the central node of `C`, have one sequence on `C`. -/
theorem rowsBelow_same_seq {C : (incompatGraph M).ConnectedComponent} (hnt : C.supp.Nontrivial) {b : W} (hb : b ≠ h.center C) {y₁ y₂ : M} (h₁ : y₁ ∈ h.rowsBelow (h.center C) b)
    (h₂ : y₂ ∈ h.rowsBelow (h.center C) b) : C.supp.domRestrict (y₁ : ι → Bool) = C.supp.domRestrict (y₂ : ι → Bool) := by
  by_contra hne
  have hconn := h.isTree.connected.preconnected
  have he₀ : s(b, h.par (h.center C) b) ∈ T.edgeSet := (h.par_spec hb).1
  obtain ⟨s, hs⟩ := exists_isCut h.isTree he₀
  have nb : ∀ {α β : Bool}, α ≠ β → α = !β := by decide
  rw [h.mem_rowsBelow_iff hb hs] at h₁ h₂
  have key : ∀ {k : SuperChar M} (_ : k.1 = C) {y y' : M}, s (φ y) ≠ s (h.center C) → s (φ y') ≠ s (h.center C) → h.side k (φ y) = true → h.side k (φ y') = false → edge k = s(b, h.par (h.center C) b) := by
    intro k hk y y' hy hy' hky hky'
    by_contra hek
    have hz := h.side_center hnt hk
    obtain ⟨a', b', he, hab, -, hb'⟩ := h.exists_ends k (h.side_cut k)
    have hcen : a' = h.center C := by
      have hmem : h.center C ∈ edge k := h.center_mem hk
      rw [he] at hmem
      rcases Sym2.mem_iff.1 hmem with h₃ | h₃
      · exact h₃.symm
      · rw [← h₃, hz] at hb'
        exact absurd hb' (by simp)
    subst hcen
    have hsb : s b' ≠ s (h.center C) := by
      intro heq
      exact IsCut.not_fourth hconn hs (h.side_cut k) he₀ (h.edge_mem k) (Ne.symm hek) (a := s (h.center C)) (b := false) (x := h.center C) (y := b') (z := φ y') (w := φ y) ⟨rfl, hz⟩ ⟨heq, hb'⟩ ⟨nb hy', hky'⟩ ⟨nb hy, hky⟩
    exact hek (he.trans ((hs hab).1 (Ne.symm hsb)))
  have hk : charOf C y₁.2 ≠ charOf C y₂.2 := fun heq => hne (congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.1 heq).2))
  have hv₁ := charValue_charOf C y₁.2
  have hv₂ := charValue_charOf C y₂.2
  have hf₁ : h.side (charOf C y₁.2) (φ y₂) = false := by
    rw [h.side_row]
    cases hc : charValue (charOf C y₁.2) (y₂ : ι → Bool)
    · rfl
    · exact absurd (charValue_disjoint hk rfl hc hv₂) (by simp)
  have hf₂ : h.side (charOf C y₂.2) (φ y₁) = false := by
    rw [h.side_row]
    cases hc : charValue (charOf C y₂.2) (y₁ : ι → Bool)
    · rfl
    · exact absurd (charValue_disjoint hk rfl hv₁ hc) (by simp)
  have e₁ := key (k := charOf C y₁.2) rfl h₁ h₂ (by rw [h.side_row]; exact hv₁) hf₁
  have e₂ := key (k := charOf C y₂.2) rfl h₂ h₁ (by rw [h.side_row]; exact hv₂) hf₂
  exact h.edge_ne hk rfl hnt (e₁.trans e₂.symm)

/-- `b` is a lowest node, for `T̄` rooted at `c`, with all the rows of `O` below it. -/
def IsMinCand (c : W) (O : Set M) (b : W) : Prop :=
  b ≠ c ∧ O ⊆ h.rowsBelow c b ∧ ∀ b', b' ≠ c → O ⊆ h.rowsBelow c b' → h.rowsBelow c b ⊆ h.rowsBelow c b'

theorem exists_isMinCand {c : W} {O : Set M} (hO : O.Nonempty) (hex : ∃ b, b ≠ c ∧ O ⊆ h.rowsBelow c b) : ∃ b, h.IsMinCand c O b := by
  obtain ⟨b, hb, hmin⟩ := Set.exists_min_image {b | b ≠ c ∧ O ⊆ h.rowsBelow c b} (fun b => (h.rowsBelow c b).ncard) (Set.toFinite _) hex
  refine ⟨b, hb.1, hb.2, fun b' hb' hO' => ?_⟩
  obtain ⟨y, hy⟩ := hO
  rcases h.rowsBelow_nested hb.1 hb' (hb.2 hy) (hO' hy) with h₁ | h₁
  · exact h₁
  · exact (Set.eq_of_subset_of_ncard_le h₁ (hmin b' ⟨hb', hO'⟩) (Set.toFinite _)).ge

end IsTBar

end Below

/-! ### Blobs with a site of a non-trivial component -/

section Merged

variable {ι : Type*} {V E : Type*} [Finite V] [Finite E] {N : Network ι V E} {M : Finset (ι → Bool)}

namespace Network

/-- Below a tree arc off a blob, the sites of the blob have one state. -/
theorem IsTreeArc.rows_below_const {e : E} (he : N.IsTreeArc e) {B : Set E} (hB : N.IsBlob B) {t : V} (ht : t ∈ N.blobVerts B) (hnot : ¬ N.Reach (N.tgt e) t) {x y : ι → Bool}
    (hx : x ∈ N.arcSide e) (hy : y ∈ N.arcSide e) {i : ι} (hi : N.site i ∈ B) : x i = y i := by
  have hr : ¬ N.Reach (N.tgt e) (N.tgt (N.site i)) := fun h => hnot ((he.reach_iff_of_toBlobNode_eq (hB.toBlobNode_eq (tgt_mem_blobVerts hi) ht)).1 h)
  obtain ⟨vx, -, hrx, rfl⟩ := hx
  obtain ⟨vy, -, hry, rfl⟩ := hy
  rw [he.label_eq_of_reach (Or.inr hr) hrx, he.label_eq_of_reach (Or.inr hr) hry]

/-- Off a tree arc above a blob, the sites of the blob have one state. -/
theorem IsTreeArc.rows_off_const {e : E} (he : N.IsTreeArc e) (hd : N.Derives M) {B : Set E} (hB : N.IsBlob B) {t : V} (ht : t ∈ N.blobVerts B) (hbelow : N.Reach (N.tgt e) t) {x y : ι → Bool}
    (hx : x ∈ M) (hy : y ∈ M) (hxA : x ∉ N.arcSide e) (hyA : y ∉ N.arcSide e) {i : ι} (hi : N.site i ∈ B) : x i = y i := by
  have hr : N.Reach (N.tgt e) (N.tgt (N.site i)) := (he.reach_iff_of_toBlobNode_eq (hB.toBlobNode_eq (tgt_mem_blobVerts hi) ht)).2 hbelow
  obtain ⟨lx, hlx, rfl⟩ := hd.surjOn hx
  obtain ⟨ly, hly, rfl⟩ := hd.surjOn hy
  have h₁ : ¬ N.Reach (N.tgt e) lx := fun h' => hxA ⟨lx, hlx, h', rfl⟩
  have h₂ : ¬ N.Reach (N.tgt e) ly := fun h' => hyA ⟨ly, hly, h', rfl⟩
  rw [label_eq_root_of_not_reach hr h₁, label_eq_root_of_not_reach hr h₂]

/-- The rows below an exit of a blob that isn't pendant are those with its sequence on the sites of the blob. -/
theorem mem_arcSide_iff_of_exit (hd : N.Derives M) (hnd : N.BlobsNodeDisjoint) (hr : N.RegularArcs) (hp : N.NonPendantPortsDistinct) {e : E} (he : N.IsTreeArc e) {B : Set E} (hB : N.IsBlob B)
    (hs : N.src e ∈ N.blobVerts B) (hleaf : ¬ N.IsLeaf (N.tgt e)) {y : ι → Bool} (hy : y ∈ M) : y ∈ N.arcSide e ↔ ∀ i, N.site i ∈ B → y i = N.label (N.src e) i := by
  constructor
  · rintro ⟨v, -, hrv, rfl⟩ i hi
    exact hB.label_eq_of_exit he hs hi hrv
  · intro hcon
    obtain ⟨l, hl, rfl⟩ := hd.surjOn hy
    by_contra hnotm
    have hnot : ¬ N.Reach (N.tgt e) l := fun h' => hnotm ⟨l, hl, h', rfl⟩
    have ht : N.tgt e ∉ N.blobVerts B := he.tgt_notMem_blobVerts hB hs
    have hc₁ : N.CrossesAt B e (N.src e) := ⟨hs, Or.inl ⟨rfl, ht⟩⟩
    obtain ⟨w, hw, -⟩ := exists_isBlobTop_reach hs
    by_cases hreach : N.Reach w l
    · rcases hw.position hnd hB hreach with h | ⟨e', he₁, he₂, he₃, he₄⟩
      · exact hr.recomb_not_leaf l (hB.isRecomb_of_isLeaf h hl) hl
      · have hlab : N.label (N.src e) = N.label (N.src e') :=
          hB.label_eq_of_forall hs he₂ fun i hi => (hcon i hi).symm.trans (hB.label_eq_of_exit he₁ he₂ hi he₄)
        have hee := hp B e e' _ _ hB hc₁ ⟨he₂, Or.inl ⟨rfl, he₃⟩⟩ hleaf hlab
        exact hnot (hee ▸ he₄)
    · have hwr : w ≠ N.root := fun h => hreach (h ▸ N.reach_root l)
      obtain ⟨g, hg, hgw⟩ := (hw.eq_root_or_exists hnd hB).resolve_left hwr
      have hc₂ : N.CrossesAt B g w := ⟨hw.1, Or.inr ⟨hgw, hg.src_notMem_blobVerts hB (hgw ▸ hw.1)⟩⟩
      have hlab : N.label (N.src e) = N.label w :=
        hB.label_eq_of_forall hs hw.1 fun i hi => (hcon i hi).symm.trans (hw.label_eq_of_not_reach hnd hB hi hreach)
      have hee := hp B e g _ _ hB hc₁ hc₂ hleaf hlab
      exact ht (hee ▸ hgw ▸ hw.1)

/-- The rows off the arc entering a blob are those with the sequence of its top on the sites of the blob. -/
theorem notMem_arcSide_iff_of_top (hd : N.Derives M) (hnd : N.BlobsNodeDisjoint) (hr : N.RegularArcs) (hp : N.NonPendantPortsDistinct) {e : E} {B : Set E} (hB : N.IsBlob B)
    (htp : N.IsBlobTop B (N.tgt e)) (he : N.IsTreeArc e) {y : ι → Bool} (hy : y ∈ M) : y ∉ N.arcSide e ↔ ∀ i, N.site i ∈ B → y i = N.label (N.tgt e) i := by
  obtain ⟨l, hl, rfl⟩ := hd.surjOn hy
  have hnl : ¬ N.IsLeaf (N.tgt e) := fun hl' => hr.recomb_not_leaf _ (hB.isRecomb_of_isLeaf htp.1 hl') hl'
  constructor
  · intro hnotm i hi
    exact htp.label_eq_of_not_reach hnd hB hi fun h' => hnotm ⟨l, hl, h', rfl⟩
  · rintro hcon ⟨v, hv, hrv, hvl⟩
    obtain rfl := hd.injOn hv hl hvl
    rcases htp.position hnd hB hrv with h | ⟨f, hf₁, hf₂, hf₃, hf₄⟩
    · exact hr.recomb_not_leaf v (hB.isRecomb_of_isLeaf h hl) hl
    · have hc₁ : N.CrossesAt B e (N.tgt e) := ⟨htp.1, Or.inr ⟨rfl, he.src_notMem_blobVerts hB htp.1⟩⟩
      have hlab : N.label (N.tgt e) = N.label (N.src f) :=
        hB.label_eq_of_forall htp.1 hf₂ fun i hi => (hcon i hi).symm.trans (hB.label_eq_of_exit hf₁ hf₂ hi hf₄)
      have hee := hp B e f _ _ hB hc₁ ⟨hf₂, Or.inl ⟨rfl, hf₃⟩⟩ hnl hlab
      exact hf₃ (hee ▸ htp.1)

end Network

variable [LinearOrder ι]

/-- A split of a tree arc and a character of `B` are compatible: not all four corners have a row. -/
theorem no_four_corners (hd : N.Derives M) {f : E} (hf : N.IsTreeArc f) (k : SuperChar M) {a b c d : ι → Bool} (ha : a ∈ N.arcSide f) (hka : charValue k a = true) (hb : b ∈ N.arcSide f)
    (hkb : charValue k b = false) (hc : c ∈ M) (hcA : c ∉ N.arcSide f) (hkc : charValue k c = true) (hdM : d ∈ M) (hdA : d ∉ N.arcSide f) (hkd : charValue k d = false) : False := by
  have hsub := N.arcSide_subset hd f
  rcases treeSplits_compatible N hd (A := N.arcSide f) ⟨f, hf, Or.inl rfl⟩ k with h | h | h | h
  · exact Set.notMem_empty a (h ▸ ⟨ha, hsub ha, hka⟩)
  · refine Set.notMem_empty b (h ▸ ⟨hb, fun hm => ?_⟩)
    rw [hm.2] at hkb
    exact absurd hkb (by simp)
  · exact Set.notMem_empty c (h ▸ ⟨⟨Finset.mem_coe.2 hc, hcA⟩, Finset.mem_coe.2 hc, hkc⟩)
  · refine Set.notMem_empty d (h ▸ ⟨⟨Finset.mem_coe.2 hdM, hdA⟩, fun hm => ?_⟩)
    rw [hm.2] at hkd
    exact absurd hkd (by simp)

variable {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W}

/-- The arc `e` and the edge `e'` of `T̄` have one split on the rows. -/
def Network.SameSplit (N : Network ι V E) (T : SimpleGraph W) (φ : M → W) (e : E) (e' : Sym2 W) : Prop :=
  ∀ x y : M, SameSide T e' (φ x) (φ y) ↔ (x.1 ∈ N.arcSide e ↔ y.1 ∈ N.arcSide e)

/-- The edge `e'` of `T̄` has, on each side, two rows that differ on the sites of the blob `B`. -/
def Network.Strad (N : Network ι V E) (T : SimpleGraph W) (φ : M → W) (B : Set E) (e' : Sym2 W) : Prop :=
  ∃ a₁ a₂ a₃ a₄ : M, SameSide T e' (φ a₁) (φ a₂) ∧ SameSide T e' (φ a₃) (φ a₄) ∧ ¬ SameSide T e' (φ a₁) (φ a₃) ∧
    (∃ i, N.site i ∈ B ∧ a₁.1 i ≠ a₂.1 i) ∧ ∃ i, N.site i ∈ B ∧ a₃.1 i ≠ a₄.1 i

/-- A side of the arc `e` is the set `O` of all the rows with one sequence `z` on the sites of the blob `B`. -/
def Network.IsPortClass (N : Network ι V E) (B : Set E) (e : E) (O : Set M) (z : ι → Bool) : Prop :=
  (∀ y : M, y ∈ O ↔ ∀ i, N.site i ∈ B → y.1 i = z i) ∧ (O = {y | y.1 ∈ N.arcSide e} ∨ O = {y | y.1 ∉ N.arcSide e}) ∧ O.Nonempty

omit [LinearOrder ι] [Finite W] in
/-- An edge of `T̄` with the split of a tree arc doesn't straddle a blob. -/
theorem Network.not_strad_of_sameSplit (hd : N.Derives M) {f : E} (hf : N.IsTreeArc f) {e' : Sym2 W} (hsame : N.SameSplit T φ f e') {B : Set E} (hB : N.IsBlob B) : ¬ N.Strad T φ B e' := by
  rintro ⟨a₁, a₂, a₃, a₄, h₁, h₂, h₃, ⟨i, hi, hne⟩, ⟨j, hj, hne'⟩⟩
  rw [hsame] at h₁ h₂ h₃
  obtain ⟨t, ht⟩ := hB.blobVerts_nonempty
  by_cases hb : N.Reach (N.tgt f) t
  · by_cases h₄ : a₁.1 ∈ N.arcSide f
    · have h₅ : a₃.1 ∉ N.arcSide f := fun h₆ => h₃ (iff_of_true h₄ h₆)
      exact hne' (hf.rows_off_const hd hB ht hb a₃.2 a₄.2 h₅ (fun h₆ => h₅ (h₂.2 h₆)) hj)
    · exact hne (hf.rows_off_const hd hB ht hb a₁.2 a₂.2 h₄ (fun h₆ => h₄ (h₁.2 h₆)) hi)
  · by_cases h₄ : a₁.1 ∈ N.arcSide f
    · exact hne (hf.rows_below_const hB ht hb h₄ (h₁.1 h₄) hi)
    · have h₅ : a₃.1 ∈ N.arcSide f := by
        by_contra h₆
        exact h₃ (iff_of_false h₄ h₆)
      exact hne' (hf.rows_below_const hB ht hb h₅ (h₂.1 h₅) hj)

omit [Finite V] [Finite E] [LinearOrder ι] in
/-- An edge of `T̄` that straddles a blob is internal, and so has a character. -/
theorem Network.Strad.exists_char {B : Set E} {e' : Sym2 W} (hT : IsTBar M T φ edge) (he' : e' ∈ T.edgeSet) (hs : N.Strad T φ B e') : ∃ k, edge k = e' := by
  obtain ⟨a₁, a₂, a₃, a₄, h₁, h₂, h₃, ⟨i, -, hne⟩, ⟨j, -, hne'⟩⟩ := hs
  induction e' with
  | h u v =>
    have huv : T.Adj u v := he'
    have hconn := hT.isTree.connected
    have hrow : ∀ {x y : W}, T.Adj x y → (s(x, y) = s(u, v)) → x ∉ Set.range φ := by
      rintro x y hxy hee ⟨w, rfl⟩
      have hdeg := (hT.mem_range_iff (φ w)).1 ⟨w, rfl⟩
      have honly : ∀ z : M, SameSide T s(u, v) (φ w) (φ z) → z = w := fun z hz => by
        rw [← hee] at hz
        exact hT.label_injective (eq_of_sameSide_of_ncard_le_one hdeg hxy hz)
      by_cases h₄ : SameSide T s(u, v) (φ w) (φ a₁)
      · have h₅ := honly a₁ h₄
        have h₆ := honly a₂ (h₄.trans h₁)
        exact hne (by rw [h₅, h₆])
      · by_cases h₅ : SameSide T s(u, v) (φ w) (φ a₃)
        · have h₆ := honly a₃ h₅
          have h₇ := honly a₄ (h₅.trans h₂)
          exact hne' (by rw [h₆, h₇])
        · exact h₃ (sameSide_of_not_sameSide hconn (fun h' => h₄ h'.symm) (fun h' => h₅ h'.symm))
    exact hT.internal_labelled u v huv (hrow huv rfl) (hrow huv.symm Sym2.eq_swap)

/-- **An edge of `T̄` straddles at most one blob.** A tree arc between two blobs would have all four corners with an edge of `T̄`. -/
theorem Network.Strad.unique (hd : N.Derives M) (hnd : N.BlobsNodeDisjoint) (hT : IsTBar M T φ edge) {e' : Sym2 W} (he' : e' ∈ T.edgeSet) {B₁ B₂ : Set E} (hB₁ : N.IsBlob B₁) (hB₂ : N.IsBlob B₂)
    (h₁ : N.Strad T φ B₁ e') (h₂ : N.Strad T φ B₂ e') : B₁ = B₂ := by
  by_contra hne
  obtain ⟨k, rfl⟩ := h₁.exists_char hT he'
  have hconn := hT.isTree.connected.preconnected
  have hv : ∀ x y : M, SameSide T (edge k) (φ x) (φ y) ↔ charValue k x.1 = charValue k y.1 := fun x y => by
    rw [(hT.side_cut k).sameSide_iff hconn (hT.edge_mem k), hT.side_row, hT.side_row]
  obtain ⟨t₁, ht₁⟩ := hB₁.blobVerts_nonempty
  obtain ⟨t₂, ht₂⟩ := hB₂.blobVerts_nonempty
  have hdisj := Set.disjoint_left.1 (hnd B₁ B₂ hB₁ hB₂ hne)
  have hcls : N.toBlobNode t₁ ≠ N.toBlobNode t₂ := by
    intro heq
    rcases Network.eq_or_exists_isBlob_of_toBlobNode_eq hnd heq with rfl | ⟨B, hB, h₃, h₄⟩
    · exact hdisj ht₁ ht₂
    · have hB₁B : B₁ = B := by
        by_contra hn
        exact Set.disjoint_left.1 (hnd B₁ B hB₁ hB hn) ht₁ h₃
      have hB₂B : B₂ = B := by
        by_contra hn
        exact Set.disjoint_left.1 (hnd B₂ B hB₂ hB hn) ht₂ h₄
      exact hne (hB₁B.trans hB₂B.symm)
  obtain ⟨w, hw, hsep, -⟩ := exists_adj_separating N.blobbedTree_isTree.1 hcls
  obtain ⟨f, hf, hfe⟩ := Network.exists_isTreeArc_of_adj hw
  have hnss : ¬ SameSide N.blobbedTree (N.blobEdge f) (N.toBlobNode t₁) (N.toBlobNode t₂) := by
    change ¬ SameSide N.blobbedTree s(N.toBlobNode (N.src f), N.toBlobNode (N.tgt f)) _ _
    rw [hfe]
    exact hsep
  -- The blob above and the blob below.
  have hcorner : ∀ {B B' : Set E} {t t' : V}, N.IsBlob B → N.IsBlob B' → t ∈ N.blobVerts B → t' ∈ N.blobVerts B' → N.Reach (N.tgt f) t → ¬ N.Reach (N.tgt f) t' →
      N.Strad T φ B (edge k) → N.Strad T φ B' (edge k) → False := by
    intro B B' t t' hB hB' ht ht' hb hnb hs hs'
    have hin : ∀ {a b : M}, (∃ i, N.site i ∈ B ∧ a.1 i ≠ b.1 i) → a.1 ∈ N.arcSide f ∨ b.1 ∈ N.arcSide f := by
      rintro a b ⟨i, hi, hab⟩
      by_contra hcon
      push Not at hcon
      exact hab (hf.rows_off_const hd hB ht hb a.2 b.2 hcon.1 hcon.2 hi)
    have hoff : ∀ {a b : M}, (∃ i, N.site i ∈ B' ∧ a.1 i ≠ b.1 i) → a.1 ∉ N.arcSide f ∨ b.1 ∉ N.arcSide f := by
      rintro a b ⟨i, hi, hab⟩
      by_contra hcon
      push Not at hcon
      exact hab (hf.rows_below_const hB' ht' hnb hcon.1 hcon.2 hi)
    obtain ⟨a₁, a₂, a₃, a₄, h₃, h₄, h₅, hd₁, hd₂⟩ := hs
    obtain ⟨c₁, c₂, c₃, c₄, h₆, h₇, h₈, hd₃, hd₄⟩ := hs'
    rw [hv] at h₃ h₄ h₅ h₆ h₇ h₈
    have hp : ∀ {p : Bool}, charValue k a₁.1 = p → (∃ x ∈ N.arcSide f, charValue k x = p) ∧ ∃ x ∈ N.arcSide f, charValue k x = !p := by
      intro p hp
      have hp₃ : charValue k a₃.1 = !p := by
        rw [← hp]
        revert h₅
        cases charValue k a₁.1 <;> cases charValue k a₃.1 <;> simp
      refine ⟨?_, ?_⟩
      · rcases hin hd₁ with h | h
        · exact ⟨_, h, hp⟩
        · exact ⟨_, h, h₃ ▸ hp⟩
      · rcases hin hd₂ with h | h
        · exact ⟨_, h, hp₃⟩
        · exact ⟨_, h, h₄ ▸ hp₃⟩
    have hq : ∀ {p : Bool}, charValue k c₁.1 = p → (∃ x ∈ M, x ∉ N.arcSide f ∧ charValue k x = p) ∧ ∃ x ∈ M, x ∉ N.arcSide f ∧ charValue k x = !p := by
      intro p hp
      have hp₃ : charValue k c₃.1 = !p := by
        rw [← hp]
        revert h₈
        cases charValue k c₁.1 <;> cases charValue k c₃.1 <;> simp
      refine ⟨?_, ?_⟩
      · rcases hoff hd₃ with h | h
        · exact ⟨_, c₁.2, h, hp⟩
        · exact ⟨_, c₂.2, h, h₆ ▸ hp⟩
      · rcases hoff hd₄ with h | h
        · exact ⟨_, c₃.2, h, hp₃⟩
        · exact ⟨_, c₄.2, h, h₇ ▸ hp₃⟩
    obtain ⟨hpT, hpF⟩ : (∃ x ∈ N.arcSide f, charValue k x = true) ∧ ∃ x ∈ N.arcSide f, charValue k x = false := by
      cases hc : charValue k a₁.1
      · obtain ⟨h₉, h₁₀⟩ := hp hc
        exact ⟨h₁₀, h₉⟩
      · exact hp hc
    obtain ⟨hqT, hqF⟩ : (∃ x ∈ M, x ∉ N.arcSide f ∧ charValue k x = true) ∧ ∃ x ∈ M, x ∉ N.arcSide f ∧ charValue k x = false := by
      cases hc : charValue k c₁.1
      · obtain ⟨h₉, h₁₀⟩ := hq hc
        exact ⟨h₁₀, h₉⟩
      · exact hq hc
    obtain ⟨a, ha, hka⟩ := hpT
    obtain ⟨b, hb', hkb⟩ := hpF
    obtain ⟨c, hc, hcA, hkc⟩ := hqT
    obtain ⟨d, hdM, hdA, hkd⟩ := hqF
    exact no_four_corners hd hf k ha hka hb' hkb hc hcA hkc hdM hdA hkd
  by_cases hb₁ : N.Reach (N.tgt f) t₁
  · by_cases hb₂ : N.Reach (N.tgt f) t₂
    · exact hnss (((hf.sameSide_tgt_iff t₁).2 hb₁).symm.trans ((hf.sameSide_tgt_iff t₂).2 hb₂))
    · exact hcorner hB₁ hB₂ ht₁ ht₂ hb₁ hb₂ h₁ h₂
  · by_cases hb₂ : N.Reach (N.tgt f) t₂
    · exact hcorner hB₂ hB₁ ht₂ ht₁ hb₂ hb₁ h₂ h₁
    · exact hnss (((hf.sameSide_src_iff t₁).2 hb₁).symm.trans ((hf.sameSide_src_iff t₂).2 hb₂))

omit [Finite V] [Finite E] [LinearOrder ι] in
/-- **A new split of `T′` straddles.** With `O` the set of rows with one sequence on a blob with the non-trivial component `C`, the lowest edge of `T̄`, rooted at the central node of `C`, above `O`, straddles the blob, if `O` isn't all that's below it. -/
theorem Network.strad_of_isMinCand (hT : IsTBar M T φ edge) {B : Set E} {C : (incompatGraph M).ConnectedComponent} (hnt : C.supp.Nontrivial) (hsub : ∀ i ∈ C.supp, N.site i ∈ B) {O : Set M} {z : ι → Bool} {e : E}
    (hO : N.IsPortClass B e O z) {b : W} (hb : hT.IsMinCand (hT.center C) O b) (hnot : ¬ N.SameSplit T φ e s(b, hT.par (hT.center C) b)) : N.Strad T φ B s(b, hT.par (hT.center C) b) := by
  obtain ⟨hOi, hOA, ⟨x₀, hx₀⟩⟩ := hO
  obtain ⟨hbc, hOb, -⟩ := hb
  have hadj := (hT.par_spec hbc).1
  have hconn := hT.isTree.connected.preconnected
  obtain ⟨s, hs⟩ := exists_isCut hT.isTree (show s(b, hT.par (hT.center C) b) ∈ T.edgeSet from hadj)
  have hmem := hT.mem_rowsBelow_iff hbc hs
  have hss : ∀ x y : M, SameSide T s(b, hT.par (hT.center C) b) (φ x) (φ y) ↔ (x ∈ hT.rowsBelow (hT.center C) b ↔ y ∈ hT.rowsBelow (hT.center C) b) := fun x y => by
    rw [hs.sameSide_iff hconn hadj, hmem, hmem]
    revert x y
    intro x y
    cases s (φ x) <;> cases s (φ y) <;> cases s (hT.center C) <;> simp
  -- A row below that isn't in `O`.
  have hex : ∃ r' ∈ hT.rowsBelow (hT.center C) b, r' ∉ O := by
    by_contra hcon
    push Not at hcon
    have hOD : O = hT.rowsBelow (hT.center C) b := Set.Subset.antisymm hOb hcon
    apply hnot
    intro x y
    rw [hss, ← hOD]
    rcases hOA with h₁ | h₁
    · rw [h₁]
      rfl
    · rw [h₁]
      simp only [Set.mem_ofPred_eq]
      tauto
  obtain ⟨r', hr', hr'O⟩ := hex
  have hdiff₁ : ∃ i, N.site i ∈ B ∧ x₀.1 i ≠ r'.1 i := by
    by_contra hcon
    push Not at hcon
    refine hr'O ((hOi r').2 fun i hi => ?_)
    rw [← hcon i hi]
    exact (hOi x₀).1 hx₀ i hi
  -- Two rows with other sequences on `C`.
  have h₄ := four_le_card_restrictRows hnt
  have ht₀ : C.supp.domRestrict x₀.1 ∈ restrictRows C.supp M := mem_restrictRows.2 ⟨x₀.1, x₀.2, rfl⟩
  obtain ⟨t₁, ht₁, ht₁₀⟩ := Finset.exists_mem_ne (show 1 < (restrictRows C.supp M).card by omega) (C.supp.domRestrict x₀.1)
  have h₅ : 1 < ((restrictRows C.supp M).erase (C.supp.domRestrict x₀.1)).card := by
    have := Finset.pred_card_le_card_erase (s := restrictRows C.supp M) (a := C.supp.domRestrict x₀.1)
    omega
  obtain ⟨t₂, ht₂, ht₂₁⟩ := Finset.exists_mem_ne h₅ t₁
  obtain ⟨ht₂₀, ht₂M⟩ := Finset.mem_erase.1 ht₂
  obtain ⟨x₃, hx₃, rfl⟩ := mem_restrictRows.1 ht₁
  obtain ⟨x₄, hx₄, rfl⟩ := mem_restrictRows.1 ht₂M
  have hout : ∀ {x : ι → Bool} (hx : x ∈ M), C.supp.domRestrict x ≠ C.supp.domRestrict x₀.1 → (⟨x, hx⟩ : M) ∉ hT.rowsBelow (hT.center C) b := fun {x} hx hne hm =>
    hne (hT.rowsBelow_same_seq hnt hbc hm (hOb hx₀))
  have ho₃ := hout hx₃ ht₁₀
  have ho₄ := hout hx₄ ht₂₀
  refine ⟨x₀, r', ⟨x₃, hx₃⟩, ⟨x₄, hx₄⟩, (hss _ _).2 (iff_of_true (hOb hx₀) hr'), (hss _ _).2 (iff_of_false ho₃ ho₄), fun h' => ho₃ (((hss _ _).1 h').1 (hOb hx₀)), hdiff₁, ?_⟩
  have hne : C.supp.domRestrict x₃ ≠ C.supp.domRestrict x₄ := Ne.symm ht₂₁
  by_contra hcon
  push Not at hcon
  exact hne (funext fun j => hcon j.1 (hsub j.1 j.2))

/-- **What a new split of `T′` is.** If the split of a tree arc isn't in `T̄`, then a side of the arc is the set of the rows with one sequence on a blob with a site of a non-trivial component. -/
theorem Network.exists_portClass (hd : N.Derives M) (hnd : N.BlobsNodeDisjoint) (hr : N.RegularArcs) (hp : N.NonPendantPortsDistinct) (hdeg : N.DegreeCond) (hT : IsTBar M T φ edge)
    (hmerge : ∀ B, N.IsBlob B → (∃ i j, N.site i ∈ B ∧ (incompatGraph M).Adj i j) ∨ ∀ i j, N.site i ∈ B → N.site j ∈ B → i = j) {e : E} (he : N.IsTreeArc e)
    (hnew : ¬ ∃ e' ∈ T.edgeSet, N.SameSplit T φ e e') :
    ∃ (B : Set E) (O : Set M) (z : ι → Bool), N.IsBlob B ∧ (∃ i j, N.site i ∈ B ∧ (incompatGraph M).Adj i j) ∧ N.IsPortClass B e O z := by
  have hlab := N.rowClass_labelled hd hdeg
  obtain ⟨⟨y₁, hy₁⟩, ⟨y₀, hy₀⟩⟩ := he.exists_rows hd hlab
  -- The split isn't a character of `B`.
  have hch : N.arcSide e ∉ charSplits M := by
    intro hm
    obtain ⟨e', he', hs⟩ := exists_edge_of_mem_splitSides hT.isTree.connected (hT.mem_splitSides_of_charSplits hy₁ hy₀ fun _ _ => hm)
    exact hnew ⟨e', he', fun x y => hs x y⟩
  have hleaf : ¬ N.IsLeaf (N.tgt e) := by
    intro hl
    obtain ⟨e', he', hs⟩ := exists_edge_of_mem_splitSides hT.isTree.connected (hT.mem_splitSides_of_charSplits hy₁ hy₀ fun h₁ _ => by
      rw [Network.arcSide_eq_singleton hl, Set.encard_singleton] at h₁
      simp at h₁)
    exact hnew ⟨e', he', fun x y => hs x y⟩
  have hsite : ¬ ∃ i, N.site i = e := by
    rintro ⟨i, hi⟩
    have hti : N.IsTreeArc (N.site i) := hi ▸ he
    have hc := N.mem_supp_iff_of_isTreeArc (M := M) hd hti
    obtain ⟨lb, hlb, hrb⟩ := Network.exists_isLeaf_reach (N := N) (N.tgt e)
    have hS₀ : ((incompatGraph M).connectedComponentMk i).supp.domRestrict (N.label (N.tgt e)) ∈
        restrictRows ((incompatGraph M).connectedComponentMk i).supp M := by
      refine mem_restrictRows.2 ⟨N.label lb, hd.mapsTo hlb, ?_⟩
      funext j
      obtain ⟨j, hj⟩ := j
      obtain rfl := (hc j).1 hj
      exact he.label_eq_iff_reach hi |>.2 hrb
    exact hch ⟨_, Or.inl ((N.charSide_eq_arcSide_of_site hd he hi hc hS₀).1 rfl).symm⟩
  -- What a blob can be.
  have hcases : ∀ B, N.IsBlob B → (∃ i j, N.site i ∈ B ∧ (incompatGraph M).Adj i j) ∨ (∃ c : (incompatGraph M).ConnectedComponent, ∀ i, N.site i ∈ B ↔ i ∈ c.supp) := by
    intro B hB
    rcases hmerge B hB with h | h
    · exact Or.inl h
    by_cases hs : ∃ i, N.site i ∈ B
    · obtain ⟨i, hi⟩ := hs
      by_cases hadj : ∃ j, (incompatGraph M).Adj i j
      · obtain ⟨j, hj⟩ := hadj
        exact Or.inl ⟨i, j, hi, hj⟩
      · push Not at hadj
        refine Or.inr ⟨(incompatGraph M).connectedComponentMk i, fun j => ?_⟩
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
        constructor
        · intro hj
          rw [h j i hj hi]
        · intro hreach
          have hreach' := hreach.symm
          rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
          rcases Relation.ReflTransGen.cases_head hreach' with h' | ⟨b, hb, -⟩
          · rw [← h']
            exact hi
          · exact absurd hb (hadj b)
    · push Not at hs
      exact absurd (N.isLeaf_tgt_of_siteFree hnd hr hp hdeg hB hs he) hleaf
  obtain ⟨lb, hlb, hrb⟩ := Network.exists_isLeaf_reach (N := N) (N.tgt e)
  by_cases hs : ∃ B, N.IsBlob B ∧ N.src e ∈ N.blobVerts B
  · obtain ⟨B, hB, hsB⟩ := hs
    have hport := fun (y : ι → Bool) (hy : y ∈ M) => N.mem_arcSide_iff_of_exit hd hnd hr hp he hB hsB hleaf hy
    rcases hcases B hB with hnt | ⟨c, hc⟩
    · refine ⟨B, {y | y.1 ∈ N.arcSide e}, N.label (N.src e), hB, hnt, fun y => hport y.1 y.2, Or.inl rfl, ⟨⟨N.label lb, hd.mapsTo hlb⟩, lb, hlb, hrb, rfl⟩⟩
    · exfalso
      have hS₀ : c.supp.domRestrict (N.label (N.src e)) ∈ restrictRows c.supp M := by
        refine mem_restrictRows.2 ⟨N.label lb, hd.mapsTo hlb, ?_⟩
        funext i
        exact hB.label_eq_of_exit he hsB ((hc i.1).2 i.2) hrb
      have hexit : ∀ l, N.IsLeaf l → ¬ N.Reach (N.tgt e) l → ∃ i, N.site i ∈ B ∧ N.label l i ≠ N.label (N.src e) i := by
        intro l hl hnot
        by_contra hcon
        push Not at hcon
        exact hnot ((N.mem_arcSide_iff hd hl e).1 ((hport _ (hd.mapsTo hl)).2 hcon))
      exact hch ⟨_, Or.inl (N.charSide_eq_arcSide_of_exit hd hB hc he hsB hexit hS₀ rfl).symm⟩
  by_cases ht : ∃ B, N.IsBlob B ∧ N.tgt e ∈ N.blobVerts B
  · obtain ⟨B, hB, htB⟩ := ht
    have htp : N.IsBlobTop B (N.tgt e) := ⟨htB, fun f hf' h => he (hB.onCycle_of_mem ((he.eq_of_tgt_eq h) ▸ hf'))⟩
    have hport := fun (y : ι → Bool) (hy : y ∈ M) => N.notMem_arcSide_iff_of_top hd hnd hr hp hB htp he hy
    rcases hcases B hB with hnt | ⟨c, hc⟩
    · exact ⟨B, {y | y.1 ∉ N.arcSide e}, N.label (N.tgt e), hB, hnt, fun y => hport y.1 y.2, Or.inr rfl, ⟨⟨y₀.1, y₀.2⟩, hy₀⟩⟩
    · exfalso
      have hS₀ : c.supp.domRestrict (N.label (N.tgt e)) ∈ restrictRows c.supp M := by
        refine mem_restrictRows.2 ⟨y₀.1, y₀.2, ?_⟩
        funext i
        exact (hport y₀.1 y₀.2).1 hy₀ i.1 ((hc i.1).2 i.2)
      have hexit : ∀ f, N.IsTreeArc f → N.src f ∈ N.blobVerts B → N.tgt f ∉ N.blobVerts B → ∃ i, N.site i ∈ B ∧ N.label (N.src f) i ≠ N.label (N.tgt e) i := by
        intro f hf hf₂ hf₃
        by_contra hcon
        push Not at hcon
        have hc₁ : N.CrossesAt B e (N.tgt e) := ⟨htB, Or.inr ⟨rfl, he.src_notMem_blobVerts hB htB⟩⟩
        have hc₂ : N.CrossesAt B f (N.src f) := ⟨hf₂, Or.inl ⟨rfl, hf₃⟩⟩
        have hlabs := hB.label_eq_of_forall htB hf₂ fun i hi => (hcon i hi).symm
        have hee := hp B e f _ _ hB hc₁ hc₂ hleaf hlabs
        exact hf₃ (hee ▸ htB)
      have h := N.charSide_eq_diff_arcSide_of_top hd hr.recomb_not_leaf hnd hB hc htp hexit hS₀ rfl
      have h₂ := charSplits_diff (⟨_, Or.inl rfl⟩ : charSide (⟨c, ⟨_, hS₀⟩⟩ : SuperChar M) ∈ charSplits M)
      rw [h, Set.sdiff_sdiff_cancel_left (N.arcSide_subset hd e)] at h₂
      exact hch h₂
  · exact absurd (hr.arc_labelled e he hs ht hleaf) hsite

/-- **The treeness inequality, for blobs with a site of a non-trivial component** (`g:treeness_merged`). Among networks whose blobs are node-disjoint, with `RegularArcs`, `NonPendantPortsDistinct` and `DegreeCond`, where each blob has a site of a non-trivial component of `G(M)`, or at most one site, the treeness is at most the number of edges of `T̄`. So a blob can merge any components, as long as one of them is non-trivial.

Equality doesn't then say that `T′` is `T̄`, unlike `treeness_le_and_eq_iff`. The other case, a blob with at least two sites, all of them isolated in `G(M)`, can break the inequality: `treeness_merged_false`.

The proof is an injection from the arcs of `T′` to the edges of `T̄`. An arc with a split of `T̄` goes to the edge with that split. The other arcs have a side `O` that's all the rows with one sequence on a blob `B`, by `Network.exists_portClass`. It goes to the lowest edge above `O`, with `T̄` rooted at the central node of a non-trivial component of `B`. That edge has two rows differing on `B` on each side, and so it isn't the split of an arc, and `B` is determined by it (`Network.Strad.unique`). If two arcs at `B` went to one edge, a site of `B` on which they differ would give two characters of one component, each with the root on its 1-side. -/
theorem treeness_le_of_merged (N : Network ι V E) (hd : N.Derives M) (hnd : N.BlobsNodeDisjoint)
    (hmerge : ∀ B, N.IsBlob B → (∃ i j, N.site i ∈ B ∧ (incompatGraph M).Adj i j) ∨ ∀ i j, N.site i ∈ B → N.site j ∈ B → i = j) (hr : N.RegularArcs) (hp : N.NonPendantPortsDistinct) (hdeg : N.DegreeCond)
    (hT : IsTBar M T φ edge) : N.treeness ≤ T.edgeSet.ncard := by
  have hconn := hT.isTree.connected.preconnected
  have hlab := N.rowClass_labelled hd hdeg
  have hne : Nonempty W := hT.isTree.connected.nonempty
  -- The central node of a blob.
  have hcen : ∀ B : Set E, ∃ c : W, N.IsBlob B → (∃ i j, N.site i ∈ B ∧ (incompatGraph M).Adj i j) →
      ∃ C : (incompatGraph M).ConnectedComponent, C.supp.Nontrivial ∧ (∀ i ∈ C.supp, N.site i ∈ B) ∧ c = hT.center C := by
    intro B
    by_cases hh : N.IsBlob B ∧ ∃ i j, N.site i ∈ B ∧ (incompatGraph M).Adj i j
    · obtain ⟨hB, i, j, hi, hij⟩ := hh
      have hnt : ((incompatGraph M).connectedComponentMk i).supp.Nontrivial :=
        ⟨i, rfl, j, SimpleGraph.ConnectedComponent.eq.2 hij.reachable.symm, hij.ne⟩
      obtain ⟨B', hB', hsub⟩ := converse N hd _ hnt
      have hBB : B' = B := by
        by_contra hn
        exact Set.disjoint_left.1 (hnd B' B hB' hB hn) (Network.src_mem_blobVerts (hsub i rfl)) (Network.src_mem_blobVerts hi)
      exact ⟨_, fun _ _ => ⟨_, hnt, hBB ▸ hsub, rfl⟩⟩
    · exact ⟨hne.some, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ hh⟩
  choose cen hcen using hcen
  -- The assignment.
  have hex : ∀ e : {e // N.IsTreeArc e}, ∃ e' : T.edgeSet, N.SameSplit T φ e.1 e'.1 ∨ ∃ B O z b, N.IsBlob B ∧ (∃ i j, N.site i ∈ B ∧ (incompatGraph M).Adj i j) ∧ N.IsPortClass B e.1 O z ∧
      hT.IsMinCand (cen B) O b ∧ e'.1 = s(b, hT.par (cen B) b) ∧ N.Strad T φ B e'.1 := by
    rintro ⟨e, he⟩
    by_cases hold : ∃ e' ∈ T.edgeSet, N.SameSplit T φ e e'
    · obtain ⟨e', he', hs⟩ := hold
      exact ⟨⟨e', he'⟩, Or.inl hs⟩
    · obtain ⟨B, O, z, hB, hnt, hO⟩ := N.exists_portClass hd hnd hr hp hdeg hT hmerge he hold
      obtain ⟨C, hCnt, hsub, hc⟩ := hcen B hB hnt
      obtain ⟨x₀, hx₀⟩ := id hO.2.2
      have hsame : ∀ y ∈ O, charValue (IsTBar.charOf C x₀.2) y.1 = true := fun y hy => by
        refine charValue_mk_iff.2 (funext fun j => ?_)
        change y.1 j.1 = x₀.1 j.1
        rw [(hO.1 y).1 hy j.1 (hsub j.1 j.2), (hO.1 x₀).1 hx₀ j.1 (hsub j.1 j.2)]
      obtain ⟨b₀, hb₀, -, hb₀'⟩ := hT.exists_below_of_side (IsTBar.charOf C x₀.2) (hT.side_center hCnt rfl)
      obtain ⟨b, hb⟩ := hT.exists_isMinCand (c := hT.center C) (O := O) ⟨x₀, hx₀⟩ ⟨b₀, hb₀, fun y hy => (hb₀' y).2 (hsame y hy)⟩
      have hedge : s(b, hT.par (hT.center C) b) ∈ T.edgeSet := (hT.par_spec hb.1).1
      have hst := N.strad_of_isMinCand hT hCnt hsub hO hb fun hs => hold ⟨_, hedge, hs⟩
      refine ⟨⟨_, hedge⟩, Or.inr ⟨B, O, z, b, hB, hnt, hO, hc ▸ hb, by rw [hc], hst⟩⟩
  choose g hg using hex
  -- Two arcs with one split are one arc.
  have huniq : ∀ {e₁ e₂ : E}, N.IsTreeArc e₁ → N.IsTreeArc e₂ → (∀ x y : M, (x.1 ∈ N.arcSide e₁ ↔ y.1 ∈ N.arcSide e₁) ↔ (x.1 ∈ N.arcSide e₂ ↔ y.1 ∈ N.arcSide e₂)) → e₁ = e₂ := by
    intro e₁ e₂ he₁ he₂ hsp
    refine Network.blobEdge_injective he₁ he₂ (edge_eq_of_sameSide_iff N.blobbedTree_isTree.1 hlab (Network.blobEdge_mem_edgeSet he₁) fun x y => ?_)
    rw [he₁.sameSide_rowClass_iff hd x y, he₂.sameSide_rowClass_iff hd x y]
    exact hsp x y
  have hinj : Function.Injective g := by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h₁₂
    refine Subtype.ext ?_
    change e₁ = e₂
    rcases hg ⟨e₁, he₁⟩ with hs₁ | ⟨B₁, O₁, z₁, b₁, hB₁, hnt₁, hO₁, hb₁, he₁', hst₁⟩ <;> rcases hg ⟨e₂, he₂⟩ with hs₂ | ⟨B₂, O₂, z₂, b₂, hB₂, hnt₂, hO₂, hb₂, he₂', hst₂⟩
    · refine huniq he₁ he₂ fun x y => ?_
      rw [← hs₁ x y, ← hs₂ x y, h₁₂]
    · rw [h₁₂] at hs₁
      exact absurd hst₂ (N.not_strad_of_sameSplit hd he₁ hs₁ hB₂)
    · rw [← h₁₂] at hs₂
      exact absurd hst₁ (N.not_strad_of_sameSplit hd he₂ hs₂ hB₁)
    · rw [h₁₂] at he₁' hst₁
      obtain rfl := hst₁.unique hd hnd hT (g ⟨e₂, he₂⟩).2 hB₁ hB₂ hst₂
      have hD : hT.rowsBelow (cen B₁) b₁ = hT.rowsBelow (cen B₁) b₂ := by
        ext z'
        change ¬ SameSide T s(b₁, hT.par (cen B₁) b₁) (φ z') (cen B₁) ↔ ¬ SameSide T s(b₂, hT.par (cen B₁) b₂) (φ z') (cen B₁)
        rw [← he₁', he₂']
      obtain ⟨x₁, hx₁⟩ := id hO₁.2.2
      obtain ⟨x₂, hx₂⟩ := id hO₂.2.2
      by_cases hdiff : ∃ i, N.site i ∈ B₁ ∧ x₁.1 i ≠ x₂.1 i
      · -- A site of the blob where they differ.
        exfalso
        obtain ⟨i, hi, hxi⟩ := hdiff
        have hcomp : ∀ j ∈ ((incompatGraph M).connectedComponentMk i).supp, N.site j ∈ B₁ := by
          intro j hj
          by_cases hnt : ((incompatGraph M).connectedComponentMk i).supp.Nontrivial
          · obtain ⟨B', hB', hsub⟩ := converse N hd _ hnt
            have hBB : B' = B₁ := by
              by_contra hn
              exact Set.disjoint_left.1 (hnd B' B₁ hB' hB₁ hn) (Network.src_mem_blobVerts (hsub i rfl)) (Network.src_mem_blobVerts hi)
            exact hBB ▸ hsub j hj
          · have : j = i := by
              by_contra hne'
              exact hnt ⟨j, hj, i, rfl, hne'⟩
            rw [this]
            exact hi
        let c₀ := (incompatGraph M).connectedComponentMk i
        have hkne : IsTBar.charOf c₀ x₁.2 ≠ IsTBar.charOf c₀ x₂.2 := fun heq => by
          have h₃ := congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.1 heq).2)
          exact hxi (congrFun h₃ ⟨i, rfl⟩)
        have hrows : ∀ {O : Set M} {z : ι → Bool} {x : M}, N.IsPortClass B₁ e₁ O z ∨ N.IsPortClass B₁ e₂ O z → x ∈ O → ∀ y ∈ O, charValue (IsTBar.charOf c₀ x.2) y.1 = true := by
          intro O z x hO hx y hy
          refine charValue_mk_iff.2 (funext fun j => ?_)
          change y.1 j.1 = x.1 j.1
          rcases hO with hO | hO
          · rw [(hO.1 y).1 hy j.1 (hcomp j.1 j.2), (hO.1 x).1 hx j.1 (hcomp j.1 j.2)]
          · rw [(hO.1 y).1 hy j.1 (hcomp j.1 j.2), (hO.1 x).1 hx j.1 (hcomp j.1 j.2)]
        have hside : ∀ {k k' : SuperChar M} {O O' : Set M} {b b' : W} {x' : M}, k ≠ k' → k.1 = k'.1 → hT.IsMinCand (cen B₁) O b → O' ⊆ hT.rowsBelow (cen B₁) b → (∀ y ∈ O, charValue k y.1 = true) →
            x' ∈ O' → charValue k' x'.1 = true → hT.side k (cen B₁) = true := by
          intro k k' O O' b b' x' hkk hcc hb hO' hk hx' hkx'
          cases hsv : hT.side k (cen B₁)
          · exfalso
            obtain ⟨b₀, hb₀, -, hb₀'⟩ := hT.exists_below_of_side k hsv
            have h₃ := hb.2.2 b₀ hb₀ fun y hy => (hb₀' y).2 (hk y hy)
            exact charValue_disjoint hkk hcc ((hb₀' x').1 (h₃ (hO' hx'))) hkx'
          · rfl
        have hs₁ := hside (b' := b₁) hkne rfl hb₁ (hD ▸ hb₂.2.1) (hrows (Or.inl hO₁) hx₁) hx₂ (IsTBar.charValue_charOf c₀ x₂.2)
        have hs₂ := hside (b' := b₂) hkne.symm rfl hb₂ (hD ▸ hb₁.2.1) (hrows (Or.inr hO₂) hx₂) hx₁ (IsTBar.charValue_charOf c₀ x₁.2)
        exact hkne (hT.side_unique rfl hs₁ hs₂)
      · -- One sequence: one set of rows.
        push Not at hdiff
        have hOO : O₁ = O₂ := by
          ext y
          rw [hO₁.1 y, hO₂.1 y]
          have hzz : ∀ i, N.site i ∈ B₁ → z₁ i = z₂ i := fun i hi => by
            rw [← (hO₁.1 x₁).1 hx₁ i hi, ← (hO₂.1 x₂).1 hx₂ i hi]
            exact hdiff i hi
          constructor
          · exact fun h i hi => (h i hi).trans (hzz i hi)
          · exact fun h i hi => (h i hi).trans (hzz i hi).symm
        refine huniq he₁ he₂ fun x y => ?_
        have hiff : ∀ {e : E}, (O₁ = {y : M | y.1 ∈ N.arcSide e} ∨ O₁ = {y : M | y.1 ∉ N.arcSide e}) → ((x.1 ∈ N.arcSide e ↔ y.1 ∈ N.arcSide e) ↔ (x ∈ O₁ ↔ y ∈ O₁)) := by
          intro e h
          rcases h with h | h
          · rw [h]
            rfl
          · rw [h]
            simp only [Set.mem_ofPred_eq]
            tauto
        rw [hiff hO₁.2.1, hiff (hOO ▸ hO₂.2.1)]
  have hcard := Nat.card_le_card_of_injective g hinj
  rw [Nat.card_coe_set_eq] at hcard
  exact hcard

end Merged

/-! ### Equality doesn't give `T′ = T̄` -/

section Tie

/-- The rows `10000, 01000, 11000, 00100, 00010, 00001`. The sites `0, 1` are a component, and the others are isolated. -/
def tieRows : Finset (Fin 5 → Bool) :=
  {ofBits [1, 0, 0, 0, 0], ofBits [0, 1, 0, 0, 0], ofBits [1, 1, 0, 0, 0], ofBits [0, 0, 1, 0, 0], ofBits [0, 0, 0, 1, 0], ofBits [0, 0, 0, 0, 1]}

/-- A blob with the sites `0, 1, 2`, and an exit for each of its five sequences. The exit of `000` leads to the rows `00010, 00001`. -/
def tieNet : Network (Fin 5) (Fin 12) (Fin 12) :=
  mkNet (tbl [0, 0, 1, 3, 2, 0, 1, 3, 2, 4, 5, 5]) (tbl [1, 2, 3, 4, 4, 5, 6, 7, 8, 9, 10, 11]) 0 (tbl [0, 2, 1, 10, 11])
    (bitsOf [[0, 0, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, 1, 0, 0], [1, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 0], [1, 0, 0, 0, 0], [1, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `T̄` for `tieRows`, as a network: a blob with the sites `0, 1`, and the other rows below the exit of `00`. -/
def tieStarNet : Network (Fin 5) (Fin 11) (Fin 11) :=
  mkNet (tbl [0, 0, 1, 2, 1, 2, 3, 0, 7, 7, 7]) (tbl [1, 2, 3, 3, 4, 5, 6, 7, 8, 9, 10]) 0 (tbl [0, 1, 8, 9, 10])
    (bitsOf [[0, 0, 0, 0, 0], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 1, 0, 0, 0], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def tieAc : Fin 12 → Option (Fin 1) := colourOf [1, 1, 1, 1, 1]
def tieVc : Fin 12 → Option (Fin 1) := colourOf [1, 1, 1, 1, 1]
def tieStarAc : Fin 11 → Option (Fin 1) := colourOf [1, 1, 1, 1]
def tieStarVc : Fin 11 → Option (Fin 1) := colourOf [1, 1, 1, 1]

theorem tieNet_derives : tieNet.Derives tieRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem tieNet_obeys (c : Crossover) : tieNet.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem tieStarNet_derives : tieStarNet.Derives tieRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem tieNet_cycle : ∀ k, tieNet.IsCycle {e | tieAc e = some k} := by
  intro k
  refine ⟨0, 4, [0, 2, 3], [1, 4], ⟨⟨3, 4, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, (by decide +kernel : tieNet.tgt 3 = (4 : Fin 12))⟩, ⟨by decide +kernel, by decide +kernel, (by decide +kernel : tieNet.tgt 4 = (4 : Fin 12))⟩, by decide, ?_⟩, ?_⟩
  · decide +kernel
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    ext e
    change tieAc e = some 0 ↔ (e ∈ [(0 : Fin 12), 2, 3] ∨ e ∈ [(1 : Fin 12), 4])
    revert e
    decide +kernel

theorem tieNet_cover : GallCover tieNet tieAc tieVc :=
  GallCover.of_cycle tieNet_cycle (fun e v => if e = 5 then decide (v = 5 ∨ 10 ≤ v.val) else decide (v = tieNet.tgt e)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem tieStarNet_cover : GallCover tieStarNet tieStarAc tieStarVc :=
  GallCover.of_decide (fun _ => 0) (fun _ => 2) (fun _ => 1) (fun _ => 3) (fun e v => if e = 7 then decide (7 ≤ v.val) else decide (v = tieStarNet.tgt e)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem tieNet_degree : tieNet.DegreeCond :=
  tieNet_cover.degree_cond₂ (tbl [5, 5, 5, 5, 5, 5, 0, 0, 0, 0, 0, 0]) (tbl [6, 6, 6, 6, 6, 10, 0, 0, 0, 0, 0, 0]) (tbl [8, 8, 8, 8, 8, 11, 0, 0, 0, 0, 0, 0])
    (tbl [5, 5, 5, 5, 5, 0, 0, 0, 0, 0, 0, 0]) (tbl [6, 6, 6, 6, 6, 10, 0, 0, 0, 0, 0, 0]) (tbl [8, 8, 8, 8, 8, 11, 0, 0, 0, 0, 0, 0]) (by decide +kernel)

theorem tieStarNet_degree : tieStarNet.DegreeCond :=
  tieStarNet_cover.degree_cond₂ (tbl [4, 4, 4, 4, 0, 0, 0, 7, 0, 0, 0]) (tbl [5, 5, 5, 5, 0, 0, 0, 8, 0, 0, 0]) (tbl [6, 6, 6, 6, 0, 0, 0, 9, 0, 0, 0])
    (tbl [4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0]) (tbl [5, 5, 5, 5, 0, 0, 0, 8, 0, 0, 0]) (tbl [6, 6, 6, 6, 0, 0, 0, 9, 0, 0, 0]) (by decide +kernel)

theorem tieNet_hr : ∀ e f, e ≠ f → tieNet.tgt e = tieNet.tgt f → ∃ g, tieNet.src g = tieNet.tgt e := by decide +kernel

theorem tieStarNet_hr : ∀ e f, e ≠ f → tieStarNet.tgt e = tieStarNet.tgt f → ∃ g, tieStarNet.src g = tieStarNet.tgt e := by decide +kernel

theorem tieNet_hl : ∀ e, tieAc e = none → tieVc (tieNet.src e) = none → tieVc (tieNet.tgt e) = none →
    (∃ g, tieNet.src g = tieNet.tgt e) → ∃ i, tieNet.site i = e := by
  decide +kernel

theorem tieStarNet_hl : ∀ e, tieStarAc e = none → tieStarVc (tieStarNet.src e) = none → tieStarVc (tieStarNet.tgt e) = none →
    (∃ g, tieStarNet.src g = tieStarNet.tgt e) → ∃ i, tieStarNet.site i = e := by
  decide +kernel

theorem tieStarNet_htop : ∀ k e w, tieStarVc (tieStarNet.src e) = some k → tieStarVc (tieStarNet.tgt e) ≠ some k → tieStarVc w = some k →
    (∀ f, tieStarAc f = some k → tieStarNet.tgt f ≠ w) → w ≠ tieStarNet.root → ∃ i, tieStarAc (tieStarNet.site i) = some k ∧
      tieStarNet.label (tieStarNet.src e) i ≠ tieStarNet.label w i := by
  decide +kernel

theorem tieNet_ports : tieNet.NonPendantPortsDistinct :=
  tieNet_cover.nonPendantPortsDistinct_of_decide (by decide +kernel)

theorem tieStarNet_fullyDecomposed : tieStarNet.IsFullyDecomposedFor (incompatGraph tieRows) :=
  tieStarNet_cover.isFullyDecomposedFor (tbl [0, 0, 1, 2, 3] : Fin 5 → Fin 4)
    (by unfold Incompatible; decide +kernel) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem tieStarNet_efficient : tieStarNet.IsEfficient :=
  tieStarNet_cover.isEfficient (by decide +kernel) (by decide +kernel)

theorem tieAc_card : Fintype.card {e // tieAc e = none} = 7 := by decide +kernel

theorem tieStarAc_card : Fintype.card {e // tieStarAc e = none} = 7 := by decide +kernel

/-- In an explicit network, the node of `T′` next to a leaf off the blobs is the source of its arc. -/
theorem GallCover.neighbor_of_leaf {ι V E κ : Type*} [Finite V] [Finite E] {N : Network ι V E} {ac : E → Option κ} {vc : V → Option κ} (h : GallCover N ac vc) {e : E} (hl : N.IsLeaf (N.tgt e)) (hv : vc (N.tgt e) = none)
    {a : N.BlobNode} (hadj : N.blobbedTree.Adj (N.toBlobNode (N.tgt e)) a) : a = N.toBlobNode (N.src e) := by
  obtain ⟨k, hk, hs⟩ := Network.exists_isTreeArc_of_adj hadj
  rcases Sym2.eq_iff.1 hs with ⟨h₁, -⟩ | ⟨h₁, h₂⟩
  · obtain ⟨h₃, h₄⟩ := h.eq_of_toBlobNode_eq h₁
    rw [hv] at h₃
    exact absurd (h₄ h₃) (hl k)
  · obtain ⟨h₃, h₄⟩ := h.eq_of_toBlobNode_eq h₂
    rw [hv] at h₃
    have htt : N.tgt e = N.tgt k := (h₄ h₃).symm
    obtain rfl := hk.eq_of_tgt_eq htt
    exact h₁.symm

variable {W : Type*} [Finite W] {T : SimpleGraph W} {φ : tieRows → W} {edge : SuperChar tieRows → Sym2 W}

/-- **With a merged blob, equality doesn't give `T′ = T̄`** (`g:treeness_merged_tie`). `tieNet`'s blob merges the non-trivial component of the sites `0, 1` with the isolated site `2`. It has the conditions of `treeness_le_of_merged`. Its treeness is `7`, the number of edges of `T̄`, and `T′` isn't `T̄`: in `T′` the rows `10000` and `00100` hang from one node. So the "if and only if" of `treeness_le_and_eq_iff` doesn't survive. -/
theorem treeness_merged_tie (c : Crossover) (hT : IsTBar tieRows T φ edge) :
    tieNet.Obeys c ∧ tieNet.Derives tieRows ∧ tieNet.BlobsNodeDisjoint ∧ tieNet.RegularArcs ∧ tieNet.NonPendantPortsDistinct ∧ tieNet.DegreeCond ∧
      (∃ B, tieNet.IsBlob B ∧ tieNet.site 0 ∈ B ∧ tieNet.site 2 ∈ B ∧ (incompatGraph tieRows).Adj 0 1 ∧ ∀ j, ¬ (incompatGraph tieRows).Adj 2 j) ∧
      (∀ B, tieNet.IsBlob B → (∃ i j, tieNet.site i ∈ B ∧ (incompatGraph tieRows).Adj i j) ∨ ∀ i j, tieNet.site i ∈ B → tieNet.site j ∈ B → i = j) ∧
      tieNet.treeness = 7 ∧ T.edgeSet.ncard = 7 ∧
      ¬ ∃ f : tieNet.blobbedTree ≃g T, ∀ v r (hr : r ∈ tieRows), tieNet.IsLeaf v → tieNet.label v = r → f (tieNet.toBlobNode v) = φ ⟨r, hr⟩ := by
  have hS : tieStarNet.IsTreeNormalStructural := tieStarNet_cover.isTreeNormalStructural tieStarNet_hr tieStarNet_htop tieStarNet_hl
  obtain ⟨g, hg⟩ := tieStarNet.exists_iso_of_isTreeNormalStructural tieStarNet_derives tieStarNet_fullyDecomposed tieStarNet_efficient.perBlob hS tieStarNet_degree hT
  have hinc : (incompatGraph tieRows).Adj 0 1 := by
    change Incompatible tieRows 0 1
    unfold Incompatible
    decide +kernel
  refine ⟨tieNet_obeys c, tieNet_derives, tieNet_cover.nodeDisjoint, ⟨GallCover.recomb_not_leaf tieNet_hr, tieNet_cover.arc_labelled tieNet_hl⟩, tieNet_ports, tieNet_degree,
    ⟨_, tieNet_cover.isBlob_color 0, by decide +kernel, by decide +kernel, hinc, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro j
    change ¬ Incompatible tieRows 2 j
    unfold Incompatible
    revert j
    decide +kernel
  · intro B hB
    obtain ⟨k, rfl⟩ := (tieNet_cover.isBlob_iff B).1 hB
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact Or.inl ⟨0, 1, by decide +kernel, hinc⟩
  · rw [tieNet_cover.treeness_eq, tieAc_card]
  · rw [ncard_edgeSet_iso g, ← Network.treeness_eq_ncard_edgeSet, tieStarNet_cover.treeness_eq, tieStarAc_card]
  · rintro ⟨f, hf⟩
    have hA₁ : tieNet.blobbedTree.Adj (tieNet.toBlobNode 6) (tieNet.toBlobNode 0) := by
      have h₁ := Network.blobbedTree_adj (tieNet_cover.tree 6 (by decide +kernel))
      have h₂ : tieNet.toBlobNode (tieNet.src 6) = tieNet.toBlobNode 0 := tieNet_cover.toBlobNode_eq_of_vc_eq (k := 0) (by decide +kernel) (by decide +kernel)
      rw [h₂] at h₁
      exact h₁.symm
    have hA₂ : tieNet.blobbedTree.Adj (tieNet.toBlobNode 8) (tieNet.toBlobNode 0) := by
      have h₁ := Network.blobbedTree_adj (tieNet_cover.tree 8 (by decide +kernel))
      have h₂ : tieNet.toBlobNode (tieNet.src 8) = tieNet.toBlobNode 0 := tieNet_cover.toBlobNode_eq_of_vc_eq (k := 0) (by decide +kernel) (by decide +kernel)
      rw [h₂] at h₁
      exact h₁.symm
    have hrow : ∀ (v : Fin 12) (u : Fin 11) (r : Fin 5 → Bool) (hr : r ∈ tieRows), tieNet.IsLeaf v → tieNet.label v = r → tieStarNet.IsLeaf u → tieStarNet.label u = r → (f.trans g.symm) (tieNet.toBlobNode v) = tieStarNet.toBlobNode u := by
      intro v u r hr hv hvr hu hur
      apply g.injective
      change g (g.symm (f (tieNet.toBlobNode v))) = _
      rw [RelIso.apply_symm_apply, hf v r hr hv hvr, hg u r hr hu hur]
    have hB₁ := (SimpleGraph.Iso.map_adj_iff (f.trans g.symm)).2 hA₁
    have hB₂ := (SimpleGraph.Iso.map_adj_iff (f.trans g.symm)).2 hA₂
    have hl₆ : ∀ e, tieNet.src e ≠ 6 := by decide +kernel
    have hl₈ : ∀ e, tieNet.src e ≠ 8 := by decide +kernel
    have hs₄ : ∀ e, tieStarNet.src e ≠ 4 := by decide +kernel
    have hs₈ : ∀ e, tieStarNet.src e ≠ 8 := by decide +kernel
    rw [hrow 6 4 (ofBits [1, 0, 0, 0, 0]) (by decide +kernel) hl₆ (by decide +kernel) hs₄ (by decide +kernel)] at hB₁
    rw [hrow 8 8 (ofBits [0, 0, 1, 0, 0]) (by decide +kernel) hl₈ (by decide +kernel) hs₈ (by decide +kernel)] at hB₂
    have h₁ := tieStarNet_cover.neighbor_of_leaf (e := 4) hs₄ (by decide +kernel) hB₁
    have h₂ := tieStarNet_cover.neighbor_of_leaf (e := 8) hs₈ (by decide +kernel) hB₂
    have h₃ := tieStarNet_cover.eq_of_toBlobNode_eq (h₁.symm.trans h₂)
    exact absurd h₃.1 (by decide +kernel)

end Tie

end Gusfield2007
