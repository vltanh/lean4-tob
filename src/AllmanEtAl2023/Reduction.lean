module

public import Phylogenetics.Network.DeletedArcs
public import Phylogenetics.Tree.Metric
public import AllmanEtAl2023.CycleLemma

/-!
# Allman, Baños, Mitchell, Rhodes 2023, Theorem 1(b): the graph side

The source proves part (b) of its Theorem 1 at boundary parameters: an inheritance probability `0`
deletes a hybrid arc. This file is the part of that proof about graphs. It reads the network off a set
`D` of deleted arcs (`Phylogenetics/Network/DeletedArcs.lean`). Its result, `exists_reduction`: a 4-set
`q` that is not treelike has a set `D` and a reticulation
`h` with exactly two parents `k₁`, `k₂` off `D` and exactly one taxon `a` of `q` below it, such that
deleting either parent gives a cut split, and the two splits differ.

The steps, in the source's order (the PMC text, lines 145-149):

1. `IsTreelikeOff`, which is `IsTreelike` at `D = ∅` (`isTreelikeOff_empty_iff`).
2. If no vertex ancestral to `q` off `D` is a reticulation, a tree on four taxa has a `2|2` arc
   (`isTreelikeOff_or_starOff`).
3. Otherwise take a lowest reticulation `h`, with parents `k₁`, `k₂`; while deleting one leaves `q`
   non-treelike, delete it (the source's "set `γᵢ = 0`"; `exists_reduction_aux`, by induction).
4. If both deletions give cut splits, "the subnetwork below `v` must be a tree"
   (`hasUniqueParentsBelow_of_lowest`), and it "can only have one leaf" (`card_taxaBelowOff_le_one`).
5. The two splits differ, by the source's contradiction with the subnetwork `N₃` on the taxa other than
   `a`, its blob determined by them, and the cut edge of `N₃` at that blob towards `b`
   (`IsLowPair.exists_splitOffAt`, in the paper's order). Here the language changes from domination to blobs of a set of arcs
   (`src/AllmanEtAl2023/SubgraphBlobs.lean`), and back (`exists_onlyCrosses_of_splitOffAt`,
   `splitOffAt_of_onlyCrosses`).

The non-binary variant that ECToBlob's adaptation needs is `exists_reduction_of_blobDegree`: only the
two uses of the degrees differ, and they are the hypotheses of `exists_reduction_aux`.

## The paper's proof and this form

`exists_reduction_aux` is the form for the later papers, on one network and a set `D` of deleted arcs, with the non-binary variant that ECToBlob's adaptation needs. The paper's statement (b), on networks of their own, with the 2-blob step and Lemma 1, is `AllmanEtAl2023.Theorem1b`, which uses the lemmas of this file on the tree below a lowest reticulation and the contradiction.

**Gap of the paper.** It says, with no reason, that the cut edge `e` of `N₃` is a cut edge of `N₁` and `N₂`. Its reason is `IsLowPair.ends_mem_far`: a cut edge `f` of `Nᵢ` with split `ab|cd` lies in `N₃` between `ℬ` and `b`, so the attachments of `a` lie beyond `f`, hence beyond `e`. With this,
`IsLowPair.exists_splitOffAt` follows the paper's order.
-/

@[expose] public noncomputable section

open Phylogenetics.DirectedMultigraph Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} {N : RootedNetwork V E X} {D : Set E}

/-! ### The subnetworks in Allman et al.'s contradiction -/

/-- The arcs off `D` above a taxon of `Y`, with their orientations forgotten: the subnetwork of the
network off `D` on the taxa `Y`, before vertices of degree two are suppressed. The source's `N₁`, `N₂`
and `N₃` (the PMC text, lines 148-149) are `arcsAbove N (insert k₂ D) q`,
`arcsAbove N (insert k₁ D) q` and `arcsAbove N D (q.erase a)`. -/
def arcsAbove (N : RootedNetwork V E X) (D : Set E) (Y : Set X) : Set E :=
  {f | f ∉ D ∧ ∃ x ∈ Y, N.ReachesOff D (N.graph.target f) (N.leaf x)}

/-- Off the empty deletion, `arcsAbove` is the library's `ancestralArcs`. -/
theorem arcsAbove_empty (Y : Set X) : arcsAbove N ∅ Y = N.ancestralArcs Y := by
  ext f
  simp only [arcsAbove, RootedNetwork.ancestralArcs, RootedNetwork.ancestralVertices, Set.mem_ofPred_eq, Set.mem_empty_iff_false, not_false_eq_true, true_and, reachesOff_empty_iff]

/-- A path off `D` that ends above a taxon of `Y` is a walk in `arcsAbove`. -/
theorem walks_arcsAbove_of_reachesOff {Y : Set X} {u w : V} (h : N.ReachesOff D u w)
    (hw : ∃ x ∈ Y, N.ReachesOff D w (N.leaf x)) : N.graph.Walks (arcsAbove N D Y) u w := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨f, hf, rfl, rfl⟩ := hbc
    obtain ⟨x, hx, hr⟩ := hw
    exact (ih ⟨x, hx, ReachesOff.head_arc hf hr⟩).tail ⟨f, ⟨hf, x, hx, hr⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- A path off `D` avoiding `e` that ends above a taxon of `Y` is a walk in `arcsAbove` avoiding `e`. -/
theorem walks_sdiff_of_reachesOff_insert {Y : Set X} {e : E} {u w : V}
    (h : N.ReachesOff (insert e D) u w) (hw : ∃ x ∈ Y, N.ReachesOff D w (N.leaf x)) :
    N.graph.Walks (arcsAbove N D Y \ {e}) u w := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨f, hf, rfl, rfl⟩ := hbc
    have hfe : f ≠ e := fun h => hf (Or.inl h)
    have hfD : f ∉ D := fun h => hf (Or.inr h)
    obtain ⟨x, hx, hr⟩ := hw
    exact (ih ⟨x, hx, ReachesOff.head_arc hfD hr⟩).tail
      ⟨f, ⟨⟨hfD, x, hx, hr⟩, hfe⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- The subnetwork `arcsAbove` is connected, through the root. -/
theorem walks_arcsAbove (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {Y : Set X} {u w : V}
    (hu : ∃ x ∈ Y, N.ReachesOff D u (N.leaf x)) (hw : ∃ x ∈ Y, N.ReachesOff D w (N.leaf x)) :
    N.graph.Walks (arcsAbove N D Y) u w :=
  (N.graph.walks_symm (walks_arcsAbove_of_reachesOff (hD.root_reachesOff hN u) hu)).trans
    (walks_arcsAbove_of_reachesOff (hD.root_reachesOff hN w) hw)

/-- **A blob of `N₃` determined by three taxa** (`a:claim:three-taxa`; the source's "a blob `ℬ` determined by the 3 taxa
`b, c, d`", the PMC text, line 149; the source states its existence after
Definition 8): by `exists_median` and `determines_of_median`, since no cut edge has two of three taxa
on each side. -/
theorem exists_determines_arcsAbove [DecidableEq X] (hN : N.IsPhylogenetic) (hD : N.IsDeletion D)
    {S : Finset X} (h3 : S.card = 3) :
    ∃ v, (∀ x ∈ S, N.graph.Walks (arcsAbove N D (S : Set X)) v (N.leaf x)) ∧
      Determines N.graph (arcsAbove N D (S : Set X)) v N.leaf S := by
  have hSU : ∀ x ∈ S, ∃ y ∈ (S : Set X), N.ReachesOff D (N.leaf x) (N.leaf y) := fun x hx =>
    ⟨x, Finset.mem_coe.mpr hx, .refl⟩
  have harc : ∀ x ∈ S, ∀ g, N.graph.target g = N.leaf x → g ∈ arcsAbove N D (S : Set X) := fun x hx g ht => by
    have : Finite E := hN.finite_arcs
    obtain ⟨f, hf, hfx⟩ := hD.parent (N.leaf x) fun h => by
      have := hN.leaf_indegree x
      rw [h, hN.root_indegree] at this
      omega
    obtain ⟨g', hg'⟩ := (N.graph.indegree_eq_one_iff _).mp (hN.leaf_indegree x)
    have hgD : g ∉ D := by
      rwa [show g = f from ((hg' g).mp ht).trans ((hg' f).mp hfx).symm]
    exact ⟨hgD, x, Finset.mem_coe.mpr hx, ht ▸ .refl⟩
  obtain ⟨v, hv, hdet⟩ := exists_determines_of_connected (F := arcsAbove N D (S : Set X))
    (U := {u | ∃ y ∈ (S : Set X), N.ReachesOff D u (N.leaf y)}) hN
    (fun _ hx _ hy => walks_arcsAbove hN hD hx hy)
    (fun f ⟨hf, x, hx, hr⟩ => ⟨⟨x, hx, ReachesOff.head_arc hf hr⟩, ⟨x, hx, hr⟩⟩) hSU harc h3.ge
    fun _ _ _ h₁ h₂ => not_twoIn_compl_of_card_three h3 h₁ h₂
  exact ⟨v, fun x hx => walks_arcsAbove hN hD hv (hSU x hx), hdet⟩

/-! ### Cut edges off a deletion: from domination to sides, and back -/

/-- If every taxon of `Y` is dominated by `e` or not below it, off `D`, then `e` is the only arc of
`arcsAbove` crossing the set of vertices all of whose root paths off `D` use `e`. -/
theorem onlyCrosses_domSetOff (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {Y : Set X} {e : E}
    (hY : ∀ y ∈ Y, N.DominatesOff D e y ∨ ¬ N.IsBelowOff D e y) :
    OnlyCrosses N.graph (arcsAbove N D Y) e {v | ¬ N.ReachesOff (insert e D) N.root v} := by
  have hA := hN.acyclic
  rintro f ⟨hfD, y, hy, hr⟩ (⟨hsf, htf⟩ | ⟨htf, hsf⟩)
  · exfalso
    rcases (hD.root_reachesOff hN (N.graph.source f)).split e with hl | ⟨-, he, hr'⟩
    · exact hsf hl
    · have hbt := hr'.tail_arc hfD
      rcases hY y hy with hdy | hny
      · exact hdy ((not_not.mp htf).trans (ReachesOff.insert_of_target_reaches hA hbt hr))
      · exact hny ⟨he, hbt.trans hr⟩
  · by_contra hfe
    exact htf ((not_not.mp hsf).tail_arc (by simp [hfe, hfD]))

/-- If `e` is the only arc of `arcsAbove` crossing `T`, with its target in `T` and its source not, then
it dominates the taxa of `Y` in `T`, and the taxa of `Y` not in `T` are not below it. -/
theorem separatesOff_of_onlyCrosses (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {Y : Set X} {e : E}
    {T : Set V} (he : e ∈ arcsAbove N D Y) (hT : OnlyCrosses N.graph (arcsAbove N D Y) e T)
    (ht : N.graph.target e ∈ T) (hs : N.graph.source e ∉ T) :
    (∀ x ∈ Y, N.leaf x ∈ T → N.DominatesOff D e x) ∧
      ∀ x ∈ Y, N.leaf x ∉ T → ¬ N.IsBelowOff D e x := by
  have hA := hN.acyclic
  obtain ⟨heD, y₀, hy₀, hr₀⟩ := he
  have hroot : N.root ∉ T := fun h => hs ((hT.mem_iff_of_walks_diff
    (walks_sdiff_of_reachesOff_insert ((hD.root_reachesOff hN _).insert_of_not_reaches fun h' =>
      not_reaches_target_source hA e h'.reaches) ⟨y₀, hy₀, ReachesOff.head_arc heD hr₀⟩)).mp h)
  refine ⟨fun x hx hxT hav => hroot ((hT.mem_iff_of_walks_diff
    (walks_sdiff_of_reachesOff_insert hav ⟨x, hx, .refl⟩)).mpr hxT), fun x hx hxT hb => hxT ?_⟩
  exact (hT.mem_iff_of_walks_diff (walks_sdiff_of_reachesOff_insert
    (ReachesOff.insert_of_target_reaches hA .refl hb.2) ⟨x, hx, .refl⟩)).mp ht

section Quartet

variable [DecidableEq X]

/-- A split off `D` is a cut edge of `arcsAbove`, with the cherry `B` on one side. -/
theorem exists_onlyCrosses_of_splitOffAt [Fintype X] (hN : N.IsPhylogenetic) (hD : N.IsDeletion D)
    {e : E} {s : QuartetTree X} (h : N.SplitOffAt D e s) {B : Finset X} (hB : B ∈ s.val) :
    ∃ T : Set V, OnlyCrosses N.graph (arcsAbove N D (s.taxa : Set X)) e T ∧
      ∀ x ∈ s.taxa, N.leaf x ∈ T ↔ x ∈ B := by
  obtain ⟨P, hP, hdom, hnb⟩ := h
  have hO := onlyCrosses_domSetOff hN hD (Y := (s.taxa : Set X)) (e := e) fun y hy => by
    by_cases hyP : y ∈ P
    · exact Or.inl (hdom y (Finset.mem_coe.mpr hyP))
    · exact Or.inr (hnb y (by simpa [hyP] using hy))
  have hmem : ∀ x ∈ s.taxa, N.leaf x ∈ {v | ¬ N.ReachesOff (insert e D) N.root v} ↔ x ∈ P := by
    intro x hx
    refine ⟨fun hn => ?_, fun hxP => hdom x (Finset.mem_coe.mpr hxP)⟩
    by_contra hxP
    rcases (hD.root_reachesOff hN (N.leaf x)).split e with hl | ⟨-, he, hr⟩
    · exact hn hl
    · exact hnb x (by simpa [hxP] using hx) ⟨he, hr⟩
  have hB' := hB
  rw [s.eq_pair_of_mem hP] at hB'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hB'
  rcases hB' with rfl | rfl
  · exact ⟨_, hO, hmem⟩
  · refine ⟨_, hO.compl, fun x hx => ?_⟩
    rw [Set.mem_compl_iff, hmem x hx]
    simp [hx]

/-- A cut edge of `arcsAbove` that has the cherry `B` on one side and the other cherry on the other is a
split off `D`. -/
theorem splitOffAt_of_onlyCrosses [Fintype X] (hN : N.IsPhylogenetic) (hD : N.IsDeletion D)
    {s : QuartetTree X} {B : Finset X} (hB : B ∈ s.val) {e : E} {T : Set V}
    (hT : OnlyCrosses N.graph (arcsAbove N D (s.taxa : Set X)) e T)
    (hleaf : ∀ x ∈ s.taxa, N.leaf x ∈ T ↔ x ∈ B) : N.SplitOffAt D e s := by
  have hsB : ∀ x ∈ B, x ∈ s.taxa := fun x hx => s.subset_taxa hB hx
  obtain ⟨x₀, hx₀⟩ : B.Nonempty := Finset.card_pos.mp (by rw [s.card_of_mem hB]; norm_num)
  obtain ⟨y₀, hy₀⟩ : (s.taxa \ B).Nonempty :=
    Finset.card_pos.mp (by rw [s.card_of_mem (s.sdiff_mem hB)]; norm_num)
  obtain ⟨hy₀t, hy₀B⟩ := Finset.mem_sdiff.mp hy₀
  have hanc : ∀ x ∈ s.taxa, ∃ y ∈ (s.taxa : Set X), N.ReachesOff D (N.leaf x) (N.leaf y) :=
    fun x hx => ⟨x, Finset.mem_coe.mpr hx, .refl⟩
  obtain ⟨he, p, r, hl, hp, hr⟩ := exists_links_of_walks hT
    (fun h => hy₀B ((hleaf y₀ hy₀t).mp h))
    (walks_arcsAbove hN hD (hanc y₀ hy₀t) (hanc x₀ (hsB x₀ hx₀))) ((hleaf x₀ (hsB x₀ hx₀)).mpr hx₀)
  rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hd, hn⟩ := separatesOff_of_onlyCrosses hN hD he hT hr hp
    refine ⟨B, hB, fun x hx => hd x (Finset.mem_coe.mpr (hsB x (Finset.mem_coe.mp hx)))
      ((hleaf x (hsB x (Finset.mem_coe.mp hx))).mpr (Finset.mem_coe.mp hx)), fun x hx => ?_⟩
    obtain ⟨hxt, hxB⟩ := Finset.mem_sdiff.mp (Finset.mem_coe.mp hx)
    exact hn x (Finset.mem_coe.mpr hxt) fun h => hxB ((hleaf x hxt).mp h)
  · obtain ⟨hd, hn⟩ := separatesOff_of_onlyCrosses hN hD he hT.compl hp (not_not.mpr hr)
    refine ⟨s.taxa \ B, s.sdiff_mem hB, fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨hxt, hxB⟩ := Finset.mem_sdiff.mp (Finset.mem_coe.mp hx)
      exact hd x (Finset.mem_coe.mpr hxt) fun h => hxB ((hleaf x hxt).mp h)
    · rw [Finset.sdiff_sdiff_eq_self (s.subset_taxa hB)] at hx
      have hxB := Finset.mem_coe.mp hx
      exact hn x (Finset.mem_coe.mpr (hsB x hxB)) (not_not.mpr ((hleaf x (hsB x hxB)).mpr hxB))

/-! ### Allman et al.'s contradiction -/

/-- The situation of the source's last step: two parents `k₁ ≠ k₂` off the deletion `D` of a vertex
below which, of the taxa `Y`, at most `a` lies. -/
structure IsLowPair (N : RootedNetwork V E X) (D : Set E) (k₁ k₂ : E) (a : X) (Y : Set X) : Prop where
  phylogenetic : N.IsPhylogenetic
  deletion : N.IsDeletion D
  ne : k₁ ≠ k₂
  target_eq : N.graph.target k₁ = N.graph.target k₂
  notMem₁ : k₁ ∉ D
  notMem₂ : k₂ ∉ D
  not_reaches : ∀ x ∈ Y, x ≠ a → ¬ N.ReachesOff D (N.graph.target k₁) (N.leaf x)

namespace IsLowPair

variable {k₁ k₂ e e' f : E} {a b c d : X} {Y : Set X} {q : Finset X} {v : V} {T : Set V}

omit [DecidableEq X] in
theorem symm (hL : IsLowPair N D k₁ k₂ a Y) : IsLowPair N D k₂ k₁ a Y where
  phylogenetic := hL.phylogenetic
  deletion := hL.deletion
  ne := hL.ne.symm
  target_eq := hL.target_eq.symm
  notMem₁ := hL.notMem₂
  notMem₂ := hL.notMem₁
  not_reaches x hx hxa := hL.target_eq ▸ hL.not_reaches x hx hxa

/-- "`N₃` is a subnetwork of both `N₁` and `N₂`" (the PMC text, line 149): a path to
a taxon other than `a` does not pass the reticulation. -/
theorem arcsAbove_erase_subset (hL : IsLowPair N D k₁ k₂ a (q : Set X)) :
    arcsAbove N D (q.erase a : Finset X) ⊆ arcsAbove N (insert k₁ D) (q : Set X) := by
  rintro f ⟨hfD, x, hx, hr⟩
  obtain ⟨hxa, hxq⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hx)
  have hb := (isBelowOff_insert_iff (hL.not_reaches x (Finset.mem_coe.mpr hxq) hxa)).mpr ⟨hfD, hr⟩
  exact ⟨hb.1, x, Finset.mem_coe.mpr hxq, hb.2⟩

omit [DecidableEq X] in
/-- Every arc of the network off `D` is in one of the two deleted networks, since a path uses at most
one of `k₁`, `k₂`. -/
theorem arcsAbove_subset_union (hL : IsLowPair N D k₁ k₂ a Y) :
    arcsAbove N D Y ⊆ arcsAbove N (insert k₁ D) Y ∪ arcsAbove N (insert k₂ D) Y := by
  have hA := hL.phylogenetic.acyclic
  rintro f ⟨hfD, x, hx, hr⟩
  by_cases h₁ : f = k₁
  · subst h₁
    exact Or.inr ⟨by simp [hL.ne, hfD], x, hx,
      ReachesOff.insert_of_target_reaches hA (hL.target_eq ▸ .refl) hr⟩
  by_cases h₂ : f = k₂
  · subst h₂
    exact Or.inl ⟨by simp [hL.ne.symm, hfD], x, hx,
      ReachesOff.insert_of_target_reaches hA (hL.target_eq ▸ .refl) hr⟩
  rcases reachesOff_insert_or hA hL.ne hL.target_eq hr with h | h
  · exact Or.inl ⟨by simp [h₁, hfD], x, hx, h⟩
  · exact Or.inr ⟨by simp [h₂, hfD], x, hx, h⟩

/-- **The reason that the paper's "Now `e` must be a cut edge in both `N₁` and `N₂`" needs, and does not give.** Let `e'` be a cut edge of the network with `k₁` deleted, with the side `T` containing `a, b` and not `c, d`. Then `e'` lies in `N₃`,
and has the blob `ℬ` on the side of `c, d`: it is between `ℬ` and `b`. An arc `f` above `a` only is joined to `a` off `e'`, so its ends are in `T`. The vertices of `N₃` in `T` are joined to `b` inside `T`, which `e`, having an end in `ℬ`, is not in. So the ends of `f` are beyond `e`. -/
theorem ends_mem_far (hL : IsLowPair N D k₁ k₂ a (q : Set X)) (ha : a ∈ q)
    (hdet : Determines N.graph (arcsAbove N D (q.erase a : Finset X)) v N.leaf (q.erase a))
    (hw : ∀ x ∈ q.erase a, N.graph.Walks (arcsAbove N D (q.erase a : Finset X)) v (N.leaf x))
    (hlead : LeadsTo N.graph (arcsAbove N D (q.erase a : Finset X)) v e (N.leaf b))
    (hb : b ∈ q.erase a) (hc : c ∈ q.erase a) (hd : d ∈ q.erase a) (hcd : c ≠ d)
    (hT : OnlyCrosses N.graph (arcsAbove N (insert k₁ D) (q : Set X)) e' T)
    (haT : N.leaf a ∈ T) (hbT : N.leaf b ∈ T) (hcT : N.leaf c ∉ T) (hdT : N.leaf d ∉ T)
    (hf : f ∈ arcsAbove N (insert k₁ D) (q : Set X))
    (hf₃ : f ∉ arcsAbove N D (q.erase a : Finset X)) :
    N.graph.source f ∈ far N.graph (arcsAbove N D (q.erase a : Finset X)) e v ∧
      N.graph.target f ∈ far N.graph (arcsAbove N D (q.erase a : Finset X)) e v := by
  have hT₃ := hT.mono hL.arcsAbove_erase_subset
  -- `ℬ` is on the side of `c, d`
  have hvT : v ∉ T := fun hv => hcd (hdet.eq_of_mem_side hT₃.compl (not_not.mpr hv) hc hd (hw c hc)
    (hw d hd) hcT hdT)
  -- `e'` is in `N₃`
  have he'₃ := (exists_links_of_walks hT₃ hcT
    ((N.graph.walks_symm (hw c hc)).trans (hw b hb)) hbT).1
  -- the path down to `a` from an arc above `a` only avoids `e'`
  have hdown : ∀ u, (∀ x ∈ q.erase a, ¬ N.ReachesOff D u (N.leaf x)) →
      N.ReachesOff (insert k₁ D) u (N.leaf a) →
      N.graph.Walks (arcsAbove N (insert k₁ D) (q : Set X) \ {e'}) u (N.leaf a) := by
    intro u hu hr
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | @head p r hpr hra ih =>
      obtain ⟨g, hg, rfl, rfl⟩ := hpr
      have hgD : g ∉ D := fun h => hg (Or.inr h)
      have hu' : ∀ x ∈ q.erase a, ¬ N.ReachesOff D (N.graph.target g) (N.leaf x) := fun x hx h =>
        hu x hx (ReachesOff.head_arc hgD h)
      have hne : g ≠ e' := by
        rintro rfl
        obtain ⟨-, x, hx, hrx⟩ := he'₃
        exact hu' x (Finset.mem_coe.mp hx) hrx
      exact Relation.ReflTransGen.head ⟨g, ⟨⟨hg, a, Finset.mem_coe.mpr ha, hra⟩, hne⟩,
        Or.inl ⟨rfl, rfl⟩⟩ (ih hu')
  -- a vertex in `T` joined to `ℬ` off `e` would join `b` to `ℬ` off `e`
  have key : ∀ u, N.graph.Walks (arcsAbove N (insert k₁ D) (q : Set X) \ {e'}) u (N.leaf a) →
      u ∈ far N.graph (arcsAbove N D (q.erase a : Finset X)) e v := fun u hu hwu => by
    have huT : u ∈ T := (hT.mem_iff_of_walks_diff hu).mpr haT
    have hin := walks_insideArcs_of_mem hT₃ hvT (walks_mono Set.sdiff_subset hwu) (hw b hb) huT hbT
    have hsub := (insideArcs_subset_diff_incidentCuts hT₃ hvT).trans
      (Set.sdiff_subset_sdiff_right (Set.singleton_subset_iff.mpr hlead.1))
    exact hlead.2 (Relation.ReflTransGen.trans hwu (walks_mono hsub hin))
  obtain ⟨hfi, x, hxq, hrx⟩ := hf
  have hfD : f ∉ D := fun h => hfi (Or.inr h)
  have hnr : ∀ y ∈ q.erase a, ¬ N.ReachesOff D (N.graph.target f) (N.leaf y) := fun y hy h =>
    hf₃ ⟨hfD, y, Finset.mem_coe.mpr hy, h⟩
  have hxa : x = a := by
    by_contra hne
    exact hnr x (Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hxq⟩) (hrx.mono (Set.subset_insert _ _))
  subst hxa
  have h₁ := hdown _ hnr hrx
  have hfe' : f ≠ e' := fun h => hf₃ (h ▸ he'₃)
  exact ⟨key _ (Relation.ReflTransGen.head ⟨f, ⟨⟨hfi, x, hxq, hrx⟩, hfe'⟩, Or.inl ⟨rfl, rfl⟩⟩ h₁),
    key _ h₁⟩

/-- **"Now `e` must be a cut edge in both `N₁` and `N₂`"** (the PMC text, line 149):
with the notation of `ends_mem_far`, `e` is the only arc of the deleted network crossing the side of
`e` in `N₃` away from `ℬ`. The paper gives no reason: it is `ends_mem_far`. -/
theorem onlyCrosses_far_insert (hL : IsLowPair N D k₁ k₂ a (q : Set X)) (ha : a ∈ q)
    (hdet : Determines N.graph (arcsAbove N D (q.erase a : Finset X)) v N.leaf (q.erase a))
    (hw : ∀ x ∈ q.erase a, N.graph.Walks (arcsAbove N D (q.erase a : Finset X)) v (N.leaf x))
    (hlead : LeadsTo N.graph (arcsAbove N D (q.erase a : Finset X)) v e (N.leaf b))
    (hb : b ∈ q.erase a) (hc : c ∈ q.erase a) (hd : d ∈ q.erase a) (hcd : c ≠ d)
    (hT : OnlyCrosses N.graph (arcsAbove N (insert k₁ D) (q : Set X)) e' T)
    (haT : N.leaf a ∈ T) (hbT : N.leaf b ∈ T) (hcT : N.leaf c ∉ T) (hdT : N.leaf d ∉ T) :
    OnlyCrosses N.graph (arcsAbove N (insert k₁ D) (q : Set X)) e
      (far N.graph (arcsAbove N D (q.erase a : Finset X)) e v) := by
  intro f hf hcr
  by_cases hf₃ : f ∈ arcsAbove N D (q.erase a : Finset X)
  · exact onlyCrosses_far f hf₃ hcr
  · obtain ⟨h₁, h₂⟩ := hL.ends_mem_far ha hdet hw hlead hb hc hd hcd hT haT hbT hcT hdT hf hf₃
    rcases hcr with ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h₂ h
    · exact absurd h₁ h

/-- **"Thus every edge in `𝒩⁺` which is incident to `N₃` and ancestral to only the taxon `a` must be attached to `N₃` in the `b`-component of `N₃ \ {e}`"** (the PMC text, line 149). Since `e` is a cut edge of the deleted network, with `a` on the side
away from `ℬ`, and an arc above `a` only is joined to `a` off `e`, which is in `N₃`. -/
theorem attached_far (hL : IsLowPair N D k₁ k₂ a (q : Set X)) (ha : a ∈ q) (he : e ∈ arcsAbove N D (q.erase a : Finset X)) {F : Set V}
    (hO : OnlyCrosses N.graph (arcsAbove N (insert k₁ D) (q : Set X)) e F) (haF : N.leaf a ∈ F)
    (hf : f ∈ arcsAbove N (insert k₁ D) (q : Set X)) (hf₃ : f ∉ arcsAbove N D (q.erase a : Finset X)) :
    N.graph.source f ∈ F ∧ N.graph.target f ∈ F := by
  -- the path down to `a` from an arc above `a` only avoids `e`
  have hdown : ∀ u, (∀ x ∈ q.erase a, ¬ N.ReachesOff D u (N.leaf x)) → N.ReachesOff (insert k₁ D) u (N.leaf a) →
      N.graph.Walks (arcsAbove N (insert k₁ D) (q : Set X) \ {e}) u (N.leaf a) := by
    intro u hu hr
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | @head p r hpr hra ih =>
      obtain ⟨g, hg, rfl, rfl⟩ := hpr
      have hgD : g ∉ D := fun h => hg (Or.inr h)
      have hu' : ∀ x ∈ q.erase a, ¬ N.ReachesOff D (N.graph.target g) (N.leaf x) := fun x hx h => hu x hx (ReachesOff.head_arc hgD h)
      have hne : g ≠ e := by
        rintro rfl
        obtain ⟨-, x, hx, hrx⟩ := he
        exact hu' x (Finset.mem_coe.mp hx) hrx
      exact Relation.ReflTransGen.head ⟨g, ⟨⟨hg, a, Finset.mem_coe.mpr ha, hra⟩, hne⟩, Or.inl ⟨rfl, rfl⟩⟩ (ih hu')
  obtain ⟨hfi, x, hxq, hrx⟩ := hf
  have hfD : f ∉ D := fun h => hfi (Or.inr h)
  have hnr : ∀ y ∈ q.erase a, ¬ N.ReachesOff D (N.graph.target f) (N.leaf y) := fun y hy h => hf₃ ⟨hfD, y, Finset.mem_coe.mpr hy, h⟩
  have hxa : x = a := by
    by_contra hne
    exact hnr x (Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hxq⟩) (hrx.mono (Set.subset_insert _ _))
  subst hxa
  have h₁ := hdown _ hnr hrx
  have hfe : f ≠ e := fun h => hf₃ (h ▸ he)
  exact ⟨(hO.mem_iff_of_walks_diff (Relation.ReflTransGen.head ⟨f, ⟨⟨hfi, x, hxq, hrx⟩, hfe⟩, Or.inl ⟨rfl, rfl⟩⟩ h₁)).mpr haF, (hO.mem_iff_of_walks_diff h₁).mpr haF⟩

variable [Fintype X] {e₁ e₂ : E} {s : QuartetTree X}

/-- **The paper's contradiction** (`a:claim:thm1b-contradiction`; the PMC text, line 149): if the deleted networks
`N₁` and `N₂` have cut edges `e₁`, `e₂` of the same quartet tree `ab|cd`, then the network has one, in the paper's order.

"Consider the subnetwork `N₃` on `b, c, d`" (`arcsAbove N D (s.taxa.erase a)`), a subnetwork of both `N₁` and `N₂` (`arcsAbove_erase_subset`), "which has a blob `ℬ` determined by the 3 taxa `b, c, d`" (`exists_determines_arcsAbove`). "Let `e` denote the cut edge of `N₃` incident to `ℬ` through
which undirected paths to `b` pass" (`exists_leadsTo`). "Now `e` must be a cut edge in both `N₁` and `N₂`, inducing the split `ab|cd` in both" (`onlyCrosses_far_insert`, and `ends_mem_far` for `a`): this sentence has no reason in the paper, and this is the gap; the reason is `ends_mem_far`, from the given cut edges
`e₁`, `e₂`. "Thus every edge in `𝒩⁺` which is incident to `N₃` and ancestral to only the taxon `a` must be attached to `N₃` in the `b`-component" (`attached_far`). "But this implies that `e` is a cut edge of `𝒩⁺` inducing the split `ab|cd`" (the end of this proof). -/
theorem exists_splitOffAt (hL : IsLowPair N D k₁ k₂ a (s.taxa : Set X)) (ha : a ∈ s.taxa)
    (h₁ : N.SplitOffAt (insert k₂ D) e₁ s) (h₂ : N.SplitOffAt (insert k₁ D) e₂ s) :
    ∃ e, N.SplitOffAt D e s := by
  have hN := hL.phylogenetic
  have hD := hL.deletion
  -- the names of the taxa: `B = {a, b}` and `{c, d}`
  obtain ⟨B, hB, haB⟩ : ∃ B ∈ s.val, a ∈ B := by simpa [QuartetTree.taxa, Finset.mem_sup] using ha
  have hsB : ∀ x ∈ B, x ∈ s.taxa := fun x hx => s.subset_taxa hB hx
  obtain ⟨b, hbB, hba⟩ := Finset.exists_mem_ne (by rw [s.card_of_mem hB]; norm_num : 1 < B.card) a
  obtain ⟨c, d, hcd, hQ⟩ := Finset.card_eq_two.mp (s.card_of_mem (s.sdiff_mem hB))
  have hcQ : c ∈ s.taxa \ B := by simp [hQ]
  have hdQ : d ∈ s.taxa \ B := by simp [hQ]
  obtain ⟨hct, hcB⟩ := Finset.mem_sdiff.mp hcQ
  obtain ⟨hdt, hdB⟩ := Finset.mem_sdiff.mp hdQ
  have hmem : ∀ {x}, x ∈ s.taxa → x ∉ B → x ≠ a := fun _ hxB h => hxB (h ▸ haB)
  have hb₃ : b ∈ s.taxa.erase a := Finset.mem_erase.mpr ⟨hba, hsB b hbB⟩
  have hc₃ : c ∈ s.taxa.erase a := Finset.mem_erase.mpr ⟨hmem hct hcB, hct⟩
  have hd₃ : d ∈ s.taxa.erase a := Finset.mem_erase.mpr ⟨hmem hdt hdB, hdt⟩
  have h3 : (s.taxa.erase a).card = 3 := by rw [Finset.card_erase_of_mem ha, s.card_taxa]
  -- the blob `ℬ` of `N₃` determined by `b, c, d`, and the cut edge `e`
  obtain ⟨v, hw, hdet⟩ := exists_determines_arcsAbove hN hD h3
  have hbb : ¬ SameBlobIn N.graph (arcsAbove N D (s.taxa.erase a : Finset X)) v (N.leaf b) := fun h =>
    hdet.ne_of_isPendantIn h3.ge (isPendantIn_leaf hN b _) hw
      ((isPendantIn_leaf hN b _).eq_of_sameBlobIn h)
  obtain ⟨e, hlead⟩ := (exists_leadsTo (hw b hb₃)).resolve_left hbb
  -- `e` is a cut edge of both `N₁` and `N₂`
  obtain ⟨T₁, hT₁, hl₁⟩ := exists_onlyCrosses_of_splitOffAt hN
    (hD.insert hN hL.ne.symm hL.target_eq.symm hL.notMem₁) h₁ hB
  obtain ⟨T₂, hT₂, hl₂⟩ := exists_onlyCrosses_of_splitOffAt hN
    (hD.insert hN hL.ne hL.target_eq hL.notMem₂) h₂ hB
  have hsides : ∀ {T : Set V}, (∀ x ∈ s.taxa, N.leaf x ∈ T ↔ x ∈ B) →
      N.leaf a ∈ T ∧ N.leaf b ∈ T ∧ N.leaf c ∉ T ∧ N.leaf d ∉ T := fun hl =>
    ⟨(hl a ha).mpr haB, (hl b (hsB b hbB)).mpr hbB, fun h => hcB ((hl c hct).mp h),
      fun h => hdB ((hl d hdt).mp h)⟩
  obtain ⟨ha₁, hb₁, hc₁, hd₁⟩ := hsides hl₁
  obtain ⟨ha₂, hb₂, hc₂, hd₂⟩ := hsides hl₂
  -- "Now `e` must be a cut edge in both `N₁` and `N₂`, inducing the split `ab|cd` in both"
  have hO₁ := hL.symm.onlyCrosses_far_insert ha hdet hw hlead hb₃ hc₃ hd₃ hcd hT₁ ha₁ hb₁ hc₁ hd₁
  have hO₂ := hL.onlyCrosses_far_insert ha hdet hw hlead hb₃ hc₃ hd₃ hcd hT₂ ha₂ hb₂ hc₂ hd₂
  have haF : N.leaf a ∈ far N.graph (arcsAbove N D (s.taxa.erase a : Finset X)) e v := by
    -- the parent arc of `a` is above `a` only
    obtain ⟨f, hf, hfx⟩ := hD.parent (N.leaf a) fun h => by
      have := hN.leaf_indegree a
      rw [h, hN.root_indegree] at this
      omega
    have hfF : f ∈ arcsAbove N D (s.taxa : Set X) := ⟨hf, a, Finset.mem_coe.mpr ha, hfx ▸ .refl⟩
    have hf₃ : f ∉ arcsAbove N D (s.taxa.erase a : Finset X) := by
      rintro ⟨-, y, hy, hr⟩
      rw [hfx] at hr
      have hyx := eq_of_leaf_reachesOff_leaf hN hr
      exact (Finset.mem_erase.mp (Finset.mem_coe.mp hy)).1 hyx
    rcases hL.arcsAbove_subset_union hfF with h | h
    · exact hfx ▸ (hL.ends_mem_far ha hdet hw hlead hb₃ hc₃ hd₃ hcd hT₂ ha₂ hb₂ hc₂ hd₂ h hf₃).2
    · exact hfx ▸ (hL.symm.ends_mem_far ha hdet hw hlead hb₃ hc₃ hd₃ hcd hT₁ ha₁ hb₁ hc₁ hd₁ h hf₃).2
  -- "Thus every edge in `𝒩⁺` which is incident to `N₃` and ancestral to only the taxon `a` must be attached to `N₃` in the `b`-component"
  have hend₁ := fun {f} => hL.symm.attached_far (f := f) ha hlead.1.1.1 hO₁ haF
  have hend₂ := fun {f} => hL.attached_far (f := f) ha hlead.1.1.1 hO₂ haF
  -- "But this implies that `e` is a cut edge of `𝒩⁺`"
  have hO : OnlyCrosses N.graph (arcsAbove N D (s.taxa : Set X)) e
      (far N.graph (arcsAbove N D (s.taxa.erase a : Finset X)) e v) := by
    intro f hf hcr
    by_cases hf₃ : f ∈ arcsAbove N D (s.taxa.erase a : Finset X)
    · exact onlyCrosses_far f hf₃ hcr
    · have hends : N.graph.source f ∈ far N.graph (arcsAbove N D (s.taxa.erase a : Finset X)) e v ∧
          N.graph.target f ∈ far N.graph (arcsAbove N D (s.taxa.erase a : Finset X)) e v := by
        rcases hL.arcsAbove_subset_union hf with h | h
        · exact hend₂ h hf₃
        · exact hend₁ h hf₃
      rcases hcr with ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd hends.2 h
      · exact absurd hends.1 h
  -- "inducing the split `ab|cd`"
  refine ⟨e, splitOffAt_of_onlyCrosses hN hD hB hO fun x hx => ⟨fun hxR => ?_, fun hxB => ?_⟩⟩
  · by_contra hxB
    have hx₃ : x ∈ s.taxa.erase a := Finset.mem_erase.mpr ⟨hmem hx hxB, hx⟩
    have := hdet.eq_of_mem_side onlyCrosses_far not_mem_far_self hb₃ hx₃ (hw b hb₃) (hw x hx₃)
      hlead.2 hxR
    exact hxB (this ▸ hbB)
  · by_cases hxa : x = a
    · rw [hxa]
      exact haF
    · have hxb : x = b := by
        obtain ⟨u, w, -, hBeq⟩ := Finset.card_eq_two.mp (s.card_of_mem hB)
        simp only [hBeq, Finset.mem_insert, Finset.mem_singleton] at haB hbB hxB
        grind
      exact hxb ▸ hlead.2

end IsLowPair

end Quartet

/-! ### Below a lowest reticulation the network is a tree -/

/-- The taxa of `q` below the vertex `w`, off `D`. -/
def taxaBelowOff (N : RootedNetwork V E X) (D : Set E) (q : Finset X) (w : V) : Finset X :=
  q.filter fun x => N.ReachesOff D w (N.leaf x)

theorem mem_taxaBelowOff {q : Finset X} {w : V} {x : X} :
    x ∈ taxaBelowOff N D q w ↔ x ∈ q ∧ N.ReachesOff D w (N.leaf x) := by
  simp [taxaBelowOff]

/-- Below `v`, off `D`, every vertex ancestral to `q` has one parent. -/
def HasUniqueParentsBelow (N : RootedNetwork V E X) (D : Set E) (q : Finset X) (v : V) : Prop :=
  ∀ w, N.ReachesOff D v w → w ≠ v → (taxaBelowOff N D q w).Nonempty →
    ∀ f g, f ∉ D → g ∉ D → N.graph.target f = w → N.graph.target g = w → f = g

/-- Off `D`, an arc into the tree below `v` dominates the taxa of `q` below it: going up from such a
taxon, each vertex has only one parent. -/
theorem dominatesOff_of_uniqueParents (hN : N.IsPhylogenetic) {q : Finset X} {v : V}
    (hT : HasUniqueParentsBelow N D q v) {e : E} (he : e ∉ D)
    (hv : N.ReachesOff D v (N.graph.source e)) {x : X} (hx : x ∈ q)
    (hr : N.ReachesOff D (N.graph.target e) (N.leaf x)) : N.DominatesOff D e x := by
  have hne : ∀ w, N.ReachesOff D (N.graph.target e) w → w ≠ v := by
    rintro w hw rfl
    exact not_reaches_target_source hN.acyclic e (ReachesOff.reaches (hw.trans hv))
  have hv' : N.ReachesOff D v (N.graph.target e) := hv.tail_arc he
  have hnon : ∀ w, N.ReachesOff D w (N.leaf x) → (taxaBelowOff N D q w).Nonempty := fun w hw =>
    ⟨x, mem_taxaBelowOff.mpr ⟨hx, hw⟩⟩
  have hnotin : ∀ {g : E}, g ∉ insert e D → g ≠ e ∧ g ∉ D := fun hg =>
    ⟨fun h => hg (Set.mem_insert_iff.mpr (Or.inl h)), fun h => hg (Set.mem_insert_of_mem _ h)⟩
  have key : ∀ w, N.ReachesOff D (N.graph.target e) w → N.ReachesOff D w (N.leaf x) →
      ¬ N.ReachesOff (insert e D) N.root w := by
    intro w hw
    induction hw with
    | refl =>
      intro hl hav
      obtain ⟨f, hf, hft, -⟩ := hav.exists_last (target_ne_root_of_isPhylogenetic hN e).symm
      obtain ⟨hfe, hfD⟩ := hnotin hf
      exact hfe (hT _ hv' (hne _ .refl) (hnon _ hl) f e hfD he hft rfl)
    | @tail b c hb hbc ih =>
      obtain ⟨f, hf, rfl, rfl⟩ := hbc
      intro hl hav
      obtain ⟨g, hg, hgt, hp⟩ := hav.exists_last (target_ne_root_of_isPhylogenetic hN f).symm
      obtain ⟨-, hgD⟩ := hnotin hg
      have hbf : N.ReachesOff D (N.graph.target e) (N.graph.target f) := ReachesOff.tail_arc hb hf
      have hgf : g = f := hT _ (hv'.trans hbf) (hne _ hbf) (hnon _ hl) g f hgD hf hgt rfl
      subst hgf
      exact ih (ReachesOff.head_arc hf hl) hp
  exact key _ hr .refl

/-- `f` is an arm at the vertex `w` towards the taxon `x` of `q`, off `D`: it leaves `w` with exactly
`x` below it, or it enters `w` with exactly the other taxa of `q` below it. -/
def ArmOff (N : RootedNetwork V E X) (D : Set E) (q : Finset X) (w : V) (x : X) (f : E) : Prop :=
  f ∉ D ∧ ((N.graph.source f = w ∧ ∀ y ∈ q, N.IsBelowOff D f y ↔ y = x) ∨
    (N.graph.target f = w ∧ ∀ y ∈ q, N.IsBelowOff D f y ↔ y ≠ x))

/-- Off `D`, the vertex `w` has an arm towards each taxon of `q`: a multifurcation of degree at least
four. -/
def StarOff (N : RootedNetwork V E X) (D : Set E) (q : Finset X) (w : V) : Prop :=
  ∀ x ∈ q, ∃ f, ArmOff N D q w x f

variable [Fintype X] [DecidableEq X]

/-- **A tree with two taxa has a `2|2` arc** (what the source's "since `𝒩−` has no 3-blobs, this tree can only
have one leaf", the PMC text, line 148, uses). Take two or more taxa of `q` below `v`, with one
parent at each vertex ancestral to `q` below `v`. The lowest vertex `w` with at least two taxa of `q` below it has
at most one below each child. If it has exactly two, the arc entering `w` separates `2|2`, so `q` is treelike off
`D`. Otherwise `w` is a multifurcation, which does not arise in a binary network. -/
theorem isTreelikeOff_or_starOff (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {q : Finset X}
    (hq : q.card = 4) {v : V} (hT : HasUniqueParentsBelow N D q v)
    (h2 : 2 ≤ (taxaBelowOff N D q v).card)
    (hv : (taxaBelowOff N D q v).card = 2 →
      ∀ f g, N.graph.source f = v → N.graph.source g = v → f = g) :
    N.IsTreelikeOff D q ∨ ∃ w, StarOff N D q w := by
  obtain ⟨w, ⟨hvw, hw2⟩, hlow⟩ :=
    exists_lowest hN (S := {w | N.ReachesOff D v w ∧ 2 ≤ (taxaBelowOff N D q w).card})
      ⟨v, .refl, h2⟩
  have hchild : ∀ f, f ∉ D → N.graph.source f = w → (taxaBelowOff N D q (N.graph.target f)).card ≤ 1 := by
    intro f hf hs
    by_contra hc
    have hvf : N.ReachesOff D v (N.graph.target f) := (hs ▸ hvw : N.ReachesOff D v _).tail_arc hf
    have hstep : N.graph.Reaches w (N.graph.target f) := .single ⟨f, hs, rfl⟩
    have heq := hlow _ ⟨hvf, by omega⟩ hstep
    exact hN.acyclic w (.single ⟨f, hs, heq⟩)
  have hfirst : ∀ x ∈ taxaBelowOff N D q w,
      ∃ f, f ∉ D ∧ N.graph.source f = w ∧ N.ReachesOff D (N.graph.target f) (N.leaf x) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne (by omega : 1 < (taxaBelowOff N D q w).card) x
    refine (mem_taxaBelowOff.mp hx).2.exists_first ?_
    intro hwx
    have hy' := (mem_taxaBelowOff.mp hy).2
    rw [hwx] at hy'
    exact hyx (eq_of_leaf_reachesOff_leaf hN hy')
  rcases (by omega : (taxaBelowOff N D q w).card = 2 ∨ 3 ≤ (taxaBelowOff N D q w).card) with h | h
  · left
    have hwv : v ≠ w := by
      rintro rfl
      obtain ⟨x, y, hxy, hxy'⟩ := Finset.card_eq_two.mp h
      obtain ⟨f, hf, hfs, hfx⟩ := hfirst x (by simp [hxy'])
      obtain ⟨g, hg, hgs, hgy⟩ := hfirst y (by simp [hxy'])
      have hfg := hv h f g hfs hgs
      subst hfg
      have hle := hchild f hf hfs
      have hxm : x ∈ taxaBelowOff N D q (N.graph.target f) :=
        mem_taxaBelowOff.mpr ⟨(mem_taxaBelowOff.mp (by simp [hxy'] : x ∈ taxaBelowOff N D q v)).1, hfx⟩
      have hym : y ∈ taxaBelowOff N D q (N.graph.target f) :=
        mem_taxaBelowOff.mpr ⟨(mem_taxaBelowOff.mp (by simp [hxy'] : y ∈ taxaBelowOff N D q v)).1, hgy⟩
      exact hxy (Finset.card_le_one.mp hle x hxm y hym)
    obtain ⟨e, he, het, hes⟩ := hvw.exists_last hwv
    obtain ⟨s, hst, hsv⟩ := TreeMetric.exists_quartetTree_of_subset (B := taxaBelowOff N D q w) hq
      (Finset.filter_subset _ _) h
    refine ⟨s, mem_treesOn.mpr hst, e, taxaBelowOff N D q w, by simp [hsv], ?_, ?_⟩
    · intro x hx
      have hx' := mem_taxaBelowOff.mp (Finset.mem_coe.mp hx)
      exact dominatesOff_of_uniqueParents hN hT he hes hx'.1 (het ▸ hx'.2)
    · intro x hx hb
      rw [hst, Finset.mem_coe, Finset.mem_sdiff] at hx
      exact hx.2 (mem_taxaBelowOff.mpr ⟨hx.1, het ▸ hb.2⟩)
  · right
    refine ⟨w, fun x hx => ?_⟩
    by_cases hxw : x ∈ taxaBelowOff N D q w
    · obtain ⟨f, hf, hfs, hfx⟩ := hfirst x hxw
      refine ⟨f, hf, Or.inl ⟨hfs, fun y hy => ⟨?_, ?_⟩⟩⟩
      · rintro ⟨-, hr⟩
        exact Finset.card_le_one.mp (hchild f hf hfs) y (mem_taxaBelowOff.mpr ⟨hy, hr⟩) x
          (mem_taxaBelowOff.mpr ⟨hx, hfx⟩)
      · rintro rfl
        exact ⟨hf, hfx⟩
    · have hwr : w ≠ N.root := by
        rintro rfl
        exact hxw (mem_taxaBelowOff.mpr ⟨hx, hD.root_reachesOff hN _⟩)
      obtain ⟨e, he, het⟩ := hD.parent w hwr
      have hsub : taxaBelowOff N D q w ⊆ q.erase x := fun y hy =>
        Finset.mem_erase.mpr ⟨fun hyx => hxw (hyx ▸ hy), (mem_taxaBelowOff.mp hy).1⟩
      have heq : taxaBelowOff N D q w = q.erase x :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_erase_of_mem hx]; omega)
      refine ⟨e, he, Or.inr ⟨het, fun y hy => ⟨?_, ?_⟩⟩⟩
      · rintro ⟨-, hr⟩ rfl
        exact hxw (mem_taxaBelowOff.mpr ⟨hx, het ▸ hr⟩)
      · intro hyx
        have hm : y ∈ taxaBelowOff N D q w := by
          rw [heq]
          exact Finset.mem_erase.mpr ⟨hyx, hy⟩
        exact ⟨he, het ▸ (mem_taxaBelowOff.mp hm).2⟩

/-- Domination language for `IsTreelike`, `hasCutSplitOn_iff_separates`: step 1 of the proof. -/
theorem isTreelikeOff_empty_iff (hN : N.IsPhylogenetic) {q : Finset X} :
    N.IsTreelikeOff ∅ q ↔ IsTreelike N q :=
  exists_congr fun s => and_congr_right fun _ => (inducedCutSplit_iff_exists_splitOffAt hN s).symm

/-! ### The reduction -/

omit [Fintype X] [DecidableEq X] in
/-- **"The subnetwork below `v` must be a tree"** (the PMC text, line 148): if `h` is a lowest
reticulation ancestral to `q` off `D`, each vertex ancestral to `q` below it has one parent off `D`. The source
takes `v` lowest in a total order extending the order of the network. This takes it minimal in that order, which is
all that is used. -/
theorem hasUniqueParentsBelow_of_lowest {q : Finset X} {h : V}
    (hlow : ∀ w, (taxaBelowOff N D q w).Nonempty → (∃ k₁ k₂, k₁ ≠ k₂ ∧ k₁ ∉ D ∧ k₂ ∉ D ∧
      N.graph.target k₁ = w ∧ N.graph.target k₂ = w) → N.graph.Reaches h w → w = h) :
    HasUniqueParentsBelow N D q h := by
  intro w hw hwh hnon f g hf hg hfw hgw
  by_contra hfg
  exact hwh (hlow w hnon ⟨f, g, hfg, hf, hg, hfw, hgw⟩ hw.reaches)

/-- **"This tree can only have one leaf, and hence there is only a single edge below `v`"**
(the PMC text, line 148): below a reticulation `h` with one child and a tree below it, at most
one taxon of `q` lies, if `q` is not treelike off `D` (the source's "`𝒩−` has no 3-blobs") and no multifurcation arises
off `D`.

The paper's proof of this sentence, by the 3-blob at the parent of a cherry, is `exists_child_eq_leaf`. In the form on a set `D`, for the later papers, the deleted arcs stay in the network, vertices of degree two are not suppressed, and taxa outside `q` may be below `h`, so the single edge is stated as one taxon of `q` below `h`. -/
theorem card_taxaBelowOff_le_one (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {q : Finset X}
    (hq : q.card = 4) {h : V} (hT : HasUniqueParentsBelow N D q h) (hout : N.graph.outdegree h = 1)
    (hnt : ¬ N.IsTreelikeOff D q) (hStar : ∀ w, ¬ StarOff N D q w) :
    (taxaBelowOff N D q h).card ≤ 1 := by
  by_contra hc
  obtain ⟨e, he⟩ := (N.graph.outdegree_eq_one_iff h).mp hout
  rcases isTreelikeOff_or_starOff hN hD hq hT (by omega) (fun _ f g hf hg => by
    rw [(he f).mp hf, (he g).mp hg]) with hl | ⟨w, hw⟩
  · exact hnt hl
  · exact hStar w hw

/-- **The reduction**, under the two uses of the degrees: a reticulation has two parents and one
child (`hRet`), and no multifurcation arises off a deletion (`hStar`). By induction on `D`, as in the
source: take a lowest reticulation ancestral to `q`, and delete a parent while `q` stays non-treelike. The
recursion runs on the set `D`, which grows at each deletion, rather than on the number of reticulations; the
deletions are the source's.

This is the form for the later papers, on non-binary networks too; the paper's proof is `exists_isNonCut_of_not_isTreelike`. Two things differ from it. The paper removes the 2-blobs first, by setting lengths to `0` (line 146); here a reticulation of a 2-blob goes through the same test as any other, since domination sees through 2-blobs: a parent is deleted when the 4-set stays non-treelike without it. And the paper's Lemma 1 is not used: "the only non-leaf blob in `𝒩−` is a 4-blob" (line 146) and "`𝒩−` has no 3-blobs" (line 148) are the hypothesis that `q` is not treelike off `D`, with `isTreelikeOff_or_starOff`; that the two deleted networks "each have exactly two 3-blobs" (line 148) is `IsTreelikeOff` for each; and the blob of `N₃` (line 149) is `exists_determines_arcsAbove`. -/
theorem exists_reduction_aux (hN : N.IsPhylogenetic)
    (hRet : ∀ v, 2 ≤ N.graph.indegree v → N.graph.indegree v = 2 ∧ N.graph.outdegree v = 1)
    {q : Finset X} (hq : q.card = 4)
    (hStar : ∀ (D : Set E) (w : V), N.IsDeletion D → ¬ StarOff N D q w) (D : Set E) :
    N.IsDeletion D → ¬ N.IsTreelikeOff D q →
    ∃ (D : Set E) (k₁ k₂ : E) (a : X) (s₁ s₂ : QuartetTree X) (e₁ e₂ : E),
      N.IsDeletion D ∧ k₁ ≠ k₂ ∧ N.graph.target k₁ = N.graph.target k₂ ∧ k₁ ∉ D ∧ k₂ ∉ D ∧
      (∀ f, N.graph.target f = N.graph.target k₁ → f ∉ D → f = k₁ ∨ f = k₂) ∧
      a ∈ q ∧ N.ReachesOff D (N.graph.target k₁) (N.leaf a) ∧
      (∀ x ∈ q, x ≠ a → ¬ N.ReachesOff D (N.graph.target k₁) (N.leaf x)) ∧
      s₁ ∈ treesOn q ∧ s₂ ∈ treesOn q ∧ s₁ ≠ s₂ ∧
      N.SplitOffAt (insert k₂ D) e₁ s₁ ∧ N.SplitOffAt (insert k₁ D) e₂ s₂ := by
  have : Finite E := hN.finite_arcs
  induction D using WellFoundedGT.induction with
  | _ D ih =>
    intro hD hnt
    have hroot : taxaBelowOff N D q N.root = q :=
      Finset.filter_true_of_mem fun x _ => hD.root_reachesOff hN (N.leaf x)
    by_cases hex : ∃ w, (taxaBelowOff N D q w).Nonempty ∧ ∃ k₁ k₂, k₁ ≠ k₂ ∧ k₁ ∉ D ∧ k₂ ∉ D ∧
        N.graph.target k₁ = w ∧ N.graph.target k₂ = w
    · -- Step 3: a lowest reticulation.
      obtain ⟨h, ⟨hhT, k₁, k₂, hk, hk₁, hk₂, ht₁, ht₂⟩, hlow⟩ := exists_lowest hN (S := {w |
        (taxaBelowOff N D q w).Nonempty ∧ ∃ k₁ k₂, k₁ ≠ k₂ ∧ k₁ ∉ D ∧ k₂ ∉ D ∧
          N.graph.target k₁ = w ∧ N.graph.target k₂ = w}) hex
      have ht : N.graph.target k₁ = N.graph.target k₂ := ht₁.trans ht₂.symm
      by_cases h₁ : N.IsTreelikeOff (insert k₁ D) q
      · by_cases h₂ : N.IsTreelikeOff (insert k₂ D) q
        · -- Step 4: exactly one taxon of `q` is below `h`.
          have hdeg := hRet h (by
            have hfin : {e | N.graph.target e = h}.Finite := Set.toFinite _
            exact (Set.one_lt_ncard_iff hfin).mpr ⟨k₁, k₂, ht₁, ht₂, hk⟩)
          have hcard : (taxaBelowOff N D q h).card ≤ 1 :=
            card_taxaBelowOff_le_one hN hD hq
              (hasUniqueParentsBelow_of_lowest fun w hnon hw hr => hlow w ⟨hnon, hw⟩ hr) hdeg.2 hnt
              fun w hw => hStar D w hD hw
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp
            (le_antisymm hcard (Finset.card_pos.mpr hhT))
          have hamem : a ∈ taxaBelowOff N D q h := by simp [ha]
          have hnot : ∀ x ∈ q, x ≠ a → ¬ N.ReachesOff D h (N.leaf x) := fun x hx hxa hr => by
            have hm : x ∈ taxaBelowOff N D q h := mem_taxaBelowOff.mpr ⟨hx, hr⟩
            rw [ha, Finset.mem_singleton] at hm
            exact hxa hm
          obtain ⟨s₂, hs₂, e₂, hs₂'⟩ := h₁
          obtain ⟨s₁, hs₁, e₁, hs₁'⟩ := h₂
          refine ⟨D, k₁, k₂, a, s₁, s₂, e₁, e₂, hD, hk, ht, hk₁, hk₂, ?_,
            (mem_taxaBelowOff.mp hamem).1, ht₁ ▸ (mem_taxaBelowOff.mp hamem).2,
            fun x hx hxa => ht₁ ▸ hnot x hx hxa, hs₁, hs₂, ?_, hs₁', hs₂'⟩
          · -- `h` has only the parents `k₁`, `k₂`.
            intro f hf _
            by_contra hne
            push Not at hne
            have hgt : 2 < N.graph.indegree h :=
              (Set.two_lt_ncard_iff (Set.toFinite _)).mpr
                ⟨k₁, k₂, f, ht₁, ht₂, hf.trans ht₁, hk, hne.1.symm, hne.2.symm⟩
            omega
          · -- Step 5: the two splits differ, "for the sake of contradiction".
            rintro rfl
            have hta : s₁.taxa = q := mem_treesOn.mp hs₁
            have hL : IsLowPair N D k₁ k₂ a (s₁.taxa : Set X) :=
              { phylogenetic := hN
                deletion := hD
                ne := hk
                target_eq := ht
                notMem₁ := hk₁
                notMem₂ := hk₂
                not_reaches := fun x hx hxa => ht₁ ▸ hnot x (hta ▸ Finset.mem_coe.mp hx) hxa }
            obtain ⟨e, he⟩ := hL.exists_splitOffAt (hta ▸ (mem_taxaBelowOff.mp hamem).1) hs₁' hs₂'
            exact hnt ⟨s₁, hs₁, e, he⟩
        · exact ih (insert k₂ D) (Set.ssubset_insert hk₂)
            (hD.insert hN hk.symm ht.symm hk₁) h₂
      · exact ih (insert k₁ D) (Set.ssubset_insert hk₁) (hD.insert hN hk ht hk₂) h₁
    · -- Step 2: no reticulation, so the ancestors of `q` form a tree.
      exfalso
      have hT : HasUniqueParentsBelow N D q N.root := by
        intro w _ _ hnon f g hf hg hfw hgw
        by_contra hfg
        exact hex ⟨w, hnon, f, g, hfg, hf, hg, hfw, hgw⟩
      rcases isTreelikeOff_or_starOff hN hD hq hT (by rw [hroot]; omega)
        (by rw [hroot]; omega) with hl | ⟨w, hw⟩
      · exact hnt hl
      · exact hStar D w hD hw

omit [Fintype X] in
/-- A vertex with an arm towards each of four taxa has degree at least four. -/
theorem StarOff.four_le_degree (hN : N.IsPhylogenetic) {q : Finset X} (hq : q.card = 4) {w : V}
    (h : StarOff N D q w) : 4 ≤ N.graph.indegree w + N.graph.outdegree w := by
  have : Finite E := hN.finite_arcs
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (by omega : 0 < q.card)
  have : Nonempty E := (h x₀ hx₀).elim fun f _ => ⟨f⟩
  choose! f hf using h
  have hinj : Set.InjOn f q := by
    intro x hx y hy hxy
    by_contra hne
    have hx : x ∈ q := Finset.mem_coe.mp hx
    have hy : y ∈ q := Finset.mem_coe.mp hy
    obtain ⟨u, hu, huxy⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {x, y}) (t := q) (by
        rw [hq]
        exact lt_of_le_of_lt Finset.card_le_two (by norm_num))
    have hux : u ≠ x := fun h => huxy (by simp [h])
    have huy : u ≠ y := fun h => huxy (by simp [h])
    obtain ⟨-, hx'⟩ := hf x hx
    obtain ⟨-, hy'⟩ := hf y hy
    rw [hxy] at hx'
    rcases hx' with ⟨-, hx'⟩ | ⟨-, hx'⟩ <;> rcases hy' with ⟨-, hy'⟩ | ⟨-, hy'⟩
    · exact hne ((hy' x hx).mp ((hx' x hx).mpr rfl))
    · exact hux ((hx' u hu).mp ((hy' u hu).mpr huy))
    · exact huy ((hy' u hu).mp ((hx' u hu).mpr hux))
    · exact (hx' x hx).mp ((hy' x hx).mpr hne) rfl
  have hcard : (f '' (q : Set X)).ncard = 4 := by
    rw [hinj.ncard_image, Set.ncard_coe_finset, hq]
  have hsub : f '' (q : Set X) ⊆ {e | N.graph.target e = w} ∪ {e | N.graph.source e = w} := by
    rintro _ ⟨x, hx, rfl⟩
    rcases (hf x hx).2 with ⟨hs, -⟩ | ⟨ht, -⟩
    · exact Or.inr hs
    · exact Or.inl ht
  calc 4 = (f '' (q : Set X)).ncard := hcard.symm
    _ ≤ ({e | N.graph.target e = w} ∪ {e | N.graph.source e = w}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ _ := Set.ncard_union_le _ _

/-- **The graph side of part (b) of Theorem 1 of Allman et al. 2023**
(the PMC text, lines 145-149). For a binary network and a 4-set `q` that is not
treelike, there are a deletion `D` of hybrid arcs and a reticulation with exactly two parents `k₁`, `k₂`
off `D` and exactly one taxon `a` of `q` below it, such that deleting `k₂` gives a cut arc `e₁` of a
quartet tree `s₁` on `q`, deleting `k₁` gives a cut arc `e₂` of a quartet tree `s₂` on `q`, and
`s₁ ≠ s₂`. See `exists_reduction_aux` for the proof and how it differs from the paper's. -/
theorem exists_reduction (hN : N.IsPhylogenetic) (hBin : N.IsBinary) {q : Finset X} (hq : q.card = 4)
    (hnt : ¬ IsTreelike N q) :
    ∃ (D : Set E) (k₁ k₂ : E) (a : X) (s₁ s₂ : QuartetTree X) (e₁ e₂ : E),
      N.IsDeletion D ∧ k₁ ≠ k₂ ∧ N.graph.target k₁ = N.graph.target k₂ ∧ k₁ ∉ D ∧ k₂ ∉ D ∧
      (∀ f, N.graph.target f = N.graph.target k₁ → f ∉ D → f = k₁ ∨ f = k₂) ∧
      a ∈ q ∧ N.ReachesOff D (N.graph.target k₁) (N.leaf a) ∧
      (∀ x ∈ q, x ≠ a → ¬ N.ReachesOff D (N.graph.target k₁) (N.leaf x)) ∧
      s₁ ∈ treesOn q ∧ s₂ ∈ treesOn q ∧ s₁ ≠ s₂ ∧
      N.SplitOffAt (insert k₂ D) e₁ s₁ ∧ N.SplitOffAt (insert k₁ D) e₂ s₂ :=
  exists_reduction_aux hN
    (fun v h2 => indegree_eq_two_of_degree_le_three hN h2 (degree_le_three_of_isBinary hN hBin v)) hq
    (fun _ w _ hw => by
      have h₁ := hw.four_le_degree hN hq
      have h₂ := degree_le_three_of_isBinary hN hBin w
      omega)
    ∅ (isDeletion_empty hN) fun h => hnt ((isTreelikeOff_empty_iff hN).mp h)

/-! ### The non-binary variant -/

omit [Fintype X] [DecidableEq X] in
/-- Under the degree condition of ECToBlob's Proposition 5.1, a reticulation has degree at most
three, since it lies in a non-trivial blob. -/
theorem degree_le_three_of_two_le_indegree (hN : N.IsPhylogenetic)
    (hdeg : ∀ v w : V, v ≠ w → N.graph.blobSetoid v w →
      N.graph.indegree v + N.graph.outdegree v ≤ 3) {v : V} (h2 : 2 ≤ N.graph.indegree v) :
    N.graph.indegree v + N.graph.outdegree v ≤ 3 := by
  have : Finite E := hN.finite_arcs
  obtain ⟨f, g, hf, hg, hne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2
  have hf' : N.graph.target f = v := hf
  have hg' : N.graph.target g = v := hg
  refine hdeg v (N.graph.source f) ?_ (.single ⟨f, not_isBridge_of_two_parents hN hne
    (hf'.trans hg'.symm), Or.inr ⟨rfl, hf'⟩⟩)
  rintro rfl
  exact hN.acyclic _ (.single ⟨f, rfl, hf'⟩)

omit [Fintype X] in
/-- Under the degree condition of ECToBlob's Proposition 5.1, a multifurcation off a deletion is a
trivial 4-blob of the network itself: its vertex has degree at least four, so it lies in no non-trivial
blob, so its arcs are bridges, and a bridge has the same taxa on each side as off `D`. -/
theorem hasTrivialFourBlob_of_starOff (hN : N.IsPhylogenetic)
    (hdeg : ∀ v w : V, v ≠ w → N.graph.blobSetoid v w →
      N.graph.indegree v + N.graph.outdegree v ≤ 3) (hD : N.IsDeletion D) {q : Finset X}
    (hq : q.card = 4) {w : V} (hw : StarOff N D q w) : HasTrivialFourBlob N q := by
  have h4 := hw.four_le_degree hN hq
  have hA := hN.acyclic
  refine ⟨w, fun x hx => ?_⟩
  obtain ⟨f, hf, harm⟩ := hw x hx
  have hbr : N.graph.underlying.IsBridge f := by
    by_contra hnb
    rcases harm with ⟨hs, -⟩ | ⟨ht, -⟩
    · have hne : w ≠ N.graph.target f := by
        rintro rfl
        exact hA _ (.single ⟨f, hs, rfl⟩)
      have := hdeg w _ hne (.single ⟨f, hnb, Or.inl ⟨hs, rfl⟩⟩)
      omega
    · have hne : w ≠ N.graph.source f := by
        rintro rfl
        exact hA _ (.single ⟨f, rfl, ht⟩)
      have := hdeg w _ hne (.single ⟨f, hnb, Or.inr ⟨rfl, ht⟩⟩)
      omega
  obtain ⟨S₀, hS₀⟩ := (N.graph.isBridge_iff f).1 hbr
  obtain ⟨S, hS, hwS⟩ : ∃ S : Set V, (∀ g, N.graph.Crosses g S ↔ g = f) ∧ w ∉ S := by
    by_cases hw0 : w ∈ S₀
    · exact ⟨S₀ᶜ, fun g => (N.graph.crosses_compl g S₀).trans (hS₀ g), by simpa using hw0⟩
    · exact ⟨S₀, hS₀, hw0⟩
  have hc := (hS f).mpr rfl
  -- A taxon not below `f` is on the side of the source of `f`, one below it on the side of the target.
  have hrs : N.ReachesOff (insert f D) N.root (N.graph.source f) :=
    (hD.root_reachesOff hN _).insert_of_not_reaches fun h =>
      not_reaches_target_source hA f (ReachesOff.reaches h)
  have hnb : ∀ y, ¬ N.IsBelowOff D f y → (N.leaf y ∈ S ↔ N.graph.source f ∈ S) := by
    intro y hy
    rcases (hD.root_reachesOff hN (N.leaf y)).split f with hl | ⟨-, he, hr⟩
    · exact (mem_iff_mem_of_reachesOff_insert hS hl).symm.trans
        (mem_iff_mem_of_reachesOff_insert hS hrs)
    · exact absurd ⟨he, hr⟩ hy
  have hbl : ∀ y, N.IsBelowOff D f y → (N.leaf y ∈ S ↔ N.graph.target f ∈ S) := fun y hy =>
    (mem_iff_mem_of_reachesOff_insert hS
      (ReachesOff.insert_of_target_reaches hA .refl hy.2)).symm
  rcases harm with ⟨hs, harm⟩ | ⟨ht, harm⟩
  · have htS : N.graph.target f ∈ S := by
      rcases hc with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd (hs ▸ h) hwS
      · exact h
    refine ⟨f, ⟨x, hx, ((harm x hx).mpr rfl).2.reaches⟩, S, fun g _ => hS g, fun y hy => ⟨?_, ?_⟩,
      hwS, Or.inl hs⟩
    · intro hyS
      by_contra hyx
      exact hwS (hs ▸ (hnb y fun h => hyx ((harm y hy).mp h)).mp hyS)
    · rintro rfl
      exact (hbl y ((harm y hy).mpr rfl)).mpr htS
  · have hsS : N.graph.source f ∈ S := by
      rcases hc with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (ht ▸ h) hwS
    obtain ⟨y₀, hy₀, hy₀x⟩ := Finset.exists_mem_ne (by omega : 1 < q.card) x
    refine ⟨f, ⟨y₀, hy₀, ((harm y₀ hy₀).mpr hy₀x).2.reaches⟩, S, fun g _ => hS g,
      fun y hy => ⟨?_, ?_⟩, hwS, Or.inr ht⟩
    · intro hyS
      by_contra hyx
      exact hwS (ht ▸ (hbl y ((harm y hy).mpr hyx)).mp hyS)
    · rintro rfl
      exact (hnb y fun h => (harm y hy).mp h rfl).mpr hsS

omit [Fintype X] in
/-- A cut arc off a deletion can be moved down to a tree arc of the network, with the same split: a
hybrid arc of the network enters a reticulation, whose one child arc dominates the same taxa. -/
theorem exists_isTreeArc_of_splitOffAt (hN : N.IsPhylogenetic) (hD : N.IsDeletion D)
    (hRet : ∀ v, 2 ≤ N.graph.indegree v → N.graph.indegree v = 2 ∧ N.graph.outdegree v = 1)
    {e : E} {s : QuartetTree X} (h : N.SplitOffAt D e s) :
    ∃ e', N.IsTreeArc e' ∧ N.SplitOffAt D e' s := by
  have : Finite E := hN.finite_arcs
  suffices H : ∀ (v : V) (e : E), N.graph.target e = v → N.SplitOffAt D e s →
      ∃ e', N.IsTreeArc e' ∧ N.SplitOffAt D e' s from H _ e rfl h
  intro v
  induction v using (wellFounded_transGen_adj_flip hN).induction with
  | _ v ih =>
    intro e hev hsplit
    by_cases htree : N.IsTreeArc e
    · exact ⟨e, htree, hsplit⟩
    have h2 : 2 ≤ N.graph.indegree (N.graph.target e) := by
      have h1 := (N.graph.one_le_indegree_iff (N.graph.target e)).mpr ⟨e, rfl⟩
      have h3 : N.graph.indegree (N.graph.target e) ≠ 1 := htree
      omega
    obtain ⟨e', he'⟩ := (N.graph.outdegree_eq_one_iff _).mp (hRet _ h2).2
    have hes : N.graph.source e' = N.graph.target e := (he' e').mpr rfl
    have hleaf : ∀ y, N.graph.target e ≠ N.leaf y := fun y hy => by
      have := hN.leaf_indegree y
      rw [← hy] at this
      omega
    obtain ⟨P, hP, hsep⟩ := hsplit
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [s.card_of_mem hP]; norm_num : 0 < P.card)
    have hbx := (hsep.1 x (Finset.mem_coe.mpr hx)).isBelowOff hN hD
    obtain ⟨g, hg, hgs, -⟩ := hbx.2.exists_first (hleaf x)
    have he'D : e' ∉ D := (he' g).mp hgs ▸ hg
    refine ih (N.graph.target e') (hev ▸ .single ⟨e', hes, rfl⟩) e' rfl ⟨P, hP, ?_, ?_⟩
    · intro y hy hav
      rcases hav.split e with hl | ⟨-, -, hr⟩
      · refine hsep.1 y hy (hl.mono ?_)
        exact Set.insert_subset_insert (Set.subset_insert _ _)
      · obtain ⟨g', hg', hg's, -⟩ := hr.exists_first (hleaf y)
        exact hg' (Set.mem_insert_iff.mpr (Or.inl ((he' g').mp hg's)))
    · rintro y hy ⟨-, hr⟩
      exact hsep.2 y hy ⟨hbx.1, hes ▸ ReachesOff.head_arc he'D hr⟩

/-- **The reduction for ECToBlob's adaptation of Theorem 1 of Allman et al. 2023**
(`ECToBlob.adaptedAllmanTheorem1`). For a network whose vertices in non-trivial blobs have degree at
most three (`hdeg`, which is `ECToBlob.BlobDegreeAtMostThree N`) and a 4-set `q` that is neither
treelike nor a trivial 4-blob, the conclusion of `exists_reduction` holds, with cut arcs `e₁`, `e₂` that
are tree arcs of the network, so that their lengths are free positive parameters on every face of
ECToBlob's measure. -/
theorem exists_reduction_of_blobDegree (hN : N.IsPhylogenetic)
    (hdeg : ∀ v w : V, v ≠ w → N.graph.blobSetoid v w →
      N.graph.indegree v + N.graph.outdegree v ≤ 3) {q : Finset X} (hq : q.card = 4)
    (hnt : ¬ IsTreelike N q) (htr : ¬ HasTrivialFourBlob N q) :
    ∃ (D : Set E) (k₁ k₂ : E) (a : X) (s₁ s₂ : QuartetTree X) (e₁ e₂ : E),
      N.IsDeletion D ∧ k₁ ≠ k₂ ∧ N.graph.target k₁ = N.graph.target k₂ ∧ k₁ ∉ D ∧ k₂ ∉ D ∧
      (∀ f, N.graph.target f = N.graph.target k₁ → f ∉ D → f = k₁ ∨ f = k₂) ∧
      a ∈ q ∧ N.ReachesOff D (N.graph.target k₁) (N.leaf a) ∧
      (∀ x ∈ q, x ≠ a → ¬ N.ReachesOff D (N.graph.target k₁) (N.leaf x)) ∧
      s₁ ∈ treesOn q ∧ s₂ ∈ treesOn q ∧ s₁ ≠ s₂ ∧
      N.SplitOffAt (insert k₂ D) e₁ s₁ ∧ N.SplitOffAt (insert k₁ D) e₂ s₂ ∧
      N.IsTreeArc e₁ ∧ N.IsTreeArc e₂ := by
  have hRet : ∀ v, 2 ≤ N.graph.indegree v →
      N.graph.indegree v = 2 ∧ N.graph.outdegree v = 1 := fun v h2 =>
    indegree_eq_two_of_degree_le_three hN h2 (degree_le_three_of_two_le_indegree hN hdeg h2)
  obtain ⟨D, k₁, k₂, a, s₁, s₂, e₁, e₂, hD, hk, ht, hk₁, hk₂, hpar, ha, hra, hnot, hs₁, hs₂, hss,
      hsp₁, hsp₂⟩ := exists_reduction_aux hN hRet hq
    (fun D w hD hw => htr (hasTrivialFourBlob_of_starOff hN hdeg hD hq hw))
    ∅ (isDeletion_empty hN) fun h => hnt ((isTreelikeOff_empty_iff hN).mp h)
  obtain ⟨e₁', he₁', hsp₁'⟩ := exists_isTreeArc_of_splitOffAt hN
    (hD.insert hN hk.symm ht.symm hk₁) hRet hsp₁
  obtain ⟨e₂', he₂', hsp₂'⟩ := exists_isTreeArc_of_splitOffAt hN
    (hD.insert hN hk ht hk₂) hRet hsp₂
  exact ⟨D, k₁, k₂, a, s₁, s₂, e₁', e₂', hD, hk, ht, hk₁, hk₂, hpar, ha, hra, hnot, hs₁, hs₂, hss,
    hsp₁', hsp₂', he₁', he₂'⟩

end AllmanEtAl2023
