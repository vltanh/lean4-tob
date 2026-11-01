module

public import AllmanEtAl2023.FigureCheck

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the examples of Figures 3 and 9

The networks are read from the figures of the paper. The paper's claims about them are in `fig3_*` (`a:claim:fig3`), `fig9L_*` (`a:claim:fig9L`) and `fig9R_*` (`a:claim:fig9R`).

* Figure 3. "A network with a 5-blob determined by the sets `{a, b, c}`, `{a, b, d, f}`, and other sets. The set `{a, b, e, f}`, however, does not determine a blob. Both `{a, b, c, d}` and `{a, b, d, e}` are B-quartets on this network. While `{a, b, c, d}` is also a
  B-quartet on its induced 4-taxon network, `{a, b, d, e}` is a T-quartet on its induced 4-taxon network." With the text: "Both `{a, b, c, d}` and `{b, c, d, e}` are CF-detectable B-quartets. While `{a, b, d, e}` is not a CF-detectable B-quartet, since `CF_abde` is strictly
  `ab|de`-cut, applying Theorem 2 shows that it is a B-quartet": `fig3_cf`.
* Figure 9, left. "While many of its B-quartets are not CF-detectable, each can be inferred from CF-detectable ones by a single application of the B-quartet Inference Rule": `fig9L_single_rule`.
* Figure 9, right. "The B-quartet `{a, b, c, d}` is not CF-detectable, but three applications of the inference rule allow it to be inferred from those that are": `fig9R_three_rules`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph
open scoped Classical

namespace AllmanEtAl2023.Figures

open InPassing FigureCheck

/-- The sets of four taxa that `CF`s detect, in the terms of `TopologyInferred`: "`CF`-detectable". -/
def Detected {V E X : Type*} [DecidableEq X] {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) (Q : Finset X) : Prop :=
  ∃ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), ({a, b, c, d} : Finset X) = Q ∧ InducedHasStarTopology hN a b c d h

/-! ### Figure 3 -/

section Fig3

/-- The sources of the edges of Figure 3. The taxa `a, b, c, d, e, f` are `0, ..., 5`, and the nodes are `h = 6`, `u = 7`, `s = 8`, `t = 9`, `p = 10`, `q = 11`, `r = 12`. The edges are `r → p`, `r → q`, `q → e`, `q → f`, `p → s`, `p → t`, `s → a`,
`s → u`, `u → b`, `u → h`, `t → d`, `t → h`, `h → c`. -/
def src3 : Fin 13 → Fin 13 := ![12, 12, 11, 11, 10, 10, 8, 8, 7, 7, 9, 9, 6]

/-- The targets of the edges of Figure 3. -/
def tgt3 : Fin 13 → Fin 13 := ![10, 11, 4, 5, 8, 9, 0, 7, 1, 6, 3, 6, 2]

/-- The taxa of Figure 3. -/
def leaf3 : Fin 6 → Fin 13 := Fin.castLE (by norm_num)

/-- **The network of Figure 3.** -/
def fig3 : RootedNetwork (Fin 13) (Fin 13) (Fin 6) := finNetwork src3 tgt3 12 leaf3

theorem isBinaryNetwork_fig3 : IsBinaryNetwork fig3 :=
  isBinaryNetwork_finNetwork (by decide) (by decide) (by decide) (Fin.castLE_injective _) (by decide) (by decide) (by decide) (by decide)

/-- The edges of the cycle of Figure 3. -/
def cycle3 : Finset (Fin 13) := {4, 5, 7, 9, 11}

/-- The colours: the nodes of the blob have one colour, and `e`, `f` are together. -/
def col3 : Fin 13 → Fin 13 := ![0, 1, 2, 3, 4, 4, 6, 6, 6, 6, 6, 4, 4]

/-- "A 5-blob". -/
theorem fig3_blobDegree : blobDegree fig3 (blobOf fig3.graph 10) = 5 := by
  rw [fig3, blobDegree_finNetwork]
  decide +kernel

/-- "Determined by the sets `{a, b, c}`, `{a, b, d, f}`". -/
theorem fig3_determined : IsDeterminedBy fig3.graph fig3.leaf (blobOf fig3.graph 10) {0, 1, 2} ∧ IsDeterminedBy fig3.graph fig3.leaf (blobOf fig3.graph 10) {0, 1, 3, 5} :=
  ⟨isDeterminedBy_of_cert (C := cycle3) (col := col3) (by decide) (by decide +kernel), isDeterminedBy_of_cert (C := cycle3) (col := col3) (by decide) (by decide +kernel)⟩

/-- "The set `{a, b, e, f}`, however, does not determine a blob": the edge `r → p` has `a, b` on one side, and `e, f` on the other. -/
theorem fig3_not_determined (b : fig3.graph.BlobVertex) : ¬ IsDeterminedBy fig3.graph fig3.leaf b {0, 1, 4, 5} := by
  induction b using Quotient.inductionOn with
  | h v =>
    intro hd
    have hdet := (isDeterminedBy_blobOf_iff.mp hd).2
    have hconn := fig3.graph_connected isBinaryNetwork_fig3.isPhylogenetic
    refine Determines.no_split (T := (({10, 8, 9, 7, 6, 0, 1, 2, 3} : Finset (Fin 13)) : Set (Fin 13))) (e := (0 : Fin 13)) hdet (by decide) (by decide) (fun s _ => hconn _ _) (fun f _ hc => ?_) ?_ ?_ ?_ ?_
    · have hall : ∀ f : Fin 13, ((src3 f ∈ ({10, 8, 9, 7, 6, 0, 1, 2, 3} : Finset (Fin 13)) ∧ tgt3 f ∉ ({10, 8, 9, 7, 6, 0, 1, 2, 3} : Finset (Fin 13))) ∨ (tgt3 f ∈ ({10, 8, 9, 7, 6, 0, 1, 2, 3} : Finset (Fin 13)) ∧ src3 f ∉ ({10, 8, 9, 7, 6, 0, 1, 2, 3} : Finset (Fin 13)))) → f = 0 := by decide
      exact hall f (by simpa [DirectedMultigraph.Crosses, fig3, finNetwork] using hc)
    · change (leaf3 0) ∈ _
      simp [leaf3]
    · change (leaf3 1) ∈ _
      simp [leaf3]
    · change (leaf3 4) ∉ _
      simp [leaf3]
    · change (leaf3 5) ∉ _
      simp [leaf3]

/-- "Both `{a, b, c, d}` and `{a, b, d, e}` are B-quartets on this network." -/
theorem fig3_isBlobQuartet : IsBlobQuartet fig3 {0, 1, 2, 3} ∧ IsBlobQuartet fig3 {0, 1, 3, 4} :=
  ⟨⟨by decide, _, isDeterminedBy_of_cert (C := cycle3) (col := col3) (v := 10) (by decide) (by decide +kernel)⟩, ⟨by decide, _, isDeterminedBy_of_cert (C := cycle3) (col := col3) (v := 10) (by decide) (by decide +kernel)⟩⟩

/-- "`{a, b, c, d}` is also a B-quartet on its induced 4-taxon network": `CF`-detectable, as is `{b, c, d, e}`. -/
theorem fig3_star : InducedHasStarTopology isBinaryNetwork_fig3 0 1 2 3 (by decide) ∧ InducedHasStarTopology isBinaryNetwork_fig3 1 2 3 4 (by decide) :=
  ⟨inducedHasStarTopology_of_cert _ _ (v := 10) (C := cycle3) (col := ![0, 1, 2, 3, 4, 4, 6, 6, 6, 6, 6, 4, 4]) (by decide +kernel) (by decide +kernel),
    inducedHasStarTopology_of_cert _ _ (v := 10) (C := cycle3) (col := ![0, 1, 2, 3, 4, 4, 6, 6, 6, 6, 6, 4, 4]) (by decide +kernel) (by decide +kernel)⟩

/-- "`{a, b, d, e}` is a T-quartet on its induced 4-taxon network", with the topology `ab|de`: the edge `h → c` is gone, and with it the cycle. -/
theorem fig3_tree : InducedHasQuartetTopology isBinaryNetwork_fig3 0 1 3 4 (by decide) :=
  inducedHasQuartetTopology_of_cut _ _ (e := 4) (S := {8, 7, 0, 1}) (by decide +kernel)

theorem fig3_not_detected : ¬ Detected isBinaryNetwork_fig3 {0, 1, 3, 4} := by
  rintro ⟨a, b, c, d, h, he, hs⟩
  have hT := (Bridges.inducedHasStarTopology_iff _ h).mp hs
  rw [he] at hT
  have hq := (Bridges.inducedHasQuartetTopology_iff _ _).mp fig3_tree
  exact hT ⟨quartetTree 0 1 3 4 (by decide), mem_treesOn.2 (quartetTree_taxa _ _ _ _ _), hq⟩

/-- "Applying Theorem 2 shows that it is a B-quartet", on topologies. -/
theorem fig3_inferred : TopologyInferredA isBinaryNetwork_fig3 {0, 1, 3, 4} :=
  .rule 0 1 2 3 4 {0, 1, 3, 4} {0, 1, 3, 4} (by decide) (.detected 0 1 2 3 _ fig3_star.1) (.detected 1 2 3 4 _ fig3_star.2) (by decide)
    ⟨0, 1, 3, 4, by decide, rfl, fig3_tree, separated_quartetTree _⟩ (by decide)

/-- **"Both `{a, b, c, d}` and `{b, c, d, e}` are CF-detectable B-quartets. While `{a, b, d, e}` is not a CF-detectable B-quartet, since `CF_abde` is strictly `ab|de`-cut, applying Theorem 2 shows that it is a B-quartet"** (`a:claim:fig3`, after Theorem 2), for generic parameters. -/
theorem fig3_cf : ForGenericParams fig3 fun θ =>
    ReadsUnresolved (nmscCF fig3 θ 0) {0, 1, 2, 3} ∧ ReadsUnresolved (nmscCF fig3 θ 0) {1, 2, 3, 4} ∧ ¬ ReadsUnresolved (nmscCF fig3 θ 0) {0, 1, 3, 4} ∧
      IsStrictlyCutAt (nmscCF fig3 θ 0) (quartetTree 0 1 3 4 (by decide)) ∧ CFInferredA (nmscCF fig3 θ 0) {0, 1, 3, 4} := by
  refine (corollary1 isBinaryNetwork_fig3).mono ?_
  rintro θ ⟨hθ, hnot⟩
  refine ⟨hθ, fun h₁ => hnot ?_⟩
  have hd : ∀ {Q : Finset (Fin 6)}, Detected isBinaryNetwork_fig3 Q → ReadsUnresolved (nmscCF fig3 θ 0) Q := by
    rintro Q ⟨a, b, c, d, h, rfl, hs⟩
    exact ⟨a, b, c, d, h, rfl, (readTopology_eq_star_iff _ h (h₁ a b c d h)).mpr hs⟩
  refine ⟨hd ⟨0, 1, 2, 3, _, rfl, fig3_star.1⟩, hd ⟨1, 2, 3, 4, _, rfl, fig3_star.2⟩, ?_, (isStrictlyCutAt_iff_inducedHasQuartetTopology _ h₁ _).mpr fig3_tree, (cfInferredA_iff_topologyInferredA _ h₁ _).mpr fig3_inferred⟩
  rintro ⟨a, b, c, d, h, he, hr⟩
  exact fig3_not_detected ⟨a, b, c, d, h, he, (readTopology_eq_star_iff _ h (h₁ a b c d h)).mp hr⟩

end Fig3

/-! ### Figure 9, left -/

section Fig9L

/-- The sources of the edges of Figure 9, left. The taxa, in the order along the path that remains when the hybrid node is gone, are `c, b, a, f, e, d = 0, ..., 5`, and `α = 6`. The nodes are `h = 7`, `y₂ = 8`, `y₁ = 9`, `x₂ = 10`, `x₄ = 11`, `x₃ = 12`,
`x₁ = 13`, and the root `14`. The edges are `r → x₁`, `r → f`, `x₁ → x₂`, `x₁ → x₃`, `x₃ → e`, `x₃ → x₄`, `x₄ → d`, `x₄ → h`, `x₂ → a`, `x₂ → y₁`, `y₁ → b`, `y₁ → y₂`, `y₂ → c`, `y₂ → h`, `h → α`. -/
def src9L : Fin 15 → Fin 15 := ![14, 14, 13, 13, 12, 12, 11, 11, 10, 10, 9, 9, 8, 8, 7]

/-- The targets of the edges of Figure 9, left. -/
def tgt9L : Fin 15 → Fin 15 := ![13, 3, 10, 12, 4, 11, 5, 7, 2, 9, 1, 8, 0, 7, 6]

/-- The taxa of Figure 9, left. -/
def leaf9L : Fin 7 → Fin 15 := Fin.castLE (by norm_num)

/-- **The network of Figure 9, left.** -/
def fig9L : RootedNetwork (Fin 15) (Fin 15) (Fin 7) := finNetwork src9L tgt9L 14 leaf9L

theorem isBinaryNetwork_fig9L : IsBinaryNetwork fig9L :=
  isBinaryNetwork_finNetwork (by decide) (by decide) (by decide) (Fin.castLE_injective _) (by decide) (by decide) (by decide) (by decide)

/-- The edges of the 7-cycle. -/
def cycle9L : Finset (Fin 15) := {2, 3, 5, 7, 9, 11, 13}

/-- The colours: the nodes of the cycle have one colour, and the root is with `f`. -/
def col9L : Fin 15 → Fin 15 := ![0, 1, 2, 3, 4, 5, 6, 7, 7, 7, 7, 7, 7, 7, 3]

theorem cert9L : Cert src9L tgt9L leaf9L Finset.univ cycle9L 13 col9L Finset.univ := by decide +kernel

/-- "A 7-blob". -/
theorem fig9L_blobDegree : blobDegree fig9L (blobOf fig9L.graph 13) = 7 := by
  rw [fig9L, blobDegree_finNetwork]
  decide +kernel

/-- "A simple cycle structure": every set of four taxa is a B-quartet. -/
theorem fig9L_isBlobQuartet {Q : Finset (Fin 7)} (hQ : Q.card = 4) : IsBlobQuartet fig9L Q :=
  ⟨hQ, _, isDeterminedBy_of_cert (by omega) (cert9L.mono (Finset.subset_univ Q))⟩

/-- A set with `α` is `CF`-detectable: the whole cycle is above `α`. -/
theorem fig9L_star {x y z w : Fin 7} (h : ({x, y, z, w} : Finset (Fin 7)).card = 4) (hα : (6 : Fin 7) ∈ ({x, y, z, w} : Finset (Fin 7))) : InducedHasStarTopology isBinaryNetwork_fig9L x y z w h := by
  have hsub : ({6} : Finset (Fin 7)) ⊆ {x, y, z, w} := Finset.singleton_subset_iff.mpr hα
  refine (Bridges.inducedHasStarTopology_iff isBinaryNetwork_fig9L h).mpr ((Bridges.isBlobQuartetOnInduced_self_iff isBinaryNetwork_fig9L h).mp ?_)
  have hv : (13 : Fin 15) ∈ ancSet src9L tgt9L leaf9L {x, y, z, w} := ancSet_mono hsub (by decide +kernel)
  have hC : cycle9L ⊆ arcsOf src9L tgt9L leaf9L {x, y, z, w} := (show cycle9L ⊆ arcsOf src9L tgt9L leaf9L {6} by decide +kernel).trans (arcsOf_mono hsub)
  exact onInduced_of_cert_univ isBinaryNetwork_fig9L _ (Finset.Subset.refl _) h hv hC (cert9L.mono (Finset.subset_univ _))

/-- The cut edge between the second and third of four taxa along the path. -/
def cut9L (x : Fin 7) : Fin 15 := if x = 1 then 9 else if x = 2 then 2 else 3

/-- The side of `cut9L` with the first two of four taxa. -/
def side9L (x : Fin 7) : Finset (Fin 15) := if x = 1 then {9, 8, 1, 0} else if x = 2 then {10, 9, 8, 2, 1, 0} else {14, 13, 10, 9, 8, 3, 2, 1, 0}

theorem cutCheck9L : ∀ w x y z : Fin 7, w < x → x < y → y < z → z < 6 → CutCheck src9L tgt9L leaf9L {w, x, y, z} {w, x} {y, z} (cut9L x) (side9L x) := by decide +kernel

/-- A set without `α` is a T-quartet on its induced network: the path remains, and the set is split in the middle. -/
theorem fig9L_tree {w x y z : Fin 7} (hwx : w < x) (hxy : x < y) (hyz : y < z) (hz : z < 6) (h : ({w, x, y, z} : Finset (Fin 7)).card = 4) : InducedHasQuartetTopology isBinaryNetwork_fig9L w x y z h :=
  inducedHasQuartetTopology_of_cut _ h (cutCheck9L w x y z hwx hxy hyz hz)

/-- **One application of the rule, on a set without `α`.** -/
theorem fig9L_rule_data {w x y z : Fin 7} (hwx : w < x) (hxy : x < y) (hyz : y < z) (hz : z < 6) :
    ({w, 6, x, y, z} : Finset (Fin 7)).card = 5 ∧ Detected isBinaryNetwork_fig9L {w, 6, x, y} ∧ Detected isBinaryNetwork_fig9L {6, x, y, z} ∧ InducedTreeSeparates isBinaryNetwork_fig9L {w, x, y, z} w z := by
  have h6 : ∀ {t : Fin 7}, t ≤ z → t ≠ 6 := fun ht he => by
    rw [he] at ht
    exact absurd (ht.trans_lt hz) (lt_irrefl _)
  have hw6 : w ≠ 6 := h6 (hwx.le.trans (hxy.le.trans hyz.le))
  have hx6 : x ≠ 6 := h6 (hxy.le.trans hyz.le)
  have hy6 : y ≠ 6 := h6 hyz.le
  have hz6 : z ≠ 6 := h6 le_rfl
  have hwy := hwx.trans hxy
  have hwz := hwy.trans hyz
  have hxz := hxy.trans hyz
  have h5 : ({w, 6, x, y, z} : Finset (Fin 7)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hw6, hwx.ne, hwy.ne, hwz.ne]), TreeMetric.card_four_of_ne hx6.symm hy6.symm hz6.symm hxy.ne hxz.ne hyz.ne]
  have h₁ := TreeMetric.card_four_of_ne hw6 hwx.ne hwy.ne hx6.symm hy6.symm hxy.ne
  have h₂ := TreeMetric.card_four_of_ne hx6.symm hy6.symm hz6.symm hxy.ne hxz.ne hyz.ne
  have h₃ := TreeMetric.card_four_of_ne hwx.ne hwy.ne hwz.ne hxy.ne hxz.ne hyz.ne
  exact ⟨h5, ⟨w, 6, x, y, h₁, rfl, fig9L_star h₁ (by simp)⟩, ⟨6, x, y, z, h₂, rfl, fig9L_star h₂ (by simp)⟩,
    w, x, y, z, h₃, rfl, fig9L_tree hwx hxy hyz hz h₃, separated_quartetTree h₃⟩

/-- **"While many of its B-quartets are not CF-detectable, each can be inferred from CF-detectable ones by a single application of the B-quartet Inference Rule"** (`a:claim:fig9L`). -/
theorem fig9L_single_rule {Q : Finset (Fin 7)} (hQ : Q.card = 4) :
    IsBlobQuartet fig9L Q ∧ (Detected isBinaryNetwork_fig9L Q ∨ ∃ (a b c d e : Fin 7) (t : Finset (Fin 7)), ({a, b, c, d, e} : Finset (Fin 7)).card = 5 ∧
      Detected isBinaryNetwork_fig9L {a, b, c, d} ∧ Detected isBinaryNetwork_fig9L {b, c, d, e} ∧ t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset (Fin 7))) ∧
      InducedTreeSeparates isBinaryNetwork_fig9L t a e ∧ Q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset (Fin 7)))) := by
  refine ⟨fig9L_isBlobQuartet hQ, ?_⟩
  by_cases hα : (6 : Fin 7) ∈ Q
  · left
    have hc : (Q.erase 6).card = 3 := by rw [Finset.card_erase_of_mem hα, hQ]
    obtain ⟨x, y, z, -, -, -, he⟩ := Finset.card_eq_three.mp hc
    have hQe : ({6, x, y, z} : Finset (Fin 7)) = Q := by rw [← he, Finset.insert_erase hα]
    have h4 : ({6, x, y, z} : Finset (Fin 7)).card = 4 := by rw [hQe, hQ]
    exact ⟨6, x, y, z, h4, hQe, fig9L_star h4 (by simp)⟩
  · right
    let f := Q.orderEmbOfFin hQ
    have hmem : ∀ i, f i ∈ Q := fun i => Finset.orderEmbOfFin_mem Q hQ i
    have hlt : ∀ {i j : Fin 4}, i < j → f i < f j := fun hij => f.strictMono hij
    have hz : f 3 < 6 := by
      have hne : f 3 ≠ 6 := fun he => hα (he ▸ hmem 3)
      exact lt_of_le_of_ne (Fin.le_last _) hne
    have hQe : Q = {f 0, f 1, f 2, f 3} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> exact hmem _
      · rw [hQ]
        exact (TreeMetric.card_four_of_ne (hlt (by decide)).ne (hlt (by decide)).ne (hlt (by decide)).ne (hlt (by decide)).ne (hlt (by decide)).ne (hlt (by decide)).ne).ge
    obtain ⟨h5, h₁, h₂, hsep⟩ := fig9L_rule_data (w := f 0) (x := f 1) (y := f 2) (z := f 3) (hlt (by decide)) (hlt (by decide)) (hlt (by decide)) hz
    refine ⟨f 0, 6, f 1, f 2, f 3, {f 0, f 1, f 2, f 3}, h5, h₁, h₂, by simp, hsep, ?_⟩
    rw [hQe]
    simp

/-- "`{a, b, c, d}` is a B-quartet although `CF_abcd` is `ad|bc`-cut", in the numbering: `a = 2`, `b = 1`, `c = 0`, `d = 5`. -/
theorem fig9L_tree_abcd : InducedHasQuartetTopology isBinaryNetwork_fig9L 2 5 0 1 (by decide) :=
  inducedHasQuartetTopology_of_cut _ _ (e := 9) (S := {14, 13, 12, 11, 10, 5, 4, 3, 2}) (by decide +kernel)

/-- "The taxa `e, f` can be ignored, as passing to the induced network without them leaves `{a, b, c, d}` a B-quartet". -/
theorem fig9L_ignore (hY : (({0, 1, 2, 5, 6} : Finset (Fin 7)) : Set (Fin 7)).Nontrivial) : IsBlobQuartetOnInduced isBinaryNetwork_fig9L (({0, 1, 2, 5, 6} : Finset (Fin 7)) : Set (Fin 7)) hY {2, 1, 0, 5} :=
  onInduced_of_cert_univ isBinaryNetwork_fig9L hY (by decide) (by decide) (by decide +kernel) (by decide +kernel) (cert9L.mono (Finset.subset_univ _))

/-- "The taxon `α` will be used, since its deletion would make `{a, b, c, d}` a T-quartet". -/
theorem fig9L_needs_alpha (hY : (({0, 1, 2, 3, 4, 5} : Finset (Fin 7)) : Set (Fin 7)).Nontrivial) : ¬ IsBlobQuartetOnInduced isBinaryNetwork_fig9L (({0, 1, 2, 3, 4, 5} : Finset (Fin 7)) : Set (Fin 7)) hY {2, 5, 0, 1} :=
  not_onInduced_of_cut _ hY (by decide) (by decide) (e := 9) (S := {14, 13, 12, 11, 10, 5, 4, 3, 2}) (by decide +kernel)

/-- "The `CF`s for `{α, a, c, d}` and `{α, b, c, d}` show those sets are B-quartets, so using that `CF_abcd` is `ad|bc`-cut in inference rule (a) of Theorem 2 gives the desired conclusion." -/
theorem fig9L_inferred : TopologyInferredA isBinaryNetwork_fig9L {2, 5, 0, 1} :=
  .rule 2 6 0 5 1 {2, 5, 0, 1} {2, 5, 0, 1} (by decide) (.detected 2 6 0 5 _ (fig9L_star (by decide) (by decide))) (.detected 6 0 5 1 _ (fig9L_star (by decide) (by decide))) (by decide)
    ⟨2, 5, 0, 1, by decide, rfl, fig9L_tree_abcd, separated_quartetTree _⟩ (by decide)

/-- **The example of Figure 9, left** (`a:claim:fig9L`), for generic parameters: `{a, b, c, d}` is not detected, `CF_abcd` is strictly `ad|bc`-cut, and the rule infers the set from the `CF`s. -/
theorem fig9L_cf : ForGenericParams fig9L fun θ =>
    ¬ ReadsUnresolved (nmscCF fig9L θ 0) {2, 5, 0, 1} ∧ IsStrictlyCutAt (nmscCF fig9L θ 0) (quartetTree 2 5 0 1 (by decide)) ∧ CFInferredA (nmscCF fig9L θ 0) {2, 5, 0, 1} := by
  refine (corollary1 isBinaryNetwork_fig9L).mono ?_
  rintro θ ⟨hθ, hnot⟩
  refine ⟨hθ, fun h₁ => hnot ⟨?_, (isStrictlyCutAt_iff_inducedHasQuartetTopology _ h₁ _).mpr fig9L_tree_abcd, (cfInferredA_iff_topologyInferredA _ h₁ _).mpr fig9L_inferred⟩⟩
  rintro ⟨a, b, c, d, h, he, hr⟩
  have hs := (readTopology_eq_star_iff _ h (h₁ a b c d h)).mp hr
  have hT := (Bridges.inducedHasStarTopology_iff _ h).mp hs
  rw [he] at hT
  exact hT ⟨quartetTree 2 5 0 1 (by decide), mem_treesOn.2 (quartetTree_taxa _ _ _ _ _), (Bridges.inducedHasQuartetTopology_iff _ _).mp fig9L_tree_abcd⟩

end Fig9L

/-! ### Figure 9, right -/

section Fig9R

/-- The sources of the edges of Figure 9, right. The taxa `a, b, c, d, α, β, δ` are `0, ..., 6`, and the nodes are `A = 7`, `B = 8`, `D = 9`, `m₁ = 10`, `m₂ = 11`, `m₃ = 12`, `m₄ = 13`, `n₄ = 14`, `n₃ = 15`, `n₂ = 16`, `n₁ = 17`, and the root `18`. -/
def src9R : Fin 21 → Fin 19 := ![18, 18, 17, 17, 16, 16, 15, 15, 14, 14, 10, 10, 11, 11, 12, 12, 13, 13, 7, 8, 9]

/-- The targets of the edges of Figure 9, right: `r → a`, `r → n₁`, `n₁ → m₁`, `n₁ → n₂`, `n₂ → m₂`, `n₂ → n₃`, `n₃ → m₃`, `n₃ → n₄`, `n₄ → m₄`, `n₄ → d`, `m₁ → b`, `m₁ → A`, `m₂ → A`, `m₂ → B`, `m₃ → B`, `m₃ → D`, `m₄ → c`, `m₄ → D`, `A → α`, `B → β`, `D → δ`. -/
def tgt9R : Fin 21 → Fin 19 := ![0, 17, 10, 16, 11, 15, 12, 14, 13, 3, 1, 7, 7, 8, 8, 9, 2, 9, 4, 5, 6]

/-- The taxa of Figure 9, right. -/
def leaf9R : Fin 7 → Fin 19 := Fin.castLE (by norm_num)

/-- **The network of Figure 9, right.** -/
def fig9R : RootedNetwork (Fin 19) (Fin 21) (Fin 7) := finNetwork src9R tgt9R 18 leaf9R

theorem isBinaryNetwork_fig9R : IsBinaryNetwork fig9R :=
  isBinaryNetwork_finNetwork (by decide) (by decide) (by decide) (Fin.castLE_injective _) (by decide) (by decide) (by decide) (by decide)

/-- The edges of the blob. -/
def blob9R : Finset (Fin 21) := {2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 14, 15, 17}

/-- "A 7-blob". -/
theorem fig9R_blobDegree : blobDegree fig9R (blobOf fig9R.graph 17) = 7 := by
  rw [fig9R, blobDegree_finNetwork]
  decide +kernel

/-- "`{a, b, c, d}` is a B-quartet". -/
theorem fig9R_isBlobQuartet : IsBlobQuartet fig9R {0, 1, 2, 3} :=
  ⟨by decide, _, isDeterminedBy_of_cert (v := 17) (C := blob9R) (col := ![0, 1, 2, 3, 4, 5, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 0]) (by decide) (by decide +kernel)⟩

/-- "`CF_abcd` is `(ab|cd)`-cut". -/
theorem fig9R_tree : InducedHasQuartetTopology isBinaryNetwork_fig9R 0 1 2 3 (by decide) :=
  inducedHasQuartetTopology_of_cut _ _ (e := 3) (S := {18, 17, 10, 0, 1}) (by decide +kernel)

/-- "Deletion of any one of `α, β, δ` would give an induced network with `{a, b, c, d}` a T-quartet." -/
theorem fig9R_deletion (h₁ : (({0, 1, 2, 3, 5, 6} : Finset (Fin 7)) : Set (Fin 7)).Nontrivial) (h₂ : (({0, 1, 2, 3, 4, 6} : Finset (Fin 7)) : Set (Fin 7)).Nontrivial) (h₃ : (({0, 1, 2, 3, 4, 5} : Finset (Fin 7)) : Set (Fin 7)).Nontrivial) :
    ¬ IsBlobQuartetOnInduced isBinaryNetwork_fig9R (({0, 1, 2, 3, 5, 6} : Finset (Fin 7)) : Set (Fin 7)) h₁ {0, 1, 2, 3} ∧
      ¬ IsBlobQuartetOnInduced isBinaryNetwork_fig9R (({0, 1, 2, 3, 4, 6} : Finset (Fin 7)) : Set (Fin 7)) h₂ {0, 1, 2, 3} ∧
        ¬ IsBlobQuartetOnInduced isBinaryNetwork_fig9R (({0, 1, 2, 3, 4, 5} : Finset (Fin 7)) : Set (Fin 7)) h₃ {0, 1, 2, 3} :=
  ⟨not_onInduced_of_cut _ h₁ (by decide) (by decide) (e := 3) (S := {18, 17, 10, 0, 1}) (by decide +kernel),
    not_onInduced_of_cut _ h₂ (by decide) (by decide) (e := 5) (S := {18, 17, 10, 16, 11, 7, 0, 1, 4}) (by decide +kernel),
    not_onInduced_of_cut _ h₃ (by decide) (by decide) (e := 7) (S := {18, 17, 10, 16, 11, 7, 0, 1, 4, 15, 12, 8, 5}) (by decide +kernel)⟩

/-- "`{a, b, c, α}` is a B-quartet using its `CF`". -/
theorem fig9R_star_abcα : InducedHasStarTopology isBinaryNetwork_fig9R 0 1 2 4 (by decide) :=
  inducedHasStarTopology_of_cert _ _ (v := 17) (C := {2, 3, 4, 11, 12}) (col := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 7, 7, 8, 2, 2, 2, 7, 7, 0]) (by decide +kernel) (by decide +kernel)

/-- `{α, b, c, β}` is `CF`-detectable. -/
theorem fig9R_star_αbcβ : InducedHasStarTopology isBinaryNetwork_fig9R 4 1 2 5 (by decide) :=
  inducedHasStarTopology_of_cert _ _ (v := 17) (C := {2, 3, 4, 5, 6, 11, 12, 13, 14}) (col := ![0, 1, 2, 3, 4, 5, 6, 7, 7, 8, 7, 7, 7, 2, 2, 7, 7, 7, 7]) (by decide +kernel) (by decide +kernel)

/-- `{b, c, β, δ}` is `CF`-detectable. -/
theorem fig9R_star_bcβδ : InducedHasStarTopology isBinaryNetwork_fig9R 1 2 5 6 (by decide) :=
  inducedHasStarTopology_of_cert _ _ (v := 16) (C := {4, 5, 6, 7, 8, 13, 14, 15, 17}) (col := ![0, 1, 2, 3, 4, 5, 6, 8, 7, 7, 1, 7, 7, 7, 7, 7, 7, 1, 1]) (by decide +kernel) (by decide +kernel)

/-- `{c, β, δ, d}` is `CF`-detectable. -/
theorem fig9R_star_cβδd : InducedHasStarTopology isBinaryNetwork_fig9R 2 5 6 3 (by decide) :=
  inducedHasStarTopology_of_cert _ _ (v := 16) (C := {4, 5, 6, 7, 8, 13, 14, 15, 17}) (col := ![0, 1, 2, 3, 4, 5, 6, 8, 7, 7, 8, 7, 7, 7, 7, 7, 7, 7, 7]) (by decide +kernel) (by decide +kernel)

/-- "The induced 6-taxon network on `{b, c, d, α, β, δ}`, which has a 6-blob when unrooted": the six taxa determine a blob of the edges above them, and `{α, b, c, d}` is a B-quartet on that network. -/
theorem fig9R_six (hY : (({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) : Set (Fin 7)).Nontrivial) :
    Determines fig9R.graph (fig9R.ancestralArcs (({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) : Set (Fin 7))) 17 fig9R.leaf {1, 2, 3, 4, 5, 6} ∧
      IsBlobQuartetOnInduced isBinaryNetwork_fig9R (({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) : Set (Fin 7)) hY {4, 1, 2, 3} := by
  have hc : Cert src9R tgt9R leaf9R (arcsOf src9R tgt9R leaf9R {1, 2, 3, 4, 5, 6}) blob9R 17 ![0, 1, 2, 3, 4, 5, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] {1, 2, 3, 4, 5, 6} := by decide +kernel
  refine ⟨?_, onInduced_of_cert _ hY (by decide) (by decide) (by decide +kernel) (hc.mono (by decide))⟩
  have := hc.determines
  rwa [← ancestralArcs_eq (r := 18) (by decide)] at this

/-- The topology `bβ|cd` of `{b, c, β, d}`. -/
theorem fig9R_tree_bβcd : InducedHasQuartetTopology isBinaryNetwork_fig9R 1 5 2 3 (by decide) :=
  inducedHasQuartetTopology_of_cut _ _ (e := 7) (S := {18, 17, 10, 1, 16, 11, 8, 15, 12, 5}) (by decide +kernel)

/-- The topology `αb|cd` of `{α, b, c, d}`. -/
theorem fig9R_tree_αbcd : InducedHasQuartetTopology isBinaryNetwork_fig9R 4 1 2 3 (by decide) :=
  inducedHasQuartetTopology_of_cut _ _ (e := 5) (S := {18, 17, 10, 1, 16, 11, 7, 4}) (by decide +kernel)

/-- **"Three applications of the inference rule allow it to be inferred from those that are"** (`a:claim:fig9R`): `{b, c, β, d}` from `{b, c, β, δ}` and `{c, β, δ, d}`; `{α, b, c, d}` from `{α, b, c, β}` and that; `{a, b, c, d}` from
`{a, b, c, α}` and that. -/
theorem fig9R_three_rules : TopologyInferredA isBinaryNetwork_fig9R {0, 1, 2, 3} := by
  have h₁ : TopologyInferredA isBinaryNetwork_fig9R {1, 2, 5, 3} :=
    .rule 1 2 5 6 3 {1, 2, 5, 3} {1, 2, 5, 3} (by decide) (.detected 1 2 5 6 _ fig9R_star_bcβδ) (.detected 2 5 6 3 _ fig9R_star_cβδd) (by decide)
      ⟨1, 5, 2, 3, by decide, by decide, fig9R_tree_bβcd, separated_quartetTree _⟩ (by decide)
  have h₂ : TopologyInferredA isBinaryNetwork_fig9R {4, 1, 2, 3} :=
    .rule 4 1 2 5 3 {4, 1, 2, 3} {4, 1, 2, 3} (by decide) (.detected 4 1 2 5 _ fig9R_star_αbcβ) h₁ (by decide)
      ⟨4, 1, 2, 3, by decide, rfl, fig9R_tree_αbcd, separated_quartetTree _⟩ (by decide)
  have h₂' : TopologyInferredA isBinaryNetwork_fig9R {1, 2, 4, 3} := by
    have he : ({1, 2, 4, 3} : Finset (Fin 7)) = {4, 1, 2, 3} := by decide
    rwa [he]
  exact .rule 0 1 2 4 3 {0, 1, 2, 3} {0, 1, 2, 3} (by decide) (.detected 0 1 2 4 _ fig9R_star_abcα) h₂' (by decide)
    ⟨0, 1, 2, 3, by decide, rfl, fig9R_tree, separated_quartetTree _⟩ (by decide)

/-- **The example of Figure 9, right** (`a:claim:fig9R`), for generic parameters: `{a, b, c, d}` is not detected, `CF_abcd` is strictly `ab|cd`-cut, and the rule infers the set from the `CF`s. -/
theorem fig9R_cf : ForGenericParams fig9R fun θ =>
    ¬ ReadsUnresolved (nmscCF fig9R θ 0) {0, 1, 2, 3} ∧ IsStrictlyCutAt (nmscCF fig9R θ 0) (quartetTree 0 1 2 3 (by decide)) ∧ CFInferredA (nmscCF fig9R θ 0) {0, 1, 2, 3} := by
  refine (corollary1 isBinaryNetwork_fig9R).mono ?_
  rintro θ ⟨hθ, hnot⟩
  refine ⟨hθ, fun h₁ => hnot ⟨?_, (isStrictlyCutAt_iff_inducedHasQuartetTopology _ h₁ _).mpr fig9R_tree, (cfInferredA_iff_topologyInferredA _ h₁ _).mpr fig9R_three_rules⟩⟩
  rintro ⟨a, b, c, d, h, he, hr⟩
  have hs := (readTopology_eq_star_iff _ h (h₁ a b c d h)).mp hr
  have hT := (Bridges.inducedHasStarTopology_iff _ h).mp hs
  rw [he] at hT
  exact hT ⟨quartetTree 0 1 2 3 (by decide), mem_treesOn.2 (quartetTree_taxa _ _ _ _ _), (Bridges.inducedHasQuartetTopology_iff _ _).mp fig9R_tree⟩

end Fig9R

end AllmanEtAl2023.Figures
