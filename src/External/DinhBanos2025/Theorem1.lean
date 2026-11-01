module

public import Phylogenetics.NMSC.Level1.General
public import Phylogenetics.NMSC.Level1.MetricCycle.Realization
public import Phylogenetics.NMSC.DisplayedTreeModel
public import Phylogenetics.Tree.Splice
public import Phylogenetics.Tree.Metric

/-!
# Dinh, Baños 2025, Theorem 1 and Corollary 2: ASTRAL's objective on a 5-cycle

V. Dinh, H. Baños, *Misspecification strikes: ASTRAL can mislead in the presence of hybridization, even for nonanomalous scenarios*, Mol. Biol. Evol. 42 (2025), msaf049. TOB-QMC cites it in passing: under the NMSC, including non-anomalous scenarios, ASTRAL's tree need not be displayed by the network.

The network of Figure 1(d) has a 5-cycle with the taxa `C, B, A, E, D` around it in this order, `C` below the hybrid node, and the edge lengths `e₄`, `e₃`, `e₂` on the three edges between `B, A, E, D`. The hybrid edge of `B` has inheritance probability `γ`, that of `D` has `1 - γ`.

* `net`, `rooted`: the network, as a term of `Phylogenetics.Net` and as a rooted network.
* `displayed_trees`: its displayed trees are `T₁ = ((B,C),A,(D,E))` and `T₂ = ((A,B),E,(C,D))`.
* `cf_abcd`, ...: its concordance factors, from the formulas `Phylogenetics.cycleCF` of a metric cycle.
* `score`: the expected ASTRAL score of a tree, per gene tree: `quartetSupport` of the concordance factors.
* `theorem1`: at Conditions (6) and (7), `S = (((A,E),B),C,D)` scores higher than both `T₁` and `T₂`, and is not displayed. `theorem1_displayed` says this of every parent choice. `corollary2`: likewise for `S′ = (((A,E),D),C,B)`.
* `exists_params`: the conditions hold somewhere, for each of the two.
* `not_quartetAnomalous`: on each set of four taxa, a quartet tree that no displayed tree displays is at most as probable as those that are. The source cites this from Baños 2019; here it is read off the formulas. So the score does what the theorem says at a network with no quartet anomaly.

Departures from the paper. The source's network is semi-directed, with "regardless of the placement of the root". Here it is rooted on the hybrid edge of `D`, as a term of `Phylogenetics.Net`, the form in which the library computes concordance factors. The pendant edges and the hybrid edges have length `1`; the source notes that their lengths have no effect, and `cycleCF` does not read them. The coalescent is at inheritance correlation `0`, the NMSC of the source, which does not mention the correlation. The source's generalization to `n`-cycles, in its Supplementary material, and its simulations, are not formalized. Its numerical example (`e₂ = 2`, `e₃ = 0.2`, `e₄ = 1.1`, `γ = 0.5`) is not checked; `exists_params` uses other values.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace External.DinhBanos2025

/-- The side of Figure 1(d), from the top node of the rooted network: the node of `D`, of `E` and of `A`, and of `B`, above the hybrid node. -/
def side (e₂ e₃ e₄ : ℝ) : Side (Fin 5) :=
  .node 1 1 (.leaf 4) (.node e₂ 1 (.leaf 3) (.node e₃ 1 (.leaf 2) (.node e₄ 1 (.leaf 1) (.hyb 1))))

/-- **The network of Figure 1(d)**, rooted on the hybrid edge of `D`. The taxa are `C, B, A, E, D = 0, …, 4`, in the order around the cycle; `C` is below the hybrid node. -/
def net (γ e₂ e₃ e₄ : ℝ) : Net (Fin 5) := .cycle γ (side e₂ e₃ e₄) (.hyb 1) 1 (.leaf 0)

/-- The cycle of the network. -/
def cyc (γ e₂ e₃ e₄ : ℝ) : (net γ e₂ e₃ e₄).Cycle where
  γ := γ
  side₁ := side e₂ e₃ e₄
  side₂ := .hyb 1
  ℓ := 1
  below := .leaf 0
  mem := by simp [net, Net.subnets]

variable {γ e₂ e₃ e₄ : ℝ}

theorem leaves_net : (net γ e₂ e₃ e₄).leaves = [4, 3, 2, 1, 0] := rfl

/-- The parameters are valid. -/
structure Params (γ e₂ e₃ e₄ : ℝ) : Prop where
  γ₀ : 0 < γ
  γ₁ : γ < 1
  h₂ : 0 < e₂
  h₃ : 0 < e₃
  h₄ : 0 < e₄

theorem wellFormed_net (h : Params γ e₂ e₃ e₄) : (net γ e₂ e₃ e₄).WellFormed := by
  refine ⟨⟨h.γ₀, h.γ₁, one_pos, ⟨one_pos, one_pos, trivial, h.h₂, one_pos, trivial, h.h₃, one_pos, trivial, h.h₄, one_pos, trivial, one_pos⟩, one_pos, trivial, Or.inl (by simp [side, Side.nodes])⟩, by
    rw [leaves_net]; decide⟩

theorem two_le : 2 ≤ (net γ e₂ e₃ e₄).leaves.length := by
  rw [leaves_net]; decide

/-- The metric cycle: `w₁ = e₄` between `B` and `A`, `w₂ = e₃` between `A` and `E`, `w₃ = e₂` between `E` and `D`. -/
def metricCycle (h : Params γ e₂ e₃ e₄) : MetricCycle 5 where
  γ := γ
  w := fun m => if m = 1 then e₄ else if m = 2 then e₃ else e₂
  γ_pos := h.γ₀
  γ_lt_one := h.γ₁
  w_pos := fun m _ _ => by
    have := h.h₂
    have := h.h₃
    have := h.h₄
    split_ifs <;> assumption

theorem size_cyc : (cyc γ e₂ e₃ e₄).size = 5 := by
  rw [Net.Cycle.size_of_top_eq _ rfl]
  rfl

theorem length_nodes : (cyc γ e₂ e₃ e₄).side₁.nodes.length = 4 := rfl

theorem quartetCF_eq (h : Params γ e₂ e₃ e₄) {a b c d : Fin 5} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (net γ e₂ e₃ e₄).quartetCF a b c d = cycleCF (metricCycle h) a b c d := by
  have key := nmsc_quartetCF (net γ e₂ e₃ e₄) (wellFormed_net h) (cyc γ e₂ e₃ e₄) size_cyc (metricCycle h) rfl (fun m h₁ h₂ => ?_) (Equiv.refl _) id (fun i => ?_)
  · exact key a b c d hab hac had hbc hbd hcd
  · have h₃ : m < (cyc γ e₂ e₃ e₄).side₁.nodes.length := by
      rw [length_nodes]
      omega
    rw [Net.Cycle.edgeLen_side₁ _ h₁ h₃]
    have h₄ : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases h₄ with rfl | rfl | rfl <;> rfl
  · have h₀ : ∀ j (hj : j < (cyc γ e₂ e₃ e₄).side₁.nodes.length), (cyc γ e₂ e₃ e₄).component (j + 1) = ((cyc γ e₂ e₃ e₄).side₁.nodes.reverse[j]'(by simpa using hj)).2.2.taxa := fun j hj =>
      Net.Cycle.component_side₁ _ hj
    fin_cases i
    · change (0 : Fin 5) ∈ (cyc γ e₂ e₃ e₄).component 0
      rw [Net.Cycle.component_zero]
      simp [cyc, Net.taxa, Net.leaves]
    · change (1 : Fin 5) ∈ (cyc γ e₂ e₃ e₄).component (0 + 1)
      rw [h₀ 0 (by rw [length_nodes]; omega)]
      simp [cyc, side, Side.nodes, Net.taxa, Net.leaves]
    · change (2 : Fin 5) ∈ (cyc γ e₂ e₃ e₄).component (1 + 1)
      rw [h₀ 1 (by rw [length_nodes]; omega)]
      simp [cyc, side, Side.nodes, Net.taxa, Net.leaves]
    · change (3 : Fin 5) ∈ (cyc γ e₂ e₃ e₄).component (2 + 1)
      rw [h₀ 2 (by rw [length_nodes]; omega)]
      simp [cyc, side, Side.nodes, Net.taxa, Net.leaves]
    · change (4 : Fin 5) ∈ (cyc γ e₂ e₃ e₄).component (3 + 1)
      rw [h₀ 3 (by rw [length_nodes]; omega)]
      simp [cyc, side, Side.nodes, Net.taxa, Net.leaves]

/-! ### The taxa of the rooted network -/

/-- The taxa, in the type of the rooted network. -/
def taxon (γ e₂ e₃ e₄ : ℝ) (x : Fin 5) : (net γ e₂ e₃ e₄).toGraph.Taxon :=
  ⟨x, (Net.taxon_iff (N := net γ e₂ e₃ e₄)).2 (by
    rw [leaves_net]
    fin_cases x <;> simp)⟩

theorem taxon_injective : Function.Injective (taxon γ e₂ e₃ e₄) := fun _ _ h => congrArg Subtype.val h

theorem taxon_surjective : Function.Surjective (taxon γ e₂ e₃ e₄) := fun x => ⟨x.1, rfl⟩

/-- The rooted network of Figure 1(d). -/
def rooted (h : Params γ e₂ e₃ e₄) : RootedNetwork (net γ e₂ e₃ e₄).Vert (net γ e₂ e₃ e₄).toGraph.Arc (net γ e₂ e₃ e₄).toGraph.Taxon :=
  Net.toRootedNetwork (wellFormed_net h) two_le

/-- The concordance factors, on the taxa of `Fin 5`. -/
def cf (h : Params γ e₂ e₃ e₄) (s : QuartetTree (Fin 5)) : ℝ :=
  nmscCF (rooted h) (net γ e₂ e₃ e₄).metricData 0 (s.map taxon_injective)

theorem cf_quartetTree (h : Params γ e₂ e₃ e₄) {a b c d : Fin 5} (hq : ({a, b, c, d} : Finset (Fin 5)).card = 4) :
    cf h (quartetTree a b c d hq) = cycleCF (metricCycle h) a b c d := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hq
  have hq' : ({taxon γ e₂ e₃ e₄ a, taxon γ e₂ e₃ e₄ b, taxon γ e₂ e₃ e₄ c, taxon γ e₂ e₃ e₄ d} : Finset _).card = 4 := by
    have : ({taxon γ e₂ e₃ e₄ a, taxon γ e₂ e₃ e₄ b, taxon γ e₂ e₃ e₄ c, taxon γ e₂ e₃ e₄ d} : Finset _) = ({a, b, c, d} : Finset (Fin 5)).image (taxon γ e₂ e₃ e₄) := by
      simp [image_insert]
    rw [this, card_image_of_injective _ taxon_injective, hq]
  have hm : (quartetTree a b c d hq).map taxon_injective = quartetTree (taxon γ e₂ e₃ e₄ a) (taxon γ e₂ e₃ e₄ b) (taxon γ e₂ e₃ e₄ c) (taxon γ e₂ e₃ e₄ d) hq' := by
    apply Subtype.ext
    simp [QuartetTree.map_val, quartetTree, image_insert]
  rw [cf, hm, rooted, Net.nmscCF_toRootedNetwork (wellFormed_net h) two_le hq']
  exact quartetCF_eq h hab hac had hbc hbd hcd

/-! ### The trees -/

/-- A family of sides on `Fin 5`, as sides on the taxa of the rooted network. -/
def treeOn (γ e₂ e₃ e₄ : ℝ) (T : Finset (Finset (Fin 5))) : Finset (Finset (net γ e₂ e₃ e₄).toGraph.Taxon) :=
  T.image (image (taxon γ e₂ e₃ e₄))

theorem displays_treeOn_map {T : Finset (Finset (Fin 5))} (s : QuartetTree (Fin 5)) :
    Displays (treeOn γ e₂ e₃ e₄ T) (s.map taxon_injective) ↔ Displays T s := by
  have hi := taxon_injective (γ := γ) (e₂ := e₂) (e₃ := e₃) (e₄ := e₄)
  simp only [Displays, treeOn, QuartetTree.map_taxa, QuartetTree.map_val, mem_image]
  constructor
  · rintro ⟨_, ⟨A, hA, rfl⟩, B, hB, hAB⟩
    refine ⟨A, hA, ?_⟩
    rw [← image_inter _ _ hi] at hAB
    rwa [← image_injective hi hAB]
  · rintro ⟨A, hA, hs⟩
    exact ⟨_, ⟨A, hA, rfl⟩, _, hs, image_inter _ _ hi⟩

/-- The score of a tree on the taxa of the rooted network is its score on `Fin 5`. -/
theorem quartetSupport_treeOn (h : Params γ e₂ e₃ e₄) (T : Finset (Finset (Fin 5))) :
    quartetSupport (nmscCF (rooted h) (net γ e₂ e₃ e₄).metricData 0) (treeOn γ e₂ e₃ e₄ T) = quartetSupport (cf h) T := by
  have hb : Function.Bijective (QuartetTree.map (X := (net γ e₂ e₃ e₄).toGraph.Taxon) (taxon_injective (γ := γ) (e₂ := e₂) (e₃ := e₃) (e₄ := e₄))) := by
    refine ⟨QuartetTree.map_injective _, fun s => QuartetTree.exists_map_eq taxon_injective s ?_⟩
    intro x _
    exact mem_image.2 (by obtain ⟨y, rfl⟩ := taxon_surjective (γ := γ) (e₂ := e₂) (e₃ := e₃) (e₄ := e₄) x; exact ⟨y, mem_univ _, rfl⟩)
  unfold quartetSupport
  rw [← (Equiv.ofBijective _ hb).sum_comp]
  refine sum_congr rfl fun s _ => ?_
  simp only [Equiv.ofBijective_apply, displays_treeOn_map, cf]

/-- The score of a tree that displays exactly five quartet trees. -/
theorem quartetSupport_eq {T : Finset (Finset (Fin 5))} {q₁ q₂ q₃ q₄ q₅ : QuartetTree (Fin 5)} (w : QuartetTree (Fin 5) → ℝ)
    (hd : ∀ s, Displays T s ↔ s = q₁ ∨ s = q₂ ∨ s = q₃ ∨ s = q₄ ∨ s = q₅)
    (h₁₂ : q₁ ≠ q₂) (h₁₃ : q₁ ≠ q₃) (h₁₄ : q₁ ≠ q₄) (h₁₅ : q₁ ≠ q₅) (h₂₃ : q₂ ≠ q₃) (h₂₄ : q₂ ≠ q₄) (h₂₅ : q₂ ≠ q₅) (h₃₄ : q₃ ≠ q₄) (h₃₅ : q₃ ≠ q₅) (h₄₅ : q₄ ≠ q₅) :
    quartetSupport w T = w q₁ + w q₂ + w q₃ + w q₄ + w q₅ := by
  unfold quartetSupport
  rw [← sum_filter]
  have hf : (univ.filter fun s => Displays T s) = ({q₁, q₂, q₃, q₄, q₅} : Finset (QuartetTree (Fin 5))) := by
    ext s
    simp [hd]
  rw [hf, sum_insert (by simp [h₁₂, h₁₃, h₁₄, h₁₅]), sum_insert (by simp [h₂₃, h₂₄, h₂₅]), sum_insert (by simp [h₃₄, h₃₅]), sum_pair h₄₅]
  ring

/-- What `T` displays, as a statement about four elements of `Fin 5`. -/
theorem displays_of_table {T : Finset (Finset (Fin 5))} {L : Finset (Finset (Finset (Fin 5)))}
    (ht : ∀ a b c d : Fin 5, ({a, b, c, d} : Finset (Fin 5)).card = 4 → ((∃ A ∈ T, A ∩ {a, b, c, d} = {a, b} ∨ A ∩ {a, b, c, d} = {c, d}) ↔ ({{a, b}, {c, d}} : Finset (Finset (Fin 5))) ∈ L))
    (s : QuartetTree (Fin 5)) : Displays T s ↔ s.val ∈ L := by
  obtain ⟨a, b, c, d, h, rfl⟩ := TreeMetric.exists_eq_quartetTree s
  change Displays T (quartetTree a b c d h) ↔ ({{a, b}, {c, d}} : Finset (Finset (Fin 5))) ∈ L
  rw [← ht a b c d h]
  unfold Displays
  rw [quartetTree_taxa]
  simp only [quartetTree, mem_insert, mem_singleton]

/-- `(((A, E), B), C, D)`, rooted at the node of `C` and `D`. The tree `S` of Theorem 1. -/
def hS : Finset (Finset (Fin 5)) := {univ, {0}, {1}, {2}, {3}, {4}, {2, 3}, {1, 2, 3}}

/-- `(((A, E), D), C, B)`. The tree `S′` of Corollary 2. -/
def hS' : Finset (Finset (Fin 5)) := {univ, {0}, {1}, {2}, {3}, {4}, {2, 3}, {2, 3, 4}}

/-- `((B, C), A, (D, E))`. The displayed tree `T₁`, from the hybrid edge of `B`. -/
def hT₁ : Finset (Finset (Fin 5)) := {univ, {0}, {1}, {2}, {3}, {4}, {0, 1}, {3, 4}}

/-- `((A, B), E, (C, D))`. The displayed tree `T₂`, from the hybrid edge of `D`. -/
def hT₂ : Finset (Finset (Fin 5)) := {univ, {0}, {1}, {2}, {3}, {4}, {1, 2}, {0, 4}}

theorem card_q₁ : ({2, 1, 0, 4} : Finset (Fin 5)).card = 4 := by decide
theorem card_q₂ : ({2, 3, 0, 4} : Finset (Fin 5)).card = 4 := by decide
theorem card_q₃ : ({1, 3, 0, 4} : Finset (Fin 5)).card = 4 := by decide
theorem card_q₄ : ({2, 3, 1, 0} : Finset (Fin 5)).card = 4 := by decide
theorem card_q₅ : ({2, 3, 1, 4} : Finset (Fin 5)).card = 4 := by decide
theorem card_q₆ : ({2, 1, 4, 3} : Finset (Fin 5)).card = 4 := by decide
theorem card_q₇ : ({2, 1, 0, 3} : Finset (Fin 5)).card = 4 := by decide
theorem card_q₈ : ({2, 4, 1, 0} : Finset (Fin 5)).card = 4 := by decide
theorem card_q₉ : ({2, 0, 4, 3} : Finset (Fin 5)).card = 4 := by decide
theorem card_q₁₀ : ({1, 0, 4, 3} : Finset (Fin 5)).card = 4 := by decide

/-- `AB|CD`. -/
abbrev abcd : QuartetTree (Fin 5) := quartetTree 2 1 0 4 card_q₁
/-- `AE|CD`. -/
abbrev aecd : QuartetTree (Fin 5) := quartetTree 2 3 0 4 card_q₂
/-- `BE|CD`. -/
abbrev becd : QuartetTree (Fin 5) := quartetTree 1 3 0 4 card_q₃
/-- `AE|BC`. -/
abbrev aebc : QuartetTree (Fin 5) := quartetTree 2 3 1 0 card_q₄
/-- `AE|BD`. -/
abbrev aebd : QuartetTree (Fin 5) := quartetTree 2 3 1 4 card_q₅
/-- `AB|DE`. -/
abbrev abde : QuartetTree (Fin 5) := quartetTree 2 1 4 3 card_q₆
/-- `AB|CE`. -/
abbrev abce : QuartetTree (Fin 5) := quartetTree 2 1 0 3 card_q₇
/-- `AD|BC`. -/
abbrev adbc : QuartetTree (Fin 5) := quartetTree 2 4 1 0 card_q₈
/-- `AC|DE`. -/
abbrev acde : QuartetTree (Fin 5) := quartetTree 2 0 4 3 card_q₉
/-- `BC|DE`. -/
abbrev bcde : QuartetTree (Fin 5) := quartetTree 1 0 4 3 card_q₁₀

theorem displays_hS (s : QuartetTree (Fin 5)) : Displays (unroot hS) s ↔ s = abcd ∨ s = aecd ∨ s = becd ∨ s = aebc ∨ s = aebd := by
  rw [displays_of_table (L := {abcd.val, aecd.val, becd.val, aebc.val, aebd.val}) (by unfold hS unroot; simp only [quartetTree]; decide +kernel) s]
  simp only [mem_insert, mem_singleton, Subtype.ext_iff]

theorem displays_hS' (s : QuartetTree (Fin 5)) : Displays (unroot hS') s ↔ s = adbc ∨ s = aecd ∨ s = bcde ∨ s = aebc ∨ s = aebd := by
  rw [displays_of_table (L := {adbc.val, aecd.val, bcde.val, aebc.val, aebd.val}) (by unfold hS' unroot; simp only [quartetTree]; decide +kernel) s]
  simp only [mem_insert, mem_singleton, Subtype.ext_iff]

theorem displays_hT₁ (s : QuartetTree (Fin 5)) : Displays (unroot hT₁) s ↔ s = adbc ∨ s = acde ∨ s = bcde ∨ s = aebc ∨ s = abde := by
  rw [displays_of_table (L := {adbc.val, acde.val, bcde.val, aebc.val, abde.val}) (by unfold hT₁ unroot; simp only [quartetTree]; decide +kernel) s]
  simp only [mem_insert, mem_singleton, Subtype.ext_iff]

theorem displays_hT₂ (s : QuartetTree (Fin 5)) : Displays (unroot hT₂) s ↔ s = abcd ∨ s = aecd ∨ s = becd ∨ s = abce ∨ s = abde := by
  rw [displays_of_table (L := {abcd.val, aecd.val, becd.val, abce.val, abde.val}) (by unfold hT₂ unroot; simp only [quartetTree]; decide +kernel) s]
  simp only [mem_insert, mem_singleton, Subtype.ext_iff]

/-- Distinct quartet trees, from their values. -/
theorem ne_of_val {s r : QuartetTree (Fin 5)} (h : s.val ≠ r.val) : s ≠ r := fun e => h (congrArg Subtype.val e)

/-- **`A(S)`.** -/
theorem support_hS (w : QuartetTree (Fin 5) → ℝ) : quartetSupport w (unroot hS) = w abcd + w aecd + w becd + w aebc + w aebd :=
  quartetSupport_eq w displays_hS (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide))
    (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide))

/-- **`A(S′)`.** -/
theorem support_hS' (w : QuartetTree (Fin 5) → ℝ) : quartetSupport w (unroot hS') = w adbc + w aecd + w bcde + w aebc + w aebd :=
  quartetSupport_eq w displays_hS' (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide))
    (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide))

/-- **`A(T₁)`.** -/
theorem support_hT₁ (w : QuartetTree (Fin 5) → ℝ) : quartetSupport w (unroot hT₁) = w adbc + w acde + w bcde + w aebc + w abde :=
  quartetSupport_eq w displays_hT₁ (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide))
    (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide))

/-- **`A(T₂)`.** -/
theorem support_hT₂ (w : QuartetTree (Fin 5) → ℝ) : quartetSupport w (unroot hT₂) = w abcd + w aecd + w becd + w abce + w abde :=
  quartetSupport_eq w displays_hT₂ (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide))
    (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide)) (ne_of_val (by simp only [quartetTree]; decide))

/-! ### The concordance factors -/

section Values

variable (h : Params γ e₂ e₃ e₄)

/-- Equations (1) to (3) of the source, on the five taxon sets: a mixture of the two displayed trees, whose reticulation has one descendant taxon. -/
theorem cf_abcd : cf h abcd = (1 - γ) * (1 - 2 / 3 * Real.exp (-(e₃ + e₂))) + γ * (1 / 3 * Real.exp (-e₄)) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 2 1 0 4 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]
  ring

theorem cf_adbc : cf h adbc = (1 - γ) * (1 / 3 * Real.exp (-(e₃ + e₂))) + γ * (1 - 2 / 3 * Real.exp (-e₄)) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 2 4 1 0 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]
  ring

theorem cf_aecd : cf h aecd = (1 - γ) * (1 - 2 / 3 * Real.exp (-e₂)) + γ * (1 / 3 * Real.exp (-e₃)) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 2 3 0 4 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]
  ring

theorem cf_acde : cf h acde = (1 - γ) * (1 / 3 * Real.exp (-e₂)) + γ * (1 - 2 / 3 * Real.exp (-e₃)) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 2 0 4 3 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]
  ring

theorem cf_becd : cf h becd = (1 - γ) * (1 - 2 / 3 * Real.exp (-e₂)) + γ * (1 / 3 * Real.exp (-(e₄ + e₃))) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 1 3 0 4 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]
  ring

theorem cf_bcde : cf h bcde = (1 - γ) * (1 / 3 * Real.exp (-e₂)) + γ * (1 - 2 / 3 * Real.exp (-(e₄ + e₃))) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 1 0 4 3 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]
  ring

theorem cf_abce : cf h abce = (1 - γ) * (1 - 2 / 3 * Real.exp (-e₃)) + γ * (1 / 3 * Real.exp (-e₄)) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 2 1 0 3 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]
  ring

theorem cf_aebc : cf h aebc = (1 - γ) * (1 / 3 * Real.exp (-e₃)) + γ * (1 - 2 / 3 * Real.exp (-e₄)) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 2 3 1 0 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]
  ring

theorem cf_abde : cf h abde = 1 - 2 / 3 * Real.exp (-e₃) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 2 1 4 3 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]

theorem cf_aebd : cf h aebd = 1 / 3 * Real.exp (-e₃) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 2 3 1 4 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]

end Values

/-! ### The vertices of the rooted network -/

/-- The vertices of the network, by their constructors. -/
abbrev V₀ : Type := CycleVert (NodeVert Unit (NodeVert Unit (NodeVert Unit (NodeVert Unit Empty)))) Empty Unit

/-- The vertices at or below the node of `A` on the side. -/
def inT : V₀ → Prop
  | .side₁ (.rest (.rest _)) => True
  | _ => False

/-- The vertices at or below the node of `A`, on the side and below the hybrid node: closed under children. -/
def inB : V₀ → Prop
  | .side₁ (.rest (.rest _)) => True
  | .hyb => True
  | .below _ => True
  | _ => False

/-- The graph, on the vertices by their constructors. -/
abbrev graph₀ (γ e₂ e₃ e₄ : ℝ) : MetricDigraph V₀ (Fin 5) := (net γ e₂ e₃ e₄).toGraph

theorem adj_enter {u v : V₀} (huv : (graph₀ γ e₂ e₃ e₄).Adj u v) (hu : ¬ inT u) (hv : inT v) : u = .side₁ (.rest .node) ∧ v = .side₁ (.rest (.rest .node)) := by
  rcases v with _ | a | b | _ | c
  · exact hv.elim
  · rcases a with _ | a | a
    · exact hv.elim
    · exact hv.elim
    · rcases a with _ | a | a
      · exact hv.elim
      · exact hv.elim
      · rcases u with _ | a' | b' | _ | c'
        · exact absurd (show (some NodeVert.node : Option (NodeVert Unit (NodeVert Unit (NodeVert Unit (NodeVert Unit Empty))))) = some (.rest (.rest a)) from huv) (by simp)
        · rcases a' with _ | a' | a'
          · exact absurd (show (some NodeVert.node : Option (NodeVert Unit (NodeVert Unit (NodeVert Unit Empty)))) = some (.rest a) from huv) (by simp)
          · exact (show False from huv).elim
          · rcases a' with _ | a' | a'
            · obtain rfl : a = .node := (Option.some.inj (show (some NodeVert.node : Option (NodeVert Unit (NodeVert Unit Empty))) = some a from huv)).symm
              exact ⟨rfl, rfl⟩
            · exact (show False from huv).elim
            · exact (hu trivial).elim
        · exact b'.elim
        · exact (show False from huv).elim
        · exact (show False from huv).elim
  · exact b.elim
  · exact hv.elim
  · exact hv.elim

theorem adj_closed {u v : V₀} (huv : (graph₀ γ e₂ e₃ e₄).Adj u v) (hu : inB u) : inB v := by
  rcases u with _ | a | b | _ | c
  · exact hu.elim
  · rcases a with _ | a | a
    · exact hu.elim
    · exact hu.elim
    · rcases a with _ | a | a
      · exact hu.elim
      · exact hu.elim
      · rcases v with _ | a' | b' | _ | c'
        · exact (show False from huv).elim
        · rcases a' with _ | a' | a'
          · exact (show False from huv).elim
          · exact (show False from huv).elim
          · rcases a' with _ | a' | a'
            · exact (show False from huv).elim
            · exact (show False from huv).elim
            · trivial
        · exact b'.elim
        · trivial
        · exact (show False from huv).elim
  · exact b.elim
  · rcases v with _ | a' | b' | _ | c'
    · exact (show False from huv).elim
    · exact (show False from huv).elim
    · exact b'.elim
    · exact (show False from huv).elim
    · trivial
  · rcases c
    rcases v with _ | a' | b' | _ | c'
    · exact (show False from huv).elim
    · exact (show False from huv).elim
    · exact b'.elim
    · exact (show False from huv).elim
    · trivial

theorem label_inT {v : V₀} {x : Fin 5} (hl : (graph₀ γ e₂ e₃ e₄).label v = some x) (hx : x = 1 ∨ x = 2) : inT v := by
  have h₄ : x ≠ 4 := by rcases hx with rfl | rfl <;> decide
  have h₃ : x ≠ 3 := by rcases hx with rfl | rfl <;> decide
  have h₀ : x ≠ 0 := by rcases hx with rfl | rfl <;> decide
  rcases v with _ | a | b | _ | c
  · exact absurd (show (none : Option (Fin 5)) = some x from hl) (by simp)
  · rcases a with _ | a | a
    · exact absurd (show (none : Option (Fin 5)) = some x from hl) (by simp)
    · exact (h₄ (Option.some.inj (show (some 4 : Option (Fin 5)) = some x from hl)).symm).elim
    · rcases a with _ | a | a
      · exact absurd (show (none : Option (Fin 5)) = some x from hl) (by simp)
      · exact (h₃ (Option.some.inj (show (some 3 : Option (Fin 5)) = some x from hl)).symm).elim
      · trivial
  · exact b.elim
  · exact absurd (show (none : Option (Fin 5)) = some x from hl) (by simp)
  · exact (h₀ (Option.some.inj (show (some 0 : Option (Fin 5)) = some x from hl)).symm).elim

theorem label_not_inB {v : V₀} {x : Fin 5} (hl : (graph₀ γ e₂ e₃ e₄).label v = some x) (hx : x = 3 ∨ x = 4) : ¬ inB v := by
  have h₂ : x ≠ 2 := by rcases hx with rfl | rfl <;> decide
  have h₁ : x ≠ 1 := by rcases hx with rfl | rfl <;> decide
  have h₀ : x ≠ 0 := by rcases hx with rfl | rfl <;> decide
  intro hv
  rcases v with _ | a | b | _ | c
  · exact hv.elim
  · rcases a with _ | a | a
    · exact hv.elim
    · exact hv.elim
    · rcases a with _ | a | a
      · exact hv.elim
      · exact hv.elim
      · rcases a with _ | a | a
        · exact absurd (show (none : Option (Fin 5)) = some x from hl) (by simp)
        · exact (h₂ (Option.some.inj (show (some 2 : Option (Fin 5)) = some x from hl)).symm).elim
        · rcases a with _ | a | a
          · exact absurd (show (none : Option (Fin 5)) = some x from hl) (by simp)
          · exact (h₁ (Option.some.inj (show (some 1 : Option (Fin 5)) = some x from hl)).symm).elim
          · exact a.elim
  · exact b.elim
  · exact absurd (show (none : Option (Fin 5)) = some x from hl) (by simp)
  · exact (h₀ (Option.some.inj (show (some 0 : Option (Fin 5)) = some x from hl)).symm).elim

/-! ### `S` is not displayed -/

section Display

variable (h : Params γ e₂ e₃ e₄)

theorem root_rooted : (rooted h).root = (CycleVert.top : V₀) :=
  (MetricDigraph.eq_toRootedNetwork_root (Net.isNetwork_toGraph (wellFormed_net h) two_le) ((MetricDigraph.indeg_eq_zero_iff (G := (net γ e₂ e₃ e₄).toGraph)).2 (net γ e₂ e₃ e₄).not_adj_root)).symm

theorem isPhylogenetic_rooted : (rooted h).IsPhylogenetic := Net.toRootedNetwork_isPhylogenetic (wellFormed_net h) two_le

theorem label_leaf (x : (net γ e₂ e₃ e₄).toGraph.Taxon) : (graph₀ γ e₂ e₃ e₄).label ((rooted h).leaf x) = some x.1 :=
  MetricDigraph.label_toRootedNetwork_leaf (Net.isNetwork_toGraph (wellFormed_net h) two_le) x

/-- The arc from the node of `E` to the node of `A`: the cut edge of `AB|DE` once `C` is removed. -/
def arcEA (γ e₂ e₃ e₄ : ℝ) : (net γ e₂ e₃ e₄).toGraph.Arc := ⟨((.side₁ (.rest .node) : V₀), (.side₁ (.rest (.rest .node)) : V₀)), rfl⟩

theorem dominates_arcEA {x : (net γ e₂ e₃ e₄).toGraph.Taxon} (hx : x.1 = 1 ∨ x.1 = 2) : (rooted h).Dominates (arcEA γ e₂ e₃ e₄) x := by
  intro hr
  have key : ∀ v, (rooted h).AvoidingReach (arcEA γ e₂ e₃ e₄) (rooted h).root v → ¬ inT (v : V₀) := by
    intro v hv
    induction hv with
    | refl =>
      rw [root_rooted]
      exact id
    | @tail a b _ hab ih =>
      obtain ⟨f, hfe, rfl, rfl⟩ := hab
      intro hb
      obtain ⟨h₁, h₂⟩ := adj_enter f.2 ih hb
      exact hfe (Subtype.ext (Prod.ext h₁ h₂))
  exact key _ hr (label_inT (label_leaf h x) hx)

theorem not_isBelow_arcEA {x : (net γ e₂ e₃ e₄).toGraph.Taxon} (hx : x.1 = 3 ∨ x.1 = 4) : ¬ (rooted h).IsBelow (arcEA γ e₂ e₃ e₄) x := by
  intro hr
  have key : ∀ v, (rooted h).graph.Reaches ((rooted h).graph.target (arcEA γ e₂ e₃ e₄)) v → inB (v : V₀) := by
    intro v hv
    induction hv with
    | refl => trivial
    | @tail a b _ hab ih =>
      obtain ⟨f, rfl, rfl⟩ := hab
      exact adj_closed f.2 ih
  exact label_not_inB (label_leaf h x) hx (key _ hr)

/-- Every parent choice displays `AB|DE`. -/
theorem displays_abde (c : (rooted h).ParentChoice) : Displays ((rooted h).displayedSides c) (abde.map taxon_injective) := by
  refine displays_displayedSides_of_separates (isPhylogenetic_rooted h) c (P := ({2, 1} : Finset (Fin 5)).image (taxon γ e₂ e₃ e₄)) (e := arcEA γ e₂ e₃ e₄) ?_ ?_ ?_
  · rw [QuartetTree.map_val]
    exact mem_image_of_mem _ (by simp [quartetTree])
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    refine dominates_arcEA h ?_
    simpa [taxon, or_comm] using hy
  · intro x hx hxP
    rw [QuartetTree.map_taxa, quartetTree_taxa] at hx
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    refine not_isBelow_arcEA h ?_
    have hy' : y ∉ ({2, 1} : Finset (Fin 5)) := fun h₀ => hxP (mem_image_of_mem _ h₀)
    have hc : ∀ y : Fin 5, y ∈ ({2, 1, 4, 3} : Finset (Fin 5)) → y ∉ ({2, 1} : Finset (Fin 5)) → y = 3 ∨ y = 4 := by decide
    exact hc y hy hy'

/-- `AE|BD` is displayed by neither `S` nor `S′`, once it is displayed by a parent choice. -/
theorem not_displays_aebd (c : (rooted h).ParentChoice) : ¬ Displays ((rooted h).displayedSides c) (aebd.map taxon_injective) := by
  intro h₂
  have : Nonempty (net γ e₂ e₃ e₄).toGraph.Taxon := ⟨taxon γ e₂ e₃ e₄ 0⟩
  have hT := isUnrootedTree_displayedSides (isPhylogenetic_rooted h) c
  have heq := hT.displays_unique (displays_abde h c) h₂ (by
    rw [QuartetTree.map_taxa, QuartetTree.map_taxa, quartetTree_taxa, quartetTree_taxa]
    congr 1
    decide)
  have hv := congrArg Subtype.val (QuartetTree.map_injective _ heq)
  simp only [quartetTree] at hv
  exact absurd hv (by decide)

theorem not_displayed_S (c : (rooted h).ParentChoice) : (rooted h).displayedSides c ≠ treeOn γ e₂ e₃ e₄ (unroot hS) := fun hc =>
  not_displays_aebd h c (by
    rw [hc, displays_treeOn_map, displays_hS]
    exact Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem not_displayed_S' (c : (rooted h).ParentChoice) : (rooted h).displayedSides c ≠ treeOn γ e₂ e₃ e₄ (unroot hS') := fun hc =>
  not_displays_aebd h c (by
    rw [hc, displays_treeOn_map, displays_hS']
    exact Or.inr (Or.inr (Or.inr (Or.inr rfl))))

end Display

/-! ### The theorems -/

/-- **The expected ASTRAL score of `T`** per gene tree: the sum, over the quartet trees that `T` displays, of their probabilities under the NMSC on the network. -/
def score (h : Params γ e₂ e₃ e₄) (T : Finset (Finset (Fin 5))) : ℝ :=
  quartetSupport (nmscCF (rooted h) (net γ e₂ e₃ e₄).metricData 0) (treeOn γ e₂ e₃ e₄ T)

section Main

variable (h : Params γ e₂ e₃ e₄)

theorem score_S : score h (unroot hS) = cf h abcd + cf h aecd + cf h becd + cf h aebc + cf h aebd := by
  rw [score, quartetSupport_treeOn, support_hS]

theorem score_S' : score h (unroot hS') = cf h adbc + cf h aecd + cf h bcde + cf h aebc + cf h aebd := by
  rw [score, quartetSupport_treeOn, support_hS']

theorem score_T₁ : score h (unroot hT₁) = cf h adbc + cf h acde + cf h bcde + cf h aebc + cf h abde := by
  rw [score, quartetSupport_treeOn, support_hT₁]

theorem score_T₂ : score h (unroot hT₂) = cf h abcd + cf h aecd + cf h becd + cf h abce + cf h abde := by
  rw [score, quartetSupport_treeOn, support_hT₂]

include h in
/-- What Condition (7) says. -/
theorem of_condition7 (h7 : 1 - Real.exp (-e₃) < min (γ / (2 - γ) * (1 - Real.exp (-e₄))) ((1 - γ) / (1 + γ) * (1 - Real.exp (-e₂)))) :
    (2 - γ) * (1 - Real.exp (-e₃)) < γ * (1 - Real.exp (-e₄)) ∧ (1 + γ) * (1 - Real.exp (-e₃)) < (1 - γ) * (1 - Real.exp (-e₂)) := by
  have hγ₀ := h.γ₀
  have hγ₁ := h.γ₁
  obtain ⟨h₁, h₂⟩ := lt_min_iff.1 h7
  rw [div_mul_eq_mul_div, lt_div_iff₀ (by linarith)] at h₁ h₂
  exact ⟨by linarith, by linarith⟩

theorem exp_neg_pos (x : ℝ) : 0 < Real.exp (-x) := Real.exp_pos _

/-- `exp (-x)` is below one, for `x > 0`. -/
theorem exp_neg_lt_one {x : ℝ} (hx : 0 < x) : Real.exp (-x) < 1 := Real.exp_lt_one_iff.2 (by linarith)

/-- **Theorem 1 of Dinh, Baños 2025** (`ext:dinh_banos_thm1`): the tree `S = (((A, E), B), C, D)`, which the network does not display, has a higher expected ASTRAL score than both `T₁` and `T₂`. -/
theorem theorem1 (h6 : 1 - Real.exp (-e₂) > γ / (1 - γ) * (1 - Real.exp (-e₃) * Real.exp (-e₄)))
    (h7 : 1 - Real.exp (-e₃) < min (γ / (2 - γ) * (1 - Real.exp (-e₄))) ((1 - γ) / (1 + γ) * (1 - Real.exp (-e₂)))) :
    score h (unroot hT₁) < score h (unroot hS) ∧ score h (unroot hT₂) < score h (unroot hS) ∧ ∀ c, (rooted h).displayedSides c ≠ treeOn γ e₂ e₃ e₄ (unroot hS) := by
  refine ⟨?_, ?_, not_displayed_S h⟩
  all_goals
    obtain ⟨h7a, h7b⟩ := of_condition7 h h7
    have hγ₀ := h.γ₀
    have hγ₁ := h.γ₁
    have hg : 0 < 1 - γ := by linarith
    have h6' : γ * (1 - Real.exp (-e₃) * Real.exp (-e₄)) < (1 - γ) * (1 - Real.exp (-e₂)) := by
      rw [gt_iff_lt, div_mul_eq_mul_div, div_lt_iff₀ hg] at h6
      linarith
    have y₂ := exp_neg_lt_one h.h₂
    have y₃ := exp_neg_lt_one h.h₃
    have y₄ := exp_neg_lt_one h.h₄
    have p₂ := exp_neg_pos e₂
    have p₃ := exp_neg_pos e₃
    have p₄ := exp_neg_pos e₄
    have e₁ : Real.exp (-(e₃ + e₂)) = Real.exp (-e₃) * Real.exp (-e₂) := by rw [neg_add, Real.exp_add]
    have e₅ : Real.exp (-(e₄ + e₃)) = Real.exp (-e₃) * Real.exp (-e₄) := by rw [neg_add, Real.exp_add, mul_comm]
  · rw [score_S, score_T₁, cf_abcd, cf_adbc, cf_aecd, cf_acde, cf_becd, cf_bcde, cf_aebc, cf_aebd, cf_abde, e₁, e₅]
    have h₁ : (1 - γ) * (1 - Real.exp (-e₂)) ≤ (1 - γ) * (1 - Real.exp (-e₃) * Real.exp (-e₂)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hg.le
    have h₂ : γ * (1 - Real.exp (-e₄)) ≤ γ * (1 - Real.exp (-e₃) * Real.exp (-e₄)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hγ₀.le
    linarith
  · rw [score_S, score_T₂, cf_aebc, cf_aebd, cf_abce, cf_abde]
    linarith

/-- **Corollary 2 of Dinh, Baños 2025** (`ext:dinh_banos_cor2`): the tree `S′ = (((A, E), D), C, B)`, which the network does not display, has a higher expected ASTRAL score than both `T₁` and `T₂`. -/
theorem corollary2 (h6 : 1 - Real.exp (-e₄) > (1 - γ) / γ * (1 - Real.exp (-e₃) * Real.exp (-e₂)))
    (h7 : 1 - Real.exp (-e₃) < min (γ / (2 - γ) * (1 - Real.exp (-e₄))) ((1 - γ) / (1 + γ) * (1 - Real.exp (-e₂)))) :
    score h (unroot hT₁) < score h (unroot hS') ∧ score h (unroot hT₂) < score h (unroot hS') ∧ ∀ c, (rooted h).displayedSides c ≠ treeOn γ e₂ e₃ e₄ (unroot hS') := by
  refine ⟨?_, ?_, not_displayed_S' h⟩
  all_goals
    obtain ⟨h7a, h7b⟩ := of_condition7 h h7
    have hγ₀ := h.γ₀
    have hγ₁ := h.γ₁
    have hg : 0 < 1 - γ := by linarith
    have h6' : (1 - γ) * (1 - Real.exp (-e₃) * Real.exp (-e₂)) < γ * (1 - Real.exp (-e₄)) := by
      rw [gt_iff_lt, div_mul_eq_mul_div, div_lt_iff₀ hγ₀] at h6
      linarith
    have y₂ := exp_neg_lt_one h.h₂
    have y₃ := exp_neg_lt_one h.h₃
    have y₄ := exp_neg_lt_one h.h₄
    have p₂ := exp_neg_pos e₂
    have p₃ := exp_neg_pos e₃
    have p₄ := exp_neg_pos e₄
    have e₁ : Real.exp (-(e₃ + e₂)) = Real.exp (-e₃) * Real.exp (-e₂) := by rw [neg_add, Real.exp_add]
    have e₅ : Real.exp (-(e₄ + e₃)) = Real.exp (-e₃) * Real.exp (-e₄) := by rw [neg_add, Real.exp_add, mul_comm]
  · rw [score_S', score_T₁, cf_aecd, cf_acde, cf_aebd, cf_abde]
    linarith
  · rw [score_S', score_T₂, cf_abcd, cf_adbc, cf_aecd, cf_becd, cf_bcde, cf_aebc, cf_aebd, cf_abce, cf_abde, e₁, e₅]
    have h₁ : (1 - γ) * (1 - Real.exp (-e₂)) ≤ (1 - γ) * (1 - Real.exp (-e₃) * Real.exp (-e₂)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hg.le
    have h₂ : γ * (1 - Real.exp (-e₄)) ≤ γ * (1 - Real.exp (-e₃) * Real.exp (-e₄)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hγ₀.le
    linarith

/-! ### No quartet anomaly -/

section Anomaly

variable (h : Params γ e₂ e₃ e₄)

/-- `AC|BD`. -/
abbrev acbd : QuartetTree (Fin 5) := quartetTree 2 0 1 4 (by decide)
/-- `AD|CE`. -/
abbrev adce : QuartetTree (Fin 5) := quartetTree 2 4 0 3 (by decide)
/-- `BD|CE`. -/
abbrev bdce : QuartetTree (Fin 5) := quartetTree 1 4 0 3 (by decide)
/-- `AC|BE`. -/
abbrev acbe : QuartetTree (Fin 5) := quartetTree 2 0 1 3 (by decide)
/-- `AD|BE`. -/
abbrev adbe : QuartetTree (Fin 5) := quartetTree 2 4 1 3 (by decide)

theorem cf_acbd : cf h acbd = (1 - γ) * (1 / 3 * Real.exp (-(e₃ + e₂))) + γ * (1 / 3 * Real.exp (-e₄)) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 2 0 1 4 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]
  ring

theorem cf_adce : cf h adce = (1 - γ) * (1 / 3 * Real.exp (-e₂)) + γ * (1 / 3 * Real.exp (-e₃)) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 2 4 0 3 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]
  ring

theorem cf_bdce : cf h bdce = (1 - γ) * (1 / 3 * Real.exp (-e₂)) + γ * (1 / 3 * Real.exp (-(e₄ + e₃))) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 1 4 0 3 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]
  ring

theorem cf_acbe : cf h acbe = (1 - γ) * (1 / 3 * Real.exp (-e₃)) + γ * (1 / 3 * Real.exp (-e₄)) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 2 0 1 3 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]
  ring

theorem cf_adbe : cf h adbe = 1 / 3 * Real.exp (-e₃) := by
  rw [cf_quartetTree]
  change cycleCF (metricCycle h) 2 4 1 3 = _
  norm_num [cycleCF, pathCF, pathLen, toRightEnd, metricCycle, Finset.sum_Ico_succ_top]

/-- **The network is not quartet-anomalous**, at all parameters: on each set of four taxa, a quartet tree that no displayed tree displays is at most as probable as those that are. -/
theorem not_quartetAnomalous :
    cf h acbd ≤ cf h abcd ∧ cf h acbd ≤ cf h adbc ∧ cf h adce ≤ cf h aecd ∧ cf h adce ≤ cf h acde ∧ cf h bdce ≤ cf h becd ∧ cf h bdce ≤ cf h bcde ∧
      cf h acbe ≤ cf h abce ∧ cf h acbe ≤ cf h aebc ∧ cf h aebd ≤ cf h abde ∧ cf h adbe ≤ cf h abde := by
  have hγ₀ := h.γ₀
  have hg : 0 < 1 - γ := by linarith [h.γ₁]
  have y₂ := exp_neg_lt_one h.h₂
  have y₃ := exp_neg_lt_one h.h₃
  have y₄ := exp_neg_lt_one h.h₄
  have y₅ := exp_neg_lt_one (add_pos h.h₃ h.h₂)
  have y₆ := exp_neg_lt_one (add_pos h.h₄ h.h₃)
  rw [cf_acbd, cf_abcd, cf_adbc, cf_adce, cf_aecd, cf_acde, cf_bdce, cf_becd, cf_bcde, cf_acbe, cf_abce, cf_aebc, cf_aebd, cf_abde, cf_adbe]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

end Anomaly

/-- **The conditions hold somewhere**: Conditions (6) and (7) of Theorem 1, at `y₂ = 1/10`, `y₃ = 9/10`, `y₄ = 3/10`, `γ = 1/2`, and those of Corollary 2 at `y₂ = 3/10`, `y₃ = 9/10`, `y₄ = 1/10`, `γ = 1/2`. -/
theorem exists_params :
    (∃ e₂ e₃ e₄ : ℝ, Params (1 / 2) e₂ e₃ e₄ ∧ 1 - Real.exp (-e₂) > (1 / 2) / (1 - 1 / 2) * (1 - Real.exp (-e₃) * Real.exp (-e₄)) ∧
      1 - Real.exp (-e₃) < min ((1 / 2) / (2 - 1 / 2) * (1 - Real.exp (-e₄))) ((1 - 1 / 2) / (1 + 1 / 2) * (1 - Real.exp (-e₂)))) ∧
    ∃ e₂ e₃ e₄ : ℝ, Params (1 / 2) e₂ e₃ e₄ ∧ 1 - Real.exp (-e₄) > (1 - 1 / 2) / (1 / 2) * (1 - Real.exp (-e₃) * Real.exp (-e₂)) ∧
      1 - Real.exp (-e₃) < min ((1 / 2) / (2 - 1 / 2) * (1 - Real.exp (-e₄))) ((1 - 1 / 2) / (1 + 1 / 2) * (1 - Real.exp (-e₂))) := by
  have hl : ∀ x : ℝ, 1 < x → 0 < Real.log x ∧ Real.exp (-Real.log x) = 1 / x := fun x hx =>
    ⟨Real.log_pos hx, by rw [Real.exp_neg, Real.exp_log (by linarith), one_div]⟩
  obtain ⟨p₁, v₁⟩ := hl (10 : ℝ) (by norm_num)
  obtain ⟨p₂, v₂⟩ := hl (10 / 9 : ℝ) (by norm_num)
  obtain ⟨p₃, v₃⟩ := hl (10 / 3 : ℝ) (by norm_num)
  refine ⟨⟨Real.log 10, Real.log (10 / 9), Real.log (10 / 3), ⟨by norm_num, by norm_num, p₁, p₂, p₃⟩, ?_, ?_⟩, ⟨Real.log (10 / 3), Real.log (10 / 9), Real.log 10, ⟨by norm_num, by norm_num, p₃, p₂, p₁⟩, ?_, ?_⟩⟩
  all_goals rw [v₁, v₂, v₃]
  all_goals norm_num

/-! ### The displayed trees -/

/-- The arcs of the network. -/
def arcs : List (V₀ × V₀) :=
  [(.top, .side₁ .node), (.top, .hyb),
   (.side₁ .node, .side₁ (.pendant ())), (.side₁ .node, .side₁ (.rest .node)),
   (.side₁ (.rest .node), .side₁ (.rest (.pendant ()))), (.side₁ (.rest .node), .side₁ (.rest (.rest .node))),
   (.side₁ (.rest (.rest .node)), .side₁ (.rest (.rest (.pendant ())))), (.side₁ (.rest (.rest .node)), .side₁ (.rest (.rest (.rest .node)))),
   (.side₁ (.rest (.rest (.rest .node))), .side₁ (.rest (.rest (.rest (.pendant ()))))), (.side₁ (.rest (.rest (.rest .node))), .hyb),
   (.hyb, .below ())]

theorem adj_mem {u v : V₀} (huv : (graph₀ γ e₂ e₃ e₄).Adj u v) : (u, v) ∈ arcs := by
  rcases u with _ | (_ | ⟨⟩ | (_ | ⟨⟩ | (_ | ⟨⟩ | (_ | ⟨⟩ | ⟨⟩)))) | ⟨⟩ | _ | ⟨⟩ <;>
  rcases v with _ | (_ | ⟨⟩ | (_ | ⟨⟩ | (_ | ⟨⟩ | (_ | ⟨⟩ | ⟨⟩)))) | ⟨⟩ | _ | ⟨⟩ <;>
  first
  | (simp [arcs]; done)
  | exact (show False from huv).elim
  | (change _ = _ at huv; cases huv)

/-- The arc left out by the parent choice that keeps the hybrid edge of `B` (`k = true`) or of `D` (`k = false`). -/
def del (k : Bool) : V₀ × V₀ := if k then (.top, .hyb) else (.side₁ (.rest (.rest (.rest .node))), .hyb)

/-- The arc kept. -/
def kept (k : Bool) : V₀ × V₀ := del (!k)

/-- The taxa below each vertex, along the arcs kept. -/
def clusterOf (k : Bool) : V₀ → Finset (Fin 5)
  | .top => univ
  | .side₁ .node => if k then univ else {4, 3, 2, 1}
  | .side₁ (.pendant _) => {4}
  | .side₁ (.rest .node) => if k then {3, 2, 1, 0} else {3, 2, 1}
  | .side₁ (.rest (.pendant _)) => {3}
  | .side₁ (.rest (.rest .node)) => if k then {2, 1, 0} else {2, 1}
  | .side₁ (.rest (.rest (.pendant _))) => {2}
  | .side₁ (.rest (.rest (.rest .node))) => if k then {1, 0} else {1}
  | .side₁ (.rest (.rest (.rest (.pendant _)))) => {1}
  | .side₁ (.rest (.rest (.rest (.rest x)))) => x.elim
  | .side₂ b => b.elim
  | .hyb => {0}
  | .below _ => {0}

/-- The leaf of a taxon. -/
def vertexOf (y : Fin 5) : V₀ :=
  match y with
  | 0 => .below ()
  | 1 => .side₁ (.rest (.rest (.rest (.pendant ()))))
  | 2 => .side₁ (.rest (.rest (.pendant ())))
  | 3 => .side₁ (.rest (.pendant ()))
  | 4 => .side₁ (.pendant ())

theorem eq_vertexOf {v : V₀} {y : Fin 5} (hl : (graph₀ γ e₂ e₃ e₄).label v = some y) : v = vertexOf y := by
  have hn : (none : Option (Fin 5)) ≠ some y := by simp
  rcases v with _ | (_ | a | (_ | a | (_ | a | (_ | a | a)))) | b | _ | c
  · exact absurd hl hn
  · exact absurd hl hn
  · obtain rfl : (4 : Fin 5) = y := Option.some.inj hl
    rfl
  · exact absurd hl hn
  · obtain rfl : (3 : Fin 5) = y := Option.some.inj hl
    rfl
  · exact absurd hl hn
  · obtain rfl : (2 : Fin 5) = y := Option.some.inj hl
    rfl
  · exact absurd hl hn
  · obtain rfl : (1 : Fin 5) = y := Option.some.inj hl
    rfl
  · exact a.elim
  · exact b.elim
  · exact absurd hl hn
  · obtain rfl : (0 : Fin 5) = y := Option.some.inj hl
    rfl

/-- What a parent of a vertex other than the hybrid node is. -/
def parentOf : V₀ → V₀
  | .side₁ .node => .top
  | .side₁ (.pendant _) => .side₁ .node
  | .side₁ (.rest .node) => .side₁ .node
  | .side₁ (.rest (.pendant _)) => .side₁ (.rest .node)
  | .side₁ (.rest (.rest .node)) => .side₁ (.rest .node)
  | .side₁ (.rest (.rest (.pendant _))) => .side₁ (.rest (.rest .node))
  | .side₁ (.rest (.rest (.rest .node))) => .side₁ (.rest (.rest .node))
  | .side₁ (.rest (.rest (.rest (.pendant _)))) => .side₁ (.rest (.rest (.rest .node)))
  | .below _ => .hyb
  | _ => .top

theorem eq_parentOf {p : V₀ × V₀} (hp : p ∈ arcs) (hne : p.2 ≠ .hyb) : p.1 = parentOf p.2 := by
  simp only [arcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | exact absurd rfl hne

/-- A step of the clusters along the arcs kept. -/
theorem clusterOf_step (k : Bool) {p : V₀ × V₀} (hp : p ∈ arcs) (hne : p ≠ del k) : clusterOf k p.2 ⊆ clusterOf k p.1 := by
  simp only [arcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  cases k <;> rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact absurd rfl hne | (simp only [clusterOf]; decide)

theorem mem_clusterOf_of_label (k : Bool) {v : V₀} {y : Fin 5} (hl : (graph₀ γ e₂ e₃ e₄).label v = some y) : y ∈ clusterOf k v := by
  rw [eq_vertexOf hl]
  cases k <;> fin_cases y <;> decide

theorem not_adj_top {u v : V₀} (huv : (graph₀ γ e₂ e₃ e₄).Adj u v) (hv : v = .top) : False := by
  subst hv
  exact (net γ e₂ e₃ e₄).not_adj_root u huv

/-- The two arcs into the hybrid node. -/
theorem arcs_hyb {p : V₀ × V₀} (hp : p ∈ arcs) (ht : p.2 = .hyb) : p = (.top, .hyb) ∨ p = (.side₁ (.rest (.rest (.rest .node))), .hyb) := by
  simp only [arcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact absurd ht (by simp)

section Choice

variable (h : Params γ e₂ e₃ e₄) {k : Bool} {c : (rooted h).ParentChoice}

theorem hyb_ne_root : (CycleVert.hyb : V₀) ≠ (rooted h).root := by
  rw [root_rooted]
  simp

theorem not_mem_deleted_iff (hc : (c ⟨.hyb, hyb_ne_root h⟩).val.1 = kept k) (f : (net γ e₂ e₃ e₄).toGraph.Arc) :
    f ∉ (rooted h).deletedArcs c ↔ f.1 ≠ del k := by
  have hcc : ∀ (v : V₀) (hv : v ≠ (rooted h).root), v = .hyb → (c ⟨v, hv⟩).val = (c ⟨.hyb, hyb_ne_root h⟩).val := by
    rintro v hv rfl
    rfl
  have hne : ∀ k' : Bool, kept k' ≠ del k' := by
    intro k'
    cases k' <;> simp [kept, del]
  constructor
  · intro hf hd
    apply hf
    intro hr hg
    have ht : (rooted h).graph.target f = .hyb := by
      change f.1.2 = _
      rw [hd]
      cases k <;> rfl
    rw [hcc _ hr ht] at hg
    apply hne k
    rw [← hc, hg, hd]
  · intro hf hd
    have hr : (rooted h).graph.target f ≠ (rooted h).root := fun h₀ =>
      not_adj_top f.2 (h₀.trans (root_rooted h))
    apply hd hr
    set g := (c ⟨(rooted h).graph.target f, hr⟩) with hg
    apply Subtype.ext
    have h₂ : g.val.1.2 = f.1.2 := g.2
    refine Prod.ext ?_ h₂
    by_cases ht : f.1.2 = (.hyb : V₀)
    · have hk : g.val.1 = kept k := by
        rw [hg, hcc _ hr ht, hc]
      have hm : f.1 ∈ arcs := adj_mem f.2
      have hk₁ : f.1 = kept k := by
        have hl := arcs_hyb hm ht
        cases k
        · rcases hl with hl | hl
          · exact hl
          · exact absurd hl hf
        · rcases hl with hl | hl
          · exact absurd hl hf
          · exact hl
      rw [hk, hk₁]
    · have h₃ := eq_parentOf (p := f.1) (adj_mem f.2) ht
      have h₄ := eq_parentOf (p := g.val.1) (adj_mem g.val.2) (by rw [h₂]; exact ht)
      rw [h₃, h₄, h₂]

theorem off_mem (hc : (c ⟨.hyb, hyb_ne_root h⟩).val.1 = kept k) {v w : V₀} {y : Fin 5} (hr : (rooted h).ReachesOff ((rooted h).deletedArcs c) v w) (hl : (graph₀ γ e₂ e₃ e₄).label w = some y) :
    y ∈ clusterOf k v := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact mem_clusterOf_of_label k hl
  | head step _ ih =>
    obtain ⟨f, hf, rfl, rfl⟩ := step
    exact clusterOf_step k (adj_mem f.2) ((not_mem_deleted_iff h hc f).1 hf) ih

theorem off_step (hc : (c ⟨.hyb, hyb_ne_root h⟩).val.1 = kept k) {a b : V₀} (hadj : (graph₀ γ e₂ e₃ e₄).Adj a b) (hne : (a, b) ≠ del k) :
    (rooted h).ReachesOff ((rooted h).deletedArcs c) a b :=
  Relation.ReflTransGen.single ⟨⟨(a, b), hadj⟩, (not_mem_deleted_iff h hc _).2 hne, rfl, rfl⟩

theorem off_of_mem (hc : (c ⟨.hyb, hyb_ne_root h⟩).val.1 = kept k) (v : V₀) {y : Fin 5} (hy : y ∈ clusterOf k v) :
    (rooted h).ReachesOff ((rooted h).deletedArcs c) v (vertexOf y) := by
  have st := fun {a b : V₀} (hadj : (graph₀ γ e₂ e₃ e₄).Adj a b) (hne : (a, b) ≠ del k) => off_step h hc hadj hne
  have r_hyb : (rooted h).ReachesOff ((rooted h).deletedArcs c) .hyb (vertexOf 0) := st (a := .hyb) (b := .below ()) rfl (by cases k <;> simp [del])
  have r_n₄ : ∀ y ∈ clusterOf k (.side₁ (.rest (.rest (.rest .node)))), (rooted h).ReachesOff ((rooted h).deletedArcs c) (.side₁ (.rest (.rest (.rest .node)))) (vertexOf y) := by
    intro y hy
    have h₁ : y = 1 ∨ (y = 0 ∧ k = true) := by
      cases k
      · have : y = 1 := by simpa [clusterOf] using hy
        exact Or.inl this
      · have : y = 1 ∨ y = 0 := by simpa [clusterOf] using hy
        rcases this with h₀ | h₀
        · exact Or.inl h₀
        · exact Or.inr ⟨h₀, rfl⟩
    rcases h₁ with rfl | ⟨rfl, rfl⟩
    · exact st (a := .side₁ (.rest (.rest (.rest .node)))) (b := .side₁ (.rest (.rest (.rest (.pendant ()))))) rfl (by cases k <;> simp [del])
    · exact (st (a := .side₁ (.rest (.rest (.rest .node)))) (b := .hyb) rfl (by simp [del])).trans r_hyb
  have r_n₃ : ∀ y ∈ clusterOf k (.side₁ (.rest (.rest .node))), (rooted h).ReachesOff ((rooted h).deletedArcs c) (.side₁ (.rest (.rest .node))) (vertexOf y) := by
    intro y hy
    have h₁ : y = 2 ∨ y ∈ clusterOf k (.side₁ (.rest (.rest (.rest .node)))) := by
      revert y
      cases k <;> simp only [clusterOf] <;> decide
    rcases h₁ with rfl | h₁
    · exact st (a := .side₁ (.rest (.rest .node))) (b := .side₁ (.rest (.rest (.pendant ())))) rfl (by cases k <;> simp [del])
    · exact (st (a := .side₁ (.rest (.rest .node))) (b := .side₁ (.rest (.rest (.rest .node)))) rfl (by cases k <;> simp [del])).trans (r_n₄ y h₁)
  have r_n₂ : ∀ y ∈ clusterOf k (.side₁ (.rest .node)), (rooted h).ReachesOff ((rooted h).deletedArcs c) (.side₁ (.rest .node)) (vertexOf y) := by
    intro y hy
    have h₁ : y = 3 ∨ y ∈ clusterOf k (.side₁ (.rest (.rest .node))) := by
      revert y
      cases k <;> simp only [clusterOf] <;> decide
    rcases h₁ with rfl | h₁
    · exact st (a := .side₁ (.rest .node)) (b := .side₁ (.rest (.pendant ()))) rfl (by cases k <;> simp [del])
    · exact (st (a := .side₁ (.rest .node)) (b := .side₁ (.rest (.rest .node))) rfl (by cases k <;> simp [del])).trans (r_n₃ y h₁)
  have r_n₁ : ∀ y ∈ clusterOf k (.side₁ .node), (rooted h).ReachesOff ((rooted h).deletedArcs c) (.side₁ .node) (vertexOf y) := by
    intro y hy
    have h₁ : y = 4 ∨ y ∈ clusterOf k (.side₁ (.rest .node)) := by
      revert y
      cases k <;> simp only [clusterOf] <;> decide
    rcases h₁ with rfl | h₁
    · exact st (a := .side₁ .node) (b := .side₁ (.pendant ())) rfl (by cases k <;> simp [del])
    · exact (st (a := .side₁ .node) (b := .side₁ (.rest .node)) rfl (by cases k <;> simp [del])).trans (r_n₂ y h₁)
  rcases v with _ | (_ | a | (_ | a | (_ | a | (_ | a | a)))) | b | _ | d
  · have h₁ : y ∈ clusterOf k (.side₁ .node) ∨ (y = 0 ∧ k = false) := by
      revert y
      cases k <;> simp only [clusterOf] <;> decide
    rcases h₁ with h₁ | ⟨rfl, rfl⟩
    · exact (st (a := .top) (b := .side₁ .node) rfl (by cases k <;> simp [del])).trans (r_n₁ y h₁)
    · exact (st (a := .top) (b := .hyb) (Or.inr rfl) (by simp [del])).trans r_hyb
  · exact r_n₁ y hy
  · obtain rfl : y = 4 := by simpa [clusterOf] using hy
    exact .refl
  · exact r_n₂ y hy
  · obtain rfl : y = 3 := by simpa [clusterOf] using hy
    exact .refl
  · exact r_n₃ y hy
  · obtain rfl : y = 2 := by simpa [clusterOf] using hy
    exact .refl
  · exact r_n₄ y hy
  · obtain rfl : y = 1 := by simpa [clusterOf] using hy
    exact .refl
  · exact a.elim
  · exact b.elim
  · obtain rfl : y = 0 := by simpa [clusterOf] using hy
    exact r_hyb
  · obtain rfl : y = 0 := by simpa [clusterOf] using hy
    exact .refl

theorem displayedCluster_eq (hc : (c ⟨.hyb, hyb_ne_root h⟩).val.1 = kept k) (v : (net γ e₂ e₃ e₄).Vert) :
    (rooted h).displayedCluster c v = (clusterOf k v).image (taxon γ e₂ e₃ e₄) := by
  ext x
  obtain ⟨y, rfl⟩ := taxon_surjective x
  refine mem_displayedCluster.trans ?_
  rw [taxon_injective.mem_finset_image]
  constructor
  · intro hr
    exact off_mem h hc hr (label_leaf h _)
  · intro hy
    rw [show (rooted h).leaf (taxon γ e₂ e₃ e₄ y) = vertexOf y from eq_vertexOf (label_leaf h _)]
    exact off_of_mem h hc v hy

/-- The clusters, for each parent choice. -/
def hier (k : Bool) : Finset (Finset (Fin 5)) :=
  if k then {univ, {4}, {3, 2, 1, 0}, {3}, {2, 1, 0}, {2}, {1, 0}, {1}, {0}} else {univ, {4, 3, 2, 1}, {4}, {3, 2, 1}, {3}, {2, 1}, {2}, {1}, {0}}

omit h in
theorem clusterOf_mem_hier (k : Bool) (v : V₀) : clusterOf k v ∈ hier k := by
  rcases v with _ | (_ | a | (_ | a | (_ | a | (_ | a | a)))) | b | _ | d
  any_goals first
    | exact a.elim
    | exact b.elim
    | (cases k <;> simp only [clusterOf] <;> decide)

omit h in
theorem exists_clusterOf (k : Bool) {B : Finset (Fin 5)} (hB : B ∈ hier k) : B.Nonempty ∧ ∃ v : V₀, clusterOf k v = B := by
  have hn : ∀ B ∈ hier k, B.Nonempty := by cases k <;> decide
  refine ⟨hn B hB, ?_⟩
  cases k
  · simp only [hier, Bool.false_eq_true, ↓reduceIte, mem_insert, mem_singleton] at hB
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.top, rfl⟩
    · exact ⟨.side₁ .node, rfl⟩
    · exact ⟨.side₁ (.pendant ()), rfl⟩
    · exact ⟨.side₁ (.rest .node), rfl⟩
    · exact ⟨.side₁ (.rest (.pendant ())), rfl⟩
    · exact ⟨.side₁ (.rest (.rest .node)), rfl⟩
    · exact ⟨.side₁ (.rest (.rest (.pendant ()))), rfl⟩
    · exact ⟨.side₁ (.rest (.rest (.rest .node))), rfl⟩
    · exact ⟨.hyb, rfl⟩
  · simp only [hier, ↓reduceIte, mem_insert, mem_singleton] at hB
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.top, rfl⟩
    · exact ⟨.side₁ (.pendant ()), rfl⟩
    · exact ⟨.side₁ (.rest .node), rfl⟩
    · exact ⟨.side₁ (.rest (.pendant ())), rfl⟩
    · exact ⟨.side₁ (.rest (.rest .node)), rfl⟩
    · exact ⟨.side₁ (.rest (.rest (.pendant ()))), rfl⟩
    · exact ⟨.side₁ (.rest (.rest (.rest .node))), rfl⟩
    · exact ⟨.side₁ (.rest (.rest (.rest (.pendant ())))), rfl⟩
    · exact ⟨.hyb, rfl⟩

theorem displayedClusters_eq (hc : (c ⟨.hyb, hyb_ne_root h⟩).val.1 = kept k) :
    (rooted h).displayedClusters c = (hier k).image (image (taxon γ e₂ e₃ e₄)) := by
  ext A
  rw [mem_displayedClusters, mem_image]
  constructor
  · rintro ⟨_, v, rfl⟩
    exact ⟨clusterOf k v, clusterOf_mem_hier k v, (displayedCluster_eq h hc v).symm⟩
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨hne, v, rfl⟩ := exists_clusterOf k hB
    exact ⟨(hne.image _).ne_empty, v, displayedCluster_eq h hc v⟩

omit h in
/-- Taking sides commutes with relabelling the taxa. -/
theorem unroot_image (H : Finset (Finset (Fin 5))) : unroot (H.image (image (taxon γ e₂ e₃ e₄))) = treeOn γ e₂ e₃ e₄ (unroot H) := by
  have hi := taxon_injective (γ := γ) (e₂ := e₂) (e₃ := e₃) (e₄ := e₄)
  have hs := taxon_surjective (γ := γ) (e₂ := e₂) (e₃ := e₃) (e₄ := e₄)
  have huniv : image (taxon γ e₂ e₃ e₄) (univ : Finset (Fin 5)) = univ := image_univ_of_surjective hs
  have hcompl : ∀ B : Finset (Fin 5), (B.image (taxon γ e₂ e₃ e₄))ᶜ = Bᶜ.image (taxon γ e₂ e₃ e₄) := fun B => by
    ext x
    obtain ⟨y, rfl⟩ := hs x
    rw [mem_compl, hi.mem_finset_image, hi.mem_finset_image, mem_compl]
  have he : (H.image (image (taxon γ e₂ e₃ e₄))).erase univ = (H.erase univ).image (image (taxon γ e₂ e₃ e₄)) := by
    rw [image_erase (image_injective hi), huniv]
  unfold unroot treeOn
  rw [he, image_union, image_image, image_image]
  congr 1
  exact image_congr fun B _ => hcompl B

theorem displayedSides_eq (hc : (c ⟨.hyb, hyb_ne_root h⟩).val.1 = kept k) :
    (rooted h).displayedSides c = treeOn γ e₂ e₃ e₄ (unroot (hier k)) := by
  rw [displayedSides, displayedClusters_eq h hc, unroot_image]

omit h in
theorem unroot_hier_true : unroot (hier true) = unroot hT₁ := by
  unfold hier hT₁ unroot
  decide

omit h in
theorem unroot_hier_false : unroot (hier false) = unroot hT₂ := by
  unfold hier hT₂ unroot
  decide

/-- A parent choice keeps one arc into the hybrid node. -/
theorem exists_kept (c : (rooted h).ParentChoice) : ∃ k, (c ⟨.hyb, hyb_ne_root h⟩).val.1 = kept k := by
  have hm : (c ⟨.hyb, hyb_ne_root h⟩).val.1 ∈ arcs := adj_mem (c ⟨.hyb, hyb_ne_root h⟩).val.2
  rcases arcs_hyb hm (c ⟨.hyb, hyb_ne_root h⟩).2 with h₁ | h₁
  · exact ⟨false, h₁⟩
  · exact ⟨true, h₁⟩

/-- The parent choice that keeps a given arc into the hybrid node. -/
theorem exists_choice (k : Bool) : ∃ c : (rooted h).ParentChoice, (c ⟨.hyb, hyb_ne_root h⟩).val.1 = kept k := by
  have hex : ∀ v : {v : (net γ e₂ e₃ e₄).Vert // v ≠ (rooted h).root}, ∃ e, (rooted h).graph.target e = v.val := by
    rintro ⟨v, hv⟩
    rcases Relation.ReflTransGen.cases_tail ((isPhylogenetic_rooted h).root_reaches v) with h₁ | ⟨w, _, f, _, h₂⟩
    · exact absurd h₁ hv
    · exact ⟨f, h₂⟩
  have hk : (graph₀ γ e₂ e₃ e₄).Adj (kept k).1 (kept k).2 := by
    cases k
    · exact Or.inr rfl
    · rfl
  let arc : (net γ e₂ e₃ e₄).toGraph.Arc := ⟨kept k, hk⟩
  have harc : (rooted h).graph.target arc = (CycleVert.hyb : V₀) := by
    cases k <;> rfl
  have hex' : ∀ v : {v : (net γ e₂ e₃ e₄).Vert // v ≠ (rooted h).root}, ∃ e, (rooted h).graph.target e = v.val ∧ (v.val = (CycleVert.hyb : V₀) → e.1 = kept k) := by
    intro v
    by_cases hv : v.val = (CycleVert.hyb : V₀)
    · exact ⟨arc, harc.trans hv.symm, fun _ => rfl⟩
    · obtain ⟨e, he⟩ := hex v
      exact ⟨e, he, fun h₀ => absurd h₀ hv⟩
  choose f hf using hex'
  exact ⟨fun v => ⟨f v, (hf v).1⟩, (hf _).2 rfl⟩

end Choice

/-- **The displayed trees of the network are `T₁` and `T₂`.** -/
theorem displayed_trees (h : Params γ e₂ e₃ e₄) :
    (∀ c, (rooted h).displayedSides c = treeOn γ e₂ e₃ e₄ (unroot hT₁) ∨ (rooted h).displayedSides c = treeOn γ e₂ e₃ e₄ (unroot hT₂)) ∧
      (∃ c, (rooted h).displayedSides c = treeOn γ e₂ e₃ e₄ (unroot hT₁)) ∧ ∃ c, (rooted h).displayedSides c = treeOn γ e₂ e₃ e₄ (unroot hT₂) := by
  refine ⟨fun c => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := exists_kept h c
    rw [displayedSides_eq h hk]
    cases k
    · exact Or.inr (by rw [unroot_hier_false])
    · exact Or.inl (by rw [unroot_hier_true])
  · obtain ⟨c, hc⟩ := exists_choice h true
    exact ⟨c, by rw [displayedSides_eq h hc, unroot_hier_true]⟩
  · obtain ⟨c, hc⟩ := exists_choice h false
    exact ⟨c, by rw [displayedSides_eq h hc, unroot_hier_false]⟩

/-- **Theorem 1, for every displayed tree**: `S` has a higher expected ASTRAL score than each tree the network displays, so that no displayed tree is an optimum of ASTRAL's objective. -/
theorem theorem1_displayed (h : Params γ e₂ e₃ e₄) (h6 : 1 - Real.exp (-e₂) > γ / (1 - γ) * (1 - Real.exp (-e₃) * Real.exp (-e₄)))
    (h7 : 1 - Real.exp (-e₃) < min (γ / (2 - γ) * (1 - Real.exp (-e₄))) ((1 - γ) / (1 + γ) * (1 - Real.exp (-e₂)))) (c : (rooted h).ParentChoice) :
    quartetSupport (nmscCF (rooted h) (net γ e₂ e₃ e₄).metricData 0) ((rooted h).displayedSides c) < score h (unroot hS) := by
  obtain ⟨h₁, h₂, _⟩ := theorem1 h h6 h7
  rcases (displayed_trees h).1 c with hc | hc
  · rw [hc]
    exact h₁
  · rw [hc]
    exact h₂

end Main

end External.DinhBanos2025
