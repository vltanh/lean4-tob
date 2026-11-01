module

public import AllmanEtAl2023.DeletedNetwork

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the 2-blob step of the proof of Theorem 1 (b)

"If there are any 2-blobs on `𝒩⁻`, set all edge lengths in `𝒩⁺` that give rise to them equal to 0, with hybrid parameters arbitrary. Doing so, we have effectively removed these blobs, and may thus assume there are no 2-blobs in `𝒩⁻`."

The paper gives no reason. Here, for a set `S` of nodes with a top `r` (`IsContractible`):

* `contractNetwork`: the network with `S` collapsed onto `r`;
* `nmscCF_contractNetwork`: at length `0` on the arcs into `S`, with any inheritance there, the `CF`s are those of the contracted network. On a history of nonzero weight no lineages coalesce in `S`, so the forest arriving at `r` is what enters `S` from below (`arriving_contract`), and the arcs into `S` sum out to a constant (`sum_prod_zero`);
* `contracted`: suppress the nodes of in- and out-degree 1, and remove a stem, as for `AllmanEtAl2023.deleted`;
* `contracted_isBinaryNetwork`, `nmscCF_contracted`, `exists_contracted_lift`, `inducedCutSplit_of_contracted`: it is a network of Definition 1, with the same `CF`s, parameters that lift at length `0` on `S`, and no new cut-edge split;
* `exists_isContractible_of_cutDegree_two`: a 2-blob of `𝒩⁻` gives such a set. Either it is below the LSA, with one arc in at its top and one arc out (`exists_isContractible_of_not_top`), or the LSA is its top, which `𝒩⁻` suppresses, and two arcs leave it (`isContractible_of_top`).

The paper removes all 2-blobs at once. Here it is one at a time, in the induction of `AllmanEtAl2023.Theorem1b`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*}

/-! ### The network -/

section Contract

/-- The nodes `S ∪ {r}` of `𝒩⁺` give rise to a blob with top `r`, that may be collapsed onto `r`: everything entering `S` comes from `S ∪ {r}`, `r` reaches `S`, and at most two arcs leave. -/
structure IsContractible (N : RootedNetwork V E X) (r : V) (S : Set V) : Prop where
  top : r ∉ S
  nonempty : S.Nonempty
  root : N.root ∉ S
  no_leaf : ∀ x, N.leaf x ∉ S
  parent : ∀ e, N.graph.target e ∈ S → N.graph.source e ∈ S ∨ N.graph.source e = r
  reaches : ∀ v ∈ S, N.graph.Reaches r v
  indegree_top : N.graph.indegree r ≤ 1
  exits : {e | (N.graph.source e ∈ S ∨ N.graph.source e = r) ∧ N.graph.target e ∉ S}.ncard ≤ 2

variable {N : RootedNetwork V E X} {r : V} {S : Set V}

/-- The map of nodes: `S` goes to `r`. -/
def contractMap (hr : r ∉ S) (v : V) : {v // v ∉ S} := if h : v ∈ S then ⟨r, hr⟩ else ⟨v, h⟩

theorem contractMap_of_mem (hr : r ∉ S) {v : V} (h : v ∈ S) : contractMap hr v = ⟨r, hr⟩ := dite_eq_left h

theorem contractMap_of_notMem (hr : r ∉ S) {v : V} (h : v ∉ S) : contractMap hr v = ⟨v, h⟩ := dite_eq_right h

/-- **The network with the blob contracted.** -/
def contractNetwork (hC : IsContractible N r S) : RootedNetwork {v // v ∉ S} {e // N.graph.target e ∉ S} X where
  graph :=
    { source := fun e => contractMap hC.top (N.graph.source e.1)
      target := fun e => ⟨N.graph.target e.1, e.2⟩ }
  root := ⟨N.root, hC.root⟩
  leaf x := ⟨N.leaf x, hC.no_leaf x⟩

variable (hC : IsContractible N r S)

include hC

theorem contractNetwork_source_val (e : {e // N.graph.target e ∉ S}) (h : N.graph.source e.1 ∉ S) : ((contractNetwork hC).graph.source e).1 = N.graph.source e.1 :=
  congrArg Subtype.val (contractMap_of_notMem hC.top h)

theorem contractNetwork_source_of_mem (e : {e // N.graph.target e ∉ S}) (h : N.graph.source e.1 ∈ S) : (contractNetwork hC).graph.source e = ⟨r, hC.top⟩ :=
  contractMap_of_mem hC.top h

/-- The top of the blob reaches the node an arc of the contraction leaves in the network. -/
theorem reaches_source_contractNetwork (e : {e // N.graph.target e ∉ S}) : N.graph.Reaches ((contractNetwork hC).graph.source e).1 (N.graph.source e.1) := by
  by_cases h : N.graph.source e.1 ∈ S
  · rw [contractNetwork_source_of_mem hC e h]
    exact hC.reaches _ h
  · rw [contractNetwork_source_val hC e h]
    exact .refl

/-- A step of the contraction is a path of the network. -/
theorem transGen_of_adj_contractNetwork {u w : {v // v ∉ S}} (h : (contractNetwork hC).graph.Adj u w) : Relation.TransGen N.graph.Adj u.1 w.1 := by
  obtain ⟨e, rfl, rfl⟩ := h
  exact Relation.TransGen.tail' (reaches_source_contractNetwork hC e) ⟨e.1, rfl, rfl⟩

/-- A nonempty path of the contraction is one of the network. -/
theorem transGen_of_transGen_contractNetwork {u w : {v // v ∉ S}} (h : Relation.TransGen (contractNetwork hC).graph.Adj u w) : Relation.TransGen N.graph.Adj u.1 w.1 := by
  induction h with
  | single h => exact transGen_of_adj_contractNetwork hC h
  | tail _ h ih => exact ih.trans (transGen_of_adj_contractNetwork hC h)

/-- A path of the contraction is a path of the network. -/
theorem reaches_of_reaches_contractNetwork {u w : {v // v ∉ S}} (h : (contractNetwork hC).graph.Reaches u w) : N.graph.Reaches u.1 w.1 := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact ih.trans (transGen_of_adj_contractNetwork hC hab).to_reflTransGen

/-- A path of the network maps to a path of the contraction. -/
theorem reaches_contractMap {u w : V} (h : N.graph.Reaches u w) : (contractNetwork hC).graph.Reaches (contractMap hC.top u) (contractMap hC.top w) := by
  induction h with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    obtain ⟨e, rfl, rfl⟩ := hab
    by_cases ht : N.graph.target e ∈ S
    · have : contractMap hC.top (N.graph.target e) = contractMap hC.top (N.graph.source e) := by
        rw [contractMap_of_mem hC.top ht]
        rcases hC.parent e ht with h | h
        · rw [contractMap_of_mem hC.top h]
        · simp only [h]
          rw [contractMap_of_notMem hC.top hC.top]
      rwa [this]
    · rw [contractMap_of_notMem hC.top ht]
      exact ih.tail ⟨⟨e, ht⟩, rfl, rfl⟩

/-- **In-degrees are unchanged.** -/
theorem indegree_contractNetwork (v : {v // v ∉ S}) : (contractNetwork hC).graph.indegree v = N.graph.indegree v.1 := by
  unfold DirectedMultigraph.indegree
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext e
  constructor
  · rintro ⟨e', he', rfl⟩
    exact congrArg Subtype.val he'
  · intro he
    exact ⟨⟨e, fun h => v.2 ((show N.graph.target e = v.1 from he) ▸ h)⟩, Subtype.ext he, rfl⟩

/-- **Out-degrees are unchanged, away from the top.** -/
theorem outdegree_contractNetwork {v : {v // v ∉ S}} (hv : v.1 ≠ r) : (contractNetwork hC).graph.outdegree v = N.graph.outdegree v.1 := by
  unfold DirectedMultigraph.outdegree
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext e
  constructor
  · rintro ⟨e', he', rfl⟩
    have he'' : (contractNetwork hC).graph.source e' = v := he'
    by_cases h : N.graph.source e'.1 ∈ S
    · rw [contractNetwork_source_of_mem hC e' h] at he''
      exact absurd (congrArg Subtype.val he'').symm hv
    · have := contractNetwork_source_val hC e' h
      rw [he''] at this
      exact this.symm
  · intro he
    have he' : N.graph.source e = v.1 := he
    have ht : N.graph.target e ∉ S := fun h => by
      rcases hC.parent e h with h | h
      · exact v.2 (he' ▸ h)
      · exact hv (he'.symm.trans h)
    refine ⟨⟨e, ht⟩, Subtype.ext ?_, rfl⟩
    exact (contractNetwork_source_val hC ⟨e, ht⟩ (he' ▸ v.2)).trans he'

/-- **The out-degree of the top is the number of arcs leaving the blob.** -/
theorem outdegree_contractNetwork_top : (contractNetwork hC).graph.outdegree ⟨r, hC.top⟩ = {e | (N.graph.source e ∈ S ∨ N.graph.source e = r) ∧ N.graph.target e ∉ S}.ncard := by
  unfold DirectedMultigraph.outdegree
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext e
  constructor
  · rintro ⟨e', he', rfl⟩
    refine ⟨?_, e'.2⟩
    have he'' : (contractNetwork hC).graph.source e' = ⟨r, hC.top⟩ := he'
    by_cases h : N.graph.source e'.1 ∈ S
    · exact Or.inl h
    · right
      have := contractNetwork_source_val hC e' h
      rw [he''] at this
      exact this.symm
  · rintro ⟨h, ht⟩
    refine ⟨⟨e, ht⟩, ?_, rfl⟩
    rcases h with h | h
    · exact contractNetwork_source_of_mem hC ⟨e, ht⟩ h
    · refine Subtype.ext ((contractNetwork_source_val hC ⟨e, ht⟩ (h ▸ hC.top)).trans h)

/-- The top of the blob is not a taxon. -/
theorem top_ne_leaf (hN : N.IsPhylogenetic) (x : X) : r ≠ N.leaf x := by
  have : Finite E := hN.finite_arcs
  rintro rfl
  obtain ⟨v, hv⟩ := hC.nonempty
  rcases Relation.ReflTransGen.cases_head (hC.reaches v hv) with h | ⟨c, ⟨f, hf, -⟩, -⟩
  · exact hC.top (h ▸ hv)
  · exact (N.graph.outdegree_eq_zero_iff _).mp ((hN.leaves _).mpr ⟨x, rfl⟩) f hf

/-- **The contraction is a phylogenetic network.** -/
theorem contractNetwork_isPhylogenetic (hN : N.IsPhylogenetic) : (contractNetwork hC).IsPhylogenetic := by
  have : Finite V := hN.finite_vertices
  have : Finite E := hN.finite_arcs
  refine ⟨inferInstance, inferInstance, hN.finite_taxa, ?_, fun v => ?_, ?_, fun v hv => ?_, fun x y h => ?_, fun x => ?_, fun v => ?_⟩
  · exact fun v hv => hN.acyclic v.1 (transGen_of_transGen_contractNetwork hC hv)
  · have := reaches_contractMap hC (hN.root_reaches v.1)
    rwa [contractMap_of_notMem hC.top hC.root, contractMap_of_notMem hC.top v.2] at this
  · rw [indegree_contractNetwork]
    exact hN.root_indegree
  · rw [indegree_contractNetwork]
    exact hN.nonroot_indegree _ fun h => hv (Subtype.ext h)
  · exact hN.leaf_injective (congrArg Subtype.val h)
  · rw [indegree_contractNetwork]
    exact hN.leaf_indegree x
  · by_cases hvr : v.1 = r
    · have hv : v = ⟨r, hC.top⟩ := Subtype.ext hvr
      subst hv
      constructor
      · intro h0
        -- a path from the top to a taxon leaves the blob
        rw [outdegree_contractNetwork_top, Set.ncard_eq_zero (Set.toFinite _)] at h0
        obtain ⟨x, hx⟩ := exists_reaches_leaf hN r
        obtain ⟨f, hf, hf'⟩ := Bridges.exists_exit_of_reaches (S := {v | v ∈ S ∨ v = r}) hx (Or.inr rfl) (by
          rintro (h | h)
          · exact hC.no_leaf x h
          · exact top_ne_leaf hC hN x h.symm)
        have : f ∈ {e | (N.graph.source e ∈ S ∨ N.graph.source e = r) ∧ N.graph.target e ∉ S} := ⟨hf, fun h => hf' (Or.inl h)⟩
        rw [h0] at this
        exact absurd this (Set.notMem_empty _)
      · rintro ⟨x, hx⟩
        exact absurd (congrArg Subtype.val hx).symm (top_ne_leaf hC hN x)
    · rw [outdegree_contractNetwork hC hvr, hN.leaves]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, Subtype.ext hx⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, congrArg Subtype.val hx⟩

/-- **A cut edge of the contraction is one of the network**, with the same taxa on its side. The arcs into `S` have both ends in one class of `contractMap`. -/
theorem hasCutSplit_of_contractNetwork {A : Set X} (h : (contractNetwork hC).HasCutSplit A) : N.HasCutSplit A := by
  obtain ⟨e, W, hW, rfl⟩ := h
  have hmap : ∀ f (hf : N.graph.target f ∉ S), (N.graph.Crosses f (contractMap hC.top ⁻¹' W) ↔ (contractNetwork hC).graph.Crosses ⟨f, hf⟩ W) := by
    intro f hf
    have ht : contractMap hC.top (N.graph.target f) = ⟨N.graph.target f, hf⟩ := contractMap_of_notMem hC.top hf
    simp only [DirectedMultigraph.Crosses, Set.mem_preimage, ht]
    rfl
  refine ⟨e.1, contractMap hC.top ⁻¹' W, fun f => ?_, ?_⟩
  · by_cases hf : N.graph.target f ∈ S
    · constructor
      · intro hcr
        have hs : contractMap hC.top (N.graph.source f) = contractMap hC.top (N.graph.target f) := by
          rw [contractMap_of_mem hC.top hf]
          rcases hC.parent f hf with h | h
          · rw [contractMap_of_mem hC.top h]
          · simp only [h]
            rw [contractMap_of_notMem hC.top hC.top]
        simp only [DirectedMultigraph.Crosses, Set.mem_preimage, hs] at hcr
        tauto
      · rintro rfl
        exact absurd hf e.2
    · rw [hmap f hf, hW ⟨f, hf⟩]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · ext x
    have : contractMap hC.top (N.leaf x) = ⟨N.leaf x, hC.no_leaf x⟩ := contractMap_of_notMem hC.top (hC.no_leaf x)
    simp only [Set.mem_preimage, this]
    rfl

end Contract

/-! ### The concordance factors -/

section Sum

variable [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

/-- **A vertex entered only by arcs of length `0` sums out**, against anything that does not see those arcs. -/
theorem sum_step_zero (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ) {v : V} (hv : v ≠ N.root) (hlen : ∀ e, N.graph.target e = v → θ.length e = 0) (hloop : ∀ e, N.graph.target e = v → N.graph.source e ≠ v)
    (inj : V → Finset (Finset X)) (G : (E → Finset (Finset X)) → (E → Finset (Finset X)) → ℝ)
    (hGb : ∀ bot top y, G (overwrite (arcsInto N v) bot y) top = G bot top) (hGt : ∀ bot top y, G bot (overwrite (arcsInto N v) top y) = G bot top) :
    ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)) ^ 2 * ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X), vertexWeight N θ ρ inj v bot top * G bot top =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X), G bot top := by
  set A := arcsInto N v with hA
  set B : ℝ := (Fintype.card (Finset (Finset X)) : ℝ) with hB
  have harr : ∀ top y : E → Finset (Finset X), arriving N inj (overwrite A top y) v = arriving N inj top v := fun top y =>
    arriving_congr rfl fun e he => overwrite_of_notMem (fun hm => hloop e (mem_arcsInto.1 hm) he) _ _
  -- summing out the tops
  have htop : ∀ bot : E → Finset (Finset X), B ^ #A * ∑ top : E → Finset (Finset X), vertexWeight N θ ρ inj v bot top * G bot top =
      ∑ top : E → Finset (Finset X), allocationFactor N θ ρ (arriving N inj top v) v bot * G bot top := by
    intro bot
    have := card_pow_mul_sum_mul_eq A (fun top : E → Finset (Finset X) => allocationFactor N θ ρ (arriving N inj top v) v bot * G bot top)
      (fun top => ∏ e ∈ A, kingmanTransition (θ.length e) (bot e) (top e))
      (fun top y => by simp only [harr, hGt])
      (fun top _ => by
        have hsimp : ∀ y : E → Finset (Finset X), ∏ e ∈ A, kingmanTransition (θ.length e) (bot e) (overwrite A top y e) = ∏ e ∈ A, kingmanTransition (θ.length e) (bot e) (y e) := fun y =>
          prod_congr rfl fun e he => by rw [overwrite_of_mem he]
        simp only [hsimp]
        refine sum_prod_of_sum_eq_one A _ fun e he => ?_
        rw [hlen e (mem_arcsInto.1 he), kingmanTransition_zero]
        simp [Matrix.one_apply])
    rw [← this]
    congr 1
    refine sum_congr rfl fun top _ => ?_
    unfold vertexWeight
    ring
  -- summing out the bottoms
  have hbot : ∀ top : E → Finset (Finset X), B ^ #A * ∑ bot : E → Finset (Finset X), allocationFactor N θ ρ (arriving N inj top v) v bot * G bot top =
      ∑ bot : E → Finset (Finset X), G bot top := by
    intro top
    have := card_pow_mul_sum_mul_eq A (fun bot : E → Finset (Finset X) => G bot top) (fun bot => allocationFactor N θ ρ (arriving N inj top v) v bot)
      (fun bot y => hGb bot top y)
      (fun bot _ => by
        have hsimp : ∀ y : E → Finset (Finset X), allocationFactor N θ ρ (arriving N inj top v) v (overwrite A bot y) = allocationFactor N θ ρ (arriving N inj top v) v y := fun y =>
          allocationFactor_congr fun e he => overwrite_of_mem (mem_arcsInto.2 he) _ _
        simp only [hsimp]
        exact sum_allocationFactor_weak hN hθ hρ hv _)
    rw [← this]
    congr 1
    exact sum_congr rfl fun bot _ => mul_comm _ _
  calc (B ^ #A) ^ 2 * ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X), vertexWeight N θ ρ inj v bot top * G bot top
      = B ^ #A * ∑ bot : E → Finset (Finset X), (B ^ #A * ∑ top : E → Finset (Finset X), vertexWeight N θ ρ inj v bot top * G bot top) := by
        rw [← mul_sum, ← mul_assoc, sq]
    _ = B ^ #A * ∑ top : E → Finset (Finset X), ∑ bot : E → Finset (Finset X), allocationFactor N θ ρ (arriving N inj top v) v bot * G bot top := by
        simp only [htop]
        rw [sum_comm]
    _ = ∑ top : E → Finset (Finset X), ∑ bot : E → Finset (Finset X), G bot top := by
        rw [mul_sum]
        exact sum_congr rfl fun top _ => hbot top
    _ = _ := sum_comm

/-- **The vertices of a set whose entering arcs have length `0` sum out**, against anything that does not see those arcs. -/
theorem sum_prod_zero [Finite V] (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ) (T : Finset V) (hroot : N.root ∉ T) (hlen : ∀ e, N.graph.target e ∈ T → θ.length e = 0)
    (inj : V → Finset (Finset X)) (Φ : (E → Finset (Finset X)) → (E → Finset (Finset X)) → ℝ)
    (hΦ : ∀ bot bot' top top' : E → Finset (Finset X), (∀ e, N.graph.target e ∉ T → bot e = bot' e) → (∀ e, N.graph.target e ∉ T → top e = top' e) → Φ bot top = Φ bot' top') :
    ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(univ.filter fun e => N.graph.target e ∈ T)) ^ 2 *
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X), (∏ v ∈ T, vertexWeight N θ ρ inj v bot top) * Φ bot top =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X), Φ bot top := by
  induction T using Finset.strongInduction with
  | H T ih =>
    rcases T.eq_empty_or_nonempty with rfl | hne
    · simp
    · have : IsTrans V (Relation.TransGen N.graph.Adj) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
      have : Std.Irrefl (Relation.TransGen N.graph.Adj) := ⟨hN.acyclic⟩
      have hwf : WellFounded (Relation.TransGen N.graph.Adj) := Finite.wellFounded_of_trans_of_irrefl _
      -- a highest vertex of `T`
      obtain ⟨v, hv, hmin⟩ := hwf.has_min (T : Set V) hne
      have hv' : v ∈ T := hv
      have hnp : ∀ e, N.graph.target e = v → N.graph.source e ∉ T := fun e he hs => hmin _ hs (Relation.TransGen.single ⟨e, rfl, he⟩)
      have hE : ∀ e, N.graph.target e ∈ T.erase v → e ∉ arcsInto N v := fun e he hm => (mem_erase.1 he).1 (mem_arcsInto.1 hm)
      have hEs : ∀ e, N.graph.source e ∈ T.erase v → e ∉ arcsInto N v := fun e he hm => hnp e (mem_arcsInto.1 hm) (mem_erase.1 he).2
      have hAT : ∀ e, N.graph.target e ∉ T → e ∉ arcsInto N v := fun e he hm => he (mem_arcsInto.1 hm ▸ hv')
      have hih := ih (T.erase v) (erase_ssubset hv') (fun h => hroot (mem_of_mem_erase h)) (fun e he => hlen e (mem_of_mem_erase he))
        fun bot bot' top top' hb ht => hΦ bot bot' top top' (fun e he => hb e fun h => he (mem_of_mem_erase h)) fun e he => ht e fun h => he (mem_of_mem_erase h)
      have hstep := sum_step_zero hN hθ hρ (v := v) (fun h => hroot (h ▸ hv')) (fun e he => hlen e (he ▸ hv')) (fun e he hs => hnp e he (hs ▸ hv')) inj
        (fun bot top => (∏ u ∈ T.erase v, vertexWeight N θ ρ inj u bot top) * Φ bot top)
        (fun bot top y => by
          congr 1
          · refine prod_congr rfl fun u hu => vertexWeight_congr rfl (fun e he => ?_) (fun _ _ => rfl) fun _ _ => rfl
            exact overwrite_of_notMem (hE e (he ▸ hu)) _ _
          · exact hΦ _ _ _ _ (fun e he => overwrite_of_notMem (hAT e he) _ _) fun _ _ => rfl)
        (fun bot top y => by
          congr 1
          · refine prod_congr rfl fun u hu => vertexWeight_congr rfl (fun _ _ => rfl) (fun e he => ?_) fun e he => ?_
            · exact overwrite_of_notMem (hE e (he ▸ hu)) _ _
            · exact overwrite_of_notMem (hEs e (he ▸ hu)) _ _
          · exact hΦ _ _ _ _ (fun _ _ => rfl) fun e he => overwrite_of_notMem (hAT e he) _ _)
      rw [← hih, ← hstep]
      have hcard : #(univ.filter fun e => N.graph.target e ∈ T) = #(univ.filter fun e => N.graph.target e ∈ T.erase v) + #(arcsInto N v) := by
        have hdis : Disjoint (univ.filter fun e => N.graph.target e ∈ T.erase v) (arcsInto N v) := disjoint_left.2 fun e he he' => hE e (mem_filter.1 he).2 he'
        rw [← card_union_of_disjoint hdis]
        congr 1
        ext e
        simp only [mem_filter, mem_univ, true_and, mem_union, mem_arcsInto, mem_erase]
        constructor
        · intro he
          by_cases h : N.graph.target e = v
          · exact Or.inr h
          · exact Or.inl ⟨h, he⟩
        · rintro (⟨-, he⟩ | he)
          · exact he
          · exact he ▸ hv'
      rw [hcard, pow_add, mul_pow, mul_assoc]
      congr 2
      simp only [← mul_assoc]
      refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
      rw [← mul_prod_erase T _ hv', mul_assoc]

end Sum

section Restrict

/-- A sum over functions of what they do on a subtype. -/
theorem sum_restrict {ι β : Type*} [Fintype ι] [Fintype β] (p : ι → Prop) [Fintype {i // p i}] (A : Finset ι) (hA : ∀ i, i ∈ A ↔ ¬ p i) (h : ({i // p i} → β) → ℝ) :
    ∑ f : ι → β, h (fun i => f i.1) = (Fintype.card β : ℝ) ^ #A * ∑ f : {i // p i} → β, h f := by
  rw [← (Equiv.piEquivPiSubtypeProd p fun _ => β).symm.sum_comp, Fintype.sum_prod_type_right]
  have hconst : ∀ (g : {i // ¬ p i} → β), ∑ f : {i // p i} → β, h (fun i => (Equiv.piEquivPiSubtypeProd p fun _ => β).symm (f, g) i.1) = ∑ f : {i // p i} → β, h f := by
    intro g
    refine sum_congr rfl fun f _ => congrArg h (funext fun i => ?_)
    simp [Equiv.piEquivPiSubtypeProd, i.2]
  simp only [hconst, sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun]
  push_cast
  rw [Fintype.card_of_subtype A hA]

end Restrict

section CF

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} {r : V} {S : Set V} {θ : MetricData E} {ρ : ℝ}

/-- The parameters of the contraction: those of the same arcs. -/
def contractParams (S : Set V) (θ : MetricData E) : MetricData {e // N.graph.target e ∉ S} where
  length e := θ.length e.1
  inheritance e := θ.inheritance e.1

omit [Fintype V] in
/-- What a factor at a node of the blob says of a history of nonzero weight: at length `0` no lineages coalesce, so the forest arriving at the node goes up its arcs as it is. -/
theorem forests_of_vertexWeight_ne_zero {inj : V → Finset (Finset X)} {bot top : E → Finset (Finset X)} {v : V} (hw : vertexWeight N θ ρ inj v bot top ≠ 0) (hlen : ∀ e, N.graph.target e = v → θ.length e = 0) :
    (∀ e, N.graph.target e = v → top e ⊆ arriving N inj top v) ∧ ∀ A ∈ arriving N inj top v, ∃ e, N.graph.target e = v ∧ A ∈ top e := by
  have hAF := left_ne_zero_of_mul hw
  have hK := right_ne_zero_of_mul hw
  have hbt : ∀ e, N.graph.target e = v → top e = bot e := fun e he => by
    have h := prod_ne_zero_iff.1 hK e (mem_arcsInto.2 he)
    rw [hlen e he, kingmanTransition_zero] at h
    by_contra hne
    exact h (Matrix.one_apply_ne (Ne.symm hne))
  obtain ⟨a, ha⟩ := exists_assignment hAF
  refine ⟨fun e he => ?_, fun A hA => ?_⟩
  · rw [hbt e he, ha ⟨e, he⟩]
    exact filter_subset _ _
  · obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
    refine ⟨(a ⟨R, hR⟩).1, (a ⟨R, hR⟩).2, ?_⟩
    rw [hbt _ (a ⟨R, hR⟩).2, ha (a ⟨R, hR⟩), mem_forestBelow]
    exact ⟨hA, R, mem_image.2 ⟨⟨R, hR⟩, mem_filter.2 ⟨mem_univ _, rfl⟩, rfl⟩, hAR⟩

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- An arc of the contraction leaves a node other than the top exactly when it does in the network. -/
theorem source_contractNetwork_iff (hC : IsContractible N r S) {v : {v // v ∉ S}} (hv : v.1 ≠ r) (e : {e // N.graph.target e ∉ S}) :
    (contractNetwork hC).graph.source e = v ↔ N.graph.source e.1 = v.1 := by
  by_cases h : N.graph.source e.1 ∈ S
  · rw [contractNetwork_source_of_mem hC e h]
    constructor
    · intro h'
      exact absurd (congrArg Subtype.val h').symm hv
    · intro h'
      exact absurd (h' ▸ h) v.2
  · rw [← contractNetwork_source_val hC e h]
    exact Subtype.ext_iff

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- An arc leaving a node other than the top does not enter the blob. -/
theorem target_notMem_of_source (hC : IsContractible N r S) {v : {v // v ∉ S}} (hv : v.1 ≠ r) {e : E} (he : N.graph.source e = v.1) : N.graph.target e ∉ S := fun h => by
  rcases hC.parent e h with h | h
  · exact v.2 (he ▸ h)
  · exact hv (he.symm.trans h)

variable [Fintype {e // N.graph.target e ∉ S}] (hC : IsContractible N r S)

omit [Fintype V] [Fintype E] [Fintype {e // N.graph.target e ∉ S}] in
/-- The contraction has the same lineages at the same nodes. -/
theorem taxaInj_contractNetwork (hC : IsContractible N r S) (v : {v // v ∉ S}) : taxaInj (contractNetwork hC) univ v = taxaInj N univ v.1 := by
  unfold taxaInj
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact Subtype.ext_iff

omit [Fintype V] in
/-- Away from the top of the blob, a node sees the same forest. -/
theorem arriving_contract_of_ne (top : E → Finset (Finset X)) {v : {v // v ∉ S}} (hv : v.1 ≠ r) :
    arriving (contractNetwork hC) (taxaInj (contractNetwork hC) univ) (fun e => top e.1) v = arriving N (taxaInj N univ) top v.1 := by
  unfold arriving
  rw [taxaInj_contractNetwork]
  congr 1
  ext A
  simp only [mem_biUnion, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨e, he, hA⟩
    exact ⟨e.1, (source_contractNetwork_iff hC hv e).mp he, hA⟩
  · rintro ⟨e, he, hA⟩
    exact ⟨⟨e, target_notMem_of_source hC hv he⟩, (source_contractNetwork_iff hC hv _).mpr he, hA⟩

omit [Fintype V] in
/-- **On a history of nonzero weight on the blob, the forest arriving at its top is what enters the blob from below**: the arcs into `S` carry forests up as they are. -/
theorem arriving_contract (hN : N.IsPhylogenetic) (top : E → Finset (Finset X)) {bot : E → Finset (Finset X)} (hlen : ∀ e, N.graph.target e ∈ S → θ.length e = 0)
    (hw : ∀ v ∈ S, vertexWeight N θ ρ (taxaInj N univ) v bot top ≠ 0) :
    arriving (contractNetwork hC) (taxaInj (contractNetwork hC) univ) (fun e => top e.1) ⟨r, hC.top⟩ = arriving N (taxaInj N univ) top r := by
  have : Finite V := hN.finite_vertices
  have hf := fun v (hv : v ∈ S) => forests_of_vertexWeight_ne_zero (hw v hv) fun e he => hlen e (he ▸ hv)
  have hempty : ∀ u ∈ S, taxaInj N univ u = ∅ := fun u hu => by
    unfold taxaInj
    rw [image_eq_empty, filter_eq_empty_iff]
    rintro x - ⟨-, hx⟩
    exact hC.no_leaf x (hx ▸ hu)
  have hmem : ∀ A, A ∈ arriving (contractNetwork hC) (taxaInj (contractNetwork hC) univ) (fun e => top e.1) ⟨r, hC.top⟩ ↔
      A ∈ taxaInj N univ r ∨ ∃ e, (N.graph.source e ∈ S ∨ N.graph.source e = r) ∧ N.graph.target e ∉ S ∧ A ∈ top e := by
    intro A
    unfold arriving
    rw [taxaInj_contractNetwork, mem_union]
    refine or_congr_right ?_
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨e, he, hA⟩
      refine ⟨e.1, ?_, e.2, hA⟩
      by_cases h : N.graph.source e.1 ∈ S
      · exact Or.inl h
      · right
        have := contractNetwork_source_val hC e h
        rw [he] at this
        exact this.symm
    · rintro ⟨e, h, ht, hA⟩
      refine ⟨⟨e, ht⟩, ?_, hA⟩
      rcases h with h | h
      · exact contractNetwork_source_of_mem hC ⟨e, ht⟩ h
      · exact Subtype.ext ((contractNetwork_source_val hC ⟨e, ht⟩ (h ▸ hC.top)).trans h)
  have hup : ∀ (u : V) (A : Finset X) (e : E), N.graph.source e = u → A ∈ top e → A ∈ arriving N (taxaInj N univ) top u := fun u A e he hA => by
    unfold arriving
    exact mem_union_right _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, he⟩, hA⟩)
  ext A
  rw [hmem]
  constructor
  · -- what enters the blob from below is at its top
    have : IsTrans V (Relation.TransGen N.graph.Adj) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
    have : Std.Irrefl (Relation.TransGen N.graph.Adj) := ⟨hN.acyclic⟩
    have hwf : WellFounded (Relation.TransGen N.graph.Adj) := Finite.wellFounded_of_trans_of_irrefl _
    have key : ∀ u, (u ∈ S ∨ u = r) → ∀ A ∈ arriving N (taxaInj N univ) top u, A ∈ arriving N (taxaInj N univ) top r := by
      intro u
      refine hwf.induction (C := fun u => (u ∈ S ∨ u = r) → ∀ A ∈ arriving N (taxaInj N univ) top u, A ∈ arriving N (taxaInj N univ) top r) u fun u ih hu A hA => ?_
      rcases hu with hu | rfl
      · obtain ⟨e, he, hAe⟩ := (hf u hu).2 A hA
        have hp := hC.parent e (he ▸ hu)
        exact ih _ (Relation.TransGen.single ⟨e, rfl, he⟩) hp A (hup _ A e rfl hAe)
      · exact hA
    rintro (hA | ⟨e, hs, -, hA⟩)
    · unfold arriving
      exact mem_union_left _ hA
    · exact key _ hs A (hup _ A e rfl hA)
  · -- what is at its top entered the blob from below
    have : IsTrans V (Function.swap (Relation.TransGen N.graph.Adj)) := ⟨fun _ _ _ h h' => h'.trans h⟩
    have : Std.Irrefl (Function.swap (Relation.TransGen N.graph.Adj)) := ⟨hN.acyclic⟩
    have hwf : WellFounded (Function.swap (Relation.TransGen N.graph.Adj)) := Finite.wellFounded_of_trans_of_irrefl _
    have key : ∀ u, (u ∈ S ∨ u = r) → ∀ A ∈ arriving N (taxaInj N univ) top u, A ∈ taxaInj N univ r ∨ ∃ e, (N.graph.source e ∈ S ∨ N.graph.source e = r) ∧ N.graph.target e ∉ S ∧ A ∈ top e := by
      intro u
      refine hwf.induction (C := fun u => (u ∈ S ∨ u = r) → ∀ A ∈ arriving N (taxaInj N univ) top u, A ∈ taxaInj N univ r ∨ ∃ e, (N.graph.source e ∈ S ∨ N.graph.source e = r) ∧ N.graph.target e ∉ S ∧ A ∈ top e) u fun u ih hu A hA => ?_
      unfold arriving at hA
      rcases mem_union.1 hA with hA | hA
      · rcases hu with hu | rfl
        · rw [hempty u hu] at hA
          exact absurd hA (notMem_empty _)
        · exact Or.inl hA
      · obtain ⟨e, he, hAe⟩ := mem_biUnion.1 hA
        have he' : N.graph.source e = u := (mem_filter.1 he).2
        by_cases ht : N.graph.target e ∈ S
        · exact ih _ (Relation.TransGen.single ⟨e, he', rfl⟩) (Or.inl ht) A ((hf _ ht).1 e rfl hAe)
        · exact Or.inr ⟨e, he' ▸ hu, ht, hAe⟩
    exact key r (Or.inr rfl) A

omit [Fintype V] in
/-- The factor of a node at the contraction, when the node sees the same forest. -/
theorem vertexWeight_contract (bot top : E → Finset (Finset X)) (v : {v // v ∉ S})
    (harr : arriving (contractNetwork hC) (taxaInj (contractNetwork hC) univ) (fun e => top e.1) v = arriving N (taxaInj N univ) top v.1) :
    vertexWeight (contractNetwork hC) (contractParams S θ) ρ (taxaInj (contractNetwork hC) univ) v (fun e => bot e.1) (fun e => top e.1) = vertexWeight N θ ρ (taxaInj N univ) v.1 bot top := by
  unfold vertexWeight
  rw [harr]
  congr 1
  · let σ : {e // N.graph.target e = v.1} ≃ {e // (contractNetwork hC).graph.target e = v} :=
      { toFun := fun e => ⟨⟨e.1, fun h => v.2 (e.2 ▸ h)⟩, Subtype.ext e.2⟩
        invFun := fun e => ⟨e.1.1, congrArg Subtype.val e.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact allocationFactor_eq_of_equiv σ (Equiv.refl _) (fun _ => rfl) fun _ _ => Iff.rfl
  · refine Finset.prod_bij (fun e _ => e.1) (fun e he => mem_arcsInto.2 (congrArg Subtype.val (mem_arcsInto.1 he))) (fun _ _ _ _ h => Subtype.ext h) (fun e he => ?_) fun _ _ => rfl
    have he' : N.graph.target e = v.1 := mem_arcsInto.1 he
    exact ⟨⟨e, fun h => v.2 (he' ▸ h)⟩, mem_arcsInto.2 (Subtype.ext he'), rfl⟩

/-- **A history of the network is a history of the blob and one of the contraction.** -/
theorem injWeight_contract (hN : N.IsPhylogenetic) [Fintype {v // v ∉ S}] (hlen : ∀ e, N.graph.target e ∈ S → θ.length e = 0) (ψ : Finset (Finset X) → ℝ) (bot top : E → Finset (Finset X)) :
    injWeight N θ ρ (taxaInj N univ) bot top * ψ (arriving N (taxaInj N univ) top N.root) =
      (∏ v ∈ univ.filter (· ∈ S), vertexWeight N θ ρ (taxaInj N univ) v bot top) *
        (injWeight (contractNetwork hC) (contractParams S θ) ρ (taxaInj (contractNetwork hC) univ) (fun e => bot e.1) (fun e => top e.1) *
          ψ (arriving (contractNetwork hC) (taxaInj (contractNetwork hC) univ) (fun e => top e.1) (contractNetwork hC).root)) := by
  have hsub : (univ.filter (· ∈ S)) ⊆ univ.erase N.root := fun v hv =>
    mem_erase.2 ⟨fun h => hC.root (h ▸ (mem_filter.1 hv).2), mem_univ _⟩
  have hsplit : injWeight N θ ρ (taxaInj N univ) bot top = (∏ v ∈ univ.erase N.root \ univ.filter (· ∈ S), vertexWeight N θ ρ (taxaInj N univ) v bot top) * ∏ v ∈ univ.filter (· ∈ S), vertexWeight N θ ρ (taxaInj N univ) v bot top :=
    (prod_sdiff hsub).symm
  rw [hsplit]
  by_cases h0 : ∏ v ∈ univ.filter (· ∈ S), vertexWeight N θ ρ (taxaInj N univ) v bot top = 0
  · rw [h0]
    ring
  have hw : ∀ v ∈ S, vertexWeight N θ ρ (taxaInj N univ) v bot top ≠ 0 := fun v hv => prod_ne_zero_iff.1 h0 v (mem_filter.2 ⟨mem_univ _, hv⟩)
  have harr : ∀ v : {v // v ∉ S}, arriving (contractNetwork hC) (taxaInj (contractNetwork hC) univ) (fun e => top e.1) v = arriving N (taxaInj N univ) top v.1 := by
    intro v
    by_cases hv : v.1 = r
    · have : v = ⟨r, hC.top⟩ := Subtype.ext hv
      rw [this]
      exact arriving_contract hC hN top hlen hw
    · exact arriving_contract_of_ne hC top hv
  have hrest : (∏ v ∈ univ.erase N.root \ univ.filter (· ∈ S), vertexWeight N θ ρ (taxaInj N univ) v bot top) =
      injWeight (contractNetwork hC) (contractParams S θ) ρ (taxaInj (contractNetwork hC) univ) (fun e => bot e.1) (fun e => top e.1) := by
    unfold injWeight
    refine (Finset.prod_bij (fun v _ => v.1) (fun v hv => ?_) (fun _ _ _ _ h => Subtype.ext h) (fun v hv => ?_) fun v _ => vertexWeight_contract hC bot top v (harr v)).symm
    · exact mem_sdiff.2 ⟨mem_erase.2 ⟨fun h => ne_of_mem_erase' hv (Subtype.ext h), mem_univ _⟩, fun h => v.2 (mem_filter.1 h).2⟩
    · obtain ⟨h₁, h₂⟩ := mem_sdiff.1 hv
      have hvS : v ∉ S := fun h => h₂ (mem_filter.2 ⟨mem_univ _, h⟩)
      exact ⟨⟨v, hvS⟩, mem_erase_of_ne' (fun h => (mem_erase.1 h₁).1 (congrArg Subtype.val h)) (mem_univ _), rfl⟩
  rw [hrest, harr (contractNetwork hC).root]
  change _ = _ * (_ * ψ (arriving N (taxaInj N univ) top N.root))
  ring

/-- **"Doing so, we have effectively removed these blobs"**: at length `0` on the arcs into `S`, with any inheritance there, the distribution of gene trees is that of the contraction. -/
theorem injDist_contract (hN : N.IsPhylogenetic) [Fintype {v // v ∉ S}] (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ) (hlen : ∀ e, N.graph.target e ∈ S → θ.length e = 0) (G : Finset (Finset X)) :
    injDist (contractNetwork hC) (contractParams S θ) ρ (taxaInj (contractNetwork hC) univ) G = injDist N θ ρ (taxaInj N univ) G := by
  set T : Finset V := univ.filter (· ∈ S) with hT
  set term : ({e // N.graph.target e ∉ S} → Finset (Finset X)) → ({e // N.graph.target e ∉ S} → Finset (Finset X)) → ℝ := fun b t =>
    injWeight (contractNetwork hC) (contractParams S θ) ρ (taxaInj (contractNetwork hC) univ) b t * kingmanAbsorption (arriving (contractNetwork hC) (taxaInj (contractNetwork hC) univ) t (contractNetwork hC).root) G with hterm
  have hB : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
  have hstep := sum_prod_zero (θ := θ) (ρ := ρ) hN hθ hρ T (fun h => hC.root (mem_filter.1 h).2) (fun e he => hlen e (mem_filter.1 he).2) (taxaInj N univ)
    (fun bot top => term (fun e => bot e.1) (fun e => top e.1))
    (fun bot bot' top top' hb ht => by
      have hS : ∀ e : {e // N.graph.target e ∉ S}, N.graph.target e.1 ∉ T := fun e he => e.2 (mem_filter.1 he).2
      simp only [funext fun e : {e // N.graph.target e ∉ S} => hb e.1 (hS e), funext fun e : {e // N.graph.target e ∉ S} => ht e.1 (hS e)])
  have hcomp : ∀ e, e ∈ (univ.filter fun e => N.graph.target e ∈ T) ↔ ¬ (N.graph.target e ∉ S) := fun e => by
    simp [hT]
  have hsum : ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X), term (fun e => bot e.1) (fun e => top e.1) =
      ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(univ.filter fun e => N.graph.target e ∈ T)) ^ 2 * ∑ b : {e // N.graph.target e ∉ S} → Finset (Finset X), ∑ t : {e // N.graph.target e ∉ S} → Finset (Finset X), term b t := by
    have h₁ : ∀ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X), term (fun e => bot e.1) (fun e => top e.1) =
        (Fintype.card (Finset (Finset X)) : ℝ) ^ #(univ.filter fun e => N.graph.target e ∈ T) * ∑ t, term (fun e => bot e.1) t := fun bot =>
      sum_restrict (fun e => N.graph.target e ∉ S) _ hcomp fun t => term (fun e => bot e.1) t
    simp only [h₁]
    have h₂ := sum_restrict (β := Finset (Finset X)) (fun e => N.graph.target e ∉ S) _ hcomp fun b => (Fintype.card (Finset (Finset X)) : ℝ) ^ #(univ.filter fun e => N.graph.target e ∈ T) * ∑ t, term b t
    rw [h₂, sq, mul_assoc, ← mul_sum]
  have hcancel := hstep.trans hsum
  have hne : ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(univ.filter fun e => N.graph.target e ∈ T)) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hB.ne')
  have hE := mul_left_cancel₀ hne hcancel
  unfold injDist
  refine Eq.trans ?_ (Eq.trans hE.symm ?_)
  · exact sum_congr_instance _ _ _ _ fun b => sum_congr_instance _ _ _ _ fun t => rfl
  · refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
    exact (injWeight_contract hC hN hlen (fun F => kingmanAbsorption F G) bot top).symm

/-- The gene trees of the contraction. -/
theorem geneTreeDist_contract (hN : N.IsPhylogenetic) [Fintype {v // v ∉ S}] (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ) (hlen : ∀ e, N.graph.target e ∈ S → θ.length e = 0) (G : Finset (Finset X)) :
    geneTreeDist (contractNetwork hC) (contractParams S θ) ρ G = geneTreeDist N θ ρ G := by
  rw [geneTreeDist_eq_injDist (contractNetwork_isPhylogenetic hC hN), geneTreeDist_eq_injDist hN]
  exact injDist_contract hC hN hθ hρ hlen G

/-- **"Doing so, we have effectively removed these blobs"**: at length `0` on the arcs into `S`, with any inheritance there, the `CF`s are those of the contraction. -/
theorem nmscCF_contractNetwork (hN : N.IsPhylogenetic) [Fintype {v // v ∉ S}] (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ) (hlen : ∀ e, N.graph.target e ∈ S → θ.length e = 0) (s : QuartetTree X) :
    nmscCF (contractNetwork hC) (contractParams S θ) ρ s = nmscCF N θ ρ s := by
  unfold nmscCF
  simp only [geneTreeDist_contract hC hN hθ hρ hlen]

end CF

/-! ### The network `𝒩⁺` with the 2-blob removed -/

section Contracted

variable {N : RootedNetwork V E X} {r : V} {S : Set V}

/-- The contraction with its vertices of in- and out-degree 1 suppressed. -/
abbrev contractSuppressed (hN : N.IsPhylogenetic) (hC : IsContractible N r S) := (contractNetwork hC).suppress (contractNetwork_isPhylogenetic hC hN)

theorem contractSuppressed_isPhylogenetic (hN : N.IsPhylogenetic) (hC : IsContractible N r S) : (contractSuppressed hN hC).IsPhylogenetic := suppress_isPhylogenetic _

variable [Nontrivial X]

/-- **The network with a 2-blob removed**: contract, suppress the nodes of degree 2, and remove a stem. -/
def contracted (hN : N.IsPhylogenetic) (hC : IsContractible N r S) := removeStem (contractSuppressed hN hC) (contractSuppressed_isPhylogenetic hN hC)

theorem contracted_isPhylogenetic (hN : N.IsPhylogenetic) (hC : IsContractible N r S) : (contracted hN hC).IsPhylogenetic := removeStem_isPhylogenetic _

/-- **The network with a 2-blob removed is a network of Definition 1.** -/
theorem contracted_isBinaryNetwork (hN : IsBinaryNetwork N) (hC : IsContractible N r S) : IsBinaryNetwork (contracted hN.isPhylogenetic hC) := by
  have hP := hN.isPhylogenetic
  have hB := hN.isBinary
  have : Finite E := hP.finite_arcs
  have hR := contractNetwork_isPhylogenetic hC hP
  have : Fintype E := Fintype.ofFinite E
  have : Fintype {e // N.graph.target e ∉ S} := Fintype.ofFinite _
  refine isBinaryNetwork_suppressStem hR ?_ fun v hv hnc h0 => ?_
  · by_cases hrr : N.root = r
    · have hroot : (contractNetwork hC).root = ⟨r, hC.top⟩ := Subtype.ext hrr
      rw [hroot, outdegree_contractNetwork_top]
      exact hC.exits
    · rw [outdegree_contractNetwork hC hrr]
      exact hB.1.le
  · have hv1 : v.1 ≠ N.root := fun h => hv (Subtype.ext h)
    have hin₁ := indegree_contractNetwork hC v
    have h1 := hR.nonroot_indegree _ hv
    have hnc' : ¬ ((contractNetwork hC).graph.indegree v = 1 ∧ (contractNetwork hC).graph.outdegree v = 1) := hnc
    by_cases hvr : v.1 = r
    · have hv' : v = ⟨r, hC.top⟩ := Subtype.ext hvr
      have h₁ := hC.indegree_top
      have h₂ := hC.exits
      have h₃ := outdegree_contractNetwork_top hC
      rw [← hv'] at h₃
      rw [hvr] at hin₁
      omega
    · have hout₁ := outdegree_contractNetwork hC hvr
      have h3 := hB.2 v.1 hv1 (by omega)
      omega

/-- **The cut-edge splits of the network with a 2-blob removed are cut-edge splits of the network**, on four taxa. -/
theorem inducedCutSplit_of_contracted [Fintype X] [DecidableEq X] (hN : N.IsPhylogenetic) (hC : IsContractible N r S) (hcard : Fintype.card X = 4) {s : QuartetTree X} (h : InducedCutSplit (contracted hN hC) s) : InducedCutSplit N s := by
  have hst : s.taxa = Finset.univ := Finset.eq_univ_of_card _ (s.card_taxa.trans hcard.symm)
  obtain ⟨B, hB, hc⟩ := h
  have h2 := s.card_of_mem hB
  have h2' := s.card_of_mem (s.sdiff_mem hB)
  rw [hst] at h2'
  obtain ⟨y, hy⟩ : (Finset.univ \ B).Nonempty := Finset.card_pos.mp (by omega)
  have h₁ : (B : Set X).Nonempty := Finset.card_pos.mp (by omega)
  have h₂ : (B : Set X)ᶜ.Nonempty := ⟨y, by simpa using hy⟩
  refine ⟨B, hB, ?_⟩
  rw [hst, Finset.coe_univ, ← hasCutSplit_iff_hasCutSplitOn_univ (contracted_isPhylogenetic hN hC)] at hc
  have hc₁ := (Bridges.removeStem_hasCutSplit_iff (contractSuppressed_isPhylogenetic hN hC) h₁ h₂).mp hc
  have hc₂ := (suppress_hasCutSplit_iff (contractNetwork_isPhylogenetic hC hN) _).mp hc₁
  rw [hst, Finset.coe_univ, ← hasCutSplit_iff_hasCutSplitOn_univ hN]
  exact hasCutSplit_of_contractNetwork hC hc₂

variable [Fintype E]

/-- **The map of parameters to the network with a 2-blob removed**: restrict, add lengths along a suppressed path, and forget the stem. -/
def contractedParams (hN : N.IsPhylogenetic) (hC : IsContractible N r S) (θ : MetricData E) : MetricData {e // ¬ (HasStem (contractSuppressed hN hC) ∧ (contractSuppressed hN hC).graph.source e = (contractSuppressed hN hC).root)} :=
  have : Fintype {e // N.graph.target e ∉ S} := Fintype.ofFinite _
  stemMetric (contractSuppressed hN hC) ((contractNetwork hC).suppressMetric (contractParams S θ))

omit [Nontrivial X] in
/-- The parameters of the contraction are normalized. -/
theorem isNormalized_contractParams [Fintype {e // N.graph.target e ∉ S}] (hC : IsContractible N r S) {θ : MetricData E} (hθ : N.IsNormalized θ) : (contractNetwork hC).IsNormalized (contractParams S θ) := by
  refine ⟨fun e he => hθ.1 e.1 ?_, fun v hv => ?_⟩
  · change N.graph.indegree (N.graph.target e.1) = 1
    rw [← he]
    exact (indegree_contractNetwork hC ((contractNetwork hC).graph.target e)).symm
  · rw [indegree_contractNetwork] at hv
    refine Eq.trans ?_ (hθ.2 v.1 hv)
    refine sum_of_injective' _ _ Subtype.val Subtype.val_injective _ _ (fun e he => ?_) fun e => ?_
    · have : N.graph.target e ≠ v.1 := fun ht => he ⟨⟨e, fun h => v.2 (ht ▸ h)⟩, rfl⟩
      exact ite_eq_right this
    · exact ite_congr' _ _ Subtype.ext_iff rfl rfl

variable {θ : MetricData E} {ρ : ℝ}

/-- **"Set all edge lengths in `𝒩⁺` that give rise to them equal to 0, with hybrid parameters arbitrary. Doing so, we have effectively removed these blobs"**: at length `0` on the arcs into `S`, the `CF`s of `𝒩⁺` are those of the network with the blob removed. -/
theorem nmscCF_contracted [Fintype V] [Fintype X] [DecidableEq X] (hN : N.IsPhylogenetic) (hC : IsContractible N r S) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ) (hlen : ∀ e, N.graph.target e ∈ S → θ.length e = 0)
    [Fintype {v // ¬ (HasStem (contractSuppressed hN hC) ∧ v = (contractSuppressed hN hC).root)}]
    [Fintype {e // ¬ (HasStem (contractSuppressed hN hC) ∧ (contractSuppressed hN hC).graph.source e = (contractSuppressed hN hC).root)}] (s : QuartetTree X) :
    nmscCF (contracted hN hC) (contractedParams hN hC θ) ρ s = nmscCF N θ ρ s := by
  let _ : Fintype {v // v ∉ S} := Fintype.ofFinite _
  let _ : Fintype {e // N.graph.target e ∉ S} := Fintype.ofFinite _
  let _ : Fintype {v // ¬ (contractNetwork hC).IsChainVertex v} := Fintype.ofFinite _
  let _ : Fintype {e // ¬ (contractNetwork hC).IsChainVertex ((contractNetwork hC).graph.source e)} := Fintype.ofFinite _
  have hR := contractNetwork_isPhylogenetic hC hN
  have hθ₁ := isNormalized_contractParams hC hθ
  exact (nmscCF_suppressStem hR hθ₁ hρ s).trans (nmscCF_contractNetwork hC hN hθ hρ hlen s)

omit [Nontrivial X] in
/-- Step 1 of the map of parameters is onto valid boundary parameters: length `0` on the arcs into `S`, and any inheritance there; here the same for each parent. -/
theorem exists_contract_lift [Fintype {e // N.graph.target e ∉ S}] (hC : IsContractible N r S) {θ' : MetricData {e // N.graph.target e ∉ S}} (hθ' : (contractNetwork hC).IsWeakMetric θ') :
    ∃ θ, N.IsWeakMetric θ ∧ (∀ e, N.graph.target e ∈ S → θ.length e = 0) ∧ contractParams S θ = θ' := by
  let θ : MetricData E :=
    { length := fun f => if h : N.graph.target f ∉ S then θ'.length ⟨f, h⟩ else 0
      inheritance := fun f => if h : N.graph.target f ∉ S then θ'.inheritance ⟨f, h⟩ else ((N.graph.indegree (N.graph.target f) : ℝ))⁻¹ }
  have hl₁ : ∀ f (h : N.graph.target f ∉ S), θ.length f = θ'.length ⟨f, h⟩ := fun f h => dite_eq_left h
  have hl₂ : ∀ f, N.graph.target f ∈ S → θ.length f = 0 := fun f h => dite_eq_right (not_not.mpr h)
  have hi₁ : ∀ f (h : N.graph.target f ∉ S), θ.inheritance f = θ'.inheritance ⟨f, h⟩ := fun f h => dite_eq_left h
  have hi₂ : ∀ f, N.graph.target f ∈ S → θ.inheritance f = ((N.graph.indegree (N.graph.target f) : ℝ))⁻¹ := fun f h => dite_eq_right (not_not.mpr h)
  refine ⟨θ, ⟨fun f => ?_, fun f hf => ?_, fun f hf => ?_, fun v hv => ?_⟩, hl₂, ?_⟩
  · by_cases h : N.graph.target f ∉ S
    · rw [hl₁ f h]
      exact hθ'.1 _
    · rw [hl₂ f (not_not.mp h)]
  · by_cases h : N.graph.target f ∉ S
    · rw [hi₁ f h]
      refine hθ'.2.1 _ ?_
      change 2 ≤ (contractNetwork hC).graph.indegree ⟨N.graph.target f, h⟩
      rw [indegree_contractNetwork]
      exact hf
    · rw [hi₂ f (not_not.mp h)]
      positivity
  · by_cases h : N.graph.target f ∉ S
    · rw [hi₁ f h]
      refine hθ'.2.2.1 _ ?_
      change (contractNetwork hC).graph.indegree ⟨N.graph.target f, h⟩ = 1
      rw [indegree_contractNetwork]
      exact hf
    · rw [hi₂ f (not_not.mp h), show N.graph.indegree (N.graph.target f) = 1 from hf]
      simp
  · by_cases h : v ∈ S
    · have hsum : ∑ e, (if N.graph.target e = v then θ.inheritance e else 0) = ∑ e, (if N.graph.target e = v then ((N.graph.indegree v : ℝ))⁻¹ else 0) := by
        refine sum_congr rfl fun e _ => ?_
        by_cases he : N.graph.target e = v
        · rw [ite_eq_left he, ite_eq_left he, hi₂ e (he ▸ h), he]
        · rw [ite_eq_right he, ite_eq_right he]
      have h0 : (N.graph.indegree v : ℝ) ≠ 0 := by
        have : N.graph.indegree v ≠ 0 := by omega
        exact_mod_cast this
      rw [hsum, ← Finset.sum_filter, sum_const, nsmul_eq_mul]
      change ((#(arcsInto N v) : ℕ) : ℝ) * _ = 1
      rw [← indegree_eq_card]
      exact mul_inv_cancel₀ h0
    · refine Eq.trans (sum_of_injective' _ _ Subtype.val Subtype.val_injective _ _ (fun e he => ?_) fun e => ?_).symm (hθ'.2.2.2 ⟨v, h⟩ (by rw [indegree_contractNetwork]; exact hv))
      · have : N.graph.target e ≠ v := fun ht => he ⟨⟨e, fun hs => h (ht ▸ hs)⟩, rfl⟩
        exact ite_eq_right this
      · exact ite_congr' _ _ Subtype.ext_iff (hi₁ e.1 e.2).symm rfl
  · have h₁ : (contractParams S θ).length = θ'.length := funext fun e => hl₁ e.1 e.2
    have h₂ : (contractParams S θ).inheritance = θ'.inheritance := funext fun e => hi₁ e.1 e.2
    cases hc : contractParams S θ with
    | mk l i =>
      cases θ' with
      | mk l' i' =>
        rw [hc] at h₁ h₂
        exact congrArg₂ MetricData.mk h₁ h₂

/-- **The map of parameters to the network with a 2-blob removed is onto valid boundary parameters**, at length `0` on the arcs into the blob, with hybrid parameters arbitrary. -/
theorem exists_contracted_lift (hN : N.IsPhylogenetic) (hC : IsContractible N r S)
    [Fintype {e // ¬ (HasStem (contractSuppressed hN hC) ∧ (contractSuppressed hN hC).graph.source e = (contractSuppressed hN hC).root)}]
    {θ' : MetricData {e // ¬ (HasStem (contractSuppressed hN hC) ∧ (contractSuppressed hN hC).graph.source e = (contractSuppressed hN hC).root)}}
    (hθ' : (contracted hN hC).IsWeakMetric θ') : ∃ θ, N.IsWeakMetric θ ∧ (∀ e, N.graph.target e ∈ S → θ.length e = 0) ∧ contractedParams hN hC θ = θ' := by
  let _ : Fintype {e // N.graph.target e ∉ S} := Fintype.ofFinite _
  let _ : Fintype {e // ¬ (contractNetwork hC).IsChainVertex ((contractNetwork hC).graph.source e)} := Fintype.ofFinite _
  obtain ⟨θ₁, hθ₁, h₁⟩ := exists_suppressStem_lift (contractNetwork_isPhylogenetic hC hN) hθ'
  obtain ⟨θ, hθ, h0, h₀⟩ := exists_contract_lift hC hθ₁
  refine ⟨θ, hθ, h0, ?_⟩
  change stemMetric (contractSuppressed hN hC) ((contractNetwork hC).suppressMetric (contractParams S θ)) = θ'
  rw [h₀, h₁]

end Contracted

/-! ### A 2-blob of `𝒩⁻` -/

section Extract

variable {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) (hX : Nontrivial X)

/-- An edge with exactly one end in a blob is a cut edge. -/
theorem mem_incidentCutEdges_iff {W F : Type*} {G : DirectedMultigraph W F} {b : G.BlobVertex} {f : F} : f ∈ incidentCutEdges G b ↔ IsIncidentToBlob G f b := by
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  by_contra hb
  have : blobOf G (G.source f) = blobOf G (G.target f) := Quotient.sound (Relation.ReflTransGen.single ⟨f, hb, Or.inl ⟨rfl, rfl⟩⟩)
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact h₂ (this ▸ h₁)
  · exact h₂ (this.symm ▸ h₁)

/-- The nodes of `𝒩⁺` of a blob of `𝒩⁻`. -/
def blobSet (b : (semidirected hN hX).graph.BlobVertex) : Set V :=
  {v | ∃ w : SemiV hN hX, w.1.1 = v ∧ blobOf (semidirected hN hX).graph w = b}

/-- The node of `𝒩⁻` that the chosen edge at the root of `𝒩⊕` leads to: edges at the root have it as their end in `𝒩⁻`. -/
def topNode : SemiV hN hX := ⟨(lsaPlus hN hX).graph.target (rootTreeArc hN hX), target_ne_root (lsaPlus_isPhylogenetic hN hX) _⟩

variable {hN hX}

theorem semi_source_of_eq (f : SemiE hN hX) (h : N.graph.source f.1.1 = lsaNode hN hX) : (semidirected hN hX).graph.source f = topNode hN hX :=
  dite_eq_left (Subtype.ext h : (lsaPlus hN hX).graph.source f.1 = (lsaPlus hN hX).root)

theorem semi_source_val_of_ne (f : SemiE hN hX) (h : N.graph.source f.1.1 ≠ lsaNode hN hX) : ((semidirected hN hX).graph.source f).1.1 = N.graph.source f.1.1 := by
  have h' : ¬ (lsaPlus hN hX).graph.source f.1 = (lsaPlus hN hX).root := fun h' => h (congrArg Subtype.val h')
  exact congrArg (fun z : SemiV hN hX => z.1.1) (dite_eq_right h' : (semidirected hN hX).graph.source f = ⟨(lsaPlus hN hX).graph.source f.1, h'⟩)

theorem blobOf_target_eq_iff {b : (semidirected hN hX).graph.BlobVertex} (f : SemiE hN hX) :
    blobOf (semidirected hN hX).graph ((semidirected hN hX).graph.target f) = b ↔ N.graph.target f.1.1 ∈ blobSet hN hX b := by
  refine ⟨fun h => ⟨_, rfl, h⟩, ?_⟩
  rintro ⟨w, hw, h⟩
  have : w = (semidirected hN hX).graph.target f := Subtype.ext (Subtype.ext hw)
  rwa [← this]

theorem blobOf_source_eq_iff {b : (semidirected hN hX).graph.BlobVertex} (f : SemiE hN hX) (hs : N.graph.source f.1.1 ≠ lsaNode hN hX) :
    blobOf (semidirected hN hX).graph ((semidirected hN hX).graph.source f) = b ↔ N.graph.source f.1.1 ∈ blobSet hN hX b := by
  refine ⟨fun h => ⟨_, semi_source_val_of_ne f hs, h⟩, ?_⟩
  rintro ⟨w, hw, h⟩
  have : w = (semidirected hN hX).graph.source f := Subtype.ext (Subtype.ext (hw.trans (semi_source_val_of_ne f hs).symm))
  rwa [← this]

theorem reaches_of_mem_blobSet {b : (semidirected hN hX).graph.BlobVertex} {v : V} (h : v ∈ blobSet hN hX b) : N.graph.Reaches (lsaNode hN hX) v ∧ v ≠ lsaNode hN hX := by
  obtain ⟨w, rfl, -⟩ := h
  exact ⟨w.1.2.1, fun h' => w.2 (Subtype.ext h')⟩

/-- An arc into a node strictly below the LSA comes from the LSA or below it. -/
theorem reaches_source_of_target {e : E} (hlt : N.graph.Reaches (lsaNode hN hX) (N.graph.target e)) (hne : N.graph.target e ≠ lsaNode hN hX) : N.graph.Reaches (lsaNode hN hX) (N.graph.source e) := by
  by_contra hs
  obtain ⟨x, hx⟩ := exists_reaches_leaf hN.isPhylogenetic (N.graph.target e)
  exact not_reaches_leaf_of_isStableAncestor hN.isPhylogenetic (lsa_spec hN.isPhylogenetic Set.univ Set.univ_nonempty).1 hlt hne hs (Set.mem_univ x) hx

theorem exists_semiArc {e : E} (hs : N.graph.Reaches (lsaNode hN hX) (N.graph.source e)) (hne : e ≠ (rootTreeArc hN hX).1) : ∃ f : SemiE hN hX, f.1.1 = e :=
  ⟨⟨⟨e, hs, mem_ancestralVertices_univ hN _⟩, fun h => hne (congrArg Subtype.val h)⟩, rfl⟩

theorem source_rootTreeArc' : N.graph.source (rootTreeArc hN hX).1 = lsaNode hN hX :=
  congrArg Subtype.val (rootTreeArc_spec hN hX).1

theorem leaf_notMem_blobSet {b : (semidirected hN hX).graph.BlobVertex} (h2 : cutDegree (semidirected hN hX).graph b = 2) (x : X) : N.leaf x ∉ blobSet hN hX b := by
  have : Finite E := hN.finite_arcs
  rintro ⟨w, hw, hb⟩
  have hwl : w = (semidirected hN hX).leaf x := Subtype.ext (Subtype.ext hw)
  have h1 := nodeDegree_treeOfBlobs_leaf hN hX x
  rw [← hwl, hb] at h1
  have hd : nodeDegree (semidirected hN hX).treeOfBlobs b = cutDegree (semidirected hN hX).graph b := nodeDegree_bridgeQuotient b
  omega

theorem root_notMem_blobSet {b : (semidirected hN hX).graph.BlobVertex} : N.root ∉ blobSet hN hX b := by
  intro h
  obtain ⟨hr, hne⟩ := reaches_of_mem_blobSet h
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, -, f, -, hf⟩
  · exact hne h
  · exact target_ne_root hN.isPhylogenetic f hf

/-- From the end `topNode`, directed paths of `𝒩⊕` are walks of `𝒩⁻`, off an edge not on them. -/
theorem walks_topNode (f : SemiE hN hX) {q : V} (hq : N.graph.Reaches (lsaNode hN hX) q) (hnr : ¬ N.graph.Reaches (N.graph.target f.1.1) q) (hne : q ≠ lsaNode hN hX) (w : SemiV hN hX) (hw : w.1.1 = q) :
    (semidirected hN hX).graph.Walks {f}ᶜ (topNode hN hX) w := by
  induction hq generalizing w with
  | refl => exact absurd rfl hne
  | @tail a c hla hac ih =>
    obtain ⟨g, rfl, rfl⟩ := hac
    have hgf : g ≠ f.1.1 := fun h => hnr (h ▸ .refl)
    by_cases hg0 : g = (rootTreeArc hN hX).1
    · have : w = topNode hN hX := by
        refine Subtype.ext (Subtype.ext (hw.trans ?_))
        rw [hg0]
        rfl
      rw [this]
      exact .refl
    obtain ⟨fg, rfl⟩ := exists_semiArc hla hg0
    have hwt : w = (semidirected hN hX).graph.target fg := Subtype.ext (Subtype.ext hw)
    have hstep : (semidirected hN hX).graph.AdjOn {f}ᶜ ((semidirected hN hX).graph.source fg) ((semidirected hN hX).graph.target fg) :=
      ⟨fg, fun h => hgf (congrArg (fun z : SemiE hN hX => z.1.1) h), Or.inl ⟨rfl, rfl⟩⟩
    rw [hwt]
    by_cases ha : N.graph.source fg.1.1 = lsaNode hN hX
    · rw [semi_source_of_eq fg ha] at hstep
      exact Relation.ReflTransGen.single hstep
    · exact (ih (fun h => hnr (h.tail ⟨fg.1.1, rfl, rfl⟩)) ha _ (semi_source_val_of_ne fg ha)).tail hstep

/-- **A 2-blob of `𝒩⁻` with the LSA at its top.** "All edge lengths in `𝒩⁺` that give rise to" it include the edges at the LSA, which `𝒩⁻` suppresses. -/
theorem isContractible_of_top {b : (semidirected hN hX).graph.BlobVertex} (h2 : cutDegree (semidirected hN hX).graph b = 2) (hc : blobOf (semidirected hN hX).graph (topNode hN hX) = b) :
    IsContractible N (lsaNode hN hX) (blobSet hN hX b) := by
  have hP := hN.isPhylogenetic
  have hB := hN.isBinary
  have : Finite V := hP.finite_vertices
  have : Finite E := hP.finite_arcs
  have htop : N.graph.target (rootTreeArc hN hX).1 ∈ blobSet hN hX b := ⟨topNode hN hX, rfl, hc⟩
  refine ⟨fun h => (reaches_of_mem_blobSet h).2 rfl, ⟨_, htop⟩, root_notMem_blobSet, leaf_notMem_blobSet h2, fun e he => ?_, fun v hv => (reaches_of_mem_blobSet hv).1, ?_, ?_⟩
  · obtain ⟨hlt, hne⟩ := reaches_of_mem_blobSet he
    by_cases hs : N.graph.source e = lsaNode hN hX
    · exact Or.inr hs
    · left
      by_contra hsU
      have he₀ : e ≠ (rootTreeArc hN hX).1 := fun h => hs (h ▸ source_rootTreeArc')
      obtain ⟨f, rfl⟩ := exists_semiArc (reaches_source_of_target hlt hne) he₀
      have hInc : f ∈ incidentCutEdges (semidirected hN hX).graph b :=
        mem_incidentCutEdges_iff.mpr (Or.inr ⟨(blobOf_target_eq_iff f).mpr he, fun h => hsU ((blobOf_source_eq_iff f hs).mp h)⟩)
      have hbr := hInc.1
      rw [DirectedMultigraph.isBridge_iff_not_walks_delete] at hbr
      refine hbr ?_
      -- from the source of `f` down from `topNode`, and across the blob to the target
      have hw₁ := walks_topNode f (reaches_source_of_target hlt hne) (fun h => hP.acyclic _ (Relation.TransGen.head' ⟨f.1.1, rfl, rfl⟩ h)) hs _ (semi_source_val_of_ne f hs)
      have hw₂ : (semidirected hN hX).graph.Walks {e | ¬ (semidirected hN hX).graph.underlying.IsBridge e} ((semidirected hN hX).graph.target f) (topNode hN hX) :=
        Quotient.exact (((blobOf_target_eq_iff f).mpr he).trans hc.symm)
      have hsubset : {e | ¬ (semidirected hN hX).graph.underlying.IsBridge e} ⊆ ({f}ᶜ : Set (SemiE hN hX)) := fun g hg hgf => hg ((show g = f from hgf) ▸ hInc.1)
      have hw₃ : (semidirected hN hX).graph.Walks {f}ᶜ ((semidirected hN hX).graph.target f) (topNode hN hX) :=
        DirectedMultigraph.walks_mono hsubset hw₂
      exact (DirectedMultigraph.walks_symm _ hw₁).trans (DirectedMultigraph.walks_symm _ hw₃)
  · have hout : 2 ≤ N.graph.outdegree (lsaNode hN hX) := by
      rw [← lsaPlus_outdegree_root hN hX]
      exact Set.ncard_le_ncard_of_injOn (f := Subtype.val) (t := {e | N.graph.source e = lsaNode hN hX}) (fun e he => congrArg Subtype.val he) (fun _ _ _ _ h => Subtype.ext h) (Set.toFinite _)
    by_cases hr : lsaNode hN hX = N.root
    · rw [hr, hP.root_indegree]
      omega
    · have := hB.2 _ hr (by omega)
      omega
  · have hsub : {e | (N.graph.source e ∈ blobSet hN hX b ∨ N.graph.source e = lsaNode hN hX) ∧ N.graph.target e ∉ blobSet hN hX b} ⊆ (fun f : SemiE hN hX => f.1.1) '' incidentCutEdges (semidirected hN hX).graph b := by
      rintro e ⟨hs, ht⟩
      have hsr : N.graph.Reaches (lsaNode hN hX) (N.graph.source e) := by
        rcases hs with h | h
        · exact (reaches_of_mem_blobSet h).1
        · exact h ▸ .refl
      have he₀ : e ≠ (rootTreeArc hN hX).1 := fun h => ht (h ▸ htop)
      obtain ⟨f, rfl⟩ := exists_semiArc hsr he₀
      refine ⟨f, mem_incidentCutEdges_iff.mpr (Or.inl ⟨?_, fun h => ht ((blobOf_target_eq_iff f).mp h)⟩), rfl⟩
      by_cases hsl : N.graph.source f.1.1 = lsaNode hN hX
      · rw [semi_source_of_eq f hsl]
        exact hc
      · exact (blobOf_source_eq_iff f hsl).mpr (hs.resolve_right hsl)
    calc _ ≤ ((fun f : SemiE hN hX => f.1.1) '' incidentCutEdges (semidirected hN hX).graph b).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (incidentCutEdges (semidirected hN hX).graph b).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = 2 := h2

/-- **A 2-blob of `𝒩⁻` below the LSA**, with a top in it. It has one arc in, at its top, and one arc out. -/
theorem exists_isContractible_of_not_top {b : (semidirected hN hX).graph.BlobVertex} (h2 : cutDegree (semidirected hN hX).graph b = 2) (hc : blobOf (semidirected hN hX).graph (topNode hN hX) ≠ b) :
    ∃ t, IsContractible N t (blobSet hN hX b \ {t}) := by
  have hP := hN.isPhylogenetic
  have hB := hN.isBinary
  have : Finite V := hP.finite_vertices
  have : Finite E := hP.finite_arcs
  set U := blobSet hN hX b with hU
  have hnt : N.graph.target (rootTreeArc hN hX).1 ∉ U := by
    rintro ⟨w, hw, hb⟩
    have : w = topNode hN hX := Subtype.ext (Subtype.ext hw)
    exact hc (this ▸ hb)
  -- an arc into `U` from outside, and one out of `U`, are incident
  have hmemI : ∀ e, N.graph.target e ∈ U → N.graph.source e ∉ U → ∃ f : SemiE hN hX, f.1.1 = e ∧ f ∈ incidentCutEdges (semidirected hN hX).graph b := by
    intro e ht hs
    obtain ⟨hlt, hne⟩ := reaches_of_mem_blobSet ht
    obtain ⟨f, rfl⟩ := exists_semiArc (reaches_source_of_target hlt hne) (fun h : e = (rootTreeArc hN hX).1 => hnt (h ▸ ht))
    refine ⟨f, rfl, mem_incidentCutEdges_iff.mpr (Or.inr ⟨(blobOf_target_eq_iff f).mpr ht, fun h => ?_⟩)⟩
    by_cases hsl : N.graph.source f.1.1 = lsaNode hN hX
    · rw [semi_source_of_eq f hsl] at h
      exact hc h
    · exact hs ((blobOf_source_eq_iff f hsl).mp h)
  have hmemO : ∀ e, N.graph.source e ∈ U → N.graph.target e ∉ U → ∃ f : SemiE hN hX, f.1.1 = e ∧ f ∈ incidentCutEdges (semidirected hN hX).graph b := by
    intro e hs ht
    obtain ⟨hlt, hne⟩ := reaches_of_mem_blobSet hs
    obtain ⟨f, rfl⟩ := exists_semiArc hlt (fun h : e = (rootTreeArc hN hX).1 => hne (h ▸ source_rootTreeArc'))
    exact ⟨f, rfl, mem_incidentCutEdges_iff.mpr (Or.inl ⟨(blobOf_source_eq_iff f hne).mpr hs, fun h => ht ((blobOf_target_eq_iff f).mp h)⟩)⟩
  have : IsTrans V (Relation.TransGen N.graph.Adj) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen N.graph.Adj) := ⟨hP.acyclic⟩
  have hwf : WellFounded (Relation.TransGen N.graph.Adj) := Finite.wellFounded_of_trans_of_irrefl _
  have hne : U.Nonempty := by
    obtain ⟨w, hw⟩ := Quotient.exists_rep b
    exact ⟨w.1.1, w, rfl, hw⟩
  -- the top
  obtain ⟨t, ht, hmin⟩ := hwf.has_min U hne
  have hmax : ∀ e, N.graph.target e = t → N.graph.source e ∉ U := fun e he hs => hmin _ hs (Relation.TransGen.single ⟨e, rfl, he⟩)
  have htr : t ≠ N.root := fun h => root_notMem_blobSet (h ▸ ht)
  -- its arc in, and an arc out
  obtain ⟨e₁, he₁⟩ := (N.graph.one_le_indegree_iff _).mp (hP.nonroot_indegree t htr)
  obtain ⟨f₁, rfl, hf₁⟩ := hmemI e₁ (he₁ ▸ ht) (hmax e₁ he₁)
  obtain ⟨x, hx⟩ := exists_reaches_leaf hP t
  obtain ⟨e₂, hs₂, ht₂⟩ := Bridges.exists_exit_of_reaches hx ht (leaf_notMem_blobSet h2 x)
  obtain ⟨f₂, rfl, hf₂⟩ := hmemO e₂ hs₂ ht₂
  have hne₁₂ : f₁ ≠ f₂ := fun h => ht₂ (by rw [← h, he₁]; exact ht)
  have huniq : ∀ f ∈ incidentCutEdges (semidirected hN hX).graph b, f = f₁ ∨ f = f₂ := by
    intro f hf
    by_contra hcon
    push Not at hcon
    have hgt : 2 < (incidentCutEdges (semidirected hN hX).graph b).ncard := (Set.two_lt_ncard_iff (Set.toFinite _)).mpr ⟨f₁, f₂, f, hf₁, hf₂, hf, hne₁₂, hcon.1.symm, hcon.2.symm⟩
    change 2 < cutDegree (semidirected hN hX).graph b at hgt
    omega
  -- what comes into `U` other than at the top comes from `U`
  have hpar : ∀ e, N.graph.target e ∈ U → N.graph.target e ≠ t → N.graph.source e ∈ U := by
    intro e h₁ h₃
    by_contra hs
    obtain ⟨f, rfl, hf⟩ := hmemI e h₁ hs
    rcases huniq f hf with rfl | rfl
    · exact h₃ he₁
    · exact ht₂ h₁
  have hreach : ∀ v, v ∈ U → N.graph.Reaches t v := by
    intro v
    refine hwf.induction (C := fun v => v ∈ U → N.graph.Reaches t v) v fun v ih hv => ?_
    by_cases hvt : v = t
    · exact hvt ▸ .refl
    · obtain ⟨e, he⟩ := (N.graph.one_le_indegree_iff _).mp (hP.nonroot_indegree v fun h => root_notMem_blobSet (h ▸ hv))
      have hs := hpar e (he ▸ hv) (he.trans_ne hvt)
      exact (ih _ (Relation.TransGen.single ⟨e, rfl, he⟩) hs).tail ⟨e, rfl, he⟩
  -- the only arc into the top
  have hin : ∀ e, N.graph.target e = t → e = f₁.1.1 := by
    intro e he
    obtain ⟨f, rfl, hf⟩ := hmemI e (he ▸ ht) (hmax e he)
    rcases huniq f hf with rfl | rfl
    · rfl
    · exact absurd (he ▸ ht) ht₂
  have hexit : ∀ e, N.graph.source e ∈ U → N.graph.target e ∉ U → e = f₂.1.1 := by
    intro e h₁ h₃
    obtain ⟨f, rfl, hf⟩ := hmemO e h₁ h₃
    rcases huniq f hf with rfl | rfl
    · exact absurd (he₁ ▸ ht) h₃
    · rfl
  have hindeg : N.graph.indegree t ≤ 1 := (Set.ncard_le_one (Set.toFinite _)).mpr fun a ha c hc' => (hin a ha).trans (hin c hc').symm
  refine ⟨t, fun h => h.2 rfl, ?_, fun h => root_notMem_blobSet h.1, fun x h => leaf_notMem_blobSet h2 x h.1, fun e he => ?_, fun v hv => hreach v hv.1, hindeg, ?_⟩
  · -- the blob is not a single node: the degrees
    by_contra hemp
    have hall : ∀ v ∈ U, v = t := fun v hv => by
      by_contra hvt
      exact hemp ⟨v, hv, hvt⟩
    have hout : N.graph.outdegree t ≤ 1 := by
      refine (Set.ncard_le_one (Set.toFinite _)).mpr fun a ha c hc' => ?_
      have hne' : ∀ e, N.graph.source e = t → N.graph.target e ∉ U := fun e he hte => source_ne_target hP e (he.trans (hall _ hte).symm)
      exact (hexit a (ha ▸ ht) (hne' a ha)).trans (hexit c (hc' ▸ ht) (hne' c hc')).symm
    have h0 : N.graph.outdegree t ≠ 0 := fun h => by
      obtain ⟨x, hx⟩ := (hP.leaves t).mp h
      exact leaf_notMem_blobSet h2 x (hx ▸ ht)
    have := hB.2 t htr h0
    omega
  · have hs := hpar e he.1 he.2
    by_cases hst : N.graph.source e = t
    · exact Or.inr hst
    · exact Or.inl ⟨hs, hst⟩
  · have hsub : {e | (N.graph.source e ∈ U \ {t} ∨ N.graph.source e = t) ∧ N.graph.target e ∉ U \ {t}} ⊆ {f₂.1.1} := by
      rintro e ⟨hs, hte⟩
      have hsU : N.graph.source e ∈ U := by
        rcases hs with h | h
        · exact h.1
        · exact h ▸ ht
      have hteU : N.graph.target e ∉ U := fun h => by
        by_cases htt : N.graph.target e = t
        · exact hmax e htt hsU
        · exact hte ⟨h, htt⟩
      exact hexit e hsU hteU
    calc _ ≤ ({f₂.1.1} : Set E).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by simp

/-- **A 2-blob of `𝒩⁻` gives rise to a set of nodes of `𝒩⁺` to contract** (`a:claim:thm1b-two-blobs`): "If there are any 2-blobs on `𝒩⁻`, set all edge lengths in `𝒩⁺` that give rise to them equal to 0". -/
theorem exists_isContractible_of_cutDegree_two {b : (semidirected hN hX).graph.BlobVertex} (h2 : cutDegree (semidirected hN hX).graph b = 2) : ∃ r S, IsContractible N r S := by
  by_cases hc : blobOf (semidirected hN hX).graph (topNode hN hX) = b
  · exact ⟨_, _, isContractible_of_top h2 hc⟩
  · obtain ⟨t, ht⟩ := exists_isContractible_of_not_top h2 hc
    exact ⟨_, _, ht⟩

end Extract

end AllmanEtAl2023
