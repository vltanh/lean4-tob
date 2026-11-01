module

public import AllmanEtAl2023.InducedNetwork
public import Phylogenetics.NMSC.Glue
public import Phylogenetics.NMSC.Induced
public import Phylogenetics.Coalescent.PMF

/-!
# Allman, Baños, Mitchell, Rhodes 2023: concordance factors on the induced network of Definition 6

"In passing to an induced network, B-quartets may become T-quartets, although `CF`s remain unchanged." The three steps of Definition 6, each a theorem, with no use of the
exchangeability of four lineages:

* step 1, `nmscCF_retained`: the lineages of the taxa `Y` stay on the arcs ancestral to `Y`, and the concordance factors of a quartet tree on `Y` do not change, for any set `Y` of taxa.
  This is the library's restriction at the root (`NMSC.sum_sum_strictBelow_eq`), with sampling consistency (`NMSC.sum_injDist_trace_weak`), where `Y` is more than the four taxa;
* step 2: the library's `NMSC.nmscCF_suppress`;
* step 3, `geneTreeDist_removeStem`, `nmscCF_removeStem`: an arc from a root with one child changes nothing, since the coalescent over an infinite time absorbs a coalescent over a finite time
  (`kingmanTransition_mul_kingmanAbsorption`).

And the map of parameters: `isMetric_stemMetric`, `isGenericNull_stemMetric`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace AllmanEtAl2023

/-! ### Kingman's coalescent over an infinite time, along an injection of the lineages -/

section Embed

variable {L M : Type*} [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]

omit [Fintype L] [Fintype M] [DecidableEq L] in
/-- The image of a forest under an injection of the lineages is a forest. -/
theorem isForest_embedFamily (ι : L ↪ M) {F : Finset (Finset L)} (hF : IsForest F) : IsForest (embedFamily ι F) := by
  constructor
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := mem_embedFamily.1 hA
    exact (hF.1 B hB).map
  · intro A hA C hC
    obtain ⟨B, hB, rfl⟩ := mem_embedFamily.1 hA
    obtain ⟨D, hD, rfl⟩ := mem_embedFamily.1 hC
    rcases hF.2 B hB D hD with h | h | h
    · exact Or.inl (Finset.map_subset_map.mpr h)
    · exact Or.inr (Or.inl (Finset.map_subset_map.mpr h))
    · exact Or.inr (Or.inr (Finset.disjoint_map _ |>.mpr h))

/-- **The coalescent over an infinite time is natural with respect to injections of the lineages.** -/
theorem kingmanAbsorption_embedFamily (ι : L ↪ M) (F G : Finset (Finset L)) :
    kingmanAbsorption (embedFamily ι F) (embedFamily ι G) = kingmanAbsorption F G := by
  simp only [kingmanAbsorption, kingmanTransition_embedFamily]

end Embed

/-! ### Step 1: the arcs ancestral to the taxa -/

section Retained

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

/-- **The concordance factor of a quartet tree** can be read from the lineages of any set of taxa containing its four. -/
theorem nmscCF_eq_sum_injDist (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ) (s : QuartetTree X) {Q : Finset X} (hQ : s.taxa ⊆ Q) :
    nmscCF N θ ρ s = ∑ G, if Displays (unroot G) s then injDist N θ ρ (taxaInj N Q) G else 0 := by
  rw [nmscCF_eq_cherryMass_weak hN hθ hρ s]
  unfold cherryMass
  have hinter : Q ∩ s.taxa = s.taxa := Finset.inter_eq_right.mpr hQ
  have hd : ∀ H, injDist N θ ρ (taxaInj N s.taxa) H = ∑ G, if traceForest s.taxa G = H then injDist N θ ρ (taxaInj N Q) G else 0 := by
    intro H
    rw [sum_injDist_trace_weak hN hθ hρ (validInj_taxaInj Q) s.taxa H]
    simp only [traceForest_taxaInj, hinter]
  have h : ∀ G : Finset (Finset X), (if Displays (unroot G) s then injDist N θ ρ (taxaInj N Q) G else 0) =
      ∑ H, if traceForest s.taxa G = H then (if ∃ B ∈ s.val, B ∈ H then injDist N θ ρ (taxaInj N Q) G else 0) else 0 := by
    intro G
    rw [sum_ite_eq]
    simp only [mem_univ, ↓reduceIte, displays_unroot_iff]
  simp only [h]
  rw [sum_comm]
  refine sum_congr rfl fun H _ => ?_
  rw [hd]
  split_ifs with hc
  · rfl
  · simp

/-- What the forest arriving at the root gives to a quartet tree. -/
def displayValue {L : Type*} [Fintype L] [DecidableEq L] (s : QuartetTree L) (F : Finset (Finset L)) : ℝ :=
  ∑ G, if Displays (unroot G) s then kingmanAbsorption F G else 0

/-- The mass of a quartet tree, from the forest arriving at the root. -/
theorem sum_displays_injDist (inj : V → Finset (Finset X)) (s : QuartetTree X) :
    (∑ G, if Displays (unroot G) s then injDist N θ ρ inj G else 0) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X), injWeight N θ ρ inj bot top * displayValue s (arriving N inj top N.root) := by
  unfold injDist displayValue
  simp only [mul_sum]
  have h : ∀ G : Finset (Finset X), (if Displays (unroot G) s then
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X), injWeight N θ ρ inj bot top * kingmanAbsorption (arriving N inj top N.root) G else 0) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        injWeight N θ ρ inj bot top * if Displays (unroot G) s then kingmanAbsorption (arriving N inj top N.root) G else 0 := by
    intro G
    split_ifs <;> simp
  simp only [h]
  rw [sum_comm]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_comm]

variable {Q : Finset X} [Fintype (Q : Set X)] [DecidableEq (Q : Set X)]

omit [Fintype V] [Fintype E] in
/-- A gene tree displays the image of a quartet tree exactly when it displays it. -/
theorem displays_unroot_embedFamily (s : QuartetTree (Q : Set X)) (G : Finset (Finset (Q : Set X))) :
    Displays (unroot (embedFamily (taxonEmb Q) G)) (s.map Subtype.val_injective) ↔ Displays (unroot G) s := by
  rw [displays_unroot_iff, displays_unroot_iff, QuartetTree.map_val, QuartetTree.map_taxa]
  have hmap : ∀ A : Finset (Q : Set X), A.map (taxonEmb Q) = A.image Subtype.val := fun A => Finset.map_eq_image _ _
  have hinter : ∀ A B : Finset (Q : Set X), A.image Subtype.val ∩ B.image Subtype.val = (A ∩ B).image Subtype.val := fun A B =>
    (Finset.image_inter _ _ Subtype.val_injective).symm
  constructor
  · rintro ⟨B', hB', hm⟩
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB'
    obtain ⟨A', hA', hne, hA⟩ := mem_traceForest.mp hm
    obtain ⟨A, hAG, rfl⟩ := mem_embedFamily.1 hA'
    rw [hmap, hinter] at hA
    have hAB : A ∩ s.taxa = B := Finset.image_injective Subtype.val_injective hA
    refine ⟨B, hB, mem_traceForest.mpr ⟨A, hAG, ?_, hAB⟩⟩
    rw [hAB]
    exact Finset.card_pos.mp (by rw [s.card_of_mem hB]; omega)
  · rintro ⟨B, hB, hm⟩
    obtain ⟨A, hAG, hne, hA⟩ := mem_traceForest.mp hm
    refine ⟨B.image Subtype.val, Finset.mem_image_of_mem _ hB, mem_traceForest.mpr ⟨A.map (taxonEmb Q), map_mem_embedFamily.2 hAG, ?_, ?_⟩⟩
    · rw [hmap, hinter]
      exact hne.image _
    · rw [hmap, hinter, hA]

omit [Fintype V] [Fintype E] in
/-- The value of a forest and of its image. -/
theorem displayValue_embedFamily (s : QuartetTree (Q : Set X)) {F : Finset (Finset (Q : Set X))} (hF : IsForest F) :
    displayValue (s.map Subtype.val_injective) (embedFamily (taxonEmb Q) F) = displayValue s F := by
  unfold displayValue
  have hsub : ∑ G ∈ univ.image (embedFamily (taxonEmb Q)),
        (if Displays (unroot G) (s.map Subtype.val_injective) then kingmanAbsorption (embedFamily (taxonEmb Q) F) G else 0) =
      ∑ G, (if Displays (unroot G) (s.map Subtype.val_injective) then kingmanAbsorption (embedFamily (taxonEmb Q) F) G else 0) := by
    refine sum_subset (subset_univ _) fun H _ hH => ?_
    have h0 : kingmanAbsorption (embedFamily (taxonEmb Q) F) H = 0 := by
      by_contra hne
      obtain ⟨-, -, hlin, -⟩ := kingmanAbsorption_support_forest (isForest_embedFamily _ hF) hne
      refine hH (mem_image.2 ⟨downFamily H, mem_univ _, embedFamily_downFamily fun A hA x hx => ?_⟩)
      have hxl : x ∈ lineages (embedFamily (taxonEmb Q) F) := hlin ▸ subset_lineages hA hx
      obtain ⟨C, hC, hxC⟩ := mem_lineages.1 hxl
      obtain ⟨B, -, rfl⟩ := mem_embedFamily.1 hC
      obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hxC
      exact y.2
    rw [h0]
    simp
  rw [← hsub, sum_image fun _ _ _ _ h => embedFamily_injective _ h]
  refine sum_congr rfl fun G _ => ?_
  simp only [displays_unroot_embedFamily, kingmanAbsorption_embedFamily]

variable {hl : N.root ∈ N.ancestralVertices (Q : Set X)} {hleaf : ∀ x ∈ (Q : Set X), N.graph.Reaches N.root (N.leaf x)}
  [Fintype (N.belowVertices N.root (Q : Set X))] [Fintype (N.belowArcs N.root (Q : Set X))]

/-- **Step 1 of Definition 6: concordance factors do not change on retaining the arcs ancestral to a set of taxa.** The proof is the law of the forest arriving at the root, `NMSC.sum_sum_strictBelow_eq`
at the root, read through what the forest gives to the quartet tree. It uses no exchangeability, and `Q` may have more than four taxa. -/
theorem nmscCF_retained (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    (hNL : (N.belowNetwork N.root (Q : Set X) hl hleaf).IsPhylogenetic) (s : QuartetTree (Q : Set X)) :
    nmscCF (N.belowNetwork N.root (Q : Set X) hl hleaf) (belowMetric N.root (Q : Set X) θ) ρ s = nmscCF N θ ρ (s.map Subtype.val_injective) := by
  have hst := N.root_isStableAncestor (Q : Set X)
  have hsub : (s.map Subtype.val_injective).taxa ⊆ Q := by
    rw [QuartetTree.map_taxa]
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  rw [nmscCF_eq_sum_injDist hN hθ hρ _ hsub]
  have hstrict : strictBelow N N.root = univ.erase N.root := by
    ext v
    simp only [mem_strictBelow, mem_erase, mem_univ, and_true]
    exact ⟨fun h => h.2, fun h => ⟨hN.root_reaches v, h⟩⟩
  have hstrict' : strictBelow (N.belowNetwork N.root (Q : Set X) hl hleaf) (N.belowNetwork N.root (Q : Set X) hl hleaf).root =
      univ.erase (N.belowNetwork N.root (Q : Set X) hl hleaf).root := by
    ext v
    simp only [mem_strictBelow, mem_erase, mem_univ, and_true]
    exact ⟨fun h => h.2, fun h => ⟨hNL.root_reaches v, h⟩⟩
  have hcompl : (univ.filter fun e => N.graph.target e ∈ strictBelow N N.root)ᶜ = ∅ := by
    rw [Finset.compl_eq_empty_iff]
    refine Finset.filter_true_of_mem fun e _ => ?_
    rw [hstrict]
    exact mem_erase.2 ⟨target_ne_root hN e, mem_univ _⟩
  have hB := sum_sum_strictBelow_eq (θ := θ) (ρ := ρ) (hl := hl) (hleaf := hleaf) hN hst hNL (displayValue (s.map Subtype.val_injective))
  rw [hcompl, hstrict, hstrict'] at hB
  simp only [card_empty, pow_zero, mul_one, one_mul] at hB
  have hR := sum_displays_injDist (N := N) (θ := θ) (ρ := ρ) (taxaInj N Q) (s.map Subtype.val_injective)
  unfold injWeight at hR
  have hL : nmscCF (N.belowNetwork N.root (Q : Set X) hl hleaf) (belowMetric N.root (Q : Set X) θ) ρ s =
      ∑ G, if Displays (unroot G) s then injDist (N.belowNetwork N.root (Q : Set X) hl hleaf) (belowMetric N.root (Q : Set X) θ) ρ
        (taxaInj (N.belowNetwork N.root (Q : Set X) hl hleaf) univ) G else 0 := by
    unfold nmscCF
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [geneTreeDist_eq_injDist hNL G]
  have hL₂ := sum_displays_injDist (N := N.belowNetwork N.root (Q : Set X) hl hleaf) (θ := belowMetric N.root (Q : Set X) θ) (ρ := ρ)
    (taxaInj (N.belowNetwork N.root (Q : Set X) hl hleaf) univ) s
  rw [hL, hL₂, hR, hB]
  have key : ∀ b t, injWeight (N.belowNetwork N.root (Q : Set X) hl hleaf) (belowMetric N.root (Q : Set X) θ) ρ
          (taxaInj (N.belowNetwork N.root (Q : Set X) hl hleaf) univ) b t *
        displayValue s (arriving (N.belowNetwork N.root (Q : Set X) hl hleaf)
          (taxaInj (N.belowNetwork N.root (Q : Set X) hl hleaf) univ) t (N.belowNetwork N.root (Q : Set X) hl hleaf).root) =
      (∏ u ∈ univ.erase (N.belowNetwork N.root (Q : Set X) hl hleaf).root,
            vertexWeight (N.belowNetwork N.root (Q : Set X) hl hleaf) (belowMetric N.root (Q : Set X) θ) ρ
              (taxaInj (N.belowNetwork N.root (Q : Set X) hl hleaf) univ) u b t) *
          displayValue (s.map Subtype.val_injective)
            (embedFamily (taxonEmb Q)
              (arriving (N.belowNetwork N.root (Q : Set X) hl hleaf) (taxaInj (N.belowNetwork N.root (Q : Set X) hl hleaf) univ) t
                (N.belowNetwork N.root (Q : Set X) hl hleaf).root)) := by
    intro b t
    have hW : (∏ u ∈ univ.erase (N.belowNetwork N.root (Q : Set X) hl hleaf).root,
          vertexWeight (N.belowNetwork N.root (Q : Set X) hl hleaf) (belowMetric N.root (Q : Set X) θ) ρ
            (taxaInj (N.belowNetwork N.root (Q : Set X) hl hleaf) univ) u b t) =
        injWeight (N.belowNetwork N.root (Q : Set X) hl hleaf) (belowMetric N.root (Q : Set X) θ) ρ
          (taxaInj (N.belowNetwork N.root (Q : Set X) hl hleaf) univ) b t := by
      unfold injWeight
      refine Finset.prod_congr ?_ fun _ _ => rfl
      ext v
      simp
    rw [hW]
    by_cases hw : injWeight (N.belowNetwork N.root (Q : Set X) hl hleaf) (belowMetric N.root (Q : Set X) θ) ρ
        (taxaInj (N.belowNetwork N.root (Q : Set X) hl hleaf) univ) b t = 0
    · rw [hw, zero_mul, zero_mul]
    · have hforest := (good_arriving_root hNL (validInj_taxaInj univ) hw).1.1
      rw [displayValue_embedFamily s hforest]
  simp only [key]
  exact sum_congr_instance _ _ _ _ fun b => sum_congr_instance _ _ _ _ fun t => rfl

end Retained

/-! ### Step 3: the stem -/

/-- `Finset.ne_of_mem_erase`, for any instance. -/
theorem ne_of_mem_erase' {α : Type*} {i : DecidableEq α} {s : Finset α} {a b : α} (h : a ∈ @Finset.erase α i s b) : a ≠ b :=
  Finset.ne_of_mem_erase h

section Stem

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {M : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

/-- The parameters after removing a stem: those of the same arcs. -/
def stemMetric (M : RootedNetwork V E X) (θ : MetricData E) : MetricData {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} where
  length e := θ.length e.1
  inheritance e := θ.inheritance e.1

/-- A function of the arcs, from its values off the stem and on it. -/
def glueStem {α : Type*} (M : RootedNetwork V E X) (b : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → α) (x : α) : E → α :=
  fun e => if h : ¬ (HasStem M ∧ M.graph.source e = M.root) then b ⟨e, h⟩ else x

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem glueStem_of_mem {α : Type*} (b : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → α) (x : α)
    (e : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}) : glueStem M b x e.1 = b e := by
  unfold glueStem
  exact dite_eq_left_of_eq_true (eq_true e.2)

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem glueStem_stem {α : Type*} (h : HasStem M) (b : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → α) (x : α) :
    glueStem M b x (stemArc M h) = x := by
  unfold glueStem
  refine dite_eq_right_of_eq_false (eq_false ?_)
  rw [not_not]
  exact ⟨h, (stemArc_spec M h _).mpr rfl⟩

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- A sum over the functions of the arcs is a sum over their values off the stem and on it. -/
theorem sum_glueStem {α : Type*} [Fintype α] (h : HasStem M) [Fintype {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}] (g : (E → α) → ℝ) :
    ∑ f, g f = ∑ b : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → α, ∑ x, g (glueStem M b x) := by
  let φ : (({e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → α) × α) ≃ (E → α) :=
    { toFun := fun p => glueStem M p.1 p.2
      invFun := fun f => (fun e => f e.1, f (stemArc M h))
      left_inv := fun p => Prod.ext (funext fun e => glueStem_of_mem _ _ e) (glueStem_stem h _ _)
      right_inv := fun f => by
        funext e
        by_cases he : ¬ (HasStem M ∧ M.graph.source e = M.root)
        · exact glueStem_of_mem (fun e => f e.1) _ ⟨e, he⟩
        · have hee : e = stemArc M h := (stemArc_spec M h e).mp (not_not.mp he).2
          subst hee
          exact glueStem_stem h _ _ }
  rw [← φ.sum_comp, Fintype.sum_prod_type]
  rfl

variable [Fintype {v // ¬ (HasStem M ∧ v = M.root)}] [Fintype {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}]

omit [Fintype V] [Fintype E] [Fintype {v // ¬ (HasStem M ∧ v = M.root)}] [Fintype {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}] in
/-- The forest arriving at a vertex other than the root, with a stem. -/
theorem arrivingForest_glueStem [Fintype E] [Fintype {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}] (hM : M.IsPhylogenetic)
    (t : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → Finset (Finset X)) (y : Finset (Finset X))
    (v : {v // ¬ (HasStem M ∧ v = M.root)}) :
    arrivingForest M (glueStem M t y) v.1 = arrivingForest (removeStem M hM) t v := by
  ext A
  simp only [arrivingForest, mem_union, mem_image, mem_filter, mem_univ, true_and, mem_biUnion]
  refine or_congr ?_ ?_
  · constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subtype.ext hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, congrArg Subtype.val hx, rfl⟩
  · constructor
    · rintro ⟨e, he, hA⟩
      have hes : ¬ (HasStem M ∧ M.graph.source e = M.root) := fun hc => v.2 ⟨hc.1, he ▸ hc.2⟩
      rw [show e = (⟨e, hes⟩ : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}).1 from rfl, glueStem_of_mem] at hA
      exact ⟨⟨e, hes⟩, Subtype.ext he, hA⟩
    · rintro ⟨e, he, hA⟩
      refine ⟨e.1, congrArg Subtype.val he, ?_⟩
      rw [glueStem_of_mem]
      exact hA

omit [Fintype V] [Fintype {v // ¬ (HasStem M ∧ v = M.root)}] [Fintype {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}] in
/-- The forest arriving at the root, with a stem, is the one at the top of the stem. -/
theorem arrivingForest_root_glueStem [Fintype {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}] (hM : M.IsPhylogenetic) (h : HasStem M)
    (t : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → Finset (Finset X)) (y : Finset (Finset X)) :
    arrivingForest M (glueStem M t y) M.root = y := by
  ext A
  simp only [arrivingForest, mem_union, mem_image, mem_filter, mem_univ, true_and, mem_biUnion]
  constructor
  · rintro (⟨x, hx, -⟩ | ⟨e, he, hA⟩)
    · exact absurd hx (M.leaf_ne_root hM x)
    · rw [(stemArc_spec M h e).mp he, glueStem_stem h] at hA
      exact hA
  · intro hA
    refine Or.inr ⟨stemArc M h, (stemArc_spec M h _).mpr rfl, ?_⟩
    rw [glueStem_stem h]
    exact hA

omit [Fintype V] [Fintype {v // ¬ (HasStem M ∧ v = M.root)}] in
/-- The allocation at a vertex other than the root and the child of the stem. -/
theorem allocationFactor_glueStem (hM : M.IsPhylogenetic) (h : HasStem M) (b : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → Finset (Finset X))
    (x : Finset (Finset X)) (F : Finset (Finset X)) (v : {v // ¬ (HasStem M ∧ v = M.root)}) (hv : v.1 ≠ M.graph.target (stemArc M h)) :
    allocationFactor M θ ρ F v.1 (glueStem M b x) = allocationFactor (removeStem M hM) (stemMetric M θ) ρ F v b := by
  have hes : ∀ e, M.graph.target e = v.1 → ¬ (HasStem M ∧ M.graph.source e = M.root) := fun e he hc =>
    hv (he ▸ congrArg M.graph.target ((stemArc_spec M h e).mp hc.2))
  refine allocationFactor_eq_of_equiv
    ⟨fun e => ⟨e.1.1, congrArg Subtype.val e.2⟩, fun e => ⟨⟨e.1, hes e.1 e.2⟩, Subtype.ext e.2⟩, fun _ => rfl, fun _ => rfl⟩
    (Equiv.refl _) (fun _ => rfl) fun a e => ?_
  have hg : glueStem M b x e.1.1 = b e.1 := glueStem_of_mem b x e.1
  change b e.1 = _ ↔ glueStem M b x e.1.1 = _
  rw [hg]
  exact Iff.rfl

omit [Fintype V] [Fintype {v // ¬ (HasStem M ∧ v = M.root)}] [Fintype {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}] in
/-- The allocation at the child of the stem is forced. -/
theorem allocationFactor_stem [Fintype {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}] (hM : M.IsPhylogenetic) (hθ : M.IsNormalized θ) (hρ : 0 ≤ ρ) (h : HasStem M)
    (b : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → Finset (Finset X)) (x F : Finset (Finset X)) :
    allocationFactor M θ ρ F (M.graph.target (stemArc M h)) (glueStem M b x) = if x = F then 1 else 0 := by
  have : Finite E := hM.finite_arcs
  have huniq : ∀ g, M.graph.target g = M.graph.target (stemArc M h) → g = stemArc M h := fun g hg => eq_stemArc_of_target hM h hg
  have h1 : θ.inheritance (stemArc M h) = 1 := hθ.1 _ ((M.graph.indegree_eq_one_iff _).mpr ⟨stemArc M h, fun f =>
    ⟨eq_stemArc_of_target hM h, fun hf => hf ▸ rfl⟩⟩)
  rw [allocationFactor_of_unique_arc hρ rfl huniq h1, glueStem_stem h]

omit [Fintype V] [Fintype X] [DecidableEq X] [Fintype {v // ¬ (HasStem M ∧ v = M.root)}] in
/-- The product over the arcs, with the stem split off. -/
theorem prod_glueStem (h : HasStem M) (f : E → ℝ) :
    ∏ e, f e = f (stemArc M h) * ∏ e : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}, f e.1 := by
  rw [← Finset.mul_prod_erase univ f (mem_univ (stemArc M h))]
  congr 1
  symm
  refine Finset.prod_bij (fun e _ => e.1) (fun e _ => mem_erase.2 ⟨fun he => e.2 ⟨h, ?_⟩, mem_univ _⟩) (fun _ _ _ _ he => Subtype.ext he) (fun e he => ?_) fun _ _ => rfl
  · rw [he]
    exact (stemArc_spec M h _).mpr rfl
  · refine ⟨⟨e, fun hc => (mem_erase.1 he).1 ((stemArc_spec M h e).mp hc.2)⟩, mem_univ _, rfl⟩

omit [Fintype E] [Fintype X] [DecidableEq X] [Fintype {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}] in
/-- The non-root vertices, with a stem: the child of the stem, which is the new root, and the non-root vertices of the network without the stem. -/
theorem prod_erase_root_glueStem (hM : M.IsPhylogenetic) (h : HasStem M) (f : V → ℝ) :
    ∏ v ∈ univ.erase M.root, f v = f (M.graph.target (stemArc M h)) * ∏ v ∈ univ.erase (removeStem M hM).root, f v.1 := by
  have hc : M.graph.target (stemArc M h) ∈ univ.erase M.root := mem_erase.2 ⟨target_ne_root hM _, mem_univ _⟩
  have hrv : ((removeStem M hM).root).1 = M.graph.target (stemArc M h) := by
    simp only [removeStem, dite_eq_left h]
  rw [← Finset.mul_prod_erase _ f hc]
  congr 1
  symm
  refine Finset.prod_bij (fun v _ => v.1) (fun v hv => ?_) (fun _ _ _ _ he => Subtype.ext he) (fun v hv => ?_) fun _ _ => rfl
  · refine mem_erase.2 ⟨fun he => (mem_erase.1 hv).1 (Subtype.ext (he.trans hrv.symm)), mem_erase.2 ⟨fun he => v.2 ⟨h, he⟩, mem_univ _⟩⟩
  · obtain ⟨hvc, hvr⟩ := mem_erase.1 hv
    have hvr' := (mem_erase.1 hvr).1
    exact ⟨⟨v, fun hc' => hvr' hc'.2⟩, mem_erase.2 ⟨fun he => hvc ((congrArg Subtype.val he).trans hrv), mem_univ _⟩, rfl⟩

/-- **Step 3 of Definition 6: removing a stem does not change the gene tree distribution**: an arc from a root with one child adds a coalescent over a finite time, before the coalescent over an
infinite time, which absorbs it. -/
theorem geneTreeDist_removeStem [Nontrivial X] (hM : M.IsPhylogenetic) (hθ : M.IsNormalized θ) (hρ : 0 ≤ ρ) (G : Finset (Finset X)) :
    geneTreeDist (removeStem M hM) (stemMetric M θ) ρ G = geneTreeDist M θ ρ G := by
  have : Finite E := hM.finite_arcs
  have hP : (removeStem M hM).IsPhylogenetic := removeStem_isPhylogenetic hM
  by_cases h : HasStem M
  · have hrv : (removeStem M hM).root = ⟨M.graph.target (stemArc M h), fun h' => target_ne_root hM _ h'.2⟩ :=
      Subtype.ext (by simp only [removeStem, dite_eq_left h])
    -- a history
    have hstep : ∀ (b t : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → Finset (Finset X)) (x y : Finset (Finset X)),
        historyWeight M θ ρ (glueStem M b x) (glueStem M t y) * kingmanAbsorption (arrivingForest M (glueStem M t y) M.root) G =
          historyWeight (removeStem M hM) (stemMetric M θ) ρ b t *
            ((if x = arrivingForest (removeStem M hM) t (removeStem M hM).root then 1 else 0) *
              (kingmanTransition (θ.length (stemArc M h)) x y * kingmanAbsorption y G)) := by
      intro b t x y
      have hF : arrivingForest M (glueStem M t y) (M.graph.target (stemArc M h)) = arrivingForest (removeStem M hM) t (removeStem M hM).root := by
        rw [hrv]
        exact arrivingForest_glueStem hM t y ⟨M.graph.target (stemArc M h), fun h' => target_ne_root hM _ h'.2⟩
      have hW : (∏ v ∈ univ.erase (removeStem M hM).root, allocationFactor M θ ρ (arrivingForest M (glueStem M t y) v.1) v.1 (glueStem M b x)) *
          (∏ e : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}, kingmanTransition (θ.length e.1) (glueStem M b x e.1) (glueStem M t y e.1)) =
          historyWeight (removeStem M hM) (stemMetric M θ) ρ b t := by
        unfold historyWeight
        congr 1
        · refine Finset.prod_congr (by ext v; simp) fun v hv => ?_
          have hvc : v.1 ≠ M.graph.target (stemArc M h) := fun he => ne_of_mem_erase' hv (by rw [hrv]; exact Subtype.ext he)
          rw [arrivingForest_glueStem hM t y v, allocationFactor_glueStem hM h b x _ v hvc]
        · exact Finset.prod_congr rfl fun e _ => by rw [glueStem_of_mem, glueStem_of_mem]; rfl
      rw [← hW]
      unfold historyWeight
      rw [prod_erase_root_glueStem hM h, prod_glueStem h, arrivingForest_root_glueStem hM h, hF, allocationFactor_stem hM hθ hρ h, glueStem_stem h, glueStem_stem h]
      ring
    -- the two sums over the stem
    have hsum : ∀ (b t : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → Finset (Finset X)),
        historyWeight (removeStem M hM) (stemMetric M θ) ρ b t * kingmanAbsorption (arrivingForest (removeStem M hM) t (removeStem M hM).root) G =
          ∑ x, ∑ y, historyWeight (removeStem M hM) (stemMetric M θ) ρ b t *
            ((if x = arrivingForest (removeStem M hM) t (removeStem M hM).root then 1 else 0) *
              (kingmanTransition (θ.length (stemArc M h)) x y * kingmanAbsorption y G)) := by
      intro b t
      by_cases hw : historyWeight (removeStem M hM) (stemMetric M θ) ρ b t = 0
      · simp [hw]
      · have hforest : IsForest (arrivingForest (removeStem M hM) t (removeStem M hM).root) := by
          rw [historyWeight_eq_injWeight hP] at hw
          rw [arrivingForest_eq]
          exact (good_arriving_root hP (validInj_taxaInj univ) hw).1.1
        simp only [← mul_sum]
        congr 1
        rw [Finset.sum_eq_single (arrivingForest (removeStem M hM) t (removeStem M hM).root)]
        · simp only [↓reduceIte, one_mul]
          exact (kingmanTransition_mul_kingmanAbsorption hforest _ G).symm
        · intro x _ hx
          simp [hx]
        · exact fun hc => absurd (mem_univ _) hc
    unfold geneTreeDist
    rw [sum_glueStem h]
    have hRHS : ∀ b : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → Finset (Finset X),
        ∑ x, ∑ top : E → Finset (Finset X), historyWeight M θ ρ (glueStem M b x) top * kingmanAbsorption (arrivingForest M top M.root) G =
          ∑ t : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → Finset (Finset X),
            historyWeight (removeStem M hM) (stemMetric M θ) ρ b t * kingmanAbsorption (arrivingForest (removeStem M hM) t (removeStem M hM).root) G := by
      intro b
      simp only [sum_glueStem h (α := Finset (Finset X)) (fun top : E → Finset (Finset X) => historyWeight M θ ρ (glueStem M b _) top * kingmanAbsorption (arrivingForest M top M.root) G)]
      rw [sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hsum b t]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hstep b t x y
    simp only [hRHS]
    exact sum_congr_instance _ _ _ _ fun b => sum_congr_instance _ _ _ _ fun t => rfl
  · -- no stem: the same network
    let fV : V ≃ {v // ¬ (HasStem M ∧ v = M.root)} := ⟨fun v => ⟨v, fun hc => h hc.1⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩
    let fE : E ≃ {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} := ⟨fun e => ⟨e, fun hc => h hc.1⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩
    have hroot : (removeStem M hM).root = fV M.root := Subtype.ext (by simp only [removeStem, dite_eq_right h]; rfl)
    have hinj : (fun v => taxaInj (removeStem M hM) univ (fV v)) = taxaInj M univ := by
      funext v
      ext A
      simp only [mem_taxaInj]
      constructor
      · rintro ⟨x, hx, hxv, rfl⟩
        exact ⟨x, hx, congrArg Subtype.val hxv, rfl⟩
      · rintro ⟨x, hx, hxv, rfl⟩
        exact ⟨x, hx, Subtype.ext hxv, rfl⟩
    rw [geneTreeDist_eq_injDist hP, geneTreeDist_eq_injDist hM, injDist_eq_sum_rootDist, injDist_eq_sum_rootDist]
    refine Finset.sum_congr rfl fun F _ => ?_
    congr 1
    rw [rootDist_congr (N := M) (N' := removeStem M hM) (θ := θ) (θ' := stemMetric M θ) fV fE (fun _ => rfl) (fun _ => rfl) hroot (fun _ => rfl) (fun _ => rfl), hinj]

/-- **Step 3 of Definition 6: removing a stem does not change the concordance factors.** -/
theorem nmscCF_removeStem [Nontrivial X] (hM : M.IsPhylogenetic) (hθ : M.IsNormalized θ) (hρ : 0 ≤ ρ) (s : QuartetTree X) :
    nmscCF (removeStem M hM) (stemMetric M θ) ρ s = nmscCF M θ ρ s := by
  unfold nmscCF
  simp only [geneTreeDist_removeStem hM hθ hρ]

/-! ### The map of parameters of a stem -/

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] [Fintype {v // ¬ (HasStem M ∧ v = M.root)}] [Fintype {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}] in
/-- The target of an arc keeps its parents. -/
theorem removeStem_indegree_target [Nontrivial X] (hM : M.IsPhylogenetic) (e : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}) :
    (removeStem M hM).graph.indegree ((removeStem M hM).graph.target e) = M.graph.indegree (M.graph.target e.1) :=
  removeStem_indegree hM (target_ne_root (removeStem_isPhylogenetic hM) e)

omit [Fintype V] [Fintype X] [DecidableEq X] [Fintype {v // ¬ (HasStem M ∧ v = M.root)}] in
/-- Inheritances sum as before, off the new root. -/
theorem sum_stemMetric_inheritance [Nontrivial X] (hM : M.IsPhylogenetic) {θ : MetricData E} {v : {v // ¬ (HasStem M ∧ v = M.root)}} (hv : v ≠ (removeStem M hM).root) :
    (∑ e, @ite _ ((removeStem M hM).graph.target e = v) (Classical.propDecidable _) ((stemMetric M θ).inheritance e) 0) = ∑ e, if M.graph.target e = v.1 then θ.inheritance e else 0 := by
  refine @sum_ite_of_injective _ _ _ _ (fun e => (removeStem M hM).graph.target e = v) (fun e => M.graph.target e = v.1) (fun _ => Classical.propDecidable _)
    (fun _ => Classical.propDecidable _) Subtype.val θ.inheritance Subtype.val_injective (fun e => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩) fun e he => ?_
  refine ⟨⟨e, fun hc => hv (Subtype.ext ?_)⟩, rfl⟩
  have hee := (stemArc_spec M hc.1 e).mp hc.2
  simp only [removeStem, dite_eq_left hc.1]
  exact he.symm.trans (congrArg M.graph.target hee)

omit [Fintype V] [Fintype X] [DecidableEq X] [Fintype {v // ¬ (HasStem M ∧ v = M.root)}] in
/-- **The map of parameters of step 3 sends valid parameters to valid parameters.** -/
theorem isMetric_stemMetric [Nontrivial X] (hM : M.IsPhylogenetic) {θ : MetricData E} (hθ : M.IsMetric θ) : (removeStem M hM).IsMetric (stemMetric M θ) := by
  have hP := removeStem_isPhylogenetic hM
  obtain ⟨h1, h2, h3, h4, h5⟩ := hθ
  refine ⟨fun e he => h1 e.1 ?_, fun e he => h2 e.1 ?_, fun e he => h3 e.1 ?_, fun e he => h4 e.1 ?_, fun v hv => ?_⟩
  · exact (removeStem_indegree_target hM e).symm.trans he
  · exact le_of_le_of_eq he (removeStem_indegree_target hM e)
  · exact (removeStem_indegree_target hM e).symm.trans he
  · exact le_of_le_of_eq he (removeStem_indegree_target hM e)
  · have hvr : v ≠ (removeStem M hM).root := by
      rintro rfl
      rw [hP.root_indegree] at hv
      omega
    rw [removeStem_indegree hM hvr] at hv
    exact (sum_stemMetric_inheritance hM hvr).trans (h5 v.1 hv)

omit [Fintype V] [Fintype X] [DecidableEq X] [Fintype {v // ¬ (HasStem M ∧ v = M.root)}] in
/-- **Preimages of null sets under the map of parameters of step 3 are null**: it is a restriction to the kept arcs, which is linear and surjective. -/
theorem isGenericNull_stemMetric [Nontrivial X] (hM : M.IsPhylogenetic) (e₀ : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)})
    {A' : Set (MetricData {e // ¬ (HasStem M ∧ M.graph.source e = M.root)})} (hA' : IsGenericNull (removeStem M hM) A') :
    IsGenericNull M {θ | M.IsMetric θ ∧ stemMetric M θ ∈ A'} := by
  have hP := removeStem_isPhylogenetic hM
  have hval : Function.Injective (Subtype.val : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)} → E) := Subtype.val_injective
  have hkept : ∀ {v : {v // ¬ (HasStem M ∧ v = M.root)}} {e : E}, 2 ≤ (removeStem M hM).graph.indegree v → M.graph.target e = v.1 →
      ¬ (HasStem M ∧ M.graph.source e = M.root) := by
    intro v e hv he hc
    have hvr : v ≠ (removeStem M hM).root := by
      rintro rfl
      rw [hP.root_indegree] at hv
      omega
    have hee := (stemArc_spec M hc.1 e).mp hc.2
    refine hvr (Subtype.ext ?_)
    simp only [removeStem, dite_eq_left hc.1]
    exact he.symm.trans (congrArg M.graph.target hee)
  refine isGenericNull_comap (stemMetric M) (fun θ hθ => isMetric_stemMetric hM hθ)
    (fun d hd => ⟨fun v => if h : ¬ (HasStem M ∧ M.graph.source (d v.1) = M.root) then ⟨d v.1, h⟩ else e₀, fun v hv => ?_,
      (LinearMap.funLeft ℝ ℝ Subtype.val).prodMap (LinearMap.funLeft ℝ ℝ Subtype.val), ?_, fun θ x hθ hℓ hg => ⟨?_, fun e he hne => ?_⟩⟩) hA'
  · have hvr : v ≠ (removeStem M hM).root := by
      rintro rfl
      rw [hP.root_indegree] at hv
      omega
    have hv' := hv
    rw [removeStem_indegree hM hvr] at hv'
    have ht := hd v.1 hv'
    have hmem := hkept hv ht
    simp only [dite_eq_left hmem]
    exact Subtype.ext ht
  · rw [LinearMap.coe_prodMap]
    exact (LinearMap.funLeft_surjective_of_injective ℝ ℝ _ hval).prodMap (LinearMap.funLeft_surjective_of_injective ℝ ℝ _ hval)
  · funext e
    exact congrFun hℓ e.1
  · have hhyb : M.IsHybridArc e.1 := le_of_le_of_eq he (removeStem_indegree_target hM e)
    refine hg e.1 hhyb fun hd' => hne ?_
    have hmem : ¬ (HasStem M ∧ M.graph.source (d ((removeStem M hM).graph.target e).1) = M.root) := by
      rw [show ((removeStem M hM).graph.target e).1 = M.graph.target e.1 from rfl, ← hd']
      exact e.2
    simp only [dite_eq_left hmem]
    exact Subtype.ext hd'

end Stem

end AllmanEtAl2023
