module

public import AllmanEtAl2023.FourCycle
public import AllmanEtAl2023.LSABlob

/-!
# Allman, Baños, Mitchell, Rhodes 2023: edges between trivial blobs

"For edges between trivial blobs, it is straightforward to see that edge lengths are identifiable" (Section 5).

The paper gives no proof. The proof here is the usual one: for an edge `e` with `a, b` in different branches below it, `c` in the other branch at its top, and `d` elsewhere, the lineages of `a, b` coalesce on `e` with probability `1 - exp (-ℓ e)`,
and otherwise three lineages reach the top of `e`, so `CF_{ab|cd} = 1 - (2/3) exp (-ℓ e)`: `nmscCF_of_edge`. The edge of `𝒩⁻` that the root of `𝒩⊕` becomes has the length of two edges of `𝒩⁺`, as Definition 5 says: `nmscCF_of_root`.

The sentence needs two qualifications, which the proof shows, and which the paper's context supplies:

* the edge is internal: a pendant edge can join a trivial blob, the taxon, to another, but a single lineage on it never coalesces, so nothing depends on its length;
* the length is that of `𝒩⁻`, since at the root only the sum of the lengths of the two edges counts.

`edge_length_eq` and `root_length_eq` are the statements on `𝒩⁺`, and `semidirected_length_eq` the statement on `𝒩⁻`. `FourCycle.pendant_not_identifiable` is a pendant edge between trivial blobs whose length is not identifiable.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph Phylogenetics.NMSC Finset
open Phylogenetics.NMSC.Chain
open scoped Classical

namespace AllmanEtAl2023.TrivialEdges

open BlobStructure

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

/-! ### One step along an edge -/

/-- The Markov property at an edge, as a mean. -/
theorem cherryMass_eq_meanOn_below (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {e : E} (hdom : DominatedInj N e inj) (r : QuartetTree X) :
    cherryMass N θ ρ inj r = meanOn N θ ρ inj (belowSet N e) fun top => cherryMass N θ ρ (liftInj N e inj (top e)) r := by
  have hB : (0 : ℝ) < ((Fintype.card (Finset (Finset X)) : ℕ) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hM := belowMass_mul_cherryMass hN hθ hρ hinj hdom r
  unfold meanOn
  rw [← hM]
  have hfil : (univ.filter fun f => N.graph.target f ∈ belowSet N e) = arcsBelow N e := by
    ext f
    simp [arcsBelow]
  rw [hfil]
  unfold belowMass
  field_simp

/-- **The lineages reaching the bottom of an edge**, when they are those of `P`, none is injected at the bottom, and no branch below has them all: they arrive apart. -/
theorem arriving_eq_singletons (hN : N.IsPhylogenetic) {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {e : E} (hdom : DominatedInj N e inj) {P : Finset X} (hP2 : #P = 2)
    (hP : ∀ x, (∃ w ∈ belowSet N e, x ∈ lineages (inj w)) ↔ x ∈ P) (hno : inj (N.graph.target e) = ∅)
    (hsplit : ∀ g, N.graph.source g = N.graph.target e → ∃ x ∈ P, ∀ w, N.graph.Reaches (N.graph.target g) w → x ∉ lineages (inj w)) {bot top : E → Finset (Finset X)}
    (h : ∏ u ∈ (belowSet N e).erase (N.graph.target e), vertexWeight N θ ρ inj u bot top ≠ 0) : arriving N inj top (N.graph.target e) = P.image fun x => ({x} : Finset X) := by
  have hW := downClosed_belowSet_erase (N := N) hN e
  have hF := frontier_of_prod_ne_zero hN hinj hW h
  have hgood := hF.good_arriving hinj (notMem_erase _ _) fun f hf => target_mem_belowSet_erase hN hf
  have hb : ∀ {g : E}, N.graph.source g = N.graph.target e → N.graph.target g ∈ (belowSet N e).erase (N.graph.target e) := fun hg => target_mem_belowSet_erase hN hg
  -- the lineages
  have hlin : lineages (arriving N inj top (N.graph.target e)) = P := by
    ext x
    rw [mem_lineages_arriving]
    constructor
    · rintro (hx | ⟨g, hg, hx⟩)
      · rw [hno] at hx
        simp at hx
      · obtain ⟨w, hw, hxw⟩ := hF.below g (hb hg) x hx
        exact (hP x).mp ⟨w, mem_belowSet.2 ((mem_belowSet.1 (mem_of_mem_erase (hb hg))).trans hw), hxw⟩
    · intro hx
      obtain ⟨w, hw, hxw⟩ := (hP x).mpr hx
      have hwne : w ≠ N.graph.target e := by
        rintro rfl
        rw [hno] at hxw
        simp at hxw
      obtain ⟨f, hft, hfs, hxf⟩ := (hF.mem x).2 ⟨w, mem_erase.2 ⟨hwne, hw⟩, hxw⟩
      by_cases hsv : N.graph.source f = N.graph.target e
      · exact Or.inr ⟨f, hsv, hxf⟩
      · exfalso
        obtain ⟨w', hw', hxw'⟩ := hF.below f hft x hxf
        obtain ⟨B, hB, -⟩ := mem_lineages.1 hxw'
        have hw'B : w' ∈ belowSet N e := mem_belowSet.2 ((mem_belowSet.1 (mem_of_mem_erase hft)).trans hw')
        refine hdom w' hw'B ⟨B, hB⟩ ?_
        have hfe : f ≠ e := by
          rintro rfl
          exact (mem_erase.1 hft).1 rfl
        have h1 : N.AvoidingReach e N.root (N.graph.source f) := by
          by_contra hn
          exact hfs (mem_erase.2 ⟨hsv, mem_belowSet.2 (target_reaches_of_not_avoidingReach (hN.root_reaches _) hn)⟩)
        exact (h1.tail ⟨f, hfe, rfl, rfl⟩).trans (avoidingReach_of_target_reaches hN.acyclic (mem_belowSet.1 (mem_of_mem_erase hft)) hw')
  -- the cherry is not there yet
  have hnP : P ∉ arriving N inj top (N.graph.target e) := by
    intro hm
    unfold arriving at hm
    rw [hno, empty_union] at hm
    obtain ⟨g, hg, hPg⟩ := mem_biUnion.1 hm
    have hgs : N.graph.source g = N.graph.target e := (mem_filter.1 hg).2
    obtain ⟨x, hx, hnx⟩ := hsplit g hgs
    obtain ⟨w, hw, hxw⟩ := hF.below g (hb hgs) x (mem_lineages.2 ⟨P, hPg, hx⟩)
    exact hnx w hw hxw
  have hsing := hgood.eq_singletons fun ⟨C, hC, hC2⟩ => hnP (by
    have hCP : C = P := eq_of_subset_of_card_le (fun x hx => hlin ▸ mem_lineages.2 ⟨C, hC, hx⟩) (by rw [hP2, hC2])
    exact hCP ▸ hC)
  rwa [hlin] at hsing

/-- **One step along an edge**: two lineages on `e` coalesce with probability `1 - exp (-ℓ e)`. -/
theorem cherryMass_step (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {e : E} (hdom : DominatedInj N e inj) {P : Finset X} (hP2 : #P = 2)
    (hu : ∀ f, N.graph.target f = N.graph.target e → f = e) (hP : ∀ x, (∃ w ∈ belowSet N e, x ∈ lineages (inj w)) ↔ x ∈ P) (hno : inj (N.graph.target e) = ∅)
    (hsplit : ∀ g, N.graph.source g = N.graph.target e → ∃ x ∈ P, ∀ w, N.graph.Reaches (N.graph.target g) w → x ∉ lineages (inj w)) (r : QuartetTree X) :
    cherryMass N θ ρ inj r =
      Real.exp (-θ.length e) * cherryMass N θ ρ (liftInj N e inj (P.image fun x => ({x} : Finset X))) r +
        (1 - Real.exp (-θ.length e)) * cherryMass N θ ρ (liftInj N e inj (insert P (P.image fun x => ({x} : Finset X)))) r := by
  rw [cherryMass_eq_meanOn_below hN hθ hρ hinj hdom r, ← insert_erase (target_mem_belowSet (N := N) e),
    meanOn_insert (downClosed_belowSet_erase hN e) (notMem_erase _ _) (fun f hf => target_mem_belowSet_erase hN hf)]
  refine meanOn_eq_const hN hθ.isNormalized hρ.1 hinj (downClosed_belowSet_erase hN e) (fun h => root_notMem_belowSet hN e (mem_of_mem_erase h)) fun bot top h => ?_
  have hγ : θ.inheritance e = 1 := hθ.2.2.1 e (isTreeArc_of_unique hu)
  have hS : e ∈ arcsInto N (N.graph.target e) := mem_arcsInto.2 rfl
  unfold stepKernel
  rw [arriving_eq_singletons hN hinj hdom hP2 hP hno hsplit h,
    stepOf_unique_two (N := N) (θ := θ) (ρ := ρ) (e := e) hρ.1 rfl hu hγ hP2 _ (ow_dep (arcsInto N (N.graph.target e)) top fun T => cherryMass N θ ρ (liftInj N e inj (T e)) r)]
  simp only [ow_of_mem hS]

/-! ### The concordance factor at an edge -/

/-- Lineages at one node: three of the taxa, and the fourth anywhere. -/
theorem cherryMass_lift_third (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {q P : Finset X} (hq : #q = 4) (hPq : P ⊆ q) {f : E} {c d : X} (hcq : c ∈ q) (hcP : c ∉ P) (hdq : d ∈ q) (hdP : d ∉ P) (hcd : c ≠ d)
    (hall : ∀ x ∈ q, x = c ∨ x = d ∨ x ∈ P) (hcf : N.Dominates f c) (hdf : ¬ N.IsBelow f d) {r : QuartetTree X} (hr : r ∈ treesOn q) :
    cherryMass N θ ρ (hubInj N q P (N.graph.source f)) r = 1 / 3 := by
  have hv := validInj_hubInj (N := N) q P (N.graph.source f)
  have hvB : ∀ u ∈ belowSet N f, u ≠ N.graph.source f := fun u hu h => source_notMem_belowSet hN f (by rw [← h]; exact hu)
  have honly : ∀ u ∈ belowSet N f, ∀ x ∈ lineages (hubInj N q P (N.graph.source f) u), x = c ∧ N.leaf x = u := by
    intro u hu x hx
    rcases (mem_lineages_hubInj x).1 hx with ⟨hxq, rfl⟩ | ⟨h, -⟩
    · obtain ⟨hxq', hxP⟩ := mem_sdiff.1 hxq
      rcases hall x hxq' with rfl | rfl | hx'
      · exact ⟨rfl, rfl⟩
      · exact absurd (mem_belowSet.1 hu) hdf
      · exact absurd hx' hxP
    · exact absurd h (hvB u hu)
  have hdom : DominatedInj N f (hubInj N q P (N.graph.source f)) := by
    rintro u hu ⟨A, hA⟩
    obtain ⟨z, hz⟩ := hv.good u |>.1.1 A hA
    obtain ⟨rfl, rfl⟩ := honly u hu z (mem_lineages.2 ⟨A, hA, hz⟩)
    exact hcf
  have hb := hcf.isBelow hN
  have hy : ∃ u ∈ belowSet N f, c ∈ lineages (hubInj N q P (N.graph.source f) u) :=
    ⟨N.leaf c, mem_belowSet.2 hb, (mem_lineages_hubInj c).2 (Or.inl ⟨mem_sdiff.2 ⟨hcq, hcP⟩, rfl⟩)⟩
  have hD : ∀ G, injDist N θ ρ (hubInj N q P (N.graph.source f)) G = injDist N θ ρ (liftInj N f (hubInj N q P (N.graph.source f)) {{c}}) G := fun G =>
    injDist_eq_lift_singleton hN hθ hρ hv hdom hy (fun u hu x hx => (honly u hu x hx).1) G
  have hlift := liftInj_hubInj (N := N) (q := q) (T := P) (L := {c}) (v := N.graph.source f) (f := f) hN rfl (fun x hx => mem_singleton.1 hx ▸ hb) (fun x hxq hxP hxL hbx => by
    rcases hall x hxq with rfl | rfl | hx'
    · exact hxL (mem_singleton_self _)
    · exact hdf hbx
    · exact hxP hx')
  rw [image_singleton] at hlift
  have hE : cherryMass N θ ρ (hubInj N q P (N.graph.source f)) r = cherryMass N θ ρ (hubInj N q (P ∪ {c}) (N.graph.source f)) r := by
    unfold cherryMass
    refine sum_congr rfl fun H _ => ?_
    rw [hD H, hlift]
  rw [hE]
  refine cherryMass_hubInj_eq_third hN hθ hρ hq (union_subset hPq (singleton_subset_iff.2 hcq)) _ hdq (fun x hx hxd => ?_) hr
  rcases hall x hx with rfl | rfl | hx'
  · exact mem_union_right _ (mem_singleton_self _)
  · exact absurd rfl hxd
  · exact mem_union_left _ hx'

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A taxon has nothing below it. -/
theorem eq_of_leaf_reaches (hN : N.IsPhylogenetic) {x : X} {w : V} (h : N.graph.Reaches (N.leaf x) w) : w = N.leaf x := by
  have : Finite E := hN.finite_arcs
  have hno : ∀ f, N.graph.source f ≠ N.leaf x := (N.graph.outdegree_eq_zero_iff _).mp ((hN.leaves _).mpr ⟨x, rfl⟩)
  rcases Relation.ReflTransGen.cases_head h with h' | ⟨c, ⟨f, hf, -⟩, -⟩
  · exact h'.symm
  · exact absurd hf (hno f)

omit [Fintype V] [Fintype E] in
/-- What `cherryMass_step` asks of the taxa `P` below an edge. -/
theorem no_inj_target (hN : N.IsPhylogenetic) {q : Finset X} {e : E} {a b : X} (hab : a ≠ b) (ha : N.IsBelow e a) (hb : N.IsBelow e b) : taxaInj N q (N.graph.target e) = ∅ := by
  unfold taxaInj
  rw [image_eq_empty]
  refine filter_false_of_mem fun x _ hx => ?_
  rw [IsBelow, ← hx.2] at ha hb
  exact hab (hN.leaf_injective ((eq_of_leaf_reaches hN ha).trans (eq_of_leaf_reaches hN hb).symm))

/-- **`CF_{ab|cd} = 1 - (2/3) exp (-ℓ e)`, for an edge `e` with `a, b` in different branches below it, `c` in the other branch at its top, and `d` elsewhere.** In general, for the three trees. -/
theorem nmscCF_of_edge (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) {e f : E} (hs : N.graph.source f = N.graph.source e) (hu : ∀ g, N.graph.target g = N.graph.target e → g = e) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hda : N.Dominates e a) (hdb : N.Dominates e b) (hsplit : ∀ g, N.graph.source g = N.graph.target e → ¬ (N.IsBelow g a ∧ N.IsBelow g b)) (hcn : ¬ N.IsBelow e c) (hdn : ¬ N.IsBelow e d)
    (hcf : N.Dominates f c) (hdf : ¬ N.IsBelow f d) {r : QuartetTree X} (hr : r.taxa = {a, b, c, d}) :
    nmscCF N θ 0 r = Real.exp (-θ.length e) * (1 / 3) + (1 - Real.exp (-θ.length e)) * (if ({a, b} : Finset X) ∈ r.val then 1 else 0) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  set q : Finset X := {a, b, c, d} with hqdef
  set P : Finset X := {a, b} with hPdef
  have hP2 : #P = 2 := card_pair hab
  have hPq : P ⊆ q := by
    intro x hx
    simp only [hPdef, hqdef, mem_insert, mem_singleton] at hx ⊢
    tauto
  have hmem : ∀ x, x ∈ q ↔ x = a ∨ x = b ∨ x = c ∨ x = d := fun x => by simp [hqdef]
  have hv := validInj_taxaInj (N := N) q
  have hba := hda.isBelow hN
  have hbb := hdb.isBelow hN
  have hdom : DominatedInj N e (taxaInj N q) := dominatedInj_taxaInj fun x hx hbx => by
    rcases (hmem x).1 hx with rfl | rfl | rfl | rfl
    · exact hda
    · exact hdb
    · exact absurd hbx hcn
    · exact absurd hbx hdn
  have hPiff : ∀ x, (∃ w ∈ belowSet N e, x ∈ lineages (taxaInj N q w)) ↔ x ∈ P := fun x => by
    rw [exists_mem_below_taxaInj]
    simp only [hPdef, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hx, hbx⟩
      rcases (hmem x).1 hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hbx hcn
      · exact absurd hbx hdn
    · rintro (rfl | rfl)
      · exact ⟨(hmem _).2 (Or.inl rfl), hba⟩
      · exact ⟨(hmem _).2 (Or.inr (Or.inl rfl)), hbb⟩
  have hsp : ∀ g, N.graph.source g = N.graph.target e → ∃ x ∈ P, ∀ w, N.graph.Reaches (N.graph.target g) w → x ∉ lineages (taxaInj N q w) := by
    intro g hg
    have hn := hsplit g hg
    by_cases hga : N.IsBelow g a
    · refine ⟨b, by simp [hPdef], fun w hw hx => hn ⟨hga, ?_⟩⟩
      obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hx
      exact hw
    · refine ⟨a, by simp [hPdef], fun w hw hx => hga ?_⟩
      obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hx
      exact hw
  rw [nmscCF_eq_cherryMass hN hθ hρ r, hr, cherryMass_step hN hθ hρ hv hdom hP2 hu hPiff (no_inj_target hN hab hba hbb) hsp r]
  -- the cherry decides
  have hB : cherryMass N θ 0 (liftInj N e (taxaInj N q) (insert P (P.image fun x => ({x} : Finset X)))) r = if P ∈ r.val then 1 else 0 := by
    have hlin := FourCycle.lineages_insert_pair (Subset.refl P)
    have hl : ValidInj (liftInj N e (taxaInj N q) (insert P (P.image fun x => ({x} : Finset X)))) :=
      validInj_liftInj hv (FourCycle.isGoodForest_insert_pair (Subset.refl P) hP2) fun x hx => (hPiff x).mpr (hlin ▸ hx)
    have hC : P ∈ liftInj N e (taxaInj N q) (insert P (P.image fun x => ({x} : Finset X))) (N.graph.source e) := by
      unfold liftInj
      exact mem_union_right _ (by simp)
    exact cherryMass_of_mem hN hθ hρ hl hC hP2 (by rw [hr]; exact hPq)
  -- otherwise three lineages at the top
  have hA : cherryMass N θ 0 (liftInj N e (taxaInj N q) (P.image fun x => ({x} : Finset X))) r = 1 / 3 := by
    have hlift := liftInj_hubInj (N := N) (q := q) (T := ∅) (L := P) (v := N.graph.source e) (f := e) hN rfl (fun x hx => ((hPiff x).mpr hx).elim fun w hw => by
      obtain ⟨hwb, hxw⟩ := hw
      obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxw
      exact mem_belowSet.1 hwb) (fun x hxq _ hxP hbx => hxP ((hPiff x).mp ((exists_mem_below_taxaInj x).mpr ⟨hxq, hbx⟩)))
    rw [hubInj_empty, empty_union] at hlift
    rw [hlift, ← hs]
    refine cherryMass_lift_third hN hθ hρ h hPq (c := c) (d := d) ((hmem _).2 (Or.inr (Or.inr (Or.inl rfl)))) (by simp [hPdef, hac.symm, hbc.symm]) ((hmem _).2 (Or.inr (Or.inr (Or.inr rfl)))) (by simp [hPdef, had.symm, hbd.symm]) hcd (fun x hx => ?_) hcf hdf (mem_treesOn.2 hr)
    rcases (hmem x).1 hx with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (by simp [hPdef]))
    · exact Or.inr (Or.inr (by simp [hPdef]))
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  rw [hA, hB]

/-- **`CF_{ab|cd} = 1 - (2/3) exp (-(ℓ e₀ + ℓ e₁))`, for the two edges `e₀`, `e₁` at a node, with `a, b` in different branches below `e₀`, and `c, d` in different branches below `e₁`.** The two edges become one edge of `𝒩⁻` if the node is the root of `𝒩⊕`. -/
theorem nmscCF_of_root (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) {e₀ e₁ : E} (hs : N.graph.source e₁ = N.graph.source e₀) (hu₀ : ∀ g, N.graph.target g = N.graph.target e₀ → g = e₀) (hu₁ : ∀ g, N.graph.target g = N.graph.target e₁ → g = e₁)
    {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (hda : N.Dominates e₀ a) (hdb : N.Dominates e₀ b) (hsplit₀ : ∀ g, N.graph.source g = N.graph.target e₀ → ¬ (N.IsBelow g a ∧ N.IsBelow g b)) (hcn : ¬ N.IsBelow e₀ c) (hdn : ¬ N.IsBelow e₀ d)
    (hdc : N.Dominates e₁ c) (hdd : N.Dominates e₁ d) (hsplit₁ : ∀ g, N.graph.source g = N.graph.target e₁ → ¬ (N.IsBelow g c ∧ N.IsBelow g d)) (han : ¬ N.IsBelow e₁ a) (hbn : ¬ N.IsBelow e₁ b) :
    nmscCF N θ 0 (quartetTree a b c d h) = 1 - 2 / 3 * Real.exp (-(θ.length e₀ + θ.length e₁)) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  set r := quartetTree a b c d h with hrdef
  have hr : r.taxa = {a, b, c, d} := quartetTree_taxa _ _ _ _ _
  set q : Finset X := {a, b, c, d} with hqdef
  set P : Finset X := {a, b} with hPdef
  set Q : Finset X := {c, d} with hQdef
  have hP2 : #P = 2 := card_pair hab
  have hQ2 : #Q = 2 := card_pair hcd
  have hPq : P ⊆ q := by
    intro x hx
    simp only [hPdef, hqdef, mem_insert, mem_singleton] at hx ⊢
    tauto
  have hQq : Q ⊆ q := by
    intro x hx
    simp only [hQdef, hqdef, mem_insert, mem_singleton] at hx ⊢
    tauto
  have hmem : ∀ x, x ∈ q ↔ x = a ∨ x = b ∨ x = c ∨ x = d := fun x => by simp [hqdef, hQdef]
  have hPval : P ∈ r.val := by simp [hrdef, hPdef, quartetTree_val]
  have hQval : Q ∈ r.val := by simp [hrdef, hQdef, quartetTree_val]
  have hv := validInj_taxaInj (N := N) q
  have hba := hda.isBelow hN
  have hbb := hdb.isBelow hN
  have hbc' := hdc.isBelow hN
  have hbd' := hdd.isBelow hN
  have hdom : DominatedInj N e₀ (taxaInj N q) := dominatedInj_taxaInj fun x hx hbx => by
    rcases (hmem x).1 hx with rfl | rfl | rfl | rfl
    · exact hda
    · exact hdb
    · exact absurd hbx hcn
    · exact absurd hbx hdn
  have hPiff : ∀ x, (∃ w ∈ belowSet N e₀, x ∈ lineages (taxaInj N q w)) ↔ x ∈ P := fun x => by
    rw [exists_mem_below_taxaInj]
    simp only [hPdef, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hx, hbx⟩
      rcases (hmem x).1 hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hbx hcn
      · exact absurd hbx hdn
    · rintro (rfl | rfl)
      · exact ⟨(hmem _).2 (Or.inl rfl), hba⟩
      · exact ⟨(hmem _).2 (Or.inr (Or.inl rfl)), hbb⟩
  have hsp : ∀ g, N.graph.source g = N.graph.target e₀ → ∃ x ∈ P, ∀ w, N.graph.Reaches (N.graph.target g) w → x ∉ lineages (taxaInj N q w) := by
    intro g hg
    have hn := hsplit₀ g hg
    by_cases hga : N.IsBelow g a
    · refine ⟨b, by simp [hPdef], fun w hw hx => hn ⟨hga, ?_⟩⟩
      obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hx
      exact hw
    · refine ⟨a, by simp [hPdef], fun w hw hx => hga ?_⟩
      obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hx
      exact hw
  rw [nmscCF_eq_cherryMass hN hθ hρ r, hr, cherryMass_step hN hθ hρ hv hdom hP2 hu₀ hPiff (no_inj_target hN hab hba hbb) hsp r]
  have hB : cherryMass N θ 0 (liftInj N e₀ (taxaInj N q) (insert P (P.image fun x => ({x} : Finset X)))) r = 1 := by
    have hlin := FourCycle.lineages_insert_pair (Subset.refl P)
    have hl : ValidInj (liftInj N e₀ (taxaInj N q) (insert P (P.image fun x => ({x} : Finset X)))) :=
      validInj_liftInj hv (FourCycle.isGoodForest_insert_pair (Subset.refl P) hP2) fun x hx => (hPiff x).mpr (hlin ▸ hx)
    have hC : P ∈ liftInj N e₀ (taxaInj N q) (insert P (P.image fun x => ({x} : Finset X))) (N.graph.source e₀) := by
      unfold liftInj
      exact mem_union_right _ (by simp)
    rw [cherryMass_of_mem hN hθ hρ hl hC hP2 (by rw [hr]; exact hPq), ite_eq_left hPval]
  have hlift := liftInj_hubInj (N := N) (q := q) (T := ∅) (L := P) (v := N.graph.source e₀) (f := e₀) hN rfl (fun x hx => ((hPiff x).mpr hx).elim fun w hw => by
    obtain ⟨hwb, hxw⟩ := hw
    obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxw
    exact mem_belowSet.1 hwb) (fun x hxq _ hxP hbx => hxP ((hPiff x).mp ((exists_mem_below_taxaInj x).mpr ⟨hxq, hbx⟩)))
  rw [hubInj_empty, empty_union] at hlift
  rw [hlift, hB]
  -- the second edge
  have hv₁ := validInj_hubInj (N := N) q P (N.graph.source e₀)
  have hvB : ∀ u ∈ belowSet N e₁, u ≠ N.graph.source e₀ := fun u hu he => source_notMem_belowSet hN e₁ (by rw [hs, ← he]; exact hu)
  have honly : ∀ u ∈ belowSet N e₁, ∀ x ∈ lineages (hubInj N q P (N.graph.source e₀) u), x ∈ Q ∧ N.leaf x = u := by
    intro u hu x hx
    rcases (mem_lineages_hubInj x).1 hx with ⟨hxq, rfl⟩ | ⟨he, -⟩
    · obtain ⟨hxq', hxP⟩ := mem_sdiff.1 hxq
      refine ⟨?_, rfl⟩
      rcases (hmem x).1 hxq' with rfl | rfl | rfl | rfl
      · exact absurd (by simp [hPdef]) hxP
      · exact absurd (by simp [hPdef]) hxP
      · simp [hQdef]
      · simp [hQdef]
    · exact absurd he (hvB u hu)
  have hdom₁ : DominatedInj N e₁ (hubInj N q P (N.graph.source e₀)) := by
    rintro u hu ⟨A, hA⟩
    obtain ⟨z, hz⟩ := hv₁.good u |>.1.1 A hA
    obtain ⟨hzQ, rfl⟩ := honly u hu z (mem_lineages.2 ⟨A, hA, hz⟩)
    simp only [hQdef, mem_insert, mem_singleton] at hzQ
    rcases hzQ with rfl | rfl
    · exact hdc
    · exact hdd
  have hQP : ∀ {x}, x ∈ Q → x ∈ q \ P := fun hx => by
    simp only [hQdef, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_sdiff.2 ⟨(hmem _).2 (Or.inr (Or.inr (Or.inl rfl))), by simp [hPdef, hac.symm, hbc.symm]⟩
    · exact mem_sdiff.2 ⟨(hmem _).2 (Or.inr (Or.inr (Or.inr rfl))), by simp [hPdef, had.symm, hbd.symm]⟩
  have hQbel : ∀ {x}, x ∈ Q → N.IsBelow e₁ x := fun hx => by
    simp only [hQdef, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hbc'
    · exact hbd'
  have hQiff : ∀ x, (∃ w ∈ belowSet N e₁, x ∈ lineages (hubInj N q P (N.graph.source e₀) w)) ↔ x ∈ Q := fun x =>
    ⟨fun ⟨w, hw, hx⟩ => (honly w hw x hx).1, fun hx => ⟨N.leaf x, mem_belowSet.2 (hQbel hx), (mem_lineages_hubInj x).2 (Or.inl ⟨hQP hx, rfl⟩)⟩⟩
  have hno₁ : hubInj N q P (N.graph.source e₀) (N.graph.target e₁) = ∅ := by
    have htn : N.graph.target e₁ ≠ N.graph.source e₀ := hvB _ (target_mem_belowSet e₁)
    unfold hubInj
    rw [ite_eq_right htn, union_empty]
    exact no_inj_target hN hcd hbc' hbd'
  have hsp₁ : ∀ g, N.graph.source g = N.graph.target e₁ → ∃ x ∈ Q, ∀ w, N.graph.Reaches (N.graph.target g) w → x ∉ lineages (hubInj N q P (N.graph.source e₀) w) := by
    intro g hg
    have hn := hsplit₁ g hg
    have hbg : ∀ w, N.graph.Reaches (N.graph.target g) w → ∀ x ∈ lineages (hubInj N q P (N.graph.source e₀) w), N.leaf x = w := by
      intro w hw x hx
      have hwB : w ∈ belowSet N e₁ := mem_belowSet.2 (Relation.ReflTransGen.head ⟨g, hg, rfl⟩ hw)
      exact (honly w hwB x hx).2
    by_cases hgc : N.IsBelow g c
    · refine ⟨d, by simp [hQdef], fun w hw hx => hn ⟨hgc, ?_⟩⟩
      have := hbg w hw d hx
      rw [IsBelow, this]
      exact hw
    · refine ⟨c, by simp [hQdef], fun w hw hx => hgc ?_⟩
      have := hbg w hw c hx
      rw [IsBelow, this]
      exact hw
  rw [cherryMass_step hN hθ hρ hv₁ hdom₁ hQ2 hu₁ hQiff hno₁ hsp₁ r]
  have hB₁ : cherryMass N θ 0 (liftInj N e₁ (hubInj N q P (N.graph.source e₀)) (insert Q (Q.image fun x => ({x} : Finset X)))) r = 1 := by
    have hlin := FourCycle.lineages_insert_pair (Subset.refl Q)
    have hl : ValidInj (liftInj N e₁ (hubInj N q P (N.graph.source e₀)) (insert Q (Q.image fun x => ({x} : Finset X)))) :=
      validInj_liftInj hv₁ (FourCycle.isGoodForest_insert_pair (Subset.refl Q) hQ2) fun x hx => (hQiff x).mpr (hlin ▸ hx)
    have hC : Q ∈ liftInj N e₁ (hubInj N q P (N.graph.source e₀)) (insert Q (Q.image fun x => ({x} : Finset X))) (N.graph.source e₁) := by
      unfold liftInj
      exact mem_union_right _ (by simp)
    rw [cherryMass_of_mem hN hθ hρ hl hC hQ2 (by rw [hr]; exact hQq), ite_eq_left hQval]
  have hA₁ : cherryMass N θ 0 (liftInj N e₁ (hubInj N q P (N.graph.source e₀)) (Q.image fun x => ({x} : Finset X))) r = 1 / 3 := by
    have hl := liftInj_hubInj (N := N) (q := q) (T := P) (L := Q) (v := N.graph.source e₀) (f := e₁) hN hs (fun x hx => hQbel hx) (fun x hxq hxP hxQ hbx => hxQ (by
      rcases (hmem x).1 hxq with rfl | rfl | rfl | rfl
      · exact absurd hbx han
      · exact absurd hbx hbn
      · simp [hQdef]
      · simp [hQdef]))
    rw [hl]
    refine cherryMass_hubInj_eq_third hN hθ hρ h (union_subset hPq hQq) _ (a := d) ((hmem _).2 (Or.inr (Or.inr (Or.inr rfl)))) (fun x hx _ => ?_) (mem_treesOn.2 hr)
    rcases (hmem x).1 hx with rfl | rfl | rfl | rfl
    · exact mem_union_left _ (by simp [hPdef])
    · exact mem_union_left _ (by simp [hPdef])
    · exact mem_union_right _ (by simp [hQdef])
    · exact mem_union_right _ (by simp [hQdef])
  rw [hA₁, hB₁, neg_add, Real.exp_add]
  ring

/-! ### Edges between trivial blobs -/

section Blobs

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A cut edge has what's below it dominated. -/
theorem dominates_of_isBridge (hN : N.IsPhylogenetic) {e : E} {x : X} (hb : N.graph.underlying.IsBridge e) (h : N.IsBelow e x) : N.Dominates e x := by
  intro hav
  rw [N.graph.isBridge_iff_not_walks_delete, Set.compl_eq_univ_sdiff] at hb
  refine hb ?_
  have h₁ := walks_diff_source hN e (hN.root_reaches _)
  have h₂ : N.graph.Walks (Set.univ \ {e}) N.root (N.leaf x) := by
    refine Relation.ReflTransGen.mono ?_ _ _ hav
    rintro _ _ ⟨f, hf, hs, ht⟩
    exact ⟨f, ⟨Set.mem_univ f, hf⟩, Or.inl ⟨hs, ht⟩⟩
  have h₃ := walks_diff_target hN e h
  exact (N.graph.walks_symm h₁).trans (h₂.trans (N.graph.walks_symm h₃))

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A taxon below a cut edge is not below another edge from the same node. -/
theorem not_isBelow_of_sibling (hN : N.IsPhylogenetic) {g g' : E} {x : X} (hne : g ≠ g') (hs : N.graph.source g = N.graph.source g') (hb : N.graph.underlying.IsBridge g') (h' : N.IsBelow g' x) : ¬ N.IsBelow g x := by
  intro h
  rw [N.graph.isBridge_iff_not_walks_delete, Set.compl_eq_univ_sdiff] at hb
  refine hb ?_
  have h₁ : N.graph.Walks (Set.univ \ {g'}) (N.graph.source g') (N.graph.target g) := by
    rw [← hs]
    exact Relation.ReflTransGen.single ⟨g, ⟨Set.mem_univ g, hne⟩, Or.inl ⟨rfl, rfl⟩⟩
  have h₂ : N.graph.Walks (Set.univ \ {g'}) (N.graph.target g) (N.leaf x) :=
    walks_diff_of_reaches h fun hc => not_reaches_target_source hN.acyclic g (hs ▸ hc.1)
  have h₃ := walks_diff_target hN g' h'
  exact h₁.trans (h₂.trans (N.graph.walks_symm h₃))

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- The edges at a node alone in its blob are cut edges. -/
theorem isBridge_of_isTrivialBlob (hN : N.IsPhylogenetic) {w : V} (hw : IsTrivialBlob N.graph (blobOf N.graph w)) {f : E} (hf : N.graph.source f = w ∨ N.graph.target f = w) : N.graph.underlying.IsBridge f := by
  by_contra hb
  have hst : blobOf N.graph (N.graph.source f) = blobOf N.graph (N.graph.target f) := N.graph.quotient_eq_of_not_isBridge hb
  obtain ⟨v, hv⟩ := hw
  have hmem : ∀ u, blobOf N.graph u = blobOf N.graph w → u = v := fun u hu => by
    have : u ∈ blobNodes N.graph (blobOf N.graph w) := hu
    rwa [hv] at this
  rcases hf with rfl | rfl
  · exact NMSC.source_ne_target hN f ((hmem _ rfl).trans (hmem _ hst.symm).symm)
  · exact NMSC.source_ne_target hN f ((hmem _ hst).trans (hmem _ rfl).symm)

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- **A node alone in its blob, other than the root and the taxa, is a tree node**: a hybrid edge is not a cut edge. -/
theorem exists_edges_of_isTrivialBlob (hN : IsBinaryNetwork N) {w : V} (hw : IsTrivialBlob N.graph (blobOf N.graph w)) (hr : w ≠ N.root) (hl : ∀ x, N.leaf x ≠ w) :
    ∃ p g₁ g₂, N.graph.target p = w ∧ (∀ f, N.graph.target f = w → f = p) ∧ N.graph.source g₁ = w ∧ N.graph.source g₂ = w ∧ g₁ ≠ g₂ ∧ (∀ f, N.graph.source f = w → f = g₁ ∨ f = g₂) := by
  have hP := hN.isPhylogenetic
  rcases hN.node_cases w with h | ⟨x, h⟩ | h | h
  · exact absurd h hr
  · exact absurd h (hl x)
  · obtain ⟨p, hp⟩ := (N.graph.indegree_eq_one_iff _).mp h.1
    obtain ⟨g₁, g₂, hne, hset⟩ := Set.ncard_eq_two.mp h.2
    have hmem : ∀ f, N.graph.source f = w ↔ f = g₁ ∨ f = g₂ := fun f => by
      have := Set.ext_iff.mp hset f
      simpa using this
    exact ⟨p, g₁, g₂, (hp p).mpr rfl, fun f hf => (hp f).mp hf, (hmem g₁).mpr (Or.inl rfl), (hmem g₂).mpr (Or.inr rfl), hne, fun f hf => (hmem f).mp hf⟩
  · exfalso
    obtain ⟨f, f', -, hpar⟩ := IsHybridNode.exists_parents h
    have hft : N.graph.target f = w := (hpar f).mpr (Or.inl rfl)
    refine InPassing.not_isBridge_of_isHybridEdge hN (e := f) ?_ (isBridge_of_isTrivialBlob hP hw (Or.inr hft))
    change IsHybridNode N (N.graph.target f)
    rw [hft]
    exact h

/-- The value of the concordance factor gives the length. -/
theorem neg_log_eq {t F : ℝ} (hF : F = Real.exp (-t) * (1 / 3) + (1 - Real.exp (-t)) * 1) : t = -Real.log (3 / 2 * (1 - F)) := by
  have : 3 / 2 * (1 - F) = Real.exp (-t) := by
    rw [hF]
    ring
  rw [this, Real.log_exp, neg_neg]

/-- **"For edges between trivial blobs, it is straightforward to see that edge lengths are identifiable"** (`a:claim:trivial-edges`, Section 5), on `𝒩⁺`, for an internal edge below the LSA other than the two at the LSA: its length is a function of a `CF`, which does not depend on the parameters. -/
theorem edge_length_eq (hN : IsBinaryNetwork N) (hX : Nontrivial X) {e : E} (hu : IsTrivialBlob N.graph (blobOf N.graph (N.graph.target e))) (hv : IsTrivialBlob N.graph (blobOf N.graph (N.graph.source e)))
    (hl : ∀ x, N.leaf x ≠ N.graph.target e) (hbelow : N.graph.Reaches (lsaNode hN hX) (N.graph.source e)) (hne : N.graph.source e ≠ lsaNode hN hX) :
    ∃ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), ∀ θ : MetricData E, N.IsMetric θ → θ.length e = -Real.log (3 / 2 * (1 - nmscCF N θ 0 (quartetTree a b c d h))) := by
  have hP := hN.isPhylogenetic
  have hr : N.graph.source e ≠ N.root := fun h => hne (eq_of_reaches_of_reaches hP.acyclic hbelow (h ▸ hP.root_reaches _)).symm
  have hlv : ∀ x, N.leaf x ≠ N.graph.source e := fun x h =>
    (N.graph.outdegree_eq_zero_iff _).mp ((hP.leaves _).mpr ⟨x, rfl⟩) e h.symm
  obtain ⟨p₀, g₁, g₂, -, hup, hg₁, hg₂, hneg, hallg⟩ := exists_edges_of_isTrivialBlob hN hu (target_ne_root hP e) hl
  obtain ⟨p, h₁, h₂, hpt, -, hs₁, hs₂, hne₁, -⟩ := exists_edges_of_isTrivialBlob hN hv hr hlv
  have hu' : ∀ f, N.graph.target f = N.graph.target e → f = e := fun f hf => (hup f hf).trans (hup e rfl).symm
  obtain ⟨f, hfe, hsf⟩ : ∃ f, f ≠ e ∧ N.graph.source f = N.graph.source e := by
    by_cases he₁ : h₁ = e
    · exact ⟨h₂, fun h => hne₁ (he₁.trans h.symm), hs₂⟩
    · exact ⟨h₁, he₁, hs₁⟩
  have hbe := isBridge_of_isTrivialBlob hP hu (Or.inr rfl)
  have hbf := isBridge_of_isTrivialBlob hP hv (Or.inl hsf)
  have hbp := isBridge_of_isTrivialBlob hP hv (Or.inr hpt)
  have hbg₁ := isBridge_of_isTrivialBlob hP hu (Or.inl hg₁)
  have hbg₂ := isBridge_of_isTrivialBlob hP hu (Or.inl hg₂)
  obtain ⟨a, ha⟩ := exists_reaches_leaf hP (N.graph.target g₁)
  obtain ⟨b, hb⟩ := exists_reaches_leaf hP (N.graph.target g₂)
  obtain ⟨c, hc⟩ := exists_reaches_leaf hP (N.graph.target f)
  -- a taxon on the side of the root
  have hpI : p ∈ incidentCuts N.graph Set.univ (N.graph.source e) := ⟨isCutIn_univ_iff.mpr hbp, Or.inr (by rw [hpt]; exact .refl)⟩
  have htp : SameBlobIn N.graph Set.univ (N.graph.source e) (N.graph.target p) := by
    rw [hpt]
    exact .refl
  obtain ⟨d, hd⟩ : ∃ d, LeadsTo N.graph Set.univ (N.graph.source e) p (N.leaf d) := by
    by_contra hno
    push Not at hno
    have hst := isStableAncestor_target hP hpI htp hno
    have hr₁ := (lsa_spec hP Set.univ Set.univ_nonempty).2 _ hst
    rw [hpt] at hr₁
    exact hne (eq_of_reaches_of_reaches hP.acyclic hr₁ hbelow)
  have hdv : ¬ N.graph.Reaches (N.graph.source e) (N.leaf d) := fun h => hd.2 (by
    rw [← hpt] at h ⊢
    exact walks_diff_target hP p h)
  have hstep : ∀ {g x}, N.graph.source g = N.graph.target e → N.graph.Reaches (N.graph.target g) (N.leaf x) → N.IsBelow e x := fun hg hx => Relation.ReflTransGen.head ⟨_, hg, rfl⟩ hx
  have hba : N.IsBelow e a := hstep hg₁ ha
  have hbb : N.IsBelow e b := hstep hg₂ hb
  have hdn : ¬ N.IsBelow e d := fun h => hdv (Relation.ReflTransGen.head ⟨e, rfl, rfl⟩ h)
  have hdf : ¬ N.IsBelow f d := fun h => hdv (Relation.ReflTransGen.head ⟨f, hsf, rfl⟩ h)
  have hcn : ¬ N.IsBelow e c := not_isBelow_of_sibling hP hfe.symm hsf.symm hbf hc
  have hbg : ¬ N.IsBelow g₁ b := not_isBelow_of_sibling hP hneg (hg₁.trans hg₂.symm) hbg₂ hb
  have hag : ¬ N.IsBelow g₂ a := not_isBelow_of_sibling hP hneg.symm (hg₂.trans hg₁.symm) hbg₁ ha
  have hsplit : ∀ g, N.graph.source g = N.graph.target e → ¬ (N.IsBelow g a ∧ N.IsBelow g b) := by
    rintro g hg ⟨h₃, h₄⟩
    rcases hallg g hg with rfl | rfl
    · exact hbg h₄
    · exact hag h₃
  have hab : a ≠ b := fun h' => hbg (h' ▸ ha)
  have hac : a ≠ c := fun h' => hcn (h' ▸ hba)
  have had : a ≠ d := fun h' => hdn (h' ▸ hba)
  have hbc : b ≠ c := fun h' => hcn (h' ▸ hbb)
  have hbd : b ≠ d := fun h' => hdn (h' ▸ hbb)
  have hcd : c ≠ d := fun h' => hdf (h' ▸ hc)
  have h := TreeMetric.card_four_of_ne hab hac had hbc hbd hcd
  refine ⟨a, b, c, d, h, fun θ hθ => neg_log_eq ?_⟩
  rw [nmscCF_of_edge hP hθ hsf hu' h (dominates_of_isBridge hP hbe hba) (dominates_of_isBridge hP hbe hbb) hsplit hcn hdn (dominates_of_isBridge hP hbf hc) hdf (quartetTree_taxa _ _ _ _ _)]
  simp [quartetTree_val]

/-- **The same, for the two edges from one node, which at the root of `𝒩⊕` become one edge of `𝒩⁻`** (`a:claim:trivial-edges`, Section 5). Only the sum of the two lengths counts. -/
theorem root_length_eq (hN : IsBinaryNetwork N) {e₀ e₁ : E} (hs : N.graph.source e₁ = N.graph.source e₀) (hne : e₀ ≠ e₁) (h₀ : IsTrivialBlob N.graph (blobOf N.graph (N.graph.target e₀))) (h₁ : IsTrivialBlob N.graph (blobOf N.graph (N.graph.target e₁)))
    (hl₀ : ∀ x, N.leaf x ≠ N.graph.target e₀) (hl₁ : ∀ x, N.leaf x ≠ N.graph.target e₁) :
    ∃ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), ∀ θ : MetricData E, N.IsMetric θ → θ.length e₀ + θ.length e₁ = -Real.log (3 / 2 * (1 - nmscCF N θ 0 (quartetTree a b c d h))) := by
  have hP := hN.isPhylogenetic
  obtain ⟨p₀, g₁, g₂, -, hup₀, hg₁, hg₂, hneg, hallg⟩ := exists_edges_of_isTrivialBlob hN h₀ (target_ne_root hP e₀) hl₀
  obtain ⟨p₁, k₁, k₂, -, hup₁, hk₁, hk₂, hnek, hallk⟩ := exists_edges_of_isTrivialBlob hN h₁ (target_ne_root hP e₁) hl₁
  have hu₀ : ∀ f, N.graph.target f = N.graph.target e₀ → f = e₀ := fun f hf => (hup₀ f hf).trans (hup₀ e₀ rfl).symm
  have hu₁ : ∀ f, N.graph.target f = N.graph.target e₁ → f = e₁ := fun f hf => (hup₁ f hf).trans (hup₁ e₁ rfl).symm
  have hb₀ := isBridge_of_isTrivialBlob hP h₀ (Or.inr rfl)
  have hb₁ := isBridge_of_isTrivialBlob hP h₁ (Or.inr rfl)
  have hbg₁ := isBridge_of_isTrivialBlob hP h₀ (Or.inl hg₁)
  have hbg₂ := isBridge_of_isTrivialBlob hP h₀ (Or.inl hg₂)
  have hbk₁ := isBridge_of_isTrivialBlob hP h₁ (Or.inl hk₁)
  have hbk₂ := isBridge_of_isTrivialBlob hP h₁ (Or.inl hk₂)
  obtain ⟨a, ha⟩ := exists_reaches_leaf hP (N.graph.target g₁)
  obtain ⟨b, hb⟩ := exists_reaches_leaf hP (N.graph.target g₂)
  obtain ⟨c, hc⟩ := exists_reaches_leaf hP (N.graph.target k₁)
  obtain ⟨d, hd⟩ := exists_reaches_leaf hP (N.graph.target k₂)
  have hba : N.IsBelow e₀ a := Relation.ReflTransGen.head ⟨_, hg₁, rfl⟩ ha
  have hbb : N.IsBelow e₀ b := Relation.ReflTransGen.head ⟨_, hg₂, rfl⟩ hb
  have hbc' : N.IsBelow e₁ c := Relation.ReflTransGen.head ⟨_, hk₁, rfl⟩ hc
  have hbd' : N.IsBelow e₁ d := Relation.ReflTransGen.head ⟨_, hk₂, rfl⟩ hd
  have hcn := not_isBelow_of_sibling hP hne hs.symm hb₁ hbc'
  have hdn := not_isBelow_of_sibling hP hne hs.symm hb₁ hbd'
  have han := not_isBelow_of_sibling hP hne.symm hs hb₀ hba
  have hbn := not_isBelow_of_sibling hP hne.symm hs hb₀ hbb
  have hbg : ¬ N.IsBelow g₁ b := not_isBelow_of_sibling hP hneg (hg₁.trans hg₂.symm) hbg₂ hb
  have hag : ¬ N.IsBelow g₂ a := not_isBelow_of_sibling hP hneg.symm (hg₂.trans hg₁.symm) hbg₁ ha
  have hdk : ¬ N.IsBelow k₁ d := not_isBelow_of_sibling hP hnek (hk₁.trans hk₂.symm) hbk₂ hd
  have hck : ¬ N.IsBelow k₂ c := not_isBelow_of_sibling hP hnek.symm (hk₂.trans hk₁.symm) hbk₁ hc
  have hsplit₀ : ∀ g, N.graph.source g = N.graph.target e₀ → ¬ (N.IsBelow g a ∧ N.IsBelow g b) := by
    rintro g hg ⟨h₃, h₄⟩
    rcases hallg g hg with rfl | rfl
    · exact hbg h₄
    · exact hag h₃
  have hsplit₁ : ∀ g, N.graph.source g = N.graph.target e₁ → ¬ (N.IsBelow g c ∧ N.IsBelow g d) := by
    rintro g hg ⟨h₃, h₄⟩
    rcases hallk g hg with rfl | rfl
    · exact hdk h₄
    · exact hck h₃
  have hab : a ≠ b := fun h' => hbg (h' ▸ ha)
  have hac : a ≠ c := fun h' => hcn (h' ▸ hba)
  have had : a ≠ d := fun h' => hdn (h' ▸ hba)
  have hbc : b ≠ c := fun h' => hcn (h' ▸ hbb)
  have hbd : b ≠ d := fun h' => hdn (h' ▸ hbb)
  have hcd : c ≠ d := fun h' => hdk (h' ▸ hc)
  have h := TreeMetric.card_four_of_ne hab hac had hbc hbd hcd
  refine ⟨a, b, c, d, h, fun θ hθ => ?_⟩
  rw [nmscCF_of_root hP hθ hs hu₀ hu₁ h (dominates_of_isBridge hP hb₀ hba) (dominates_of_isBridge hP hb₀ hbb) hsplit₀ hcn hdn (dominates_of_isBridge hP hb₁ hbc') (dominates_of_isBridge hP hb₁ hbd') hsplit₁ han hbn]
  have : 3 / 2 * (1 - (1 - 2 / 3 * Real.exp (-(θ.length e₀ + θ.length e₁)))) = Real.exp (-(θ.length e₀ + θ.length e₁)) := by ring
  rw [this, Real.log_exp, neg_neg]

end Blobs

section Semi

variable (hN : IsBinaryNetwork N) (hX : Nontrivial X)

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
include hN hX in
/-- **The two edges from the LSA don't both lead to one node**: that node would be a stable ancestor below the LSA. So the LSA is not alone in a blob with one other node. -/
theorem lsaNode_ne_of_blobOf_eq {u : V} (hu : u ≠ lsaNode hN hX) (hb : blobOf N.graph (lsaNode hN hX) = blobOf N.graph u) (huniq : ∀ w, w ≠ lsaNode hN hX → blobOf N.graph w = blobOf N.graph u → w = u) : False := by
  have hP := hN.isPhylogenetic
  have : Finite E := hP.finite_arcs
  have hst := (lsa_spec hP Set.univ Set.univ_nonempty).1
  obtain ⟨f₁, f₂, hne, hat₁, hat₂, hn₁, hn₂⟩ := InPassing.exists_two_nonCuts hP hu.symm (sameBlobIn_univ_iff.mpr hb)
  have hcut : ∀ {g}, g ∈ nonCutsIn N.graph Set.univ → ¬ N.graph.underlying.IsBridge g := fun hg hb' => hg.2 (isCutIn_univ_iff.mpr hb')
  have hsrc : ∀ {g}, g ∈ TreeSuppression.edgesAt N.graph (lsaNode hN hX) → g ∈ nonCutsIn N.graph Set.univ → N.graph.source g = lsaNode hN hX := by
    rintro g (h | h) hg
    · exact h
    · exact absurd ((N.graph.isBridge_iff g).mpr ⟨_, crosses_reached_iff hN hX h⟩) (hcut hg)
  have hs₁ := hsrc hat₁ hn₁
  have hs₂ := hsrc hat₂ hn₂
  have hto : ∀ {g}, N.graph.source g = lsaNode hN hX → g ∈ nonCutsIn N.graph Set.univ → N.graph.target g = u := by
    intro g hs hg
    refine huniq _ (fun h' => NMSC.source_ne_target hP g (hs.trans h'.symm)) ?_
    have he : blobOf N.graph (N.graph.source g) = blobOf N.graph (N.graph.target g) := N.graph.quotient_eq_of_not_isBridge (hcut hg)
    rw [← he, hs]
    exact hb
  -- so all edges from the LSA lead to `u`
  have h2 := two_le_outdegree_lsaNode hN hX
  have hout : N.graph.outdegree (lsaNode hN hX) = 2 := by
    by_cases hr : lsaNode hN hX = N.root
    · rw [hr]
      exact hN.isBinary.1
    · have h3 := hN.isBinary.2 _ hr (by omega)
      have h1 := hP.nonroot_indegree _ hr
      omega
  obtain ⟨p, q, -, hset⟩ := Set.ncard_eq_two.mp hout
  have hall : ∀ g, N.graph.source g = lsaNode hN hX → N.graph.target g = u := by
    intro g hg
    have hmem : ∀ g', N.graph.source g' = lsaNode hN hX ↔ g' = p ∨ g' = q := fun g' => by
      have := Set.ext_iff.mp hset g'
      simpa using this
    have hgf : g = f₁ ∨ g = f₂ := by
      rcases (hmem g).mp hg with rfl | rfl <;> rcases (hmem f₁).mp hs₁ with rfl | rfl <;> rcases (hmem f₂).mp hs₂ with rfl | rfl <;> simp_all
    rcases hgf with rfl | rfl
    · exact hto hg hn₁
    · exact hto hg hn₂
  -- `u` is a stable ancestor
  have hstable : N.IsStableAncestor Set.univ u := by
    rintro x - ⟨-, -, hp⟩
    have key : ∀ z, Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ u ∧ b ≠ u) N.root z → ¬ (N.graph.Reaches (lsaNode hN hX) z ∧ z ≠ lsaNode hN hX) := by
      intro z hz
      induction hz with
      | refl =>
        rintro ⟨h₁, h₂⟩
        exact h₂ (eq_of_reaches_of_reaches hP.acyclic h₁ (hP.root_reaches _)).symm
      | @tail a c _ hac ih =>
        rintro ⟨h₁, h₂⟩
        obtain ⟨⟨g, hgs, hgt⟩, -, hcu⟩ := hac
        by_cases hra : N.graph.Reaches (lsaNode hN hX) a
        · have ha : a = lsaNode hN hX := by
            by_contra hne'
            exact ih ⟨hra, hne'⟩
          exact hcu (hgt.symm.trans (hall g (hgs.trans ha)))
        · refine h₂ ?_
          rw [← hgt]
          exact target_eq_lsaNode hN hX (by rw [hgs]; exact hra) (by rw [hgt]; exact h₁)
    have hl := hst.leaf_ne hP Set.nontrivial_univ x
    exact key _ hp ⟨hst.reaches_leaf hP (Set.mem_univ x), hl⟩
  have hrl := (lsa_spec hP Set.univ Set.univ_nonempty).2 _ hstable
  exact hu (eq_of_reaches_of_reaches hP.acyclic hrl (Relation.ReflTransGen.single ⟨f₁, hs₁, hto hs₁ hn₁⟩))

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- **A node alone in its blob of `𝒩⁻` is alone in its blob of `𝒩⁺`.** -/
theorem isTrivialBlob_of_semidirected (u : SemiV hN hX) (h : IsTrivialBlob (semidirected hN hX).graph (blobOf (semidirected hN hX).graph u)) : IsTrivialBlob N.graph (blobOf N.graph u.1.1) := by
  have hreach : N.graph.Reaches (lsaNode hN hX) u.1.1 := u.1.2.1
  have huL : u.1.1 ≠ lsaNode hN hX := fun he => u.2 (Subtype.ext he)
  obtain ⟨v₀, hv₀⟩ := h
  have hone : ∀ w : SemiV hN hX, blobOf (semidirected hN hX).graph w = blobOf (semidirected hN hX).graph u → w = v₀ := fun w hw => by
    have : w ∈ blobNodes (semidirected hN hX).graph (blobOf (semidirected hN hX).graph u) := hw
    rwa [hv₀] at this
  have huniq : ∀ w, w ≠ lsaNode hN hX → blobOf N.graph w = blobOf N.graph u.1.1 → w = u.1.1 := by
    intro w hwL hw
    have hrw : N.graph.Reaches (lsaNode hN hX) w := (reaches_lsaNode_iff_of_blobOf_eq hN hX hw).mpr hreach
    have hmem : w ∈ N.belowVertices (lsaNode hN hX) Set.univ := (mem_belowVertices_univ_iff hN hX w).mpr fun h' => h'.2 (eq_of_reaches_of_reaches hN.isPhylogenetic.acyclic h'.1 hrw)
    let w' : SemiV hN hX := ⟨⟨w, hmem⟩, fun he => hwL (congrArg Subtype.val he)⟩
    have hw' : w' = u := (hone w' ((blobOf_semidirected_iff hN hX w' u).mpr hw)).trans (hone u rfl).symm
    exact congrArg (fun z : SemiV hN hX => z.1.1) hw'
  refine ⟨u.1.1, Set.eq_singleton_iff_unique_mem.mpr ⟨rfl, fun w hw => ?_⟩⟩
  by_cases hwL : w = lsaNode hN hX
  · exact (lsaNode_ne_of_blobOf_eq hN hX huL (hwL ▸ hw) huniq).elim
  · exact huniq w hwL hw

/-- **"For edges between trivial blobs, it is straightforward to see that edge lengths are identifiable"** (`a:claim:trivial-edges`, Section 5), on `𝒩⁻`: for an internal edge between trivial blobs of `𝒩⁻`, its length is a function of a `CF`, which does not depend on the parameters. The
hypothesis that the edge is internal can't be dropped: `FourCycle.pendant_not_identifiable`. -/
theorem semidirected_length_eq (e : SemiE hN hX) (hs : IsTrivialBlob (semidirected hN hX).graph (blobOf (semidirected hN hX).graph ((semidirected hN hX).graph.source e)))
    (ht : IsTrivialBlob (semidirected hN hX).graph (blobOf (semidirected hN hX).graph ((semidirected hN hX).graph.target e))) (hls : ∀ x, (semidirected hN hX).leaf x ≠ (semidirected hN hX).graph.source e)
    (hlt : ∀ x, (semidirected hN hX).leaf x ≠ (semidirected hN hX).graph.target e) :
    ∃ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), ∀ θ : MetricData E, N.IsMetric θ → (semidirectedMetric hN hX θ).length e = -Real.log (3 / 2 * (1 - nmscCF N θ 0 (quartetTree a b c d h))) := by
  have hPp := lsaPlus_isPhylogenetic hN hX
  have hval : ∀ {x : X} {w : SemiV hN hX}, N.leaf x = w.1.1 → (semidirected hN hX).leaf x = w := fun hx => Subtype.ext (Subtype.ext hx)
  have ht' := isTrivialBlob_of_semidirected hN hX _ ht
  have hlt' : ∀ x, N.leaf x ≠ N.graph.target e.1.1 := fun x hx => hlt x (hval hx)
  by_cases hsrc : (lsaPlus hN hX).graph.source e.1 = (lsaPlus hN hX).root
  · -- the edge the root becomes
    have hsv : (semidirected hN hX).graph.source e = ⟨(lsaPlus hN hX).graph.target (rootTreeArc hN hX), target_ne_root hPp _⟩ := source_unrootAt_of_eq hPp hsrc
    have hs' := isTrivialBlob_of_semidirected hN hX _ hs
    rw [hsv] at hs'
    have hls' : ∀ x, N.leaf x ≠ N.graph.target (rootTreeArc hN hX).1 := fun x hx => hls x (by
      rw [hsv]
      exact hval hx)
    have hss : N.graph.source e.1.1 = N.graph.source (rootTreeArc hN hX).1 := by
      have h₁ : N.graph.source e.1.1 = lsaNode hN hX := congrArg Subtype.val hsrc
      have h₂ : N.graph.source (rootTreeArc hN hX).1 = lsaNode hN hX := congrArg Subtype.val (rootTreeArc_spec hN hX).1
      exact h₁.trans h₂.symm
    have hne : (rootTreeArc hN hX).1 ≠ e.1.1 := fun he => e.2 (Subtype.ext he.symm)
    obtain ⟨a, b, c, d, h, hF⟩ := root_length_eq hN hss hne hs' ht' hls' hlt'
    refine ⟨a, b, c, d, h, fun θ hθ => ?_⟩
    rw [← hF θ hθ, add_comm]
    change (if (lsaPlus hN hX).graph.source e.1 = (lsaPlus hN hX).root then θ.length e.1.1 + θ.length (rootTreeArc hN hX).1 else θ.length e.1.1) = _
    rw [ite_eq_left hsrc]
  · have hsv : (semidirected hN hX).graph.source e = ⟨(lsaPlus hN hX).graph.source e.1, hsrc⟩ := source_unrootAt_of_ne hPp hsrc
    have hs' := isTrivialBlob_of_semidirected hN hX _ hs
    rw [hsv] at hs'
    have hls' : ∀ x, N.leaf x ≠ N.graph.source e.1.1 := fun x hx => hls x (by
      rw [hsv]
      exact hval hx)
    have hL : N.graph.source e.1.1 ≠ lsaNode hN hX := fun he => hsrc (Subtype.ext he)
    obtain ⟨a, b, c, d, h, hF⟩ := edge_length_eq hN hX ht' hs' hlt' e.1.2.1 hL
    refine ⟨a, b, c, d, h, fun θ hθ => ?_⟩
    rw [← hF θ hθ]
    change (if (lsaPlus hN hX).graph.source e.1 = (lsaPlus hN hX).root then θ.length e.1.1 + θ.length (rootTreeArc hN hX).1 else θ.length e.1.1) = _
    rw [ite_eq_right hsrc]

end Semi

end AllmanEtAl2023.TrivialEdges
