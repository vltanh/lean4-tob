module

public import External.AneEtAl2024.Proposition12
public import External.AllmanBanosRhodes2019.NANUQ

/-!
# Ané et al. 2024: the count of subnetworks with one hybrid node, and the rules for `3₂`-cycles

The source (Section 3.3, "`3₂`-cycle containment"): "it is not easy to decide if a given network with `k` hybrids contains a `3₂`-cycle. Even the number of subnetworks with exactly `1` hybrid node can be as large as `k 2^(k-1)`, growing exponentially".

A subnetwork with exactly one hybrid node keeps both parent arcs of one reticulation, and one parent arc of each of the others. `card_oneHybridChoices` counts these choices, for `k` reticulations of indegree two: exactly `k 2^(k-1)`. Pruning what is left without a taxon can make two choices the same subgraph,
which is the source's "can be as large as".

The source goes on, for "a particular 4-taxon network with a 3-blob `B`":

"2. If the edges that are incident to `B` and that exit `B` (for some placement of the root) have at most 2 descendants total, then `B` does not contain a `3₂`-cycle. This is because the number of descendant leaves of a `3₂`-cycle is either 3 (when the root is outside the blob) or 4 (when the root is inside the blob)."

and "deciding if rule 1 or 2 applies takes constant time after calculating a blob decomposition". Here:

* `three_le_card_belowBlob`: a `3₂`-cycle in the sense of `External.AllmanBanosRhodes2019.HasThreeTwoCycle`, of the blobs of the network, has at least three taxa below its blob, and all four when the root is in the blob (`card_belowBlob_of_root`). The source's two taxa are below the hybrid node; of the other two, one at least is below the blob, since otherwise they would be joined outside the blob, through the root.
* `rule2`: rule 2, for `3₂`-cycles of subnetworks, which is what "contain" means for a network that is not of level 1: `restrict` deletes arcs, and the blobs of the subnetwork are in the blobs of the network.
* `card_exitArcs_le`: at most one arc per taxon leaves a blob by a bridge. So on four taxa rule 2 reads at most four sets of descendants, each a subset of four, however many hybrid nodes the network has; rule 1 reads one such set.

Rule 1 is the source's Lemma 11. On a level-1 network it is the definition, since the blob `B` has one hybrid node, and a 3-blob joins the two other taxa only through `B`. Its general form, on a network with several hybrid nodes in `B`, is not formalized here: it constructs the cycle in a subnetwork, from its Lemmas 9 and 10.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace External.AneEtAl2024

variable {H A : Type*} [Fintype H] [DecidableEq H]

/-- For reticulations `H`, a choice of a parent at each, from two: which parent to keep. A subnetwork with exactly one hybrid node is a reticulation `h`, and such a choice at the others. -/
abbrev OneHybridChoice (H : Type*) := Σ h : H, ({h' : H // h' ≠ h} → Bool)

/-- **"The number of subnetworks with exactly `1` hybrid node can be as large as `k 2^(k-1)`"**: this many choices, on `k` reticulations with two parents each. -/
theorem card_oneHybridChoices : Fintype.card (OneHybridChoice H) = Fintype.card H * 2 ^ (Fintype.card H - 1) := by
  rw [Fintype.card_sigma]
  have h : ∀ h : H, Fintype.card ({h' : H // h' ≠ h} → Bool) = 2 ^ (Fintype.card H - 1) := by
    intro h
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl]
    simp
  simp [h]

section Rules

variable {V E X : Type*} [Fintype X] [DecidableEq X]

open Phylogenetics Phylogenetics.RootedNetwork External.AllmanBanosRhodes2019 TOBQMC.Level1

/-- The taxa of `q` below the blob of `h`: below some vertex of it. -/
def belowBlob (N : RootedNetwork V E X) (h : V) (q : Finset X) : Finset X :=
  q.filter fun x => ∃ v, N.graph.blobSetoid h v ∧ N.graph.Reaches v (N.leaf x)

omit [Fintype X] [DecidableEq X] in
/-- A directed path to a vertex not below the blob stays outside the blob. -/
theorem blockWalk_of_reaches {N : RootedNetwork V E X} {h u w : V} (hr : N.graph.Reaches u w) (hw : ∀ v, N.graph.blobSetoid h v → ¬ N.graph.Reaches v w) :
    BlockWalk N h u w := by
  induction hr with
  | refl => exact .refl
  | @tail a b hua hab ih =>
    have hb : ∀ v, N.graph.blobSetoid h v → ¬ N.graph.Reaches v a := fun v hv hr => hw v hv (hr.tail hab)
    refine (ih hb).tail ⟨fun ha => hb a ha .refl, fun hb' => hw b hb' .refl, ?_⟩
    obtain ⟨e, h₁, h₂⟩ := hab
    exact ⟨e, Or.inl ⟨h₁, h₂⟩⟩

omit [Fintype X] in
/-- **"The number of descendant leaves of a `3₂`-cycle is" at least three.** The two taxa below the hybrid node are below the blob. If neither of the two others were, they would be joined outside the blob, through the root. -/
theorem three_le_card_belowBlob {N : RootedNetwork V E X} {q : Finset X} {h : V} (hq : q.card = 4) (hr : ∀ x ∈ q, N.graph.Reaches N.root (N.leaf x))
    (hc : (q.filter fun x => N.graph.Reaches h (N.leaf x)).card = 2)
    (hs : ∀ x ∈ q, ∀ y ∈ q, x ≠ y → ¬ N.graph.Reaches h (N.leaf x) → ¬ N.graph.Reaches h (N.leaf y) → ¬ BlockWalk N h (N.leaf x) (N.leaf y)) :
    3 ≤ (belowBlob N h q).card := by
  by_contra hlt
  have hsub : (q.filter fun x => N.graph.Reaches h (N.leaf x)) ⊆ belowBlob N h q := fun x hx => by
    obtain ⟨h₁, h₂⟩ := mem_filter.1 hx
    exact mem_filter.2 ⟨h₁, h, N.graph.blobSetoid.refl' h, h₂⟩
  have heq : (q.filter fun x => N.graph.Reaches h (N.leaf x)) = belowBlob N h q :=
    eq_of_subset_of_card_le hsub (by omega)
  have hrest : 2 ≤ (q \ belowBlob N h q).card := by
    have hbs : belowBlob N h q ⊆ q := filter_subset _ _
    have := card_sdiff_add_card_eq_card hbs
    omega
  obtain ⟨x, y, hxy, hx, hy⟩ : ∃ x y, x ≠ y ∧ x ∈ q \ belowBlob N h q ∧ y ∈ q \ belowBlob N h q := by
    obtain ⟨x, hx, y, hy, hne⟩ := one_lt_card.1 hrest
    exact ⟨x, y, hne, hx, hy⟩
  obtain ⟨hxq, hxb⟩ := mem_sdiff.1 hx
  obtain ⟨hyq, hyb⟩ := mem_sdiff.1 hy
  have hnot : ∀ {z}, z ∈ q → z ∉ belowBlob N h q → ∀ v, N.graph.blobSetoid h v → ¬ N.graph.Reaches v (N.leaf z) := fun hz hzb v hv hrv =>
    hzb (mem_filter.2 ⟨hz, v, hv, hrv⟩)
  refine hs x hxq y hyq hxy (fun hb => hxb (mem_filter.2 ⟨hxq, h, N.graph.blobSetoid.refl' h, hb⟩)) (fun hb => hyb (mem_filter.2 ⟨hyq, h, N.graph.blobSetoid.refl' h, hb⟩)) ?_
  exact blockWalk_trans (blockWalk_symm (blockWalk_of_reaches (hr x hxq) (hnot hxq hxb))) (blockWalk_of_reaches (hr y hyq) (hnot hyq hyb))

omit [Fintype X] [DecidableEq X] in
/-- **"or 4 (when the root is inside the blob)"**. -/
theorem card_belowBlob_of_root {N : RootedNetwork V E X} {q : Finset X} {h : V} (hr : ∀ x ∈ q, N.graph.Reaches N.root (N.leaf x)) (hroot : N.graph.blobSetoid h N.root) :
    (belowBlob N h q).card = q.card := by
  congr 1
  exact filter_true_of_mem fun x hx => ⟨N.root, hroot, hr x hx⟩

/-- The subnetwork with the arcs of `D` deleted. -/
def restrict (N : RootedNetwork V E X) (D : Set E) : RootedNetwork V {e // e ∉ D} X :=
  ⟨⟨fun e => N.graph.source e.val, fun e => N.graph.target e.val⟩, N.root, N.leaf⟩

omit [Fintype X] [DecidableEq X] in
/-- A bridge of the network is a bridge of a subnetwork that has it. -/
theorem restrict_isBridge {N : RootedNetwork V E X} {D : Set E} {e : {e // e ∉ D}} (he : N.graph.underlying.IsBridge e.val) : (restrict N D).graph.underlying.IsBridge e := by
  obtain ⟨S, hS⟩ := (N.graph.isBridge_iff e.val).1 he
  exact ((restrict N D).graph.isBridge_iff e).2 ⟨S, fun f => (hS f.val).trans Subtype.ext_iff.symm⟩

omit [Fintype X] [DecidableEq X] in
/-- A blob of a subnetwork is in a blob of the network. -/
theorem blob_of_restrict {N : RootedNetwork V E X} {D : Set E} {u v : V} (h : (restrict N D).graph.blobSetoid u v) : N.graph.blobSetoid u v := by
  change Relation.ReflTransGen _ u v at h
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
    obtain ⟨f, hf, hab⟩ := hab
    exact Relation.ReflTransGen.tail ih ⟨f.val, fun hb => hf (restrict_isBridge hb), hab⟩

omit [Fintype X] [DecidableEq X] in
theorem reaches_of_restrict {N : RootedNetwork V E X} {D : Set E} {u v : V} (h : (restrict N D).graph.Reaches u v) : N.graph.Reaches u v := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
    obtain ⟨f, h₁, h₂⟩ := hab
    exact ih.tail ⟨f.val, h₁, h₂⟩

omit [Fintype X] in
/-- **Rule 2** (`ext:ane2024-rule2`): if at most two taxa are below the blob of `h`, then no subnetwork in which the root still reaches the taxa has a `3₂`-cycle at `h`. -/
theorem rule2 {N : RootedNetwork V E X} {q : Finset X} {h : V} (hq : q.card = 4) (hle : (belowBlob N h q).card ≤ 2) (D : Set E) (hr : ∀ x ∈ q, (restrict N D).graph.Reaches N.root (N.leaf x)) :
    ¬ ((q.filter fun x => (restrict N D).graph.Reaches h (N.leaf x)).card = 2 ∧
      ∀ x ∈ q, ∀ y ∈ q, x ≠ y → ¬ (restrict N D).graph.Reaches h (N.leaf x) → ¬ (restrict N D).graph.Reaches h (N.leaf y) → ¬ BlockWalk (restrict N D) h (N.leaf x) (N.leaf y)) := by
  rintro ⟨hc, hs⟩
  have h₃ := three_le_card_belowBlob (N := restrict N D) hq hr hc hs
  have hsub : belowBlob (restrict N D) h q ⊆ belowBlob N h q := fun x hx => by
    obtain ⟨hxq, v, hv, hrv⟩ := mem_filter.1 hx
    exact mem_filter.2 ⟨hxq, v, blob_of_restrict hv, reaches_of_restrict hrv⟩
  have := card_le_card hsub
  omega

/-- The arcs that leave the blob of `h` by a bridge. -/
def exitArcs (N : RootedNetwork V E X) (h : V) : Set E :=
  {e | N.graph.underlying.IsBridge e ∧ N.graph.blobSetoid h (N.graph.source e) ∧ ¬ N.graph.blobSetoid h (N.graph.target e)}

omit [Fintype X] [DecidableEq X] in
/-- A taxon below a bridge is dominated by it: the root is on the side of its source. -/
theorem dominates_of_isBridge {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {e : E} {x : X} (he : N.graph.underlying.IsBridge e) (hx : N.IsBelow e x) : N.Dominates e x := by
  obtain ⟨S, hS⟩ := (N.graph.isBridge_iff e).1 he
  obtain ⟨T, hT, htT, hsT⟩ : ∃ T : Set V, (∀ f, N.graph.Crosses f T ↔ f = e) ∧ N.graph.target e ∈ T ∧ N.graph.source e ∉ T := by
    rcases (hS e).2 rfl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · refine ⟨Sᶜ, fun f => ?_, h₂, by simpa using h₁⟩
      rw [← hS f]
      simp only [DirectedMultigraph.Crosses, Set.mem_compl_iff, not_not]
      tauto
    · exact ⟨S, hS, h₁, h₂⟩
  have hdown : ∀ w, N.graph.Reaches (N.graph.target e) w → w ∈ T := by
    intro w hw
    induction hw with
    | refl => exact htT
    | @tail a b _ hab ih =>
      obtain ⟨f, rfl, rfl⟩ := hab
      by_contra hb
      have hfe := (hT f).1 (Or.inl ⟨ih, hb⟩)
      subst hfe
      exact hsT ih
  have hroot : N.root ∉ T := by
    intro hr
    have key : ∀ w, N.graph.Reaches N.root w → w ∈ T := by
      intro w hw
      induction hw with
      | refl => exact hr
      | @tail a b _ hab ih =>
        obtain ⟨f, rfl, rfl⟩ := hab
        by_contra hb
        have hfe := (hT f).1 (Or.inl ⟨ih, hb⟩)
        subst hfe
        exact hsT ih
    exact hsT (key _ (hN.root_reaches _))
  intro hav
  have hin : N.leaf x ∈ T := hdown _ hx
  have key : ∀ w, N.AvoidingReach e N.root w → w ∉ T := by
    intro w hw
    induction hw with
    | refl => exact hroot
    | @tail a b _ hab ih =>
      obtain ⟨f, hfe, rfl, rfl⟩ := hab
      intro hb
      exact hfe ((hT f).1 (Or.inr ⟨hb, ih⟩))
  exact key _ hav hin

omit [Fintype X] [DecidableEq X] in
/-- Two arcs leaving a blob by bridges have no taxon below both. -/
theorem eq_of_exitArcs {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {h : V} {e e' : E} (he : e ∈ exitArcs N h) (he' : e' ∈ exitArcs N h) {x : X} (hx : N.IsBelow e x) (hx' : N.IsBelow e' x) : e = e' := by
  by_contra hne
  have key : ∀ {e e' : E}, e ∈ exitArcs N h → e' ∈ exitArcs N h → N.graph.Reaches (N.graph.target e) (N.graph.source e') → False := by
    intro e e' he he' hr
    obtain ⟨hb, hs, ht⟩ := he
    obtain ⟨_, hs', _⟩ := he'
    obtain ⟨S, hS⟩ := (N.graph.isBridge_iff e).1 hb
    have hwalk : N.graph.Walks {f | ¬ N.graph.underlying.IsBridge f} (N.graph.source e) (N.graph.source e') :=
      N.graph.walks_trans (N.graph.walks_symm hs) hs'
    have hstable : N.graph.source e ∈ S ↔ N.graph.source e' ∈ S :=
      N.graph.mem_iff_mem_of_walks (F := {f | ¬ N.graph.underlying.IsBridge f}) (fun f (hf : ¬ N.graph.underlying.IsBridge f) hc => hf ((hS f).1 hc ▸ hb)) hwalk
    have hd : ∀ w, N.graph.Reaches (N.graph.target e) w → (w ∈ S ↔ N.graph.target e ∈ S) := by
      intro w hw
      induction hw with
      | refl => exact Iff.rfl
      | @tail a b _ hab ih =>
        obtain ⟨f, rfl, rfl⟩ := hab
        by_cases hf : f = e
        · subst hf
          exact absurd hr (fun _ => by
            exact not_reaches_target_source hN.acyclic f ‹_›)
        · have hnc : ¬ N.graph.Crosses f S := fun hc => hf ((hS f).1 hc)
          rw [← ih]
          simp only [DirectedMultigraph.Crosses, not_or, not_and, not_not] at hnc
          tauto
    have hc := (hS e).2 rfl
    have h₁ := hd _ hr
    simp only [DirectedMultigraph.Crosses] at hc
    tauto
  rcases (dominates_of_isBridge hN he.1 hx).reaches_or_reaches hN (dominates_of_isBridge hN he'.1 hx') hne with hr | hr
  · exact key he he' hr
  · exact key he' he hr

omit [DecidableEq X] in
/-- **At most one arc per taxon leaves a blob by a bridge**: the arcs are told apart by a taxon below each. On four taxa, rule 2 reads at most four sets of descendants, each a subset of four taxa, however many hybrid nodes the network has. -/
theorem card_exitArcs_le [Finite E] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) (h : V) : (exitArcs N h).ncard ≤ Fintype.card X := by
  have hex : ∀ e : exitArcs N h, ∃ x, N.IsBelow e x := fun e => exists_reaches_leaf hN _
  choose f hf using hex
  have hinj : Function.Injective f := fun e e' hee => Subtype.ext (eq_of_exitArcs hN e.2 e'.2 (hf e) (hee ▸ hf e'))
  have : Finite (exitArcs N h) := Subtype.finite
  have : Fintype (exitArcs N h) := Fintype.ofFinite _
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective f hinj

end Rules

end External.AneEtAl2024
