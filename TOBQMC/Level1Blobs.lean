module

public import Basic.Phylogenetics.NetworkCuts

/-!
# Blobs of binary level-1 networks

The graph facts behind TOB-QMC Lemma 4 (`TOBQMC/Level1.lean`), in the domination language of
`Basic/Phylogenetics/NetworkCuts.lean`.

* An arc is a bridge exactly when nothing outside enters the descendants of its target
  (`isBridge_iff_reaches`).
* Arcs entering a reticulation are not bridges (`not_isBridge_of_two_le_indegree`).
* A blob with a non-bridge arc has a reticulation (`exists_reticulation_or_forall_isBridge`), a unique
  one when the network is level-1 (`reticulation_unique`), and every vertex of the blob
  reaches it (`reaches_reticulation`).
* A connected component of the complement of a blob is the far side of a cut edge
  (`exists_blockWalk_cut`).
* Four taxa in distinct blocks at a blob of a binary network: some arc of the blob has exactly two of
  them below it (`exists_arc_two_below`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical


namespace TOBQMC.Level1

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-! ### Reachability in a rooted network -/

omit [Fintype X] [DecidableEq X] in
theorem reaches_of_arc (N : RootedNetwork V E X) (e : E) :
    N.graph.Reaches (N.graph.source e) (N.graph.target e) :=
  Relation.ReflTransGen.single ⟨e, rfl, rfl⟩

omit [Fintype X] [DecidableEq X] in
/-- A step down an arc, then a path. -/
theorem transGen_of_arc_reaches {e : E} {w : V} (h : N.graph.Reaches (N.graph.target e) w) :
    Relation.TransGen N.graph.Adj (N.graph.source e) w :=
  Relation.TransGen.head' ⟨e, rfl, rfl⟩ h

omit [Fintype X] [DecidableEq X] in
theorem not_reaches_source (hN : N.IsPhylogenetic) (e : E) :
    ¬ N.graph.Reaches (N.graph.target e) (N.graph.source e) :=
  fun h => hN.acyclic _ (transGen_of_arc_reaches h)

omit [Fintype X] [DecidableEq X] in
theorem target_ne_source (hN : N.IsPhylogenetic) (e : E) : N.graph.target e ≠ N.graph.source e := by
  intro h
  apply not_reaches_source hN e
  rw [h]
  exact Relation.ReflTransGen.refl

omit [Fintype X] [DecidableEq X] in
/-- In a finite acyclic graph, a nonempty set of vertices has a sink-most member. -/
theorem exists_sink (hN : N.IsPhylogenetic) {S : Set V} (hS : S.Nonempty) :
    ∃ u ∈ S, ∀ w ∈ S, ¬ Relation.TransGen N.graph.Adj u w := by
  have := hN.finite_vertices
  let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj b a
  have : IsTrans V r := ⟨fun a b c hab hbc => hbc.trans hab⟩
  have : Std.Irrefl r := ⟨fun a h => hN.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨u, hu, hmin⟩ := hwf.has_min S hS
  exact ⟨u, hu, fun w hw => hmin w hw⟩

omit [Fintype X] [DecidableEq X] in
/-- In a finite acyclic graph, a nonempty set of vertices has a source-most member. -/
theorem exists_source (hN : N.IsPhylogenetic) {S : Set V} (hS : S.Nonempty) :
    ∃ u ∈ S, ∀ w ∈ S, ¬ Relation.TransGen N.graph.Adj w u := by
  have := hN.finite_vertices
  let r : V → V → Prop := Relation.TransGen N.graph.Adj
  have : IsTrans V r := ⟨fun a b c hab hbc => hab.trans hbc⟩
  have : Std.Irrefl r := ⟨fun a h => hN.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨u, hu, hmin⟩ := hwf.has_min S hS
  exact ⟨u, hu, fun w hw => hmin w hw⟩

omit [Fintype X] [DecidableEq X] in
/-- Every vertex has a taxon below it. -/
theorem exists_leaf_below (hN : N.IsPhylogenetic) (u : V) : ∃ x, N.graph.Reaches u (N.leaf x) := by
  have := hN.finite_arcs
  obtain ⟨w, hw, hmin⟩ := exists_sink hN (S := {w | N.graph.Reaches u w}) ⟨u, .refl⟩
  have h0 : N.graph.outdegree w = 0 := by
    rw [DirectedMultigraph.outdegree_eq_zero_iff]
    intro e he
    have hu : N.graph.Reaches u (N.graph.target e) := by
      refine Relation.ReflTransGen.trans hw ?_
      rw [← he]
      exact reaches_of_arc N e
    refine hmin _ hu (Relation.TransGen.single ⟨e, he, rfl⟩)
  obtain ⟨x, rfl⟩ := (hN.leaves w).mp h0
  exact ⟨x, hw⟩

/-! ### Avoiding an arc -/

omit [Fintype X] [DecidableEq X] in
theorem reaches_of_avoidingReach {e : E} {a b : V} (h : N.AvoidingReach e a b) :
    N.graph.Reaches a b :=
  Relation.ReflTransGen.mono (r := fun a b => ∃ f, f ≠ e ∧ N.graph.source f = a ∧ N.graph.target f = b)
    (p := N.graph.Adj) (fun _ _ ⟨f, _, hs, ht⟩ => ⟨f, hs, ht⟩) _ _ h

omit [Fintype X] [DecidableEq X] in
/-- A path either avoids the arc `e` or passes through it. -/
theorem avoidingReach_or_reaches (e : E) {a b : V} (h : N.graph.Reaches a b) :
    N.AvoidingReach e a b ∨ N.graph.Reaches (N.graph.target e) b := by
  induction h with
  | refl => exact Or.inl .refl
  | @tail w b _ hwb ih =>
    obtain ⟨f, rfl, rfl⟩ := hwb
    rcases ih with ih | ih
    · by_cases hf : f = e
      · subst hf
        exact Or.inr .refl
      · exact Or.inl (ih.tail ⟨f, hf, rfl, rfl⟩)
    · exact Or.inr (ih.tail ⟨f, rfl, rfl⟩)

omit [Fintype X] [DecidableEq X] in
/-- A path starting below the source of `e`, at no ancestor of it, avoids `e`. -/
theorem avoidingReach_of_not_reaches_source {e : E} {a b : V} (h : N.graph.Reaches a b)
    (ha : ¬ N.graph.Reaches a (N.graph.source e)) : N.AvoidingReach e a b := by
  induction h with
  | refl => exact .refl
  | @tail w b hw hwb ih =>
    obtain ⟨f, rfl, rfl⟩ := hwb
    refine ih.tail ⟨f, ?_, rfl, rfl⟩
    rintro rfl
    exact ha hw

omit [Fintype X] [DecidableEq X] in
/-- A dominated taxon is below the arc. -/
theorem isBelow_of_dominates (hN : N.IsPhylogenetic) {e : E} {x : X} (h : N.Dominates e x) :
    N.IsBelow e x :=
  (avoidingReach_or_reaches e (hN.root_reaches (N.leaf x))).resolve_left h

omit [Fintype X] [DecidableEq X] in
/-- A path avoiding `e` from outside the descendants of `c` into them has an entering arc other
than `e`. -/
theorem exists_entering_arc {e : E} {c a b : V} (h : N.AvoidingReach e a b)
    (ha : ¬ N.graph.Reaches c a) (hb : N.graph.Reaches c b) :
    ∃ f, f ≠ e ∧ ¬ N.graph.Reaches c (N.graph.source f) ∧ N.graph.Reaches c (N.graph.target f) ∧
      N.graph.Reaches (N.graph.target f) b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd hb ha
  | @head a a' haa' _ ih =>
    obtain ⟨f, hfe, rfl, rfl⟩ := haa'
    by_cases hc : N.graph.Reaches c (N.graph.target f)
    · exact ⟨f, hfe, ha, hc, reaches_of_avoidingReach ‹_›⟩
    · exact ih hc

/-! ### Bridges through descendants -/

omit [Fintype X] [DecidableEq X] in
/-- Only `e` crosses `S`, entering it: descendants of a member of `S` are in `S`. -/
theorem mem_of_reaches_of_cut {e : E} {S : Set V} (hS : ∀ f, N.graph.Crosses f S ↔ f = e)
    (hs : N.graph.source e ∉ S) {a b : V} (ha : a ∈ S) (hab : N.graph.Reaches a b) : b ∈ S := by
  induction hab with
  | refl => exact ha
  | @tail w b _ hwb ih =>
    obtain ⟨f, rfl, rfl⟩ := hwb
    by_contra hb
    have := (hS f).mp (Or.inl ⟨ih, hb⟩)
    subst this
    exact hs ih

omit [Fintype X] [DecidableEq X] in
/-- Only `e` crosses `S`, entering it: the root is outside. -/
theorem root_notMem_of_cut (hN : N.IsPhylogenetic) {e : E} {S : Set V}
    (hS : ∀ f, N.graph.Crosses f S ↔ f = e) (hs : N.graph.source e ∉ S) : N.root ∉ S :=
  fun hr => hs (mem_of_reaches_of_cut hS hs hr (hN.root_reaches _))

omit [Fintype X] [DecidableEq X] in
/-- Only `e` crosses `S`, entering it: every member of `S` is below the target of `e`. -/
theorem reaches_of_mem_cut {e : E} {S : Set V} (hS : ∀ f, N.graph.Crosses f S ↔ f = e)
    {a b : V} (ha : a ∉ S) (hb : b ∈ S) (hab : N.graph.Reaches a b) :
    N.graph.Reaches (N.graph.target e) b := by
  induction hab with
  | refl => exact absurd hb ha
  | @tail w b _ hwb ih =>
    obtain ⟨f, rfl, rfl⟩ := hwb
    by_cases hw : N.graph.source f ∈ S
    · exact (ih hw).tail ⟨f, rfl, rfl⟩
    · have := (hS f).mp (Or.inr ⟨hb, hw⟩)
      subst this
      exact .refl

omit [Fintype X] [DecidableEq X] in
theorem crosses_compl_iff (f : E) (S : Set V) : N.graph.Crosses f Sᶜ ↔ N.graph.Crosses f S := by
  simp only [DirectedMultigraph.Crosses, Set.mem_compl_iff, not_not]
  tauto

omit [Fintype X] [DecidableEq X] in
/-- A singleton cut, oriented: its set contains the target of the arc and not its source. -/
theorem exists_oriented_cut {e : E} (he : IsBridge N e) :
    ∃ S : Set V, (∀ f, N.graph.Crosses f S ↔ f = e) ∧ N.graph.target e ∈ S ∧
      N.graph.source e ∉ S := by
  obtain ⟨S, hS⟩ := he
  rcases (hS e).mpr rfl with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · exact ⟨Sᶜ, fun f => (crosses_compl_iff f S).trans (hS f), ht, not_not.mpr hs⟩
  · exact ⟨S, hS, ht, hs⟩

omit [Fintype X] [DecidableEq X] in
/-- **An arc is a bridge exactly when no other arc enters the descendants of its target.** -/
theorem isBridge_iff_reaches (hN : N.IsPhylogenetic) (e : E) :
    IsBridge N e ↔ ∀ f, f ≠ e → N.graph.Reaches (N.graph.target e) (N.graph.target f) →
      N.graph.Reaches (N.graph.target e) (N.graph.source f) := by
  constructor
  · intro he f hfe hf
    obtain ⟨S, hS, ht, hs⟩ := exists_oriented_cut he
    have hft : N.graph.target f ∈ S := mem_of_reaches_of_cut hS hs ht hf
    have hfs : N.graph.source f ∈ S := by
      by_contra h
      exact hfe ((hS f).mp (Or.inr ⟨hft, h⟩))
    exact reaches_of_mem_cut hS (root_notMem_of_cut hN hS hs) hfs (hN.root_reaches _)
  · intro h
    refine ⟨{u | N.graph.Reaches (N.graph.target e) u}, fun f => ⟨?_, ?_⟩⟩
    · rintro (⟨hs, ht⟩ | ⟨ht, hs⟩)
      · exact absurd (Relation.ReflTransGen.tail hs ⟨f, rfl, rfl⟩) ht
      · by_contra hfe
        exact hs (h f hfe ht)
    · rintro rfl
      exact Or.inr ⟨.refl, not_reaches_source hN _⟩

omit [Fintype X] [DecidableEq X] in
/-- A bridge is the only arc crossing the descendants of its target. -/
theorem isBridge_crosses_iff (hN : N.IsPhylogenetic) {e : E} (he : IsBridge N e) (f : E) :
    N.graph.Crosses f {u | N.graph.Reaches (N.graph.target e) u} ↔ f = e := by
  have h := (isBridge_iff_reaches hN e).mp he
  constructor
  · rintro (⟨hs, ht⟩ | ⟨ht, hs⟩)
    · exact absurd (Relation.ReflTransGen.tail hs ⟨f, rfl, rfl⟩) ht
    · by_contra hfe
      exact hs (h f hfe ht)
  · rintro rfl
    exact Or.inr ⟨.refl, not_reaches_source hN _⟩

/-! ### Indegrees -/

omit [Fintype X] [DecidableEq X] in
theorem two_le_indegree_of_ne (hN : N.IsPhylogenetic) {e f : E} (hne : e ≠ f)
    (h : N.graph.target e = N.graph.target f) : 2 ≤ N.graph.indegree (N.graph.target e) := by
  have := hN.finite_arcs
  rw [DirectedMultigraph.indegree, ← Set.ncard_pair hne]
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  rintro g (rfl | rfl)
  · rfl
  · exact h.symm

omit [Fintype X] [DecidableEq X] in
theorem exists_ne_target_eq {e : E} (he : 2 ≤ N.graph.indegree (N.graph.target e)) (hN : N.IsPhylogenetic) :
    ∃ f, f ≠ e ∧ N.graph.target f = N.graph.target e := by
  have := hN.finite_arcs
  obtain ⟨f, hf, hfe⟩ := Set.exists_ne_of_one_lt_ncard (lt_of_lt_of_le one_lt_two he) e
  exact ⟨f, hfe, hf⟩

omit [Fintype X] [DecidableEq X] in
/-- An arc entering a vertex with at most one incoming arc is its only incoming arc. -/
theorem eq_of_indegree_le_one (hN : N.IsPhylogenetic) {e f : E}
    (h : N.graph.indegree (N.graph.target e) ≤ 1) (hfe : N.graph.target f = N.graph.target e) :
    f = e := by
  by_contra hne
  have := two_le_indegree_of_ne hN hne hfe
  rw [hfe] at this
  omega

omit [Fintype X] [DecidableEq X] in
/-- **Arcs entering a reticulation are not bridges.** -/
theorem not_isBridge_of_two_le_indegree (hN : N.IsPhylogenetic) {e : E}
    (he : 2 ≤ N.graph.indegree (N.graph.target e)) : ¬ IsBridge N e := by
  intro hb
  obtain ⟨f, hfe, hf⟩ := exists_ne_target_eq he hN
  have := (isBridge_iff_reaches hN e).mp hb f hfe (by rw [hf]; exact .refl)
  rw [← hf] at this
  exact not_reaches_source hN f this

omit [Fintype X] [DecidableEq X] in
/-- If every arc leaving a vertex with at most one incoming arc is a bridge, so is the incoming arc. -/
theorem isBridge_of_indegree_le_one (hN : N.IsPhylogenetic) {f : E}
    (hin : N.graph.indegree (N.graph.target f) ≤ 1)
    (hout : ∀ g, N.graph.source g = N.graph.target f → IsBridge N g) : IsBridge N f := by
  rw [isBridge_iff_reaches hN]
  intro k hkf hk
  rcases Relation.ReflTransGen.cases_head hk with heq | ⟨c, ⟨g, hg, rfl⟩, hc⟩
  · exact absurd (eq_of_indegree_le_one hN hin heq.symm) hkf
  · by_cases hkg : k = g
    · subst hkg
      rw [hg]
      exact .refl
    · exact (reaches_of_arc N g).trans ((isBridge_iff_reaches hN g).mp (hout g hg) k hkg hc)
        |> fun h => by rw [hg] at h; exact h

/-! ### Blobs -/

omit [Fintype X] [DecidableEq X] in
theorem sameBlob_symm {u w : V} (h : SameBlob N u w) : SameBlob N w u := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
    obtain ⟨e, he, hl⟩ := hab
    exact Relation.ReflTransGen.head ⟨e, he, hl.symm⟩ ih

omit [Fintype X] [DecidableEq X] in
theorem sameBlob_trans {u w z : V} (h : SameBlob N u w) (h' : SameBlob N w z) : SameBlob N u z :=
  Relation.ReflTransGen.trans h h'

omit [Fintype X] [DecidableEq X] in
theorem sameBlob_of_not_isBridge {e : E} (he : ¬ IsBridge N e) :
    SameBlob N (N.graph.source e) (N.graph.target e) :=
  Relation.ReflTransGen.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

omit [Fintype X] [DecidableEq X] in
/-- Walks in a blob do not change the side of a singleton cut. -/
theorem mem_iff_of_sameBlob {e : E} {S : Set V} (hS : ∀ f, N.graph.Crosses f S ↔ f = e)
    {u w : V} (h : SameBlob N u w) : u ∈ S ↔ w ∈ S := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hab ih =>
    obtain ⟨f, hf, hl⟩ := hab
    have hb : ¬ N.graph.Crosses f S := fun hc => hf ⟨S, by rw [(hS f).mp hc]; exact hS⟩
    have heq : N.graph.source f ∈ S ↔ N.graph.target f ∈ S := by
      simp only [DirectedMultigraph.Crosses] at hb
      tauto
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ih.trans heq
    · exact ih.trans heq.symm

omit [Fintype X] [DecidableEq X] in
/-- Below a bridge, a whole blob is below it or none of it is. -/
theorem reaches_iff_of_sameBlob (hN : N.IsPhylogenetic) {e : E} (he : IsBridge N e)
    {u w : V} (h : SameBlob N u w) :
    N.graph.Reaches (N.graph.target e) u ↔ N.graph.Reaches (N.graph.target e) w :=
  mem_iff_of_sameBlob (isBridge_crosses_iff hN he) h

omit [Fintype X] [DecidableEq X] in
/-- A bridge entering a blob has the whole blob below it. -/
theorem reaches_of_sameBlob (hN : N.IsPhylogenetic) {e : E} (he : IsBridge N e)
    {u : V} (h : SameBlob N (N.graph.target e) u) : N.graph.Reaches (N.graph.target e) u :=
  (reaches_iff_of_sameBlob hN he h).mp .refl

omit [Fintype X] [DecidableEq X] in
/-- A vertex all of whose arcs are bridges is alone in its blob. -/
theorem eq_of_sameBlob_of_forall_isBridge {u w : V}
    (hu : ∀ f, (N.graph.source f = u ∨ N.graph.target f = u) → IsBridge N f)
    (h : SameBlob N u w) : w = u := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, ⟨f, hf, hl⟩, _⟩
  · exact heq.symm
  · exfalso
    apply hf
    apply hu
    rcases hl with ⟨h, _⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h

omit [Fintype X] [DecidableEq X] in
/-- All arcs at a vertex are bridges when it has at most one incoming arc and its outgoing arcs are
bridges. -/
theorem forall_isBridge_of_indegree_le_one (hN : N.IsPhylogenetic) {u : V}
    (hin : N.graph.indegree u ≤ 1) (hout : ∀ g, N.graph.source g = u → IsBridge N g) :
    ∀ f, (N.graph.source f = u ∨ N.graph.target f = u) → IsBridge N f := by
  rintro f (hf | rfl)
  · exact hout f hf
  · exact isBridge_of_indegree_le_one hN hin hout

omit [Fintype X] [DecidableEq X] in
/-- **A blob with a non-bridge arc has a reticulation**: take a sink of the blob. -/
theorem exists_reticulation_or_forall_isBridge (hN : N.IsPhylogenetic) (v : V) :
    (∃ h, SameBlob N v h ∧ 2 ≤ N.graph.indegree h) ∨
      ∀ f, (N.graph.source f = v ∨ N.graph.target f = v) → IsBridge N f := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hno, f, hf, hnb⟩ := hcon
  obtain ⟨u, hu, hmin⟩ := exists_sink hN (S := {u | SameBlob N v u}) ⟨v, .refl⟩
  have hu₁ : N.graph.indegree u ≤ 1 := by
    have := hno u hu
    omega
  have hout : ∀ g, N.graph.source g = u → IsBridge N g := by
    rintro g rfl
    by_contra hg
    exact hmin _ (sameBlob_trans hu (sameBlob_of_not_isBridge hg)) (.single ⟨g, rfl, rfl⟩)
  have huall := forall_isBridge_of_indegree_le_one hN hu₁ hout
  have hvu : v = u := eq_of_sameBlob_of_forall_isBridge huall (sameBlob_symm hu)
  subst hvu
  exact hnb (huall f hf)

omit [Fintype X] [DecidableEq X] in
/-- No arc enters the root. -/
theorem target_ne_root (hN : N.IsPhylogenetic) (g : E) : N.graph.target g ≠ N.root := by
  intro hg
  have := hN.finite_arcs
  have h0 := hN.root_indegree
  rw [DirectedMultigraph.indegree, Set.ncard_eq_zero] at h0
  exact (Set.eq_empty_iff_forall_notMem.mp h0 g) hg

omit [Fintype X] [DecidableEq X] in
/-- Only the root reaches the root. -/
theorem eq_root_of_reaches_root (hN : N.IsPhylogenetic) {u : V} (h : N.graph.Reaches u N.root) :
    u = N.root := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨c, _, ⟨g, _, hg⟩⟩
  · exact heq.symm
  · exact absurd hg (target_ne_root hN g)

omit [Fintype X] [DecidableEq X] in
/-- A vertex with no outgoing arc other than the taxa: all arcs at a taxon are bridges. -/
theorem forall_isBridge_leaf (hN : N.IsPhylogenetic) (x : X) :
    ∀ f, (N.graph.source f = N.leaf x ∨ N.graph.target f = N.leaf x) → IsBridge N f := by
  have := hN.finite_arcs
  apply forall_isBridge_of_indegree_le_one hN (hN.leaf_indegree x).le
  intro g hg
  have h0 := (hN.leaves (N.leaf x)).mpr ⟨x, rfl⟩
  exact absurd hg ((DirectedMultigraph.outdegree_eq_zero_iff _ _).mp h0 g)

omit [Fintype X] [DecidableEq X] in
/-- A blob with a reticulation contains no taxon. -/
theorem leaf_not_sameBlob (hN : N.IsPhylogenetic) {v h : V} (hh : SameBlob N v h)
    (hh₂ : 2 ≤ N.graph.indegree h) (x : X) : ¬ SameBlob N v (N.leaf x) := by
  intro hx
  have := eq_of_sameBlob_of_forall_isBridge (forall_isBridge_leaf hN x)
    (sameBlob_trans (sameBlob_symm hx) hh)
  rw [this, hN.leaf_indegree] at hh₂
  omega

/-! ### Binary networks -/

omit [Fintype X] [DecidableEq X] in
theorem outdegree_le_two (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (u : V) :
    N.graph.outdegree u ≤ 2 := by
  by_cases hu : u = N.root
  · subst hu
    exact hBin.1.le
  · by_cases h0 : N.graph.outdegree u = 0
    · omega
    · have := hBin.2 u hu h0
      have := hN.nonroot_indegree u hu
      omega

omit [Fintype X] [DecidableEq X] in
theorem reticulation_ne_root (hN : N.IsPhylogenetic) {h : V} (hh : 2 ≤ N.graph.indegree h) :
    h ≠ N.root := by
  rintro rfl
  rw [hN.root_indegree] at hh
  omega

omit [Fintype X] [DecidableEq X] in
/-- A reticulation of a binary network has exactly one outgoing arc. -/
theorem outdegree_eq_one_of_reticulation (hN : N.IsPhylogenetic) (hBin : N.IsBinary) {h : V}
    (hh : 2 ≤ N.graph.indegree h) : N.graph.outdegree h = 1 := by
  have h0 : N.graph.outdegree h ≠ 0 := by
    intro h0
    obtain ⟨x, rfl⟩ := (hN.leaves h).mp h0
    rw [hN.leaf_indegree] at hh
    omega
  have := hBin.2 h (reticulation_ne_root hN hh) h0
  omega

/-! ### Level-1 blobs -/

section LevelOne

variable [Fintype V] [Fintype E]

omit [Fintype X] [DecidableEq X] in
/-- **A level-1 blob has at most one reticulation**: a blob with `k` reticulations has at least `2k`
reticulation arcs, none of them a bridge. -/
theorem reticulation_unique (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) {v h h' : V}
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) (hh' : SameBlob N v h')
    (hh'₂ : 2 ≤ N.graph.indegree h') : h = h' := by
  have hl := hLevel v
  set R : Finset V := univ.filter fun u => 2 ≤ N.graph.indegree u ∧ SameBlob N v u with hR
  set H : Finset E := univ.filter fun e => N.IsHybridArc e ∧ SameBlob N v (N.graph.source e) ∧
    SameBlob N v (N.graph.target e) with hH
  have hmaps : ∀ e ∈ H, N.graph.target e ∈ R := by
    intro e he
    simp only [hH, mem_filter, mem_univ, true_and] at he
    simp only [hR, mem_filter, mem_univ, true_and]
    exact ⟨he.1, he.2.2⟩
  have hfib : ∀ u ∈ R, 2 ≤ (H.filter fun e => N.graph.target e = u).card := by
    intro u hu
    simp only [hR, mem_filter, mem_univ, true_and] at hu
    have hsub : {e | N.graph.target e = u} ⊆ ((H.filter fun e => N.graph.target e = u : Finset E) : Set E) := by
      intro e he
      have he' : N.graph.target e = u := he
      subst he'
      simp only [hH, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq, and_true]
      refine ⟨hu.1, ?_, hu.2⟩
      exact sameBlob_trans hu.2
        (sameBlob_symm (sameBlob_of_not_isBridge (not_isBridge_of_two_le_indegree hN hu.1)))
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at this
    exact hu.1.trans this
  have hcard : R.card * 2 ≤ H.card := by
    rw [card_eq_sum_card_fiberwise hmaps]
    simpa using card_nsmul_le_sum R _ 2 hfib
  have hR1 : R.card ≤ 1 := by omega
  exact card_le_one.mp hR1 h (by simp [hR, hh₂, hh]) h' (by simp [hR, hh'₂, hh'])

omit [Fintype X] [DecidableEq X] in
/-- **Every vertex of a blob reaches its reticulation.** -/
theorem reaches_reticulation (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) {v h u : V}
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) (hu : SameBlob N v u) :
    N.graph.Reaches u h := by
  by_contra hcon
  obtain ⟨w, ⟨hw, hwh⟩, hmin⟩ :=
    exists_sink hN (S := {w | SameBlob N v w ∧ ¬ N.graph.Reaches w h}) ⟨u, hu, hcon⟩
  have hwne : w ≠ h := by
    rintro rfl
    exact hwh .refl
  have hin : N.graph.indegree w ≤ 1 := by
    by_contra hc
    exact hwne (reticulation_unique hN hLevel hw (by omega) hh hh₂)
  have hout : ∀ g, N.graph.source g = w → IsBridge N g := by
    rintro g rfl
    by_contra hg
    have h1 := sameBlob_trans hw (sameBlob_of_not_isBridge hg)
    by_cases h2 : N.graph.Reaches (N.graph.target g) h
    · exact hwh ((reaches_of_arc N g).trans h2)
    · exact hmin _ ⟨h1, h2⟩ (.single ⟨g, rfl, rfl⟩)
  have := eq_of_sameBlob_of_forall_isBridge (forall_isBridge_of_indegree_le_one hN hin hout)
    (sameBlob_trans (sameBlob_symm hw) hh)
  exact hwne this.symm

end LevelOne

omit [Fintype X] [DecidableEq X] in
/-- If `f` enters the descendants of `t`, then the path from `t` to its target uses no bridge. -/
theorem sameBlob_of_entering (hN : N.IsPhylogenetic) {t : V} {f : E}
    (hR : N.graph.Reaches t (N.graph.target f)) (hnot : ¬ N.graph.Reaches t (N.graph.source f)) :
    SameBlob N t (N.graph.target f) := by
  have key : ∀ w, N.graph.Reaches t w → N.graph.Reaches w (N.graph.target f) → SameBlob N t w := by
    intro w hw
    induction hw with
    | refl => exact fun _ => .refl
    | @tail a b hta hab ih =>
      intro hb
      obtain ⟨g, rfl, rfl⟩ := hab
      have hga : SameBlob N t (N.graph.source g) := ih ((reaches_of_arc N g).trans hb)
      refine sameBlob_trans hga (sameBlob_of_not_isBridge ?_)
      intro hbg
      have hfg : f ≠ g := by
        rintro rfl
        exact hnot hta
      have := (isBridge_iff_reaches hN g).mp hbg f hfg hb
      exact hnot ((hta.trans (reaches_of_arc N g)).trans this)
  exact key _ hR .refl

section LevelOne

variable [Fintype V] [Fintype E]

omit [Fintype X] [DecidableEq X] in
/-- An arc other than `e` that enters the descendants of the target of `e`, a vertex of the blob,
enters the reticulation of the blob. -/
theorem target_eq_reticulation (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) {v h : V}
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {e f : E}
    (ht : SameBlob N v (N.graph.target e)) (hfe : f ≠ e)
    (hR : N.graph.Reaches (N.graph.target e) (N.graph.target f))
    (hnot : ¬ N.graph.Reaches (N.graph.target e) (N.graph.source f)) : N.graph.target f = h := by
  have hsb := sameBlob_trans ht (sameBlob_of_entering hN hR hnot)
  have h2 : 2 ≤ N.graph.indegree (N.graph.target f) := by
    rcases Relation.ReflTransGen.cases_tail hR with heq | ⟨c, hc, ⟨g, rfl, hg⟩⟩
    · exact two_le_indegree_of_ne hN hfe heq
    · have hgf : f ≠ g := by
        rintro rfl
        exact hnot hc
      exact two_le_indegree_of_ne hN hgf hg.symm
  exact reticulation_unique hN hLevel hsb h2 hh hh₂

omit [Fintype X] [DecidableEq X] in
/-- **A non-bridge arc of the blob does not dominate the reticulation.** -/
theorem avoidingReach_root_reticulation (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) {v h : V}
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {e : E}
    (ht : SameBlob N v (N.graph.target e)) (he : ¬ IsBridge N e) :
    N.AvoidingReach e N.root h := by
  rw [isBridge_iff_reaches hN] at he
  push Not at he
  obtain ⟨f, hfe, hR, hnot⟩ := he
  have hfh := target_eq_reticulation hN hLevel hh hh₂ ht hfe hR hnot
  have hsf : N.AvoidingReach e N.root (N.graph.source f) :=
    (avoidingReach_or_reaches e (hN.root_reaches _)).resolve_right hnot
  rw [← hfh]
  exact hsf.tail ⟨f, hfe, rfl, rfl⟩

omit [Fintype X] [DecidableEq X] in
/-- An arc into a vertex of the blob dominates the taxa below it that are not below the
reticulation. -/
theorem dominates_of_below (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) {v h : V}
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {k : E} {x : X}
    (hc : SameBlob N v (N.graph.target k)) (hx : N.graph.Reaches (N.graph.target k) (N.leaf x))
    (hxh : ¬ N.graph.Reaches h (N.leaf x)) : N.Dominates k x := by
  intro hav
  have hroot : ¬ N.graph.Reaches (N.graph.target k) N.root :=
    fun hr => target_ne_root hN k (eq_root_of_reaches_root hN hr)
  obtain ⟨f, hfk, hs, ht, hfx⟩ := exists_entering_arc hav hroot hx
  have := target_eq_reticulation hN hLevel hh hh₂ hc hfk ht hs
  rw [this] at hfx
  exact hxh hfx

end LevelOne

/-! ### Entering a blob -/

omit [Fintype X] [DecidableEq X] in
/-- A vertex outside a blob with a descendant in the blob reaches the whole blob. -/
theorem reaches_of_reaches_blob (hN : N.IsPhylogenetic) {v t b u : V} (ht : ¬ SameBlob N v t)
    (hb : SameBlob N v b) (hR : N.graph.Reaches t b) (hu : SameBlob N v u) :
    N.graph.Reaches t u := by
  have : ∃ g, N.graph.Reaches t (N.graph.source g) ∧ ¬ SameBlob N v (N.graph.source g) ∧
      SameBlob N v (N.graph.target g) := by
    induction hR with
    | refl => exact absurd hb ht
    | @tail a b hta hab ih =>
      obtain ⟨g, rfl, rfl⟩ := hab
      by_cases ha : SameBlob N v (N.graph.source g)
      · exact ih ha
      · exact ⟨g, hta, ha, hb⟩
  obtain ⟨g, hg1, hg2, hg3⟩ := this
  have hgb : IsBridge N g := by
    by_contra hnb
    exact hg2 (sameBlob_trans hg3 (sameBlob_symm (sameBlob_of_not_isBridge hnb)))
  exact (hg1.trans (reaches_of_arc N g)).trans
    (reaches_of_sameBlob hN hgb (sameBlob_trans (sameBlob_symm hg3) hu))

omit [Fintype X] [DecidableEq X] in
/-- Every blob has a top vertex, reaching the whole blob. -/
theorem exists_top (hN : N.IsPhylogenetic) (v : V) :
    ∃ T, SameBlob N v T ∧ ∀ u, SameBlob N v u → N.graph.Reaches T u := by
  obtain ⟨T, hT, hmin⟩ := exists_source hN (S := {u | SameBlob N v u}) ⟨v, .refl⟩
  refine ⟨T, hT, fun u hu => ?_⟩
  by_cases hr : T = N.root
  · rw [hr]
    exact hN.root_reaches u
  · have := hN.finite_arcs
    have h1 := hN.nonroot_indegree T hr
    obtain ⟨g, hg⟩ : ∃ g, N.graph.target g = T := by
      by_contra hno
      push Not at hno
      have h0 : {e | N.graph.target e = T} = ∅ := Set.eq_empty_iff_forall_notMem.mpr hno
      simp [DirectedMultigraph.indegree, h0] at h1
    subst hg
    have hgb : IsBridge N g := by
      by_contra hnb
      exact hmin _ (sameBlob_trans hT (sameBlob_symm (sameBlob_of_not_isBridge hnb)))
        (.single ⟨g, rfl, rfl⟩)
    exact reaches_of_sameBlob hN hgb (sameBlob_trans (sameBlob_symm hT) hu)

omit [Fintype X] [DecidableEq X] in
/-- A bridge leaving a blob has no vertex of the blob below it. -/
theorem not_sameBlob_of_reaches_exit (hN : N.IsPhylogenetic) {v : V} {k : E} (hk : IsBridge N k)
    (hs : SameBlob N v (N.graph.source k)) {w : V} (hw : N.graph.Reaches (N.graph.target k) w) :
    ¬ SameBlob N v w := by
  intro hb
  exact not_reaches_source hN k
    ((reaches_iff_of_sameBlob hN hk (sameBlob_trans (sameBlob_symm hb) hs)).mp hw)

/-! ### Walks outside a blob -/

/-- One step of a walk outside the blob of `v`. -/
def BlockStep (N : RootedNetwork V E X) (v a b : V) : Prop :=
  ¬ SameBlob N v a ∧ ¬ SameBlob N v b ∧
    ∃ e, (N.graph.source e = a ∧ N.graph.target e = b) ∨ (N.graph.source e = b ∧ N.graph.target e = a)

/-- A walk outside the blob of `v`, possibly empty. -/
def BlockWalk (N : RootedNetwork V E X) (v : V) : V → V → Prop :=
  Relation.ReflTransGen (BlockStep N v)

omit [Fintype X] [DecidableEq X] in
theorem blockWalk_symm {v a b : V} (h : BlockWalk N v a b) : BlockWalk N v b a := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
    obtain ⟨h1, h2, e, he⟩ := hab
    exact Relation.ReflTransGen.head ⟨h2, h1, e, he.symm⟩ ih

omit [Fintype X] [DecidableEq X] in
theorem blockWalk_trans {v a b c : V} (h : BlockWalk N v a b) (h' : BlockWalk N v b c) :
    BlockWalk N v a c :=
  Relation.ReflTransGen.trans h h'

omit [Fintype X] [DecidableEq X] in
theorem not_sameBlob_of_blockWalk {v a b : V} (ha : ¬ SameBlob N v a) (h : BlockWalk N v a b) :
    ¬ SameBlob N v b := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨c, _, hc⟩
  · rwa [heq]
  · exact hc.2.1

omit [Fintype X] [DecidableEq X] in
/-- A nonempty walk has both ends outside the blob. -/
theorem not_sameBlob_of_blockWalk_of_ne {v a b : V} (h : BlockWalk N v a b) (hab : a ≠ b) :
    ¬ SameBlob N v a := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, _⟩
  · exact absurd heq hab
  · exact hc.1

omit [Fintype X] [DecidableEq X] in
/-- A directed path avoiding the blob is a walk outside it. -/
theorem blockWalk_of_reaches {v a b : V} (h : N.graph.Reaches a b)
    (hav : ∀ w, N.graph.Reaches a w → N.graph.Reaches w b → ¬ SameBlob N v w) :
    BlockWalk N v a b := by
  induction h with
  | refl => exact .refl
  | @tail c d hac hcd ih =>
    obtain ⟨e, rfl, rfl⟩ := hcd
    have hc := hav _ hac (reaches_of_arc N e)
    have hd := hav _ (hac.tail ⟨e, rfl, rfl⟩) .refl
    refine Relation.ReflTransGen.tail (ih fun w hw hwc => hav w hw (hwc.tail ⟨e, rfl, rfl⟩)) ?_
    exact ⟨hc, hd, e, Or.inl ⟨rfl, rfl⟩⟩

omit [Fintype X] [DecidableEq X] in
/-- **A component of the complement of a blob is the far side of a cut edge** (TOB-QMC, proof of
Lemma 4: "any taxa drawn from the same block attach to B via the same cut edge"). -/
theorem exists_blockWalk_cut (hN : N.IsPhylogenetic) {v a : V} (ha : ¬ SameBlob N v a) :
    ∃ e, IsBridge N e ∧ (∀ f, N.graph.Crosses f {u | BlockWalk N v a u} ↔ f = e) ∧
      ((SameBlob N v (N.graph.source e) ∧ BlockWalk N v a (N.graph.target e)) ∨
        (SameBlob N v (N.graph.target e) ∧ BlockWalk N v a (N.graph.source e))) := by
  set K : Set V := {u | BlockWalk N v a u} with hKdef
  have hKav : ∀ u ∈ K, ¬ SameBlob N v u := fun u hu => not_sameBlob_of_blockWalk ha hu
  have hcross : ∀ f, N.graph.Crosses f K →
      (SameBlob N v (N.graph.source f) ∧ N.graph.target f ∈ K) ∨
        (SameBlob N v (N.graph.target f) ∧ N.graph.source f ∈ K) := by
    rintro f (⟨hs, ht⟩ | ⟨ht, hs⟩)
    · right
      refine ⟨?_, hs⟩
      by_contra hb
      exact ht (Relation.ReflTransGen.tail hs ⟨hKav _ hs, hb, f, Or.inl ⟨rfl, rfl⟩⟩)
    · left
      refine ⟨?_, ht⟩
      by_contra hb
      exact hs (Relation.ReflTransGen.tail ht ⟨hKav _ ht, hb, f, Or.inr ⟨rfl, rfl⟩⟩)
  have hbridge : ∀ f, N.graph.Crosses f K → IsBridge N f := by
    intro f hf
    by_contra hnb
    have hsb := sameBlob_of_not_isBridge hnb
    rcases hcross f hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hKav _ h2 (sameBlob_trans h1 hsb)
    · exact hKav _ h2 (sameBlob_trans h1 (sameBlob_symm hsb))
  have hex : ∃ e, N.graph.Crosses e K := by
    by_contra hno
    push Not at hno
    have := N.graph.mem_iff_mem_of_walks (F := Set.univ) (S := K) (fun e _ hc => hno e hc)
      (N.graph_connected hN a v)
    exact hKav v (this.mp .refl) .refl
  have huniq : ∀ f g, N.graph.Crosses f K → N.graph.Crosses g K → g = f := by
    intro f g hf hg
    obtain ⟨S, hS⟩ := hbridge f hf
    have hK : ∀ u, BlockWalk N v a u → (a ∈ S ↔ u ∈ S) := by
      intro u hu
      induction hu with
      | refl => exact Iff.rfl
      | @tail b c hab hbc ih =>
        have hbK : b ∈ K := hab
        have hcK : c ∈ K := Relation.ReflTransGen.tail hab hbc
        obtain ⟨_, _, k, hk⟩ := hbc
        have hnc : ¬ N.graph.Crosses k S := by
          intro hc
          have hkf := (hS k).mp hc
          subst hkf
          rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rcases hf with ⟨_, h⟩ | ⟨_, h⟩
            · exact h hcK
            · exact h hbK
          · rcases hf with ⟨_, h⟩ | ⟨_, h⟩
            · exact h hbK
            · exact h hcK
        have heq : N.graph.source k ∈ S ↔ N.graph.target k ∈ S := by
          simp only [DirectedMultigraph.Crosses] at hnc
          tauto
        rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ih.trans heq
        · exact ih.trans heq.symm
    have hB : ∀ u, SameBlob N v u → (v ∈ S ↔ u ∈ S) := fun u hu => mem_iff_of_sameBlob hS hu
    have hne : ¬ (a ∈ S ↔ v ∈ S) := by
      intro hav
      have hfc := (hS f).mpr rfl
      simp only [DirectedMultigraph.Crosses] at hfc
      rcases hcross f hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hK _ h2
        have := hB _ h1
        tauto
      · have := hK _ h2
        have := hB _ h1
        tauto
    apply (hS g).mp
    simp only [DirectedMultigraph.Crosses]
    rcases hcross g hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hK _ h2
      have := hB _ h1
      tauto
    · have := hK _ h2
      have := hB _ h1
      tauto
  obtain ⟨e, he⟩ := hex
  refine ⟨e, hbridge e he, fun f => ⟨fun hf => huniq e f he hf, ?_⟩, hcross e he⟩
  rintro rfl
  exact he

omit [Fintype X] [DecidableEq X] in
/-- The far side of a cut edge from the blob, when the edge leaves the blob: it is below the edge. -/
theorem reaches_of_blockWalk_of_exit (hN : N.IsPhylogenetic) {v a : V} {e : E} (ha : ¬ SameBlob N v a)
    (hS : ∀ f, N.graph.Crosses f {u | BlockWalk N v a u} ↔ f = e)
    (hs : SameBlob N v (N.graph.source e)) {u : V} (hu : BlockWalk N v a u) :
    N.graph.Reaches (N.graph.target e) u := by
  have hsK : N.graph.source e ∉ {u | BlockWalk N v a u} :=
    fun hK => not_sameBlob_of_blockWalk ha hK hs
  exact reaches_of_mem_cut hS (root_notMem_of_cut hN hS hsK) hu (hN.root_reaches _)

omit [Fintype X] [DecidableEq X] in
/-- The far side of a cut edge from the blob, when the edge enters the blob: it contains the root
and no vertex below the edge. -/
theorem not_reaches_of_blockWalk_of_entry {v a : V} {e : E}
    (hS : ∀ f, N.graph.Crosses f {u | BlockWalk N v a u} ↔ f = e)
    (hs : BlockWalk N v a (N.graph.source e)) (ht : ¬ BlockWalk N v a (N.graph.target e)) {u : V}
    (hu : N.graph.Reaches (N.graph.target e) u) : ¬ BlockWalk N v a u := by
  have hS' : ∀ f, N.graph.Crosses f {u | BlockWalk N v a u}ᶜ ↔ f = e :=
    fun f => (crosses_compl_iff f _).trans (hS f)
  exact mem_of_reaches_of_cut hS' (not_not.mpr hs) ht hu

omit [Fintype X] [DecidableEq X] in
/-- With the cut edge entering the blob, the root is on the far side. -/
theorem blockWalk_root_of_entry {v a : V} {e : E} (hN : N.IsPhylogenetic)
    (hS : ∀ f, N.graph.Crosses f {u | BlockWalk N v a u} ↔ f = e)
    (hs : BlockWalk N v a (N.graph.source e)) : BlockWalk N v a N.root := by
  have hS' : ∀ f, N.graph.Crosses f {u | BlockWalk N v a u}ᶜ ↔ f = e :=
    fun f => (crosses_compl_iff f _).trans (hS f)
  have := root_notMem_of_cut hN hS' (not_not.mpr hs)
  exact not_not.mp this

/-! ### Four taxa in distinct blocks -/

/-- The taxa of `Y` below `u`. -/
def below (N : RootedNetwork V E X) (Y : Finset X) (u : V) : Finset X :=
  Y.filter fun x => N.graph.Reaches u (N.leaf x)

omit [Fintype X] [DecidableEq X] in
theorem mem_below {Y : Finset X} {u : V} {x : X} :
    x ∈ below N Y u ↔ x ∈ Y ∧ N.graph.Reaches u (N.leaf x) := by
  simp [below]

omit [Fintype X] [DecidableEq X] in
/-- Taxa below a common vertex with no blob vertex below it are in one block. -/
theorem blockWalk_of_both_below {v c : V} {x y : X}
    (hav : ∀ w, N.graph.Reaches c w → ¬ SameBlob N v w)
    (hx : N.graph.Reaches c (N.leaf x)) (hy : N.graph.Reaches c (N.leaf y)) :
    BlockWalk N v (N.leaf x) (N.leaf y) :=
  blockWalk_trans
    (blockWalk_symm (blockWalk_of_reaches hx fun w hw _ => hav w hw))
    (blockWalk_of_reaches hy fun w hw _ => hav w hw)

omit [Fintype X] [DecidableEq X] in
/-- At most one of two taxa in distinct blocks is not below the blob. -/
theorem reaches_top_of_not_blockWalk (hN : N.IsPhylogenetic) {v T : V} {x y : X}
    (hT : ∀ u, SameBlob N v u → N.graph.Reaches T u)
    (hxy : ¬ BlockWalk N v (N.leaf x) (N.leaf y)) :
    N.graph.Reaches T (N.leaf x) ∨ N.graph.Reaches T (N.leaf y) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hx, hy⟩ := hcon
  apply hxy
  exact blockWalk_trans
    (blockWalk_symm (blockWalk_of_reaches (hN.root_reaches _)
      fun w _ hwx hb => hx ((hT w hb).trans hwx)))
    (blockWalk_of_reaches (hN.root_reaches _) fun w _ hwy hb => hy ((hT w hb).trans hwy))

omit [Fintype X] in
/-- **Four taxa in distinct blocks at a blob of a binary network: some arc inside the blob has exactly
two of them below it.** Descend in the blob from its top, where at least three of the taxa are below,
using that a vertex has at most two children. -/
theorem exists_arc_two_below [Fintype E] (hN : N.IsPhylogenetic) (hBin : N.IsBinary) {v : V}
    {Y : Finset X} (hY : Y.card = 4)
    (hdist : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → ¬ BlockWalk N v (N.leaf x) (N.leaf y)) :
    ∃ k, SameBlob N v (N.graph.source k) ∧ SameBlob N v (N.graph.target k) ∧
      (below N Y (N.graph.target k)).card = 2 := by
  obtain ⟨T, hT, hTall⟩ := exists_top hN v
  have hT3 : 3 ≤ (below N Y T).card := by
    have hle : (Y.filter fun x => ¬ N.graph.Reaches T (N.leaf x)).card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      simp only [mem_filter] at hx hy
      by_contra hxy
      rcases reaches_top_of_not_blockWalk hN hTall (hdist x hx.1 y hy.1 hxy) with h | h
      · exact hx.2 h
      · exact hy.2 h
    have hadd := card_filter_add_card_filter_not (s := Y) fun x => N.graph.Reaches T (N.leaf x)
    unfold below
    omega
  obtain ⟨u, ⟨hu, hu3⟩, hmin⟩ := exists_sink hN (S := {u | SameBlob N v u ∧ 3 ≤ (below N Y u).card})
    ⟨T, hT, hT3⟩
  -- a child outside the blob has at most one taxon of `Y` below it
  have hexit : ∀ k, N.graph.source k = u → ¬ SameBlob N v (N.graph.target k) →
      (below N Y (N.graph.target k)).card ≤ 1 := by
    rintro k rfl hc
    have hkb : IsBridge N k := by
      by_contra hnb
      exact hc (sameBlob_trans hu (sameBlob_of_not_isBridge hnb))
    apply card_le_one.mpr
    intro x hx y hy
    rw [mem_below] at hx hy
    by_contra hxy
    exact hdist x hx.1 y hy.1 hxy (blockWalk_of_both_below
      (fun w hw => not_sameBlob_of_reaches_exit hN hkb hu hw) hx.2 hy.2)
  -- a child inside the blob has at most two
  have hinner : ∀ k, N.graph.source k = u → SameBlob N v (N.graph.target k) →
      (below N Y (N.graph.target k)).card ≤ 2 := by
    rintro k rfl hc
    by_contra hk
    exact hmin _ ⟨hc, by omega⟩ (.single ⟨k, rfl, rfl⟩)
  -- `u` is not a taxon, as it has three taxa below it
  have hnotleaf : ∀ x, N.leaf x ≠ u := by
    rintro x rfl
    have := hN.finite_arcs
    have h0 := (hN.leaves (N.leaf x)).mpr ⟨x, rfl⟩
    have : (below N Y (N.leaf x)).card ≤ 1 := by
      apply card_le_one.mpr
      intro a ha b hb
      rw [mem_below] at ha hb
      have h1 := N.graph.eq_of_reaches_of_outdegree_eq_zero ha.2 h0
      have h2 := N.graph.eq_of_reaches_of_outdegree_eq_zero hb.2 h0
      exact hN.leaf_injective (h1.trans h2.symm)
    omega
  -- pigeonhole over the at most two children
  by_contra hcon
  push Not at hcon
  have hall : ∀ k, N.graph.source k = u → (below N Y (N.graph.target k)).card ≤ 1 := by
    intro k hk
    by_cases hc : SameBlob N v (N.graph.target k)
    · have h1 := hinner k hk hc
      have h2 := hcon k (hk ▸ hu) hc
      omega
    · exact hexit k hk hc
  set Out : Finset E := univ.filter fun k => N.graph.source k = u with hOut
  have hOutcard : Out.card ≤ 2 := by
    have := outdegree_le_two hN hBin u
    rw [DirectedMultigraph.outdegree] at this
    have heq : {e | N.graph.source e = u} = ((Out : Finset E) : Set E) := by
      ext e
      simp [hOut]
    rwa [heq, Set.ncard_coe_finset] at this
  have hsub : below N Y u ⊆ Out.biUnion fun k => below N Y (N.graph.target k) := by
    intro x hx
    rw [mem_below] at hx
    rcases Relation.ReflTransGen.cases_head hx.2 with heq | ⟨c, ⟨k, hk, rfl⟩, hc⟩
    · exact absurd heq.symm (hnotleaf x)
    · exact mem_biUnion.mpr ⟨k, by simp [hOut, hk], mem_below.mpr ⟨hx.1, hc⟩⟩
  have hle : (below N Y u).card ≤ Out.card * 1 := by
    refine (card_le_card hsub).trans ?_
    refine card_biUnion_le_card_mul _ _ _ ?_
    intro k hk
    exact hall k (by simpa [hOut] using hk)
  omega

omit [Fintype X] [DecidableEq X] in
/-- Taxa below the reticulation are in one block. -/
theorem blockWalk_of_below_reticulation [Fintype V] [Fintype E] (hN : N.IsPhylogenetic)
    (hBin : N.IsBinary) (hLevel : IsLevelOne N) {v h : V}
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {x y : X}
    (hx : N.graph.Reaches h (N.leaf x)) (hy : N.graph.Reaches h (N.leaf y)) :
    BlockWalk N v (N.leaf x) (N.leaf y) := by
  have hne : ∀ z, N.leaf z ≠ h := by
    rintro z rfl
    rw [hN.leaf_indegree] at hh₂
    omega
  rcases Relation.ReflTransGen.cases_head hx with heq | ⟨c, ⟨k, hk, rfl⟩, hc⟩
  · exact absurd heq.symm (hne x)
  rcases Relation.ReflTransGen.cases_head hy with heq | ⟨c', ⟨k', hk', rfl⟩, hc'⟩
  · exact absurd heq.symm (hne y)
  have hkk : k = k' := by
    have h1 := outdegree_eq_one_of_reticulation hN hBin hh₂
    rw [DirectedMultigraph.outdegree, Set.ncard_eq_one] at h1
    obtain ⟨a, ha⟩ := h1
    have h3 : k ∈ {e | N.graph.source e = h} := hk
    have h4 : k' ∈ {e | N.graph.source e = h} := hk'
    rw [ha] at h3 h4
    exact h3.trans h4.symm
  subst hkk
  subst hk
  refine blockWalk_of_both_below (fun w hw hb => ?_) hc hc'
  exact hN.acyclic _ (transGen_of_arc_reaches (hw.trans (reaches_reticulation hN hLevel hh hh₂ hb)))

end TOBQMC.Level1
