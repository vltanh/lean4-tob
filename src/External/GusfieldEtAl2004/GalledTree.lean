module

public import External.GusfieldEtAl2004.SameBlob
public import Gusfield2007.ExplicitNetworks

/-!
# Reduced galled trees are fully decomposed (Gusfield, Eddhu, Langley 2004)

See the `README.md` of this directory. Definitions 1.3, 1.4 and 2.2 of the source are `IsGall`, `IsGalledTree` and `IsReducedGalledTree`, Theorem 2.4 is `theorem2_4`, Theorem 2.5 is
`theorem2_5`, and Lemma 2.3 is `lemma2_3`. Gusfield et al. 2007 cite the conclusion at line 180 (`IsReducedGalledTree.isFullyDecomposedFor_conflictGraph`,
`IsReducedGalledTree.isFullyDecomposedFor_incompatGraph`). Its wording of "reduced" at that line is weaker than the source's, and with it the claim fails (`line180_printed_false`).

## The columns on a gall

Set the nodes of a gall on a line: one side going up to the coalescent node, and the other going down from it. The site of an arc of the gall is a threshold on this line, and the column of the site, compared
with the recombination node, is one side of the threshold (`OnSide`). This is the content of Theorem 2.2 of the source: two sites in conflict are of different kinds, which is its statement that
they are on different sides of the recombination point, and the three arrays W1, W2, W3 are the three ways to place the two thresholds.
-/

@[expose] public section

open scoped Classical

namespace GusfieldEtAl2004

open Gusfield2007 Gusfield2007.Network

variable {ι V E : Type*}

/-- **Definition 1.3** of the source: a gall is a recombination cycle that shares no node with any other recombination cycle. -/
def IsGall (N : Network ι V E) (Q : Set E) : Prop :=
  N.IsCycle Q ∧ ∀ Q', N.IsCycle Q' → Q' ≠ Q → Disjoint (N.blobVerts Q) (N.blobVerts Q')

/-- **Definition 1.4** of the source: a galled tree is a network whose recombination cycles are all galls. -/
def IsGalledTree (N : Network ι V E) : Prop := ∀ Q, N.IsCycle Q → IsGall N Q

/-- **Definition 2.2** of the source: a galled tree is reduced if every gall contains at least one conflicted pair of sites, and contains no unconflicted sites. `G` is the graph of the conflicts: in the
source, the conflict graph relative to the ancestral sequence (`conflictGraph`), and in the unrooted setting of Gusfield et al. 2007 the incompatibility graph (`incompatGraph`).

The wording of Gusfield et al. 2007, line 180, "every recombination cycle contains some incompatible sites", leaves out the second condition, which full decomposition needs: a compatible site on a gall isn't on a tree edge. -/
structure IsReducedGalledTree (N : Network ι V E) (G : SimpleGraph ι) : Prop where
  galled : IsGalledTree N
  exists_conflict : ∀ Q, N.IsCycle Q → ∃ i j, N.site i ∈ Q ∧ N.site j ∈ Q ∧ G.Adj i j
  no_unconflicted : ∀ Q, N.IsCycle Q → ∀ i, N.site i ∈ Q → ∃ j, G.Adj i j

section Thresholds

variable {L : Finset (ι → Bool)} {D : Set ι} {x₀ : ι → Bool} {kind : ι → Prop} {τ : ι → ℤ}

/-- The side of the threshold of the site `s` that the coordinate `z` is on: the side where the column differs from the recombination node. -/
def OnSide (kind : ι → Prop) (τ : ι → ℤ) (z : ℤ) (s : ι) : Prop := (kind s ∧ τ s < z) ∨ (¬ kind s ∧ z < τ s)

/-- A row is at the coordinate `z`, on the sites `D`. -/
def Seen (L : Finset (ι → Bool)) (D : Set ι) (x₀ : ι → Bool) (kind : ι → Prop) (τ : ι → ℤ) (z : ℤ) : Prop :=
  ∃ r ∈ L, ∀ s ∈ D, (r s ≠ x₀ s ↔ OnSide kind τ z s)

/-- The two thresholds `a`, `b` are of different kinds, and three rows show that the columns are in conflict relative to the recombination node. -/
def Straddles (L : Finset (ι → Bool)) (D : Set ι) (x₀ : ι → Bool) (kind : ι → Prop) (τ : ι → ℤ) (a b : ι) : Prop :=
  kind a ∧ ¬ kind b ∧ (∃ z, Seen L D x₀ kind τ z ∧ τ a < z ∧ z < τ b) ∧ (∃ z, Seen L D x₀ kind τ z ∧ τ a < z ∧ ¬ z < τ b) ∧
    ∃ z, Seen L D x₀ kind τ z ∧ ¬ τ a < z ∧ z < τ b

/-- Two incompatible columns on the line: all of the pairs that differ from the recombination node's. -/
theorem exists_seen_of_incompatible (hrow : ∀ r ∈ L, (∀ s ∈ D, r s = x₀ s) ∨ ∃ z, ∀ s ∈ D, (r s ≠ x₀ s ↔ OnSide kind τ z s)) {s t : ι} (hs : s ∈ D) (ht : t ∈ D)
    (h : Incompatible L s t) (d₁ d₂ : Bool) (hd : d₁ = true ∨ d₂ = true) :
    ∃ z, Seen L D x₀ kind τ z ∧ (OnSide kind τ z s ↔ d₁ = true) ∧ (OnSide kind τ z t ↔ d₂ = true) := by
  obtain ⟨r, hr, h₁, h₂⟩ := h (xor (x₀ s) d₁) (xor (x₀ t) d₂)
  have hd₁ : r s ≠ x₀ s ↔ d₁ = true := by
    rw [h₁]
    cases x₀ s <;> cases d₁ <;> simp
  have hd₂ : r t ≠ x₀ t ↔ d₂ = true := by
    rw [h₂]
    cases x₀ t <;> cases d₂ <;> simp
  rcases hrow r hr with hx | ⟨z, hz⟩
  · exfalso
    rcases hd with hd | hd
    · exact hd₁.2 hd (hx s hs)
    · exact hd₂.2 hd (hx t ht)
  · exact ⟨z, ⟨r, hr, hz⟩, (hz s hs).symm.trans hd₁, (hz t ht).symm.trans hd₂⟩

/-- **Two incompatible columns straddle**, in one order or the other. -/
theorem straddles_of_incompatible (hrow : ∀ r ∈ L, (∀ s ∈ D, r s = x₀ s) ∨ ∃ z, ∀ s ∈ D, (r s ≠ x₀ s ↔ OnSide kind τ z s)) {s t : ι} (hs : s ∈ D) (ht : t ∈ D)
    (h : Incompatible L s t) : Straddles L D x₀ kind τ s t ∨ Straddles L D x₀ kind τ t s := by
  obtain ⟨z₁, hz₁, h₁s, h₁t⟩ := exists_seen_of_incompatible hrow hs ht h true true (Or.inl rfl)
  obtain ⟨z₂, hz₂, h₂s, h₂t⟩ := exists_seen_of_incompatible hrow hs ht h true false (Or.inl rfl)
  obtain ⟨z₃, hz₃, h₃s, h₃t⟩ := exists_seen_of_incompatible hrow hs ht h false true (Or.inr rfl)
  simp only [OnSide, iff_true, Bool.false_eq_true, iff_false] at h₁s h₁t h₂s h₂t h₃s h₃t
  by_cases hks : kind s <;> by_cases hkt : kind t <;> simp only [hks, hkt, true_and, false_and, or_false, not_true_eq_false, not_false_eq_true, false_or] at h₁s h₁t h₂s h₂t h₃s h₃t
  · exfalso
    omega
  · exact Or.inl ⟨hks, hkt, ⟨z₁, hz₁, h₁s, h₁t⟩, ⟨z₂, hz₂, h₂s, h₂t⟩, ⟨z₃, hz₃, h₃s, h₃t⟩⟩
  · exact Or.inr ⟨hkt, hks, ⟨z₁, hz₁, h₁t, h₁s⟩, ⟨z₃, hz₃, h₃t, h₃s⟩, ⟨z₂, hz₂, h₂t, h₂s⟩⟩
  · exfalso
    omega

/-- Two columns that straddle are incompatible, with the row of the recombination node for the fourth pair. -/
theorem incompatible_of_straddles (hx : ∃ r ∈ L, ∀ s ∈ D, r s = x₀ s) {a b : ι} (ha : a ∈ D) (hb : b ∈ D) (h : Straddles L D x₀ kind τ a b) : Incompatible L a b := by
  obtain ⟨hka, hkb, ⟨z₁, ⟨r₁, hr₁, hs₁⟩, h₁a, h₁b⟩, ⟨z₂, ⟨r₂, hr₂, hs₂⟩, h₂a, h₂b⟩, ⟨z₃, ⟨r₃, hr₃, hs₃⟩, h₃a, h₃b⟩⟩ := h
  have hOa : ∀ z, OnSide kind τ z a ↔ τ a < z := fun z => by simp [OnSide, hka]
  have hOb : ∀ z, OnSide kind τ z b ↔ z < τ b := fun z => by simp [OnSide, hkb]
  have flip : ∀ {u v w : Bool}, u ≠ w → v ≠ w → u = v := by decide
  intro p q
  by_cases hp : p = x₀ a <;> by_cases hq : q = x₀ b
  · obtain ⟨r, hr, hrs⟩ := hx
    exact ⟨r, hr, by rw [hrs a ha, hp], by rw [hrs b hb, hq]⟩
  · refine ⟨r₃, hr₃, ?_, flip ((hs₃ b hb).2 ((hOb z₃).2 h₃b)) hq⟩
    by_contra hne
    exact h₃a ((hOa z₃).1 ((hs₃ a ha).1 (fun h' => hne (h'.trans hp.symm))))
  · refine ⟨r₂, hr₂, flip ((hs₂ a ha).2 ((hOa z₂).2 h₂a)) hp, ?_⟩
    by_contra hne
    exact h₂b ((hOb z₂).1 ((hs₂ b hb).1 (fun h' => hne (h'.trans hq.symm))))
  · exact ⟨r₁, hr₁, flip ((hs₁ a ha).2 ((hOa z₁).2 h₁a)) hp, flip ((hs₁ b hb).2 ((hOb z₁).2 h₁b)) hq⟩

/-- "The `i, j` state-pair at `x` differs from the `i, j` state-pair at every other node on `Q`" (after the proof of Theorem 2.2 of the source): a row at a coordinate differs from the recombination node at one of two incompatible columns. -/
theorem onSide_or_of_incompatible (hrow : ∀ r ∈ L, (∀ s ∈ D, r s = x₀ s) ∨ ∃ z, ∀ s ∈ D, (r s ≠ x₀ s ↔ OnSide kind τ z s)) {s t : ι} (hs : s ∈ D) (ht : t ∈ D)
    (h : Incompatible L s t) (z : ℤ) : OnSide kind τ z s ∨ OnSide kind τ z t := by
  rcases straddles_of_incompatible hrow hs ht h with ⟨hks, hkt, ⟨z₁, -, h₁, h₂⟩, -⟩ | ⟨hkt, hks, ⟨z₁, -, h₁, h₂⟩, -⟩
  · simp only [OnSide, hks, hkt, true_and, false_and, or_false, not_true_eq_false, not_false_eq_true, false_or]
    omega
  · simp only [OnSide, hks, hkt, true_and, false_and, or_false, not_true_eq_false, not_false_eq_true, false_or]
    omega

/-- Two incompatible columns on the line need a row with the state of the recombination node at every site on the line. -/
theorem exists_row_of_incompatible (hrow : ∀ r ∈ L, (∀ s ∈ D, r s = x₀ s) ∨ ∃ z, ∀ s ∈ D, (r s ≠ x₀ s ↔ OnSide kind τ z s)) {s t : ι} (hs : s ∈ D) (ht : t ∈ D)
    (h : Incompatible L s t) : ∃ r ∈ L, ∀ u ∈ D, r u = x₀ u := by
  obtain ⟨r, hr, h₁, h₂⟩ := h (x₀ s) (x₀ t)
  rcases hrow r hr with hx | ⟨z, hz⟩
  · exact ⟨r, hr, hx⟩
  · rcases onSide_or_of_incompatible hrow hs ht h z with h' | h'
    · exact absurd h₁ ((hz s hs).2 h')
    · exact absurd h₂ ((hz t ht).2 h')

/-- The argument of Lemma 2.3 of the source: of two pairs that straddle, the one with the lower threshold of the second kind exchanges with the other. -/
theorem Straddles.cross {a₁ b₁ a₂ b₂ : ι} (h₁ : Straddles L D x₀ kind τ a₁ b₁) (h₂ : Straddles L D x₀ kind τ a₂ b₂) (hle : τ b₁ ≤ τ b₂) :
    Straddles L D x₀ kind τ a₁ b₂ := by
  obtain ⟨hka, -, ⟨z₁, hz₁, h₁a, h₁b⟩, -, ⟨z₃, hz₃, h₃a, h₃b⟩⟩ := h₁
  obtain ⟨-, hkb, -, ⟨z₂, hz₂, h₂a, h₂b⟩, -⟩ := h₂
  refine ⟨hka, hkb, ⟨z₁, hz₁, h₁a, by omega⟩, ⟨z₂, hz₂, by omega, h₂b⟩, ⟨z₃, hz₃, h₃a, by omega⟩⟩

/-- Sites on one line with incompatibilities are all in one connected component, in the exchange form of Lemma 2.3. -/
theorem threshold_exchange (hx : ∃ r ∈ L, ∀ s ∈ D, r s = x₀ s)
    (hrow : ∀ r ∈ L, (∀ s ∈ D, r s = x₀ s) ∨ ∃ z, ∀ s ∈ D, (r s ≠ x₀ s ↔ OnSide kind τ z s)) {i j k l : ι} (hi : i ∈ D) (hj : j ∈ D) (hk : k ∈ D) (hl : l ∈ D)
    (hij : Incompatible L i j) (hkl : Incompatible L k l) : (incompatGraph L).Reachable i k := by
  have hadj : (incompatGraph L).Adj i j := hij
  have hadj' : (incompatGraph L).Adj k l := hkl
  have hnorm : ∀ {u v : ι}, u ∈ D → v ∈ D → Incompatible L u v → (incompatGraph L).Reachable u v →
      ∃ a b, a ∈ D ∧ b ∈ D ∧ Straddles L D x₀ kind τ a b ∧ (incompatGraph L).Reachable u a ∧ (incompatGraph L).Reachable u b := by
    intro u v hu hv huv hr
    rcases straddles_of_incompatible hrow hu hv huv with h | h
    · exact ⟨u, v, hu, hv, h, .refl _, hr⟩
    · exact ⟨v, u, hv, hu, h, hr, .refl _⟩
  obtain ⟨a₁, b₁, ha₁, hb₁, h₁, r₁, r₁'⟩ := hnorm hi hj hij hadj.reachable
  obtain ⟨a₂, b₂, ha₂, hb₂, h₂, r₂, r₂'⟩ := hnorm hk hl hkl hadj'.reachable
  rcases le_total (τ b₁) (τ b₂) with hle | hle
  · have hc : (incompatGraph L).Adj a₁ b₂ := incompatible_of_straddles hx ha₁ hb₂ (h₁.cross h₂ hle)
    exact r₁.trans (hc.reachable.trans r₂'.symm)
  · have hc : (incompatGraph L).Adj a₂ b₁ := incompatible_of_straddles hx ha₂ hb₁ (h₂.cross h₁ hle)
    exact r₁'.trans (hc.reachable.symm.trans r₂.symm)

/-- `threshold_exchange`, with the row of the recombination node from the incompatibility. -/
theorem threshold_exchange_of_incompatible (hrow : ∀ r ∈ L, (∀ s ∈ D, r s = x₀ s) ∨ ∃ z, ∀ s ∈ D, (r s ≠ x₀ s ↔ OnSide kind τ z s)) {i j k l : ι} (hi : i ∈ D) (hj : j ∈ D) (hk : k ∈ D) (hl : l ∈ D)
    (hij : Incompatible L i j) (hkl : Incompatible L k l) : (incompatGraph L).Reachable i k :=
  threshold_exchange (exists_row_of_incompatible hrow hi hj hij) hrow hi hj hk hl hij hkl

end Thresholds

section Gall

variable {N : Network ι V E}

/-- A cycle sharing an arc with a gall is that gall. -/
theorem IsGalledTree.eq_of_inter (hG : IsGalledTree N) {Q Q' : Set E} (hQ : N.IsCycle Q) (hQ' : N.IsCycle Q') (h : (Q ∩ Q').Nonempty) : Q' = Q := by
  by_contra hne
  obtain ⟨e, he, he'⟩ := h
  exact Set.disjoint_left.1 ((hG Q hQ).2 Q' hQ' hne) (Or.inl ⟨e, he, rfl⟩) (Or.inl ⟨e, he', rfl⟩)

/-- A blob of a galled tree is a gall. -/
theorem IsGalledTree.isCycle_of_isBlob (hG : IsGalledTree N) {B : Set E} (hB : N.IsBlob B) : N.IsCycle B := by
  obtain ⟨Q, hQ, rfl⟩ := hB
  have hall : ∀ Q', Relation.ReflTransGen N.ShareArc Q Q' → Q' = Q := by
    intro Q' hr
    induction hr with
    | refl => rfl
    | tail _ hs ih =>
      obtain ⟨h₁, h₂, h₃⟩ := hs
      subst ih
      exact hG.eq_of_inter h₁ h₂ h₃
  have heq : ⋃₀ {Q' | Relation.ReflTransGen N.ShareArc Q Q'} = Q := by
    ext e
    constructor
    · rintro ⟨Q', hr, he⟩
      rw [hall Q' hr] at he
      exact he
    · exact fun he => ⟨Q, .refl, he⟩
  rwa [heq]

/-- Two arcs of a path with one target are one arc. -/
theorem path_eq_of_tgt_eq {u v : V} {p : List E} {e f : E} (h : N.IsPath u v p) (he : e ∈ p) (hf : f ∈ p) (ht : N.tgt e = N.tgt f) : e = f := by
  obtain ⟨p₁, p₂, rfl, h₁, h₂⟩ := h.split he
  rcases List.mem_append.1 hf with hf | hf
  · obtain ⟨_, r, -, -, hr⟩ := h₁.split hf
    exact absurd (ht ▸ hr.reach) (not_reach_tgt_src e)
  · rcases List.mem_cons.1 hf with hf | hf
    · exact hf.symm
    · obtain ⟨r, _, -, hr, -⟩ := h₂.split hf
      exact absurd (ht ▸ hr.reach) (not_reach_tgt_src f)

variable {w x : V} {p q : List E}

theorem cycle_reach_src (hc : N.IsCycleOn w x p q) {e : E} (he : e ∈ p ∨ e ∈ q) : N.Reach w (N.src e) :=
  he.elim hc.2.1.reach_src_of_mem hc.2.2.1.reach_src_of_mem

theorem cycle_reach_tgt (hc : N.IsCycleOn w x p q) {e : E} (he : e ∈ p ∨ e ∈ q) : N.Reach (N.tgt e) x :=
  he.elim hc.2.1.reach_tgt_of_mem hc.2.2.1.reach_tgt_of_mem

/-- Each node of a recombination cycle reaches its recombination node. -/
theorem cycle_reach_of_mem (hc : N.IsCycleOn w x p q) {v : V} (hv : v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}) : N.Reach v x := by
  rcases hv with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · exact (reach_src_tgt e).trans (cycle_reach_tgt hc he)
  · exact cycle_reach_tgt hc he

/-- A node of a recombination cycle is its recombination node, or at the end of the start of one of its paths. -/
theorem cycle_mem_cases (hc : N.IsCycleOn w x p q) {v : V} (hv : v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}) :
    v = x ∨ (∃ c d, p = c ++ d ∧ d ≠ [] ∧ N.IsPath w v c) ∨ ∃ c d, q = c ++ d ∧ d ≠ [] ∧ N.IsPath w v c := by
  have key : ∀ {l : List E} (_ : N.IsPath w x l) {e : E} (_ : e ∈ l), (v = N.src e ∨ v = N.tgt e) → v = x ∨ ∃ c d, l = c ++ d ∧ d ≠ [] ∧ N.IsPath w v c := by
    rintro l hl e he (rfl | rfl)
    · obtain ⟨l₁, l₂, rfl, h₁, -⟩ := hl.split he
      exact Or.inr ⟨l₁, e :: l₂, rfl, by simp, h₁⟩
    · obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := hl.split he
      cases l₂ with
      | nil => exact Or.inl h₂
      | cons f l₃ => exact Or.inr ⟨l₁ ++ [e], f :: l₃, by simp, by simp, h₁.append ⟨rfl, rfl⟩⟩
  have hsplit : ∃ e, (e ∈ p ∨ e ∈ q) ∧ (v = N.src e ∨ v = N.tgt e) := by
    rcases hv with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · exact ⟨e, he, Or.inl rfl⟩
    · exact ⟨e, he, Or.inr rfl⟩
  obtain ⟨e, he | he, hve⟩ := hsplit
  · rcases key hc.2.1 he hve with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases key hc.2.2.1 he hve with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

variable [Finite V]

/-- The coalescent node has the state of the root at the sites of the cycle. -/
theorem label_coalescent (hc : N.IsCycleOn w x p q) {s : ι} (hs : N.site s ∈ {e | e ∈ p ∨ e ∈ q}) : N.label w s = N.label N.root s := by
  by_contra h
  exact not_reach_tgt_src _ ((N.reach_of_label_ne h).trans (cycle_reach_src hc hs))

/-- **Lemma 2.1 of the source.** An arc whose target is off a gall leaves the states of the sites on the gall as they are: a difference at the parents of a recombination node would make a cycle through the
site, and so it would be the gall. -/
theorem label_tgt_of_notMem (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) {f : E} (hf : N.tgt f ∉ N.blobVerts {e | e ∈ p ∨ e ∈ q}) {s : ι}
    (hs : N.site s ∈ {e | e ∈ p ∨ e ∈ q}) : N.label (N.tgt f) s = N.label (N.src f) s := by
  have hsf : N.site s ≠ f := fun h => hf (Or.inr ⟨N.site s, hs, by rw [h]⟩)
  by_cases hu : ∀ g, N.tgt g = N.tgt f → g = f
  · have := N.label_tree f hu s
    rwa [ite_eq_right hsf] at this
  · push Not at hu
    obtain ⟨g, hg, hne⟩ := hu
    have hpar : N.label (N.src f) s = N.label (N.src g) s := by
      by_contra hd
      obtain ⟨Q, hQ, hfQ, -, hsQ⟩ := exists_isCycle_of_label_ne hne.symm hg.symm hd
      have heq := hG.eq_of_inter ⟨w, x, p, q, hc, rfl⟩ hQ ⟨_, hs, hsQ⟩
      rw [heq] at hfQ
      exact hf (Or.inr ⟨f, hfQ, rfl⟩)
    rcases N.label_recomb f g hne.symm hg.symm s with h | h
    · exact h
    · exact h.trans hpar.symm

/-- **The rows on a gall.** On the sites of a gall, each node has the label of a node of the gall. -/
theorem exists_mem_label_eq (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) (y : V) :
    ∃ v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}, ∀ s, N.site s ∈ {e | e ∈ p ∨ e ∈ q} → N.label y s = N.label v s := by
  refine N.arc_induction (P := fun y => ∃ v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}, ∀ s, N.site s ∈ {e | e ∈ p ∨ e ∈ q} → N.label y s = N.label v s) (fun y ih => ?_) y
  by_cases hy : y ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}
  · exact ⟨y, hy, fun _ _ => rfl⟩
  by_cases hno : ∀ e, N.tgt e ≠ y
  · obtain rfl := (N.root_iff y).1 hno
    have hwmem : w ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q} := by
      cases hpe : p with
      | nil => exact absurd hpe hc.ne_nil
      | cons f l =>
        have hsrc : N.src f = w := by
          have := hc.2.1
          rw [hpe] at this
          exact this.1
        exact Or.inl ⟨f, Or.inl (by simp), hsrc⟩
    exact ⟨w, hwmem, fun s hs => (label_coalescent hc hs).symm⟩
  · push Not at hno
    obtain ⟨f, rfl⟩ := hno
    obtain ⟨v, hv, hvs⟩ := ih f rfl
    exact ⟨v, hv, fun s hs => (label_tgt_of_notMem hG hc hy hs).trans (hvs s hs)⟩

/-- The states along a side of a gall: at the end of the start `c` of a side, other than the recombination node, exactly the sites on `c` differ from the root. -/
theorem label_cut (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) {c d : List E} {v : V} (hp : p = c ++ d) (hd : d ≠ []) (hv : N.IsPath w v c) {s : ι}
    (hs : N.site s ∈ {e | e ∈ p ∨ e ∈ q}) : N.label v s ≠ N.label N.root s ↔ N.site s ∈ c := by
  induction c using List.reverseRecOn generalizing v d with
  | nil =>
    obtain rfl : w = v := hv
    simpa using label_coalescent hc hs
  | append_singleton c₀ a ih =>
    obtain ⟨y, h₁, ⟨rfl, rfl⟩⟩ := isPath_append.1 hv
    have hp' : p = c₀ ++ a :: d := by simp [hp]
    have hap : a ∈ p := by simp [hp']
    -- the node isn't the recombination node
    have hvx : N.tgt a ≠ x := by
      intro h
      have hdp := hc.2.1
      rw [hp', isPath_append] at hdp
      obtain ⟨y', -, -, hrest⟩ := hdp
      rw [h] at hrest
      exact hd hrest.eq_nil_of_self
    -- it has one arc in
    have hu : ∀ g, N.tgt g = N.tgt a → g = a := by
      intro g hg
      by_contra hne
      obtain ⟨Q, hQ, hgQ, haQ⟩ := exists_isCycle_of_tgt_eq hne hg
      have heq := hG.eq_of_inter ⟨w, x, p, q, hc, rfl⟩ hQ ⟨a, Or.inl hap, haQ⟩
      rw [heq] at hgQ
      rcases hgQ with hgQ | hgQ
      · exact hne (path_eq_of_tgt_eq hc.2.1 hgQ hap hg)
      · exact hvx (hc.2.2.2.2 a hap g hgQ hg.symm)
    have hih := ih (d := a :: d) (v := N.src a) hp' (by simp) h₁
    have hl := N.label_tree a hu s
    by_cases hsa : N.site s = a
    · rw [ite_eq_left hsa] at hl
      have hnot : N.site s ∉ c₀ := by
        rw [hsa]
        exact (IsPath.notMem_of_split (p₂ := []) hv).1
      have hroot : N.label (N.src a) s = N.label N.root s := by
        by_contra hne
        exact hnot (hih.1 hne)
      rw [hl, hroot]
      simp [hsa]
    · rw [ite_eq_right hsa] at hl
      rw [hl, hih]
      simp [hsa]

/-- The start `c` of a list has the arcs before its length. -/
theorem mem_prefix_iff {a : E} {c d : List E} : a ∈ c ↔ (c ++ d).idxOf a < c.length := by
  constructor
  · intro h
    rw [List.idxOf_append_of_mem h]
    exact List.idxOf_lt_length_iff.2 h
  · intro h
    by_contra hc
    rw [List.idxOf_append_of_notMem hc] at h
    omega

/-- **Theorem 2.2 of the source**, on one gall: the coordinates of the nodes of the gall. The nodes of one side have negative even coordinates, of the other side positive ones, and the sites odd ones. -/
theorem exists_threshold_mem (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) :
    ∃ (kind : ι → Prop) (τ : ι → ℤ), ∀ v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}, v = x ∨
      ∃ z, ∀ s, N.site s ∈ {e | e ∈ p ∨ e ∈ q} → (N.label v s ≠ N.label x s ↔ OnSide kind τ z s) := by
  let τ : ι → ℤ := fun s => if N.site s ∈ p then -(2 * (p.idxOf (N.site s) : ℤ) + 1) else 2 * (q.idxOf (N.site s) : ℤ) + 1
  let X : ι → Prop := fun s => N.label x s ≠ N.label N.root s
  let kind : ι → Prop := fun s => (N.site s ∈ p ∧ X s) ∨ (N.site s ∉ p ∧ ¬ X s)
  -- from the states relative to the root to the states relative to the recombination node
  have hconv : ∀ {v : V} {z : ℤ} {s : ι}, (N.label v s ≠ N.label N.root s ↔ if N.site s ∈ p then z < τ s else τ s < z) → z ≠ τ s →
      (N.label v s ≠ N.label x s ↔ OnSide kind τ z s) := by
    intro v z s hF hne
    have hbool : ∀ a b c : Bool, a ≠ b ↔ ((a ≠ c) ↔ ¬ (b ≠ c)) := by decide
    rw [hbool _ _ (N.label N.root s), hF]
    change ((if N.site s ∈ p then z < τ s else τ s < z) ↔ ¬ X s) ↔ OnSide kind τ z s
    by_cases hsp : N.site s ∈ p <;> by_cases hX : X s <;> simp only [OnSide, kind, hsp, hX, ite_true, ite_false, true_and, false_and, and_true, and_false, or_false, false_or, not_true_eq_false, not_false_eq_true, iff_false, iff_true, or_true, and_self] <;> omega
  refine ⟨kind, τ, fun v hv => ?_⟩
  rcases cycle_mem_cases hc hv with h | ⟨c, d, hp, hd, hcv⟩ | ⟨c, d, hq, hd, hcv⟩
  · exact Or.inl h
  · refine Or.inr ⟨-(2 * (c.length : ℤ)), fun s hs => ?_⟩
    have hne : -(2 * (c.length : ℤ)) ≠ τ s := by
      simp only [τ]
      split_ifs <;> omega
    refine hconv ?_ hne
    rw [label_cut hG hc hp hd hcv hs]
    by_cases hsp : N.site s ∈ p
    · rw [mem_prefix_iff (d := d), ← hp]
      simp only [τ, hsp, ite_true]
      omega
    · have hnc : N.site s ∉ c := fun h => hsp (by rw [hp]; exact List.mem_append_left _ h)
      simp only [τ, hsp, ite_false, hnc, false_iff]
      omega
  · refine Or.inr ⟨2 * (c.length : ℤ), fun s hs => ?_⟩
    have hne : 2 * (c.length : ℤ) ≠ τ s := by
      simp only [τ]
      split_ifs <;> omega
    refine hconv ?_ hne
    have hs' : N.site s ∈ {e | e ∈ q ∨ e ∈ p} := Or.symm hs
    rw [label_cut hG hc.symm hq hd hcv hs']
    by_cases hsp : N.site s ∈ p
    · have hnc : N.site s ∉ c := fun h => hc.notMem hsp (by rw [hq]; exact List.mem_append_left _ h)
      simp only [τ, hsp, ite_true, hnc, false_iff]
      omega
    · rw [mem_prefix_iff (d := d), ← hq]
      simp only [τ, hsp, ite_false]
      omega

/-- **Theorem 2.2 of the source**, on one gall: the coordinates. A node has the states on the gall of the recombination node, or of a coordinate on the line. -/
theorem exists_threshold (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) :
    ∃ (kind : ι → Prop) (τ : ι → ℤ), ∀ y : V, (∀ s, N.site s ∈ {e | e ∈ p ∨ e ∈ q} → N.label y s = N.label x s) ∨
      ∃ z, ∀ s, N.site s ∈ {e | e ∈ p ∨ e ∈ q} → (N.label y s ≠ N.label x s ↔ OnSide kind τ z s) := by
  obtain ⟨kind, τ, hτ⟩ := exists_threshold_mem hG hc
  refine ⟨kind, τ, fun y => ?_⟩
  obtain ⟨v, hv, hyv⟩ := exists_mem_label_eq hG hc y
  rcases hτ v hv with rfl | ⟨z, hz⟩
  · exact Or.inl hyv
  · exact Or.inr ⟨z, fun s hs => by rw [hyv s hs]; exact hz s hs⟩

/-- What is below the recombination node of a gall has its states on the gall. -/
theorem label_of_reach (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) {y : V} (hy : N.Reach x y) {s : ι} (hs : N.site s ∈ {e | e ∈ p ∨ e ∈ q}) :
    N.label y s = N.label x s := by
  induction hy with
  | refl => rfl
  | tail hb hbc ih =>
    obtain ⟨f, rfl, rfl⟩ := hbc
    have hf : N.tgt f ∉ N.blobVerts {e | e ∈ p ∨ e ∈ q} := fun hmem => by
      have hx := cycle_reach_of_mem hc hmem
      exact not_reach_tgt_src f (hx.trans hb)
    exact (label_tgt_of_notMem hG hc hf hs).trans ih

variable {L : Finset (ι → Bool)}

/-- **Lemma 2.3 of the source**, in the form used. Sites with conflicts on a gall are in one connected component. -/
theorem lemma2_3 (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) {M : Finset (ι → Bool)} (hD : N.Derives M) (hML : M ⊆ L) (hL : ∀ r ∈ L, ∃ v, N.label v = r) {i j k l : ι}
    (hi : N.site i ∈ {e | e ∈ p ∨ e ∈ q}) (hj : N.site j ∈ {e | e ∈ p ∨ e ∈ q}) (hk : N.site k ∈ {e | e ∈ p ∨ e ∈ q}) (hl : N.site l ∈ {e | e ∈ p ∨ e ∈ q})
    (hij : Incompatible L i j) (hkl : Incompatible L k l) : (incompatGraph L).Reachable i k := by
  obtain ⟨kind, τ, hτ⟩ := exists_threshold hG hc
  have hx : ∃ r ∈ L, ∀ s ∈ {s | N.site s ∈ {e | e ∈ p ∨ e ∈ q}}, r s = N.label x s := by
    obtain ⟨y, hy, hxy⟩ := N.exists_isLeaf_reach x
    exact ⟨N.label y, hML (hD.mapsTo hy), fun s hs => label_of_reach hG hc hxy hs⟩
  refine threshold_exchange (D := {s | N.site s ∈ {e | e ∈ p ∨ e ∈ q}}) (x₀ := N.label x) (kind := kind) (τ := τ) hx (fun r hr => ?_) hi hj hk hl hij hkl
  obtain ⟨y, rfl⟩ := hL r hr
  exact hτ y

/-- **Lemma 2.3 of the source**, for rows that are labels of nodes on the sites `D`, on one gall, whichever rows are there. The fourth pair of an incompatibility is that of the recombination node (`exists_row_of_incompatible`), so no leaf below that node needs to be assumed. -/
theorem lemma2_3_of_rows (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) {Y : Finset (ι → Bool)} {D : Set ι} (hDQ : ∀ s ∈ D, N.site s ∈ {e | e ∈ p ∨ e ∈ q})
    (hY : ∀ r ∈ Y, ∃ v, ∀ s ∈ D, r s = N.label v s) {i j k l : ι} (hi : i ∈ D) (hj : j ∈ D) (hk : k ∈ D) (hl : l ∈ D) (hij : Incompatible Y i j) (hkl : Incompatible Y k l) :
    (incompatGraph Y).Reachable i k := by
  obtain ⟨kind, τ, hτ⟩ := exists_threshold hG hc
  refine threshold_exchange_of_incompatible (D := D) (x₀ := N.label x) (kind := kind) (τ := τ) (fun r hr => ?_) hi hj hk hl hij hkl
  obtain ⟨y, hy⟩ := hY r hr
  rcases hτ y with h | ⟨z, hz⟩
  · exact Or.inl fun s hs => (hy s hs).trans (h s (hDQ s hs))
  · exact Or.inr ⟨z, fun s hs => by rw [hy s hs]; exact hz s (hDQ s hs)⟩

/-- **Theorem 2.4** of the source. All the sites of a connected component with a site on a gall are on the gall. -/
theorem theorem2_4 (hG : IsGalledTree N) {Q : Set E} (hQ : N.IsCycle Q) (hL : ∀ r ∈ L, ∃ v, N.label v = r) {i k : ι} (hi : N.site i ∈ Q)
    (hr : (incompatGraph L).Reachable i k) : N.site k ∈ Q := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => exact hi
  | tail _ hab ih =>
    obtain ⟨B, hB, ha, hb⟩ := exists_isBlob_of_incompatible N hL hab
    have hBQ := hG.eq_of_inter hQ (hG.isCycle_of_isBlob hB) ⟨_, ih, ha⟩
    rwa [hBQ] at hb

/-- **Theorem 2.5** of the source. Sites with conflicts on one gall are in one connected component. -/
theorem theorem2_5 (hG : IsGalledTree N) {Q : Set E} (hQ : N.IsCycle Q) {M : Finset (ι → Bool)} (hD : N.Derives M) (hML : M ⊆ L) (hL : ∀ r ∈ L, ∃ v, N.label v = r) {i k i' k' : ι}
    (hi : N.site i ∈ Q) (hk : N.site k ∈ Q) (hii' : Incompatible L i i') (hkk' : Incompatible L k k') : (incompatGraph L).Reachable i k := by
  have hi' : N.site i' ∈ Q := theorem2_4 hG hQ hL hi (SimpleGraph.Adj.reachable (G := incompatGraph L) hii')
  have hk' : N.site k' ∈ Q := theorem2_4 hG hQ hL hk (SimpleGraph.Adj.reachable (G := incompatGraph L) hkk')
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  exact lemma2_3 hG hc hD hML hL hi hi' hk hk' hii' hkk'

/-- **Theorem 2.5** of the source, for any set of rows that label nodes. Sites with conflicts on one gall are in one connected component. -/
theorem theorem2_5_of_rows (hG : IsGalledTree N) {Q : Set E} (hQ : N.IsCycle Q) (hL : ∀ r ∈ L, ∃ v, N.label v = r) {i k i' k' : ι}
    (hi : N.site i ∈ Q) (hk : N.site k ∈ Q) (hii' : Incompatible L i i') (hkk' : Incompatible L k k') : (incompatGraph L).Reachable i k := by
  have hi' : N.site i' ∈ Q := theorem2_4 hG hQ hL hi (SimpleGraph.Adj.reachable (G := incompatGraph L) hii')
  have hk' : N.site k' ∈ Q := theorem2_4 hG hQ hL hk (SimpleGraph.Adj.reachable (G := incompatGraph L) hkk')
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  refine lemma2_3_of_rows hG hc (D := {s | N.site s ∈ {e | e ∈ p ∨ e ∈ q}}) (fun s hs => hs) (fun r hr => ?_) hi hi' hk hk' hii' hkk'
  obtain ⟨v, rfl⟩ := hL r hr
  exact ⟨v, fun _ _ => rfl⟩

/-- A reduced galled tree is fully decomposed, for the graph of the incompatibilities of a set `L` of rows that label nodes, containing the rows derived. -/
theorem IsReducedGalledTree.isFullyDecomposedFor_of_subset (h : IsReducedGalledTree N (incompatGraph L)) {M : Finset (ι → Bool)} (hD : N.Derives M) (hML : M ⊆ L)
    (hL : ∀ r ∈ L, ∃ v, N.label v = r) : N.IsFullyDecomposedFor (incompatGraph L) where
  blob_component B hB := by
    have hQ := h.galled.isCycle_of_isBlob hB
    obtain ⟨i, j, hi, -, hij⟩ := h.exists_conflict B hQ
    refine ⟨(incompatGraph L).connectedComponentMk i, ⟨i, rfl, j, ?_, hij.ne⟩, fun k => ?_⟩
    · exact (SimpleGraph.ConnectedComponent.eq.2 hij.reachable).symm
    · constructor
      · intro hk
        obtain ⟨k', hk'⟩ := h.no_unconflicted B hQ k hk
        have hr := theorem2_5 h.galled hQ hD hML hL hi hk hij hk'
        exact SimpleGraph.ConnectedComponent.eq.2 hr.symm
      · intro hk
        have hr : (incompatGraph L).Reachable k i := SimpleGraph.ConnectedComponent.exact hk
        exact theorem2_4 h.galled hQ hL hi hr.symm
  isolated_treeArc i hi := by
    rintro ⟨Q, hQ, hiQ⟩
    obtain ⟨j, hj⟩ := h.no_unconflicted Q hQ i hiQ
    exact hi j hj
  nodeDisjoint B B' hB hB' hne :=
    (h.galled B (h.galled.isCycle_of_isBlob hB)).2 B' (h.galled.isCycle_of_isBlob hB') hne.symm

/-- **Gusfield et al. 2007, lines 180, 381** (`g:reduced_galled`), from the source's Theorems 2.4, 2.5, unrooted. A reduced galled tree for `M` is fully decomposed. -/
theorem IsReducedGalledTree.isFullyDecomposedFor_incompatGraph {M : Finset (ι → Bool)} (h : IsReducedGalledTree N (incompatGraph M)) (hD : N.Derives M) :
    N.IsFullyDecomposedFor (incompatGraph M) :=
  h.isFullyDecomposedFor_of_subset hD subset_rfl hD.displays

/-- **Gusfield, Eddhu, Langley 2004** (`ext:reduced_galled`), Theorems 2.4, 2.5, 2.6, the source's rooted form. A reduced galled tree for `M`, relative to its ancestral sequence, is fully decomposed for the conflict graph. -/
theorem IsReducedGalledTree.isFullyDecomposedFor_conflictGraph {M : Finset (ι → Bool)} (h : IsReducedGalledTree N (conflictGraph N.ancestral M)) (hD : N.Derives M) :
    N.IsFullyDecomposedFor (conflictGraph N.ancestral M) := by
  rw [conflictGraph_eq_incompatGraph_addRow] at h ⊢
  refine h.isFullyDecomposedFor_of_subset hD (Finset.subset_insert _ _) fun r hr => ?_
  rcases mem_addRow.1 hr with rfl | hr
  · exact ⟨N.root, rfl⟩
  · exact hD.displays r hr

end Gall

section Printed

/-- A galled tree with one gall, on the sites `0`, `1`, `2`. One side of the gall has arcs with the sites `2`, then `0`, and the other side an arc with the site `1`. As strings of the states of the sites `0`, `1`, `2`, the rows are `000`, `101`,
`010` and `110`, the last being the recombinant. Sites `0`, `1` are incompatible, and site `2` is compatible with both. -/
def printedSpec : NetSpec 3 9 9 :=
  ⟨[0, 1, 2, 0, 3, 0, 2, 3, 4], [1, 2, 4, 3, 4, 5, 6, 7, 8], [1, 3, 0], [0, 4, 5, 2, 3, 0, 5, 2, 3]⟩

theorem printedSpec_valid : printedSpec.Valid := by decide

/-- The rows of `printedSpec`. -/
def printedRows : Finset (Fin 3 → Bool) := {printedSpec.label 5, printedSpec.label 6, printedSpec.label 7, printedSpec.label 8}

/-- The network of `printedSpec`. -/
def printedNet : Network (Fin 3) (Fin 9) (Fin 9) := NetSpec.toNetwork printedSpec_valid

/-- The paths to the recombination node, with their starts. -/
def printedPaths : List (Fin 9 × List (Fin 9)) := [(4, []), (2, [2]), (1, [1, 2]), (0, [0, 1, 2]), (3, [4]), (0, [3, 4])]

theorem printedNet_path {u : Fin 9} {l : List (Fin 9)} (h : printedNet.IsPath u 4 l) : (u, l) ∈ printedPaths := by
  have step : ∀ e : Fin 9, ∀ c ∈ printedPaths, c.1 = printedSpec.tgt e → (printedSpec.src e, e :: c.2) ∈ printedPaths := by decide
  induction l generalizing u with
  | nil =>
    obtain rfl : u = 4 := h
    decide
  | cons e l ih =>
    obtain ⟨rfl, h₂⟩ := h
    exact step e (printedNet.tgt e, l) (ih h₂) rfl

/-- The arcs of the gall of `printedNet`. -/
def printedGall : Set (Fin 9) := {e | e ∈ ([0, 1, 2] : List (Fin 9)) ∨ e ∈ ([3, 4] : List (Fin 9))}

theorem printedNet_isCycleOn : printedNet.IsCycleOn 0 4 [0, 1, 2] [3, 4] := by
  refine ⟨⟨2, 4, by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, show printedSpec.tgt 2 = 4 by decide⟩, ⟨by decide, by decide, show printedSpec.tgt 4 = 4 by decide⟩, by decide, ?_⟩
  change ∀ e ∈ ([0, 1, 2] : List (Fin 9)), ∀ f ∈ ([3, 4] : List (Fin 9)), printedSpec.tgt e = printedSpec.tgt f → printedSpec.tgt e = 4
  decide

/-- `printedNet` has one recombination cycle. -/
theorem printedNet_isCycle_iff {Q : Set (Fin 9)} (hQ : printedNet.IsCycle Q) : Q = printedGall := by
  obtain ⟨w, x, p, q, ⟨⟨e, f, hef, he, hf⟩, hp, hq, hne, -⟩, rfl⟩ := hQ
  have hx : ∀ x : Fin 9, ∀ e f : Fin 9, e ≠ f → printedSpec.tgt e = x → printedSpec.tgt f = x → x = 4 := by decide
  obtain rfl : x = 4 := hx x e f hef he hf
  have hcases : ∀ c ∈ printedPaths, ∀ c' ∈ printedPaths, c.1 = c'.1 → c.2 ≠ c'.2 →
      (c.2 = [0, 1, 2] ∧ c'.2 = [3, 4]) ∨ (c.2 = [3, 4] ∧ c'.2 = [0, 1, 2]) := by decide
  rcases hcases (w, p) (printedNet_path hp) (w, q) (printedNet_path hq) rfl hne with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · change p = _ at h₁
    change q = _ at h₂
    subst h₁ h₂
    rfl
  · change p = _ at h₁
    change q = _ at h₂
    subst h₁ h₂
    ext a
    exact or_comm

/-- `printedNet` is a galled tree. -/
theorem printedNet_isGalledTree : IsGalledTree printedNet := fun _ hQ =>
  ⟨hQ, fun _ hQ' hne => absurd ((printedNet_isCycle_iff hQ').trans (printedNet_isCycle_iff hQ).symm) hne⟩

/-- **Gusfield et al. 2007, line 180** (`g:reduced_galled_printed`). "A galled-tree is 'reduced' if every recombination cycle contains some incompatible sites", and "every reduced galled-tree for `M` must be fully-decomposed". With this
wording the claim fails: `printedNet` has one recombination cycle, which contains two incompatible sites, and also a compatible one, which isn't on a tree edge. The source's Definition 2.2 also asks that a gall contain "no unconflicted sites",
and with it the claim holds (`IsReducedGalledTree.isFullyDecomposedFor_incompatGraph`). -/
theorem line180_printed_false :
    printedNet.Derives printedRows ∧ printedNet.Obeys .single ∧ IsGalledTree printedNet ∧
      (∀ Q, printedNet.IsCycle Q → ∃ i j, printedNet.site i ∈ Q ∧ printedNet.site j ∈ Q ∧ (incompatGraph printedRows).Adj i j) ∧
      ¬ printedNet.IsFullyDecomposedFor (incompatGraph printedRows) := by
  refine ⟨NetSpec.derives_toNetwork printedSpec_valid (by decide), NetSpec.obeys_single_toNetwork printedSpec_valid (by decide), printedNet_isGalledTree, fun Q hQ => ?_, fun hfd => ?_⟩
  · rw [printedNet_isCycle_iff hQ]
    refine ⟨0, 1, Or.inl (by decide), Or.inr (by decide), ?_⟩
    change Incompatible printedRows 0 1
    unfold Incompatible
    decide
  · have hiso : ∀ j, ¬ (incompatGraph printedRows).Adj 2 j := by
      intro j
      change ¬ Incompatible printedRows 2 j
      unfold Incompatible
      revert j
      decide
    exact hfd.isolated_treeArc 2 hiso ⟨printedGall, ⟨0, 4, _, _, printedNet_isCycleOn, rfl⟩, Or.inl (by decide)⟩

/-- **Corollary 2.1** (`ext:cor2_1_printed`) of the source, one direction, is false. "A sequence is in `M(C) − 0` if and only if it is the sequence `S_v(C)` for some node `v ≠ w` on `Q`. Stated differently, the node labels of the non-coalescent nodes on `Q`, restricted to sites in `C`, are exactly the sequences in `M(C) − 0`."
On `printedNet`, with `C` all the sites, the node `1` of the gall isn't the coalescent node, and it has no edge off the gall: its label isn't a row. The source's proof shows that each row is the label of a node of the gall (`exists_mem_label_eq`). The other direction holds at a branching node, by its Lemma 2.1 (`label_tgt_of_notMem`), so what is missing is that every non-coalescent node branches. The source also uses that direction as printed, in its Section 3, for the leaves it adds at all the nodes of the gall. Its standing assumptions hold here: the columns are distinct, and each has a `1`. Gusfield et al. 2007 don't use this. -/
theorem corollary2_1_printed_false : (1 : Fin 9) ∈ printedNet.blobVerts printedGall ∧ (1 : Fin 9) ≠ 0 ∧ printedNet.label 1 ∉ printedRows ∧ printedNet.label 0 = (fun _ => false) := by
  refine ⟨Or.inr ⟨0, Or.inl (by decide), rfl⟩, by decide, ?_, ?_⟩
  · change printedSpec.label 1 ∉ printedRows
    decide
  · change printedSpec.label 0 = _
    decide

end Printed

end GusfieldEtAl2004
