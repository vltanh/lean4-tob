module

public import Gusfield2007.NetworkOps

/-!
# The Elimination Algorithm (Gusfield, Eddhu, Langley 2004, Section 8)

See the `README.md` of this directory. Section 8 of the source uses the lower bound of Myers and Griffiths 2003, "specialized to the case when the ancestral sequence is known". It has three operations on the
matrix: "A column deletion of column `c` from `M` is allowed if column `c` contains zero or one 1's. A sequence deletion of sequence `f` from `M` is allowed if sequence `f` is identical to some other sequence in `M`.
A sequence removal of an arbitrary sequence `f` from `M` is allowed if neither a column deletion nor a sequence deletion is possible." The matrix is "eliminated" when it is empty, and `B` is the minimum number of
sequence removals over all executions.

## Representation

The matrix is a `Finset` of rows on all the sites, and `1` means a state other than the ancestral sequence's.

* A deleted column stays, with the ancestral state in every row (`maskCol`). A column with no `1` is one that needs no deletion. `liveRow_bridge` says that the rows on the sites `D` are those of `M(D)`, one for one.
* A sequence deletion has no step of its own: two identical rows are one element of the `Finset`.
* The matrix is eliminated when no row has a `1`: all the columns are gone, and the rows, of length zero, are one row or none.

`theorem8_1` is Theorem 8.1 of the source, `B ≤ R`. It doesn't look at the crossovers, which is the source's remark after Definition 8.1 that the bound holds for multiple crossovers.
-/

@[expose] public noncomputable section

open scoped Classical

namespace GusfieldEtAl2004

open Gusfield2007 Gusfield2007.Network

variable {ι V E : Type*}

/-- The row with the column `i` deleted: it has the ancestral state there. -/
def maskCol (S : ι → Bool) (i : ι) (r : ι → Bool) : ι → Bool := fun j => if j = i then S i else r j

/-- The number of rows of `X` with a `1` in the column `i`: a state other than that of the ancestral sequence `S`. -/
def ones (S : ι → Bool) (X : Finset (ι → Bool)) (i : ι) : ℕ := (X.filter fun r => r i ≠ S i).card

/-- **The Elimination Algorithm** of Section 8 of the source, for the ancestral sequence `S`: `Elim S X k` says that an execution eliminates `X` with `k` sequence removals. A sequence removal is allowed only when no
column can be deleted, as in the source. -/
inductive Elim (S : ι → Bool) : Finset (ι → Bool) → ℕ → Prop
  /-- No row has a `1`: the matrix is eliminated. -/
  | eliminated {X : Finset (ι → Bool)} : (∀ r ∈ X, r = S) → Elim S X 0
  /-- A column deletion, of a column with one `1`. -/
  | columnDeletion {X : Finset (ι → Bool)} {i : ι} {k : ℕ} : ones S X i = 1 → Elim S (X.image (maskCol S i)) k → Elim S X k
  /-- A sequence removal, when no column can be deleted. It counts one. -/
  | sequenceRemoval {X : Finset (ι → Bool)} {r : ι → Bool} {k : ℕ} : r ∈ X → (∀ i, ones S X i ≠ 1) → Elim S (X.erase r) k → Elim S X (k + 1)

/-- `B`: "the minimum number of sequence removals over all possible executions of the algorithm". -/
def minRemovals (S : ι → Bool) (M : Finset (ι → Bool)) : ℕ := sInf {k | Elim S M k}

/-- A row on the sites `D`, with the ancestral state at the deleted columns. -/
def liveRow (S : ι → Bool) (D : Set ι) (r : ι → Bool) : ι → Bool := fun i => if i ∈ D then r i else S i

theorem liveRow_univ (S r : ι → Bool) : liveRow S Set.univ r = r := by
  funext i
  simp [liveRow]

theorem maskCol_liveRow (S : ι → Bool) (D : Set ι) (i : ι) (r : ι → Bool) : maskCol S i (liveRow S D r) = liveRow S (D \ {i}) r := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [maskCol, liveRow]
  · by_cases hd : j ∈ D <;> simp [maskCol, liveRow, hj, hd]

/-- **The bridge for the representation.** The rows `X` with the columns off `D` deleted are the rows `M(D)`, one for one: they have the same restriction to `D`, and two of them with the same restriction are the same. -/
theorem liveRow_bridge (S : ι → Bool) (D : Set ι) (X : Finset (ι → Bool)) :
    restrictRows D (X.image (liveRow S D)) = restrictRows D X ∧ Set.InjOn D.domRestrict (X.image (liveRow S D) : Set (ι → Bool)) := by
  have hr : ∀ r : ι → Bool, D.domRestrict (liveRow S D r) = D.domRestrict r := by
    intro r
    funext i
    simp [Set.domRestrict, liveRow]
  constructor
  · ext a
    simp only [restrictRows, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨r, hr₁, rfl⟩, rfl⟩
      exact ⟨r, hr₁, (hr r).symm⟩
    · rintro ⟨r, hr₁, rfl⟩
      exact ⟨_, ⟨r, hr₁, rfl⟩, hr r⟩
  · intro x hx y hy hxy
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨r', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    funext i
    by_cases hi : i ∈ D
    · have := congrFun hxy ⟨i, hi⟩
      simpa [Set.domRestrict, liveRow, hi] using this
    · simp [liveRow, hi]

/-- **Lemma 8.2** (`ext:lem8_2`) of the source, in the part about the graph. A column with at most one `1` is in no incompatibility, and deleting it changes no other: "it does not result in the deletion of an edge" of the conflict graph. -/
theorem incompatGraph_image_maskCol {S : ι → Bool} {Y : Finset (ι → Bool)} {i : ι} (h : ones S Y i ≤ 1) :
    incompatGraph (Y.image (maskCol S i)) = incompatGraph Y := by
  have hold : ∀ j, ¬ Incompatible Y i j := by
    intro j hij
    obtain ⟨r, hr, h₁, h₂⟩ := hij (!S i) true
    obtain ⟨r', hr', h₁', h₂'⟩ := hij (!S i) false
    have hne : ∀ b : Bool, (!b) ≠ b := fun b => by cases b <;> simp
    have hmem : ∀ {s : ι → Bool}, s ∈ Y → s i = !S i → s ∈ Y.filter fun r => r i ≠ S i := fun {s} hs hi =>
      Finset.mem_filter.2 ⟨hs, by rw [hi]; exact hne _⟩
    have heq : r = r' := Finset.card_le_one.1 h r (hmem hr h₁) r' (hmem hr' h₁')
    rw [heq, h₂'] at h₂
    simp at h₂
  have hnew : ∀ j, ¬ Incompatible (Y.image (maskCol S i)) i j := by
    intro j hij
    obtain ⟨r, hr, h₁, -⟩ := hij (!S i) true
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hr
    simp [maskCol] at h₁
  ext j l
  change Incompatible _ j l ↔ Incompatible _ j l
  by_cases hj : j = i
  · subst hj
    exact iff_of_false (hnew l) (hold l)
  by_cases hl : l = i
  · subst hl
    have hsymm : ∀ {X : Finset (ι → Bool)}, Incompatible X j l → Incompatible X l j := fun h' a b => by
      obtain ⟨r, hr, h₁, h₂⟩ := h' b a
      exact ⟨r, hr, h₂, h₁⟩
    exact iff_of_false (fun h' => hnew j (hsymm h')) (fun h' => hold j (hsymm h'))
  constructor
  · intro h' a b
    obtain ⟨r, hr, h₁, h₂⟩ := h' a b
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hr
    exact ⟨s, hs, by simpa [maskCol, hj] using h₁, by simpa [maskCol, hl] using h₂⟩
  · intro h' a b
    obtain ⟨r, hr, h₁, h₂⟩ := h' a b
    exact ⟨_, Finset.mem_image_of_mem _ hr, by simpa [maskCol, hj] using h₁, by simpa [maskCol, hl] using h₂⟩

section Bound

variable (N : Network ι V E)

/-- The matrix of the labels of the nodes `A`, on the sites `D`. -/
def nodeRows (D : Set ι) (A : Finset V) : Finset (ι → Bool) := A.image fun v => liveRow N.ancestral D (N.label v)

variable {N}

/-- The ancestors of the nodes `A`. -/
def ancestors (N : Network ι V E) (A : Finset V) : Set V := {y | ∃ v ∈ A, N.Reach y v}

/-- **Theorem 8.1 of the source**, the induction. The matrix of the labels of a set `A` of nodes, on some sites, can be eliminated with at most one removal for each recombination node above `A`. Any node of `A` with no other below it goes:

* if a column can be deleted, it is, before anything else: this is the rule of the algorithm;
* a recombination node is removed;
* the target of an arc with a site that is left would make a column with one `1`, which was just excluded;
* otherwise it has the row of its parent, and the parent takes its place. -/
theorem exists_elim_nodeRows [Finite V] (A : Finset V) (D : Finset ι) :
    ∃ k, k ≤ {x | N.IsRecomb x ∧ x ∈ ancestors N A}.ncard ∧ Elim N.ancestral (nodeRows N (D : Set ι) A) k := by
  have hrootLabel : N.label N.root = N.ancestral := rfl
  induction hn : (ancestors N A).ncard + D.card using Nat.strong_induction_on generalizing A D with
  | _ n ih =>
  set X := nodeRows N (D : Set ι) A with hX
  have hmemX : ∀ {r}, r ∈ X ↔ ∃ v ∈ A, liveRow N.ancestral (D : Set ι) (N.label v) = r := by
    intro r
    simp [hX, nodeRows]
  by_cases hcol : ∃ i, ones N.ancestral X i = 1
  · -- a column deletion
    obtain ⟨i, hi⟩ := hcol
    have hiD : i ∈ D := by
      by_contra hnot
      have : ones N.ancestral X i = 0 := by
        refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun r hr => ?_)
        obtain ⟨v, -, rfl⟩ := hmemX.1 hr
        simp [liveRow, hnot]
      omega
    have himg : X.image (maskCol N.ancestral i) = nodeRows N ((D.erase i : Finset ι) : Set ι) A := by
      rw [hX, nodeRows, nodeRows, Finset.image_image]
      refine Finset.image_congr fun v _ => ?_
      simp only [Function.comp_apply, maskCol_liveRow, Finset.coe_erase]
    have hcard : (D.erase i).card < D.card := Finset.card_erase_lt_of_mem hiD
    obtain ⟨k, hk, hE⟩ := ih ((ancestors N A).ncard + (D.erase i).card) (by omega) A (D.erase i) rfl
    exact ⟨k, hk, Elim.columnDeletion hi (himg ▸ hE)⟩
  push Not at hcol
  by_cases hdone : ∀ r ∈ X, r = N.ancestral
  · exact ⟨0, Nat.zero_le _, Elim.eliminated hdone⟩
  push Not at hdone
  obtain ⟨r₀, hr₀, hr₀S⟩ := hdone
  obtain ⟨u₀, hu₀, -⟩ := hmemX.1 hr₀
  -- a node of `A` with no other below it
  obtain ⟨v, hvA, hmin⟩ := N.wellFounded_transGen_swap.has_min (A : Set V) ⟨u₀, hu₀⟩
  have hlow : ∀ y ∈ A, N.Reach v y → y = v := by
    intro y hy hr
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h | h
    · exact h
    · exact absurd h (hmin y hy)
  have hrootNot : v ≠ N.root := by
    rintro rfl
    apply hr₀S
    obtain ⟨u, hu, rfl⟩ := hmemX.1 hr₀
    rw [hlow u hu (N.reach_root u)]
    funext i
    simp [liveRow, hrootLabel]
  obtain ⟨e, rfl⟩ : ∃ e, N.tgt e = v := by
    by_contra hno
    push Not at hno
    exact hrootNot ((N.root_iff v).1 hno)
  have hvanc : N.tgt e ∈ ancestors N A := ⟨_, hvA, Relation.ReflTransGen.refl⟩
  have hfin : ∀ s : Set V, s.Finite := fun s => s.toFinite
  by_cases hrec : N.IsRecomb (N.tgt e)
  · -- a sequence removal, or nothing if the row is left by another node
    have hnot : N.tgt e ∉ ancestors N (A.erase (N.tgt e)) := by
      rintro ⟨u, hu, hr⟩
      obtain ⟨hne, huA⟩ := Finset.mem_erase.1 hu
      exact hne (hlow u huA hr)
    have hsub : ancestors N (A.erase (N.tgt e)) ⊆ ancestors N A := by
      rintro y ⟨u, hu, hr⟩
      exact ⟨u, Finset.mem_of_mem_erase hu, hr⟩
    have hlt : (ancestors N (A.erase (N.tgt e))).ncard < (ancestors N A).ncard :=
      Set.ncard_lt_ncard ⟨hsub, fun h' => hnot (h' hvanc)⟩ (hfin _)
    obtain ⟨k, hk, hE⟩ := ih ((ancestors N (A.erase (N.tgt e))).ncard + D.card) (by omega) (A.erase (N.tgt e)) D rfl
    have hlt' : {x | N.IsRecomb x ∧ x ∈ ancestors N (A.erase (N.tgt e))}.ncard < {x | N.IsRecomb x ∧ x ∈ ancestors N A}.ncard := by
      refine Set.ncard_lt_ncard ⟨fun x hx => ⟨hx.1, hsub hx.2⟩, fun h' => ?_⟩ (hfin _)
      exact hnot (h' ⟨hrec, hvanc⟩).2
    set row := liveRow N.ancestral (D : Set ι) (N.label (N.tgt e)) with hrow
    have hrowX : row ∈ X := hmemX.2 ⟨_, hvA, rfl⟩
    by_cases hstill : row ∈ nodeRows N (D : Set ι) (A.erase (N.tgt e))
    · have heq : nodeRows N (D : Set ι) (A.erase (N.tgt e)) = X := by
        ext r
        simp only [hmemX, nodeRows, Finset.mem_image]
        constructor
        · rintro ⟨u, hu, rfl⟩
          exact ⟨u, Finset.mem_of_mem_erase hu, rfl⟩
        · rintro ⟨u, hu, rfl⟩
          by_cases huv : u = N.tgt e
          · subst huv
            obtain ⟨u', hu', hr'⟩ := Finset.mem_image.1 hstill
            exact ⟨u', hu', hr'⟩
          · exact ⟨u, Finset.mem_erase.2 ⟨huv, hu⟩, rfl⟩
      exact ⟨k, by omega, heq ▸ hE⟩
    · have heq : nodeRows N (D : Set ι) (A.erase (N.tgt e)) = X.erase row := by
        ext r
        simp only [Finset.mem_erase, hmemX, nodeRows, Finset.mem_image]
        constructor
        · rintro ⟨u, ⟨hne, huA⟩, rfl⟩
          exact ⟨fun h' => hstill (Finset.mem_image.2 ⟨u, Finset.mem_erase.2 ⟨hne, huA⟩, h'⟩), u, huA, rfl⟩
        · rintro ⟨hne, u, hu, rfl⟩
          exact ⟨u, ⟨fun h' => hne (by rw [h']), hu⟩, rfl⟩
      exact ⟨k + 1, by omega, Elim.sequenceRemoval hrowX hcol (heq ▸ hE)⟩
  · have huniq : ∀ f, N.tgt f = N.tgt e → f = e := fun f hf => eq_of_not_isRecomb hrec hf
    by_cases hs : ∃ i ∈ D, N.site i = e
    · -- the column of a site on this arc has one `1`
      exfalso
      obtain ⟨i, hiD, rfl⟩ := hs
      refine hcol i ?_
      have hi : (i ∈ (D : Set ι)) := hiD
      have heq : X.filter (fun r => r i ≠ N.ancestral i) = {liveRow N.ancestral (D : Set ι) (N.label (N.tgt (N.site i)))} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hr, hne⟩
          obtain ⟨u, hu, rfl⟩ := hmemX.1 hr
          have hu' : N.label u i ≠ N.label N.root i := by simpa [liveRow, hi, hrootLabel] using hne
          rw [hlow u hu (N.reach_of_label_ne hu')]
        · rintro rfl
          refine ⟨hmemX.2 ⟨_, hvA, rfl⟩, ?_⟩
          simpa [liveRow, hi, hrootLabel] using N.label_tgt_site_ne i
      rw [ones, heq, Finset.card_singleton]
    · -- the parent takes its place
      push Not at hs
      have hrow : liveRow N.ancestral (D : Set ι) (N.label (N.src e)) = liveRow N.ancestral (D : Set ι) (N.label (N.tgt e)) := by
        funext i
        by_cases hi : i ∈ D
        · have hl := N.label_tree e huniq i
          rw [ite_eq_right (hs i hi)] at hl
          simp only [liveRow, Finset.mem_coe, hi, ite_true, hl]
        · simp [liveRow, hi]
      set A' := insert (N.src e) (A.erase (N.tgt e)) with hA'
      have hrows : nodeRows N (D : Set ι) A' = X := by
        rw [hX, nodeRows, nodeRows, hA', Finset.image_insert, hrow]
        conv_rhs => rw [← Finset.insert_erase (Finset.mem_coe.1 hvA), Finset.image_insert]
      have hsub : ancestors N A' ⊆ ancestors N A := by
        rintro y ⟨u, hu, hr⟩
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exact ⟨_, hvA, hr.trans (reach_src_tgt e)⟩
        · exact ⟨u, Finset.mem_of_mem_erase hu, hr⟩
      have hnot : N.tgt e ∉ ancestors N A' := by
        rintro ⟨u, hu, hr⟩
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exact not_reach_tgt_src e hr
        · obtain ⟨hne, huA⟩ := Finset.mem_erase.1 hu
          exact hne (hlow u huA hr)
      have hlt : (ancestors N A').ncard < (ancestors N A).ncard :=
        Set.ncard_lt_ncard ⟨hsub, fun h' => hnot (h' hvanc)⟩ (hfin _)
      obtain ⟨k, hk, hE⟩ := ih ((ancestors N A').ncard + D.card) (by omega) A' D rfl
      refine ⟨k, hk.trans (Set.ncard_le_ncard (fun x hx => ⟨hx.1, hsub hx.2⟩) (hfin _)), hrows ▸ hE⟩

/-- **Theorem 8.1** (`ext:thm8_1`) of the source: Myers and Griffiths 2003, specialized to a known ancestral sequence. "`B ≤ R`": a network deriving `M` gives an execution of the Elimination Algorithm with at most as many sequence removals as it has
recombination nodes. This holds for any number of crossovers: "the proof in [14] actually establishes that `B` is a lower bound on the minimum number of multiple-crossover events". The source says that it "can be proven by induction on the number of distinct sequences in `M`, or by
induction on `R`", and gives no more. Its reference, Myers and Griffiths 2003, p. 380, has the bound as `R_s` with known types, and takes the first event back in time: "the first event back in time must be a recombination to an ancestor of the sample", whose descendant is removed. `exists_elim_nodeRows` is this on a network, the sample being the nodes `A`. -/
theorem theorem8_1 [Finite V] [Finite ι] {M : Finset (ι → Bool)} (hD : N.Derives M) : ∃ k, k ≤ N.recombCount ∧ Elim N.ancestral M k := by
  have : Fintype V := Fintype.ofFinite V
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨k, hk, hE⟩ := exists_elim_nodeRows (N := N) (Finset.univ.filter fun v => N.IsLeaf v) Finset.univ
  have hrows : nodeRows N ((Finset.univ : Finset ι) : Set ι) (Finset.univ.filter fun v => N.IsLeaf v) = M := by
    ext r
    simp only [nodeRows, Finset.coe_univ, liveRow_univ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact Finset.mem_coe.1 (hD.mapsTo hv)
    · intro hr
      obtain ⟨v, hv, rfl⟩ := hD.surjOn (Finset.mem_coe.2 hr)
      exact ⟨v, hv, rfl⟩
  refine ⟨k, hk.trans ?_, hrows ▸ hE⟩
  have hcount : N.recombCount = {x | N.IsRecomb x}.ncard := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [hcount]
  exact Set.ncard_le_ncard (fun x hx => hx.1) (Set.toFinite _)

/-- `B ≤ R(N)`, for the minimum `B`. -/
theorem minRemovals_le_recombCount [Finite V] [Finite ι] {M : Finset (ι → Bool)} (hD : N.Derives M) : minRemovals N.ancestral M ≤ N.recombCount := by
  obtain ⟨k, hk, hE⟩ := theorem8_1 hD
  exact (Nat.sInf_le hE).trans hk

end Bound

end GusfieldEtAl2004
