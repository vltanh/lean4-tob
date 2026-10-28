module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Union
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation

/-!
Finite quartet topologies, represented as unordered partitions into two pairs.
This file supplies representation bridges; it does not prove a paper result.
-/

@[expose] public section

namespace Phylogenetics

universe u v

/-- A quartet is an unordered set of four distinct taxa. -/
abbrev Quartet (X : Type u) := {q : Finset X // q.card = 4}

/-- An unordered pair of distinct elements. -/
abbrev TaxonPair (X : Type u) := {p : Finset X // p.card = 2}

section Pairing

variable {X : Type u} {Y : Type v} [DecidableEq X] [DecidableEq Y]

/-- Transport an unordered pair along a bijection of its elements. -/
def TaxonPair.congr (e : X ≃ Y) : TaxonPair X ≃ TaxonPair Y :=
  e.finsetCongr.subtypeEquiv (by intro s; simp)

omit [DecidableEq X] [DecidableEq Y] in
@[simp] theorem TaxonPair.congr_val (e : X ≃ Y) (p : TaxonPair X) :
    (TaxonPair.congr e p).val = p.val.map e.toEmbedding := rfl

variable [Fintype X] [Fintype Y]

/-- Two unordered pairs whose union is the full set of elements.
For a four-element type these pairs are automatically disjoint. -/
def IsPairing (p : Finset (TaxonPair X)) : Prop :=
  p.card = 2 ∧ p.biUnion (fun b => b.val) = Finset.univ

instance (p : Finset (TaxonPair X)) : Decidable (IsPairing p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Two unordered pairs covering all the elements. -/
abbrev Pairing (X : Type u) [DecidableEq X] [Fintype X] :=
  {p : Finset (TaxonPair X) // IsPairing p}

/-- Pairing is invariant under relabeling taxa. -/
theorem isPairing_congr (e : X ≃ Y) (p : Finset (TaxonPair X)) :
    IsPairing ((TaxonPair.congr e).finsetCongr p) ↔ IsPairing p := by
  simp only [IsPairing, Equiv.finsetCongr_apply, Finset.card_map]
  apply and_congr_right
  intro _
  rw [Finset.eq_univ_iff_forall, Finset.eq_univ_iff_forall]
  constructor
  · intro h x
    obtain ⟨b, hb, hx⟩ := Finset.mem_biUnion.mp (h (e x))
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    exact Finset.mem_biUnion.mpr ⟨a, ha, by simpa using hx⟩
  · intro h y
    obtain ⟨a, ha, hy⟩ := Finset.mem_biUnion.mp (h (e.symm y))
    apply Finset.mem_biUnion.mpr
    refine ⟨TaxonPair.congr e a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
    simpa using hy

/-- Transport both blocks of a pairing along a bijection. -/
def Pairing.congr (e : X ≃ Y) : Pairing X ≃ Pairing Y :=
  (TaxonPair.congr e).finsetCongr.subtypeEquiv (fun p => (isPairing_congr e p).symm)

end Pairing

section Standard

/-- The topology 01|23 on the standard quartet. -/
def split01_23 : Pairing (Fin 4) :=
  ⟨{⟨{0, 1}, by decide⟩, ⟨{2, 3}, by decide⟩}, by decide⟩

/-- The topology 02|13 on the standard quartet. -/
def split02_13 : Pairing (Fin 4) :=
  ⟨{⟨{0, 2}, by decide⟩, ⟨{1, 3}, by decide⟩}, by decide⟩

/-- The topology 03|12 on the standard quartet. -/
def split03_12 : Pairing (Fin 4) :=
  ⟨{⟨{0, 3}, by decide⟩, ⟨{1, 2}, by decide⟩}, by decide⟩

/-- The three standard pairings are distinct. -/
theorem standard_splits_distinct :
    split01_23 ≠ split02_13 ∧ split01_23 ≠ split03_12 ∧
      split02_13 ≠ split03_12 := by decide

/-- Every pairing of four labels is one of the three quartet topologies. -/
theorem standard_splits_exhaustive (p : Pairing (Fin 4)) :
    p = split01_23 ∨ p = split02_13 ∨ p = split03_12 := by
  revert p
  decide

/-- Distinct blocks of each standard pairing are disjoint. -/
theorem standard_pairing_disjoint (p : Pairing (Fin 4))
    (a b : TaxonPair (Fin 4)) (ha : a ∈ p.val) (hb : b ∈ p.val) (hne : a ≠ b) :
    Disjoint a.val b.val := by
  revert p a b
  decide

/-- Exactly three unordered topologies exist on four labels. -/
theorem card_standard_pairings : Fintype.card (Pairing (Fin 4)) = 3 := by decide

end Standard

section Quartet

variable {X : Type u} [DecidableEq X]

/-- The quartet consisting of the four distinct entries of an embedding. -/
def Quartet.ofEmbedding (f : Fin 4 ↪ X) : Quartet X :=
  ⟨Finset.univ.map f, by simp⟩

/-- The embedding gives the corresponding ordering of its quartet. -/
noncomputable def Quartet.ordering (f : Fin 4 ↪ X) :
    Fin 4 ≃ (Quartet.ofEmbedding f).val :=
  Equiv.ofBijective
    (fun i => ⟨f i, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j h => f.injective (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact ⟨i, rfl⟩⟩

omit [DecidableEq X] in
@[simp] theorem Quartet.ordering_val (f : Fin 4 ↪ X) (i : Fin 4) :
    (Quartet.ordering f i).val = f i := rfl

/-- Four pairwise distinct named taxa determine an embedding of the standard labels. -/
def fourTaxa (a b c d : X) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Fin 4 ↪ X where
  toFun := ![a, b, c, d]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

omit [DecidableEq X] in
@[simp] theorem fourTaxa_values (a b c d : X)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    let f := fourTaxa a b c d hab hac had hbc hbd hcd
    f 0 = a ∧ f 1 = b ∧ f 2 = c ∧ f 3 = d := by
  simp [fourTaxa]

/-- The unordered quartet underlying four named distinct taxa. -/
theorem quartet_of_fourTaxa (a b c d : X)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (Quartet.ofEmbedding (fourTaxa a b c d hab hac had hbc hbd hcd)).val =
      {a, b, c, d} := by
  ext x
  simp only [Quartet.ofEmbedding, Finset.mem_map, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [fourTaxa]
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

/-- An actual split of a quartet. Its labels live in the quartet itself, so this
is finite even when the ambient taxon type is infinite. -/
abbrev QuartetSplit (q : Quartet X) := Pairing q.val

/-- An ordering of the quartet identifies its splits with the three standard ones. -/
def QuartetSplit.congr (q : Quartet X) (e : Fin 4 ≃ q.val) :
    Pairing (Fin 4) ≃ QuartetSplit q := Pairing.congr e

/-- The first standard split becomes the two labeled pairs ab and cd. -/
theorem split01_23_blocks (q : Quartet X) (e : Fin 4 ≃ q.val) :
    (QuartetSplit.congr q e split01_23).val =
      {⟨{e 0, e 1}, by simp [e.injective.ne (by decide : (0 : Fin 4) ≠ 1)]⟩,
       ⟨{e 2, e 3}, by simp [e.injective.ne (by decide : (2 : Fin 4) ≠ 3)]⟩} := by
  simp [QuartetSplit.congr, Pairing.congr, split01_23, TaxonPair.congr,
    Equiv.finsetCongr, Equiv.subtypeEquiv]

/-- The second standard split becomes the two labeled pairs ac and bd. -/
theorem split02_13_blocks (q : Quartet X) (e : Fin 4 ≃ q.val) :
    (QuartetSplit.congr q e split02_13).val =
      {⟨{e 0, e 2}, by simp [e.injective.ne (by decide : (0 : Fin 4) ≠ 2)]⟩,
       ⟨{e 1, e 3}, by simp [e.injective.ne (by decide : (1 : Fin 4) ≠ 3)]⟩} := by
  simp [QuartetSplit.congr, Pairing.congr, split02_13, TaxonPair.congr,
    Equiv.finsetCongr, Equiv.subtypeEquiv]

/-- The third standard split becomes the two labeled pairs ad and bc. -/
theorem split03_12_blocks (q : Quartet X) (e : Fin 4 ≃ q.val) :
    (QuartetSplit.congr q e split03_12).val =
      {⟨{e 0, e 3}, by simp [e.injective.ne (by decide : (0 : Fin 4) ≠ 3)]⟩,
       ⟨{e 1, e 2}, by simp [e.injective.ne (by decide : (1 : Fin 4) ≠ 2)]⟩} := by
  simp [QuartetSplit.congr, Pairing.congr, split03_12, TaxonPair.congr,
    Equiv.finsetCongr, Equiv.subtypeEquiv]

/-- The three named topologies remain distinct after any taxon relabeling. -/
theorem quartet_splits_distinct (q : Quartet X) (e : Fin 4 ≃ q.val) :
    QuartetSplit.congr q e split01_23 ≠ QuartetSplit.congr q e split02_13 ∧
    QuartetSplit.congr q e split01_23 ≠ QuartetSplit.congr q e split03_12 ∧
    QuartetSplit.congr q e split02_13 ≠ QuartetSplit.congr q e split03_12 := by
  simpa only [ne_eq, Equiv.apply_eq_iff_eq] using standard_splits_distinct

/-- Every quartet has exactly three split topologies, independent of its labeling. -/
theorem card_quartet_splits (q : Quartet X) : Fintype.card (QuartetSplit q) = 3 := by
  calc
    Fintype.card (QuartetSplit q) = Fintype.card (Pairing (Fin 4)) :=
      Fintype.card_congr (Pairing.congr (Finset.equivFinOfCardEq q.property))
    _ = 3 := card_standard_pairings

/-- The two blocks of an actual quartet split are disjoint, so the cover is a partition. -/
theorem QuartetSplit.blocks_disjoint {q : Quartet X} (p : QuartetSplit q)
    (a b : TaxonPair q.val) (ha : a ∈ p.val) (hb : b ∈ p.val) (hne : a ≠ b) :
    Disjoint a.val b.val := by
  let e : q.val ≃ Fin 4 := Finset.equivFinOfCardEq q.property
  have ha' : TaxonPair.congr e a ∈ (Pairing.congr e p).val :=
    Finset.mem_map.mpr ⟨a, ha, rfl⟩
  have hb' : TaxonPair.congr e b ∈ (Pairing.congr e p).val :=
    Finset.mem_map.mpr ⟨b, hb, rfl⟩
  have h := standard_pairing_disjoint (Pairing.congr e p)
    (TaxonPair.congr e a) (TaxonPair.congr e b) ha' hb'
    ((TaxonPair.congr e).injective.ne hne)
  simpa only [TaxonPair.congr_val, Finset.disjoint_map] using h

/-- The ordered quartet displays exactly ab|cd, ac|bd, ad|bc. -/
theorem quartet_splits_exhaustive (q : Quartet X) (e : Fin 4 ≃ q.val)
    (p : QuartetSplit q) :
    p = QuartetSplit.congr q e split01_23 ∨
    p = QuartetSplit.congr q e split02_13 ∨
    p = QuartetSplit.congr q e split03_12 := by
  obtain h | h | h := standard_splits_exhaustive ((QuartetSplit.congr q e).symm p)
  · exact Or.inl ((Equiv.symm_apply_eq _).mp h)
  · exact Or.inr (Or.inl ((Equiv.symm_apply_eq _).mp h))
  · exact Or.inr (Or.inr ((Equiv.symm_apply_eq _).mp h))

end Quartet

end Phylogenetics
