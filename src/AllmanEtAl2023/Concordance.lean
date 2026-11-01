module

public import AllmanEtAl2023.Basic
public import AllmanEtAl2023.BlobDefinitions
public import Phylogenetics.Tree.Splits
public import Phylogenetics.Tree.Splice

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Definitions 14 and 15, generic parameters, and what can be identified

* Definition 14: `quartetCF` and `cfTriple`, the ordered triple `CF_abcd`. The NMSC of the paper is the library's
  `nmscCF` at inheritance correlation `0`: lineages at a hybrid node choose a parent independently.
* Definition 15, on triples: `IsCutCF`, `IsStrictlyCutCF` (the paper's "strictly cut": some entry is the distinct one), `IsStrictlyCutAtFirst` (its "strictly `(ab|cd)`-cut": the first entry is), `IsNonCutCF`.
  On a function of quartet trees, with no order on the taxa: `IsStrictlyCutAt p s` ("strictly `s`-cut"), `IsNonCut`. `isStrictlyCutAtFirst_iff` and `isNonCutCF_iff` are the bridges.
* `ForGenericParams N P`: "for generic numerical parameters": the valid parameters where `P` fails form a null
  set, in the sense of the library's `RootedNetwork.IsGenericNull`. That is the paper's: Lebesgue measure on the
  parameter space, whose coordinates are all edge lengths and, at each hybrid node, one of the two hybridization
  parameters.

What "identifiable" means. The paper says that an object is identifiable from the CFs when the CFs determine it, for
generic parameters, on a network that is not known. So the procedure must not depend on the network:

* `readTopology` is what CF-detectability reads off one CF, in Corollary 1;
* `CFInferred p` is what CF-detectability, as `readTopology` reads it, and applications of the Inference Rule give from the CFs `p`, in Theorem 3;
* `treeFromCF p` is the tree whose displayed quartets are read off, treating `CFInferred` sets as unresolved, in
  Theorem 4.

Each is a function of the CFs alone.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]

/-! ### Definition 14 -/

omit [Fintype X] in
theorem card_acbd {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    ({a, c, b, d} : Finset X).card = 4 := by
  rw [← h]
  congr 1
  ext x
  simp only [mem_insert, mem_singleton]
  tauto

omit [Fintype X] in
theorem card_adbc {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    ({a, d, b, c} : Finset X).card = 4 := by
  rw [← h]
  congr 1
  ext x
  simp only [mem_insert, mem_singleton]
  tauto

/-- **Definition 14** (`a:def:cf`). The *quartet concordance factor* `CF_{ab|cd}`, for the quartet `s = ab|cd`: "the probability
under the NMSC on `𝒩⁺` that a gene tree displays the quartet". -/
abbrev quartetCF (N : RootedNetwork V E X) (θ : MetricData E) (s : QuartetTree X) : ℝ := nmscCF N θ 0 s

/-- **Definition 14** (`a:def:cf`). The *concordance factor for taxa `a, b, c, d`*: the ordered triple
`CF_abcd = (CF_{ab|cd}, CF_{ac|bd}, CF_{ad|bc})`. -/
def cfTriple (N : RootedNetwork V E X) (θ : MetricData E) (a b c d : X)
    (h : ({a, b, c, d} : Finset X).card = 4) : ℝ × ℝ × ℝ :=
  (quartetCF N θ (quartetTree a b c d h), quartetCF N θ (quartetTree a c b d (card_acbd h)),
    quartetCF N θ (quartetTree a d b c (card_adbc h)))

/-! ### Definition 15 -/

/-- **Definition 15** (`a:def:cutCF`): a *cut CF*: two of its entries are equal. -/
def IsCutCF (t : ℝ × ℝ × ℝ) : Prop := t.1 = t.2.1 ∨ t.1 = t.2.2 ∨ t.2.1 = t.2.2

/-- **Definition 15** (`a:def:cutCF`): *strictly cut*: two entries are equal, and the third is distinct, whichever it is. -/
def IsStrictlyCutCF (t : ℝ × ℝ × ℝ) : Prop := IsCutCF t ∧ ¬ (t.1 = t.2.1 ∧ t.1 = t.2.2)

/-- **Definition 15** (`a:def:cutCF`): *strictly `(ab|cd)`-cut*, for `t = CF_abcd`, the first entry being the distinct one: `CF_{ab|cd} ≠ CF_{ac|bd} = CF_{ad|bc}`. -/
def IsStrictlyCutAtFirst (t : ℝ × ℝ × ℝ) : Prop := t.1 ≠ t.2.1 ∧ t.2.1 = t.2.2

/-- **Definition 15** (`a:def:cutCF`): *non-cut*. -/
def IsNonCutCF (t : ℝ × ℝ × ℝ) : Prop := ¬ IsCutCF t

/-- A strictly `(ab|cd)`-cut CF is strictly cut. -/
theorem IsStrictlyCutAtFirst.isStrictlyCutCF {t : ℝ × ℝ × ℝ} (h : IsStrictlyCutAtFirst t) : IsStrictlyCutCF t :=
  ⟨Or.inr (Or.inr h.2), fun h' => h.1 h'.1⟩

omit [Fintype X] in
/-- `ab|cd` is not `ac|bd`. -/
theorem quartetTree_ne_acbd {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    quartetTree a b c d h ≠ quartetTree a c b d (card_acbd h) := fun heq => by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hv : ({{a, b}, {c, d}} : Finset (Finset X)) = {{a, c}, {b, d}} := congrArg Subtype.val heq
  have hm : ({a, b} : Finset X) ∈ ({{a, c}, {b, d}} : Finset (Finset X)) := hv ▸ by simp
  simp only [mem_insert, mem_singleton, Finset.ext_iff] at hm
  rcases hm with hm | hm
  · have := (hm b).mp (by simp)
    rcases this with h' | h'
    · exact hab h'.symm
    · exact hbc h'
  · have := (hm a).mp (by simp)
    rcases this with h' | h'
    · exact hab h'
    · exact had h'

omit [Fintype X] in
/-- `ab|cd` is not `ad|bc`. -/
theorem quartetTree_ne_adbc {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    quartetTree a b c d h ≠ quartetTree a d b c (card_adbc h) := fun heq => by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hv : ({{a, b}, {c, d}} : Finset (Finset X)) = {{a, d}, {b, c}} := congrArg Subtype.val heq
  have hm : ({a, b} : Finset X) ∈ ({{a, d}, {b, c}} : Finset (Finset X)) := hv ▸ by simp
  simp only [mem_insert, mem_singleton, Finset.ext_iff] at hm
  rcases hm with hm | hm
  · have := (hm b).mp (by simp)
    rcases this with h' | h'
    · exact hab h'.symm
    · exact hbd h'
  · have := (hm a).mp (by simp)
    rcases this with h' | h'
    · exact hab h'
    · exact hac h'

omit [Fintype V] [Fintype E] in
/-- The trees on `{a, b, c, d}`. -/
theorem treesOn_eq {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    treesOn ({a, b, c, d} : Finset X) =
      {quartetTree a b c d h, quartetTree a c b d (card_acbd h), quartetTree a d b c (card_adbc h)} := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hsub : ({quartetTree a b c d h, quartetTree a c b d (card_acbd h), quartetTree a d b c (card_adbc h)} :
      Finset (QuartetTree X)) ⊆ treesOn {a, b, c, d} := by
    intro r hr
    simp only [mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact mem_treesOn.2 (quartetTree_taxa _ _ _ _ _)
    · refine mem_treesOn.2 ((quartetTree_taxa _ _ _ _ _).trans ?_)
      ext x
      simp only [mem_insert, mem_singleton]
      tauto
    · refine mem_treesOn.2 ((quartetTree_taxa _ _ _ _ _).trans ?_)
      ext x
      simp only [mem_insert, mem_singleton]
      tauto
  have hne := quartetTree_ne_acbd h
  have hne' := quartetTree_ne_adbc h
  have hne'' : quartetTree a c b d (card_acbd h) ≠ quartetTree a d b c (card_adbc h) := fun heq => by
    have hv : ({{a, c}, {b, d}} : Finset (Finset X)) = {{a, d}, {b, c}} := congrArg Subtype.val heq
    have hm : ({a, c} : Finset X) ∈ ({{a, d}, {b, c}} : Finset (Finset X)) := hv ▸ by simp
    simp only [mem_insert, mem_singleton, Finset.ext_iff] at hm
    rcases hm with hm | hm
    · have := (hm c).mp (by simp)
      rcases this with h' | h'
      · exact hac h'.symm
      · exact hcd h'
    · have := (hm a).mp (by simp)
      rcases this with h' | h'
      · exact hab h'
      · exact hac h'
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [card_treesOn h, Finset.card_eq_three.mpr ⟨_, _, _, hne, hne', hne'', rfl⟩]

/-- **Definition 15 on a triple is that on a function of quartet trees**: strictly `(ab|cd)`-cut. -/
theorem isStrictlyCutAtFirst_iff (p : QuartetTree X → ℝ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    IsStrictlyCutAtFirst (p (quartetTree a b c d h), p (quartetTree a c b d (card_acbd h)),
        p (quartetTree a d b c (card_adbc h))) ↔ IsStrictlyCutAt p (quartetTree a b c d h) := by
  have hne : quartetTree a b c d h ≠ quartetTree a c b d (card_acbd h) ∧
      quartetTree a b c d h ≠ quartetTree a d b c (card_adbc h) := by
    have hc := card_treesOn h
    rw [treesOn_eq h] at hc
    have := Finset.card_eq_three.mp hc
    by_contra hcon
    have hle : ({quartetTree a b c d h, quartetTree a c b d (card_acbd h),
        quartetTree a d b c (card_adbc h)} : Finset (QuartetTree X)).card ≤ 2 := by
      by_cases h₁ : quartetTree a b c d h = quartetTree a c b d (card_acbd h)
      · rw [← h₁, Finset.insert_idem]
        exact Finset.card_le_two
      · have h₂ : quartetTree a b c d h = quartetTree a d b c (card_adbc h) := by
          by_contra h₂
          exact hcon ⟨h₁, h₂⟩
        rw [h₂.symm, show ({quartetTree a b c d h, quartetTree a c b d (card_acbd h), quartetTree a b c d h} :
            Finset (QuartetTree X)) = {quartetTree a b c d h, quartetTree a c b d (card_acbd h)} by
          ext r
          simp only [mem_insert, mem_singleton]
          tauto]
        exact Finset.card_le_two
    omega
  have halt : ∀ r, r ∈ (quartetTree a b c d h).alternatives ↔
      r = quartetTree a c b d (card_acbd h) ∨ r = quartetTree a d b c (card_adbc h) := by
    intro r
    rw [QuartetTree.alternatives_eq, mem_erase, quartetTree_taxa, treesOn_eq h]
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro ⟨hr, rfl | h' | h'⟩
      · exact absurd rfl hr
      · exact Or.inl h'
      · exact Or.inr h'
    · rintro (rfl | rfl)
      · exact ⟨hne.1.symm, Or.inr (Or.inl rfl)⟩
      · exact ⟨hne.2.symm, Or.inr (Or.inr rfl)⟩
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₁' : p (quartetTree a b c d h) ≠ p (quartetTree a c b d (card_acbd h)) := h₁
    have h₂' : p (quartetTree a c b d (card_acbd h)) = p (quartetTree a d b c (card_adbc h)) := h₂
    refine ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩
    · rcases (halt r).mp hr with rfl | rfl
      · exact h₁'.symm
      · rw [← h₂']
        exact h₁'.symm
    · rcases (halt r).mp hr with rfl | rfl <;> rcases (halt r').mp hr' with rfl | rfl
      · rfl
      · exact h₂'
      · exact h₂'.symm
      · rfl
  · rintro ⟨h₁, h₂⟩
    have ha₁ := (halt _).mpr (Or.inl rfl)
    have ha₂ := (halt _).mpr (Or.inr rfl)
    exact ⟨(h₁ _ ha₁).symm, h₂ _ ha₁ _ ha₂⟩

/-- **Definition 15 on a triple is that on a function of quartet trees**: non-cut. -/
theorem isNonCutCF_iff (p : QuartetTree X → ℝ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    IsNonCutCF (p (quartetTree a b c d h), p (quartetTree a c b d (card_acbd h)),
        p (quartetTree a d b c (card_adbc h))) ↔ IsNonCut p {a, b, c, d} := by
  have hmem : ∀ r, r ∈ treesOn ({a, b, c, d} : Finset X) ↔ r = quartetTree a b c d h ∨
      r = quartetTree a c b d (card_acbd h) ∨ r = quartetTree a d b c (card_adbc h) := fun r => by
    rw [treesOn_eq h]
    simp only [mem_insert, mem_singleton]
  simp only [IsNonCutCF, IsCutCF, IsNonCut]
  constructor
  · intro hn r hr r' hr' hne
    simp only [not_or] at hn
    obtain ⟨h₁, h₂, h₃⟩ := hn
    rcases (hmem r).mp hr with rfl | rfl | rfl <;> rcases (hmem r').mp hr' with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact h₁
    · exact h₂
    · exact Ne.symm h₁
    · exact absurd rfl hne
    · exact h₃
    · exact Ne.symm h₂
    · exact Ne.symm h₃
    · exact absurd rfl hne
  · intro hn
    have hc := card_treesOn h
    rw [treesOn_eq h] at hc
    obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Finset.card_eq_three.mp hc
    have hne : quartetTree a b c d h ≠ quartetTree a c b d (card_acbd h) ∧
        quartetTree a b c d h ≠ quartetTree a d b c (card_adbc h) ∧
        quartetTree a c b d (card_acbd h) ≠ quartetTree a d b c (card_adbc h) := by
      by_contra hcon
      have hle : ({quartetTree a b c d h, quartetTree a c b d (card_acbd h),
          quartetTree a d b c (card_adbc h)} : Finset (QuartetTree X)).card ≤ 2 := by
        by_cases h₁ : quartetTree a b c d h = quartetTree a c b d (card_acbd h)
        · rw [← h₁, Finset.insert_idem]
          exact Finset.card_le_two
        by_cases h₂ : quartetTree a b c d h = quartetTree a d b c (card_adbc h)
        · rw [h₂.symm, show ({quartetTree a b c d h, quartetTree a c b d (card_acbd h), quartetTree a b c d h} :
              Finset (QuartetTree X)) = {quartetTree a b c d h, quartetTree a c b d (card_acbd h)} by
            ext r
            simp only [mem_insert, mem_singleton]
            tauto]
          exact Finset.card_le_two
        have h₃ : quartetTree a c b d (card_acbd h) = quartetTree a d b c (card_adbc h) := by
          by_contra h₃
          exact hcon ⟨h₁, h₂, h₃⟩
        rw [h₃, Finset.pair_eq_singleton, Finset.insert_eq]
        exact Finset.card_union_le _ _ |>.trans (by simp)
      have := hc
      omega
    rintro (h' | h' | h')
    · exact hn _ ((hmem _).mpr (Or.inl rfl)) _ ((hmem _).mpr (Or.inr (Or.inl rfl))) hne.1 h'
    · exact hn _ ((hmem _).mpr (Or.inl rfl)) _ ((hmem _).mpr (Or.inr (Or.inr rfl))) hne.2.1 h'
    · exact hn _ ((hmem _).mpr (Or.inr (Or.inl rfl))) _ ((hmem _).mpr (Or.inr (Or.inr rfl))) hne.2.2 h'

/-! ### Generic parameters -/

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- `ForGenericParams N P`: `P` holds "for generic numerical parameters": "all those that lie outside of a subset of
measure zero in the parameter space". The parameter space is `N.IsMetric`, and null sets of it are the library's
`RootedNetwork.IsGenericNull`: null in the coordinates given by all edge lengths and the inheritance of all but one
parent at each hybrid node, for every choice of the parent left out. -/
def ForGenericParams (N : RootedNetwork V E X) (P : MetricData E → Prop) : Prop :=
  N.IsGenericNull {θ | N.IsMetric θ ∧ ¬ P θ}

/-! ### Corollary 1: reading the topology off a CF -/

/-- The topologies of a tree on `a, b, c, d`: `ab|cd`, `ac|bd`, `ad|bc`, and the unresolved `abcd`. -/
inductive QuartetTopology
  | first | second | third | star

/-- **What CF-detectability reads off the CF `t = CF_abcd`**: strictly `(ab|cd)`-cut gives `ab|cd`, and so on, and otherwise
the unresolved topology. It depends on `t` alone. -/
def readTopology (t : ℝ × ℝ × ℝ) : QuartetTopology :=
  if t.1 ≠ t.2.1 ∧ t.2.1 = t.2.2 then .first
  else if t.2.1 ≠ t.1 ∧ t.1 = t.2.2 then .second
  else if t.2.2 ≠ t.1 ∧ t.1 = t.2.1 then .third
  else .star

/-- `T_rd(𝒩⁻_Q)` has the topology `τ`, for `Q = {a, b, c, d}`. -/
def InducedTopologyIs {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) (a b c d : X)
    (h : ({a, b, c, d} : Finset X).card = 4) : QuartetTopology → Prop
  | .first => InducedHasQuartetTopology hN a b c d h
  | .second => InducedHasQuartetTopology hN a c b d (card_acbd h)
  | .third => InducedHasQuartetTopology hN a d b c (card_adbc h)
  | .star => InducedHasStarTopology hN a b c d h

/-! ### Theorem 3: what the rule infers from the CFs -/

/-- **What CF-detectability reads as unresolved on the set `q`**: `readTopology` of the `CF` on `q` is the unresolved topology. It depends on `p` alone. -/
def ReadsUnresolved (p : QuartetTree X → ℝ) (q : Finset X) : Prop :=
  ∃ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), ({a, b, c, d} : Finset X) = q ∧
    readTopology (p (quartetTree a b c d h), p (quartetTree a c b d (card_acbd h)), p (quartetTree a d b c (card_adbc h))) = .star

/-- **What CF-detectability and the B-quartet Inference Rule give from the CFs `p`**, as Theorem 3 reads "can be identified
from the quartet `CF`s using `CF`-detectability (Theorem 1) and applications of the B-quartet Inference Rule (Theorem 2)".
A set of four taxa that `readTopology` reads as unresolved, as in Corollary 1, is detected. The rule is Theorem 2's, as printed: its third hypothesis is on the
induced network, that is, on the CF of the third set, as (a) strictly `s`-cut with `a, e` separated in `s`, or (b) read as unresolved.
It depends on `p` alone. -/
inductive CFInferred (p : QuartetTree X → ℝ) : Finset X → Prop
  | detected (Q : Finset X) : ReadsUnresolved p Q → CFInferred p Q
  | rule (a b c d e : X) (t q : Finset X) :
      ({a, b, c, d, e} : Finset X).card = 5 →
      CFInferred p {a, b, c, d} → CFInferred p {b, c, d, e} →
      t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      ((∃ s ∈ treesOn t, IsStrictlyCutAt p s ∧ Separated s a e) ∨ ReadsUnresolved p t) →
      q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      CFInferred p q

/-- `CFInferred`, with part (a) of the Inference Rule alone: "only part (a) of Theorem 2 is needed". -/
inductive CFInferredA (p : QuartetTree X → ℝ) : Finset X → Prop
  | detected (Q : Finset X) : ReadsUnresolved p Q → CFInferredA p Q
  | rule (a b c d e : X) (t q : Finset X) :
      ({a, b, c, d, e} : Finset X).card = 5 →
      CFInferredA p {a, b, c, d} → CFInferredA p {b, c, d, e} →
      t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      (∃ s ∈ treesOn t, IsStrictlyCutAt p s ∧ Separated s a e) →
      q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      CFInferredA p q

/-! ### Theorem 4: the tree read off the CFs -/

/-- The quartet trees read off the CFs: "treating B-quartets on `𝒩⁺` as unresolved, we thus can identify the topology of every
displayed quartet tree". -/
def displayedFromCF (p : QuartetTree X → ℝ) : Set (QuartetTree X) :=
  {s | IsStrictlyCutAt p s ∧ ¬ CFInferred p s.taxa}

/-- The tree with given displayed quartets, as a family of splits: "the collection of displayed quartets determine the tree".
`A` is a side of a split when every quartet tree with its cherries on the two sides is displayed. -/
def treeFromQuartets (D : Set (QuartetTree X)) : Finset (Finset X) :=
  univ.filter fun A => A.Nonempty ∧ Aᶜ.Nonempty ∧ ∀ s ∈ bipartitionQuartets A, s ∈ D

/-- **The tree of blobs read off the CFs `p`**. It depends on `p` alone. -/
def treeFromCF (p : QuartetTree X → ℝ) : Finset (Finset X) := treeFromQuartets (displayedFromCF p)

omit [DecidableEq X] in
/-- A set of four taxa has two distinct taxa. -/
theorem nontrivial_of_card_four (h : Fintype.card X = 4) : Nontrivial X :=
  Fintype.one_lt_card_iff_nontrivial.mp (by omega)

end AllmanEtAl2023
