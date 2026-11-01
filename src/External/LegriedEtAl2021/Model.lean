module

public import External.LegriedEtAl2021.Expect
public import External.LegriedEtAl2021.Paths

/-!
# A model of gene duplication and loss on a species tree

The model of Section 3.1 of Legried, Molloy, Warnow and Roch: "on each edge, each gene copy independently duplicates at exponential
rate `λ` and is lost at exponential rate `μ`; at speciation events, each gene copy bifurcates and proceeds similarly in the descendant
edges". They add: "for ease of presentation, we assume that there is a single copy of each gene at the root of `T` and that the rates
of duplication `λ` and loss `μ` are fixed throughout `T` (although our proofs do not use these assumptions)".

What a gene copy at the top of an edge becomes at the bottom is here a `Shape`: the addresses of its copies there, an antichain. The
law `K : PMF Shape` of an edge is arbitrary, with one for each edge, including one above the root. So this model contains the
birth-death process above, whose law on shapes is not defined here, for each edge length and rates; `K` is what the proofs use, which
is the independence of the copies, and neither the rates nor the exponential waiting times.

* `SpeciesTree`, with the law of its edges; `geneLaw T`, the law of a gene tree, as the addresses of its leaves in each species.
* `expect_iid_node`: the recursion of the process, for an i.i.d. family of copies.
* `eq_zero_of_geneLaw_ne_zero`: a gene tree has no leaf in a species that isn't below the copy.
* `score`: the statistic on gene trees. With the weight `φ n = 1 / n`, it is the probability of a topology, picking one gene copy
  uniformly in each of the four species, and with `φ n = 1` it is the number of choices of copies with the topology.
-/

@[expose] public noncomputable section

open scoped ENNReal Classical

namespace External.LegriedEtAl2021

/-- **What a gene copy at the top of an edge becomes at its bottom**: the addresses of its copies there, below it in a binary tree, an
antichain. The empty shape is a copy lost; `{[]}` a copy that goes through unchanged; `{[false], [true]}` one duplication. -/
structure Shape where
  /-- The addresses of the copies at the bottom of the edge. -/
  copies : Finset Path
  /-- No copy descends from another. -/
  anti : ∀ p ∈ copies, ∀ q ∈ copies, p <+: q → p = q

/-- **A rooted binary species tree, with the law of the gene process on each edge**, including one above the root. -/
inductive SpeciesTree (X : Type) where
  /-- A species, with its pendant edge. -/
  | leaf (K : PMF Shape) (x : X) : SpeciesTree X
  /-- A speciation, with the edge above it and the two trees below it. -/
  | node (K : PMF Shape) (l r : SpeciesTree X) : SpeciesTree X

/-- **A gene tree**, as the addresses of its leaves in each species. Topologies are read from addresses by `Pat`. -/
abbrev Leaves (X : Type) := X → Multiset Path

variable {X : Type}

/-- The leaves of a forest of gene trees, the tree `j` rooted at the address `ρ j`. -/
def forestLeaves {J : Type} [Fintype J] (ρ : J → Path) (g : J → Leaves X) : Leaves X :=
  fun y => ∑ j, (g j y).map (ρ j ++ ·)

/-- The leaves below one gene copy at a speciation: each copy `w` at the bottom of the edge above goes to both sides. -/
def glue (s : Shape) (gl gr : s.copies → Leaves X) : Leaves X :=
  forestLeaves (fun w : s.copies => w.1 ++ [false]) gl + forestLeaves (fun w : s.copies => w.1 ++ [true]) gr

/-- **The law of the gene tree descending from one copy at the top of the edge above the root.** -/
def geneLaw : SpeciesTree X → PMF (Leaves X)
  | .leaf K x => K.bind fun s => PMF.pure fun y => if y = x then s.copies.val else 0
  | .node K l r => K.bind fun s =>
      (iid s.copies (geneLaw l)).bind fun gl =>
        (iid s.copies (geneLaw r)).bind fun gr => PMF.pure (glue s gl gr)

namespace SpeciesTree

/-- The species below a vertex. -/
def Has : SpeciesTree X → X → Prop
  | .leaf _ x, y => y = x
  | .node _ l r, y => l.Has y ∨ r.Has y

/-- Every species is at one leaf. -/
def Nodup : SpeciesTree X → Prop
  | .leaf _ _ => True
  | .node _ l r => l.Nodup ∧ r.Nodup ∧ ∀ y, l.Has y → ¬ r.Has y

/-- The clusters of a species tree: the sets of species below its vertices. -/
def clusters : SpeciesTree X → Set (Set X)
  | .leaf K x => {{y | (SpeciesTree.leaf K x).Has y}}
  | .node K l r => {{y | (SpeciesTree.node K l r).Has y}} ∪ l.clusters ∪ r.clusters

theorem has_of_mem_cluster {T : SpeciesTree X} {S : Set X} (hS : S ∈ T.clusters) {y : X} (hy : y ∈ S) : T.Has y := by
  induction T with
  | leaf K x =>
    simp only [clusters, Set.mem_singleton_iff] at hS
    subst hS
    exact hy
  | node K l r ihl ihr =>
    simp only [clusters, Set.mem_union, Set.mem_singleton_iff] at hS
    rcases hS with (rfl | hS) | hS
    · exact hy
    · exact Or.inl (ihl hS)
    · exact Or.inr (ihr hS)

/-- **A cluster holds `A`, `B` and not `C`, `D`.** -/
def Sep (T : SpeciesTree X) (A B C D : X) : Prop := ∃ S ∈ T.clusters, A ∈ S ∧ B ∈ S ∧ C ∉ S ∧ D ∉ S

/-- **The species tree, unrooted, displays the quartet `AB|CD`**: some edge separates `A`, `B` from `C`, `D`. -/
def IsQuartet (T : SpeciesTree X) (A B C D : X) : Prop := T.Sep A B C D ∨ T.Sep C D A B

/-- **A cluster holds `A`, `B` and not `C`.** -/
def Trip (T : SpeciesTree X) (A B C : X) : Prop := ∃ S ∈ T.clusters, A ∈ S ∧ B ∈ S ∧ C ∉ S

end SpeciesTree

/-- A child of a speciation, by its side. -/
def child (l r : SpeciesTree X) (e : Bool) : SpeciesTree X := if e then r else l

@[simp] theorem child_false (l r : SpeciesTree X) : child l r false = l := rfl
@[simp] theorem child_true (l r : SpeciesTree X) : child l r true = r := rfl

theorem has_child_or {K : PMF Shape} {l r : SpeciesTree X} {y : X} (h : (SpeciesTree.node K l r).Has y) :
    ∃ e, (child l r e).Has y := by
  rcases h with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

theorem not_has_child_not {K : PMF Shape} {l r : SpeciesTree X} (hT : (SpeciesTree.node K l r).Nodup) {y : X} {e : Bool}
    (h : (child l r e).Has y) : ¬ (child l r (!e)).Has y := by
  cases e
  · exact hT.2.2 y h
  · exact fun h' => hT.2.2 y h' h

/-- The leaves below one gene copy at a speciation, the first family on side `e`. -/
def glueSide (e : Bool) (s : Shape) (h h' : s.copies → Leaves X) : Leaves X :=
  forestLeaves (fun w : s.copies => w.1 ++ [e]) h + forestLeaves (fun w : s.copies => w.1 ++ [!e]) h'

/-- The copies at the bottom of an edge, below all the copies at its top. -/
abbrev Slots {J : Type} (s : J → Shape) := Σ j, ↥(s j).copies

/-- The address of a copy at the bottom of an edge. -/
def slot {J : Type} (ρ : J → Path) (s : J → Shape) (k : Slots s) : Path := ρ k.1 ++ k.2.1

theorem isAnti_slot {J : Type} {ρ : J → Path} (hρ : IsAnti ρ) (s : J → Shape) : IsAnti (slot ρ s) := by
  rintro ⟨j, w⟩ ⟨i, v⟩ h
  have h' : ρ j ++ w.1 <+: ρ i ++ v.1 := h
  have hji : j = i := hρ.eq_of_prefix ((List.prefix_append _ _).trans h') (List.prefix_append _ _)
  subst hji
  have hwv := (s j).anti _ w.2 _ v.2 ((List.prefix_append_right_inj _).1 h')
  have : w = v := Subtype.ext hwv
  rw [this]

theorem isAnti_slot_side {J : Type} {ρ : J → Path} (hρ : IsAnti ρ) (s : J → Shape) (e : Bool) :
    IsAnti fun k => slot ρ s k ++ [e] :=
  (isAnti_slot hρ s).append_singleton e

variable {J : Type} [Fintype J]

theorem geneLaw_node (K : PMF Shape) (l r : SpeciesTree X) :
    geneLaw (.node K l r) = K.bind fun s =>
      (iid s.copies (geneLaw l)).bind fun gl =>
        (iid s.copies (geneLaw r)).bind fun gr => PMF.pure (glue s gl gr) := rfl

/-- **The recursion of the process on an i.i.d. family of copies at the top of an edge.** -/
theorem expect_iid_node_false (K : PMF Shape) (l r : SpeciesTree X) (F : (J → Leaves X) → ℝ≥0∞) :
    expect (iid J (geneLaw (.node K l r))) F =
      expect (iid J K) fun s =>
        expect (iid (Slots s) (geneLaw l)) fun h =>
          expect (iid (Slots s) (geneLaw r)) fun h' =>
            F fun j => glue (s j) (fun w => h ⟨j, w⟩) (fun w => h' ⟨j, w⟩) := by
  have h₁ : iid J (geneLaw (.node K l r)) = (iid J K).bind fun s =>
      (piLaw fun j => iid (s j).copies (geneLaw l)).bind fun gl =>
        (piLaw fun j => iid (s j).copies (geneLaw r)).bind fun gr =>
          PMF.pure fun j => glue (s j) (gl j) (gr j) := by
    rw [iid]
    simp only [geneLaw_node]
    rw [piLaw_bind]
    refine congrArg _ (funext fun s => ?_)
    rw [piLaw_bind]
    refine congrArg _ (funext fun gl => ?_)
    rw [piLaw_bind]
    refine congrArg _ (funext fun gr => ?_)
    exact piLaw_pure _
  rw [h₁, expect_bind]
  refine congrArg _ (funext fun s => ?_)
  rw [expect_bind, expect_piLaw_sigma]
  refine congrArg _ (funext fun gl => ?_)
  rw [expect_bind, expect_piLaw_sigma]
  refine congrArg _ (funext fun gr => ?_)
  rw [expect_pure]

/-- **The recursion of the process on an i.i.d. family of copies at the top of an edge**, with the first family on side `e`. -/
theorem expect_iid_node (K : PMF Shape) (l r : SpeciesTree X) (e : Bool) (F : (J → Leaves X) → ℝ≥0∞) :
    expect (iid J (geneLaw (.node K l r))) F =
      expect (iid J K) fun s =>
        expect (iid (Slots s) (geneLaw (child l r e))) fun h =>
          expect (iid (Slots s) (geneLaw (child l r (!e)))) fun h' =>
            F fun j => glueSide e (s j) (fun w => h ⟨j, w⟩) (fun w => h' ⟨j, w⟩) := by
  rw [expect_iid_node_false]
  refine congrArg _ (funext fun s => ?_)
  cases e
  · rfl
  · rw [expect_comm]
    refine congrArg _ (funext fun h' => ?_)
    refine congrArg _ (funext fun h => ?_)
    refine congrArg F (funext fun j => ?_)
    exact add_comm _ _

theorem map_sum_multiset {ι : Type*} (f : Path → Path) (t : Finset ι) (g : ι → Multiset Path) :
    (∑ i ∈ t, g i).map f = ∑ i ∈ t, (g i).map f :=
  map_sum (Multiset.mapAddMonoidHom f) g t

/-- The leaves of a forest, after the speciation. -/
theorem forestLeaves_glueSide (ρ : J → Path) (s : J → Shape) (e : Bool) (h h' : Slots s → Leaves X) :
    forestLeaves ρ (fun j => glueSide e (s j) (fun w => h ⟨j, w⟩) (fun w => h' ⟨j, w⟩)) =
      forestLeaves (fun k => slot ρ s k ++ [e]) h + forestLeaves (fun k => slot ρ s k ++ [!e]) h' := by
  funext y
  simp only [forestLeaves, glueSide, Pi.add_apply]
  rw [Fintype.sum_sigma, Fintype.sum_sigma, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Multiset.map_add, map_sum_multiset, map_sum_multiset]
  simp only [Multiset.map_map, Function.comp_def, slot, List.append_assoc]

/-- **A gene tree has no leaf in a species that isn't below the copy.** -/
theorem eq_zero_of_geneLaw_ne_zero (T : SpeciesTree X) {g : Leaves X} (hg : geneLaw T g ≠ 0) {y : X} (hy : ¬ T.Has y) :
    g y = 0 := by
  induction T generalizing g with
  | leaf K x =>
    obtain ⟨s, -, hs⟩ := (PMF.mem_support_bind_iff _ _ _).1 ((PMF.mem_support_iff _ _).2 hg)
    have hgs := (PMF.mem_support_pure_iff _ _).1 hs
    have hyx : y ≠ x := hy
    rw [hgs]
    simp [hyx]
  | node K l r ihl ihr =>
    have hyl : ¬ l.Has y := fun h => hy (Or.inl h)
    have hyr : ¬ r.Has y := fun h => hy (Or.inr h)
    obtain ⟨s, -, hs⟩ := (PMF.mem_support_bind_iff _ _ _).1 ((PMF.mem_support_iff _ _).2 hg)
    obtain ⟨gl, hgl, hs⟩ := (PMF.mem_support_bind_iff _ _ _).1 hs
    obtain ⟨gr, hgr, hs⟩ := (PMF.mem_support_bind_iff _ _ _).1 hs
    have hgs := (PMF.mem_support_pure_iff _ _).1 hs
    have h₁ : ∀ w, gl w y = 0 := fun w => ihl (piLaw_ne_zero ((PMF.mem_support_iff _ _).1 hgl) w) hyl
    have h₂ : ∀ w, gr w y = 0 := fun w => ihr (piLaw_ne_zero ((PMF.mem_support_iff _ _).1 hgr) w) hyr
    rw [hgs]
    simp [glue, forestLeaves, h₁, h₂]

/-! ### The statistic on gene trees -/

/-- The indicator of a statement. -/
def ind (P : Prop) : ℝ≥0∞ := if P then 1 else 0

/-- A sum over a multiset of leaves. -/
def sumMS (M : Multiset Path) (h : Path → ℝ≥0∞) : ℝ≥0∞ := (M.map h).sum

/-- The number of choices of one leaf in each of four multisets, with the given topology. -/
def topo (pat : Path → Path → Path → Path → Prop) (La Lb Lc Ld : Multiset Path) : ℝ≥0∞ :=
  sumMS La fun a => sumMS Lb fun b => sumMS Lc fun c => sumMS Ld fun d => ind (pat a b c d)

/-- **The statistic of a gene tree on the four species**: the number of choices of copies with a topology, with a weight `φ` for each
species, depending on the number of its copies. With `φ n = 1 / n` it is the probability of the topology under a uniform pick of one
copy in each species, and `0` when one of the species has no copy. With `φ n = 1` it is the number of such choices. -/
def score (φ : ℕ → ℝ≥0∞) (pat : Path → Path → Path → Path → Prop) (La Lb Lc Ld : Multiset Path) : ℝ≥0∞ :=
  φ (Multiset.card La) * φ (Multiset.card Lb) * φ (Multiset.card Lc) * φ (Multiset.card Ld) * topo pat La Lb Lc Ld

theorem sumMS_zero (h : Path → ℝ≥0∞) : sumMS 0 h = 0 := by simp [sumMS]

theorem sumMS_add (M M' : Multiset Path) (h : Path → ℝ≥0∞) : sumMS (M + M') h = sumMS M h + sumMS M' h := by
  simp [sumMS]

theorem sumMS_forest {ι : Type*} (t : Finset ι) (M : ι → Multiset Path) (f : ι → Path) (h : Path → ℝ≥0∞) :
    sumMS (∑ i ∈ t, (M i).map (f i ++ ·)) h = ∑ i ∈ t, sumMS (M i) fun a => h (f i ++ a) := by
  induction t using Finset.induction_on with
  | empty => simp [sumMS]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, sumMS_add, ih]
    simp [sumMS]

theorem sumMS_const_of_forall {M : Multiset Path} {h : Path → ℝ≥0∞} {c : ℝ≥0∞} (hc : ∀ a ∈ M, h a = c) :
    sumMS M h = (Multiset.card M : ℝ≥0∞) * c := by
  unfold sumMS
  rw [Multiset.map_congr rfl hc]
  simp

theorem sumMS_mono {M : Multiset Path} {h h' : Path → ℝ≥0∞} (hc : ∀ a, h a ≤ h' a) : sumMS M h ≤ sumMS M h' := by
  unfold sumMS
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    gcongr
    exact hc a

theorem topo_mono {pat pat' : Path → Path → Path → Path → Prop} (h : ∀ a b c d, pat a b c d → pat' a b c d)
    (La Lb Lc Ld : Multiset Path) : topo pat La Lb Lc Ld ≤ topo pat' La Lb Lc Ld := by
  unfold topo
  refine sumMS_mono fun a => sumMS_mono fun b => sumMS_mono fun c => sumMS_mono fun d => ?_
  unfold ind
  by_cases hp : pat a b c d
  · simp [hp, h a b c d hp]
  · simp [hp]

theorem score_mono {pat pat' : Path → Path → Path → Path → Prop} (h : ∀ a b c d, pat a b c d → pat' a b c d)
    (φ : ℕ → ℝ≥0∞) (La Lb Lc Ld : Multiset Path) : score φ pat La Lb Lc Ld ≤ score φ pat' La Lb Lc Ld := by
  unfold score
  gcongr
  exact topo_mono h _ _ _ _

/-- The statistic for the topology `ab|cd`. -/
def Sc (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : ℝ≥0∞ := score φ Pat (L A) (L B) (L C) (L D)

/-- The statistic for the topology `ac|bd`. -/
def Alt (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : ℝ≥0∞ :=
  score φ (fun a b c d => Pat a c b d) (L A) (L B) (L C) (L D)

/-- The statistic for all topologies. -/
def Tot (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : ℝ≥0∞ :=
  score φ (fun _ _ _ _ => True) (L A) (L B) (L C) (L D)

theorem Sc_le_Tot (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : Sc φ A B C D L ≤ Tot φ A B C D L :=
  score_mono (fun _ _ _ _ _ => trivial) _ _ _ _ _

theorem Alt_le_Tot (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : Alt φ A B C D L ≤ Tot φ A B C D L :=
  score_mono (fun _ _ _ _ _ => trivial) _ _ _ _ _

end External.LegriedEtAl2021
