module

public import External.SongHein2005.Minimal

/-!
# The minimum of `L(P)` over the source's trees

Song and Hein 2005 take "leaf-labelled rooted binary trees", whose degree-3 vertices are "totally ordered", and SPR operations between such trees. `SongHein2005.R_eq_iInf_sprLength` has any time-ordered trees. Here the minimum is over the source's class, and the distance goes through trees of that class only (`IsOrdered`, `OrderedSteps`, `dOrdered`, `orderedLength`): `exists_orderedLength_eq_R`.

An ordered tree of the source has an order on its vertices, and here real times, with no two equal. A path of the source lifts to one here, by choosing times along it, and this one comes with the times chosen.

The proof is that of `SongHein2005.exists_sprLength_le`, on a network with at most two arcs out of each node (`exists_outDegree_le_two`, by splitting nodes, `splitOut`), and with a rank along the arcs that takes no value twice (`exists_rank_injective`). Then every sampled tree is binary with distinct times (`isOrdered_sampledTree`).
-/

@[expose] public noncomputable section

open scoped Classical

namespace SongHein2005

open Gusfield2007

/-! ### The source's trees and distance -/

section Ordered

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **An ordered tree of the source** (`ext:sh_ordered`): "a leaf-labelled rooted binary tree whose corresponding set of degree-3 vertices is a totally ordered set". Each internal node splits in two, and no two of them have the same time. -/
structure IsOrdered (T : TimeOrderedTree X) : Prop where
  binary : ∀ D ∈ T.clusters, 2 ≤ D.card → ∃ B ∈ T.clusters, ∃ C ∈ T.clusters, B ∪ C = D ∧ Disjoint B C
  total : ∀ D ∈ T.clusters, ∀ D' ∈ T.clusters, 2 ≤ D.card → 2 ≤ D'.card → T.time D = T.time D' → D = D'

/-- `T` is taken to `T'` by exactly `k` ordered-SPR operations, through ordered trees. -/
def OrderedSteps : ℕ → TimeOrderedTree X → TimeOrderedTree X → Prop
  | 0, T, T' => T.Same T'
  | k + 1, T, T' => ∃ T'', IsOrdered T'' ∧ T.IsOrderedSPR T'' ∧ OrderedSteps k T'' T'

/-- The SPR-distance of the source, on ordered trees. -/
def dOrdered (T T' : TimeOrderedTree X) : ℕ∞ := sInf ((↑) '' {k | OrderedSteps k T T'})

/-- `L(P)` of the source, equation (2). -/
def orderedLength : List (TimeOrderedTree X) → ℕ∞
  | a :: b :: l => dOrdered a b + orderedLength (b :: l)
  | _ => 0

theorem OrderedSteps.sprSteps {k : ℕ} {T T' : TimeOrderedTree X} (h : OrderedSteps k T T') : TimeOrderedTree.SPRSteps k T T' := by
  induction k generalizing T with
  | zero => exact h
  | succ k ih =>
    obtain ⟨T'', -, h₁, h₂⟩ := h
    exact ⟨T'', h₁, ih h₂⟩

theorem doSPR_le_dOrdered (T T' : TimeOrderedTree X) : T.doSPR T' ≤ dOrdered T T' := by
  refine sInf_le_sInf ?_
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, OrderedSteps.sprSteps hk, rfl⟩

theorem sprLength_le_orderedLength : ∀ L : List (TimeOrderedTree X), sprLength L ≤ orderedLength L
  | [] => le_rfl
  | [_] => le_rfl
  | a :: b :: l => add_le_add (doSPR_le_dOrdered a b) (sprLength_le_orderedLength (b :: l))

theorem orderedSteps_of_same_left {T T' T'' : TimeOrderedTree X} (h : T.Same T') {k : ℕ} (hs : OrderedSteps k T' T'') : OrderedSteps k T T'' := by
  cases k with
  | zero =>
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨h₃, h₄⟩ := hs
    exact ⟨h₁.trans h₃, fun A hA hc => (h₂ A hA hc).trans (h₄ A (h₁ ▸ hA) hc)⟩
  | succ k =>
    obtain ⟨T₁, h₀, h₁, h₂⟩ := hs
    exact ⟨T₁, h₀, IsOrderedSPR_of_same_left h h₁, h₂⟩

theorem dOrdered_le_of_steps {k n : ℕ} {T T' : TimeOrderedTree X} (h : OrderedSteps k T T') (hk : k ≤ n) : dOrdered T T' ≤ n := by
  unfold dOrdered
  have hmem : (k : ℕ∞) ∈ ((↑) '' {k | OrderedSteps k T T'} : Set ℕ∞) := ⟨k, h, rfl⟩
  exact (sInf_le hmem).trans (Nat.cast_le.2 hk)

theorem orderedLength_ofFn_le (Q : ℕ → TimeOrderedTree X) (w : ℕ → ℕ) (hw : ∀ n, dOrdered (Q n) (Q (n + 1)) ≤ w n) (m a : ℕ) :
    orderedLength (List.ofFn fun i : Fin m => Q (a + i.val)) ≤ ((∑ l ∈ Finset.Ico a (a + (m - 1)), w l : ℕ) : ℕ∞) := by
  induction m generalizing a with
  | zero => simp [orderedLength]
  | succ m ih =>
    rcases m with - | m
    · simp [orderedLength]
    · have hL : (List.ofFn fun i : Fin (m + 1 + 1) => Q (a + i.val)) = Q a :: List.ofFn fun i : Fin (m + 1) => Q (a + 1 + i.val) := by
        rw [List.ofFn_succ]
        congr 2
        funext i
        congr 1
        simp only [Fin.val_succ]
        omega
      have hL₂ : (List.ofFn fun i : Fin (m + 1) => Q (a + 1 + i.val)) = Q (a + 1) :: List.ofFn fun i : Fin m => Q (a + 1 + i.succ.val) := by
        rw [List.ofFn_succ]
        rfl
      have hIH := ih (a + 1)
      rw [hL, hL₂]
      change dOrdered (Q a) (Q (a + 1)) + orderedLength (Q (a + 1) :: _) ≤ _
      rw [← hL₂]
      have hb : a + (m + 1 + 1 - 1) = a + 1 + (m + 1 - 1) := by omega
      rw [hb, Finset.sum_eq_sum_Ico_succ_bot (by omega), Nat.cast_add]
      exact add_le_add (hw a) hIH

end Ordered

/-! ### At most two arcs out of a node -/

section Split

variable {ι V E : Type*} [Fintype V] (N : Network ι V E) {e f : E}

/-- A new node below `src e`, with the label of `src e`, to which the arcs `e`, `f` are moved. -/
def splitOut (e f : E) (he : N.src e = N.src f) : Network ι (Option V) (Option E) where
  src g := match g with
    | none => some (N.src e)
    | some k => if k = e ∨ k = f then none else some (N.src k)
  tgt g := match g with
    | none => none
    | some k => some (N.tgt k)
  root := some N.root
  site i := some (N.site i)
  label w := match w with
    | none => N.label (N.src e)
    | some u => N.label u
  simple := by
    rintro (- | k) (- | l) h₁ h₂
    · rfl
    · simp at h₂
    · simp at h₂
    · have ht := Option.some.inj h₂
      refine congrArg some (N.simple k l ?_ ht)
      by_cases hk : k = e ∨ k = f
      · by_cases hl : l = e ∨ l = f
        · have hsk : N.src k = N.src e := by
            rcases hk with rfl | rfl
            · rfl
            · exact he.symm
          have hsl : N.src l = N.src e := by
            rcases hl with rfl | rfl
            · rfl
            · exact he.symm
          rw [hsk, hsl]
        · simp only [hk, hl, ↓reduceIte] at h₁
          simp at h₁
      · by_cases hl : l = e ∨ l = f
        · simp only [hk, hl, ↓reduceIte] at h₁
          simp at h₁
        · simp only [hk, hl, ↓reduceIte] at h₁
          exact Option.some.inj h₁
  acyclic := by
    obtain ⟨t, ht⟩ := exists_rank N
    refine Network.acyclic_of_rank (fun w : Option V => match w with
      | none => 2 * t (N.src e) + 1
      | some u => 2 * t u) ?_
    rintro (- | k)
    · change 2 * t (N.src e) < 2 * t (N.src e) + 1
      omega
    · by_cases hk : k = e ∨ k = f
      · have hsk : N.src k = N.src e := by
          rcases hk with rfl | rfl
          · rfl
          · exact he.symm
        simp only [hk, ↓reduceIte]
        have := ht k
        rw [hsk] at this
        omega
      · simp only [hk, ↓reduceIte]
        have := ht k
        omega
  root_iff := by
    rintro (- | v)
    · exact ⟨fun h => absurd rfl (h none), fun h => by simp at h⟩
    · constructor
      · intro h
        exact congrArg some ((N.root_iff v).1 fun k hk => h (some k) (congrArg some hk))
      · intro h
        obtain rfl := Option.some.inj h
        rintro (- | k) hk
        · simp at hk
        · exact (N.root_iff N.root).2 rfl k (Option.some.inj hk)
  inDegree_le_two := by
    rintro (- | a) (- | b) (- | c) h₁ h₂
    · exact Or.inl rfl
    · simp at h₂
    · simp at h₁
    · simp at h₁
    · simp at h₁
    · simp at h₁
    · simp at h₂
    · rcases N.inDegree_le_two a b c (Option.some.inj h₁) (Option.some.inj h₂) with h | h | h
      · exact Or.inl (congrArg some h)
      · exact Or.inr (Or.inl (congrArg some h))
      · exact Or.inr (Or.inr (congrArg some h))
  site_not_recomb := by
    rintro i (- | k) h
    · simp at h
    · exact congrArg some (N.site_not_recomb i k (Option.some.inj h))
  label_tree := by
    have hlab : ∀ k, (match (if k = e ∨ k = f then none else some (N.src k) : Option V) with
        | none => N.label (N.src e)
        | some u => N.label u) = N.label (N.src k) := by
      intro k
      by_cases hk : k = e ∨ k = f
      · simp only [hk, ↓reduceIte]
        rcases hk with rfl | rfl
        · rfl
        · rw [he]
      · simp only [hk, ↓reduceIte]
    rintro (- | k) hu i
    · simp
    · have hu' : ∀ l, N.tgt l = N.tgt k → l = k := fun l hl => Option.some.inj (hu (some l) (congrArg some hl))
      have := N.label_tree k hu' i
      simp only [hlab, Option.some.injEq]
      exact this
  label_recomb := by
    have hlab : ∀ k, (match (if k = e ∨ k = f then none else some (N.src k) : Option V) with
        | none => N.label (N.src e)
        | some u => N.label u) = N.label (N.src k) := by
      intro k
      by_cases hk : k = e ∨ k = f
      · simp only [hk, ↓reduceIte]
        rcases hk with rfl | rfl
        · rfl
        · rw [he]
      · simp only [hk, ↓reduceIte]
    rintro (- | k) (- | l) hkl h i
    · exact absurd rfl hkl
    · simp at h
    · simp at h
    · have hkl' : k ≠ l := fun h' => hkl (congrArg some h')
      simp only [hlab]
      exact N.label_recomb k l hkl' (Option.some.inj h) i

variable {N} {he : N.src e = N.src f}

theorem label_src_splitOut (k : E) : (splitOut N e f he).label ((splitOut N e f he).src (some k)) = N.label (N.src k) := by
  change (match (if k = e ∨ k = f then none else some (N.src k) : Option V) with
    | none => N.label (N.src e)
    | some u => N.label u) = _
  by_cases hk : k = e ∨ k = f
  · simp only [hk, ↓reduceIte]
    rcases hk with rfl | rfl
    · rfl
    · rw [he]
  · simp only [hk, ↓reduceIte]

theorem isRecomb_splitOut {x : Option V} (h : (splitOut N e f he).IsRecomb x) : ∃ x', x = some x' ∧ N.IsRecomb x' := by
  obtain ⟨a, b, hab, ha, hb⟩ := h
  rcases a with - | a <;> rcases b with - | b
  · exact absurd rfl hab
  · exact absurd (ha.trans hb.symm) (by simp [splitOut])
  · exact absurd (ha.trans hb.symm) (by simp [splitOut])
  · exact ⟨N.tgt a, ha.symm, a, b, fun h' => hab (congrArg some h'), rfl, Option.some.inj (show some (N.tgt b) = some (N.tgt a) from hb.trans ha.symm)⟩

theorem recombCount_splitOut_le : (splitOut N e f he).recombCount ≤ N.recombCount := by
  refine Nat.card_le_card_of_surjective (fun x : {x // N.IsRecomb x} => (⟨some x.1, ?_⟩ : {x // (splitOut N e f he).IsRecomb x})) ?_
  · obtain ⟨a, b, hab, ha, hb⟩ := x.2
    exact ⟨some a, some b, fun h => hab (Option.some.inj h), congrArg some ha, congrArg some hb⟩
  · rintro ⟨x, hx⟩
    obtain ⟨x', rfl, hx'⟩ := isRecomb_splitOut hx
    exact ⟨⟨x', hx'⟩, rfl⟩

theorem obeys_splitOut [LinearOrder ι] {c : Crossover} (h : N.Obeys c) : (splitOut N e f he).Obeys c := by
  rw [Network.obeys_iff] at h ⊢
  intro x hx
  obtain ⟨x', rfl, hx'⟩ := isRecomb_splitOut hx
  obtain ⟨a, b, hab, ha, hb, hr⟩ := h x' hx'
  refine ⟨some a, some b, fun h' => hab (Option.some.inj h'), congrArg some ha, congrArg some hb, ?_⟩
  rw [label_src_splitOut, label_src_splitOut]
  exact hr

theorem isLeaf_some_splitOut {u : V} : (splitOut N e f he).IsLeaf (some u) ↔ N.IsLeaf u := by
  constructor
  · intro h k hk
    by_cases hkm : k = e ∨ k = f
    · have hsk : N.src k = N.src e := by
        rcases hkm with rfl | rfl
        · rfl
        · exact he.symm
      exact h none (congrArg some (hsk.symm.trans hk))
    · refine h (some k) ?_
      change (if k = e ∨ k = f then none else some (N.src k)) = some u
      rw [ite_eq_right hkm, hk]
  · rintro h (- | k) hk
    · exact h e (Option.some.inj hk)
    · change (if k = e ∨ k = f then none else some (N.src k)) = some u at hk
      by_cases hkm : k = e ∨ k = f
      · rw [ite_eq_left hkm] at hk
        simp at hk
      · rw [ite_eq_right hkm] at hk
        exact h k (Option.some.inj hk)

theorem not_isLeaf_none_splitOut : ¬ (splitOut N e f he).IsLeaf none := by
  intro h
  refine h (some e) ?_
  change (if e = e ∨ e = f then none else some (N.src e)) = none
  rw [ite_eq_left (Or.inl rfl)]

theorem derives_splitOut {M : Finset (ι → Bool)} (h : N.Derives M) : (splitOut N e f he).Derives M := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (- | u) hu
    · exact absurd hu not_isLeaf_none_splitOut
    · exact h.mapsTo (isLeaf_some_splitOut.1 hu)
  · rintro (- | u) hu (- | w) hw huw
    · rfl
    · exact absurd hu not_isLeaf_none_splitOut
    · exact absurd hw not_isLeaf_none_splitOut
    · exact congrArg some (h.injOn (isLeaf_some_splitOut.1 hu) (isLeaf_some_splitOut.1 hw) huw)
  · intro r hr
    obtain ⟨u, hu, hl⟩ := h.surjOn hr
    exact ⟨some u, isLeaf_some_splitOut.2 hu, hl⟩

/-- The number of arcs out of a node. -/
def outCount [Fintype E] (N : Network ι V E) (u : V) : ℕ := (Finset.univ.filter fun g => N.src g = u).card

omit [Fintype V] in
theorem src_eq_of_mem_out [Fintype E] {N : Network ι V E} {u : V} {k : E} (hk : k ∈ Finset.univ.filter fun g => N.src g = u) : N.src k = u := (Finset.mem_filter.1 hk).2

/-- What the arcs out of the nodes have above two. -/
def excess [Fintype E] (N : Network ι V E) : ℕ := ∑ u, (outCount N u - 2)

/-- Splitting a node with a third arc out lowers the excess. -/
theorem excess_splitOut_lt [Fintype E] {g : E} (hef : e ≠ f) (hge : g ≠ e) (hgf : g ≠ f) (hg : N.src g = N.src e) : excess (splitOut N e f he) < excess N := by
  unfold excess
  rw [Fintype.sum_option]
  have hnone : outCount (splitOut N e f he) none - 2 = 0 := by
    refine Nat.sub_eq_zero_of_le ((Finset.card_le_card (t := {some e, some f}) ?_).trans (Finset.card_le_two (a := some e) (b := some f)))
    intro k hk
    have hk' := src_eq_of_mem_out hk
    rcases k with - | k
    · simp [splitOut] at hk'
    · change (if k = e ∨ k = f then none else some (N.src k)) = none at hk'
      by_cases hkm : k = e ∨ k = f
      · rcases hkm with rfl | rfl <;> simp
      · rw [ite_eq_right hkm] at hk'
        simp at hk'
  rw [hnone, Nat.zero_add]
  have hother : ∀ u, u ≠ N.src e → outCount (splitOut N e f he) (some u) ≤ outCount N u := by
    intro u hu
    refine (Finset.card_le_card (t := (Finset.univ.filter fun k => N.src k = u).image some) ?_).trans Finset.card_image_le
    intro k hk
    have hk' := src_eq_of_mem_out hk
    rcases k with - | k
    · exact absurd (Option.some.inj hk').symm hu
    · change (if k = e ∨ k = f then none else some (N.src k)) = some u at hk'
      by_cases hkm : k = e ∨ k = f
      · rw [ite_eq_left hkm] at hk'
        simp at hk'
      · rw [ite_eq_right hkm] at hk'
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, Option.some.inj hk'⟩)
  -- At the node itself.
  set A := Finset.univ.filter fun k => N.src k = N.src e with hA
  have heA : e ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  have hfA : f ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, he.symm⟩
  have hgA : g ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩
  have hthree : 3 ≤ A.card := by
    have hsub : ({e, f, g} : Finset E) ⊆ A := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl
      · exact heA
      · exact hfA
      · exact hgA
    have hcard : ({e, f, g} : Finset E).card = 3 := Finset.card_eq_three.2 ⟨e, f, g, hef, hge.symm, hgf.symm, rfl⟩
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hat : outCount (splitOut N e f he) (some (N.src e)) + 1 ≤ A.card := by
    have h₁ : outCount (splitOut N e f he) (some (N.src e)) ≤ (insert none (((A.erase e).erase f).image some)).card := by
      refine Finset.card_le_card ?_
      intro k hk
      have hk' := src_eq_of_mem_out hk
      rcases k with - | k
      · exact Finset.mem_insert_self _ _
      · change (if k = e ∨ k = f then none else some (N.src k)) = some (N.src e) at hk'
        by_cases hkm : k = e ∨ k = f
        · rw [ite_eq_left hkm] at hk'
          simp at hk'
        · rw [ite_eq_right hkm] at hk'
          push Not at hkm
          refine Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ?_)
          exact Finset.mem_erase.2 ⟨hkm.2, Finset.mem_erase.2 ⟨hkm.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, Option.some.inj hk'⟩⟩⟩
    have h₂ := Finset.card_insert_le (none : Option E) (((A.erase e).erase f).image some)
    have h₃ : (((A.erase e).erase f).image some).card ≤ ((A.erase e).erase f).card := Finset.card_image_le
    have h₄ : ((A.erase e).erase f).card = A.card - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hef.symm, hfA⟩), Finset.card_erase_of_mem heA]
      omega
    omega
  refine Finset.sum_lt_sum (fun u _ => ?_) ⟨N.src e, Finset.mem_univ _, ?_⟩
  · by_cases hu : u = N.src e
    · rw [hu]
      have : outCount N (N.src e) = A.card := rfl
      omega
    · have := hother u hu
      omega
  · have : outCount N (N.src e) = A.card := rfl
    omega

end Split

/-- **Every network can have at most two arcs out of each node** (`ext:sh_out_degree`), keeping the crossovers, the rows, and the number of recombination nodes. -/
theorem exists_outDegree_le_two {ι : Type*} [LinearOrder ι] (n : ℕ) : ∀ {V E : Type} [Fintype V] [Fintype E] (N : Network ι V E), excess N ≤ n →
    ∃ (V' E' : Type) (_ : Fintype V') (_ : Fintype E') (N' : Network ι V' E'), (∀ c, N.Obeys c → N'.Obeys c) ∧ (∀ M, N.Derives M → N'.Derives M) ∧ N'.recombCount ≤ N.recombCount ∧
      ∀ e f g, N'.src e = N'.src f → N'.src f = N'.src g → e = f ∨ e = g ∨ f = g := by
  induction n with
  | zero =>
    intro V E _ _ N hn
    by_cases hall : ∀ e f g, N.src e = N.src f → N.src f = N.src g → e = f ∨ e = g ∨ f = g
    · exact ⟨V, E, inferInstance, inferInstance, N, fun _ h => h, fun _ h => h, le_rfl, hall⟩
    · push Not at hall
      obtain ⟨e, f, g, h₁, h₂, h₃, h₄, h₅⟩ := hall
      have := excess_splitOut_lt (N := N) (he := h₁) h₃ (Ne.symm h₄) (Ne.symm h₅) (h₂.symm.trans h₁.symm)
      omega
  | succ n ih =>
    intro V E _ _ N hn
    by_cases hall : ∀ e f g, N.src e = N.src f → N.src f = N.src g → e = f ∨ e = g ∨ f = g
    · exact ⟨V, E, inferInstance, inferInstance, N, fun _ h => h, fun _ h => h, le_rfl, hall⟩
    · push Not at hall
      obtain ⟨e, f, g, h₁, h₂, h₃, h₄, h₅⟩ := hall
      have hlt := excess_splitOut_lt (N := N) (he := h₁) h₃ (Ne.symm h₄) (Ne.symm h₅) (h₂.symm.trans h₁.symm)
      obtain ⟨V', E', h₆, h₇, N', ho, hd, hc, hout⟩ := ih (splitOut N e f h₁) (by omega)
      exact ⟨V', E', h₆, h₇, N', fun c h => ho c (obeys_splitOut h), fun M h => hd M (derives_splitOut h), hc.trans recombCount_splitOut_le, hout⟩

/-- A rank along the arcs with no value taken twice. -/
theorem exists_rank_injective {ι V E : Type*} [Fintype V] (N : Network ι V E) : ∃ t : V → ℕ, (∀ e, t (N.src e) < t (N.tgt e)) ∧ Function.Injective t := by
  obtain ⟨t₀, ht₀⟩ := exists_rank N
  set n := Fintype.card V with hn
  set idx : V → ℕ := fun v => (Fintype.equivFin V v).val with hidx
  have hlt : ∀ v, idx v < n := fun v => (Fintype.equivFin V v).2
  refine ⟨fun v => n * t₀ v + idx v, fun e => ?_, fun u v h => ?_⟩
  · have h₁ := ht₀ e
    have h₂ := hlt (N.src e)
    have h₃ : n * (t₀ (N.src e) + 1) ≤ n * t₀ (N.tgt e) := Nat.mul_le_mul_left n h₁
    rw [Nat.mul_add, Nat.mul_one] at h₃
    show n * t₀ (N.src e) + idx (N.src e) < n * t₀ (N.tgt e) + idx (N.tgt e)
    omega
  · have h' : n * t₀ u + idx u = n * t₀ v + idx v := h
    have hm : (n * t₀ u + idx u) % n = (n * t₀ v + idx v) % n := by rw [h']
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt (hlt u), Nat.mod_eq_of_lt (hlt v)] at hm
    exact (Fintype.equivFin V).injective (Fin.ext hm)

/-! ### The sampled trees are ordered -/

section TreeOrdered

variable {ι V E X : Type*} [Fintype V] [Fintype X] [DecidableEq X] [Nonempty X] {N : Network ι V E} {leaf : X → V} {keep : E → Prop}
  {hleaf : ∀ x, N.IsLeaf (leaf x)} {hinj : Function.Injective leaf} {t : V → ℕ} {ht : ∀ e, t (N.src e) < t (N.tgt e)}

/-- **The tree of a sampling is an ordered tree of the source** (`ext:sh_ordered_sampled`), for a network with at most two arcs out of each node and a rank taking no value twice. -/
theorem isOrdered_sampledTree (hk : IsSampling N keep) (hout : ∀ e f g, N.src e = N.src f → N.src f = N.src g → e = f ∨ e = g ∨ f = g) (htinj : Function.Injective t) :
    IsOrdered (sampledTree hleaf hinj t ht hk) := by
  have hlast : ∀ D ∈ (sampledTree hleaf hinj t ht hk).clusters, ∃ v, below N leaf keep v = D ∧ (sampledTree hleaf hinj t ht hk).time D = (t v : ℝ) ∧ ∀ u, below N leaf keep u = D → t u ≤ t v := by
    intro D hD
    obtain ⟨⟨v₀, hv₀⟩, -⟩ := mem_clusters.1 hD
    obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun v => below N leaf keep v = D) t ⟨v₀, by simp [hv₀]⟩
    refine ⟨v, (Finset.mem_filter.1 hv).2, ?_, fun u hu => hmax u (by simp [hu])⟩
    rw [time_eq]
    exact Nat.cast_inj.2 (le_antisymm (Finset.sup_le hmax) (Finset.le_sup hv))
  refine ⟨fun D hD hcard => ?_, fun D hD D' hD' _ _ htime => ?_⟩
  · obtain ⟨v, hv, -, hmax⟩ := hlast D hD
    -- Each row of `D` is below an arc kept out of `v`.
    have hchild : ∀ x ∈ D, ∃ g, keep g ∧ N.src g = v ∧ x ∈ below N leaf keep (N.tgt g) := by
      intro x hx
      have hreach := mem_below.1 (hv ▸ hx)
      rcases Relation.ReflTransGen.cases_head hreach with h₁ | ⟨c, ⟨g, hg, h₂, rfl⟩, h₃⟩
      · exfalso
        have hleafD : below N leaf keep v = {x} := by
          rw [h₁]
          exact below_leaf hleaf hinj x
        rw [hv] at hleafD
        rw [hleafD, Finset.card_singleton] at hcard
        omega
      · exact ⟨g, hg, h₂, mem_below.2 h₃⟩
    have hsub : ∀ g, keep g → N.src g = v → below N leaf keep (N.tgt g) ⊂ D := by
      intro g hg hs
      have hle : below N leaf keep (N.tgt g) ⊆ D := by
        rw [← hv]
        exact below_subset (Relation.ReflTransGen.single ⟨g, hg, hs, rfl⟩)
      refine hle.ssubset_of_ne fun heq => ?_
      have h₁ := hmax _ heq
      have h₂ := ht g
      rw [hs] at h₂
      omega
    obtain ⟨x₁, hx₁⟩ := Finset.card_pos.1 (by omega : 0 < D.card)
    obtain ⟨g₁, hg₁, hs₁, hm₁⟩ := hchild x₁ hx₁
    obtain ⟨x₂, hx₂, hx₂n⟩ := Finset.exists_of_ssubset (hsub g₁ hg₁ hs₁)
    obtain ⟨g₂, hg₂, hs₂, hm₂⟩ := hchild x₂ hx₂
    have hne : g₁ ≠ g₂ := by
      rintro rfl
      exact hx₂n hm₂
    refine ⟨_, mem_clusters.2 ⟨⟨N.tgt g₁, rfl⟩, ⟨x₁, hm₁⟩⟩, _, mem_clusters.2 ⟨⟨N.tgt g₂, rfl⟩, ⟨x₂, hm₂⟩⟩, ?_, ?_⟩
    · refine Finset.Subset.antisymm (Finset.union_subset (hsub g₁ hg₁ hs₁).subset (hsub g₂ hg₂ hs₂).subset) fun x hx => ?_
      obtain ⟨g, hg, hs, hm⟩ := hchild x hx
      rcases hout g g₁ g₂ (hs.trans hs₁.symm) (hs₁.trans hs₂.symm) with h | h | h
      · exact Finset.mem_union_left _ (h ▸ hm)
      · exact Finset.mem_union_right _ (h ▸ hm)
      · exact absurd h hne
    · refine Finset.disjoint_left.2 fun y hy₁ hy₂ => ?_
      have hthrough : ∀ {a b : E}, keep a → keep b → N.src a = v → N.src b = v → a ≠ b → ¬ KeptReach N keep (N.tgt a) (N.tgt b) := by
        intro a b ha hb hsa hsb hab h
        rcases Relation.ReflTransGen.cases_tail h with h₁ | ⟨c, hc, g', hg', rfl, h₂⟩
        · exact hab (hk.unique ha hb h₁.symm)
        · obtain rfl := hk.unique hg' hb h₂
          exact N.not_reach_tgt_src a (by rw [hsa, ← hsb]; exact KeptReach.reach hc)
      rcases keptReach_total hk (mem_below.1 hy₁) (mem_below.1 hy₂) with h | h
      · exact hthrough hg₁ hg₂ hs₁ hs₂ hne h
      · exact hthrough hg₂ hg₁ hs₂ hs₁ hne.symm h
  · obtain ⟨v, hv, hvt, -⟩ := hlast D hD
    obtain ⟨v', hv', hvt', -⟩ := hlast D' hD'
    rw [hvt, hvt'] at htime
    have heq : v = v' := htinj (Nat.cast_inj.1 htime)
    rw [← hv, ← hv', heq]

/-- Choices that differ at few nodes, through ordered trees. -/
theorem exists_orderedSteps {left right : {x // N.IsRecomb x} → E} (hl : ∀ x, N.tgt (left x) = x.1) (hr : ∀ x, N.tgt (right x) = x.1)
    (hout : ∀ e f g, N.src e = N.src f → N.src f = N.src g → e = f ∨ e = g ∨ f = g) (htinj : Function.Injective t) (D : Finset V) :
    ∀ sel sel' : V → Bool, (∀ x, N.IsRecomb x → sel x ≠ sel' x → x ∈ D) →
      ∃ k ≤ D.card, OrderedSteps k (sampledTree hleaf hinj t ht (isSampling_keepOf hl hr sel)) (sampledTree hleaf hinj t ht (isSampling_keepOf hl hr sel')) := by
  induction D using Finset.induction_on with
  | empty =>
    intro sel sel' h
    refine ⟨0, le_rfl, sampledTree_same _ _ ?_⟩
    funext g
    refine propext (keepOf_iff fun hx => ?_)
    by_contra hne
    exact Finset.notMem_empty _ (h _ hx hne)
  | insert x₀ D hx₀ ih =>
    intro sel sel' h
    set sel₁ : V → Bool := Function.update sel x₀ (sel' x₀) with hsel₁
    have hdiff : ∀ g, N.tgt g ≠ x₀ → (keepOf left right sel g ↔ keepOf left right sel₁ g) := fun g hg =>
      keepOf_iff fun _ => (Function.update_of_ne hg _ _).symm
    obtain ⟨k, hk, hsteps⟩ := ih sel₁ sel' (by
      intro x hx hne
      by_cases hxx : x = x₀
      · subst hxx
        exact absurd (Function.update_self _ _ _) hne
      · have hne' : sel x ≠ sel' x := by
          rwa [hsel₁, Function.update_of_ne hxx] at hne
        rcases Finset.mem_insert.1 (h x hx hne') with h₁ | h₁
        · exact absurd h₁ hxx
        · exact h₁)
    rw [Finset.card_insert_of_notMem hx₀]
    rcases same_or_isOrderedSPR (hleaf := hleaf) (hinj := hinj) (ht := ht) (hk := isSampling_keepOf hl hr sel) (hk' := isSampling_keepOf hl hr sel₁) hdiff with hs | hs
    · exact ⟨k, by omega, orderedSteps_of_same_left hs hsteps⟩
    · exact ⟨k + 1, by omega, _, isOrdered_sampledTree _ hout htinj, hs, hsteps⟩

end TreeOrdered

variable {m : ℕ}

/-- **The minimum of `L(P)` over the source's trees is `R¹(M)`** (`ext:song_hein_eq_ordered`): Song and Hein's equations (3), (5), `min_P L(P) = R_min(S)`, for binary trees with a total order on their internal nodes, and the SPR-distance through such trees. The columns aren't constant, as a constant column has no compatible tree here. -/
theorem exists_orderedLength_eq_R (M : Finset (Fin m → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ P : Fin m → TimeOrderedTree M, (∀ i, IsOrdered (P i)) ∧ (∀ i, (P i).CompatibleWith fun r => (r : Fin m → Bool) i) ∧ orderedLength (List.ofFn P) = R .single M := by
  have hne : Nonempty M := hM.to_subtype
  obtain ⟨a, b, N₀, hc₀, hd₀, hcount⟩ := Nat.sInf_mem (recombSet_nonempty .single hM)
  obtain ⟨V, E, _, _, N, hobey, hderive, hle, hout⟩ := exists_outDegree_le_two _ N₀ le_rfl
  have hc := hobey _ hc₀
  have hd := hderive _ hd₀
  have hex : ∀ r : M, ∃ v, N.IsLeaf v ∧ N.label v = r.1 := fun r => hd.surjOn r.2
  choose leaf hl₁ hl₂ using hex
  have hinj : Function.Injective leaf := fun r r' h => Subtype.ext ((hl₂ r).symm.trans ((congrArg N.label h).trans (hl₂ r')))
  obtain ⟨t, ht, htinj⟩ := exists_rank_injective N
  obtain ⟨left, right, hleft, hright, sel, D, hcompat, hD, hsum⟩ := exists_choices N hc hl₁ hl₂ hinj hC t ht
  set Q : ℕ → TimeOrderedTree M := fun n => sampledTree hl₁ hinj t ht (isSampling_keepOf hleft hright (sel n)) with hQ
  have hstep : ∀ n, dOrdered (Q n) (Q (n + 1)) ≤ (D n).card := by
    intro n
    obtain ⟨k, hk, hs⟩ := exists_orderedSteps (hleaf := hl₁) (hinj := hinj) (ht := ht) hleft hright hout htinj (D n) (sel n) (sel (n + 1)) (hD n)
    exact dOrdered_le_of_steps hs hk
  refine ⟨fun i => Q i.val, fun i => isOrdered_sampledTree _ hout htinj, hcompat, le_antisymm ?_ ?_⟩
  · have hl := orderedLength_ofFn_le Q (fun n => (D n).card) hstep m 0
    simp only [Nat.zero_add] at hl
    refine hl.trans (Nat.cast_le.2 (hsum.trans (hle.trans (le_of_eq hcount))))
  · exact (R_le_sprLength M hM _ hcompat).trans (sprLength_le_orderedLength _)

/-- **Over the source's trees, every path is at least `R¹`** (`ext:song_hein_ordered`). -/
theorem R_le_orderedLength (M : Finset (Fin m → Bool)) (hM : M.Nonempty) (P : Fin m → TimeOrderedTree M) (hP : ∀ i, (P i).CompatibleWith fun r => (r : Fin m → Bool) i) :
    (R .single M : ℕ∞) ≤ orderedLength (List.ofFn P) :=
  (R_le_sprLength M hM P hP).trans (sprLength_le_orderedLength _)

end SongHein2005
