module

public import External.AllmanBanosRhodes2019.QuartetCycle

/-!
# `Q̃` on a set of four taxa with no cut-edge split is the 4-cycle

`Q̃_xyzw` "is either a tree or has a single 4-cycle" (line 1026). This module has the second case.

* `HasFourCycleTopology`: the literal 4-cycle with a taxon at each vertex, of the source's Figure 3 (R) after contraction.
* `CycleGaps`, `exists_cycleGaps`, `CycleData`, `exists_cycleData`: the four taxa and their attachments in their order around the cycle, with
  the segments of the cycle between the attachments.
* `CycleData.chainLink_leaf`, `CycleData.chainLink_gap`: the eight edges of `Q̃` are there. By the degrees, of `QuartetCycle.lean`, the
  vertices between are suppressed.
* `CycleData.exists_cl_of_chainLink`, `CycleData.branch_of_cl`: there are no others: a chain stays in one block or one segment.
* `CycleData.hasFourCycleTopology`: **`Q̃` is the 4-cycle on the taxa in their order around the cycle.**
* `not_groveDisplays_of_cycle`: the quartet tree of its opposite pairs is the one that the grove does not display (Figure 6).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open TOBQMC TOBQMC.Level1
open AllmanEtAl2023 AllmanEtAl2023.TreeSuppression
open scoped Classical

namespace External.AllmanBanosRhodes2019.Quartet

variable {V E X : Type*}

/-! ### Lists -/

section Lists

variable {α β : Type*}

/-- Two members of a list, in the order they come. -/
theorem exists_sort_two {g : β → α} {L : List α} {u v : β} (hu : g u ∈ L) (hv : g v ∈ L) (huv : g u ≠ g v) :
    ∃ a b, (a = u ∧ b = v ∨ a = v ∧ b = u) ∧ ∃ A B D, L = A ++ g a :: (B ++ g b :: D) := by
  induction L with
  | nil => simp at hu
  | cons z L ih =>
    by_cases hzu : z = g u
    · subst hzu
      have hv' : g v ∈ L := (List.mem_cons.1 hv).resolve_left (Ne.symm huv)
      obtain ⟨B, D, rfl⟩ := List.append_of_mem hv'
      exact ⟨u, v, Or.inl ⟨rfl, rfl⟩, [], B, D, rfl⟩
    by_cases hzv : z = g v
    · subst hzv
      have hu' : g u ∈ L := (List.mem_cons.1 hu).resolve_left huv
      obtain ⟨B, D, rfl⟩ := List.append_of_mem hu'
      exact ⟨v, u, Or.inr ⟨rfl, rfl⟩, [], B, D, rfl⟩
    obtain ⟨a, b, hab, A, B, D, rfl⟩ := ih ((List.mem_cons.1 hu).resolve_left (Ne.symm hzu)) ((List.mem_cons.1 hv).resolve_left (Ne.symm hzv))
    exact ⟨a, b, hab, z :: A, B, D, rfl⟩

/-- Three members of a list, in the order they come. -/
theorem exists_sort_three {g : β → α} {L : List α} {u v w : β} (hu : g u ∈ L) (hv : g v ∈ L) (hw : g w ∈ L)
    (huv : g u ≠ g v) (huw : g u ≠ g w) (hvw : g v ≠ g w) :
    ∃ a b c, (∀ t, t = a ∨ t = b ∨ t = c ↔ t = u ∨ t = v ∨ t = w) ∧ ∃ A B D F, L = A ++ g a :: (B ++ g b :: (D ++ g c :: F)) := by
  induction L with
  | nil => simp at hu
  | cons z L ih =>
    by_cases hzu : z = g u
    · subst hzu
      obtain ⟨a, b, hab, A, B, D, rfl⟩ := exists_sort_two (g := g) ((List.mem_cons.1 hv).resolve_left (Ne.symm huv))
        ((List.mem_cons.1 hw).resolve_left (Ne.symm huw)) hvw
      refine ⟨u, a, b, fun t => ?_, [], A, B, D, rfl⟩
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
    by_cases hzv : z = g v
    · subst hzv
      obtain ⟨a, b, hab, A, B, D, rfl⟩ := exists_sort_two (g := g) ((List.mem_cons.1 hu).resolve_left huv)
        ((List.mem_cons.1 hw).resolve_left (Ne.symm hvw)) huw
      refine ⟨v, a, b, fun t => ?_, [], A, B, D, rfl⟩
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
    by_cases hzw : z = g w
    · subst hzw
      obtain ⟨a, b, hab, A, B, D, rfl⟩ := exists_sort_two (g := g) ((List.mem_cons.1 hu).resolve_left huw)
        ((List.mem_cons.1 hv).resolve_left hvw) huv
      refine ⟨w, a, b, fun t => ?_, [], A, B, D, rfl⟩
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
    obtain ⟨a, b, c, habc, A, B, D, F, rfl⟩ := ih ((List.mem_cons.1 hu).resolve_left (Ne.symm hzu))
      ((List.mem_cons.1 hv).resolve_left (Ne.symm hzv)) ((List.mem_cons.1 hw).resolve_left (Ne.symm hzw))
    exact ⟨a, b, c, habc, z :: A, B, D, F, rfl⟩

/-- A pair in order is a sublist. -/
theorem pair_sublist (X : List α) (u : α) (Y : List α) (w : α) (Z : List α) : List.Sublist [u, w] (X ++ u :: (Y ++ w :: Z)) := by
  induction X with
  | nil =>
    refine List.Sublist.cons_cons u ?_
    exact List.singleton_sublist.2 (by simp)
  | cons a X ih => exact List.Sublist.cons a ih

end Lists

/-! ### Directed paths and sublists -/

section Paths

variable {N : RootedNetwork V E X}

/-- On a directed path, a vertex before another reaches it. -/
theorem IsDirPath.reaches_of_sublist {t e : V} {p : List E} (hp : N.IsDirPath t p e) {w u : V}
    (h : List.Sublist [w, u] (t :: p.map N.graph.target)) : N.graph.Reaches w u := by
  induction p generalizing t with
  | nil =>
    simp only [List.map_nil] at h
    have := h.length_le
    simp at this
  | cons f p ih =>
    obtain ⟨rfl, hp⟩ := hp
    simp only [List.map_cons] at h
    rcases List.sublist_cons_iff.1 h with h' | ⟨l, hl, h'⟩
    · exact ih hp h'
    · simp only [List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      have hmem : u ∈ N.graph.target f :: p.map N.graph.target := by
        simpa using List.singleton_sublist.1 h'
      rcases List.mem_cons.1 hmem with rfl | hu
      · exact .single ⟨f, rfl, rfl⟩
      · exact Relation.ReflTransGen.head ⟨f, rfl, rfl⟩ (hp.reaches_of_mem_map hu).1

end Paths

/-- A walk stops at each of its steps. -/
theorem IsWalk.split_cons {N : RootedNetwork V E X} {u v : V} {A R : List (E × V)} {t : E × V}
    (h : N.IsWalk u (A ++ t :: R) v) : N.IsWalk u (A ++ [t]) t.2 ∧ N.IsWalk t.2 R v := by
  induction A generalizing u with
  | nil => exact ⟨⟨h.1, rfl⟩, h.2⟩
  | cons a A ih =>
    obtain ⟨h₁, h₂⟩ := ih h.2
    exact ⟨⟨h.1, h₁⟩, h₂⟩

/-- The arcs of a walk have their ends among its vertices. -/
theorem IsWalk.ends_mem {N : RootedNetwork V E X} {u v : V} {l : List (E × V)} (h : N.IsWalk u l v) {f : E}
    (hf : f ∈ l.map Prod.fst) : N.graph.source f ∈ u :: l.map Prod.snd ∧ N.graph.target f ∈ u :: l.map Prod.snd := by
  induction l generalizing u with
  | nil => simp at hf
  | cons t l ih =>
    simp only [List.map_cons, List.mem_cons] at hf ⊢
    rcases hf with rfl | hf
    · rcases h.1 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact ⟨Or.inl h₁, Or.inr (Or.inl h₂)⟩
      · exact ⟨Or.inr (Or.inl h₁), Or.inl h₂⟩
    · obtain ⟨h₁, h₂⟩ := ih h.2 hf
      exact ⟨Or.inr (List.mem_cons.1 h₁), Or.inr (List.mem_cons.1 h₂)⟩

/-- **The cycle in four segments**, between the four attachments `b 0 = h`, `b 1`, `b 2`, `b 3` in their order around it. -/
structure CycleGaps (N : RootedNetwork V E X) (h : V) (b : Fin 4 → V) (P : Fin 4 → List (E × V)) (s : Fin 4 → E) : Prop where
  base : b 0 = h
  walk : ∀ i, N.IsWalk (b i) (P i ++ [(s i, b (i + 1))]) (b (i + 1))
  cover : ∀ f ∈ N.graph.blobArcs h, ∃ i, f = s i ∨ f ∈ (P i).map Prod.fst
  arc_last : ∀ i, s i ∈ N.graph.blobArcs h
  arc_mem : ∀ i, ∀ f ∈ (P i).map Prod.fst, f ∈ N.graph.blobArcs h
  ne_of_mem : ∀ i j, ∀ c ∈ (P i).map Prod.snd, c ≠ b j
  eq_of_mem : ∀ i j, ∀ c ∈ (P i).map Prod.snd, c ∈ (P j).map Prod.snd → i = j
  inj : Function.Injective b

/-- The facts on the five parts of a list with no repetition. -/
theorem nodup_five {α : Type*} {h a b c : α} {A B D G : List α} (hnd : (h :: (A ++ a :: (B ++ b :: (D ++ c :: G)))).Nodup) :
    (∀ i j : Fin 4, ∀ z ∈ (![A, B, D, G] : Fin 4 → List α) i, z ≠ (![h, a, b, c] : Fin 4 → α) j) ∧
    (∀ i j : Fin 4, ∀ z ∈ (![A, B, D, G] : Fin 4 → List α) i, z ∈ (![A, B, D, G] : Fin 4 → List α) j → i = j) ∧
    Function.Injective (![h, a, b, c] : Fin 4 → α) := by
  simp only [List.nodup_cons, List.nodup_append, List.mem_append, List.mem_cons, not_or] at hnd
  refine ⟨fun i j z hz => ?_, fun i j z hz hz' => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp at hz ⊢ <;> grind
  · fin_cases i <;> fin_cases j <;> simp at hz hz' ⊢ <;> grind
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> grind

/-! ### The 4-cycle -/

/-- The labelled graph is the 4-cycle on `a, b, c, d`, literally: four taxa, four vertices next to them, and the eight edges. "`N_c⁻` displays a
4-cycle joining taxa in circular order `a, b, c, d`" (line 491). -/
def HasFourCycleTopology {W Y : Type*} (T : LabelledGraph W Y) (a b c d : Y) : Prop :=
  ∃ ua ub uc ud : W, [T.leaf a, T.leaf b, T.leaf c, T.leaf d, ua, ub, uc, ud].Nodup ∧
    (∀ v, v ∈ [T.leaf a, T.leaf b, T.leaf c, T.leaf d, ua, ub, uc, ud]) ∧
    T.graph.edgeSet = {s(T.leaf a, ua), s(T.leaf b, ub), s(T.leaf c, uc), s(T.leaf d, ud), s(ua, ub), s(ub, uc), s(uc, ud), s(ud, ua)}

theorem HasFourCycleTopology.rotate {W Y : Type*} {T : LabelledGraph W Y} {a b c d : Y} (h : HasFourCycleTopology T a b c d) :
    HasFourCycleTopology T b c d a := by
  obtain ⟨ua, ub, uc, ud, hnd, hall, hE⟩ := h
  refine ⟨ub, uc, ud, ua, ?_, fun v => ?_, ?_⟩
  · refine (List.Perm.nodup_iff ?_).1 hnd
    simp only [List.perm_iff_count]
    intro v
    simp only [List.count_cons, List.count_nil]
    omega
  · have := hall v
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    tauto
  · rw [hE]
    ext e
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

theorem HasFourCycleTopology.reflect {W Y : Type*} {T : LabelledGraph W Y} {a b c d : Y} (h : HasFourCycleTopology T a b c d) :
    HasFourCycleTopology T a d c b := by
  obtain ⟨ua, ub, uc, ud, hnd, hall, hE⟩ := h
  refine ⟨ua, ud, uc, ub, ?_, fun v => ?_, ?_⟩
  · refine (List.Perm.nodup_iff ?_).1 hnd
    simp only [List.perm_iff_count]
    intro v
    simp only [List.count_cons, List.count_nil]
    omega
  · have := hall v
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    tauto
  · rw [hE]
    ext e
    have h₁ : s(ua, ud) = s(ud, ua) := Sym2.eq_swap
    have h₂ : s(ud, uc) = s(uc, ud) := Sym2.eq_swap
    have h₃ : s(uc, ub) = s(ub, uc) := Sym2.eq_swap
    have h₄ : s(ub, ua) = s(ua, ub) := Sym2.eq_swap
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, h₁, h₂, h₃, h₄]
    tauto

/-- The taxa `x`, `y` are adjacent on the graph: the vertices next to them are joined. -/
def AdjTaxa {W Y : Type*} (T : LabelledGraph W Y) (x y : Y) : Prop :=
  ∃ u v, T.graph.Adj (T.leaf x) u ∧ T.graph.Adj (T.leaf y) v ∧ T.graph.Adj u v

theorem HasFourCycleTopology.adjTaxa {W Y : Type*} {T : LabelledGraph W Y} {a b c d : Y} (h : HasFourCycleTopology T a b c d) :
    AdjTaxa T a b := by
  obtain ⟨ua, ub, uc, ud, -, -, hE⟩ := h
  have hadj : ∀ {p r : W}, s(p, r) ∈ T.graph.edgeSet → T.graph.Adj p r := fun h => h
  refine ⟨ua, ub, hadj ?_, hadj ?_, hadj ?_⟩ <;> rw [hE] <;> simp

/-- Opposite taxa on the 4-cycle are not adjacent. -/
theorem HasFourCycleTopology.not_adjTaxa {W Y : Type*} {T : LabelledGraph W Y} {a b c d : Y} (h : HasFourCycleTopology T a b c d) :
    ¬ AdjTaxa T a c := by
  obtain ⟨ua, ub, uc, ud, hnd, -, hE⟩ := h
  rintro ⟨u, v, hu, hv, huv⟩
  have hmem : ∀ {p r : W}, T.graph.Adj p r → s(p, r) ∈ T.graph.edgeSet := fun h => h
  have h₁ := hmem hu
  have h₂ := hmem hv
  have h₃ := hmem huv
  rw [hE] at h₁ h₂ h₃
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff] at h₁ h₂ h₃
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true] at hnd
  grind

/-! ### The four taxa around the cycle -/

section Frame

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {q : Finset X} {a : X} {h T : V} {k₁ k₂ : E} {pL pR : List E}

omit [Fintype X] in
/-- **The four taxa, in their order around the cycle**, starting with the taxon below the reticulation. The cycle is walked from `h`
through `k₁`, up `pL`, down `pR`, and back through `k₂`. `b` are the attachments. -/
theorem exists_cycleGaps (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (F : CycleFrame N q a h h T k₁ k₂ pL pR) :
    ∃ (y : Fin 4 → X) (b : Fin 4 → V) (P : Fin 4 → List (E × V)) (s : Fin 4 → E),
      y 0 = a ∧ (∀ i, y i ∈ q) ∧ (∀ x ∈ q, ∃ i, x = y i) ∧ Function.Injective y ∧ (∀ i, IsAttachment N h (y i) (b i)) ∧
      CycleGaps N h b P s ∧
      List.Sublist [b 1, b 2] ((pL.map N.graph.target).reverse ++ T :: pR.map N.graph.target) ∧
      List.Sublist [b 2, b 3] ((pL.map N.graph.target).reverse ++ T :: pR.map N.graph.target) := by
  have hA := hN.acyclic
  have C := F.cycle
  have hh₂ := F.two_le
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl hh₂
  have hex : ∀ z, ∃ b, IsAttachment N h z b := fun z => exists_isAttachment hN (hx' z)
  choose att hatt using hex
  -- the other three taxa
  have hc3 : #(q.erase a) = 3 := by rw [card_erase_of_mem F.mem, F.card]
  obtain ⟨x₁, x₂, x₃, h₁₂, h₁₃, h₂₃, hE⟩ := card_eq_three.1 hc3
  have hmemE : ∀ z, z ∈ q.erase a ↔ z = x₁ ∨ z = x₂ ∨ z = x₃ := fun z => by
    rw [hE]
    simp
  have hne_h : ∀ {z : X}, z ∈ q.erase a → att z ≠ h := fun hz =>
    IsAttachment.ne_of_not_below hN hBin hLevel hh₂ (hatt _) (F.only _ (mem_of_mem_erase hz) (ne_of_mem_erase hz))
  have hinjatt : ∀ {u v : X}, u ∈ q → v ∈ q → att u = att v → u = v := fun {u v} hu hv he =>
    frame_eq_of_attachment hN hBin hLevel F hu hv (hatt u) (he ▸ hatt v)
  -- the walk around the cycle
  have hWP : N.IsWedgePath (N.graph.source k₁) (N.graph.source k₂) T pL pR := IsWedgePath.of_disjoint hA C.left C.right C.disjoint
  set St := N.wedgeSteps T pL pR with hSt
  set St' : List (E × V) := (k₁, N.graph.source k₁) :: St with hSt'
  have hwalk : N.IsWalk h St' (N.graph.source k₂) := ⟨Or.inr ⟨rfl, C.target₁⟩, hWP.isPath.walk⟩
  have hverts : St'.map Prod.snd = (pL.map N.graph.target).reverse ++ T :: pR.map N.graph.target := hWP.verts
  have hnotL : h ∉ T :: pL.map N.graph.target := by
    intro hm
    rcases List.mem_cons.1 hm with he | hm
    · exact C.top_ne hN he.symm
    · exact C.reticulation_notMem_left hN hm
  have hnotR : h ∉ pR.map N.graph.target := fun hm => C.swap.reticulation_notMem_left hN hm
  have hnd : (h :: St'.map Prod.snd).Nodup := by
    rw [hverts]
    refine List.nodup_cons.2 ⟨?_, hWP.distinct⟩
    simp only [List.mem_append, List.mem_reverse, List.mem_cons, not_or]
    exact ⟨fun hm => hnotL (List.mem_cons_of_mem _ hm), fun he => hnotL (he ▸ List.mem_cons_self), hnotR⟩
  have hmemV : ∀ {u : V}, N.graph.blobSetoid h u → u ≠ h → u ∈ St'.map Prod.snd := by
    intro u hu huh
    rw [hverts]
    rcases C.mem_of_sameBlob hN hLevel hh₂ hu huh with hm | hm
    · rcases List.mem_cons.1 hm with he | hm
      · simp [he]
      · simp [hm]
    · rcases List.mem_cons.1 hm with he | hm
      · simp [he]
      · simp [hm]
  have hstep : ∀ z, z ∈ q.erase a → ∃ st ∈ St', st.2 = att z := fun z hz => by
    obtain ⟨st, hst, he⟩ := List.mem_map.1 (hmemV (hatt z).1 (hne_h hz))
    exact ⟨st, hst, he⟩
  have hEV : Nonempty (E × V) := ⟨(k₁, h)⟩
  choose! g hg using hstep
  have hx₁ : x₁ ∈ q.erase a := (hmemE _).2 (Or.inl rfl)
  have hx₂ : x₂ ∈ q.erase a := (hmemE _).2 (Or.inr (Or.inl rfl))
  have hx₃ : x₃ ∈ q.erase a := (hmemE _).2 (Or.inr (Or.inr rfl))
  have hgne : ∀ {u v : X}, u ∈ q.erase a → v ∈ q.erase a → u ≠ v → g u ≠ g v := fun hu hv huv he =>
    huv (hinjatt (mem_of_mem_erase hu) (mem_of_mem_erase hv) (by rw [← (hg _ hu).2, ← (hg _ hv).2, he]))
  obtain ⟨a₁, a₂, a₃, hall, A, B, D, G, heq⟩ := exists_sort_three (g := g) (L := St') (hg _ hx₁).1 (hg _ hx₂).1 (hg _ hx₃).1
    (hgne hx₁ hx₂ h₁₂) (hgne hx₁ hx₃ h₁₃) (hgne hx₂ hx₃ h₂₃)
  have hm₁ : a₁ ∈ q.erase a := (hmemE _).2 ((hall a₁).1 (Or.inl rfl))
  have hm₂ : a₂ ∈ q.erase a := (hmemE _).2 ((hall a₂).1 (Or.inr (Or.inl rfl)))
  have hm₃ : a₃ ∈ q.erase a := (hmemE _).2 ((hall a₃).1 (Or.inr (Or.inr rfl)))
  have hg₁ : g a₁ = ((g a₁).1, att a₁) := Prod.ext rfl (hg _ hm₁).2
  have hg₂ : g a₂ = ((g a₂).1, att a₂) := Prod.ext rfl (hg _ hm₂).2
  have hg₃ : g a₃ = ((g a₃).1, att a₃) := Prod.ext rfl (hg _ hm₃).2
  set e₁ := (g a₁).1
  set e₂ := (g a₂).1
  set e₃ := (g a₃).1
  rw [hg₁, hg₂, hg₃] at heq
  rw [heq] at hwalk
  obtain ⟨w₁, r₁⟩ := IsWalk.split_cons hwalk
  obtain ⟨w₂, r₂⟩ := IsWalk.split_cons r₁
  obtain ⟨w₃, r₃⟩ := IsWalk.split_cons r₂
  have w₄ : N.IsWalk (att a₃) (G ++ [(k₂, h)]) h := IsWalk.append r₃ ⟨Or.inl ⟨rfl, C.target₂⟩, rfl⟩
  -- the vertices
  have hvs : St'.map Prod.snd = A.map Prod.snd ++ att a₁ :: (B.map Prod.snd ++ att a₂ :: (D.map Prod.snd ++ att a₃ :: G.map Prod.snd)) := by
    rw [heq]
    simp
  have hnd' := hnd
  rw [hvs] at hnd'
  obtain ⟨hne, hint, hinj⟩ := nodup_five hnd'
  -- the arcs
  have hfst : St'.map Prod.fst = A.map Prod.fst ++ e₁ :: (B.map Prod.fst ++ e₂ :: (D.map Prod.fst ++ e₃ :: G.map Prod.fst)) := by
    rw [heq]
    simp
  have hSfst : ∀ f, f ∈ St'.map Prod.fst ↔ f = k₁ ∨ f ∈ pL ∨ f ∈ pR := by
    intro f
    simp only [hSt', List.map_cons, List.mem_cons, hSt, map_fst_wedgeSteps, List.mem_append, List.mem_reverse]
  have hblobSt : ∀ f ∈ St'.map Prod.fst, f ∈ N.graph.blobArcs h := by
    intro f hf
    rcases (hSfst f).1 hf with rfl | hf | hf
    · exact mem_blobArcs_iff.2 (C.sameBlob_of_mem hN (by simp))
    · exact mem_blobArcs_iff.2 (C.sameBlob_of_mem hN (by simp [hf]))
    · exact mem_blobArcs_iff.2 (C.swap.sameBlob_of_mem hN (by simp [hf]))
  have hk₂b : k₂ ∈ N.graph.blobArcs h := mem_blobArcs_iff.2 (C.swap.sameBlob_of_mem hN (by simp))
  have hfstmem : ∀ {f : E}, (f ∈ A.map Prod.fst ∨ f = e₁ ∨ f ∈ B.map Prod.fst ∨ f = e₂ ∨ f ∈ D.map Prod.fst ∨ f = e₃ ∨
      f ∈ G.map Prod.fst) ↔ f ∈ St'.map Prod.fst := by
    intro f
    rw [hfst]
    simp only [List.mem_append, List.mem_cons]
  refine ⟨![a, a₁, a₂, a₃], ![h, att a₁, att a₂, att a₃], ![A, B, D, G], ![e₁, e₂, e₃, k₂], rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact F.mem
    · exact mem_of_mem_erase hm₁
    · exact mem_of_mem_erase hm₂
    · exact mem_of_mem_erase hm₃
  · intro x hx
    by_cases hxa : x = a
    · exact ⟨0, hxa⟩
    have hxE : x ∈ q.erase a := mem_erase.2 ⟨hxa, hx⟩
    rcases (hall x).2 ((hmemE x).1 hxE) with rfl | rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · intro i j hij
    have hatt' : ∀ i, IsAttachment N h ((![a, a₁, a₂, a₃] : Fin 4 → X) i) ((![h, att a₁, att a₂, att a₃] : Fin 4 → V) i) := by
      intro i
      fin_cases i
      · exact isAttachment_of_below hN hBin hLevel hh₂ F.below
      · exact hatt _
      · exact hatt _
      · exact hatt _
    refine hinj (IsAttachment.eq_of_isAttachment (hx' _) (hatt' i) ?_)
    rw [hij]
    exact hatt' j
  · intro i
    fin_cases i
    · exact isAttachment_of_below hN hBin hLevel hh₂ F.below
    · exact hatt _
    · exact hatt _
    · exact hatt _
  · refine ⟨rfl, fun i => ?_, fun f hf => ?_, fun i => ?_, fun i f hf => ?_, fun i j c hc => ?_, fun i j c hc hc' => ?_, ?_⟩
    · fin_cases i
      · exact w₁
      · exact w₂
      · exact w₃
      · exact w₄
    · obtain ⟨hs', ht'⟩ := mem_blobArcs_iff.1 hf
      by_cases hth : N.graph.target f = h
      · rcases C.arcs f hth with rfl | rfl
        · have := hfstmem (f := f).2 ((hSfst f).2 (Or.inl rfl))
          rcases this with h' | h' | h' | h' | h' | h' | h'
          · exact ⟨0, Or.inr h'⟩
          · exact ⟨0, Or.inl h'⟩
          · exact ⟨1, Or.inr h'⟩
          · exact ⟨1, Or.inl h'⟩
          · exact ⟨2, Or.inr h'⟩
          · exact ⟨2, Or.inl h'⟩
          · exact ⟨3, Or.inr h'⟩
        · exact ⟨3, Or.inl rfl⟩
      · have := hfstmem (f := f).2 ((hSfst f).2 (Or.inr (C.mem_of_arc hN hLevel hh₂ hs' ht' hth)))
        rcases this with h' | h' | h' | h' | h' | h' | h'
        · exact ⟨0, Or.inr h'⟩
        · exact ⟨0, Or.inl h'⟩
        · exact ⟨1, Or.inr h'⟩
        · exact ⟨1, Or.inl h'⟩
        · exact ⟨2, Or.inr h'⟩
        · exact ⟨2, Or.inl h'⟩
        · exact ⟨3, Or.inr h'⟩
    · fin_cases i
      · exact hblobSt _ (hfstmem.1 (Or.inr (Or.inl rfl)))
      · exact hblobSt _ (hfstmem.1 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact hblobSt _ (hfstmem.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      · exact hk₂b
    · fin_cases i
      · exact hblobSt _ (hfstmem.1 (Or.inl hf))
      · exact hblobSt _ (hfstmem.1 (Or.inr (Or.inr (Or.inl hf))))
      · exact hblobSt _ (hfstmem.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf))))))
      · exact hblobSt _ (hfstmem.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hf)))))))
    · have hmap : ∀ i : Fin 4, ((![A, B, D, G] : Fin 4 → List (E × V)) i).map Prod.snd =
          (![A.map Prod.snd, B.map Prod.snd, D.map Prod.snd, G.map Prod.snd] : Fin 4 → List V) i := by
        intro i
        fin_cases i <;> rfl
      rw [hmap] at hc
      exact hne i j c hc
    · have hmap : ∀ i : Fin 4, ((![A, B, D, G] : Fin 4 → List (E × V)) i).map Prod.snd =
          (![A.map Prod.snd, B.map Prod.snd, D.map Prod.snd, G.map Prod.snd] : Fin 4 → List V) i := by
        intro i
        fin_cases i <;> rfl
      rw [hmap] at hc hc'
      exact hint i j c hc hc'
    · exact hinj
  · rw [← hverts, hvs]
    have := pair_sublist (A.map Prod.snd) (att a₁) (B.map Prod.snd) (att a₂) (D.map Prod.snd ++ att a₃ :: G.map Prod.snd)
    exact this
  · rw [← hverts, hvs]
    have := pair_sublist (A.map Prod.snd ++ att a₁ :: B.map Prod.snd) (att a₂) (D.map Prod.snd) (att a₃) (G.map Prod.snd)
    simpa using this

/-- The data of `exists_cycleGaps`. -/
structure CycleData (N : RootedNetwork V E X) (q : Finset X) (a : X) (h T : V) (k₁ k₂ : E) (pL pR : List E)
    (y : Fin 4 → X) (b : Fin 4 → V) (P : Fin 4 → List (E × V)) (s : Fin 4 → E) : Prop where
  frame : CycleFrame N q a h h T k₁ k₂ pL pR
  y_zero : y 0 = a
  y_mem : ∀ i, y i ∈ q
  y_surj : ∀ x ∈ q, ∃ i, x = y i
  y_inj : Function.Injective y
  att : ∀ i, IsAttachment N h (y i) (b i)
  gaps : CycleGaps N h b P s

end Frame

/-! ### Walks in the contracted graph -/

section Chains

variable {N : RootedNetwork V E X} {q : Finset X}

theorem adjOn_of_joins {e : E} (he : e ∈ trekArcs N q) (hc : e ∉ contractedArcs N q) {u w : V} (hj : N.Joins e u w)
    (hu : IsKept N q u) (hw : IsKept N q w) : (tildeGraph N q).AdjOn Set.univ (toV hu) (toV hw) := by
  refine ⟨⟨e, he, hc⟩, Set.mem_univ _, ?_⟩
  rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem toV_eq_of_joins {e : E} (hc : e ∈ contractedArcs N q) {u w : V} (hj : N.Joins e u w)
    {hu : IsKept N q u} {hw : IsKept N q w} : toV hu = toV hw := by
  rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact toV_eq_of_mem_contractedArcs hc
  · exact (toV_eq_of_mem_contractedArcs hc).symm

theorem Joins.isKept_left {e : E} (he : e ∈ trekArcs N q) {u w : V} (hj : N.Joins e u w) : IsKept N q u := by
  rcases hj with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · exact isKept_source he
  · exact isKept_target he

theorem Joins.isKept_right {e : E} (he : e ∈ trekArcs N q) {u w : V} (hj : N.Joins e u w) : IsKept N q w := by
  rcases hj with ⟨-, rfl⟩ | ⟨rfl, -⟩
  · exact isKept_target he
  · exact isKept_source he

/-- A walk of kept edges through vertices of degree two is a chain of the contracted graph. -/
theorem chain_of_walk {u w : V} {l : List (E × V)} (hl : N.IsWalk u l w) (hK : ∀ t ∈ l, t.1 ∈ trekArcs N q)
    (hdeg : ∀ t ∈ l, t.2 ≠ w → ∀ hk : IsKept N q t.2, nodeDegree (tildeGraph N q) (toV hk) = 2)
    (hu : IsKept N q u) (hw : IsKept N q w) :
    ∃ x, Relation.ReflTransGen (Enter (tildeGraph N q)) (toV hu) x ∧
      (x = toV hw ∨ (tildeGraph N q).AdjOn Set.univ x (toV hw)) := by
  induction l generalizing u with
  | nil =>
    obtain rfl : u = w := hl
    exact ⟨toV hu, .refl, Or.inl rfl⟩
  | cons t l ih =>
    obtain ⟨e, w'⟩ := t
    obtain ⟨hj, hl'⟩ := hl
    have he : e ∈ trekArcs N q := hK (e, w') (by simp)
    have hw' : IsKept N q w' := Joins.isKept_right he hj
    obtain ⟨x, hx, hend⟩ := ih hl' (fun t ht => hK t (by simp [ht])) (fun t ht => hdeg t (by simp [ht])) hw'
    by_cases hc : e ∈ contractedArcs N q
    · rw [toV_eq_of_joins hc hj (hw := hw')]
      exact ⟨x, hx, hend⟩
    · have hadj := adjOn_of_joins he hc hj hu hw'
      by_cases hww : w' = w
      · subst hww
        exact ⟨toV hu, .refl, Or.inr hadj⟩
      · exact ⟨x, Relation.ReflTransGen.head ⟨hadj, hdeg (e, w') (by simp) hww hw'⟩ hx, hend⟩

/-- A chain to a vertex of degree other than two, from another class. -/
theorem chainLink_of_chain {α β : V} {hα : IsKept N q α} {hβ : IsKept N q β} (hne : toV hα ≠ toV hβ)
    (hd : nodeDegree (tildeGraph N q) (toV hβ) ≠ 2)
    (h : ∃ x, Relation.ReflTransGen (Enter (tildeGraph N q)) (toV hα) x ∧
      (x = toV hβ ∨ (tildeGraph N q).AdjOn Set.univ x (toV hβ))) :
    ChainLink (tildeGraph N q) (toV hα) (toV hβ) := by
  obtain ⟨x, hx, hend⟩ := h
  rcases hend with rfl | hadj
  · exfalso
    rcases Relation.ReflTransGen.cases_tail hx with he | ⟨c, -, -, hd'⟩
    · exact hne he.symm
    · exact hd hd'
  · exact ⟨x, hx, hadj⟩

theorem IsWalk.incident_of_mem {u w : V} {l : List (E × V)} (hl : N.IsWalk u l w) {t : E × V} (ht : t ∈ l) :
    N.Incident t.1 t.2 := by
  induction l generalizing u with
  | nil => simp at ht
  | cons t' l ih =>
    rcases List.mem_cons.1 ht with rfl | ht
    · exact hl.1.symm.incident
    · exact ih hl.2 ht

end Chains

/-! ### The literal cycle -/

section Literal

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {q : Finset X} {a : X} {h T : V} {k₁ k₂ : E} {pL pR : List E}
variable {y : Fin 4 → X} {b : Fin 4 → V} {P : Fin 4 → List (E × V)} {s : Fin 4 → E}
variable (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (D : CycleData N q a h T k₁ k₂ pL pR y b P s)
include hN hBin hLevel D

omit [Fintype X] [DecidableEq X] in
/-- An attachment is kept. -/
theorem CycleData.kept_b (i : Fin 4) : IsKept N q (b i) := isKept_of_blob hN hBin hLevel D.frame (D.att i).1

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] hBin hLevel in
/-- A taxon is kept. -/
theorem CycleData.kept_leaf (x : X) (hx : x ∈ q) : IsKept N q (N.leaf x) :=
  isKept_leaf' hN (by rw [D.frame.card]; norm_num) hx

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] hN hBin hLevel in
/-- A vertex between attachments is on the cycle. -/
theorem CycleData.blob_of_interior {i : Fin 4} {c : V} (hc : c ∈ (P i).map Prod.snd) : N.graph.blobSetoid h c := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
  have hinc := IsWalk.incident_of_mem (D.gaps.walk i) (List.mem_append_left _ ht)
  have hb := D.gaps.arc_mem i t.1 (List.mem_map_of_mem ht)
  obtain ⟨h₁, h₂⟩ := mem_blobArcs_iff.1 hb
  rcases hinc with he | he
  · rwa [← he]
  · rwa [← he]

/-- **A vertex between attachments has degree two.** -/
theorem CycleData.degree_of_interior {i : Fin 4} {c : V} (hc : c ∈ (P i).map Prod.snd) (hk : IsKept N q c) :
    nodeDegree (tildeGraph N q) (toV hk) = 2 := by
  have hcb := D.blob_of_interior hc
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl D.frame.two_le
  refine (nodeDegree_eq_of_frame hN hBin hLevel D.frame).1 _ (fun x _ hx he => ?_) fun x hx b' hb' hkb' he => ?_
  · have := eq_of_toV_leaf_eq hN he.symm
    exact hx' x (this ▸ hcb)
  · have hcb' := eq_of_toV_blob_eq hN hLevel D.frame hBin hb'.1 he.symm
    obtain ⟨j, rfl⟩ := D.y_surj x hx
    have : b' = b j := IsAttachment.eq_of_isAttachment (hx' _) hb' (D.att j)
    exact D.gaps.ne_of_mem i j c hc (hcb'.trans this)

/-- **The attachments are joined around the cycle.** -/
theorem CycleData.chainLink_gap (i : Fin 4) :
    ChainLink (tildeGraph N q) (toV (D.kept_b hN hBin hLevel i)) (toV (D.kept_b hN hBin hLevel (i + 1))) := by
  have hQ := frame_hQ hN hBin hLevel D.frame
  have hne : b i ≠ b (i + 1) := fun he => by
    have key : ∀ i : Fin 4, i ≠ i + 1 := by decide
    exact key i (D.gaps.inj he)
  refine chainLink_of_chain (fun he => hne ?_) ?_ (chain_of_walk (D.gaps.walk i) (fun t ht => ?_) (fun t ht hne' hk => ?_) _ _)
  · exact eq_of_toV_blob_eq hN hLevel D.frame hBin (D.att (i + 1)).1 he
  · rw [(nodeDegree_eq_of_frame hN hBin hLevel D.frame).2 _ (D.y_mem (i + 1)) _ (D.att (i + 1)) _]
    norm_num
  · rcases List.mem_append.1 ht with ht | ht
    · exact hQ.2 _ (D.gaps.arc_mem i t.1 (List.mem_map_of_mem ht))
    · obtain rfl := List.mem_singleton.1 ht
      exact hQ.2 _ (D.gaps.arc_last i)
  · rcases List.mem_append.1 ht with ht | ht
    · exact D.degree_of_interior hN hBin hLevel (List.mem_map_of_mem ht) hk
    · obtain rfl := List.mem_singleton.1 ht
      exact absurd rfl hne'

/-- A walk in the block of a taxon, of kept arcs, from the taxon to its attachment, or back, is a chain. -/
theorem CycleData.degree_of_block {x : X} (hx : x ∈ q) {z : V} (hz : BlockWalk N h (N.leaf x) z) (hzx : z ≠ N.leaf x)
    (hk : IsKept N q z) : nodeDegree (tildeGraph N q) (toV hk) = 2 := by
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl D.frame.two_le
  refine (nodeDegree_eq_of_frame hN hBin hLevel D.frame).1 _ (fun x' hx'q hl he => ?_) fun x' _ b' hb' hkb' he => ?_
  · have hzl := eq_of_toV_leaf_eq hN he.symm
    have hxe : x = x' := by
      by_contra hne
      exact D.frame.distinct x hx x' hx'q hne (hzl ▸ hz)
    exact hzx (hzl.trans (hxe ▸ rfl))
  · have hzb := eq_of_toV_blob_eq hN hLevel D.frame hBin hb'.1 he.symm
    exact not_sameBlob_of_blockWalk (hx' x) hz (hzb ▸ hb'.1)

/-- **A taxon is joined to its attachment.** -/
theorem CycleData.chainLink_leaf (i : Fin 4) :
    ChainLink (tildeGraph N q) (toV (D.kept_leaf hN (y i) (D.y_mem i))) (toV (D.kept_b hN hBin hLevel i)) := by
  have F := D.frame
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl F.two_le
  have hne : toV (D.kept_leaf hN (y i) (D.y_mem i)) ≠ toV (D.kept_b hN hBin hLevel i) := fun he => by
    have := eq_of_toV_leaf_eq hN he.symm
    exact hx' (y i) (this ▸ (D.att i).1)
  have hd3 : nodeDegree (tildeGraph N q) (toV (D.kept_b hN hBin hLevel i)) ≠ 2 := by
    rw [(nodeDegree_eq_of_frame hN hBin hLevel F).2 _ (D.y_mem i) _ (D.att i) _]
    norm_num
  -- the path from `h` to the taxon below it
  obtain ⟨l, hl, hlb⟩ := exists_path_of_below_reticulation hN hLevel (v := h) .refl F.two_le F.below
  have hglue : ∀ {j : Fin 4}, y j ≠ a → ∃ (u : V) (l₁ l₂ : List E), AttachPath N h (y j) (b j) u l₁ l₂ ∧
      ∀ f, f ∈ l ∨ f ∈ l₁ ∨ f ∈ l₂ → f ∈ N.wedgeArcs (q : Set X) := by
    intro j hj
    obtain ⟨u, l₁, l₂, hP⟩ := (D.att j).exists_attachPath hN (hx' _)
    have hbh : b j ≠ h := IsAttachment.ne_of_not_below hN hBin hLevel F.two_le (D.att j) (F.only _ (D.y_mem j) hj)
    obtain ⟨W, _, -, hW', -⟩ := exactly_two_wedgePaths hN hBin hLevel (v := h) .refl F.two_le (D.att j).1 hbh
    refine ⟨u, l₁, l₂, hP, fun f hf => ?_⟩
    obtain ⟨u', p, r, hw, hc⟩ := hP.glue hN (hx' _) (hx' a) (F.distinct _ (D.y_mem j) _ F.mem hj) .refl hl hlb ((hW' W).2 (Or.inl rfl))
    refine ⟨a, F.mem, y j, D.y_mem j, hj.symm, u', p, r, hw, hc f ?_⟩
    rcases hf with hf | hf | hf
    · exact Or.inl hf
    · exact Or.inr (Or.inr (Or.inr (Or.inl hf)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hf)))
  by_cases hi : i = 0
  · -- the taxon below the reticulation
    subst hi
    have hy0 : y 0 = a := D.y_zero
    have hb0 : b 0 = h := D.gaps.base
    have hy1 : y 1 ≠ a := fun he => by
      have := D.y_inj (he.trans hy0.symm)
      revert this
      decide
    obtain ⟨_, _, _, _, hK⟩ := hglue hy1
    have hwalk : N.IsWalk (b 0) (N.downSteps l) (N.leaf (y 0)) := by
      rw [hb0, hy0]
      exact hl.isWalk_downSteps
    have hrev := ChainLink.symm (chainLink_of_chain (hα := D.kept_b hN hBin hLevel 0) (hβ := D.kept_leaf hN (y 0) (D.y_mem 0))
      hne.symm ?_ (chain_of_walk hwalk (fun t ht => ?_) (fun t ht hne' hk => ?_) _ _))
    · exact hrev
    · rw [nodeDegree_toV_leaf hN]
      norm_num
    · rw [trekArcs_eq_wedgeArcs hN]
      have := List.mem_map_of_mem (f := Prod.fst) ht
      rw [map_fst_downSteps] at this
      exact hK _ (Or.inl this)
    · have hm := List.mem_map_of_mem (f := Prod.snd) ht
      rw [map_snd_downSteps] at hm
      exact D.degree_of_block hN hBin hLevel (D.y_mem 0) (by rw [hy0]; exact hlb _ hm) hne' hk
  · -- the other taxa
    have hyi : y i ≠ a := fun he => hi (D.y_inj (he.trans D.y_zero.symm))
    obtain ⟨u, l₁, l₂, hP, hK⟩ := hglue hyi
    have hpath := hP.wedge.isPath
    refine chainLink_of_chain hne hd3 (chain_of_walk hpath.walk (fun t ht => ?_) (fun t ht hne' hk => ?_) _ _)
    · rw [trekArcs_eq_wedgeArcs hN]
      exact hK _ (Or.inr (mem_of_mem_wedgeSteps ht))
    · have hzm : t.2 ∈ N.leaf (y i) :: (N.wedgeSteps u l₁ l₂).map Prod.snd := List.mem_cons_of_mem _ (List.mem_map_of_mem ht)
      have hzv := hzm
      rw [hP.wedge.verts] at hzv
      have hblock : BlockWalk N h (N.leaf (y i)) t.2 := by
        simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hzv
        rcases hzv with hz | hz | hz
        · exact hP.block₁ _ hz
        · rw [hz]
          rcases hP.summit with hs | hs
          · exact absurd (hz.trans hs) hne'
          · exact hs
        · rcases hP.block₂ _ hz with hs | hs
          · exact absurd hs hne'
          · exact hs
      have hnl : t.2 ≠ N.leaf (y i) := by
        intro he
        have hd := hpath.distinct
        exact (List.nodup_cons.1 hd).1 (he ▸ List.mem_map_of_mem ht)
      exact D.degree_of_block hN hBin hLevel (D.y_mem i) hblock hnl hk

/-! #### The edges of `Q̃` -/

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] hBin hLevel in
/-- A kept vertex off the cycle is in the block of a taxon of `q`: a wedge path through it enters its block and leaves it, if the taxa
at its ends are not in the block, and the block has only one arc crossing it. -/
theorem CycleData.exists_block {v : V} (hk : IsKept N q v) (hv : ¬ N.graph.blobSetoid h v) :
    ∃ i, BlockWalk N h (N.leaf (y i)) v := by
  obtain ⟨e, he, hve⟩ := hk
  rw [trekArcs_eq_wedgeArcs hN] at he
  obtain ⟨x, hx, x', hx', hxx, t, p, r, hw, hep⟩ := he
  obtain ⟨k, -, hS, -⟩ := exists_blockWalk_cut hN hv
  have hvw : v ∈ t :: (p.map N.graph.target ++ r.map N.graph.target) := by
    have hmem : ∀ {l : List E} {c : V}, N.IsDirPath t l c → e ∈ l → v ∈ t :: l.map N.graph.target := by
      intro l c hl hel
      rcases hve with rfl | rfl
      · exact hl.source_mem_vertices hel
      · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hel)
    rcases hep with hep | hep
    · rcases List.mem_cons.1 (hmem hw.left hep) with h' | h'
      · simp [h']
      · simp [h']
    · rcases List.mem_cons.1 (hmem hw.right hep) with h' | h'
      · simp [h']
      · simp [h']
  by_cases hxB : BlockWalk N h v (N.leaf x)
  · obtain ⟨i, rfl⟩ := D.y_surj x hx
    exact ⟨_, blockWalk_symm hxB⟩
  by_cases hxB' : BlockWalk N h v (N.leaf x')
  · obtain ⟨i, rfl⟩ := D.y_surj x' hx'
    exact ⟨_, blockWalk_symm hxB'⟩
  exfalso
  obtain ⟨f, g, hfg, -, -, hf, hg⟩ := IsWedgePath.exists_two_crosses hN hw (S := {u | BlockWalk N h v u}) hxB hxB' .refl hvw
  exact hfg (((hS f).1 hf).trans ((hS g).1 hg).symm)

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] hBin hLevel in
/-- A kept arc off the cycle is in the block of a taxon of `q`, with the attachment. -/
theorem CycleData.arc_part {e : E} (he : e ∈ trekArcs N q) (heb : e ∉ N.graph.blobArcs h) :
    ∃ i, (BlockWalk N h (N.leaf (y i)) (N.graph.source e) ∨ N.graph.source e = b i) ∧
      (BlockWalk N h (N.leaf (y i)) (N.graph.target e) ∨ N.graph.target e = b i) := by
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl D.frame.two_le
  have hbr : (N.graph.blobSetoid h (N.graph.source e) ∨ N.graph.blobSetoid h (N.graph.target e)) → N.graph.underlying.IsBridge e := by
    intro hc
    by_contra hnb
    have hsame := sameBlob_of_not_isBridge hnb
    refine heb (mem_blobArcs_iff.2 ?_)
    rcases hc with hc | hc
    · exact ⟨hc, sameBlob_trans hc hsame⟩
    · exact ⟨sameBlob_trans hc (sameBlob_symm hsame), hc⟩
  by_cases hs : N.graph.blobSetoid h (N.graph.source e)
  · have ht : ¬ N.graph.blobSetoid h (N.graph.target e) := fun ht => heb (mem_blobArcs_iff.2 ⟨hs, ht⟩)
    obtain ⟨i, hi⟩ := D.exists_block hN (isKept_target he) ht
    have hat := isAttachment_of_bridge hN (hx' _) (hbr (Or.inl hs)) hs (w := N.graph.target e) (Or.inl ⟨rfl, rfl⟩) hi
    exact ⟨i, Or.inr (IsAttachment.eq_of_isAttachment (hx' _) hat (D.att i)), Or.inl hi⟩
  · by_cases ht : N.graph.blobSetoid h (N.graph.target e)
    · obtain ⟨i, hi⟩ := D.exists_block hN (isKept_source he) hs
      have hat := isAttachment_of_bridge hN (hx' _) (hbr (Or.inr ht)) ht (w := N.graph.source e) (Or.inr ⟨rfl, rfl⟩) hi
      exact ⟨i, Or.inl hi, Or.inr (IsAttachment.eq_of_isAttachment (hx' _) hat (D.att i))⟩
    · obtain ⟨i, hi⟩ := D.exists_block hN (isKept_source he) hs
      exact ⟨i, Or.inl hi, Or.inl (hi.tail ⟨hs, ht, e, Or.inl ⟨rfl, rfl⟩⟩)⟩

/-- The block of a taxon, with its attachment, in the contracted graph. -/
def clP (N : RootedNetwork V E X) (q : Finset X) (h : V) (y : Fin 4 → X) (b : Fin 4 → V) (i : Fin 4) : Set (TildeV N q) :=
  {w | ∃ v, ∃ hv : IsKept N q v, w = toV hv ∧ (BlockWalk N h (N.leaf (y i)) v ∨ v = b i)}

/-- A segment of the cycle, with its ends, in the contracted graph. -/
def clG (N : RootedNetwork V E X) (q : Finset X) (b : Fin 4 → V) (P : Fin 4 → List (E × V)) (i : Fin 4) : Set (TildeV N q) :=
  {w | ∃ v, ∃ hv : IsKept N q v, w = toV hv ∧ (v = b i ∨ v = b (i + 1) ∨ v ∈ (P i).map Prod.snd)}

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] hN hBin hLevel in
/-- The ends of the arcs of a segment are in it. -/
theorem CycleData.ends_mem_clG {i : Fin 4} {f : E} (hf : f = s i ∨ f ∈ (P i).map Prod.fst) :
    (N.graph.source f = b i ∨ N.graph.source f = b (i + 1) ∨ N.graph.source f ∈ (P i).map Prod.snd) ∧
      (N.graph.target f = b i ∨ N.graph.target f = b (i + 1) ∨ N.graph.target f ∈ (P i).map Prod.snd) := by
  have hm : f ∈ (P i ++ [(s i, b (i + 1))]).map Prod.fst := by
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton]
    tauto
  obtain ⟨h₁, h₂⟩ := IsWalk.ends_mem (D.gaps.walk i) hm
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h₁ h₂
  tauto

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] hBin hLevel in
/-- **Every edge of the contracted graph is in a block or a segment.** -/
theorem CycleData.arc_cover (e : TildeE N q) :
    ∃ σ : Fin 4 ⊕ Fin 4, (tildeGraph N q).source e ∈ Sum.elim (clP N q h y b) (clG N q b P) σ ∧
      (tildeGraph N q).target e ∈ Sum.elim (clP N q h y b) (clG N q b P) σ := by
  by_cases heb : e.1 ∈ N.graph.blobArcs h
  · obtain ⟨i, hi⟩ := D.gaps.cover e.1 heb
    obtain ⟨h₁, h₂⟩ := D.ends_mem_clG hi
    exact ⟨Sum.inr i, ⟨_, isKept_source e.2.1, rfl, h₁⟩, ⟨_, isKept_target e.2.1, rfl, h₂⟩⟩
  · obtain ⟨i, h₁, h₂⟩ := D.arc_part hN e.2.1 heb
    exact ⟨Sum.inl i, ⟨_, isKept_source e.2.1, rfl, h₁⟩, ⟨_, isKept_target e.2.1, rfl, h₂⟩⟩

/-- A contracted arc does not cross a block. -/
theorem CycleData.not_crosses_block (i : Fin 4) {f : E} (hf : f ∈ contractedArcs N q) :
    ¬ N.graph.Crosses f {u | BlockWalk N h (N.leaf (y i)) u} := by
  obtain ⟨h₁, h₂⟩ := contracted_off_blob hN hLevel D.frame hBin hf
  rintro (⟨hs, ht⟩ | ⟨ht, hs⟩)
  · exact ht (Relation.ReflTransGen.tail hs ⟨h₁, h₂, f, Or.inl ⟨rfl, rfl⟩⟩)
  · exact hs (Relation.ReflTransGen.tail ht ⟨h₂, h₁, f, Or.inr ⟨rfl, rfl⟩⟩)

/-- **What is joined to a vertex of degree two of a block or a segment is in it.** -/
theorem CycleData.closure (σ : Fin 4 ⊕ Fin 4) {z z' : TildeV N q} (hz : z ∈ Sum.elim (clP N q h y b) (clG N q b P) σ)
    (hd : nodeDegree (tildeGraph N q) z = 2) (hadj : (tildeGraph N q).AdjOn Set.univ z z') :
    z' ∈ Sum.elim (clP N q h y b) (clG N q b P) σ := by
  have F := D.frame
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl F.two_le
  have hdeg3 : ∀ j, ∀ hv : IsKept N q (b j), nodeDegree (tildeGraph N q) (toV hv) = 3 := fun j hv =>
    (nodeDegree_eq_of_frame hN hBin hLevel F).2 _ (D.y_mem j) _ (D.att j) hv
  -- an arc at `z`, with the end at `z` and the other
  obtain ⟨e, -, hends⟩ := hadj
  obtain ⟨v₀, w₀, hv₀, hw₀, hz₀, hz'₀, hcase⟩ : ∃ (v₀ w₀ : V) (hv₀ : IsKept N q v₀) (hw₀ : IsKept N q w₀), z = toV hv₀ ∧ z' = toV hw₀ ∧
      N.Joins e.1 v₀ w₀ := by
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, _, isKept_source e.2.1, isKept_target e.2.1, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, isKept_target e.2.1, isKept_source e.2.1, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
  subst hz₀
  subst hz'₀
  rcases σ with i | i
  · obtain ⟨v, hv, hve, hcase'⟩ := hz
    have hvS : BlockWalk N h (N.leaf (y i)) v := by
      rcases hcase' with h' | h'
      · exact h'
      · subst h'
        have := hdeg3 i hv
        rw [← hve] at this
        omega
    have hv₀S : BlockWalk N h (N.leaf (y i)) v₀ :=
      (mem_iff_of_toV_eq (S := {u | BlockWalk N h (N.leaf (y i)) u}) (fun f hf => D.not_crosses_block hN hBin hLevel i hf) hve).2 hvS
    have hoff : ¬ N.graph.blobSetoid h v₀ := not_sameBlob_of_blockWalk (hx' _) hv₀S
    have heb : e.1 ∉ N.graph.blobArcs h := by
      intro hb
      obtain ⟨h₁, h₂⟩ := mem_blobArcs_iff.1 hb
      rcases hcase with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact hoff h₁
      · exact hoff h₂
    obtain ⟨j, h₁, h₂⟩ := D.arc_part hN e.2.1 heb
    have hin : BlockWalk N h (N.leaf (y j)) v₀ := by
      rcases hcase with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact h₁.resolve_right fun he => hoff (he ▸ (D.att j).1)
      · exact h₂.resolve_right fun he => hoff (he ▸ (D.att j).1)
    have hij : i = j := by
      by_contra hne
      exact F.distinct _ (D.y_mem i) _ (D.y_mem j) (fun he => hne (D.y_inj he)) (blockWalk_trans hv₀S (blockWalk_symm hin))
    subst hij
    refine ⟨w₀, hw₀, rfl, ?_⟩
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h₂
    · exact h₁
  · obtain ⟨v, hv, hve, hcase'⟩ := hz
    have hvP : v ∈ (P i).map Prod.snd := by
      rcases hcase' with h' | h' | h'
      · subst h'
        have := hdeg3 i hv
        rw [← hve] at this
        omega
      · subst h'
        have := hdeg3 (i + 1) hv
        rw [← hve] at this
        omega
      · exact h'
    have hvb := D.blob_of_interior hvP
    have hv₀v : v₀ = v := eq_of_toV_blob_eq hN hLevel F hBin hvb hve
    subst hv₀v
    have heb : e.1 ∈ N.graph.blobArcs h := by
      by_contra hnb
      have hK : e.1 ∈ N.wedgeArcs (q : Set X) := by
        rw [← trekArcs_eq_wedgeArcs hN]
        exact e.2.1
      have hinc : N.graph.source e.1 = v₀ ∨ N.graph.target e.1 = v₀ := by
        rcases hcase with ⟨h', -⟩ | ⟨-, h'⟩
        · exact Or.inl h'
        · exact Or.inr h'
      obtain ⟨x, hx, hxa⟩ := exists_isAttachment_of_kept hN F.two_le hvb hK hnb hinc
      obtain ⟨j, rfl⟩ := D.y_surj x hx
      exact D.gaps.ne_of_mem i j v₀ hvP (IsAttachment.eq_of_isAttachment (hx' _) hxa (D.att j))
    obtain ⟨j, hj⟩ := D.gaps.cover e.1 heb
    obtain ⟨h₁, h₂⟩ := D.ends_mem_clG hj
    have hv₀j : v₀ ∈ (P j).map Prod.snd := by
      have hin : v₀ = b j ∨ v₀ = b (j + 1) ∨ v₀ ∈ (P j).map Prod.snd := by
        rcases hcase with ⟨rfl, -⟩ | ⟨-, rfl⟩
        · exact h₁
        · exact h₂
      rcases hin with h' | h' | h'
      · exact absurd h' (D.gaps.ne_of_mem i j _ hvP)
      · exact absurd h' (D.gaps.ne_of_mem i (j + 1) _ hvP)
      · exact h'
    have hij : i = j := D.gaps.eq_of_mem i j _ hvP hv₀j
    subst hij
    refine ⟨w₀, hw₀, rfl, ?_⟩
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h₂
    · exact h₁

/-- **A chain between vertices has its ends in one block or segment.** -/
theorem CycleData.exists_cl_of_chainLink {p r : TildeV N q} (hc : ChainLink (tildeGraph N q) p r) :
    ∃ σ : Fin 4 ⊕ Fin 4, p ∈ Sum.elim (clP N q h y b) (clG N q b P) σ ∧ r ∈ Sum.elim (clP N q h y b) (clG N q b P) σ := by
  have hcover : ∀ {u w : TildeV N q}, (tildeGraph N q).AdjOn Set.univ u w →
      ∃ σ : Fin 4 ⊕ Fin 4, u ∈ Sum.elim (clP N q h y b) (clG N q b P) σ ∧ w ∈ Sum.elim (clP N q h y b) (clG N q b P) σ := by
    rintro u w ⟨e, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact D.arc_cover hN e
    · obtain ⟨σ, h₁, h₂⟩ := D.arc_cover hN e
      exact ⟨σ, h₂, h₁⟩
  obtain ⟨x, hx, hadj⟩ := hc
  rcases Relation.ReflTransGen.cases_head hx with rfl | ⟨z₁, ⟨hpz, hdz⟩, hzx⟩
  · exact hcover hadj
  · obtain ⟨σ, hp, hz⟩ := hcover hpz
    refine ⟨σ, hp, ?_⟩
    have hst : x ∈ Sum.elim (clP N q h y b) (clG N q b P) σ ∧ nodeDegree (tildeGraph N q) x = 2 := by
      clear hadj hx
      induction hzx with
      | refl => exact ⟨hz, hdz⟩
      | @tail c d _ hcd ih => exact ⟨D.closure hN hBin hLevel σ ih.1 ih.2 hcd.1, hcd.2⟩
    exact D.closure hN hBin hLevel σ hst.1 hst.2 hadj

/-- A vertex of degree other than two is a taxon or an attachment. -/
theorem CycleData.branch (w : TildeV N q) (hd : nodeDegree (tildeGraph N q) w ≠ 2) :
    (∃ i, w = toV (D.kept_leaf hN (y i) (D.y_mem i))) ∨ ∃ i, w = toV (D.kept_b hN hBin hLevel i) := by
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl D.frame.two_le
  by_contra hno
  push Not at hno
  refine hd ((nodeDegree_eq_of_frame hN hBin hLevel D.frame).1 w (fun x hx hk he => ?_) fun x hx b' hb' hk he => ?_)
  · obtain ⟨i, rfl⟩ := D.y_surj x hx
    exact hno.1 i he.symm
  · obtain ⟨i, rfl⟩ := D.y_surj x hx
    have hbe : b' = b i := IsAttachment.eq_of_isAttachment (hx' _) hb' (D.att i)
    subst hbe
    exact hno.2 i he.symm

/-- **The vertices of degree other than two in a block or segment are its two ends.** -/
theorem CycleData.branch_of_cl (σ : Fin 4 ⊕ Fin 4) {w : TildeV N q} (hw : w ∈ Sum.elim (clP N q h y b) (clG N q b P) σ)
    (hd : nodeDegree (tildeGraph N q) w ≠ 2) :
    match σ with
    | Sum.inl i => w = toV (D.kept_leaf hN (y i) (D.y_mem i)) ∨ w = toV (D.kept_b hN hBin hLevel i)
    | Sum.inr i => w = toV (D.kept_b hN hBin hLevel i) ∨ w = toV (D.kept_b hN hBin hLevel (i + 1)) := by
  have F := D.frame
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl F.two_le
  rcases σ with i | i
  · obtain ⟨v, hv, rfl, hcase⟩ := hw
    rcases hcase with hbw | rfl
    · left
      rcases D.branch hN hBin hLevel _ hd with ⟨j, hj⟩ | ⟨j, hj⟩
      · have hvl := eq_of_toV_leaf_eq hN hj
        subst hvl
        have hij : i = j := by
          by_contra hne
          exact F.distinct _ (D.y_mem i) _ (D.y_mem j) (fun he => hne (D.y_inj he)) hbw
        subst hij
        exact hj
      · exfalso
        have hvb := eq_of_toV_blob_eq hN hLevel F hBin (D.att j).1 hj
        exact not_sameBlob_of_blockWalk (hx' _) hbw (hvb ▸ (D.att j).1)
    · exact Or.inr rfl
  · obtain ⟨v, hv, rfl, hcase⟩ := hw
    rcases hcase with rfl | rfl | hvP
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (D.degree_of_interior hN hBin hLevel hvP hv) hd

/-- **`Q̃` is the 4-cycle on the four taxa in their order around the cycle.** -/
theorem CycleData.hasFourCycleTopology :
    HasFourCycleTopology (qTilde hN (by rw [D.frame.card]; norm_num : 2 ≤ #q)) ⟨y 0, D.y_mem 0⟩ ⟨y 1, D.y_mem 1⟩ ⟨y 2, D.y_mem 2⟩ ⟨y 3, D.y_mem 3⟩ := by
  have F := D.frame
  have hq2 : 2 ≤ #q := by rw [F.card]; norm_num
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl F.two_le
  have hd3 : ∀ i, nodeDegree (tildeGraph N q) (toV (D.kept_b hN hBin hLevel i)) ≠ 2 := fun i => by
    rw [(nodeDegree_eq_of_frame hN hBin hLevel F).2 _ (D.y_mem i) _ (D.att i) _]
    norm_num
  set T := qTilde hN hq2 with hT
  let lf : Fin 4 → {w // nodeDegree (tildeGraph N q) w ≠ 2} := fun i => T.leaf ⟨y i, D.y_mem i⟩
  let ub : Fin 4 → {w // nodeDegree (tildeGraph N q) w ≠ 2} := fun i => ⟨toV (D.kept_b hN hBin hLevel i), hd3 i⟩
  have hlf : ∀ i, (lf i).1 = toV (D.kept_leaf hN (y i) (D.y_mem i)) := fun _ => rfl
  have hub : ∀ i, (ub i).1 = toV (D.kept_b hN hBin hLevel i) := fun _ => rfl
  have hlink₁ : ∀ i, ChainLink (tildeGraph N q) (lf i).1 (ub i).1 := fun i => D.chainLink_leaf hN hBin hLevel i
  have hlink₂ : ∀ i, ChainLink (tildeGraph N q) (ub i).1 (ub (i + 1)).1 := fun i => D.chainLink_gap hN hBin hLevel i
  have hinjl : Function.Injective lf := fun i j he => by
    have h₁ : toV (D.kept_leaf hN (y i) (D.y_mem i)) = toV (D.kept_leaf hN (y j) (D.y_mem j)) := congrArg Subtype.val he
    exact D.y_inj (hN.leaf_injective (eq_of_toV_leaf_eq hN h₁))
  have hinju : Function.Injective ub := fun i j he => by
    have h₁ : toV (D.kept_b hN hBin hLevel i) = toV (D.kept_b hN hBin hLevel j) := congrArg Subtype.val he
    exact D.gaps.inj (eq_of_toV_blob_eq hN hLevel F hBin (D.att j).1 h₁)
  have hdisj : ∀ i j, lf i ≠ ub j := fun i j he => by
    have h₁ : toV (D.kept_leaf hN (y i) (D.y_mem i)) = toV (D.kept_b hN hBin hLevel j) := congrArg Subtype.val he
    have := eq_of_toV_blob_eq hN hLevel F hBin (D.att j).1 h₁
    exact hx' _ (this ▸ (D.att j).1)
  have hadj₁ : ∀ i, T.graph.Adj (lf i) (ub i) := fun i =>
    (SimpleGraph.fromRel_adj _ _ _).2 ⟨hdisj i i, Or.inl (hlink₁ i)⟩
  have hadj₂ : ∀ i, T.graph.Adj (ub i) (ub (i + 1)) := fun i => by
    refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨fun he => ?_, Or.inl (hlink₂ i)⟩
    have key : ∀ i : Fin 4, i ≠ i + 1 := by decide
    exact key i (hinju he)
  -- the edges are these
  have hcases : ∀ {p r : {w // nodeDegree (tildeGraph N q) w ≠ 2}}, T.graph.Adj p r →
      ∃ i, s(p, r) = s(lf i, ub i) ∨ s(p, r) = s(ub i, ub (i + 1)) := by
    intro p r hadj
    obtain ⟨hne, hlink⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hadj
    have hlink' : ChainLink (tildeGraph N q) p.1 r.1 ∨ ChainLink (tildeGraph N q) r.1 p.1 := hlink
    obtain ⟨σ, hp, hr⟩ : ∃ σ : Fin 4 ⊕ Fin 4, p.1 ∈ Sum.elim (clP N q h y b) (clG N q b P) σ ∧ r.1 ∈ Sum.elim (clP N q h y b) (clG N q b P) σ := by
      rcases hlink' with hl | hl
      · exact D.exists_cl_of_chainLink hN hBin hLevel hl
      · obtain ⟨σ, h₁, h₂⟩ := D.exists_cl_of_chainLink hN hBin hLevel hl
        exact ⟨σ, h₂, h₁⟩
    have hbp := D.branch_of_cl hN hBin hLevel σ hp p.2
    have hbr := D.branch_of_cl hN hBin hLevel σ hr r.2
    rcases σ with i | i
    · refine ⟨i, Or.inl ?_⟩
      have hp' : p = lf i ∨ p = ub i := hbp.imp (fun he => Subtype.ext he) (fun he => Subtype.ext he)
      have hr' : r = lf i ∨ r = ub i := hbr.imp (fun he => Subtype.ext he) (fun he => Subtype.ext he)
      rcases hp' with rfl | rfl <;> rcases hr' with rfl | rfl
      · exact absurd rfl hne
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hne
    · refine ⟨i, Or.inr ?_⟩
      have hp' : p = ub i ∨ p = ub (i + 1) := hbp.imp (fun he => Subtype.ext he) (fun he => Subtype.ext he)
      have hr' : r = ub i ∨ r = ub (i + 1) := hbr.imp (fun he => Subtype.ext he) (fun he => Subtype.ext he)
      rcases hp' with rfl | rfl <;> rcases hr' with rfl | rfl
      · exact absurd rfl hne
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hne
  refine ⟨ub 0, ub 1, ub 2, ub 3, ?_, fun v => ?_, ?_⟩
  · -- no repetition
    let g : Fin 4 ⊕ Fin 4 → {w // nodeDegree (tildeGraph N q) w ≠ 2} := Sum.elim lf ub
    have hg : Function.Injective g := by
      rintro (i | i) (j | j) he
      · exact congrArg Sum.inl (hinjl he)
      · exact absurd he (hdisj i j)
      · exact absurd he.symm (hdisj j i)
      · exact congrArg Sum.inr (hinju he)
    have hl : [T.leaf ⟨y 0, D.y_mem 0⟩, T.leaf ⟨y 1, D.y_mem 1⟩, T.leaf ⟨y 2, D.y_mem 2⟩, T.leaf ⟨y 3, D.y_mem 3⟩, ub 0, ub 1, ub 2, ub 3] =
        ([Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3] : List (Fin 4 ⊕ Fin 4)).map g := rfl
    rw [hl]
    exact List.Nodup.map hg (by decide)
  · -- every vertex is among them
    rcases D.branch hN hBin hLevel v.1 v.2 with ⟨i, hi⟩ | ⟨i, hi⟩
    · have : v = lf i := Subtype.ext hi
      rw [this]
      fin_cases i <;> simp [lf]
    · have : v = ub i := Subtype.ext hi
      rw [this]
      fin_cases i <;> simp
  · ext e
    induction e using Sym2.ind with
    | _ p r =>
      rw [SimpleGraph.mem_edgeSet]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hadj
        obtain ⟨i, hi⟩ := hcases hadj
        fin_cases i
        · rcases hi with hi | hi
          · exact Or.inl hi
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hi))))
        · rcases hi with hi | hi
          · exact Or.inr (Or.inl hi)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hi)))))
        · rcases hi with hi | hi
          · exact Or.inr (Or.inr (Or.inl hi))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hi))))))
        · rcases hi with hi | hi
          · exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hi))))))
      · have key : ∀ {p r p' r' : {w // nodeDegree (tildeGraph N q) w ≠ 2}}, s(p, r) = s(p', r') → T.graph.Adj p' r' → T.graph.Adj p r := by
          intro p r p' r' he hadj
          rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hadj
          · exact hadj.symm
        rintro (he | he | he | he | he | he | he | he)
        · exact key he (hadj₁ 0)
        · exact key he (hadj₁ 1)
        · exact key he (hadj₁ 2)
        · exact key he (hadj₁ 3)
        · exact key he (hadj₂ 0)
        · exact key he (hadj₂ 1)
        · exact key he (hadj₂ 2)
        · exact key he (hadj₂ 3)

/-! #### The order around the cycle and the quartet tree that is not displayed -/

end Literal

section Order

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {q : Finset X} {a : X} {h T : V} {k₁ k₂ : E} {pL pR : List E}

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- Before a vertex on the left side, around the cycle, is below it. -/
theorem reaches_of_before_left (hA : N.graph.IsAcyclic) {v : V} (C : BlobCycle N v h T k₁ k₂ pL pR) {u w : V}
    (hs : List.Sublist [u, w] ((pL.map N.graph.target).reverse ++ T :: pR.map N.graph.target))
    (hw : w ∈ T :: pL.map N.graph.target) : N.graph.Reaches w u := by
  have hL : (pL.map N.graph.target).reverse ++ T :: pR.map N.graph.target = (T :: pL.map N.graph.target).reverse ++ pR.map N.graph.target := by
    simp
  rw [hL, List.sublist_append_iff] at hs
  obtain ⟨l₁, l₂, he, h₁, h₂⟩ := hs
  have hnotR : w ∉ pR.map N.graph.target := by
    intro hm
    rcases List.mem_cons.1 hw with rfl | hm'
    · exact C.right.start_notMem hA hm
    · exact C.disjoint _ hm' hm
  rcases l₁ with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, l₁⟩⟩⟩
  · simp only [List.nil_append] at he
    subst he
    exact absurd (List.Sublist.subset h₂ (by simp)) hnotR
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact absurd (List.Sublist.subset h₂ (by simp)) hnotR
  · simp only [List.cons_append, List.cons.injEq, List.nil_append] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have h' : List.Sublist [w, u] (T :: pL.map N.graph.target) := by simpa using h₁.reverse
    exact IsDirPath.reaches_of_sublist C.left h'
  · simp at he

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- After a vertex on the right side, around the cycle, is below it. -/
theorem reaches_of_before_right (hA : N.graph.IsAcyclic) {v : V} (C : BlobCycle N v h T k₁ k₂ pL pR) {u w : V}
    (hs : List.Sublist [u, w] ((pL.map N.graph.target).reverse ++ T :: pR.map N.graph.target))
    (hu : u ∈ T :: pR.map N.graph.target) : N.graph.Reaches u w := by
  rw [List.sublist_append_iff] at hs
  obtain ⟨l₁, l₂, he, h₁, h₂⟩ := hs
  have hnotL : u ∉ (pL.map N.graph.target).reverse := by
    intro hm
    rw [List.mem_reverse] at hm
    rcases List.mem_cons.1 hu with rfl | hm'
    · exact C.left.start_notMem hA hm
    · exact C.disjoint _ hm hm'
  rcases l₁ with _ | ⟨x₁, l₁⟩
  · simp only [List.nil_append] at he
    subst he
    exact IsDirPath.reaches_of_sublist C.right h₂
  · simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact absurd (List.Sublist.subset h₁ (by simp)) hnotL

omit [Fintype X] in
/-- **The lowest vertex with two lineages does not make the opposite taxa a cherry.** With the lineage of `a` at the source of `k₁`: if
`w₂`, attached at `u₂`, were in its cherry with `a`, the vertex is on the side of `k₁`, so that it is above `u₁`, and `w₁` is a third
lineage. If `w₁`, attached at `u₁`, were in its cherry, without `a` and `w₂`, the vertex is on the side of `k₂`, above `u₁`, so above `u₂`. -/
theorem false_of_isCycleSide (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (F : CycleFrame N q a h h T k₁ k₂ pL pR) {f : E} {x y : X}
    (S : IsCycleSide N q a h h T k₁ f x y) {w₁ w₂ : X} (h₁q : w₁ ∈ q) (h₂q : w₂ ∈ q) (h₁a : w₁ ≠ a) (h₂a : w₂ ≠ a) {u₁ u₂ : V}
    (hu₁ : IsAttachment N h w₁ u₁) (hu₂ : IsAttachment N h w₂ u₂) (hne : u₁ ≠ u₂)
    (hL : u₂ ∈ T :: pL.map N.graph.target → N.graph.Reaches u₂ u₁) (hR : u₁ ∈ T :: pR.map N.graph.target → N.graph.Reaches u₁ u₂) :
    ¬ ((a = x ∨ a = y) ∧ (w₂ = x ∨ w₂ = y) ∧ ¬ (w₁ = x ∨ w₁ = y)) ∧ ¬ ((w₁ = x ∨ w₁ = y) ∧ ¬ (a = x ∨ a = y) ∧ ¬ (w₂ = x ∨ w₂ = y)) := by
  have C := F.cycle
  have hh₂ := F.two_le
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl hh₂
  set t := N.graph.target f with ht
  have htb : N.graph.blobSetoid h t := S.blob
  have hiff : ∀ {z : X}, z ∈ q → z ≠ a → (N.graph.Reaches t (N.leaf z) ↔ z = x ∨ z = y) := fun hz hza => by
    have := S.iff _ hz
    rwa [sidePos_of_ne hza] at this
  have hiffa : N.graph.Reaches t (N.graph.source k₁) ↔ a = x ∨ a = y := by
    have := S.iff _ F.mem
    rwa [sidePos_self] at this
  have hne₁ : u₁ ≠ h := IsAttachment.ne_of_not_below hN hBin hLevel hh₂ hu₁ (F.only _ h₁q h₁a)
  have hne₂ : u₂ ≠ h := IsAttachment.ne_of_not_below hN hBin hLevel hh₂ hu₂ (F.only _ h₂q h₂a)
  refine ⟨?_, ?_⟩
  · rintro ⟨ha, hw₂, hw₁⟩
    have hta := hiffa.2 ha
    have htu₂ : N.graph.Reaches t u₂ := IsAttachment.reaches_of_reaches hN (hx' w₂) hu₂ htb ((hiff h₂q h₂a).2 hw₂)
    rcases C.reaches_source hN hLevel hh₂ hu₂.1 hne₂ with h' | h'
    · have hm := C.mem_left_of_reaches hN hLevel hh₂ hu₂.1 h'
      have htu₁ := htu₂.trans (hL hm)
      rcases hu₁.reaches_or_top hN (hx' w₁) with h'' | ⟨htop, -⟩
      · exact hw₁ ((hiff h₁q h₁a).1 (htu₁.trans h''))
      · have h₃ : u₁ = t := eq_of_reaches_of_reaches hN.acyclic (htop t htb) htu₁
        have h₄ : u₁ = T := eq_of_reaches_of_reaches hN.acyclic (htop T C.top) (C.top_reaches u₁ hu₁.1)
        exact S.ne_top (h₃.symm.trans h₄)
    · exact F.exclusive hN hLevel htb S.ne_top hta (htu₂.trans h')
  · rintro ⟨hw₁, ha, hw₂⟩
    have htu₁ : N.graph.Reaches t u₁ := IsAttachment.reaches_of_reaches hN (hx' w₁) hu₁ htb ((hiff h₁q h₁a).2 hw₁)
    rcases C.reaches_source hN hLevel hh₂ hu₁.1 hne₁ with h' | h'
    · exact ha (hiffa.1 (htu₁.trans h'))
    · have hm := C.swap.mem_left_of_reaches hN hLevel hh₂ hu₁.1 h'
      have h₁₂' := hR hm
      rcases hu₂.reaches_or_top hN (hx' w₂) with h'' | ⟨htop, -⟩
      · exact hw₂ ((hiff h₂q h₂a).1 ((htu₁.trans h₁₂').trans h''))
      · exact hne (eq_of_reaches_of_reaches hN.acyclic h₁₂' (htop u₁ hu₁.1))

/-- **The quartet tree of the opposite pairs of the 4-cycle is not displayed by the grove**: `Q̃` "displays a 4-cycle joining taxa in
circular order `a, b, c, d`", and "the trees displayed by `Q_abcd` are `ab|cd` and `ad|bc`" (Figure 6, line 1080). -/
theorem not_groveDisplays_of_cycle (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) {y : Fin 4 → X} {b : Fin 4 → V}
    {P : Fin 4 → List (E × V)} {s : Fin 4 → E} (D : CycleData N q a h T k₁ k₂ pL pR y b P s)
    (H₁₂ : List.Sublist [b 1, b 2] ((pL.map N.graph.target).reverse ++ T :: pR.map N.graph.target))
    (H₂₃ : List.Sublist [b 2, b 3] ((pL.map N.graph.target).reverse ++ T :: pR.map N.graph.target))
    (hc : ({y 0, y 2, y 1, y 3} : Finset X).card = 4) : ¬ GroveDisplays N (quartetTree (y 0) (y 2) (y 1) (y 3) hc) := by
  have hA := hN.acyclic
  have F := D.frame
  have C := F.cycle
  obtain ⟨h₀₂, h₀₁, h₀₃, h₂₁, h₂₃, h₁₃⟩ := ne_of_card_four hc
  have hy0 : y 0 = a := D.y_zero
  have hbne : ∀ {i j : Fin 4}, i ≠ j → b i ≠ b j := fun hij he => hij (D.gaps.inj he)
  have ht : (quartetTree (y 0) (y 2) (y 1) (y 3) hc).taxa = q := by
    rw [quartetTree_taxa]
    refine eq_of_subset_of_card_le (fun z hz => ?_) (by rw [F.card, hc])
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> exact D.y_mem _
  have hcherry : ∀ {x x' : X}, x ∈ q → x' ∈ q → x ≠ x' → ∃ r : QuartetTree X, r.taxa = q ∧ ({x, x'} : Finset X) ∈ r.val := by
    intro x x' hx hx' hxx
    have hsub : ({x, x'} : Finset X) ⊆ q := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hx'
    refine ⟨quartetOfCherry q {x, x'} F.card hsub (card_pair hxx), quartetOfCherry_taxa _ _ _ _ _, ?_⟩
    rw [quartetOfCherry_val]
    simp
  -- a cherry of `y 0, y 2 | y 1, y 3`
  have hval : ∀ {x x' : X}, ({x, x'} : Finset X) ∈ (quartetTree (y 0) (y 2) (y 1) (y 3) hc).val →
      ((x = y 0 ∨ x' = y 0) ∧ (x = y 2 ∨ x' = y 2) ∧ ¬ (x = y 1 ∨ x' = y 1) ∧ ¬ (x = y 3 ∨ x' = y 3)) ∨
      ((x = y 1 ∨ x' = y 1) ∧ (x = y 3 ∨ x' = y 3) ∧ ¬ (x = y 0 ∨ x' = y 0) ∧ ¬ (x = y 2 ∨ x' = y 2)) := by
    intro x x' hm
    simp only [quartetTree_val, mem_insert, mem_singleton] at hm
    rcases hm with he | he
    · left
      have key : ∀ z, (z = x ∨ z = x') ↔ (z = y 0 ∨ z = y 2) := fun z => by
        have := Finset.ext_iff.1 he z
        simpa using this
      have k₀ := key (y 0)
      have k₁' := key (y 1)
      have k₂' := key (y 2)
      have k₃ := key (y 3)
      refine ⟨by grind, by grind, by grind, by grind⟩
    · right
      have key : ∀ z, (z = x ∨ z = x') ↔ (z = y 1 ∨ z = y 3) := fun z => by
        have := Finset.ext_iff.1 he z
        simpa using this
      have k₀ := key (y 0)
      have k₁' := key (y 1)
      have k₂' := key (y 2)
      have k₃ := key (y 3)
      refine ⟨by grind, by grind, by grind, by grind⟩
  rintro ⟨D', hD', hun, e, hse⟩
  obtain ⟨g, hg, hgt⟩ := hD'.parent h (reticulation_ne_root hN F.two_le)
  have ht₁₂ : N.graph.target k₁ = N.graph.target k₂ := C.target₁.trans C.target₂.symm
  have hne' : ∀ i : Fin 4, i ≠ 0 → y i ≠ a := fun i hi he => hi (D.y_inj (he.trans hy0.symm))
  have hq' : ∀ i, y i ∈ q := D.y_mem
  rcases C.arcs g hgt with rfl | rfl
  · -- `k₂` is deleted
    have hk₂ : k₂ ∈ D' := by
      by_contra hc'
      exact C.ne (hun _ _ hg hc' ht₁₂)
    obtain ⟨f, x, x', S⟩ := F.exists_isCycleSide hN hBin
    obtain ⟨r, hr, hrC⟩ := hcherry S.mem₁ S.mem₂ S.ne
    have hsp := F.splitOffAt hN hBin hLevel S hr hrC hk₂
    have heq := eq_of_splitOffAt hN hD' (ht.trans hr.symm) hse hsp
    rw [← heq] at hrC
    obtain ⟨h₁, h₂⟩ := false_of_isCycleSide hN hBin hLevel F S (hq' 1) (hq' 2) (hne' 1 (by decide)) (hne' 2 (by decide)) (D.att 1) (D.att 2)
      (hbne (by decide)) (fun hm => reaches_of_before_left hA C H₁₂ hm) (fun hm => reaches_of_before_right hA C H₁₂ hm)
    rcases hval hrC with ⟨h₁', h₂', h₃', -⟩ | ⟨h₁', -, h₃', h₄'⟩
    · refine h₁ ⟨?_, ?_, ?_⟩
      · rcases h₁' with h' | h'
        · exact Or.inl (hy0.symm.trans h'.symm)
        · exact Or.inr (hy0.symm.trans h'.symm)
      · rcases h₂' with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
      · rintro (h' | h')
        · exact h₃' (Or.inl h'.symm)
        · exact h₃' (Or.inr h'.symm)
    · refine h₂ ⟨?_, ?_, ?_⟩
      · rcases h₁' with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
      · rintro (h' | h')
        · exact h₃' (Or.inl (h'.symm.trans hy0.symm))
        · exact h₃' (Or.inr (h'.symm.trans hy0.symm))
      · rintro (h' | h')
        · exact h₄' (Or.inl h'.symm)
        · exact h₄' (Or.inr h'.symm)
  · -- `k₁` is deleted
    have hk₁ : k₁ ∈ D' := by
      by_contra hc'
      exact C.ne (hun _ _ hc' hg ht₁₂)
    obtain ⟨f, x, x', S⟩ := F.swap.exists_isCycleSide hN hBin
    obtain ⟨r, hr, hrC⟩ := hcherry S.mem₁ S.mem₂ S.ne
    have hsp := F.swap.splitOffAt hN hBin hLevel S hr hrC hk₁
    have heq := eq_of_splitOffAt hN hD' (ht.trans hr.symm) hse hsp
    rw [← heq] at hrC
    obtain ⟨h₁, h₂⟩ := false_of_isCycleSide hN hBin hLevel F.swap S (hq' 3) (hq' 2) (hne' 3 (by decide)) (hne' 2 (by decide)) (D.att 3) (D.att 2)
      (hbne (by decide)) (fun hm => reaches_of_before_right hA C H₂₃ hm) (fun hm => reaches_of_before_left hA C H₂₃ hm)
    rcases hval hrC with ⟨h₁', h₂', -, h₄'⟩ | ⟨-, h₂', h₃', h₄'⟩
    · refine h₁ ⟨?_, ?_, ?_⟩
      · rcases h₁' with h' | h'
        · exact Or.inl (hy0.symm.trans h'.symm)
        · exact Or.inr (hy0.symm.trans h'.symm)
      · rcases h₂' with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
      · rintro (h' | h')
        · exact h₄' (Or.inl h'.symm)
        · exact h₄' (Or.inr h'.symm)
    · refine h₂ ⟨?_, ?_, ?_⟩
      · rcases h₂' with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
      · rintro (h' | h')
        · exact h₃' (Or.inl (h'.symm.trans hy0.symm))
        · exact h₃' (Or.inr (h'.symm.trans hy0.symm))
      · rintro (h' | h')
        · exact h₄' (Or.inl h'.symm)
        · exact h₄' (Or.inr h'.symm)

/-- **On a set of four taxa with no cut-edge split, the data of the 4-cycle.** -/
theorem exists_cycleData (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4) (hnt : ¬ IsTreelike N q) :
    ∃ (a : X) (h T : V) (k₁ k₂ : E) (pL pR : List E) (y : Fin 4 → X) (b : Fin 4 → V) (P : Fin 4 → List (E × V)) (s : Fin 4 → E),
      CycleData N q a h T k₁ k₂ pL pR y b P s ∧
      List.Sublist [b 1, b 2] ((pL.map N.graph.target).reverse ++ T :: pR.map N.graph.target) ∧
      List.Sublist [b 2, b 3] ((pL.map N.graph.target).reverse ++ T :: pR.map N.graph.target) := by
  obtain ⟨v, h, hh, hh₂, hdist, a, ⟨ha, hah⟩, hu⟩ := exists_cycle_of_not_isTreelike hN hBin hLevel hq hnt
  have hmono : ∀ {α β : V}, BlockWalk N h α β → BlockWalk N v α β := by
    intro α β hw
    refine Relation.ReflTransGen.mono ?_ _ _ hw
    rintro c d ⟨h₁, h₂, e, he⟩
    exact ⟨fun hc => h₁ (sameBlob_trans (sameBlob_symm hh) hc), fun hc => h₂ (sameBlob_trans (sameBlob_symm hh) hc), e, he⟩
  obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel (v := h) .refl hh₂
  have F : CycleFrame N q a h h T k₁ k₂ pL pR :=
    ⟨hq, hh₂, fun x hx y hy hxy hw => hdist x hx y hy hxy (hmono hw), ha, hah, fun z hz hza hr => hza (hu z ⟨hz, hr⟩), C⟩
  obtain ⟨y, b, P, s, h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := exists_cycleGaps hN hBin hLevel F
  exact ⟨a, h, T, k₁, k₂, pL, pR, y, b, P, s, ⟨F, h₀, h₁, h₂, h₃, h₄, h₅⟩, h₆, h₇⟩

end Order


end External.AllmanBanosRhodes2019.Quartet
