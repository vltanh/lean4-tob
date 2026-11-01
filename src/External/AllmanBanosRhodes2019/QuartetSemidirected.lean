module

public import AllmanEtAl2023.Definitions
public import External.AllmanBanosRhodes2019.Quartet

/-!
# Definition 5 on `N⁻` itself

Definition 4 obtains `N⁻` by "deleting all edges and nodes above `LSA(X)`", "undirecting all tree edges", and "suppressing `LSA(X)`". The
object with the suppression carried out is `AllmanEtAl2023.semidirected`, the same definition in Allman et al. 2023. `Quartet.lean` reads
Definition 5 on `N` itself, with `LSA(X)` kept as a vertex. This module reads it on that object, and proves that they agree.

* `IsSPath`, `IsSSimpleTrek`, `sTrekEdges`: Definition 5, step 1, on any `SemidirectedNetwork`: "keeping only the edges in simple treks".
  `sKeptDegree`: the degrees that step 2, "suppressing all degree two nodes", reads.
* `mem_sTrekEdges_iff`: an edge of `N⁻` is kept exactly when the arc of `N` it comes from is, the edge merging the two arcs at `LSA(X)` included.
* `mem_sTrekEdges_merged_iff`: that edge is kept exactly when the arc it replaces is, so the two arcs at `LSA(X)` are kept together.
* `image_sTrekEdges`: the kept edges of `N⁻` are the kept arcs of `N` other than the arc it replaces.
* `sKeptDegree_eq`: a vertex of `N⁻` has the same degree in both graphs of kept edges, so step 2 suppresses the same vertices. The one vertex of
  `N` that is not in `N⁻` is `LSA(X)`, and step 2 suppresses it in any case (`keptDegree_lsa_le`, `mem_sTrekEdges_merged_iff`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open TOBQMC TOBQMC.Level1
open AllmanEtAl2023
open scoped Classical

namespace External.AllmanBanosRhodes2019.Quartet

variable {V E X : Type*}

/-! ### Definition 5 on a semidirected network -/

section Defs

variable {V' E' : Type*} (S : SemidirectedNetwork V' E' X)

/-- One step of a semidirected path on the edge `e`: along it, or against it if it is undirected. -/
def SStep (e : E') (u w : V') : Prop :=
  (S.graph.source e = u ∧ S.graph.target e = w) ∨ (¬ S.IsDirected e ∧ S.graph.target e = u ∧ S.graph.source e = w)

/-- A semidirected walk, as its steps. -/
def IsSWalk : V' → List (E' × V') → V' → Prop
  | u, [], w => u = w
  | u, t :: l, w => SStep S t.1 u t.2 ∧ IsSWalk t.2 l w

/-- A semidirected path: a semidirected walk with distinct vertices. -/
structure IsSPath (u : V') (l : List (E' × V')) (w : V') : Prop where
  walk : IsSWalk S u l w
  nodup : (u :: l.map Prod.snd).Nodup

/-- A simple trek between `a` and `b`: semidirected paths from `v` to `a` and from `v` to `b` that "intersect only at `v`" (line 271). -/
structure IsSSimpleTrek (a b v : V') (l₁ l₂ : List (E' × V')) : Prop where
  left : IsSPath S v l₁ a
  right : IsSPath S v l₂ b
  disjoint : ∀ z ∈ l₁.map Prod.snd, z ∉ l₂.map Prod.snd

/-- **Definition 5, step 1** (`nanuq:definition5`), on a semidirected network: the edges in simple treks between pairs of elements of `q`. -/
def sTrekEdges (q : Finset X) : Set E' :=
  {e | ∃ x ∈ q, ∃ y ∈ q, x ≠ y ∧ ∃ v l₁ l₂, IsSSimpleTrek S (S.leaf x) (S.leaf y) v l₁ l₂ ∧
    (e ∈ l₁.map Prod.fst ∨ e ∈ l₂.map Prod.fst)}

/-- The degree of a vertex in the graph of the kept edges of a semidirected network. -/
def sKeptDegree (q : Finset X) (u : V') : ℕ :=
  {e | e ∈ sTrekEdges S q ∧ S.graph.target e = u}.ncard + {e | e ∈ sTrekEdges S q ∧ S.graph.source e = u}.ncard

variable {S}

/-- The ends of the edges of a walk are among its vertices. -/
theorem IsSWalk.ends_mem {u w : V'} {l : List (E' × V')} (h : IsSWalk S u l w) {f : E'} (hf : f ∈ l.map Prod.fst) :
    S.graph.source f ∈ u :: l.map Prod.snd ∧ S.graph.target f ∈ u :: l.map Prod.snd := by
  induction l generalizing u with
  | nil => simp at hf
  | cons t l ih =>
    simp only [List.map_cons, List.mem_cons] at hf ⊢
    rcases hf with rfl | hf
    · rcases h.1 with ⟨h₁, h₂⟩ | ⟨-, h₁, h₂⟩
      · exact ⟨Or.inl h₁, Or.inr (Or.inl h₂)⟩
      · exact ⟨Or.inr (Or.inl h₂), Or.inl h₁⟩
    · obtain ⟨h₁, h₂⟩ := ih h.2 hf
      exact ⟨Or.inr (List.mem_cons.1 h₁), Or.inr (List.mem_cons.1 h₂)⟩

end Defs

/-! ### The edges of `N⁻` and the arcs of `N` -/

section Bridge

variable {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) (hX : Nontrivial X)
include hN hX

omit hN hX in
theorem semidirected_leaf_val (hN : IsBinaryNetwork N) (hX : Nontrivial X) (x : X) : ((semidirected hN hX).leaf x).1.1 = N.leaf x := rfl

omit hN hX in
theorem semidirected_target_val (hN : IsBinaryNetwork N) (hX : Nontrivial X) (k : SemiE hN hX) :
    ((semidirected hN hX).graph.target k).1.1 = N.graph.target k.1.1 := rfl

/-- The source of an edge of `N⁻` not at `LSA(X)`. -/
theorem semidirected_source_val_of_ne (k : SemiE hN hX) (h : N.graph.source k.1.1 ≠ lsaNode hN hX) :
    ((semidirected hN hX).graph.source k).1.1 = N.graph.source k.1.1 := by
  have h' : ¬ (lsaPlus hN hX).graph.source k.1 = (lsaPlus hN hX).root := fun he => h (congrArg Subtype.val he)
  have key : (semidirected hN hX).graph.source k = ⟨(lsaPlus hN hX).graph.source k.1, h'⟩ := dite_eq_right h'
  rw [key]
  rfl

/-- The source of the edge of `N⁻` that merges the two arcs at `LSA(X)` is the child of the other. -/
theorem semidirected_source_val_of_eq (k : SemiE hN hX) (h : N.graph.source k.1.1 = lsaNode hN hX) :
    ((semidirected hN hX).graph.source k).1.1 = N.graph.target (rootTreeArc hN hX).1 := by
  have h' : (lsaPlus hN hX).graph.source k.1 = (lsaPlus hN hX).root := Subtype.ext h
  have key : (semidirected hN hX).graph.source k =
      ⟨(lsaPlus hN hX).graph.target (rootTreeArc hN hX), AllmanEtAl2023.target_ne_root (lsaPlus_isPhylogenetic hN hX) _⟩ := dite_eq_left h'
  rw [key]
  rfl

/-- A vertex of `N⁻` is not `LSA(X)`. -/
theorem semiV_ne_lsa (v : SemiV hN hX) : v.1.1 ≠ lsaNode hN hX := fun he => v.2 (Subtype.ext he)

theorem source_rootTreeArc : N.graph.source (rootTreeArc hN hX).1 = lsaNode hN hX :=
  congrArg Subtype.val (rootTreeArc_spec hN hX).1

/-- The arcs of `𝒩⊕` are those with a source below `LSA(X)`. -/
theorem mem_belowArcs_of_reaches {f : E} (hf : N.graph.Reaches (lsaNode hN hX) (N.graph.source f)) :
    f ∈ N.belowArcs (lsaNode hN hX) Set.univ :=
  ⟨hf, mem_ancestralVertices_univ hN _⟩

/-- An arc of `𝒩⊕` is an arc of `N⁻` of Definition 4. -/
theorem isMinusArc_of_mem (f : N.belowArcs (lsaNode hN hX) Set.univ) : IsMinusArc N f.1 := by
  intro l hl
  have hP := hN.isPhylogenetic
  have : l = lsaNode hN hX := hl.unique hP (lsa_spec hP Set.univ Set.univ_nonempty)
  rw [this]
  exact f.2.1

/-- What is a tree arc in `𝒩⊕` is one in `N`. Its target is not above the LSA, so all the arcs into it are in `𝒩⊕`. -/
theorem isTreeArc_of_lsaPlus {f : N.belowArcs (lsaNode hN hX) Set.univ} (hf : (lsaPlus hN hX).IsTreeArc f) : N.IsTreeArc f.1 := by
  have hP := hN.isPhylogenetic
  have hF := hP.finite_arcs
  have hFM := (lsaPlus_isPhylogenetic hN hX).finite_arcs
  obtain ⟨g, hg⟩ := ((lsaPlus hN hX).graph.indegree_eq_one_iff _).1 hf
  refine (N.graph.indegree_eq_one_iff _).2 ⟨f.1, fun e => ⟨fun he => ?_, fun he => he ▸ rfl⟩⟩
  have hnr : ¬ N.graph.Reaches (N.graph.target e) (lsaNode hN hX) := by
    intro hr
    rw [he] at hr
    exact not_reaches_target_source hP.acyclic f.1 (hr.trans f.2.1)
  have hem : e ∈ N.belowArcs (lsaNode hN hX) Set.univ := (mem_belowArcs_univ_iff hN hX e).2 hnr
  have h₁ : (⟨e, hem⟩ : N.belowArcs (lsaNode hN hX) Set.univ) = g :=
    (hg ⟨e, hem⟩).1 (Subtype.ext he)
  have h₂ : f = g := (hg f).1 rfl
  exact congrArg Subtype.val (h₁.trans h₂.symm)

/-- Only one arc other than the chosen one leaves `LSA(X)`. -/
theorem eq_of_source_eq_lsa {f g : E} (hf : N.graph.source f = lsaNode hN hX) (hg : N.graph.source g = lsaNode hN hX)
    (hf₀ : f ≠ (rootTreeArc hN hX).1) (hg₀ : g ≠ (rootTreeArc hN hX).1) : f = g := by
  by_contra hne
  exact false_of_three_out_arcs hN.isPhylogenetic hN.isBinary hne hf₀ hg₀ hf hg (source_rootTreeArc hN hX)

/-! #### From `N⁻` to `N` -/

/-- The two ends of the merged edge are different: the chosen arc is a tree arc. -/
theorem target_ne_of_source_eq_lsa (k : SemiE hN hX) : N.graph.target k.1.1 ≠ N.graph.target (rootTreeArc hN hX).1 := by
  intro he
  have hT : N.IsTreeArc (rootTreeArc hN hX).1 := isTreeArc_of_lsaPlus hN hX (rootTreeArc_spec hN hX).2
  refine k.2 (Subtype.ext ?_)
  exact eq_of_indegree_le_one hN.isPhylogenetic (le_of_eq hT) he

/-- **A semidirected path of `N⁻` is one of `N`**, through `LSA(X)` if it uses the merged edge. -/
theorem IsSPath.lift {u w : SemiV hN hX} {l : List (SemiE hN hX × SemiV hN hX)} (h : IsSPath (semidirected hN hX) u l w) :
    ∃ L : List (E × V), IsSemiPath N u.1.1 L w.1.1 ∧
      (∀ k ∈ l.map Prod.fst, k.1.1 ∈ L.map Prod.fst) ∧
      (∀ k ∈ l.map Prod.fst, N.graph.source k.1.1 = lsaNode hN hX → (rootTreeArc hN hX).1 ∈ L.map Prod.fst) ∧
      (∀ z ∈ L.map Prod.snd, (∃ v ∈ l.map Prod.snd, z = v.1.1) ∨ (z = lsaNode hN hX ∧ ∃ k ∈ l.map Prod.fst, N.graph.source k.1.1 = lsaNode hN hX)) := by
  induction l generalizing u with
  | nil =>
    obtain rfl : u = w := h.walk
    exact ⟨[], ⟨rfl, by simp⟩, by simp, by simp, by simp⟩
  | cons t l ih =>
    obtain ⟨k, w₁⟩ := t
    obtain ⟨hstep, hwalk⟩ := h.walk
    have hnd := h.nodup
    simp only [List.map_cons] at hnd
    obtain ⟨hu, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨L, hL, harc, hmer, hvert⟩ := ih ⟨hwalk, hnd'⟩
    -- the vertex `u` is not on the rest, as a vertex of `N`
    have huL : u.1.1 ∉ L.map Prod.snd := by
      intro hm
      rcases hvert _ hm with ⟨v, hv, he⟩ | ⟨he, -⟩
      · have huv : u = v := Subtype.ext (Subtype.ext he)
        exact hu (List.mem_cons_of_mem _ (huv ▸ hv))
      · exact semiV_ne_lsa hN hX u he
    have hkm : k.1.1 ∈ (k :: l.map Prod.fst).map (fun k : SemiE hN hX => k.1.1) := by simp
    have htv : (w₁ : SemiV hN hX).1.1 ≠ lsaNode hN hX := semiV_ne_lsa hN hX w₁
    by_cases hks : N.graph.source k.1.1 = lsaNode hN hX
    · -- the merged edge
      have hnomer : ∀ k' ∈ l.map Prod.fst, N.graph.source k'.1.1 ≠ lsaNode hN hX := by
        intro k' hk' hs'
        have hkk : k' = k := Subtype.ext (Subtype.ext (eq_of_source_eq_lsa hN hX hs' hks
          (fun he => k'.2 (Subtype.ext he)) (fun he => k.2 (Subtype.ext he))))
        obtain ⟨h₁, h₂⟩ := IsSWalk.ends_mem hwalk (hkk ▸ hk')
        rcases hstep with ⟨h₃, -⟩ | ⟨-, h₃, -⟩
        · exact hu (h₃ ▸ h₁)
        · exact hu (h₃ ▸ h₂)
      have hlsaL : lsaNode hN hX ∉ L.map Prod.snd := by
        intro hm
        rcases hvert _ hm with ⟨v, -, he⟩ | ⟨-, k', hk', hs'⟩
        · exact semiV_ne_lsa hN hX v he.symm
        · exact hnomer k' hk' hs'
      have hmin₀ := isMinusArc_of_mem hN hX (rootTreeArc hN hX)
      have hmin := isMinusArc_of_mem hN hX k.1
      have hT₀ : N.IsTreeArc (rootTreeArc hN hX).1 := isTreeArc_of_lsaPlus hN hX (rootTreeArc_spec hN hX).2
      have hs₀ := source_rootTreeArc hN hX
      have hstep' : (N.graph.target (rootTreeArc hN hX).1 = u.1.1 ∧ N.graph.target k.1.1 = w₁.1.1) ∨
          (N.IsTreeArc k.1.1 ∧ N.graph.target k.1.1 = u.1.1 ∧ N.graph.target (rootTreeArc hN hX).1 = w₁.1.1) := by
        rcases hstep with ⟨h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
        · left
          refine ⟨?_, congrArg (fun v : SemiV hN hX => v.1.1) h₂⟩
          rw [← semidirected_source_val_of_eq hN hX k hks, h₁]
        · right
          refine ⟨?_, congrArg (fun v : SemiV hN hX => v.1.1) h₁, ?_⟩
          · refine isTreeArc_of_lsaPlus hN hX ?_
            have hge := (lsaPlus_isPhylogenetic hN hX).nonroot_indegree _ (AllmanEtAl2023.target_ne_root (lsaPlus_isPhylogenetic hN hX) k.1)
            have hnh : ¬ 2 ≤ (lsaPlus hN hX).graph.indegree ((lsaPlus hN hX).graph.target k.1) := h₀
            unfold RootedNetwork.IsTreeArc
            omega
          · rw [← semidirected_source_val_of_eq hN hX k hks, h₂]
      rcases hstep' with ⟨h₁, h₂⟩ | ⟨hT, h₁, h₂⟩
      · refine ⟨((rootTreeArc hN hX).1, lsaNode hN hX) :: (k.1.1, w₁.1.1) :: L, ⟨⟨⟨hmin₀, Or.inr ⟨hT₀, h₁, hs₀⟩⟩, ⟨hmin, Or.inl ⟨hks, h₂⟩⟩, hL.walk⟩, ?_⟩, ?_, ?_, ?_⟩
        · have hnl : (w₁.1.1 :: L.map Prod.snd).Nodup := hL.nodup
          simp only [List.map_cons]
          refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, hnl⟩⟩
          · simp only [List.mem_cons, not_or]
            refine ⟨semiV_ne_lsa hN hX u, ?_, huL⟩
            intro he
            exact hu (List.mem_cons.2 (Or.inl (Subtype.ext (Subtype.ext he))))
          · simp only [List.mem_cons, not_or]
            exact ⟨htv.symm, hlsaL⟩
        · intro k' hk'
          simp only [List.map_cons, List.mem_cons] at hk' ⊢
          rcases hk' with rfl | hk'
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (harc k' hk'))
        · intro _ _ _
          simp
        · intro z hz
          simp only [List.map_cons, List.mem_cons] at hz
          rcases hz with rfl | rfl | hz
          · exact Or.inr ⟨rfl, k, by simp, hks⟩
          · exact Or.inl ⟨w₁, by simp, rfl⟩
          · rcases hvert z hz with ⟨v, hv, he⟩ | ⟨he, k', hk', hs'⟩
            · exact Or.inl ⟨v, by simp [hv], he⟩
            · exact Or.inr ⟨he, k', by simp [hk'], hs'⟩
      · refine ⟨(k.1.1, lsaNode hN hX) :: ((rootTreeArc hN hX).1, w₁.1.1) :: L, ⟨⟨⟨hmin, Or.inr ⟨hT, h₁, hks⟩⟩, ⟨hmin₀, Or.inl ⟨hs₀, h₂⟩⟩, hL.walk⟩, ?_⟩, ?_, ?_, ?_⟩
        · have hnl : (w₁.1.1 :: L.map Prod.snd).Nodup := hL.nodup
          simp only [List.map_cons]
          refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, hnl⟩⟩
          · simp only [List.mem_cons, not_or]
            refine ⟨semiV_ne_lsa hN hX u, ?_, huL⟩
            intro he
            exact hu (List.mem_cons.2 (Or.inl (Subtype.ext (Subtype.ext he))))
          · simp only [List.mem_cons, not_or]
            exact ⟨htv.symm, hlsaL⟩
        · intro k' hk'
          simp only [List.map_cons, List.mem_cons] at hk' ⊢
          rcases hk' with rfl | hk'
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (harc k' hk'))
        · intro _ _ _
          simp
        · intro z hz
          simp only [List.map_cons, List.mem_cons] at hz
          rcases hz with rfl | rfl | hz
          · exact Or.inr ⟨rfl, k, by simp, hks⟩
          · exact Or.inl ⟨w₁, by simp, rfl⟩
          · rcases hvert z hz with ⟨v, hv, he⟩ | ⟨he, k', hk', hs'⟩
            · exact Or.inl ⟨v, by simp [hv], he⟩
            · exact Or.inr ⟨he, k', by simp [hk'], hs'⟩
    · -- an edge of `N`
      have hmin := isMinusArc_of_mem hN hX k.1
      have hsv := semidirected_source_val_of_ne hN hX k hks
      have hstep' : SemiStep N k.1.1 u.1.1 w₁.1.1 := by
        refine ⟨hmin, ?_⟩
        rcases hstep with ⟨h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
        · refine Or.inl ⟨?_, congrArg (fun v : SemiV hN hX => v.1.1) h₂⟩
          rw [← hsv, h₁]
        · refine Or.inr ⟨?_, congrArg (fun v : SemiV hN hX => v.1.1) h₁, ?_⟩
          · refine isTreeArc_of_lsaPlus hN hX ?_
            have hge := (lsaPlus_isPhylogenetic hN hX).nonroot_indegree _ (AllmanEtAl2023.target_ne_root (lsaPlus_isPhylogenetic hN hX) k.1)
            have hnh : ¬ 2 ≤ (lsaPlus hN hX).graph.indegree ((lsaPlus hN hX).graph.target k.1) := h₀
            unfold RootedNetwork.IsTreeArc
            omega
          · rw [← hsv, h₂]
      refine ⟨(k.1.1, w₁.1.1) :: L, ⟨⟨hstep', hL.walk⟩, ?_⟩, ?_, ?_, ?_⟩
      · have hnl : (w₁.1.1 :: L.map Prod.snd).Nodup := hL.nodup
        simp only [List.map_cons]
        refine List.nodup_cons.2 ⟨?_, hnl⟩
        simp only [List.mem_cons, not_or]
        refine ⟨fun he => ?_, huL⟩
        exact hu (List.mem_cons.2 (Or.inl (Subtype.ext (Subtype.ext he))))
      · intro k' hk'
        simp only [List.map_cons, List.mem_cons] at hk' ⊢
        rcases hk' with rfl | hk'
        · exact Or.inl rfl
        · exact Or.inr (harc k' hk')
      · intro k' hk' hs'
        simp only [List.map_cons, List.mem_cons] at hk' ⊢
        rcases hk' with rfl | hk'
        · exact absurd hs' hks
        · exact Or.inr (hmer k' hk' hs')
      · intro z hz
        simp only [List.map_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact Or.inl ⟨w₁, by simp, rfl⟩
        · rcases hvert z hz with ⟨v, hv, he⟩ | ⟨he, k', hk', hs'⟩
          · exact Or.inl ⟨v, by simp [hv], he⟩
          · exact Or.inr ⟨he, k', by simp [hk'], hs'⟩

/-- **A simple trek of `N⁻` is one of `N`.** The two paths do not both use the merged edge, which has two different ends. -/
theorem IsSSimpleTrek.lift {a b v : SemiV hN hX} {l₁ l₂ : List (SemiE hN hX × SemiV hN hX)}
    (h : IsSSimpleTrek (semidirected hN hX) a b v l₁ l₂) :
    ∃ L₁ L₂ : List (E × V), IsSimpleTrek N a.1.1 b.1.1 v.1.1 L₁ L₂ ∧
      (∀ k, k ∈ l₁.map Prod.fst ∨ k ∈ l₂.map Prod.fst → k.1.1 ∈ L₁.map Prod.fst ∨ k.1.1 ∈ L₂.map Prod.fst) ∧
      (∀ k, k ∈ l₁.map Prod.fst ∨ k ∈ l₂.map Prod.fst → N.graph.source k.1.1 = lsaNode hN hX →
        (rootTreeArc hN hX).1 ∈ L₁.map Prod.fst ∨ (rootTreeArc hN hX).1 ∈ L₂.map Prod.fst) := by
  obtain ⟨L₁, hL₁, ha₁, hm₁, hv₁⟩ := IsSPath.lift hN hX h.left
  obtain ⟨L₂, hL₂, ha₂, hm₂, hv₂⟩ := IsSPath.lift hN hX h.right
  refine ⟨L₁, L₂, ⟨hL₁, hL₂, fun z hz hz' => ?_⟩, ?_, ?_⟩
  · rcases hv₁ z hz with ⟨w₁, hw₁, he₁⟩ | ⟨he₁, k₁, hk₁, hs₁⟩ <;> rcases hv₂ z hz' with ⟨w₂, hw₂, he₂⟩ | ⟨he₂, k₂, hk₂, hs₂⟩
    · have hww : w₁ = w₂ := Subtype.ext (Subtype.ext (he₁.symm.trans he₂))
      exact h.disjoint w₁ hw₁ (hww ▸ hw₂)
    · exact semiV_ne_lsa hN hX w₁ (he₁.symm.trans he₂)
    · exact semiV_ne_lsa hN hX w₂ (he₂.symm.trans he₁)
    · have hkk : k₂ = k₁ := Subtype.ext (Subtype.ext (eq_of_source_eq_lsa hN hX hs₂ hs₁
        (fun he => k₂.2 (Subtype.ext he)) (fun he => k₁.2 (Subtype.ext he))))
      subst hkk
      obtain ⟨hs₁', ht₁'⟩ := IsSWalk.ends_mem h.left.walk hk₁
      obtain ⟨hs₂', ht₂'⟩ := IsSWalk.ends_mem h.right.walk hk₂
      have hne : (semidirected hN hX).graph.source k₂ ≠ (semidirected hN hX).graph.target k₂ := by
        intro he
        have hval := congrArg (fun v : SemiV hN hX => v.1.1) he
        simp only [semidirected_source_val_of_eq hN hX k₂ hs₂, semidirected_target_val] at hval
        exact target_ne_of_source_eq_lsa hN hX k₂ hval.symm
      by_cases hsv : (semidirected hN hX).graph.source k₂ = v
      · have htv : (semidirected hN hX).graph.target k₂ ≠ v := fun he => hne (hsv.trans he.symm)
        exact h.disjoint _ ((List.mem_cons.1 ht₁').resolve_left htv) ((List.mem_cons.1 ht₂').resolve_left htv)
      · exact h.disjoint _ ((List.mem_cons.1 hs₁').resolve_left hsv) ((List.mem_cons.1 hs₂').resolve_left hsv)
  · rintro k (hk | hk)
    · exact Or.inl (ha₁ k hk)
    · exact Or.inr (ha₂ k hk)
  · rintro k (hk | hk) hs
    · exact Or.inl (hm₁ k hk hs)
    · exact Or.inr (hm₂ k hk hs)

/-! #### From `N` to `N⁻` -/

/-- A directed path below `LSA(X)` and off it is a semidirected path of `N⁻`. -/
theorem exists_sWalk_of_isDirPath {a b : V} {p : List E} (hp : N.IsDirPath a p b)
    (hsrc : ∀ f ∈ p, N.graph.source f ≠ lsaNode hN hX) (hmem : ∀ f ∈ p, N.graph.Reaches (lsaNode hN hX) (N.graph.source f))
    (a' b' : SemiV hN hX) (ha : a'.1.1 = a) (hb : b'.1.1 = b) :
    ∃ l' : List (SemiE hN hX × SemiV hN hX), IsSWalk (semidirected hN hX) a' l' b' ∧
      l'.map (fun t => t.1.1.1) = p ∧ l'.map (fun t => t.2.1.1) = p.map N.graph.target := by
  induction p generalizing a a' with
  | nil =>
    obtain rfl : a = b := hp
    exact ⟨[], Subtype.ext (Subtype.ext (ha.trans hb.symm)), rfl, rfl⟩
  | cons f p ih =>
    obtain ⟨hfs, hp⟩ := hp
    have hfm : f ∈ N.belowArcs (lsaNode hN hX) Set.univ := mem_belowArcs_of_reaches hN hX (hmem f (by simp))
    have hfne : f ≠ (rootTreeArc hN hX).1 := fun he => hsrc f (by simp) (he ▸ source_rootTreeArc hN hX)
    let k : SemiE hN hX := ⟨⟨f, hfm⟩, fun he => hfne (congrArg Subtype.val he)⟩
    have hks : (semidirected hN hX).graph.source k = a' := by
      refine Subtype.ext (Subtype.ext ?_)
      rw [semidirected_source_val_of_ne hN hX k (hsrc f (by simp)), ha]
      exact hfs
    obtain ⟨l', hw, h₁, h₂⟩ := ih hp (fun g hg => hsrc g (by simp [hg])) (fun g hg => hmem g (by simp [hg]))
      ((semidirected hN hX).graph.target k) rfl
    refine ⟨(k, (semidirected hN hX).graph.target k) :: l', ⟨Or.inl ⟨hks, rfl⟩, hw⟩, ?_, ?_⟩
    · simp only [List.map_cons, h₁]
      rfl
    · simp only [List.map_cons, h₂]
      rfl

/-- The vertices of a walk given by a directed path have no repetition. -/
theorem nodup_of_map_val {a' : SemiV hN hX} {l' : List (SemiE hN hX × SemiV hN hX)} {a : V} {p : List E} (ha : a'.1.1 = a)
    (hmap : l'.map (fun t => t.2.1.1) = p.map N.graph.target) (hnd : (a :: p.map N.graph.target).Nodup) :
    (a' :: l'.map Prod.snd).Nodup := by
  refine List.Nodup.of_map (fun v : SemiV hN hX => v.1.1) ?_
  simp only [List.map_cons, List.map_map]
  rw [ha]
  have : (((fun v : SemiV hN hX => v.1.1) ∘ Prod.snd) : SemiE hN hX × SemiV hN hX → V) = fun t => t.2.1.1 := rfl
  rw [this, hmap]
  exact hnd

/-- The arc of `N⁻` above an arc of a list given by a directed path is in the list of the walk. -/
theorem mem_map_fst_of_mem {l' : List (SemiE hN hX × SemiV hN hX)} {p : List E} (hmap : l'.map (fun t => t.1.1.1) = p) {k : SemiE hN hX}
    (hk : k.1.1 ∈ p) : k ∈ l'.map Prod.fst := by
  rw [← hmap] at hk
  obtain ⟨t, ht, he⟩ := List.mem_map.1 hk
  have : t.1 = k := Subtype.ext (Subtype.ext he)
  exact this ▸ List.mem_map_of_mem ht

/-- A wedge path through `LSA(X)`, starting with the chosen arc. The other arc is the merged edge, going out of the child of the chosen one. -/
theorem exists_sTrek_of_first {x y : X} {p r : List E} {g : E}
    (hw : N.IsWedgePath (N.leaf x) (N.leaf y) (lsaNode hN hX) ((rootTreeArc hN hX).1 :: p) (g :: r)) (hg : g ≠ (rootTreeArc hN hX).1) :
    ∃ v l₁ l₂, IsSSimpleTrek (semidirected hN hX) ((semidirected hN hX).leaf x) ((semidirected hN hX).leaf y) v l₁ l₂ ∧
      ∀ k : SemiE hN hX, (k.1.1 ∈ (rootTreeArc hN hX).1 :: p ∨ k.1.1 ∈ g :: r) → k ∈ l₁.map Prod.fst ∨ k ∈ l₂.map Prod.fst := by
  have hP := hN.isPhylogenetic
  have hA := hP.acyclic
  obtain ⟨hs₀, hp⟩ := hw.left
  obtain ⟨hgs, hr⟩ := hw.right
  have hl₀ : N.graph.Reaches (lsaNode hN hX) (N.graph.target (rootTreeArc hN hX).1) := .single ⟨_, hs₀, rfl⟩
  have hlg : N.graph.Reaches (lsaNode hN hX) (N.graph.target g) := .single ⟨_, hgs, rfl⟩
  have hgm : g ∈ N.belowArcs (lsaNode hN hX) Set.univ := mem_belowArcs_of_reaches hN hX (hgs ▸ .refl)
  let k : SemiE hN hX := ⟨⟨g, hgm⟩, fun he => hg (congrArg Subtype.val he)⟩
  set a' := (semidirected hN hX).graph.source k with ha'
  have haval : a'.1.1 = N.graph.target (rootTreeArc hN hX).1 := semidirected_source_val_of_eq hN hX k hgs
  have hoff : ∀ {d : V} {q : List E} {e : E}, N.IsDirPath (N.graph.target e) q d → N.graph.source e = lsaNode hN hX →
      ∀ f ∈ q, N.graph.source f ≠ lsaNode hN hX ∧ N.graph.Reaches (lsaNode hN hX) (N.graph.source f) := by
    intro d q e hq hes f hf
    have hre := (hq.reaches_of_mem hf).1
    refine ⟨fun he => not_reaches_source hP e (by rw [hes, ← he]; exact hre), ?_⟩
    exact (Relation.ReflTransGen.single ⟨e, hes, rfl⟩).trans hre
  obtain ⟨l₁, hw₁, hm₁, hv₁⟩ := exists_sWalk_of_isDirPath hN hX hp (fun f hf => (hoff hp hs₀ f hf).1)
    (fun f hf => (hoff hp hs₀ f hf).2) a' ((semidirected hN hX).leaf x) haval rfl
  obtain ⟨l₂, hw₂, hm₂, hv₂⟩ := exists_sWalk_of_isDirPath hN hX hr (fun f hf => (hoff hr hgs f hf).1)
    (fun f hf => (hoff hr hgs f hf).2) ((semidirected hN hX).graph.target k) ((semidirected hN hX).leaf y) rfl rfl
  have hnd₁ : (a' :: l₁.map Prod.snd).Nodup := by
    refine nodup_of_map_val hN hX haval hv₁ ?_
    have := hw.left.nodup hA
    simpa using this
  have hnd₂' : ((semidirected hN hX).graph.target k :: l₂.map Prod.snd).Nodup := by
    refine nodup_of_map_val hN hX (a := N.graph.target g) rfl hv₂ ?_
    have := hw.right.nodup hA
    simpa using this
  have hdisj : ∀ z, z ∈ (N.graph.target (rootTreeArc hN hX).1 :: p.map N.graph.target) → z ∈ (N.graph.target g :: r.map N.graph.target) → False := by
    intro z hz hz'
    refine hw.disjoint (z := z) ?_ ?_
    · simpa using hz
    · simpa using hz'
  have hval₂ : ∀ z ∈ l₂.map Prod.snd, z.1.1 ∈ r.map N.graph.target := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hz
    rw [← hv₂]
    exact List.mem_map_of_mem (f := fun t : SemiE hN hX × SemiV hN hX => t.2.1.1) ht
  have hval₁ : ∀ z ∈ l₁.map Prod.snd, z.1.1 ∈ p.map N.graph.target := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hz
    rw [← hv₁]
    exact List.mem_map_of_mem (f := fun t : SemiE hN hX × SemiV hN hX => t.2.1.1) ht
  refine ⟨a', l₁, (k, (semidirected hN hX).graph.target k) :: l₂, ⟨⟨hw₁, hnd₁⟩, ⟨⟨Or.inl ⟨rfl, rfl⟩, hw₂⟩, ?_⟩, fun z hz hz' => ?_⟩, fun k' hk' => ?_⟩
  · simp only [List.map_cons]
    refine List.nodup_cons.2 ⟨fun hm => ?_, hnd₂'⟩
    rcases List.mem_cons.1 hm with he | hm
    · have h₁ : N.graph.target (rootTreeArc hN hX).1 = N.graph.target g := by
        rw [← haval, he]
        rfl
      exact hdisj _ List.mem_cons_self (by rw [h₁]; exact List.mem_cons_self)
    · exact hdisj (a'.1.1) (by rw [haval]; exact List.mem_cons_self) (List.mem_cons_of_mem _ (hval₂ _ hm))
  · have hz₁ := hval₁ z hz
    simp only [List.map_cons, List.mem_cons] at hz'
    rcases hz' with he | hz₂
    · exact hdisj z.1.1 (List.mem_cons_of_mem _ hz₁) (by rw [he]; exact List.mem_cons_self)
    · exact hdisj z.1.1 (List.mem_cons_of_mem _ hz₁) (List.mem_cons_of_mem _ (hval₂ _ hz₂))
  · rcases hk' with hk' | hk'
    · rcases List.mem_cons.1 hk' with he | hk'
      · exact absurd (Subtype.ext he) k'.2
      · exact Or.inl (mem_map_fst_of_mem hN hX hm₁ hk')
    · rcases List.mem_cons.1 hk' with he | hk'
      · have : k' = k := Subtype.ext (Subtype.ext he)
        exact Or.inr (by simp [this])
      · refine Or.inr ?_
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (mem_map_fst_of_mem hN hX hm₂ hk')

/-- **A wedge path of `N` between taxa is a simple trek of `N⁻`.** Below `LSA(X)` and off it, the same arcs. Through it, its two arcs are the
merged edge, and the summit of the trek is the child of the chosen one. -/
theorem exists_sTrek_of_isWedgePath {x y : X} {t : V} {p r : List E} (hw : N.IsWedgePath (N.leaf x) (N.leaf y) t p r) :
    ∃ v l₁ l₂, IsSSimpleTrek (semidirected hN hX) ((semidirected hN hX).leaf x) ((semidirected hN hX).leaf y) v l₁ l₂ ∧
      ∀ k : SemiE hN hX, (k.1.1 ∈ p ∨ k.1.1 ∈ r) → k ∈ l₁.map Prod.fst ∨ k ∈ l₂.map Prod.fst := by
  have hP := hN.isPhylogenetic
  have hA := hP.acyclic
  have hst : N.IsStableAncestor Set.univ (lsaNode hN hX) := (lsa_spec hP Set.univ Set.univ_nonempty).1
  have hlt : N.graph.Reaches (lsaNode hN hX) t := hw.reaches_summit hP hst (Set.mem_univ x) (Set.mem_univ y)
  by_cases htl : t = lsaNode hN hX
  · -- through `LSA(X)`
    subst htl
    have hx := semiV_ne_lsa hN hX ((semidirected hN hX).leaf x)
    have hy := semiV_ne_lsa hN hX ((semidirected hN hX).leaf y)
    rcases p with _ | ⟨f, p⟩
    · exact absurd (show lsaNode hN hX = N.leaf x from hw.left).symm hx
    rcases r with _ | ⟨g, r⟩
    · exact absurd (show lsaNode hN hX = N.leaf y from hw.right).symm hy
    have hfs : N.graph.source f = lsaNode hN hX := hw.left.1
    have hgs : N.graph.source g = lsaNode hN hX := hw.right.1
    have hfg : f ≠ g := by
      rintro rfl
      exact hw.disjoint (z := N.graph.target f) (by simp) (by simp)
    have hcase : f = (rootTreeArc hN hX).1 ∨ g = (rootTreeArc hN hX).1 := by
      by_contra hno
      push Not at hno
      exact false_of_three_out_arcs hP hN.isBinary hfg hno.1 hno.2 hfs hgs (source_rootTreeArc hN hX)
    rcases hcase with rfl | rfl
    · exact exists_sTrek_of_first hN hX hw hfg.symm
    · obtain ⟨v, l₁, l₂, ht, hk⟩ := exists_sTrek_of_first hN hX (hw.symm hA) hfg
      exact ⟨v, l₂, l₁, ⟨ht.right, ht.left, fun z hz hz' => ht.disjoint z hz' hz⟩, fun k hk' => (hk k hk'.symm).symm⟩
  · -- off `LSA(X)`
    have hoff : ∀ {d : V} {q : List E}, N.IsDirPath t q d → ∀ f ∈ q, N.graph.source f ≠ lsaNode hN hX ∧ N.graph.Reaches (lsaNode hN hX) (N.graph.source f) := by
      intro d q hq f hf
      have hre := (hq.reaches_of_mem hf).1
      exact ⟨fun he => htl (eq_of_reaches_of_reaches hA (he ▸ hre) hlt), hlt.trans hre⟩
    let a' : SemiV hN hX := ⟨⟨t, hlt, mem_ancestralVertices_univ hN t⟩, fun he => htl (congrArg Subtype.val he)⟩
    obtain ⟨l₁, hw₁, hm₁, hv₁⟩ := exists_sWalk_of_isDirPath hN hX hw.left (fun f hf => (hoff hw.left f hf).1) (fun f hf => (hoff hw.left f hf).2)
      a' ((semidirected hN hX).leaf x) rfl rfl
    obtain ⟨l₂, hw₂, hm₂, hv₂⟩ := exists_sWalk_of_isDirPath hN hX hw.right (fun f hf => (hoff hw.right f hf).1) (fun f hf => (hoff hw.right f hf).2)
      a' ((semidirected hN hX).leaf y) rfl rfl
    have hndq : ∀ {d : V} {q : List E}, N.IsDirPath t q d → (t :: q.map N.graph.target).Nodup := fun hq =>
      List.nodup_cons.2 ⟨hq.start_notMem hA, hq.nodup hA⟩
    have hval : ∀ {l' : List (SemiE hN hX × SemiV hN hX)} {q : List E}, l'.map (fun t => t.2.1.1) = q.map N.graph.target →
        ∀ z ∈ l'.map Prod.snd, z.1.1 ∈ q.map N.graph.target := by
      intro l' q hq z hz
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hz
      rw [← hq]
      exact List.mem_map_of_mem (f := fun t : SemiE hN hX × SemiV hN hX => t.2.1.1) ht'
    refine ⟨a', l₁, l₂, ⟨⟨hw₁, nodup_of_map_val hN hX rfl hv₁ (hndq hw.left)⟩, ⟨hw₂, nodup_of_map_val hN hX rfl hv₂ (hndq hw.right)⟩,
      fun z hz hz' => hw.disjoint (hval hv₁ z hz) (hval hv₂ z hz')⟩, fun k hk => ?_⟩
    rcases hk with hk | hk
    · exact Or.inl (mem_map_fst_of_mem hN hX hm₁ hk)
    · exact Or.inr (mem_map_fst_of_mem hN hX hm₂ hk)

/-- **Definition 5 on `N⁻` is Definition 5 on `N`**: an edge of `AllmanEtAl2023.semidirected` is in a simple trek between taxa of `q` exactly when
the arc of `N` is, for the edge merging the two arcs at `LSA(X)` as for the others. -/
theorem mem_sTrekEdges_iff (q : Finset X) (k : SemiE hN hX) :
    k ∈ sTrekEdges (semidirected hN hX) q ↔ k.1.1 ∈ trekArcs N q := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy, v, l₁, l₂, ht, hk⟩
    obtain ⟨L₁, L₂, hT, ha, -⟩ := IsSSimpleTrek.lift hN hX ht
    exact ⟨x, hx, y, hy, hxy, v.1.1, L₁, L₂, hT, ha k hk⟩
  · intro hk
    rw [trekArcs_eq_wedgeArcs hN.isPhylogenetic] at hk
    obtain ⟨x, hx, y, hy, hxy, t, p, r, hw, hep⟩ := hk
    obtain ⟨v, l₁, l₂, ht, hk'⟩ := exists_sTrek_of_isWedgePath hN hX hw
    exact ⟨x, hx, y, hy, hxy, v, l₁, l₂, ht, hk' k hep⟩

/-- If the arc that `N⁻` replaces is kept, it is on a wedge path whose legs begin with the two arcs leaving `LSA(X)`. -/
theorem exists_wedge_of_mem_trekArcs {q : Finset X} (he : (rootTreeArc hN hX).1 ∈ trekArcs N q) :
    ∃ x ∈ q, ∃ y ∈ q, x ≠ y ∧ ∃ f p g r, N.IsWedgePath (N.leaf x) (N.leaf y) (lsaNode hN hX) (f :: p) (g :: r) ∧ f ≠ g ∧
      N.graph.source f = lsaNode hN hX ∧ N.graph.source g = lsaNode hN hX := by
  have hP := hN.isPhylogenetic
  have hA := hP.acyclic
  rw [trekArcs_eq_wedgeArcs hP] at he
  obtain ⟨x, hx, y, hy, hxy, t, p, r, hw, hep⟩ := he
  have hst : N.IsStableAncestor Set.univ (lsaNode hN hX) := (lsa_spec hP Set.univ Set.univ_nonempty).1
  have hlt : N.graph.Reaches (lsaNode hN hX) t := hw.reaches_summit hP hst (Set.mem_univ x) (Set.mem_univ y)
  have htl : N.graph.Reaches t (lsaNode hN hX) := by
    rw [← source_rootTreeArc hN hX]
    rcases hep with h' | h'
    · exact (hw.left.reaches_of_mem h').1
    · exact (hw.right.reaches_of_mem h').1
  obtain rfl : t = lsaNode hN hX := eq_of_reaches_of_reaches hA htl hlt
  have hnx := semiV_ne_lsa hN hX ((semidirected hN hX).leaf x)
  have hny := semiV_ne_lsa hN hX ((semidirected hN hX).leaf y)
  rcases p with _ | ⟨f, p⟩
  · exact absurd (show lsaNode hN hX = N.leaf x from hw.left).symm hnx
  rcases r with _ | ⟨g, r⟩
  · exact absurd (show lsaNode hN hX = N.leaf y from hw.right).symm hny
  have hfg : f ≠ g := by
    rintro rfl
    exact hw.disjoint (z := N.graph.target f) (by simp) (by simp)
  exact ⟨x, hx, y, hy, hxy, f, p, g, r, hw, hfg, hw.left.1, hw.right.1⟩

/-- **The two arcs at `LSA(X)` are kept together**, with the edge that merges them: suppressing `LSA(X)` loses nothing. -/
theorem mem_sTrekEdges_merged_iff (q : Finset X) {k : SemiE hN hX} (hk : N.graph.source k.1.1 = lsaNode hN hX) :
    k ∈ sTrekEdges (semidirected hN hX) q ↔ (rootTreeArc hN hX).1 ∈ trekArcs N q := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy, v, l₁, l₂, ht, hk'⟩
    obtain ⟨L₁, L₂, hT, -, hm⟩ := IsSSimpleTrek.lift hN hX ht
    exact ⟨x, hx, y, hy, hxy, v.1.1, L₁, L₂, hT, hm k hk' hk⟩
  · intro he
    obtain ⟨x, hx, y, hy, hxy, f, p, g, r, hw, hfg, hfs, hgs⟩ := exists_wedge_of_mem_trekArcs hN hX he
    -- `k` is one of the two arcs leaving `LSA(X)`
    have hmem : k.1.1 ∈ f :: p ∨ k.1.1 ∈ g :: r := by
      by_contra hno
      push Not at hno
      have h₁ : k.1.1 ≠ f := fun he => hno.1 (he ▸ List.mem_cons_self)
      have h₂ : k.1.1 ≠ g := fun he => hno.2 (he ▸ List.mem_cons_self)
      exact false_of_three_out_arcs hN.isPhylogenetic hN.isBinary hfg h₁.symm h₂.symm hfs hgs hk
    obtain ⟨v, l₁, l₂, ht, hk'⟩ := exists_sTrek_of_isWedgePath hN hX hw
    exact ⟨x, hx, y, hy, hxy, v, l₁, l₂, ht, hk' k hmem⟩

/-- If the arc that `N⁻` replaces is kept, there is an edge merging it with the other arc at `LSA(X)`, and that edge is kept. -/
theorem exists_merged_of_mem_trekArcs {q : Finset X} (he : (rootTreeArc hN hX).1 ∈ trekArcs N q) :
    ∃ k : SemiE hN hX, N.graph.source k.1.1 = lsaNode hN hX ∧ k ∈ sTrekEdges (semidirected hN hX) q := by
  obtain ⟨-, -, -, -, -, f, -, g, -, -, hfg, hfs, hgs⟩ := exists_wedge_of_mem_trekArcs hN hX he
  have hex : ∃ a, N.graph.source a = lsaNode hN hX ∧ a ≠ (rootTreeArc hN hX).1 := by
    by_cases hf : f = (rootTreeArc hN hX).1
    · exact ⟨g, hgs, fun hg => hfg (hf.trans hg.symm)⟩
    · exact ⟨f, hfs, hf⟩
  obtain ⟨a, has, hne⟩ := hex
  have hbelow : a ∈ N.belowArcs (lsaNode hN hX) Set.univ := mem_belowArcs_of_reaches hN hX (has ▸ Relation.ReflTransGen.refl)
  let k : SemiE hN hX := ⟨⟨a, hbelow⟩, fun h => hne (congrArg Subtype.val h)⟩
  exact ⟨k, has, (mem_sTrekEdges_merged_iff hN hX q has).2 he⟩

/-- The arcs of `N` that Definition 5 keeps are below `LSA(X)`. -/
theorem mem_belowArcs_of_mem_trekArcs {q : Finset X} {e : E} (he : e ∈ trekArcs N q) :
    e ∈ N.belowArcs (lsaNode hN hX) Set.univ := by
  have hP := hN.isPhylogenetic
  rw [trekArcs_eq_wedgeArcs hP] at he
  obtain ⟨x, -, y, -, -, t, p, r, hw, hep⟩ := he
  have hst : N.IsStableAncestor Set.univ (lsaNode hN hX) := (lsa_spec hP Set.univ Set.univ_nonempty).1
  refine mem_belowArcs_of_reaches hN hX ((hw.reaches_summit hP hst (Set.mem_univ x) (Set.mem_univ y)).trans ?_)
  rcases hep with h' | h'
  · exact (hw.left.reaches_of_mem h').1
  · exact (hw.right.reaches_of_mem h').1

/-- **The kept edges of `N⁻` are the kept arcs of `N` other than the arc it replaces.** -/
theorem image_sTrekEdges (q : Finset X) :
    (fun k : SemiE hN hX => k.1.1) '' sTrekEdges (semidirected hN hX) q = trekArcs N q \ {(rootTreeArc hN hX).1} := by
  ext e
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨(mem_sTrekEdges_iff hN hX q k).1 hk, fun he => k.2 (Subtype.ext he)⟩
  · rintro ⟨he, hne⟩
    let k : SemiE hN hX := ⟨⟨e, mem_belowArcs_of_mem_trekArcs hN hX he⟩, fun h => hne (congrArg Subtype.val h)⟩
    exact ⟨k, (mem_sTrekEdges_iff hN hX q k).2 he, rfl⟩

/-- A vertex of `N⁻` is determined by the vertex of `N` that it is. -/
theorem semiV_ext {u w : SemiV hN hX} (h : u.1.1 = w.1.1) : u = w := Subtype.ext (Subtype.ext h)

/-- The two ends of an edge of `N⁻` differ. -/
theorem semidirected_target_ne_source (k : SemiE hN hX) :
    (semidirected hN hX).graph.target k ≠ (semidirected hN hX).graph.source k := by
  intro he
  have hval : N.graph.target k.1.1 = ((semidirected hN hX).graph.source k).1.1 := congrArg (fun v : SemiV hN hX => v.1.1) he
  by_cases h : N.graph.source k.1.1 = lsaNode hN hX
  · rw [semidirected_source_val_of_eq hN hX k h] at hval
    exact target_ne_of_source_eq_lsa hN hX k hval
  · rw [semidirected_source_val_of_ne hN hX k h] at hval
    exact target_ne_source hN.isPhylogenetic k.1.1 hval

/-- **Step 2 of Definition 5 suppresses the same vertices on `N⁻` and on `N`**: a vertex of `N⁻` has the same degree in both graphs of kept edges.
At the child of the arc that `N⁻` replaces, that arc is exchanged for the edge merging it with the other arc at `LSA(X)`, and the two are kept
together. -/
theorem sKeptDegree_eq [Fintype E] (q : Finset X) (v : SemiV hN hX) :
    sKeptDegree (semidirected hN hX) q v = keptDegree N q v.1.1 := by
  have hP := hN.isPhylogenetic
  have hv := semiV_ne_lsa hN hX v
  rw [keptDegree_eq_ncard hP, sKeptDegree, ← Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _)]
  swap
  · exact Set.disjoint_left.2 fun k hk hk' => semidirected_target_ne_source hN hX k (hk.2.trans hk'.2.symm)
  refine Set.ncard_congr (fun k _ => if N.graph.source k.1.1 = lsaNode hN hX ∧ v.1.1 = N.graph.target (rootTreeArc hN hX).1
    then (rootTreeArc hN hX).1 else k.1.1) ?_ ?_ ?_
  · intro k hk
    by_cases hc : N.graph.source k.1.1 = lsaNode hN hX ∧ v.1.1 = N.graph.target (rootTreeArc hN hX).1
    · simp only [ite_eq_left hc]
      have hkept : k ∈ sTrekEdges (semidirected hN hX) q := by
        rcases hk with hk | hk
        · exact hk.1
        · exact hk.1
      exact ⟨(mem_sTrekEdges_merged_iff hN hX q hc.1).1 hkept, Or.inl hc.2.symm⟩
    · simp only [ite_eq_right hc]
      rcases hk with ⟨hkept, hk⟩ | ⟨hkept, hk⟩
      · exact ⟨(mem_sTrekEdges_iff hN hX q k).1 hkept, Or.inl (congrArg (fun w : SemiV hN hX => w.1.1) hk)⟩
      · refine ⟨(mem_sTrekEdges_iff hN hX q k).1 hkept, Or.inr ?_⟩
        have hval : ((semidirected hN hX).graph.source k).1.1 = v.1.1 := congrArg (fun w : SemiV hN hX => w.1.1) hk
        by_cases h : N.graph.source k.1.1 = lsaNode hN hX
        · rw [semidirected_source_val_of_eq hN hX k h] at hval
          exact absurd ⟨h, hval.symm⟩ hc
        · rwa [semidirected_source_val_of_ne hN hX k h] at hval
  · intro k k' _ _ hkk
    have hne₁ : ∀ a : SemiE hN hX, a.1.1 ≠ (rootTreeArc hN hX).1 := fun a he => a.2 (Subtype.ext he)
    by_cases hc : N.graph.source k.1.1 = lsaNode hN hX ∧ v.1.1 = N.graph.target (rootTreeArc hN hX).1 <;>
      by_cases hc' : N.graph.source k'.1.1 = lsaNode hN hX ∧ v.1.1 = N.graph.target (rootTreeArc hN hX).1
    · exact Subtype.ext (Subtype.ext (eq_of_source_eq_lsa hN hX hc.1 hc'.1 (hne₁ k) (hne₁ k')))
    · simp only [ite_eq_left hc, ite_eq_right hc'] at hkk
      exact absurd hkk.symm (hne₁ k')
    · simp only [ite_eq_right hc, ite_eq_left hc'] at hkk
      exact absurd hkk (hne₁ k)
    · simp only [ite_eq_right hc, ite_eq_right hc'] at hkk
      exact Subtype.ext (Subtype.ext hkk)
  · rintro e ⟨hkept, hinc⟩
    by_cases he : e = (rootTreeArc hN hX).1
    · subst he
      have ht : v.1.1 = N.graph.target (rootTreeArc hN hX).1 := by
        rcases hinc with hinc | hinc
        · exact hinc.symm
        · exact absurd (hinc.symm.trans (source_rootTreeArc hN hX)) hv
      obtain ⟨k, hks, hk⟩ := exists_merged_of_mem_trekArcs hN hX hkept
      have hs : (semidirected hN hX).graph.source k = v :=
        semiV_ext hN hX ((semidirected_source_val_of_eq hN hX k hks).trans ht.symm)
      exact ⟨k, Or.inr ⟨hk, hs⟩, ite_eq_left ⟨hks, ht⟩⟩
    · let k : SemiE hN hX := ⟨⟨e, mem_belowArcs_of_mem_trekArcs hN hX hkept⟩, fun h => he (congrArg Subtype.val h)⟩
      have hk : k ∈ sTrekEdges (semidirected hN hX) q := (mem_sTrekEdges_iff hN hX q k).2 hkept
      have hc : ¬ (N.graph.source k.1.1 = lsaNode hN hX ∧ v.1.1 = N.graph.target (rootTreeArc hN hX).1) := by
        rintro ⟨hs, ht⟩
        rcases hinc with hinc | hinc
        · exact target_ne_of_source_eq_lsa hN hX k (hinc.trans ht)
        · exact hv (hinc.symm.trans hs)
      refine ⟨k, ?_, ite_eq_right hc⟩
      rcases hinc with hinc | hinc
      · exact Or.inl ⟨hk, semiV_ext hN hX hinc⟩
      · refine Or.inr ⟨hk, semiV_ext hN hX ?_⟩
        have hs : N.graph.source k.1.1 ≠ lsaNode hN hX := fun hs => hv (hinc.symm.trans hs)
        exact (semidirected_source_val_of_ne hN hX k hs).trans hinc

end Bridge

end External.AllmanBanosRhodes2019.Quartet
