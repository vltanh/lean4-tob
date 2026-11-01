module

public import External.GusfieldEtAl2004.SameBlob
public import External.SempleSteel2003.Support

/-!
# The Perfect Phylogeny Theorem (Gusfield 1991)

See the `README.md` of this directory. The paper wasn't read, and the proofs are the standard argument, which it's known for: with
a row, or the ancestral sequence, as a base, the set of rows differing from the base at a column is disjoint from or nested with
the set of another column, when the two aren't incompatible (`comparable_of_missing`). These sets, with the singletons of rows,
are a laminar family, and its tree (`SempleSteel2003.lamGraph`) has a node per set.
-/

@[expose] public section

open scoped Classical

namespace Gusfield1991

open Gusfield2007 SempleSteel2003

section Family

variable {X κ : Type*}

/-- The sets of rows that differ from the base at a column, and the singletons of rows, on `X` and a new element for the
root. The root of the tree is then a node apart from the sets, even when a column differs from the base at all rows. -/
def rowSets (O : κ → Set X) : Set (Set (Option X)) := {A | (∃ k, A = some '' O k) ∨ ∃ x, A = {some x}}

/-- Two columns that miss a pair of states, other than the pair of the base, have their sets disjoint or nested. -/
theorem comparable_of_missing {f g : X → Bool} {p q a b : Bool} (hne : a ≠ p ∨ b ≠ q) (h : ∀ x, ¬ (f x = a ∧ g x = b)) :
    Disjoint {x | f x ≠ p} {x | g x ≠ q} ∨ {x | f x ≠ p} ⊆ {x | g x ≠ q} ∨ {x | g x ≠ q} ⊆ {x | f x ≠ p} := by
  have flip : ∀ {u v : Bool}, u ≠ v → u = !v := by decide
  by_cases ha : a = p
  · have hb : b = !q := flip (hne.resolve_left (by simpa using ha))
    subst ha hb
    refine Or.inr (Or.inr fun x hx => ?_)
    by_contra hxf
    have hxf' : f x = a := by simpa using hxf
    exact h x ⟨hxf', flip hx⟩
  · have ha' : a = !p := flip ha
    by_cases hb : b = q
    · subst ha' hb
      refine Or.inr (Or.inl fun x hx => ?_)
      by_contra hxg
      have hxg' : g x = b := by simpa using hxg
      exact h x ⟨flip hx, hxg'⟩
    · have hb' : b = !q := flip hb
      subst ha' hb'
      refine Or.inl (Set.disjoint_left.2 fun x hx hy => ?_)
      exact h x ⟨flip hx, flip hy⟩

variable {O : κ → Set X}

theorem rowSets_isLaminar (hne : ∀ k, (O k).Nonempty)
    (hO : ∀ k l, Disjoint (O k) (O l) ∨ O k ⊆ O l ∨ O l ⊆ O k) : IsLaminar (rowSets O) where
  nonempty := by
    rintro _ (⟨k, rfl⟩ | ⟨x, rfl⟩)
    · exact (hne k).image _
    · exact Set.singleton_nonempty _
  comparable := by
    rintro _ (⟨k, rfl⟩ | ⟨x, rfl⟩) _ (⟨l, rfl⟩ | ⟨y, rfl⟩)
    · rcases hO k l with h | h | h
      · exact Or.inl ((Set.disjoint_image_iff (Option.some_injective X)).2 h)
      · exact Or.inr (Or.inl (Set.image_mono h))
      · exact Or.inr (Or.inr (Set.image_mono h))
    · by_cases hy : y ∈ O k
      · refine Or.inr (Or.inr ?_)
        rw [Set.singleton_subset_iff]
        exact ⟨y, hy, rfl⟩
      · refine Or.inl (Set.disjoint_singleton_right.2 ?_)
        rintro ⟨z, hz, h⟩
        exact hy (Option.some_injective X h ▸ hz)
    · by_cases hx : x ∈ O l
      · refine Or.inr (Or.inl ?_)
        rw [Set.singleton_subset_iff]
        exact ⟨x, hx, rfl⟩
      · refine Or.inl (Set.disjoint_singleton_left.2 ?_)
        rintro ⟨z, hz, h⟩
        exact hx (Option.some_injective X h ▸ hz)
    · by_cases hxy : x = y
      · subst hxy
        exact Or.inr (Or.inl subset_rfl)
      · refine Or.inl (Set.disjoint_singleton.2 ?_)
        exact fun h => hxy (Option.some_injective X h)

theorem none_notMem_of_mem {A : Set (Option X)} (hA : A ∈ rowSets O) : none ∉ A := by
  rcases hA with ⟨k, rfl⟩ | ⟨x, rfl⟩
  · rintro ⟨z, -, h⟩
    cases h
  · exact fun h => by cases h

/-- The node of a column. -/
def colNode (O : κ → Set X) (k : κ) : LamNode (rowSets O) := ⟨some '' O k, Or.inl (Or.inl ⟨k, rfl⟩)⟩

/-- The node of a row. -/
def rowNode (O : κ → Set X) (x : X) : LamNode (rowSets O) := ⟨{some x}, Or.inl (Or.inr ⟨x, rfl⟩)⟩

theorem node_ne_root_of_none {v : LamNode (rowSets O)} (h : none ∉ v.1) : v ≠ lamRoot (rowSets O) := by
  rintro rfl
  exact h (Set.mem_univ _)

theorem colNode_ne_root (k : κ) : colNode O k ≠ lamRoot (rowSets O) :=
  node_ne_root_of_none (none_notMem_of_mem (O := O) (Or.inl ⟨k, rfl⟩))

theorem rowNode_ne_root (x : X) : rowNode O x ≠ lamRoot (rowSets O) :=
  node_ne_root_of_none (none_notMem_of_mem (O := O) (Or.inr ⟨x, rfl⟩))

theorem rowNode_le_iff {x : X} {v : LamNode (rowSets O)} : rowNode O x ≤ v ↔ some x ∈ v.1 := by
  rw [← Subtype.coe_le_coe]
  exact Set.singleton_subset_iff

theorem rowNode_le_colNode {x : X} {k : κ} : rowNode O x ≤ colNode O k ↔ x ∈ O k := by
  rw [rowNode_le_iff]
  constructor
  · rintro ⟨z, hz, h⟩
    exact Option.some_injective X h ▸ hz
  · exact fun h => ⟨x, h, rfl⟩

theorem rowNode_injective : Function.Injective (rowNode O) := fun x y h => by
  have : ({some x} : Set (Option X)) = {some y} := congrArg Subtype.val h
  exact Option.some_injective X (Set.singleton_injective this)

theorem not_lt_rowNode (hL : IsLaminar (rowSets O)) [Nonempty X] (x : X) (v : LamNode (rowSets O)) : ¬ v < rowNode O x := by
  intro hv
  obtain ⟨y, hy⟩ := hL.node_nonempty v
  have hsub : v.1 ⊆ {some x} := Subtype.coe_le_coe.2 hv.le
  have hyx : y = some x := hsub hy
  subst hyx
  exact hv.not_ge (rowNode_le_iff.2 hy)

variable [Finite X]

/-- A node with no node below it is the node of a row. -/
theorem exists_rowNode_of_no_child [Nonempty X] (hL : IsLaminar (rowSets O)) {v : LamNode (rowSets O)} (hv : ∀ c, ¬ c ⋖ v) :
    ∃ x, v = rowNode O x := by
  -- an element of `X` in `v`
  obtain ⟨x, hx⟩ : ∃ x, some x ∈ v.1 := by
    rcases v with ⟨A, hA | rfl⟩
    · obtain ⟨y, hy⟩ := hL.nonempty A hA
      cases y with
      | none => exact absurd hy (none_notMem_of_mem hA)
      | some x => exact ⟨x, hy⟩
    · obtain ⟨x⟩ := ‹Nonempty X›
      exact ⟨x, Set.mem_univ _⟩
  refine ⟨x, ?_⟩
  by_contra hne
  have hlt : rowNode O x < v := lt_of_le_of_ne (rowNode_le_iff.2 hx) (Ne.symm hne)
  obtain ⟨c, -, hc⟩ := exists_le_covBy_of_lt hlt
  exact hv c hc

end Family

section Network

variable {X : Type*} {L : Set (Set X)} [Finite X] {ι : Type*}

/-- The node just above a node. -/
noncomputable def lamParent (a : {a : LamNode L // a ≠ lamRoot L}) : LamNode L := (exists_covBy_of_ne_root a.2).choose

theorem lamParent_covBy (a : {a : LamNode L // a ≠ lamRoot L}) : a.1 ⋖ lamParent a := (exists_covBy_of_ne_root a.2).choose_spec

/-- The network of a laminar family: arcs from each node to the nodes it covers, each site on the arc above its node `g i`, and
the sequence of a node is the ancestral sequence `S` changed at the sites whose node is above it. -/
noncomputable def lamNetwork (hL : IsLaminar L) [Nonempty X] (g : ι → LamNode L) (hg : ∀ i, g i ≠ lamRoot L) (S : ι → Bool) :
    Network ι (LamNode L) {a : LamNode L // a ≠ lamRoot L} where
  src := lamParent
  tgt := Subtype.val
  root := lamRoot L
  site i := ⟨g i, hg i⟩
  label v i := if v ≤ g i then !S i else S i
  simple _ _ _ h := Subtype.ext h
  acyclic := by
    refine fun v h => ?_
    have key : ∀ {a b : LamNode L}, Relation.TransGen (fun a b => ∃ e, lamParent e = a ∧ e.1 = b) a b → b < a := by
      intro a b hab
      induction hab with
      | single h =>
        obtain ⟨e, rfl, rfl⟩ := h
        exact (lamParent_covBy e).lt
      | tail _ h ih =>
        obtain ⟨e, rfl, rfl⟩ := h
        exact (lamParent_covBy e).lt.trans ih
    exact lt_irrefl _ (key h)
  root_iff v := by
    constructor
    · intro h
      by_contra hv
      exact h ⟨v, hv⟩ rfl
    · rintro rfl e
      exact e.2
  inDegree_le_two _ _ _ h _ := Or.inl (Subtype.ext h)
  site_not_recomb _ _ h := Subtype.ext h
  label_tree := by
    rintro ⟨a, ha⟩ - i
    have hcov : a ⋖ lamParent ⟨a, ha⟩ := lamParent_covBy ⟨a, ha⟩
    dsimp only
    by_cases hga : g i = a
    · rw [ite_eq_left (Subtype.ext hga : (⟨g i, hg i⟩ : {a : LamNode L // a ≠ lamRoot L}) = ⟨a, ha⟩)]
      subst hga
      simp [hcov.lt.not_ge]
    · have hsub : (⟨g i, hg i⟩ : {a : LamNode L // a ≠ lamRoot L}) ≠ ⟨a, ha⟩ := fun h => hga (congrArg Subtype.val h)
      rw [ite_eq_right hsub]
      by_cases hag : a ≤ g i
      · have hp : lamParent ⟨a, ha⟩ ≤ g i := by
          rcases hL.le_or_le_of_le hcov.le hag with h | h
          · exact h
          · rcases h.eq_or_lt with h | h
            · exact h.ge
            · exact absurd h (hcov.2 (lt_of_le_of_ne hag (Ne.symm hga)))
        simp [hag, hp]
      · have hp : ¬ lamParent ⟨a, ha⟩ ≤ g i := fun h => hag (hcov.le.trans h)
        simp [hag, hp]
  label_recomb _ _ hne h := absurd (Subtype.ext h) hne

theorem lamNetwork_tgt_injective (hL : IsLaminar L) [Nonempty X] (g : ι → LamNode L) (hg : ∀ i, g i ≠ lamRoot L) (S : ι → Bool) :
    Function.Injective (lamNetwork hL g hg S).tgt := Subtype.val_injective

end Network

section RootedExistence

variable {ι : Type*}

/-- A network with no recombination node, with no arc or node that could be suppressed: each arc has a site or enters a leaf, a node
other than the root with an arc in and out has two arcs out, and the root isn't a leaf. This is the form in which line 156 of
Gusfield et al. 2007 can claim that the network is unique: an arc with no site, or a node with one arc in and one out, can be
added to a perfect phylogeny without changing what it derives. -/
structure IsReducedTree {ι V E : Type*} (N : Network ι V E) : Prop where
  arc_labelled : ∀ e, (∃ i, N.site i = e) ∨ N.IsLeaf (N.tgt e)
  not_chain : ∀ e f, N.tgt e = N.src f → ∃ g, N.src g = N.src f ∧ g ≠ f
  root_not_leaf : ¬ N.IsLeaf N.root

/-- **The Perfect Phylogeny Theorem, the construction.** With no two columns in conflict relative to `S`, the laminar family of the
sets of rows differing from `S` gives a network. -/
theorem exists_network_of_no_conflict (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty)
    (hC : NoConstantColumn (addRow M S)) (h : ∀ i j, ¬ Conflict S M i j) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), (∀ x, ¬ N.IsRecomb x) ∧ N.Derives M ∧ N.ancestral = S ∧ IsReducedTree N := by
  let O : ι → Set M := fun i => {r | (r : ι → Bool) i ≠ S i}
  have hne : ∀ i, (O i).Nonempty := by
    intro i
    obtain ⟨r, hr, r', hr', hrr⟩ := hC i
    have hex : ∃ s ∈ addRow M S, s i ≠ S i := by
      by_cases h₁ : r i = S i
      · exact ⟨r', hr', fun h₂ => hrr (h₁.trans h₂.symm)⟩
      · exact ⟨r, hr, h₁⟩
    obtain ⟨s, hs, hsi⟩ := hex
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact absurd rfl hsi
    · exact ⟨⟨s, hs⟩, hsi⟩
  have hO : ∀ i j, Disjoint (O i) (O j) ∨ O i ⊆ O j ∨ O j ⊆ O i := by
    intro i j
    have hcon := h i j
    unfold Conflict at hcon
    push Not at hcon
    obtain ⟨a, b, hab, hno⟩ := hcon
    exact comparable_of_missing (f := fun r : M => (r : ι → Bool) i) (g := fun r : M => (r : ι → Bool) j) hab
      fun r ⟨h₁, h₂⟩ => hno r r.2 h₁ h₂
  have hL : IsLaminar (rowSets O) := rowSets_isLaminar hne hO
  have : Nonempty M := hM.to_subtype
  have : Nonempty (Option M) := ⟨none⟩
  have : Finite M := Finite.of_fintype _
  let N₀ := lamNetwork hL (colNode O) colNode_ne_root S
  have hinj := lamNetwork_tgt_injective hL (colNode O) colNode_ne_root S
  obtain ⟨a, b, N, eV, eE, hiso⟩ := N₀.exists_fin_iso
  -- the label of the node of a row is the row
  have hlabel : ∀ r : M, N₀.label (rowNode O r) = r := by
    intro r
    funext i
    change (if rowNode O r ≤ colNode O i then !S i else S i) = (r : ι → Bool) i
    by_cases hri : (r : ι → Bool) i = S i
    · have : ¬ rowNode O r ≤ colNode O i := by
        rw [rowNode_le_colNode]
        exact fun h => h hri
      simp [this, hri]
    · have hmem : rowNode O r ≤ colNode O i := rowNode_le_colNode.2 hri
      simp only [hmem, ite_true]
      cases hr : (r : ι → Bool) i <;> cases hs : S i <;> simp_all
  have hleaf : ∀ v, N₀.IsLeaf v ↔ ∃ r : M, v = rowNode O r := by
    intro v
    constructor
    · intro hv
      refine exists_rowNode_of_no_child hL fun c hc => ?_
      have hcne : c ≠ lamRoot (rowSets O) := fun h => hc.lt.not_ge (h ▸ le_lamRoot v)
      refine hv ⟨c, hcne⟩ ?_
      exact hL.covBy_unique (lamParent_covBy ⟨c, hcne⟩) hc
    · rintro ⟨r, rfl⟩ e he
      have hcov := lamParent_covBy e
      rw [show lamParent e = rowNode O r from he] at hcov
      exact not_lt_rowNode hL r _ hcov.lt
  have hder : N₀.Derives M := by
    refine ⟨fun v hv => ?_, fun u hu v hv huv => ?_, fun r hr => ?_⟩
    · obtain ⟨r, rfl⟩ := (hleaf v).1 hv
      rw [hlabel]
      exact r.2
    · obtain ⟨r, rfl⟩ := (hleaf u).1 hu
      obtain ⟨r', rfl⟩ := (hleaf v).1 hv
      rw [hlabel, hlabel] at huv
      rw [Subtype.ext huv]
    · exact ⟨rowNode O ⟨r, hr⟩, (hleaf _).2 ⟨_, rfl⟩, hlabel ⟨r, hr⟩⟩
  have hanc : N₀.ancestral = S := by
    funext i
    change (if lamRoot (rowSets O) ≤ colNode O i then !S i else S i) = S i
    have : ¬ lamRoot (rowSets O) ≤ colNode O i := fun hle => colNode_ne_root i (le_antisymm (le_lamRoot _) hle)
    simp [this]
  -- it is reduced
  have hred : IsReducedTree N₀ := by
    refine ⟨?_, ?_, fun hroot => ?_⟩
    · rintro ⟨c, hc⟩
      rcases c with ⟨A, (⟨k, rfl⟩ | ⟨r, rfl⟩) | rfl⟩
      · exact Or.inl ⟨k, rfl⟩
      · exact Or.inr ((hleaf _).2 ⟨r, rfl⟩)
      · exact absurd rfl hc
    · rintro ⟨x, hx⟩ ⟨c, hcr⟩ hxc
      have hxc' : x = lamParent ⟨c, hcr⟩ := hxc
      have hcov : c ⋖ x := hxc' ▸ lamParent_covBy ⟨c, hcr⟩
      -- an element of `x` off `c`, in another node below `x`
      obtain ⟨y, hy, hyc⟩ : ∃ y ∈ x.1, y ∉ c.1 := by
        by_contra hall
        push Not at hall
        exact hcov.lt.not_ge (Subtype.coe_le_coe.1 hall)
      obtain ⟨r, rfl⟩ : ∃ r, y = some r := by
        cases y with
        | none =>
          exfalso
          rcases x with ⟨A, hA | rfl⟩
          · exact none_notMem_of_mem hA hy
          · exact hx rfl
        | some r => exact ⟨r, rfl⟩
      have hle : rowNode O r ≤ x := rowNode_le_iff.2 hy
      have hlt : rowNode O r < x := lt_of_le_of_ne hle fun h => not_lt_rowNode hL r c (h ▸ hcov.lt)
      obtain ⟨d, hrd, hd⟩ := exists_le_covBy_of_lt hlt
      have hdr : d ≠ lamRoot (rowSets O) := fun h => hd.lt.not_ge (h ▸ le_lamRoot x)
      refine ⟨⟨d, hdr⟩, ?_, fun h => ?_⟩
      · change lamParent ⟨d, hdr⟩ = lamParent ⟨c, hcr⟩
        rw [← hxc']
        exact hL.covBy_unique (lamParent_covBy ⟨d, hdr⟩) hd
      · have hdc : d = c := congrArg Subtype.val h
        exact hyc (hdc ▸ rowNode_le_iff.1 hrd)
    · obtain ⟨r, hr⟩ := (hleaf _).1 hroot
      exact rowNode_ne_root r hr.symm
  refine ⟨a, b, N, fun x hx => ?_, (hiso.derives M).2 hder, ?_, ?_, ?_, ?_⟩
  · have := (hiso.isRecomb (eV.symm x)).1 (by simpa using hx)
    exact Network.not_isRecomb_of_tgt_injective hinj _ this
  · rw [← hanc]
    unfold Network.ancestral
    rw [hiso.root, hiso.label]
  · intro e
    obtain ⟨e₀, rfl⟩ := eE.surjective e
    rcases hred.arc_labelled e₀ with ⟨i, rfl⟩ | hl
    · exact Or.inl ⟨i, hiso.site i⟩
    · refine Or.inr ?_
      rw [hiso.tgt, hiso.isLeaf]
      exact hl
  · intro e f hef
    obtain ⟨e₀, rfl⟩ := eE.surjective e
    obtain ⟨f₀, rfl⟩ := eE.surjective f
    rw [hiso.tgt, hiso.src] at hef
    obtain ⟨g, hg, hne⟩ := hred.not_chain e₀ f₀ (eV.injective hef)
    exact ⟨eE g, by rw [hiso.src, hiso.src, hg], fun h => hne (eE.injective h)⟩
  · intro hl
    rw [hiso.root, hiso.isLeaf] at hl
    exact hred.root_not_leaf hl

end RootedExistence

section Trees

variable {X κ : Type*} {W W' : Type*}

/-- An isomorphism carries a perfect phylogeny to a perfect phylogeny. -/
theorem isPerfectPhylogeny_map {T : SimpleGraph W} {T' : SimpleGraph W'} {φ : X → W} {A : X → κ → Bool} {edge : κ → Sym2 W}
    (h : IsPerfectPhylogeny T φ A edge) (f : T ≃g T') : IsPerfectPhylogeny T' (f ∘ φ) A fun k => (edge k).map f where
  isTree := f.isTree_iff.1 h.isTree
  label_injective := f.injective.comp h.label_injective
  mem_range_iff v := by
    obtain ⟨u, rfl⟩ := f.surjective v
    rw [ncard_neighborSet_iso f u, ← h.mem_range_iff u]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, f.injective hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  edge_mem k := by
    have := h.edge_mem k
    induction hk : edge k using Sym2.ind with
    | _ a b =>
      rw [hk] at this
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact f.map_adj_iff.2 this
  split k x y := by
    rw [h.split k x y]
    exact (reachable_deleteEdges_iso f (edge k) (φ x) (φ y)).symm

end Trees

/-- **The Perfect Phylogeny Theorem** (`ext:perfect_phylogeny`), for a matrix `A` with rows `X` and no constant column: it has a perfect phylogeny
exactly when no two columns contain all four pairs of states. -/
theorem exists_isPerfectPhylogeny_iff {X κ : Type*} [Finite X] [Nonempty X] [Finite κ] (A : X → κ → Bool)
    (hA : ∀ k, ∃ x y, A x k ≠ A y k) :
    (∃ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : X → Fin n) (edge : κ → Sym2 (Fin n)), IsPerfectPhylogeny T φ A edge) ↔
      ∀ k l, ∃ a b, ∀ x, ¬ (A x k = a ∧ A x l = b) := by
  constructor
  · rintro ⟨n, T, φ, edge, h⟩ k l
    have hT := h.isTree
    -- one side of each edge has a row
    have hrow : ∀ (m : κ) {u v : Fin n}, edge m = s(u, v) → ∃ x, (T.deleteEdges {edge m}).Reachable u (φ x) := by
      intro m u v hm
      have hadj : T.Adj u v := by
        have := h.edge_mem m
        rwa [hm] at this
      obtain ⟨x, y, hxy⟩ := hA m
      have hnr : ¬ (T.deleteEdges {edge m}).Reachable (φ x) (φ y) := fun hr => hxy ((h.split m x y).2 hr)
      rw [hm] at hnr ⊢
      rcases reachable_deleteEdges_or hT.1 u v (φ x) with h₁ | h₁
      · exact ⟨x, h₁⟩
      · rcases reachable_deleteEdges_or hT.1 u v (φ y) with h₂ | h₂
        · exact ⟨y, h₂⟩
        · exact absurd (h₁.symm.trans h₂) hnr
    induction hk : edge k using Sym2.ind with
    | _ a b =>
    induction hl : edge l using Sym2.ind with
    | _ c d =>
    have hab : T.Adj a b := by
      have := h.edge_mem k
      rwa [hk] at this
    have hcd : T.Adj c d := by
      have := h.edge_mem l
      rwa [hl] at this
    obtain ⟨u, v, t, t', hee, -, hff, -, hfar⟩ := exists_far_sides hT hab hcd
    obtain ⟨x₀, hx₀⟩ := hrow k (hk.trans hee)
    obtain ⟨x₁, hx₁⟩ := hrow l (hl.trans hff)
    refine ⟨A x₀ k, A x₁ l, fun x ⟨h₁, h₂⟩ => ?_⟩
    have h₃ := (h.split k x x₀).1 h₁
    have h₄ := (h.split l x x₁).1 h₂
    unfold SameSide at h₃ h₄
    rw [hk] at h₃ hx₀
    rw [hl] at h₄ hx₁
    exact hfar (φ x) ⟨hx₀.trans h₃.symm, hx₁.trans h₄.symm⟩
  · intro hmiss
    by_cases hX : Subsingleton X
    · -- one row: no column, a single node
      have hκ : IsEmpty κ := ⟨fun k => by
        obtain ⟨x, y, hxy⟩ := hA k
        exact hxy (by rw [Subsingleton.elim x y])⟩
      refine ⟨1, ⊥, fun _ => 0, fun k => hκ.elim k, SimpleGraph.IsTree.of_subsingleton, fun x y _ => Subsingleton.elim x y, fun v => ?_, fun k => hκ.elim k, fun k => hκ.elim k⟩
      have hv : (⊥ : SimpleGraph (Fin 1)).neighborSet v = ∅ := by
        ext w
        simp
      rw [hv, Set.ncard_empty]
      obtain ⟨x⟩ := ‹Nonempty X›
      exact ⟨fun _ => Nat.zero_le _, fun _ => ⟨x, Subsingleton.elim _ _⟩⟩
    · rw [not_subsingleton_iff_nontrivial] at hX
      obtain ⟨x₀⟩ := ‹Nonempty X›
      let O : κ → Set X := fun k => {x | A x k ≠ A x₀ k}
      have hne : ∀ k, (O k).Nonempty := by
        intro k
        obtain ⟨x, y, hxy⟩ := hA k
        by_cases h₁ : A x k = A x₀ k
        · exact ⟨y, fun h₂ => hxy (h₁.trans h₂.symm)⟩
        · exact ⟨x, h₁⟩
      have hO : ∀ k l, Disjoint (O k) (O l) ∨ O k ⊆ O l ∨ O l ⊆ O k := by
        intro k l
        obtain ⟨a, b, hab⟩ := hmiss k l
        refine comparable_of_missing (f := fun x => A x k) (g := fun x => A x l) (p := A x₀ k) (q := A x₀ l) ?_ hab
        by_contra hno
        push Not at hno
        exact hab x₀ ⟨hno.1.symm, hno.2.symm⟩
      have hL : IsLaminar (rowSets O) := rowSets_isLaminar hne hO
      have hx₀O : ∀ k, x₀ ∉ O k := fun k h => h rfl
      have hT := lamGraph_isTree hL
      have hcov : ∀ k, ∃ b, colNode O k ⋖ b := fun k => exists_covBy_of_ne_root (colNode_ne_root k)
      choose par hpar using hcov
      have hpp : IsPerfectPhylogeny (lamGraph (rowSets O)) (rowNode O) A fun k => s(colNode O k, par k) := by
        refine ⟨hT, rowNode_injective, fun v => ?_, fun k => lamGraph_adj.2 (Or.inl (hpar k)), fun k x y => ?_⟩
        · constructor
          · rintro ⟨x, rfl⟩
            -- the node of a row has one neighbour, the node above it
            obtain ⟨p, hp⟩ := exists_covBy_of_ne_root (rowNode_ne_root (O := O) x)
            have hsub : (lamGraph (rowSets O)).neighborSet (rowNode O x) ⊆ {p} := by
              intro w hw
              rcases lamGraph_adj.1 hw with h | h
              · exact hL.covBy_unique h hp
              · exact absurd h.lt (not_lt_rowNode hL x w)
            calc _ ≤ ({p} : Set _).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
              _ = 1 := Set.ncard_singleton p
          · intro hv
            by_contra hno
            -- otherwise it has a child; and a second neighbour
            have hchild : ∃ c, c ⋖ v := by
              by_contra hc
              push Not at hc
              obtain ⟨x, rfl⟩ := exists_rowNode_of_no_child hL hc
              exact hno ⟨x, rfl⟩
            obtain ⟨c, hc⟩ := hchild
            have htwo : ∃ d, (lamGraph (rowSets O)).Adj v d ∧ d ≠ c := by
              by_cases hvr : v = lamRoot (rowSets O)
              · -- two children at the root: the node of `x₀`, and a node of another row
                obtain ⟨x₁, hx₁⟩ := exists_ne x₀
                have hchildof : ∀ x, ∃ d, d ⋖ v ∧ some x ∈ d.1 := by
                  intro x
                  have hlt : rowNode O x < v := hvr ▸ lt_of_le_of_ne (le_lamRoot _) (rowNode_ne_root x)
                  obtain ⟨d, h₁, h₂⟩ := exists_le_covBy_of_lt hlt
                  exact ⟨d, h₂, rowNode_le_iff.1 h₁⟩
                obtain ⟨d₀, hd₀, hmem₀⟩ := hchildof x₀
                obtain ⟨d₁, hd₁, hmem₁⟩ := hchildof x₁
                have hd : d₀ ≠ d₁ := by
                  intro hdd
                  subst hdd
                  have hvne : d₀ ≠ lamRoot (rowSets O) := by
                    intro h'
                    exact hd₀.lt.not_ge (h' ▸ le_lamRoot v)
                  rcases d₀ with ⟨A', hA' | rfl⟩
                  · rcases hA' with ⟨k, rfl⟩ | ⟨y, rfl⟩
                    · obtain ⟨z, hz, hzx⟩ := hmem₀
                      exact hx₀O k (Option.some_injective X hzx ▸ hz)
                    · have h₁ : some x₀ = some y := hmem₀
                      have h₂ : some x₁ = some y := hmem₁
                      exact hx₁ (Option.some_injective X (h₂.trans h₁.symm))
                  · exact hvne rfl
                by_cases hdc : d₀ = c
                · exact ⟨d₁, lamGraph_adj.2 (Or.inr hd₁), fun h => hd (hdc.trans h.symm)⟩
                · exact ⟨d₀, lamGraph_adj.2 (Or.inr hd₀), hdc⟩
              · obtain ⟨p, hp⟩ := exists_covBy_of_ne_root hvr
                exact ⟨p, lamGraph_adj.2 (Or.inl hp), fun h => hp.lt.not_gt (h ▸ hc.lt)⟩
            obtain ⟨d, hd, hdc⟩ := htwo
            have htw : 1 < ((lamGraph (rowSets O)).neighborSet v).ncard :=
              (Set.one_lt_ncard (Set.toFinite _)).2 ⟨d, hd, c, lamGraph_adj.2 (Or.inr hc), hdc⟩
            omega
        · change _ ↔ ((lamGraph (rowSets O)).deleteEdges {s(colNode O k, par k)}).Reachable _ _
          rw [lam_reachable_deleteEdges_iff hL (hpar k), rowNode_le_colNode, rowNode_le_colNode]
          change _ ↔ (A x k ≠ A x₀ k ↔ A y k ≠ A x₀ k)
          cases A x k <;> cases A y k <;> cases A x₀ k <;> simp
      obtain ⟨n, T', ⟨f⟩⟩ := exists_iso_fin (lamGraph (rowSets O))
      exact ⟨n, T', f ∘ rowNode O, _, isPerfectPhylogeny_map hpp f⟩

variable {ι : Type*}

/-- The columns of `M` are compatible at a network with no recombination node: there's no blob. -/
theorem not_incompatible_of_no_recomb {a b : ℕ} (N : Network ι (Fin a) (Fin b)) (hN : ∀ x, ¬ N.IsRecomb x)
    {L : Finset (ι → Bool)} (hL : ∀ r ∈ L, ∃ v, N.label v = r) (i j : ι) : ¬ Incompatible L i j := by
  intro h
  obtain ⟨B, ⟨Q, ⟨w, x, p, q, hc, -⟩, -⟩, -⟩ := GusfieldEtAl2004.exists_isBlob_of_incompatible N hL h
  exact hN x hc.1

/-- **The Perfect Phylogeny Theorem**, rooted, in the terms of Gusfield et al. 2007, line 156: a network with no
recombination derives `M` with ancestral sequence `S` exactly when no two columns conflict relative to `S`. -/
theorem exists_network_rooted_iff (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty)
    (hC : NoConstantColumn (addRow M S)) :
    (∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), (∀ x, ¬ N.IsRecomb x) ∧ N.Derives M ∧ N.ancestral = S) ↔
      ∀ i j, ¬ Conflict S M i j := by
  constructor
  · rintro ⟨a, b, N, hN, hD, rfl⟩ i j hcon
    refine not_incompatible_of_no_recomb N hN (L := addRow M N.ancestral) (fun r hr => ?_) i j ?_
    · rcases Finset.mem_insert.1 hr with rfl | hr
      · exact ⟨N.root, rfl⟩
      · obtain ⟨v, -, rfl⟩ := hD.surjOn hr
        exact ⟨v, rfl⟩
    · intro s t
      by_cases hst : s = N.ancestral i ∧ t = N.ancestral j
      · exact ⟨N.ancestral, Finset.mem_insert_self _ _, hst.1.symm, hst.2.symm⟩
      · have : s ≠ N.ancestral i ∨ t ≠ N.ancestral j := by
          by_contra hno
          push Not at hno
          exact hst hno
        obtain ⟨r, hr, h₁, h₂⟩ := hcon s t this
        exact ⟨r, Finset.mem_insert_of_mem hr, h₁, h₂⟩
  · intro h
    obtain ⟨a, b, N, h₁, h₂, h₃, -⟩ := exists_network_of_no_conflict M S hM hC h
    exact ⟨a, b, N, h₁, h₂, h₃⟩

/-- **The Perfect Phylogeny Theorem**, in the terms of Gusfield et al. 2007, line 154: a network with no recombination
derives `M` exactly when no two columns of `M` are incompatible. -/
theorem exists_network_iff (M : Finset (ι → Bool)) (hM : M.Nonempty) :
    (∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), (∀ x, ¬ N.IsRecomb x) ∧ N.Derives M) ↔
      ∀ i j, ¬ Incompatible M i j := by
  constructor
  · rintro ⟨a, b, N, hN, hD⟩
    refine not_incompatible_of_no_recomb N hN fun r hr => ?_
    obtain ⟨v, -, rfl⟩ := hD.surjOn hr
    exact ⟨v, rfl⟩
  · intro h
    -- the base is a row, flipped at the constant columns, so that `M + S` has no constant column
    obtain ⟨r₀, hr₀⟩ := hM
    let cst : ι → Prop := fun i => ∀ r ∈ M, r i = r₀ i
    let S : ι → Bool := fun i => if cst i then !r₀ i else r₀ i
    have hS₁ : ∀ {i}, cst i → S i = !r₀ i := fun {i} hi => by simp [S, hi]
    have hS₂ : ∀ {i}, ¬ cst i → S i = r₀ i := fun {i} hi => by simp [S, hi]
    have hC : NoConstantColumn (addRow M S) := by
      intro i
      by_cases hi : cst i
      · refine ⟨r₀, Finset.mem_insert_of_mem hr₀, S, Finset.mem_insert_self _ _, ?_⟩
        rw [hS₁ hi]
        simp
      · unfold cst at hi
        push Not at hi
        obtain ⟨r, hr, hne⟩ := hi
        exact ⟨r, Finset.mem_insert_of_mem hr, r₀, Finset.mem_insert_of_mem hr₀, hne⟩
    have hcon : ∀ i j, ¬ Conflict S M i j := by
      intro i j hc
      by_cases hi : cst i
      · obtain ⟨r, hr, h₁, -⟩ := hc (S i) (!S j) (Or.inr (by simp))
        rw [hi r hr, hS₁ hi] at h₁
        simp at h₁
      · by_cases hj : cst j
        · obtain ⟨r, hr, -, h₂⟩ := hc (!S i) (S j) (Or.inl (by simp))
          rw [hj r hr, hS₁ hj] at h₂
          simp at h₂
        · refine h i j fun a b => ?_
          by_cases hab : a = S i ∧ b = S j
          · exact ⟨r₀, hr₀, by rw [hab.1, hS₂ hi], by rw [hab.2, hS₂ hj]⟩
          · have : a ≠ S i ∨ b ≠ S j := by
              by_contra hno
              push Not at hno
              exact hab hno
            exact hc a b this
    obtain ⟨a, b, N, hN, hD, -⟩ := exists_network_of_no_conflict M S ⟨r₀, hr₀⟩ hC hcon
    exact ⟨a, b, N, hN, hD⟩

section Uniqueness

open Gusfield2007.Network

variable {V E V' E' : Type*}

/-- The rows on the leaves below a node. -/
def rowsBelow (N : Network ι V E) (v : V) : Set (ι → Bool) := {r | ∃ l, N.IsLeaf l ∧ N.Reach v l ∧ N.label l = r}

/-- The rows below a node, with a mark for the root, so that the root differs from a node just below it. -/
def treeImage (N : Network ι V E) (v : V) : Set (Option (ι → Bool)) :=
  some '' rowsBelow N v ∪ {x | x = none ∧ v = N.root}

/-- What the node sets of a perfect phylogeny for `M` with ancestral sequence `S` must be. -/
def treeImages (M : Finset (ι → Bool)) (S : ι → Bool) : Set (Set (Option (ι → Bool))) :=
  {A | A = some '' (M : Set (ι → Bool)) ∪ {none} ∨ (∃ i, A = some '' {r | r ∈ M ∧ r i ≠ S i}) ∨ ∃ r ∈ M, A = {some r}}

variable {N : Network ι V E}

/-- Two nodes above a common node are comparable, with one arc into each node. -/
theorem reach_total (hinj : Function.Injective N.tgt) {x y l : V} (hx : N.Reach x l) (hy : N.Reach y l) :
    N.Reach x y ∨ N.Reach y x := by
  induction hy with
  | refl => exact Or.inl hx
  | @tail b c hb hbc ih =>
    obtain ⟨f, rfl, rfl⟩ := hbc
    rcases Relation.ReflTransGen.cases_tail hx with h | ⟨d, hd, f', rfl, hf'⟩
    · exact Or.inr (h ▸ hb.tail ⟨f, rfl, rfl⟩)
    · obtain rfl := hinj hf'
      exact ih hd

theorem rowsBelow_mono {x y : V} (h : N.Reach x y) : rowsBelow N y ⊆ rowsBelow N x := by
  rintro r ⟨l, hl, hr, rfl⟩
  exact ⟨l, hl, h.trans hr, rfl⟩

/-- A leaf has only its row below it. -/
theorem rowsBelow_leaf {l : V} (hl : N.IsLeaf l) : rowsBelow N l = {N.label l} := by
  ext r
  constructor
  · rintro ⟨l', -, hr, rfl⟩
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, ⟨e, he, -⟩, -⟩
    · rw [h]
      rfl
    · exact absurd he (hl e)
  · rintro rfl
    exact ⟨l, hl, .refl, rfl⟩

/-- **The state of a site at a node, in a tree**: it differs from the ancestral state exactly below the arc of the site. -/
theorem label_ne_iff [Finite V] (hinj : Function.Injective N.tgt) (i : ι) (v : V) :
    N.label v i ≠ N.ancestral i ↔ N.Reach (N.tgt (N.site i)) v := by
  refine N.arc_induction (P := fun v => N.label v i ≠ N.ancestral i ↔ N.Reach (N.tgt (N.site i)) v)
    (fun v ih => ?_) v
  by_cases hno : ∀ e, N.tgt e ≠ v
  · obtain rfl := (N.root_iff v).1 hno
    constructor
    · exact fun h => absurd rfl h
    · intro h
      exfalso
      rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, -, e, -, he⟩
      · exact hno _ h.symm
      · exact hno e he
  · push Not at hno
    obtain ⟨f, rfl⟩ := hno
    have hu : ∀ g, N.tgt g = N.tgt f → g = f := fun g hg => hinj hg
    have hlab := N.label_tree f hu i
    have hih := ih f rfl
    by_cases hs : N.site i = f
    · rw [ite_eq_left hs] at hlab
      subst hs
      have hnr : ¬ N.Reach (N.tgt (N.site i)) (N.src (N.site i)) := not_reach_tgt_src _
      have h₁ : N.label (N.src (N.site i)) i = N.ancestral i := by
        by_contra h
        exact hnr (hih.1 h)
      rw [hlab, h₁]
      simp only [Bool.not_eq_self, ne_eq, not_false_eq_true, true_iff]
      exact .refl
    · rw [ite_eq_right hs] at hlab
      rw [hlab, hih]
      constructor
      · exact fun h => h.tail ⟨f, rfl, rfl⟩
      · intro h
        rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hc, g, rfl, hg⟩
        · exact absurd (hinj h.symm) hs
        · obtain rfl := hinj hg
          exact hc

variable {M : Finset (ι → Bool)} {S : ι → Bool}

theorem treeImage_root [Finite V] (hD : N.Derives M) : treeImage N N.root = some '' (M : Set (ι → Bool)) ∪ {none} := by
  have hrows : rowsBelow N N.root = M := by
    ext r
    constructor
    · rintro ⟨l, hl, -, rfl⟩
      exact hD.mapsTo hl
    · intro hr
      obtain ⟨l, hl, rfl⟩ := hD.surjOn hr
      exact ⟨l, hl, N.reach_root l, rfl⟩
  rw [treeImage, hrows]
  ext x
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, and_true]

theorem none_mem_treeImage_iff {v : V} : none ∈ treeImage N v ↔ v = N.root := by
  constructor
  · rintro (⟨r, -, h⟩ | ⟨-, h⟩)
    · cases h
    · exact h
  · exact fun h => Or.inr ⟨rfl, h⟩

theorem treeImage_of_ne_root {v : V} (h : v ≠ N.root) : treeImage N v = some '' rowsBelow N v := by
  ext x
  constructor
  · rintro (hx | ⟨-, hx⟩)
    · exact hx
    · exact absurd hx h
  · exact fun hx => Or.inl hx

/-- **The sets of a reduced tree are distinct.** -/
theorem treeImage_injective [Finite V] (hN : ∀ x, ¬ N.IsRecomb x) (hD : N.Derives M) (hr : IsReducedTree N) :
    Function.Injective (treeImage N) := by
  have hinj := tgt_injective_of_no_recomb hN
  -- the case of `x` above `y`
  have key : ∀ {x y : V}, N.Reach x y → x ≠ N.root → rowsBelow N x = rowsBelow N y → x = y := by
    intro x y hxy hx hb
    by_contra hne
    rcases Relation.ReflTransGen.cases_head hxy with h | ⟨c, ⟨f, hf, rfl⟩, hc⟩
    · exact hne h
    obtain ⟨e, he⟩ : ∃ e, N.tgt e = x := by
      by_contra hno
      push Not at hno
      exact hx ((N.root_iff x).1 hno)
    obtain ⟨g, hg, hgf⟩ := hr.not_chain e f (he.trans hf.symm)
    obtain ⟨l, hl, hgl⟩ := N.exists_isLeaf_reach (N.tgt g)
    -- the row of `l` is below `x`, so below `y`, so below the target of `f`
    have hrow : N.label l ∈ rowsBelow N x :=
      ⟨l, hl, Relation.ReflTransGen.head ⟨g, hg.trans hf, rfl⟩ hgl, rfl⟩
    rw [hb] at hrow
    obtain ⟨l', hl', hyl', hlab⟩ := hrow
    obtain rfl := hD.injOn hl' hl hlab
    have hf' : N.Reach (N.tgt f) l' := hc.trans hyl'
    -- so two arcs out of `x` reach one leaf
    rcases reach_total hinj hgl hf' with h | h
    · rcases Relation.ReflTransGen.cases_tail h with h | ⟨d, hd, f₂, hf₁, hf₂⟩
      · exact hgf (hinj h.symm)
      · have hff : f₂ = f := hinj hf₂
        have : N.Reach (N.tgt g) (N.src g) := by rw [hg, ← hff, hf₁]; exact hd
        exact not_reach_tgt_src g this
    · rcases Relation.ReflTransGen.cases_tail h with h | ⟨d, hd, f₂, hf₁, hf₂⟩
      · exact hgf (hinj h)
      · have hfg : f₂ = g := hinj hf₂
        have : N.Reach (N.tgt f) (N.src f) := by rw [← hg, ← hfg, hf₁]; exact hd
        exact not_reach_tgt_src f this
  intro x y hxy
  have hroot : x = N.root ↔ y = N.root := by
    rw [← none_mem_treeImage_iff, ← none_mem_treeImage_iff (v := y), hxy]
  by_cases hx : x = N.root
  · rw [hx, hroot.1 hx]
  · have hy : y ≠ N.root := fun h => hx (hroot.2 h)
    rw [treeImage_of_ne_root hx, treeImage_of_ne_root hy] at hxy
    have hb : rowsBelow N x = rowsBelow N y := (Option.some_injective _).image_injective hxy
    obtain ⟨l, hl, hxl⟩ := N.exists_isLeaf_reach x
    have hrow : N.label l ∈ rowsBelow N y := hb ▸ ⟨l, hl, hxl, rfl⟩
    obtain ⟨l', hl', hyl', hlab⟩ := hrow
    obtain rfl := hD.injOn hl' hl hlab
    rcases reach_total (tgt_injective_of_no_recomb hN) hxl hyl' with h | h
    · exact key h hx hb
    · exact (key h hy hb.symm).symm

/-- In a reduced tree, the order of the sets is the order of the nodes. -/
theorem treeImage_subset_iff [Finite V] (hN : ∀ x, ¬ N.IsRecomb x) (hD : N.Derives M) (hr : IsReducedTree N) {x y : V} :
    treeImage N x ⊆ treeImage N y ↔ N.Reach y x := by
  have hinj := tgt_injective_of_no_recomb hN
  constructor
  · intro h
    by_cases hx : x = N.root
    · have hy : y = N.root := none_mem_treeImage_iff.1 (h (none_mem_treeImage_iff.2 hx))
      rw [hx, hy]
      exact .refl
    obtain ⟨l, hl, hxl⟩ := N.exists_isLeaf_reach x
    have hmem : some (N.label l) ∈ treeImage N x := Or.inl ⟨_, ⟨l, hl, hxl, rfl⟩, rfl⟩
    rcases h hmem with ⟨r, ⟨l', hl', hyl', rfl⟩, hsome⟩ | ⟨h', -⟩
    · obtain rfl := hD.injOn hl' hl (Option.some_injective _ hsome)
      rcases reach_total hinj hxl hyl' with h₁ | h₁
      · -- `x` is above `y`, and below it by the sets
        have hy : y ≠ N.root := fun hy => hx (eq_root_of_reach (hy ▸ h₁))
        have hsets : treeImage N x = treeImage N y := by
          refine Set.Subset.antisymm h ?_
          rw [treeImage_of_ne_root hx, treeImage_of_ne_root hy]
          exact Set.image_mono (rowsBelow_mono h₁)
        rw [treeImage_injective hN hD hr hsets]
        exact .refl
      · exact h₁
    · cases h'
  · intro h
    by_cases hx : x = N.root
    · rw [hx] at h ⊢
      rw [eq_root_of_reach h]
    · rw [treeImage_of_ne_root hx]
      intro a ha
      rcases ha with ⟨r, hr', rfl⟩
      exact Or.inl ⟨r, rowsBelow_mono h hr', rfl⟩

/-- The set of the target of an arc is strictly below that of its source. -/
theorem treeImage_tgt_ssubset [Finite V] (hN : ∀ x, ¬ N.IsRecomb x) (hD : N.Derives M) (hr : IsReducedTree N) (e : E) :
    treeImage N (N.tgt e) ⊂ treeImage N (N.src e) := by
  refine ⟨(treeImage_subset_iff hN hD hr).2 (Relation.ReflTransGen.single ⟨e, rfl, rfl⟩), fun h => ?_⟩
  have h₂ := (treeImage_subset_iff hN hD hr).1 h
  exact not_reach_tgt_src e h₂

/-- The source of an arc is the least node above its target. -/
theorem treeImage_src_subset [Finite V] (hN : ∀ x, ¬ N.IsRecomb x) (hD : N.Derives M) (hr : IsReducedTree N) (e : E) (w : V)
    (h : treeImage N (N.tgt e) ⊂ treeImage N w) : treeImage N (N.src e) ⊆ treeImage N w := by
  have hinj := tgt_injective_of_no_recomb hN
  have hw := (treeImage_subset_iff hN hD hr).1 h.subset
  refine (treeImage_subset_iff hN hD hr).2 ?_
  rcases Relation.ReflTransGen.cases_tail hw with h₁ | ⟨d, hd, f, hf₁, hf₂⟩
  · rw [← h₁] at h
    exact absurd h (ssubset_irrefl _)
  · rw [← hinj hf₂, hf₁]
    exact hd

/-- The set of the arc of a site. -/
theorem treeImage_site [Finite V] (hN : ∀ x, ¬ N.IsRecomb x) (hD : N.Derives M) (hS : N.ancestral = S) (i : ι) :
    treeImage N (N.tgt (N.site i)) = some '' {r | r ∈ M ∧ r i ≠ S i} := by
  have hinj := tgt_injective_of_no_recomb hN
  rw [treeImage_of_ne_root ((N.root_iff _).not.1 (fun h => h _ rfl))]
  congr 1
  ext r
  constructor
  · rintro ⟨l, hl, hr, rfl⟩
    refine ⟨hD.mapsTo hl, ?_⟩
    rw [← hS]
    exact (label_ne_iff hinj i l).2 hr
  · rintro ⟨hr, hri⟩
    obtain ⟨l, hl, rfl⟩ := hD.surjOn hr
    rw [← hS] at hri
    exact ⟨l, hl, (label_ne_iff hinj i l).1 hri, rfl⟩

/-- The sets of the nodes of a reduced tree are exactly `treeImages M S`. -/
theorem treeImage_mem [Finite V] (hN : ∀ x, ¬ N.IsRecomb x) (hD : N.Derives M) (hS : N.ancestral = S) (hr : IsReducedTree N)
    (v : V) : treeImage N v ∈ treeImages M S := by
  by_cases hv : v = N.root
  · exact Or.inl (hv ▸ treeImage_root hD)
  · obtain ⟨e, rfl⟩ : ∃ e, N.tgt e = v := by
      by_contra hno
      push Not at hno
      exact hv ((N.root_iff v).1 hno)
    rcases hr.arc_labelled e with ⟨i, rfl⟩ | hl
    · exact Or.inr (Or.inl ⟨i, treeImage_site hN hD hS i⟩)
    · refine Or.inr (Or.inr ⟨N.label (N.tgt e), hD.mapsTo hl, ?_⟩)
      rw [treeImage_of_ne_root hv, rowsBelow_leaf hl, Set.image_singleton]

theorem exists_treeImage_eq [Finite V] (hN : ∀ x, ¬ N.IsRecomb x) (hD : N.Derives M) (hS : N.ancestral = S)
    (hr : IsReducedTree N) {A : Set (Option (ι → Bool))} (hA : A ∈ treeImages M S) : ∃ v, treeImage N v = A := by
  rcases hA with rfl | ⟨i, rfl⟩ | ⟨r, hr', rfl⟩
  · exact ⟨N.root, treeImage_root hD⟩
  · exact ⟨_, treeImage_site hN hD hS i⟩
  · obtain ⟨l, hl, rfl⟩ := hD.surjOn hr'
    have hne : l ≠ N.root := fun h => hr.root_not_leaf (h ▸ hl)
    refine ⟨l, ?_⟩
    rw [treeImage_of_ne_root hne, rowsBelow_leaf hl, Set.image_singleton]

/-- **Line 156** (`g:rooted_unique`). "There is a unique phylogenetic network that derives `M`, with ancestral sequence `S` and without
recombination cycles". As printed this isn't so: an arc with no site can be subdivided, for one thing. It's so among the reduced trees
(`IsReducedTree`), as here. `exists_network_of_no_conflict` gives one when no two columns are in conflict. -/
theorem network_rooted_unique {N' : Network ι V' E'} [Finite V] [Finite V'] (hN : ∀ x, ¬ N.IsRecomb x) (hN' : ∀ x, ¬ N'.IsRecomb x)
    (hD : N.Derives M) (hD' : N'.Derives M) (hS : N.ancestral = S) (hS' : N'.ancestral = S) (hr : IsReducedTree N)
    (hr' : IsReducedTree N') : ∃ (eV : V ≃ V') (eE : E ≃ E'), N.IsIso N' eV eE := by
  have hinj := tgt_injective_of_no_recomb hN
  have hinj' := tgt_injective_of_no_recomb hN'
  have him := treeImage_injective hN hD hr
  have him' := treeImage_injective hN' hD' hr'
  have hex : ∀ v, ∃ v', treeImage N' v' = treeImage N v := fun v =>
    exists_treeImage_eq hN' hD' hS' hr' (treeImage_mem hN hD hS hr v)
  have hex' : ∀ v', ∃ v, treeImage N v = treeImage N' v' := fun v' =>
    exists_treeImage_eq hN hD hS hr (treeImage_mem hN' hD' hS' hr' v')
  choose f hf using hex
  choose g hg using hex'
  have hgf : ∀ v, g (f v) = v := fun v => him (by rw [hg, hf])
  have hfg : ∀ v', f (g v') = v' := fun v' => him' (by rw [hf, hg])
  let eV : V ≃ V' := ⟨f, g, hgf, hfg⟩
  have hroot : f N.root = N'.root := him' (by rw [hf, treeImage_root hD, treeImage_root hD'])
  have hroot' : g N'.root = N.root := by rw [← hroot, hgf]
  -- arcs correspond through their targets
  have harc : ∀ e, ∃ e', N'.tgt e' = f (N.tgt e) := by
    intro e
    by_contra hno
    push Not at hno
    have h₁ := (N'.root_iff _).1 hno
    have h₂ : N.tgt e = N.root := by rw [← hgf (N.tgt e), h₁, hroot']
    exact (N.root_iff _).2 h₂ e rfl
  have harc' : ∀ e', ∃ e, N.tgt e = g (N'.tgt e') := by
    intro e'
    by_contra hno
    push Not at hno
    have h₁ := (N.root_iff _).1 hno
    have h₂ : N'.tgt e' = N'.root := by rw [← hfg (N'.tgt e'), h₁, hroot]
    exact (N'.root_iff _).2 h₂ e' rfl
  choose a ha using harc
  choose a' ha' using harc'
  let eE : E ≃ E' :=
    ⟨a, a', fun e => hinj (by rw [ha', ha, hgf]), fun e' => hinj' (by rw [ha, ha', hfg])⟩
  have hsite : ∀ i, treeImage N' (N'.tgt (N'.site i)) = treeImage N (N.tgt (N.site i)) := fun i => by
    rw [treeImage_site hN hD hS i, treeImage_site hN' hD' hS' i]
  refine ⟨eV, eE, ⟨fun e => ?_, fun e => ha e, hroot.symm, fun i => ?_, fun v => ?_⟩⟩
  · -- the source of an arc is the least set above its target
    change N'.src (a e) = f (N.src e)
    refine him' (Set.Subset.antisymm ?_ ?_)
    · have h₁ : treeImage N' (N'.tgt (a e)) ⊂ treeImage N' (f (N.src e)) := by
        rw [ha, hf, hf]
        exact treeImage_tgt_ssubset hN hD hr e
      exact treeImage_src_subset hN' hD' hr' (a e) _ h₁
    · have h₁ : treeImage N (N.tgt e) ⊂ treeImage N (g (N'.src (a e))) := by
        rw [hg, ← hf (N.tgt e), ← ha]
        exact treeImage_tgt_ssubset hN' hD' hr' (a e)
      have h₂ := treeImage_src_subset hN hD hr e _ h₁
      rw [hg] at h₂
      rw [hf]
      exact h₂
  · change N'.site i = a (N.site i)
    refine hinj' (him' ?_)
    rw [ha, hf, hsite]
  · funext i
    have h₁ : N'.label (f v) i ≠ S i ↔ N.label v i ≠ S i := by
      conv_lhs => rw [← hS']
      conv_rhs => rw [← hS]
      rw [label_ne_iff hinj' i (f v), label_ne_iff hinj i v, ← treeImage_subset_iff hN' hD' hr',
        ← treeImage_subset_iff hN hD hr, hf, hsite]
    change N'.label (f v) i = N.label v i
    cases h₃ : N'.label (f v) i <;> cases h₄ : N.label v i <;> cases h₅ : S i <;> simp_all

end Uniqueness

end Gusfield1991
