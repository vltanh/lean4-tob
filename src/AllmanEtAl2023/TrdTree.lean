module

public import AllmanEtAl2023.TreeSuppression
public import Phylogenetics.Tree.Splits
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The shape of a suppressed tree

The results here say what `suppressDegreeTwo G` is, when `G` is a tree:

* `isTree_suppressDegreeTwo`: it is a tree;
* `ncard_neighborSet_suppressDegreeTwo`: a node keeps its degree;

and, for a labelled tree whose labelled nodes have degree 1 and whose other nodes have degree at least 3, on four taxa, `LabelledGraph.hasStar_or_hasQuartet`:
it has one of the literal topologies of the paper's Figure 4. This is the combinatorial content of the last sentences of Lemma 1, whose proof the paper omits; the degree
count on trees is the standard one.
-/

@[expose] public noncomputable section

open Phylogenetics
open scoped Classical

namespace AllmanEtAl2023.TreeSuppression

variable {W F X : Type*} {G : DirectedMultigraph W F}

/-! ### Connected -/

/-- A node reached in the tree from a node of degree other than 2 lies on a chain entered from a node reached in the suppressed graph. -/
theorem exists_reachable_enter (u : {w // nodeDegree G w ≠ 2}) {c : W} (hc : G.Walks Set.univ u.1 c) :
    ∃ y : {w // nodeDegree G w ≠ 2}, (suppressDegreeTwo G).Reachable u y ∧ Relation.ReflTransGen (Enter G) y.1 c := by
  induction hc with
  | refl => exact ⟨u, .refl _, .refl⟩
  | @tail a b _ hab ih =>
    obtain ⟨y, hy, hyr⟩ := ih
    by_cases hdb : nodeDegree G b = 2
    · exact ⟨y, hy, hyr.tail ⟨hab, hdb⟩⟩
    · by_cases hyb : y.1 = b
      · exact ⟨y, hy, hyb ▸ .refl⟩
      · refine ⟨⟨b, hdb⟩, hy.trans (SimpleGraph.Adj.reachable ?_), .refl⟩
        exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨fun h => hyb (congrArg Subtype.val h), Or.inl ⟨a, hyr, hab⟩⟩

/-- The suppressed graph of a connected graph is preconnected. -/
theorem preconnected_suppressDegreeTwo (hG : G.IsConnected) : (suppressDegreeTwo G).Preconnected := by
  intro u z
  obtain ⟨y, hy, hyr⟩ := exists_reachable_enter u (hG u.1 z.1)
  have : y = z := by
    rcases Relation.ReflTransGen.cases_tail hyr with h | ⟨c, -, -, hc⟩
    · exact Subtype.ext h.symm
    · exact absurd hc z.2
  exact this ▸ hy

/-! ### Sides of the edges of a tree -/

/-- What `x` reaches without the edge `g`. -/
def sideAt (G : DirectedMultigraph W F) (g : F) (x : W) : Set W := {v | G.Walks {g}ᶜ x v}

theorem mem_sideAt_self (g : F) (x : W) : x ∈ sideAt G g x := Relation.ReflTransGen.refl

/-- Walking from `x` to `v` without `g` is being on the side of `x`. -/
theorem Ends.not_mem_sideAt (hG : G.IsTree) {g : F} {x q : W} (hends : Ends G g x q) : q ∉ sideAt G g x := by
  intro hw
  refine hG.2 g ?_
  rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
    exact hw
  · rw [h₁, h₂]
    exact G.walks_symm hw

/-- `sideAt` is a side of the edge. -/
theorem Ends.isSideOf_sideAt (hG : G.IsTree) {g : F} {x q : W} (hends : Ends G g x q) : IsSideOf G g (sideAt G g x) := by
  have hq := hends.not_mem_sideAt hG
  intro f
  constructor
  · intro hc
    by_contra hfg
    exact G.not_crosses_walk_component {g}ᶜ x (e := f) hfg hc
  · rintro rfl
    rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨h₁ ▸ mem_sideAt_self _ _, h₂ ▸ hq⟩
    · exact Or.inr ⟨h₂ ▸ mem_sideAt_self _ _, h₁ ▸ hq⟩

/-- A chain into a side, after an edge, makes a `ChainLink`. -/
theorem ChainIn.chainLink {T : Set W} {a u v a' : W} (h : ChainIn G T a u) (hadj : G.AdjOn Set.univ a' a)
    (hr : Relation.ReflTransGen (Enter G) v a') : ChainLink G v u := by
  induction h using Relation.ReflTransGen.head_induction_on generalizing a' with
  | refl => exact ⟨a', hr, hadj⟩
  | @head a b hab _ ih => exact ih hab.1 (hr.tail ⟨hadj, hab.2.1⟩)

/-- **An edge of the suppressed graph is a chain of the tree**, starting at a side of its last edge. -/
theorem exists_side_of_chainLink {u w : {w // nodeDegree G w ≠ 2}} (hne : u ≠ w)
    (hl : ChainLink G u.1 w.1) :
    ∃ g z, Ends G g z w.1 ∧ ChainIn G (sideAt G g z) z u.1 := by
  obtain ⟨z, hz, g, -, hg⟩ := hl
  have hends : Ends G g z w.1 := hg
  have hzT : z ∈ sideAt G g z := mem_sideAt_self _ _
  -- the chain from `u` to `z` stays on the side of `z`
  have hchain : ∀ a, Relation.ReflTransGen (Enter G) a z → a ≠ w.1 → ChainIn G (sideAt G g z) z a := by
    intro a ha
    induction ha using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => .refl
    | @head a b hab _ ih =>
      intro haw
      have hbw : b ≠ w.1 := fun h => w.2 (h ▸ hab.2)
      have hb := ih hbw
      have hbT : b ∈ sideAt G g z := hb.mem_right hzT
      obtain ⟨f, -, hf⟩ := hab.1
      have hfne : f ≠ g := by
        rintro rfl
        have hf' : Ends G f a b := hf
        rcases hf' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hends with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
        · exact hbw (h₂.symm.trans h₄)
        · exact haw (h₁.symm.trans h₃)
        · exact haw (h₂.symm.trans h₄)
        · exact hbw (h₁.symm.trans h₃)
      have haT : a ∈ sideAt G g z := by
        have hf' : G.AdjOn {g}ᶜ b a := ⟨f, hfne, Or.symm hf⟩
        exact Relation.ReflTransGen.tail hbT hf'
      exact hb.tail ⟨G.adjOn_symm ⟨f, Set.mem_univ f, hf⟩, hab.2, hbT, haT⟩
  exact ⟨g, z, hends, hchain _ hz fun h => hne (Subtype.ext h)⟩

/-! ### It is a tree -/

/-- **The suppressed graph of a tree is acyclic.** -/
theorem isAcyclic_suppressDegreeTwo [Finite W] [Finite F] (hG : G.IsTree) : (suppressDegreeTwo G).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro u w hadj
  rw [SimpleGraph.isBridge_iff]
  intro hr
  obtain ⟨hne, hlink⟩ := (SimpleGraph.fromRel_adj _ _ _).mp hadj
  obtain ⟨g, z, hends, hu⟩ := exists_side_of_chainLink hne (hlink.elim id ChainLink.symm)
  have hT := hends.isSideOf_sideAt hG
  have := (reachable_iff hG hT hends (mem_sideAt_self _ _) (hends.not_mem_sideAt hG) hu (w := w) .refl w).mp hr
  exact hends.not_mem_sideAt hG this

/-- **Suppressing the nodes of degree 2 of a tree gives a tree.** -/
theorem isTree_suppressDegreeTwo [Finite W] [Finite F] [Nonempty {w // nodeDegree G w ≠ 2}] (hG : G.IsTree) :
    (suppressDegreeTwo G).IsTree :=
  ⟨⟨preconnected_suppressDegreeTwo hG.1⟩, isAcyclic_suppressDegreeTwo hG⟩

/-! ### Degrees -/

/-- The edges at a node. -/
def edgesAt (G : DirectedMultigraph W F) (v : W) : Set F := {e | G.source e = v ∨ G.target e = v}

/-- In a tree, the degree of a node is the number of edges at it. -/
theorem nodeDegree_eq_ncard_edgesAt [Finite F] (hG : G.IsTree) (v : W) : nodeDegree G v = (edgesAt G v).ncard := by
  have hdisj : Disjoint {g | G.target g = v} {g | G.source g = v} :=
    Set.disjoint_left.mpr fun g h₁ h₂ => source_ne_target hG g (Eq.trans h₂ (Eq.symm h₁))
  have hun : edgesAt G v = {g | G.target g = v} ∪ {g | G.source g = v} := by
    ext g
    simp only [edgesAt, Set.mem_ofPred_eq, Set.mem_union]
    exact or_comm
  rw [hun, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  rfl

theorem exists_ends_of_mem_edgesAt {e : F} {v : W} (he : e ∈ edgesAt G v) : ∃ x, Ends G e v x := by
  rcases he with h | h
  · exact ⟨G.target e, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨G.source e, Or.inr ⟨rfl, h⟩⟩

theorem Ends.mem_edgesAt {e : F} {v x : W} (he : Ends G e v x) : e ∈ edgesAt G v := by
  rcases he with ⟨h, -⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

/-- In a tree, an edge at a node has one other end. -/
theorem Ends.other_unique (hG : G.IsTree) {e : F} {v x x' : W} (h : Ends G e v x) (h' : Ends G e v x') : x = x' := by
  rcases h.eq_of_eq h' rfl with h₁ | h₁
  · exact h₁
  · exfalso
    rcases h with ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩
    · exact source_ne_target hG e (h₂.trans (h₁.trans h₃.symm))
    · exact source_ne_target hG e (h₂.trans (h₁.symm.trans h₃.symm))

/-- In a tree, the sides of two edges at a node, away from the node, are disjoint. -/
theorem sideAt_disjoint (hG : G.IsTree) {e e' : F} {v x x' : W} (he : Ends G e v x) (he' : Ends G e' v x') (hne : e ≠ e') :
    Disjoint (sideAt G e x) (sideAt G e' x') := by
  have hq : v ∉ sideAt G e x := he.symm.not_mem_sideAt hG
  have hq' : v ∉ sideAt G e' x' := he'.symm.not_mem_sideAt hG
  have hT := he.symm.isSideOf_sideAt hG
  have hx' : x' ∉ sideAt G e x := fun h => hne (hT.eq_of_ends he'.symm h hq).symm
  have key : ∀ y, G.Walks {e'}ᶜ x' y → y ∉ sideAt G e x := by
    intro y hw
    induction hw with
    | refl => exact hx'
    | @tail a b hprev hab ih =>
      intro hb
      obtain ⟨g, -, hgl⟩ := hab
      have hgends : Ends G g b a := Or.symm hgl
      have hge := hT.eq_of_ends hgends hb ih
      subst hge
      have hcompl : x ∉ (sideAt G g x)ᶜ := not_not.mpr (mem_sideAt_self _ _)
      have hav : a = v := he.eq_end hcompl ih hgends.symm
      exact hq' (hav ▸ hprev)
  exact Set.disjoint_left.mpr fun y hy hy' => key y hy' hy

/-- A step from a node at a chain from `v`, not back to `v`, stays beyond an edge at `v`. -/
theorem exists_edge_step (hG : G.IsTree) {v a b : W} {f : F} (hf : Ends G f a b) (hb : b ≠ v)
    (ha : a = v ∨ ∃ e x, Ends G e v x ∧ a ∈ sideAt G e x) : ∃ e x, Ends G e v x ∧ b ∈ sideAt G e x := by
  rcases ha with rfl | ⟨e, x, he, ha⟩
  · exact ⟨f, b, hf, mem_sideAt_self _ _⟩
  · refine ⟨e, x, he, ?_⟩
    by_cases hfe : f = e
    · subst hfe
      have hq : v ∉ sideAt G f x := he.symm.not_mem_sideAt hG
      have hax : a = x := he.symm.eq_end hq ha hf
      subst hax
      exact absurd (hf.other_unique hG he.symm) hb
    · have hstep : G.AdjOn {e}ᶜ a b := ⟨f, hfe, hf⟩
      exact Relation.ReflTransGen.tail ha hstep

/-- **A neighbour in the suppressed graph lies beyond an edge at the node.** -/
theorem exists_edge_of_chainLink (hG : G.IsTree) {v u : W} (hv : nodeDegree G v ≠ 2) (hne : u ≠ v) (h : ChainLink G v u) :
    ∃ e x, Ends G e v x ∧ u ∈ sideAt G e x := by
  obtain ⟨z, hz, g, -, hg⟩ := h
  have key : ∀ y, Relation.ReflTransGen (Enter G) v y → y = v ∨ ∃ e x, Ends G e v x ∧ y ∈ sideAt G e x := by
    intro y hy
    induction hy with
    | refl => exact Or.inl rfl
    | @tail a b _ hab ih =>
      obtain ⟨f, -, hf⟩ := hab.1
      exact Or.inr (exists_edge_step hG hf (fun h => hv (h ▸ hab.2)) ih)
  exact exists_edge_step hG hg hne (key z hz)

/-- **A node keeps its degree in the suppressed graph of a tree**: "a blob with `m` incident cut edges produces an `m`-multifurcation". -/
theorem ncard_neighborSet_suppressDegreeTwo [Finite W] [Finite F] (hG : G.IsTree) (v : {w // nodeDegree G w ≠ 2}) :
    ((suppressDegreeTwo G).neighborSet v).ncard = nodeDegree G v.1 := by
  rw [nodeDegree_eq_ncard_edgesAt hG]
  have hspec : ∀ e, e ∈ edgesAt G v.1 → ∃ (u : {w // nodeDegree G w ≠ 2}) (x : W),
      Ends G e v.1 x ∧ ChainIn G (sideAt G e x) x u.1 := by
    intro e he
    obtain ⟨x, hx⟩ := exists_ends_of_mem_edgesAt he
    have hT := hx.symm.isSideOf_sideAt hG
    obtain ⟨u, hu, hdu⟩ := exists_chainIn_end hG hT hx.symm (mem_sideAt_self _ _) (hx.symm.not_mem_sideAt hG)
    exact ⟨⟨u, hdu⟩, x, hx, hu⟩
  choose f x hx hf using hspec
  refine (Set.ncard_congr f (fun e he => ?_) (fun a b ha hb hab => ?_) (fun u hu => ?_)).symm
  · have hmem : (f e he).1 ∈ sideAt G e (x e he) := (hf e he).mem_right (mem_sideAt_self _ _)
    have hq : v.1 ∉ sideAt G e (x e he) := (hx e he).symm.not_mem_sideAt hG
    change (suppressDegreeTwo G).Adj v (f e he)
    refine (SimpleGraph.fromRel_adj _ _ _).mpr ⟨fun h => hq ?_, Or.inl ?_⟩
    · rw [h]
      exact hmem
    · exact (hf e he).chainLink (hx e he).adjOn .refl
  · by_contra hne
    have hd := sideAt_disjoint hG (hx a ha) (hx b hb) hne
    have h₁ := (hf a ha).mem_right (mem_sideAt_self _ _)
    have h₂ := (hf b hb).mem_right (mem_sideAt_self _ _)
    rw [← hab] at h₂
    exact Set.disjoint_left.mp hd h₁ h₂
  · have hadj : (suppressDegreeTwo G).Adj v u := hu
    obtain ⟨hne, hlink⟩ := (SimpleGraph.fromRel_adj _ _ _).mp hadj
    have hl : ChainLink G v.1 u.1 := hlink.elim id ChainLink.symm
    obtain ⟨e, y, hy, huy⟩ := exists_edge_of_chainLink hG v.2 (fun h => hne (Subtype.ext h.symm)) hl
    have he : e ∈ edgesAt G v.1 := hy.mem_edgesAt
    have hxy : x e he = y := (hx e he).other_unique hG hy
    have hT := hy.symm.isSideOf_sideAt hG
    have hq : v.1 ∉ sideAt G e y := hy.symm.not_mem_sideAt hG
    have hc := chainIn_of_chainLink hT hy.symm hq (ChainLink.symm hl) huy hq
    have hf' := hf e he
    rw [hxy] at hf'
    refine ⟨e, he, Subtype.ext ?_⟩
    exact eq_of_chainIn hG hT hy.symm (mem_sideAt_self _ _) hq hf' hc (f e he).2 u.2

end AllmanEtAl2023.TreeSuppression

/-! ### Four taxa -/

namespace AllmanEtAl2023.LabelledGraph

open Finset

variable {W X : Type*} (T : LabelledGraph W X)

/-- A labelled tree whose labelled nodes have degree 1 and whose other nodes have degree at least 3: what `T_rd(𝒩⁻)` is. -/
structure IsReducedTree (T : LabelledGraph W X) : Prop where
  isTree : T.graph.IsTree
  finite : Finite W
  injective : Function.Injective T.leaf
  leaf_degree : ∀ x, (T.graph.neighborSet (T.leaf x)).ncard = 1
  degree : ∀ v, (∀ x, T.leaf x ≠ v) → 3 ≤ (T.graph.neighborSet v).ncard

/-- A labelled tree with a node `u` adjacent to the four taxa, which are all the nodes but `u`, has the unresolved topology. -/
theorem hasStarTopology_of_adj (hinj : Function.Injective T.leaf) {a b c d : X} (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    {u : W} (hu : ∀ x, T.leaf x ≠ u) (ha : T.graph.Adj (T.leaf a) u) (hb : T.graph.Adj (T.leaf b) u)
    (hc : T.graph.Adj (T.leaf c) u) (hd : T.graph.Adj (T.leaf d) u)
    (huniq : ∀ x p q, T.graph.Adj (T.leaf x) p → T.graph.Adj (T.leaf x) q → p = q)
    (hcover : ∀ v, v = T.leaf a ∨ v = T.leaf b ∨ v = T.leaf c ∨ v = T.leaf d ∨ v = u) :
    T.HasStarTopology a b c d := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
  have hne : ∀ {x y}, x ≠ y → T.leaf x ≠ T.leaf y := fun hxy he => hxy (hinj he)
  refine ⟨u, ?_, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]
    exact ⟨⟨hne hab, hne hac, hne had, hu a⟩, ⟨hne hbc, hne hbd, hu b⟩, ⟨hne hcd, hu c⟩, hu d⟩
  · intro v
    simpa using hcover v
  · ext e
    constructor
    · induction e using Sym2.ind with
      | _ p q =>
        intro hadj
        have hadj : T.graph.Adj p q := hadj
        rcases hcover p with rfl | rfl | rfl | rfl | rfl
        · obtain rfl := huniq a _ _ hadj ha
          simp
        · obtain rfl := huniq b _ _ hadj hb
          simp
        · obtain rfl := huniq c _ _ hadj hc
          simp
        · obtain rfl := huniq d _ _ hadj hd
          simp
        · rcases hcover q with rfl | rfl | rfl | rfl | rfl
          · rw [Sym2.eq_swap]
            simp
          · rw [Sym2.eq_swap]
            simp
          · rw [Sym2.eq_swap]
            simp
          · rw [Sym2.eq_swap]
            simp
          · exact absurd hadj (T.graph.irrefl)
    · rintro (rfl | rfl | rfl | rfl)
      exacts [ha, hb, hc, hd]

/-- A labelled tree with two nodes `u, w` adjacent to each other and to two taxa each, which are all the nodes, has the quartet tree topology. -/
theorem hasQuartetTopology_of_adj (hinj : Function.Injective T.leaf) {a b c d : X} (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    {u w : W} (hu : ∀ x, T.leaf x ≠ u) (hw : ∀ x, T.leaf x ≠ w) (huw : T.graph.Adj u w) (ha : T.graph.Adj (T.leaf a) u)
    (hb : T.graph.Adj (T.leaf b) u) (hc : T.graph.Adj (T.leaf c) w) (hd : T.graph.Adj (T.leaf d) w)
    (huniq : ∀ x p q, T.graph.Adj (T.leaf x) p → T.graph.Adj (T.leaf x) q → p = q)
    (hcover : ∀ v, v = T.leaf a ∨ v = T.leaf b ∨ v = T.leaf c ∨ v = T.leaf d ∨ v = u ∨ v = w) :
    T.HasQuartetTopology a b c d := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
  have hne : ∀ {x y}, x ≠ y → T.leaf x ≠ T.leaf y := fun hxy he => hxy (hinj he)
  refine ⟨u, w, ?_, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]
    exact ⟨⟨hne hab, hne hac, hne had, hu a, hw a⟩, ⟨hne hbc, hne hbd, hu b, hw b⟩, ⟨hne hcd, hu c, hw c⟩,
      ⟨hu d, hw d⟩, huw.ne⟩
  · intro v
    simpa using hcover v
  · ext e
    constructor
    · induction e using Sym2.ind with
      | _ p q =>
        intro hadj
        have hadj : T.graph.Adj p q := hadj
        rcases hcover p with rfl | rfl | rfl | rfl | rfl | rfl
        · obtain rfl := huniq a _ _ hadj ha
          simp
        · obtain rfl := huniq b _ _ hadj hb
          simp
        · obtain rfl := huniq c _ _ hadj hc
          simp
        · obtain rfl := huniq d _ _ hadj hd
          simp
        · rcases hcover q with rfl | rfl | rfl | rfl | rfl | rfl
          · rw [Sym2.eq_swap]
            simp
          · rw [Sym2.eq_swap]
            simp
          · exact absurd (huniq c _ _ hadj.symm hc) huw.ne
          · exact absurd (huniq d _ _ hadj.symm hd) huw.ne
          · exact absurd hadj (T.graph.irrefl)
          · simp
        · rcases hcover q with rfl | rfl | rfl | rfl | rfl | rfl
          · exact absurd (huniq a _ _ hadj.symm ha) huw.ne.symm
          · exact absurd (huniq b _ _ hadj.symm hb) huw.ne.symm
          · rw [Sym2.eq_swap]
            simp
          · rw [Sym2.eq_swap]
            simp
          · rw [Sym2.eq_swap]
            simp
          · exact absurd hadj (T.graph.irrefl)
    · rintro (rfl | rfl | rfl | rfl | rfl)
      exacts [ha, hb, huw, hc, hd]

/-- The case of two nodes other than the taxa, in `hasStar_or_hasQuartet`: `a` is at the node `p`, with one other taxon. -/
theorem hasQuartet_of_nodes [DecidableEq X] (hinj : Function.Injective T.leaf) {a b c d : X}
    (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) (huniv : ∀ x : X, x = a ∨ x = b ∨ x = c ∨ x = d)
    {p q : W} (hpL : ∀ x, T.leaf x ≠ p) (hqL : ∀ x, T.leaf x ≠ q) (hpq : T.graph.Adj p q) {S S' : Finset X} (hS2 : S.card = 2)
    (hSS' : ∀ x, x ∈ S ∨ x ∈ S') (haS : a ∈ S) (hSadj : ∀ {x}, x ∈ S → T.graph.Adj (T.leaf x) p)
    (hS'adj : ∀ {x}, x ∈ S' → T.graph.Adj (T.leaf x) q)
    (huniq : ∀ x p q, T.graph.Adj (T.leaf x) p → T.graph.Adj (T.leaf x) q → p = q)
    (hcov : ∀ v, v = p ∨ v = q ∨ ∃ x, v = T.leaf x) :
    T.HasQuartetTopology a b c d ∨ T.HasQuartetTopology a c b d ∨ T.HasQuartetTopology a d b c := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
  obtain ⟨r, s, hrs, hSeq⟩ := Finset.card_eq_two.mp hS2
  have hother : ∃ y, y ≠ a ∧ S = {a, y} := by
    have ha' : a ∈ ({r, s} : Finset X) := hSeq ▸ haS
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
    rcases ha' with rfl | rfl
    · exact ⟨s, hrs.symm, hSeq⟩
    · exact ⟨r, hrs, by rw [hSeq, Finset.pair_comm]⟩
  obtain ⟨y, hya, hSy⟩ := hother
  have hnot : ∀ x, x ≠ a → x ≠ y → x ∈ S' := fun x hxa hxy => by
    rcases hSS' x with hx | hx
    · rw [hSy] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · exact absurd hx hxa
      · exact absurd hx hxy
    · exact hx
  have hyS : y ∈ S := by simp [hSy]
  rcases huniv y with rfl | rfl | rfl | rfl
  · exact absurd rfl hya
  · refine Or.inl (T.hasQuartetTopology_of_adj hinj ⟨hab, hac, had, hbc, hbd, hcd⟩ hpL hqL hpq (hSadj haS) (hSadj hyS)
      (hS'adj (hnot c hac.symm hbc.symm)) (hS'adj (hnot d had.symm hbd.symm)) huniq fun v => ?_)
    rcases hcov v with rfl | rfl | ⟨x, rfl⟩
    · simp
    · simp
    · rcases huniv x with rfl | rfl | rfl | rfl <;> simp
  · refine Or.inr (Or.inl (T.hasQuartetTopology_of_adj hinj ⟨hac, hab, had, hbc.symm, hcd, hbd⟩ hpL hqL hpq (hSadj haS) (hSadj hyS)
      (hS'adj (hnot b hab.symm hbc)) (hS'adj (hnot d had.symm hcd.symm)) huniq fun v => ?_))
    rcases hcov v with rfl | rfl | ⟨x, rfl⟩
    · simp
    · simp
    · rcases huniv x with rfl | rfl | rfl | rfl <;> simp
  · refine Or.inr (Or.inr (T.hasQuartetTopology_of_adj hinj ⟨had, hab, hac, hbd.symm, hcd.symm, hbc⟩ hpL hqL hpq (hSadj haS) (hSadj hyS)
      (hS'adj (hnot b hab.symm hbd)) (hS'adj (hnot c hac.symm hcd)) huniq fun v => ?_))
    rcases hcov v with rfl | rfl | ⟨x, rfl⟩
    · simp
    · simp
    · rcases huniv x with rfl | rfl | rfl | rfl <;> simp

/-- **The degree count on a tree with four labelled leaves.** A labelled tree, on exactly four taxa, whose labelled nodes have degree 1 and whose other nodes have degree at
least 3, has one of the literal topologies. The paper omits this, in Lemma 1. -/
theorem hasStar_or_hasQuartet [Finite W] [Fintype X] [DecidableEq X] (hT : T.graph.IsTree) (hinj : Function.Injective T.leaf)
    (hcard : Fintype.card X = 4) (hl : ∀ x, (T.graph.neighborSet (T.leaf x)).ncard = 1)
    (hint : ∀ v, (∀ x, T.leaf x ≠ v) → 3 ≤ (T.graph.neighborSet v).ncard)
    {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    T.HasStarTopology a b c d ∨ T.HasQuartetTopology a b c d ∨ T.HasQuartetTopology a c b d ∨
      T.HasQuartetTopology a d b c := by
  let _ : Fintype W := Fintype.ofFinite W
  have hne := ne_of_card_four h
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := hne
  have huniv : ∀ x : X, x = a ∨ x = b ∨ x = c ∨ x = d := by
    intro x
    have hu : ({a, b, c, d} : Finset X) = Finset.univ :=
      Finset.eq_univ_of_card _ (h.trans hcard.symm)
    have := Finset.mem_univ x
    rw [← hu] at this
    simpa using this
  have hdeg : ∀ v, T.graph.degree v = (T.graph.neighborSet v).ncard := fun v => by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
  -- the degree count
  let L : Finset W := Finset.univ.image T.leaf
  have hLcard : L.card = 4 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard]
  have hsumL : ∑ v ∈ L, T.graph.degree v = 4 := by
    rw [Finset.sum_image fun x _ y _ hxy => hinj hxy]
    simp [hdeg, hl, hcard]
  have hsum := T.graph.sum_degrees_eq_twice_card_edges
  have hedges := hT.card_edgeFinset
  have hsplit := Finset.sum_add_sum_compl L (fun v => T.graph.degree v)
  have hcardW : Fintype.card W = L.card + Lᶜ.card := by
    rw [Finset.card_compl]
    have := Finset.card_le_univ L
    omega
  have hmem : ∀ v, v ∈ Lᶜ ↔ ∀ x, T.leaf x ≠ v := fun v => by
    simp [L]
  have hlow : 3 * Lᶜ.card ≤ ∑ v ∈ Lᶜ, T.graph.degree v := by
    rw [mul_comm, ← smul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun v hv => ?_
    rw [hdeg]
    exact hint v ((hmem v).mp hv)
  have hcount : ∑ v ∈ Lᶜ, T.graph.degree v = 2 + 2 * Lᶜ.card := by omega
  have hm : Lᶜ.card ≤ 2 := by omega
  have hm0 : Lᶜ.card ≠ 0 := by
    intro h0
    rw [h0, Finset.card_eq_zero.mp h0] at hcount
    simp at hcount
  have huniq : ∀ x p q, T.graph.Adj (T.leaf x) p → T.graph.Adj (T.leaf x) q → p = q := by
    intro x p q hp hq
    have h1 := hl x
    rw [← hdeg, SimpleGraph.degree_eq_one_iff_existsUnique_adj] at h1
    exact h1.unique hp hq
  have hcases : ∀ v, v ∈ Lᶜ ∨ v = T.leaf a ∨ v = T.leaf b ∨ v = T.leaf c ∨ v = T.leaf d := by
    intro v
    by_cases hv : v ∈ Lᶜ
    · exact Or.inl hv
    · refine Or.inr ?_
      rw [hmem] at hv
      push Not at hv
      obtain ⟨x, rfl⟩ := hv
      rcases huniv x with rfl | rfl | rfl | rfl <;> simp
  have hnotL : ∀ {v}, v ∈ Lᶜ → ∀ x, T.leaf x ≠ v := fun hv => (hmem _).mp hv
  have hsix : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := ⟨hab, hac, had, hbc, hbd, hcd⟩
  have hm12 : Lᶜ.card = 1 ∨ Lᶜ.card = 2 := by omega
  rcases hm12 with h1 | h2
  · -- one node of degree 4: the star
    left
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
    have huL : u ∈ Lᶜ := by simp [hu]
    have hdu : T.graph.degree u = 4 := by
      rw [hu, Finset.sum_singleton, Finset.card_singleton] at hcount
      omega
    have hsub : T.graph.neighborFinset u ⊆ L := by
      intro v hv
      have hadj := (SimpleGraph.mem_neighborFinset _ _ _).mp hv
      by_contra hvL
      have hvc : v ∈ Lᶜ := Finset.mem_compl.mpr hvL
      rw [hu, Finset.mem_singleton] at hvc
      exact T.graph.loopless.irrefl u (hvc ▸ hadj)
    have heq : T.graph.neighborFinset u = L :=
      Finset.eq_of_subset_of_card_le hsub (by rw [SimpleGraph.card_neighborFinset_eq_degree, hdu, hLcard])
    have hadj : ∀ x, T.graph.Adj (T.leaf x) u := fun x => by
      have : T.leaf x ∈ T.graph.neighborFinset u := by
        rw [heq]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
      exact ((SimpleGraph.mem_neighborFinset _ _ _).mp this).symm
    refine T.hasStarTopology_of_adj hinj hsix (hnotL huL) (hadj a) (hadj b) (hadj c) (hadj d) huniq fun v => ?_
    rcases hcases v with hv | hv
    · rw [hu, Finset.mem_singleton] at hv
      exact Or.inr (Or.inr (Or.inr (Or.inr hv)))
    · tauto
  · -- two nodes of degree 3: the quartet tree
    right
    obtain ⟨u, w, huw, hset⟩ := Finset.card_eq_two.mp h2
    have huL : u ∈ Lᶜ := by simp [hset]
    have hwL : w ∈ Lᶜ := by simp [hset]
    have hdsum : T.graph.degree u + T.graph.degree w = 6 := by
      rw [hset, Finset.sum_pair huw, ← hset, h2] at hcount
      omega
    have hdu3 : 3 ≤ T.graph.degree u := by
      rw [hdeg]
      exact hint u (hnotL huL)
    have hdw3 : 3 ≤ T.graph.degree w := by
      rw [hdeg]
      exact hint w (hnotL hwL)
    have hdu : T.graph.degree u = 3 := by omega
    have hdw : T.graph.degree w = 3 := by omega
    -- the taxa at each node
    let Su : Finset X := Finset.univ.filter fun x => T.graph.Adj (T.leaf x) u
    let Sw : Finset X := Finset.univ.filter fun x => T.graph.Adj (T.leaf x) w
    have hdisj : Disjoint Su Sw := Finset.disjoint_left.mpr fun x hx hx' => huw (huniq x _ _
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hx').2)
    have hnbr : ∀ {p r}, (∀ v, v ∈ Lᶜ → v = p ∨ v = r) →
        T.graph.degree p ≤ (Finset.univ.filter fun x => T.graph.Adj (T.leaf x) p).card + if T.graph.Adj p r then 1 else 0 := by
      intro p r hall
      have hsub : T.graph.neighborFinset p ⊆ (Finset.univ.filter fun x => T.graph.Adj (T.leaf x) p).image T.leaf ∪
          (if T.graph.Adj p r then {r} else ∅) := by
        intro v hv
        have hadj := (SimpleGraph.mem_neighborFinset _ _ _).mp hv
        rcases hcases v with hvL | hvL
        · rcases hall v hvL with rfl | rfl
          · exact absurd hadj T.graph.irrefl
          · simp [hadj]
        · refine Finset.mem_union_left _ ?_
          have hv' : ∃ x, v = T.leaf x := by
            rcases hvL with h | h | h | h
            exacts [⟨_, h⟩, ⟨_, h⟩, ⟨_, h⟩, ⟨_, h⟩]
          obtain ⟨x, rfl⟩ := hv'
          exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj.symm⟩)
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
      have h₂ := Finset.card_image_le (s := Finset.univ.filter fun x => T.graph.Adj (T.leaf x) p) (f := T.leaf)
      split_ifs <;> simp only [Finset.card_singleton, Finset.card_empty] <;> omega
    have hallu : ∀ v, v ∈ Lᶜ → v = u ∨ v = w := fun v hv => by
      rw [hset] at hv
      simpa using hv
    have hallw : ∀ v, v ∈ Lᶜ → v = w ∨ v = u := fun v hv => (hallu v hv).symm
    have hbu : 3 ≤ Su.card + if T.graph.Adj u w then 1 else 0 := hdu ▸ hnbr hallu
    have hbw : 3 ≤ Sw.card + if T.graph.Adj w u then 1 else 0 := hdw ▸ hnbr hallw
    have hcardX : (Su ∪ Sw).card ≤ 4 := by
      rw [← hcard]
      exact Finset.card_le_univ _
    have hsumS : Su.card + Sw.card ≤ 4 := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact hcardX
    have hadjuw : T.graph.Adj u w := by
      by_contra hna
      have hna' : ¬ T.graph.Adj w u := fun h => hna h.symm
      simp only [hna, hna', ↓reduceIte] at hbu hbw
      omega
    simp only [hadjuw, hadjuw.symm, ↓reduceIte] at hbu hbw
    have hSu : Su.card = 2 := by omega
    have hSw : Sw.card = 2 := by omega
    have hun : ∀ x, x ∈ Su ∨ x ∈ Sw := by
      have hUU : Su ∪ Sw = Finset.univ := Finset.eq_univ_of_card _ (by
        rw [Finset.card_union_of_disjoint hdisj, hSu, hSw, hcard])
      intro x
      have := Finset.mem_univ x
      rw [← hUU] at this
      simpa using this
    have hSuAdj : ∀ {x}, x ∈ Su → T.graph.Adj (T.leaf x) u := fun hx => (Finset.mem_filter.mp hx).2
    have hSwAdj : ∀ {x}, x ∈ Sw → T.graph.Adj (T.leaf x) w := fun hx => (Finset.mem_filter.mp hx).2
    have hnotw : ∀ {x}, x ∈ Su → x ∉ Sw := fun hx => Finset.disjoint_left.mp hdisj hx
    have hcov : ∀ v, v = u ∨ v = w ∨ ∃ x, v = T.leaf x := fun v => by
      rcases hcases v with hv | rfl | rfl | rfl | rfl
      · rcases hallu v hv with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      all_goals exact Or.inr (Or.inr ⟨_, rfl⟩)
    rcases hun a with ha | ha
    · exact T.hasQuartet_of_nodes hinj hsix huniv (hnotL huL) (hnotL hwL) hadjuw hSu hun ha hSuAdj hSwAdj huniq hcov
    · refine T.hasQuartet_of_nodes hinj hsix huniv (hnotL hwL) (hnotL huL) hadjuw.symm hSw (fun x => (hun x).symm) ha hSwAdj
        hSuAdj huniq fun v => ?_
      rcases hcov v with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-! ### The sides of the literal topologies -/

/-- **The tree with the literal topology `ab|cd` has `{a, b}` as a side**, on four taxa. -/
theorem HasQuartetTopology.pair_mem_splits [Fintype X] [DecidableEq X] {T : LabelledGraph W X} {a b c d : X}
    (h : T.HasQuartetTopology a b c d) (huniv : ∀ x : X, x = a ∨ x = b ∨ x = c ∨ x = d) :
    ({a, b} : Finset X) ∈ T.splits := by
  obtain ⟨u, w, hnd, -, hE⟩ := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hnd
  obtain ⟨⟨hab, hac, had, hau, haw⟩, ⟨hbc, hbd, hbu, hbw⟩, ⟨hcd, hcu, hcw⟩, ⟨hdu, hdw⟩, huw⟩ := hnd
  have hadj : ∀ {p q : W}, s(p, q) ∈ T.graph.edgeSet → T.graph.Adj p q := fun h => h
  have hmem : ∀ {p q : W}, T.graph.Adj p q → s(p, q) ∈ T.graph.edgeSet := fun h => h
  have hedge : T.graph.Adj u w := hadj (by rw [hE]; simp)
  have hau' : T.graph.Adj (T.leaf a) u := hadj (by rw [hE]; simp)
  have hbu' : T.graph.Adj (T.leaf b) u := hadj (by rw [hE]; simp)
  have hca : c ∉ ({a, b} : Finset X) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hac (h ▸ rfl), fun h => hbc (h ▸ rfl)⟩
  have hda : d ∉ ({a, b} : Finset X) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => had (h ▸ rfl), fun h => hbd (h ▸ rfl)⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, by simp⟩, ⟨c, Finset.mem_compl.mpr hca⟩, u, w, hedge, fun x => ?_⟩
  -- the side of `u`
  have hclosed : ∀ z, Relation.ReflTransGen (T.graph.deleteEdges {s(u, w)}).Adj u z → z = T.leaf a ∨ z = T.leaf b ∨ z = u := by
    intro z hz
    induction hz with
    | refl => exact Or.inr (Or.inr rfl)
    | @tail p q _ hpq ih =>
      obtain ⟨hA, hne⟩ := SimpleGraph.deleteEdges_adj.mp hpq
      have hM := hmem hA
      rw [hE] at hM
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff] at hM
      simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or, not_and] at hne
      rcases hM with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
      · exact absurd rfl (hne.1 rfl)
      · rcases ih with h | h | h
        · exact absurd h.symm haw
        · exact absurd h.symm hbw
        · exact absurd h.symm huw
      · rcases ih with h | h | h
        · exact absurd h.symm hac
        · exact absurd h.symm hbc
        · exact absurd h hcu
      · rcases ih with h | h | h
        · exact absurd h.symm haw
        · exact absurd h.symm hbw
        · exact absurd h.symm huw
      · rcases ih with h | h | h
        · exact absurd h.symm had
        · exact absurd h.symm hbd
        · exact absurd h hdu
      · rcases ih with h | h | h
        · exact absurd h.symm haw
        · exact absurd h.symm hbw
        · exact absurd h.symm huw
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · refine SimpleGraph.Adj.reachable (SimpleGraph.deleteEdges_adj.mpr ⟨hau'.symm, ?_⟩)
      simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or, not_and]
      exact ⟨fun _ h => absurd h haw, fun h => absurd h huw⟩
    · refine SimpleGraph.Adj.reachable (SimpleGraph.deleteEdges_adj.mpr ⟨hbu'.symm, ?_⟩)
      simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or, not_and]
      exact ⟨fun _ h => absurd h hbw, fun h => absurd h huw⟩
  · intro hr
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    have hc := hclosed _ hr
    rcases huniv x with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rcases hc with h | h | h
      · exact absurd h.symm hac
      · exact absurd h.symm hbc
      · exact absurd h hcu
    · rcases hc with h | h | h
      · exact absurd h.symm had
      · exact absurd h.symm hbd
      · exact absurd h hdu

/-- **The tree with the literal unresolved topology has no side with two taxa on each side**: every side, or its complement, is one taxon. -/
theorem HasStarTopology.card_of_mem_splits [Fintype X] [DecidableEq X] {T : LabelledGraph W X} {a b c d : X}
    (h : T.HasStarTopology a b c d) (huniv : ∀ x : X, x = a ∨ x = b ∨ x = c ∨ x = d) {A : Finset X} (hA : A ∈ T.splits) :
    A.card = 1 ∨ Aᶜ.card = 1 := by
  obtain ⟨u, hnd, -, hE⟩ := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hnd
  obtain ⟨⟨hab, hac, had, hau⟩, ⟨hbc, hbd, hbu⟩, ⟨hcd, hcu⟩, hdu⟩ := hnd
  have hmem : ∀ {p q : W}, T.graph.Adj p q → s(p, q) ∈ T.graph.edgeSet := fun h => h
  have hadj' : ∀ {p q : W}, s(p, q) ∈ T.graph.edgeSet → T.graph.Adj p q := fun h => h
  have hxu : ∀ x, T.leaf x ≠ u := fun x => by
    rcases huniv x with rfl | rfl | rfl | rfl <;> assumption
  have hinj : Function.Injective T.leaf := by
    intro x y hxy
    rcases huniv x with rfl | rfl | rfl | rfl <;> rcases huniv y with rfl | rfl | rfl | rfl <;> first
      | rfl
      | exact absurd hxy ‹_›
      | exact absurd hxy.symm ‹_›
  have hadj : ∀ x, T.graph.Adj (T.leaf x) u := fun x => by
    refine hadj' ?_
    rw [hE]
    rcases huniv x with rfl | rfl | rfl | rfl <;> simp
  have hall : ∀ {p q}, T.graph.Adj p q → ∃ y, (p = T.leaf y ∧ q = u) ∨ (p = u ∧ q = T.leaf y) := by
    intro p q hpq
    have hM := hmem hpq
    rw [hE] at hM
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff] at hM
    rcases hM with h | h | h | h <;> exact ⟨_, h⟩
  have huq : ∀ {y z}, T.graph.Adj (T.leaf y) z → z = u := by
    intro y z hyz
    obtain ⟨t, ⟨h₁, h₂⟩ | ⟨h₁, -⟩⟩ := hall hyz
    · exact h₂
    · exact absurd h₁ (hxu y)
  obtain ⟨-, hne₁, hne₂, p, q, hpq, hside⟩ := Finset.mem_filter.mp hA
  obtain ⟨y, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hall hpq
  · -- the side of a taxon alone
    left
    have hclosed : ∀ z, Relation.ReflTransGen (T.graph.deleteEdges {s(T.leaf y, q)}).Adj (T.leaf y) z → z = T.leaf y := by
      intro z hz
      induction hz with
      | refl => rfl
      | @tail r t _ hrt ih =>
        subst ih
        obtain ⟨hA', hne⟩ := SimpleGraph.deleteEdges_adj.mp hrt
        exact absurd (by rw [huq hA']; rfl) hne
    have hsub : A ⊆ {y} := by
      intro x hx
      have hr := (hside x).mp hx
      rw [SimpleGraph.reachable_iff_reflTransGen] at hr
      simpa using hinj (hclosed _ hr)
    obtain ⟨x, hx⟩ := hne₁
    have hxy := Finset.mem_singleton.mp (hsub hx)
    subst hxy
    rw [Finset.eq_singleton_iff_unique_mem.mpr ⟨hx, fun z hz => Finset.mem_singleton.mp (hsub hz)⟩]
    simp
  · -- the side away from a taxon
    right
    have hsub : Aᶜ ⊆ {y} := by
      intro x hx
      by_contra hxy
      refine Finset.mem_compl.mp hx ((hside x).mpr ?_)
      refine SimpleGraph.Adj.reachable (SimpleGraph.deleteEdges_adj.mpr ⟨(hadj x).symm, ?_⟩)
      simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or, not_and]
      refine ⟨fun _ h => hxy (Finset.mem_singleton.mpr (hinj h)), fun h => absurd h.symm (hxu y)⟩
    obtain ⟨x, hx⟩ := hne₂
    have hxy := Finset.mem_singleton.mp (hsub hx)
    subst hxy
    rw [Finset.eq_singleton_iff_unique_mem.mpr ⟨hx, fun z hz => Finset.mem_singleton.mp (hsub hz)⟩]
    simp

end AllmanEtAl2023.LabelledGraph
