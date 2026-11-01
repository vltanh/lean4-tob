module

public import AllmanEtAl2023.BlobDefinitions

/-!
# Suppressing the nodes of degree 2 of a tree keeps its splits

`suppressDegreeTwo G` has the nodes of degree other than 2 of the multigraph `G`, and two of them are adjacent when a path through nodes of degree 2 joins them.
When `G` is a tree, the sides of the edges of `suppressDegreeTwo G` are the sides of the edges of `G`, on labelled nodes of degree other than 2: `hasSide_iff`. The
lemmas are about a side `T` of an edge `e` of the tree, and the chain of nodes of degree 2 from an end of `e` into `T`, which is unique (`eq_of_chainIn`) and ends
(`exists_chainIn_end`).
-/

@[expose] public noncomputable section

open Phylogenetics
open scoped Classical

namespace AllmanEtAl2023.TreeSuppression

variable {W F X : Type*} {G : DirectedMultigraph W F}

/-- `T` is a side of the edge `e`: `e` is the only edge crossing `T`. -/
def IsSideOf (G : DirectedMultigraph W F) (e : F) (T : Set W) : Prop := ∀ f, G.Crosses f T ↔ f = e

/-- A walk inside `T` all of whose nodes but the last have degree 2. -/
def ChainIn (G : DirectedMultigraph W F) (T : Set W) : W → W → Prop :=
  Relation.ReflTransGen fun a b => G.AdjOn Set.univ a b ∧ nodeDegree G a = 2 ∧ a ∈ T ∧ b ∈ T

/-- The step of `ChainLink`. -/
abbrev Enter (G : DirectedMultigraph W F) (a b : W) : Prop := G.AdjOn Set.univ a b ∧ nodeDegree G b = 2

/-- The edge `e` has the ends `p` and `q`. -/
def Ends (G : DirectedMultigraph W F) (e : F) (p q : W) : Prop :=
  (G.source e = p ∧ G.target e = q) ∨ (G.source e = q ∧ G.target e = p)

theorem Ends.symm {e : F} {p q : W} (h : Ends G e p q) : Ends G e q p := Or.symm h

theorem Ends.adjOn {e : F} {p q : W} (h : Ends G e p q) : G.AdjOn Set.univ p q := ⟨e, Set.mem_univ e, h⟩

theorem Ends.eq_of_eq {e : F} {p q p' q' : W} (h : Ends G e p q) (h' : Ends G e p' q') (hp : p = p') : q = q' ∨ (p = q) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl h₂
  · exact Or.inr (hp.trans h₂.symm)
  · exact Or.inr (hp.trans h₁.symm)
  · exact Or.inl h₁

theorem exists_ends_of_adjOn {a b : W} (h : G.AdjOn Set.univ a b) : ∃ e, Ends G e a b := by
  obtain ⟨e, -, he⟩ := h
  exact ⟨e, he⟩

theorem IsSideOf.compl {e : F} {T : Set W} (hT : IsSideOf G e T) : IsSideOf G e Tᶜ := fun f =>
  (G.crosses_compl f T).trans (hT f)

theorem IsSideOf.crosses {e : F} {T : Set W} (hT : IsSideOf G e T) : G.Crosses e T := (hT e).mpr rfl

/-- An edge crossing a side is its edge. -/
theorem IsSideOf.eq_of_ends {e g : F} {T : Set W} {a b : W} (hT : IsSideOf G e T) (hg : Ends G g a b) (ha : a ∈ T)
    (hb : b ∉ T) : g = e := by
  refine (hT g).mp ?_
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩

/-- A tree has no loop. -/
theorem source_ne_target (hG : G.IsTree) (e : F) : G.source e ≠ G.target e := fun h =>
  hG.2 e (h ▸ .refl)

/-- The end of `e` on one side of `e`. -/
theorem Ends.eq_end {e : F} {T : Set W} {x q y z : W} (he : Ends G e x q) (hq : q ∉ T)
    (hy : y ∈ T) (hyz : Ends G e y z) : y = x := by
  rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hyz with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
  · exact h₃.symm.trans h₁
  · exact absurd (h₄.symm.trans h₂ ▸ hy) hq
  · exact absurd (h₃.symm.trans h₁ ▸ hy) hq
  · exact h₄.symm.trans h₂

/-- A node of degree 2 in a tree, with one edge `e`, has exactly one other edge. -/
theorem exists_other_edge [Finite F] (hG : G.IsTree) {e : F} {x : W} (he : G.source e = x ∨ G.target e = x)
    (hd : nodeDegree G x = 2) :
    ∃ f, f ≠ e ∧ (G.source f = x ∨ G.target f = x) ∧ ∀ g, (G.source g = x ∨ G.target g = x) → g = e ∨ g = f := by
  have hdisj : Disjoint {g | G.target g = x} {g | G.source g = x} :=
    Set.disjoint_left.mpr fun g h₁ h₂ => source_ne_target hG g (Eq.trans h₂ (Eq.symm h₁))
  have hc : ({g | G.target g = x} ∪ {g | G.source g = x}).ncard = 2 := by
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    exact hd
  obtain ⟨p, q, hpq, h⟩ := Set.ncard_eq_two.mp hc
  have hmem : ∀ g, (G.source g = x ∨ G.target g = x) ↔ g = p ∨ g = q := fun g => by
    have := Set.ext_iff.mp h g
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rw [or_comm]
    exact this
  rcases (hmem e).mp he with rfl | rfl
  · exact ⟨q, hpq.symm, (hmem q).mpr (Or.inr rfl), fun g hg => (hmem g).mp hg⟩
  · exact ⟨p, hpq, (hmem p).mpr (Or.inl rfl), fun g hg => ((hmem g).mp hg).symm⟩

/-- The next edge of a chain. `T \ {x}` is a side of the other edge at a node `x` of degree 2. -/
theorem exists_next [Finite F] (hG : G.IsTree) {e : F} {T : Set W} {x q : W} (hT : IsSideOf G e T) (he : Ends G e x q)
    (hx : x ∈ T) (hq : q ∉ T) (hd : nodeDegree G x = 2) :
    ∃ f x', IsSideOf G f (T \ {x}) ∧ Ends G f x x' ∧ x' ∈ T \ {x} ∧
      ∀ b, G.AdjOn Set.univ x b → b ∈ T → b = x' := by
  have hex : G.source e = x ∨ G.target e = x := by
    rcases he with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨f, hfe, hfx, hall⟩ := exists_other_edge hG hex hd
  have hne := source_ne_target hG f
  obtain ⟨x', hends⟩ : ∃ x', Ends G f x x' := by
    rcases hfx with h | h
    · exact ⟨G.target f, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨G.source f, Or.inr ⟨rfl, h⟩⟩
  have hxx' : x' ≠ x := by
    rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact fun h => hne (h₁.trans (h.symm.trans h₂.symm))
    · exact fun h => hne (h₁.trans (h.trans h₂.symm))
  have hx'T : x' ∈ T := by
    by_contra hx'
    exact hfe (hT.eq_of_ends hends hx hx')
  have hmem' : x' ∈ T \ {x} := ⟨hx'T, hxx'⟩
  refine ⟨f, x', fun g => ⟨fun hc => ?_, ?_⟩, hends, hmem', fun b hb hbT => ?_⟩
  · -- `g` crosses `T \ {x}`
    obtain ⟨a, c, hg, ha, hc'⟩ : ∃ a c, Ends G g a c ∧ a ∈ T \ {x} ∧ c ∉ T \ {x} := by
      rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, h₁, h₂⟩
      · exact ⟨_, _, Or.inr ⟨rfl, rfl⟩, h₁, h₂⟩
    by_cases hcT : c ∈ T
    · have hcx : c = x := by
        by_contra hcx
        exact hc' ⟨hcT, hcx⟩
      subst hcx
      have hgc : G.source g = c ∨ G.target g = c := by
        rcases hg with ⟨-, h⟩ | ⟨h, -⟩
        · exact Or.inr h
        · exact Or.inl h
      rcases hall g hgc with rfl | rfl
      · rcases Ends.eq_of_eq he hg.symm rfl with h | h
        · exact absurd (h ▸ ha.1) hq
        · exact absurd (h ▸ hx) hq
      · rfl
    · -- `g` crosses `T`, so it is `e`, whose end in `T` is `x`
      have hge := hT.eq_of_ends hg ha.1 hcT
      subst hge
      exact absurd (he.eq_end hq ha.1 hg) ha.2
  · rintro rfl
    rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₂ ▸ hmem', fun h => h.2 h₁⟩
    · exact Or.inl ⟨h₁ ▸ hmem', fun h => h.2 h₂⟩
  · obtain ⟨g, hg⟩ := exists_ends_of_adjOn hb
    have hgx : G.source g = x ∨ G.target g = x := by
      rcases hg with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    rcases hall g hgx with rfl | rfl
    · rcases Ends.eq_of_eq hg he rfl with h | h
      · exact absurd (h ▸ hbT) hq
      · exact (source_ne_target hG g (by
          rcases hg with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exact h₁.trans (h.trans h₂.symm)
          · exact h₁.trans (h.symm.trans h₂.symm))).elim
    · rcases Ends.eq_of_eq hg hends rfl with h | h
      · exact h
      · exact (hne (by
          rcases hg with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exact h₁.trans (h.trans h₂.symm)
          · exact h₁.trans (h.symm.trans h₂.symm))).elim

theorem ChainIn.mem_right {T : Set W} {a b : W} (h : ChainIn G T a b) (ha : a ∈ T) : b ∈ T := by
  induction h with
  | refl => exact ha
  | tail _ hst _ => exact hst.2.2.2

/-- A chain from a node `x` of degree 2 to a node of another degree passes on to the next node, and stays beyond. -/
theorem chainIn_next {T : Set W} {x x' p : W} (hdx : nodeDegree G x = 2) (hp : nodeDegree G p ≠ 2)
    (hnext : ∀ b, G.AdjOn Set.univ x b → b ∈ T → b = x') (h : ChainIn G T x p) : ChainIn G (T \ {x}) x' p := by
  have key : ∀ a, ChainIn G T a p → (a = x → ChainIn G (T \ {x}) x' p) ∧ (a ≠ x → ChainIn G (T \ {x}) a p) := by
    intro a ha
    induction ha using Relation.ReflTransGen.head_induction_on with
    | refl =>
      have hpx : p ≠ x := fun h => hp (h ▸ hdx)
      exact ⟨fun h => absurd h hpx, fun _ => .refl⟩
    | @head a b hab _ ih =>
      obtain ⟨hadj, hda, haT, hbT⟩ := hab
      refine ⟨?_, fun hax => ?_⟩
      · rintro rfl
        have hb := hnext b hadj hbT
        by_cases hbx : b = a
        · exact ih.1 hbx
        · exact hb ▸ ih.2 hbx
      · by_cases hbx : b = x
        · subst hbx
          have ha' : a = x' := hnext a (G.adjOn_symm hadj) haT
          exact ha' ▸ ih.1 rfl
        · exact Relation.ReflTransGen.head ⟨hadj, hda, ⟨haT, hax⟩, ⟨hbT, hbx⟩⟩ (ih.2 hbx)
  exact (key x h).1 rfl

/-- **The chain from an end of an edge into its side is unique.** -/
theorem eq_of_chainIn [Finite W] [Finite F] (hG : G.IsTree) {e : F} {T : Set W} {x q p u : W} (hT : IsSideOf G e T)
    (he : Ends G e x q) (hx : x ∈ T) (hq : q ∉ T) (hp : ChainIn G T x p) (hu : ChainIn G T x u)
    (hdp : nodeDegree G p ≠ 2) (hdu : nodeDegree G u ≠ 2) : p = u := by
  induction hn : T.ncard using Nat.strong_induction_on generalizing e T x q with
  | _ n ih =>
    by_cases hd : nodeDegree G x = 2
    · obtain ⟨f, x', hT', hends, hx', hnext⟩ := exists_next hG hT he hx hq hd
      have hlt : (T \ {x}).ncard < n := hn ▸ Set.ncard_sdiff_singleton_lt_of_mem hx (Set.toFinite _)
      exact ih _ hlt hT' hends.symm hx' (fun h => h.2 rfl)
        (chainIn_next hd hdp hnext hp) (chainIn_next hd hdu hnext hu) rfl
    · have key : ∀ y, ChainIn G T x y → y = x := fun y hy => by
        rcases Relation.ReflTransGen.cases_head hy with h | ⟨c, hc, -⟩
        · exact h.symm
        · exact absurd hc.2.1 hd
      rw [key p hp, key u hu]

/-- **The chain from an end of an edge into its side ends.** -/
theorem exists_chainIn_end [Finite W] [Finite F] (hG : G.IsTree) {e : F} {T : Set W} {x q : W} (hT : IsSideOf G e T)
    (he : Ends G e x q) (hx : x ∈ T) (hq : q ∉ T) : ∃ u, ChainIn G T x u ∧ nodeDegree G u ≠ 2 := by
  induction hn : T.ncard using Nat.strong_induction_on generalizing e T x q with
  | _ n ih =>
    by_cases hd : nodeDegree G x = 2
    · obtain ⟨f, x', hT', hends, hx', hnext⟩ := exists_next hG hT he hx hq hd
      have hlt : (T \ {x}).ncard < n := hn ▸ Set.ncard_sdiff_singleton_lt_of_mem hx (Set.toFinite _)
      obtain ⟨u, hu, hdu⟩ := ih _ hlt hT' hends.symm hx' (fun h => h.2 rfl) rfl
      refine ⟨u, Relation.ReflTransGen.head ⟨hends.adjOn, hd, hx, hx'.1⟩ ?_, hdu⟩
      refine Relation.ReflTransGen.mono ?_ _ _ hu
      rintro a b ⟨h₁, h₂, h₃, h₄⟩
      exact ⟨h₁, h₂, h₃.1, h₄.1⟩
    · exact ⟨x, .refl, hd⟩

/-- `ChainLink` is symmetric. -/
theorem ChainLink.symm {u v : W} (h : ChainLink G u v) : ChainLink G v u := by
  obtain ⟨x, hx, hv⟩ := h
  have key : ∀ y, Relation.ReflTransGen (Enter G) u y → ∀ w, G.AdjOn Set.univ y w → ChainLink G w u := by
    intro y hy
    induction hy with
    | refl => exact fun w hw => ⟨w, .refl, G.adjOn_symm hw⟩
    | @tail a b _ hab ih =>
      intro w hw
      obtain ⟨z, hz, hzu⟩ := ih b hab.1
      exact ⟨z, Relation.ReflTransGen.head ⟨G.adjOn_symm hw, hab.2⟩ hz, hzu⟩
  exact key x hx v hv

/-- A chain into a side gives a chain back out, entering nodes of degree 2. -/
theorem ChainIn.enter_rev {T : Set W} {a b : W} (h : ChainIn G T a b) : Relation.ReflTransGen (Enter G) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact Relation.ReflTransGen.head ⟨G.adjOn_symm hst.1, hst.2.1⟩ ih

/-- A chain crossing a side from `p` starts in the side, and reaches the end of the edge there. -/
theorem chainIn_of_chainLink {e : F} {T : Set W} {x q p r : W} (hT : IsSideOf G e T) (he : Ends G e x q)
    (hq : q ∉ T) (h : ChainLink G p r) (hp : p ∈ T) (hr : r ∉ T) : ChainIn G T x p := by
  obtain ⟨z, hz, hzr⟩ := h
  have key : ∀ y, Relation.ReflTransGen (Enter G) p y → ChainIn G T x p ∨ (y ∈ T ∧ ChainIn G T y p) := by
    intro y hy
    induction hy with
    | refl => exact Or.inr ⟨hp, .refl⟩
    | @tail a b _ hab ih =>
      rcases ih with ih | ⟨ha, hc⟩
      · exact Or.inl ih
      · by_cases hb : b ∈ T
        · exact Or.inr ⟨hb, Relation.ReflTransGen.head ⟨G.adjOn_symm hab.1, hab.2, hb, ha⟩ hc⟩
        · obtain ⟨g, hg⟩ := exists_ends_of_adjOn hab.1
          have hge := hT.eq_of_ends hg ha hb
          subst hge
          have := he.eq_end hq ha hg
          exact Or.inl (this ▸ hc)
  rcases key z hz with h' | ⟨hzT, hc⟩
  · exact h'
  · obtain ⟨g, hg⟩ := exists_ends_of_adjOn hzr
    have hge := hT.eq_of_ends hg hzT hr
    subst hge
    have := he.eq_end hq hzT hg
    exact this ▸ hc

/-- **The core.** The nodes reached in the suppressed tree from one end of an edge, without that edge, are those of a side of an edge of the tree. -/
theorem reachable_iff [Finite W] [Finite F] (hG : G.IsTree) {e : F} {T : Set W} {x q : W} (hT : IsSideOf G e T)
    (he : Ends G e x q) (hx : x ∈ T) (hq : q ∉ T) {u w : {w // nodeDegree G w ≠ 2}} (hu : ChainIn G T x u.1)
    (hw : ChainIn G Tᶜ q w.1) (z : {w // nodeDegree G w ≠ 2}) :
    ((suppressDegreeTwo G).deleteEdges {s(u, w)}).Reachable u z ↔ z.1 ∈ T := by
  have huT : u.1 ∈ T := hu.mem_right hx
  have hwT : w.1 ∉ T := hw.mem_right hq
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact huT
    | @tail a b _ hab ih =>
      by_contra hb
      obtain ⟨hadj, hne⟩ := SimpleGraph.deleteEdges_adj.mp hab
      obtain ⟨-, hlink⟩ := (SimpleGraph.fromRel_adj _ _ _).mp hadj
      have hl : ChainLink G a.1 b.1 := hlink.elim id ChainLink.symm
      have h₁ : ChainIn G T x a.1 := chainIn_of_chainLink hT he hq hl ih hb
      have h₂ : ChainIn G Tᶜ q b.1 := chainIn_of_chainLink hT.compl he.symm (not_not.mpr hx) (ChainLink.symm hl) hb (not_not.mpr ih)
      have hau : a = u := Subtype.ext (eq_of_chainIn hG hT he hx hq h₁ hu a.2 u.2)
      have hbw : b = w := Subtype.ext (eq_of_chainIn hG hT.compl he.symm hq (not_not.mpr hx) h₂ hw b.2 w.2)
      exact hne (by rw [hau, hbw]; rfl)
  · intro hz
    -- a walk of the tree inside `T` splits at the nodes of degree other than 2
    have hwalk := G.walks_diff_of_cut hT (hG.1 u.1 z.1) huT hz
    have key : ∀ c, G.Walks (Set.univ \ {e}) u.1 c → c ∈ T → ∃ y : {w // nodeDegree G w ≠ 2}, y.1 ∈ T ∧
        Relation.ReflTransGen ((suppressDegreeTwo G).deleteEdges {s(u, w)}).Adj u y ∧
        Relation.ReflTransGen (Enter G) y.1 c := by
      intro c hc
      induction hc with
      | refl => exact fun _ => ⟨u, huT, .refl, .refl⟩
      | @tail a b hprev hab ih =>
        intro hbT
        obtain ⟨g, hg, hgl⟩ := hab
        have haT : a ∈ T := by
          by_contra haT
          have hend : Ends G g a b := hgl
          exact hg.2 (hT.eq_of_ends hend.symm hbT haT)
        obtain ⟨y, hyT, hy, hyr⟩ := ih haT
        have hadj : G.AdjOn Set.univ a b := ⟨g, Set.mem_univ g, hgl⟩
        by_cases hdb : nodeDegree G b = 2
        · exact ⟨y, hyT, hy, hyr.tail ⟨hadj, hdb⟩⟩
        · by_cases hyb : y.1 = b
          · exact ⟨y, hyT, hy, hyb ▸ .refl⟩
          · refine ⟨⟨b, hdb⟩, hbT, hy.tail ?_, .refl⟩
            refine SimpleGraph.deleteEdges_adj.mpr ⟨(SimpleGraph.fromRel_adj _ _ _).mpr ⟨fun h => hyb (congrArg Subtype.val h),
              Or.inl ⟨a, hyr, hadj⟩⟩, ?_⟩
            simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or, not_and]
            refine ⟨fun _ hbw => hwT (hbw ▸ hbT), fun hyw => absurd (hyw ▸ hyT) hwT⟩
    obtain ⟨y, -, hy, hyr⟩ := key z.1 hwalk hz
    have : y = z := by
      rcases Relation.ReflTransGen.cases_tail hyr with h | ⟨c, -, -, hc⟩
      · exact Subtype.ext h.symm
      · exact absurd hc z.2
    exact this ▸ hy

/-- **Suppressing the nodes of degree 2 keeps the sides of the edges of a tree**, on labelled nodes of degree other than 2. -/
theorem hasSide_iff [Finite W] [Finite F] (hG : G.IsTree) (ℓ : X → {w // nodeDegree G w ≠ 2}) (A : Set X) :
    (LabelledGraph.mk (suppressDegreeTwo G) ℓ).HasSide A ↔
      ∃ e T, IsSideOf G e T ∧ (fun x => (ℓ x).1) ⁻¹' T = A := by
  constructor
  · rintro ⟨u, w, hadj, hA⟩
    obtain ⟨hne, hlink⟩ := (SimpleGraph.fromRel_adj _ _ _).mp hadj
    have hl : ChainLink G u.1 w.1 := hlink.elim id ChainLink.symm
    obtain ⟨z, hz, g, -, hg⟩ := hl
    have hends : Ends G g z w.1 := hg
    let T : Set W := {v | G.Walks {g}ᶜ z v}
    have hzT : z ∈ T := Relation.ReflTransGen.refl
    have hwT : w.1 ∉ T := by
      intro hw
      refine hG.2 g ?_
      rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂]
        exact hw
      · rw [h₁, h₂]
        exact G.walks_symm hw
    have hTs : IsSideOf G g T := by
      intro f
      constructor
      · intro hc
        by_contra hfg
        exact G.not_crosses_walk_component {g}ᶜ z (e := f) hfg hc
      · rintro rfl
        rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl ⟨h₁ ▸ hzT, h₂ ▸ hwT⟩
        · exact Or.inr ⟨h₂ ▸ hzT, h₁ ▸ hwT⟩
    -- the chain from `u` to `z` stays on the side of `z`
    have hchain : ∀ a, Relation.ReflTransGen (Enter G) a z → a ≠ w.1 → ChainIn G T z a := by
      intro a ha
      induction ha using Relation.ReflTransGen.head_induction_on with
      | refl => exact fun _ => .refl
      | @head a b hab _ ih =>
        intro haw
        have hbw : b ≠ w.1 := fun h => w.2 (h ▸ hab.2)
        have hb := ih hbw
        have hbT : b ∈ T := hb.mem_right hzT
        obtain ⟨f, -, hf⟩ := hab.1
        have hfne : f ≠ g := by
          rintro rfl
          have hf' : Ends G f a b := hf
          rcases hf' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hends with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
          · exact hbw (h₂.symm.trans h₄)
          · exact haw (h₁.symm.trans h₃)
          · exact haw (h₂.symm.trans h₄)
          · exact hbw (h₁.symm.trans h₃)
        have haT : a ∈ T := by
          have hf' : G.AdjOn {g}ᶜ b a := ⟨f, hfne, Or.symm hf⟩
          exact Relation.ReflTransGen.tail hbT hf'
        exact hb.tail ⟨G.adjOn_symm ⟨f, Set.mem_univ f, hf⟩, hab.2, hbT, haT⟩
    have huw : u.1 ≠ w.1 := fun h => hne (Subtype.ext h)
    refine ⟨g, T, hTs, ?_⟩
    ext y
    have hreach := reachable_iff hG hTs hends hzT hwT (u := u) (w := w) (hchain _ hz huw) .refl (ℓ y)
    exact (hreach.symm.trans (hA y).symm)
  · rintro ⟨e, T, hT, rfl⟩
    obtain ⟨x, q, hends, hx, hq⟩ : ∃ x q, Ends G e x q ∧ x ∈ T ∧ q ∉ T := by
      rcases hT.crosses with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, h₁, h₂⟩
      · exact ⟨_, _, Or.inr ⟨rfl, rfl⟩, h₁, h₂⟩
    obtain ⟨u, hu, hdu⟩ := exists_chainIn_end hG hT hends hx hq
    obtain ⟨w, hw, hdw⟩ := exists_chainIn_end hG hT.compl hends.symm hq (not_not.mpr hx)
    have huT : u ∈ T := hu.mem_right hx
    have hwT : w ∉ T := hw.mem_right hq
    -- the chain from `u` to `w`
    have hlink : ∀ a a', ChainIn G Tᶜ a w → G.AdjOn Set.univ a' a → Relation.ReflTransGen (Enter G) u a' →
        ChainLink G u w := by
      intro a a' ha
      induction ha using Relation.ReflTransGen.head_induction_on generalizing a' with
      | refl => exact fun hadj hr => ⟨a', hr, hadj⟩
      | @head a b hab _ ih =>
        intro hadj hr
        exact ih a hab.1 (hr.tail ⟨hadj, hab.2.1⟩)
    have hl : ChainLink G u w := hlink q x hw hends.adjOn hu.enter_rev
    have hne : (⟨u, hdu⟩ : {w // nodeDegree G w ≠ 2}) ≠ ⟨w, hdw⟩ := fun h => hwT (by
      have h' : u = w := congrArg Subtype.val h
      exact h' ▸ huT)
    refine ⟨⟨u, hdu⟩, ⟨w, hdw⟩, (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl hl⟩, fun y => ?_⟩
    exact (reachable_iff hG hT hends hx hq (u := ⟨u, hdu⟩) (w := ⟨w, hdw⟩) hu hw (ℓ y)).symm

end AllmanEtAl2023.TreeSuppression
