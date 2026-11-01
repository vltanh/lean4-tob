module

public import Gusfield2007.Blobs
public import Gusfield2007.NetworkOps

/-!
# Gusfield et al. 2007: recombination cycles and tree arcs of a network

General facts behind Sections 3.7 and 5.1, on any network: a site off a blob doesn't change along the blob; below a tree arc all of a site's states agree, and likewise off
it (the first sentences of the proof of Theorem 4, line 341); and the sides of a tree arc in `T′` are "below it" and "not below it".
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

namespace Network

universe u v w

variable {ι : Type u} {V : Type v} {E : Type w} (N : Network ι V E)

/-! ### Cycles and blobs -/

variable {N} in
theorem IsCycleOn.onCycle_left {w x : V} {p q : List E} (h : N.IsCycleOn w x p q) {e : E} (he : e ∈ p) : N.OnCycle e :=
  ⟨_, ⟨w, x, p, q, h, rfl⟩, Or.inl he⟩

variable {N} in
theorem IsCycleOn.onCycle_right {w x : V} {p q : List E} (h : N.IsCycleOn w x p q) {e : E} (he : e ∈ q) : N.OnCycle e :=
  ⟨_, ⟨w, x, p, q, h, rfl⟩, Or.inr he⟩

/-- A blob's arcs are on cycles. -/
theorem IsBlob.onCycle_of_mem {N : Network ι V E} {B : Set E} (hB : N.IsBlob B) {e : E} (he : e ∈ B) : N.OnCycle e := by
  obtain ⟨Q₀, hQ₀, rfl⟩ := hB
  obtain ⟨P, hP, heP⟩ := he
  refine ⟨P, ?_, heP⟩
  clear heP
  induction hP with
  | refl => exact hQ₀
  | tail _ h _ => exact h.2.1

section Finite

variable [Finite V]

variable {N} in
/-- The arcs into a recombination node are on cycles. -/
theorem onCycle_of_tgt_eq {e f : E} (hef : e ≠ f) (h : N.tgt e = N.tgt f) : N.OnCycle e := by
  obtain ⟨w, p, q, -, -, hc⟩ := exists_isCycleOn_of_tgt_eq hef h
  exact hc.onCycle_left (by simp)

variable {N} in
/-- The target of a tree arc isn't a recombination node. -/
theorem IsTreeArc.eq_of_tgt_eq {e f : E} (he : N.IsTreeArc e) (h : N.tgt f = N.tgt e) : f = e := by
  by_contra hne
  exact he (onCycle_of_tgt_eq (Ne.symm hne) h.symm)

variable {N} in
/-- The other arc into a recombination node is on the same blob. -/
theorem IsBlob.mem_of_tgt_eq {B : Set E} (hB : N.IsBlob B) {e f : E} (he : e ∈ B) (h : N.tgt e = N.tgt f) : f ∈ B := by
  by_cases hef : e = f
  · exact hef ▸ he
  · obtain ⟨w, p, q, -, -, hc⟩ := exists_isCycleOn_of_tgt_eq hef h
    exact hB.subset_of_mem ⟨_, _, _, _, hc, rfl⟩ he (Or.inl (by simp)) (Or.inr (by simp))

variable {N} in
/-- A recombination node is on a blob, with both of its entering arcs. -/
theorem exists_isBlob_of_tgt_eq {e f : E} (hef : e ≠ f) (h : N.tgt e = N.tgt f) : ∃ B, N.IsBlob B ∧ e ∈ B ∧ f ∈ B := by
  obtain ⟨B, hB, he⟩ := N.exists_isBlob_of_onCycle (onCycle_of_tgt_eq hef h)
  exact ⟨B, hB, he, hB.mem_of_tgt_eq he h⟩

variable {N} in
/-- **A site off a blob doesn't change along the blob**: both ends of each of its arcs have the same state. It's the fact the proof of
Theorem 4 uses for the sites off `C`, and Lemma 5's proof for the recombination nodes mapped to other components. -/
theorem IsBlob.label_src_eq_label_tgt {B : Set E} (hB : N.IsBlob B) {i : ι} (hi : N.site i ∉ B) {e : E} (he : e ∈ B) :
    N.label (N.src e) i = N.label (N.tgt e) i := by
  suffices key : ∀ z e, e ∈ B → N.tgt e = z → N.label (N.src e) i = N.label z i from key _ e he rfl
  intro z
  induction z using N.wellFounded_transGen.induction with
  | _ z ih =>
    intro e he hz
    subst hz
    by_cases huniq : ∀ f, N.tgt f = N.tgt e → f = e
    · have hne : N.site i ≠ e := fun h => hi (h ▸ he)
      rw [N.label_tree e huniq i]
      simp [hne]
    · push Not at huniq
      obtain ⟨f, hf, hfe⟩ := huniq
      have hef : e ≠ f := Ne.symm hfe
      obtain ⟨w, p, q, hp, hq, hc⟩ := exists_isCycleOn_of_tgt_eq hef hf.symm
      have hQ : N.IsCycle {g | g ∈ p ++ [e] ∨ g ∈ q ++ [f]} := ⟨_, _, _, _, hc, rfl⟩
      have hsub := hB.subset_of_mem hQ he (Or.inl (by simp))
      have hstep : ∀ {u v : V} {l : List E}, N.IsPath u v l → (∀ g ∈ l, g ∈ B) → N.Reach v (N.src e) ∨ N.Reach v (N.src f) →
          (N.label u i = N.label v i) := by
        intro u v l
        induction l generalizing u with
        | nil => intro h _ _; exact congrArg (N.label · i) h
        | cons g l ihl =>
          intro h hl hv
          obtain ⟨rfl, h₂⟩ := h
          have hg : g ∈ B := hl g List.mem_cons_self
          have hreach : N.Reach (N.tgt g) v := IsPath.reach h₂
          have hlt : Relation.TransGen N.Arc (N.tgt g) (N.tgt e) := by
            rcases hv with hv | hv
            · exact Relation.TransGen.tail' (hreach.trans hv) (arc_src_tgt e)
            · exact hf ▸ Relation.TransGen.tail' (hreach.trans hv) (arc_src_tgt f)
          rw [ih _ hlt g hg rfl]
          exact ihl h₂ (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) hv
      have h₁ : N.label w i = N.label (N.src e) i :=
        hstep hp (fun g hg => hsub (Or.inl (List.mem_append_left _ hg))) (Or.inl Relation.ReflTransGen.refl)
      have h₂ : N.label w i = N.label (N.src f) i :=
        hstep hq (fun g hg => hsub (Or.inr (List.mem_append_left _ hg))) (Or.inr Relation.ReflTransGen.refl)
      rcases N.label_recomb e f hef hf.symm i with h | h
      · exact h.symm
      · rw [h, ← h₂, h₁]

end Finite

/-! ### Criteria for a tree arc -/

/-- **A cut shows an arc is a tree arc.** If `D` is closed under arcs, and `e` is the only arc entering it, and the only arc into its target, then `e` is on no recombination cycle. -/
theorem isTreeArc_of_cut {N : Network ι V E} (D : V → Prop) {e : E} (ht : D (N.tgt e)) (hs : ¬ D (N.src e))
    (hout : ∀ f, D (N.src f) → D (N.tgt f)) (hin : ∀ f, D (N.tgt f) → ¬ D (N.src f) → f = e)
    (huniq : ∀ f, N.tgt f = N.tgt e → f = e) : N.IsTreeArc e := by
  have hclosed : ∀ {l : List E} {u v : V}, N.IsPath u v l → D u → D v := by
    intro l u v hp hu
    exact IsPath.rec_of_forall (P := D) hp (fun f _ h => hout f h) hu
  have hcross : ∀ {l : List E} {u v : V}, N.IsPath u v l → ¬ D u → D v → e ∈ l := by
    intro l
    induction l with
    | nil =>
      intro u v hp hu hv
      cases hp
      exact absurd hv hu
    | cons g l ih =>
      intro u v hp hu hv
      obtain ⟨rfl, h₂⟩ := hp
      by_cases hg : D (N.tgt g)
      · exact (hin g hg hu) ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h₂ hg hv)
  have hcloseReach : ∀ {u v : V}, N.Reach u v → D u → D v := by
    intro u v h hu
    obtain ⟨p, hp⟩ := Reach.exists_isPath h
    exact hclosed hp hu
  rintro ⟨Q, ⟨w, x, p, q, hc, rfl⟩, he⟩
  have hboth : e ∈ p ∧ e ∈ q := by
    rcases he with he | he
    · have hw : ¬ D w := fun h => hs (hcloseReach (hc.2.1.reach_src_of_mem he) h)
      exact ⟨he, hcross hc.2.2.1 hw (hcloseReach (hc.2.1.reach_tgt_of_mem he) ht)⟩
    · have hw : ¬ D w := fun h => hs (hcloseReach (hc.2.2.1.reach_src_of_mem he) h)
      exact ⟨hcross hc.2.1 hw (hcloseReach (hc.2.2.1.reach_tgt_of_mem he) ht), he⟩
  have hx : N.tgt e = x := hc.2.2.2.2 e hboth.1 e hboth.2 rfl
  obtain ⟨e₁, f₁, hne, he₁, hf₁⟩ := hc.1
  exact hne ((huniq e₁ (he₁.trans hx.symm)).trans (huniq f₁ (hf₁.trans hx.symm)).symm)

/-- **A criterion for a tree arc**: `g` is the only arc into its target, and the two arcs into each recombination node come from one node, by paths that avoid `g`. It's how a modification of a network is shown to keep its tree arcs. -/
theorem isTreeArc_of_forall_tgt_eq {N : Network ι V E} [Finite V] {g : E} (huniq : ∀ f, N.tgt f = N.tgt g → f = g)
    (h : ∀ f₁ f₂, f₁ ≠ f₂ → N.tgt f₁ = N.tgt f₂ → ∃ w p q, N.IsPath w (N.src f₁) p ∧ N.IsPath w (N.src f₂) q ∧ g ∉ p ∧ g ∉ q) : N.IsTreeArc g := by
  have hkey : ∀ z, N.Reach (N.tgt g) z → ∀ f, N.tgt f = z → f ≠ g → N.Reach (N.tgt g) (N.src f) := by
    intro z
    induction z using N.wellFounded_transGen.induction with
    | _ z ih =>
      intro hz f hf hfg
      subst hf
      rcases Relation.ReflTransGen.cases_tail hz with hz' | ⟨c, hc, f₀, rfl, hf₀⟩
      · exact absurd (huniq f hz') hfg
      · by_cases hff : f = f₀
        · rw [hff]
          exact hc
        · by_contra hnot
          obtain ⟨w, p, q, hp, hq, -, hgq⟩ := h f f₀ hff hf₀.symm
          have hw : ¬ N.Reach (N.tgt g) w := fun hr => hnot (hr.trans hp.reach)
          have hcross : ∀ {l : List E} {u v : V}, N.IsPath u v l → ¬ N.Reach (N.tgt g) u → N.Reach (N.tgt g) v → g ∉ l →
              (∀ k ∈ l, N.Reach (N.tgt k) (N.src f₀)) → False := by
            intro l
            induction l with
            | nil =>
              intro u v hl hu hv _ _
              cases hl
              exact hu hv
            | cons k l ihl =>
              intro u v hl hu hv hgl hreach
              obtain ⟨rfl, h₂⟩ := hl
              have hkg : k ≠ g := fun hk => hgl (hk ▸ List.mem_cons_self)
              by_cases hk : N.Reach (N.tgt g) (N.tgt k)
              · have hlt : Relation.TransGen N.Arc (N.tgt k) (N.tgt f) :=
                  hf₀ ▸ Relation.TransGen.tail' (hreach k List.mem_cons_self) (arc_src_tgt f₀)
                exact hu (ih _ hlt hk k rfl hkg)
              · exact ihl h₂ hk hv (fun hgl' => hgl (List.mem_cons_of_mem _ hgl'))
                  (fun k' hk' => hreach k' (List.mem_cons_of_mem _ hk'))
          exact hcross hq hw hc hgq fun k hk => hq.reach_tgt_of_mem hk
  refine isTreeArc_of_cut (N := N) (fun z => N.Reach (N.tgt g) z) Relation.ReflTransGen.refl (not_reach_tgt_src g)
    (fun f hf => hf.tail (arc_src_tgt f)) (fun f hf hs => ?_) huniq
  by_contra hne
  exact hs (hkey _ hf f rfl hne)

/-! ### The classes of `T′` -/

variable {N} in
theorem toBlobNode_eq_of_onCycle {e : E} (he : N.OnCycle e) : N.toBlobNode (N.src e) = N.toBlobNode (N.tgt e) :=
  Quotient.sound (Relation.EqvGen.rel _ _ ⟨e, he, rfl, rfl⟩)

/-- A property constant along the arcs on cycles is constant on classes of `T′`. -/
theorem eq_of_toBlobNode_eq {α : Type*} (g : V → α) (hg : ∀ e, N.OnCycle e → g (N.src e) = g (N.tgt e)) {u v : V}
    (h : N.toBlobNode u = N.toBlobNode v) : g u = g v := by
  have hr : Relation.EqvGen (fun u v => ∃ e, N.OnCycle e ∧ N.src e = u ∧ N.tgt e = v) u v := Quotient.exact h
  clear h
  induction hr with
  | rel _ _ hab =>
    obtain ⟨e, he, rfl, rfl⟩ := hab
    exact hg e he
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

variable {N} in
/-- A function that's constant along each arc of a cycle is constant on the cycle. -/
theorem IsCycleOn.eq_of_forall {α : Type*} {g : V → α} {w x : V} {p q : List E} (hc : N.IsCycleOn w x p q)
    (hg : ∀ h, (h ∈ p ∨ h ∈ q) → g (N.src h) = g (N.tgt h)) {e : E} (he : e ∈ p ∨ e ∈ q) :
    g (N.src e) = g w ∧ g (N.tgt e) = g w := by
  have key : ∀ {l : List E} {u v : V}, N.IsPath u v l → (∀ h ∈ l, g (N.src h) = g (N.tgt h)) → ∀ h ∈ l,
      g (N.src h) = g u ∧ g (N.tgt h) = g u := by
    intro l
    induction l with
    | nil => intro _ _ _ _ h hh; exact absurd hh (by simp)
    | cons a l ih =>
      intro u v hp hl h hh
      obtain ⟨rfl, h₂⟩ := hp
      have ha := hl a List.mem_cons_self
      rcases List.mem_cons.1 hh with rfl | hh
      · exact ⟨rfl, ha.symm⟩
      · have := ih h₂ (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) h hh
        exact ⟨this.1.trans ha.symm, this.2.trans ha.symm⟩
  rcases he with he | he
  · exact key hc.2.1 (fun h hh => hg h (Or.inl hh)) e he
  · exact key hc.2.2.1 (fun h hh => hg h (Or.inr hh)) e he

variable {N} in
/-- A function that's constant along each arc of a blob is constant on the blob. -/
theorem IsBlob.eq_of_forall_mem {α : Type*} {g : V → α} {B : Set E} (hB : N.IsBlob B) (hg : ∀ e ∈ B, g (N.src e) = g (N.tgt e))
    {u v : V} (hu : u ∈ N.blobVerts B) (hv : v ∈ N.blobVerts B) : g u = g v := by
  obtain ⟨Q₀, hQ₀, rfl⟩ := hB
  obtain ⟨w₀, x₀, p₀, q₀, hc₀, hQ₀'⟩ := id hQ₀
  subst hQ₀'
  set B := ⋃₀ {Q' | Relation.ReflTransGen N.ShareArc {g | g ∈ p₀ ∨ g ∈ q₀} Q'} with hBdef
  have key : ∀ P, Relation.ReflTransGen N.ShareArc {g | g ∈ p₀ ∨ g ∈ q₀} P → ∀ a ∈ P,
      g (N.src a) = g w₀ ∧ g (N.tgt a) = g w₀ := by
    intro P hP
    induction hP with
    | refl => exact fun a ha => hc₀.eq_of_forall (fun h hh => hg h ⟨_, Relation.ReflTransGen.refl, hh⟩) ha
    | @tail P₁ P₂ hP₁ hs ih =>
      obtain ⟨-, ⟨w, x, p, q, hc, rfl⟩, a₀, ha₀, ha₀'⟩ := hs
      have hinB : ∀ h, (h ∈ p ∨ h ∈ q) → g (N.src h) = g (N.tgt h) := fun h hh =>
        hg h ⟨_, hP₁.tail ⟨(by
          clear ih ha₀
          induction hP₁ with
          | refl => exact ⟨w₀, x₀, p₀, q₀, hc₀, rfl⟩
          | tail _ h' _ => exact h'.2.1), ⟨w, x, p, q, hc, rfl⟩, a₀, ha₀, ha₀'⟩, hh⟩
      intro a ha
      have h₁ := hc.eq_of_forall hinB ha
      have h₂ := hc.eq_of_forall hinB ha₀'
      have h₃ := ih a₀ ha₀
      exact ⟨h₁.1.trans (h₂.1.symm.trans h₃.1), h₁.2.trans (h₂.1.symm.trans h₃.1)⟩
  have hend : ∀ {z}, z ∈ N.blobVerts B → g z = g w₀ := by
    rintro z (⟨a, ⟨P, hP, ha⟩, rfl⟩ | ⟨a, ⟨P, hP, ha⟩, rfl⟩)
    · exact (key P hP a ha).1
    · exact (key P hP a ha).2
  exact (hend hu).trans (hend hv).symm

variable {N} in
/-- All the nodes of a blob are in one class of `T′`: "a blob" is contracted "to a single point". -/
theorem IsBlob.toBlobNode_eq {B : Set E} (hB : N.IsBlob B) {u v : V} (hu : u ∈ N.blobVerts B) (hv : v ∈ N.blobVerts B) :
    N.toBlobNode u = N.toBlobNode v :=
  hB.eq_of_forall_mem (fun _ he => toBlobNode_eq_of_onCycle (hB.onCycle_of_mem he)) hu hv

variable {N} in
/-- The ends of an arc of a blob are on the blob. -/
theorem src_mem_blobVerts {B : Set E} {e : E} (he : e ∈ B) : N.src e ∈ N.blobVerts B := Or.inl ⟨e, he, rfl⟩

variable {N} in
theorem tgt_mem_blobVerts {B : Set E} {e : E} (he : e ∈ B) : N.tgt e ∈ N.blobVerts B := Or.inr ⟨e, he, rfl⟩

variable {N} in
/-- With blobs node-disjoint, the classes of `T′` are the blobs' nodes and singletons (the reading in `Gusfield2007.Defs`). -/
theorem eq_or_exists_isBlob_of_toBlobNode_eq (hd : N.BlobsNodeDisjoint) [Finite V] {u v : V}
    (h : N.toBlobNode u = N.toBlobNode v) : u = v ∨ ∃ B, N.IsBlob B ∧ u ∈ N.blobVerts B ∧ v ∈ N.blobVerts B := by
  have hr : Relation.EqvGen (fun u v => ∃ e, N.OnCycle e ∧ N.src e = u ∧ N.tgt e = v) u v := Quotient.exact h
  clear h
  induction hr with
  | rel _ _ hab =>
    obtain ⟨e, he, rfl, rfl⟩ := hab
    obtain ⟨B, hB, heB⟩ := N.exists_isBlob_of_onCycle he
    exact Or.inr ⟨B, hB, src_mem_blobVerts heB, tgt_mem_blobVerts heB⟩
  | refl => exact Or.inl rfl
  | symm _ _ _ ih =>
    rcases ih with rfl | ⟨B, hB, h₁, h₂⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨B, hB, h₂, h₁⟩
  | trans _ _ _ _ _ ih₁ ih₂ =>
    rcases ih₁ with rfl | ⟨B, hB, h₁, h₂⟩
    · exact ih₂
    · rcases ih₂ with rfl | ⟨B', hB', h₃, h₄⟩
      · exact Or.inr ⟨B, hB, h₁, h₂⟩
      · by_cases hBB : B = B'
        · subst hBB
          exact Or.inr ⟨B, hB, h₁, h₄⟩
        · exact absurd h₃ (Set.disjoint_left.1 (hd B B' hB hB' hBB) h₂)

/-! ### Tree arcs -/

section TreeArcs

variable {N} [Finite V] [Finite E]

/-- **The only arc entering what's below a tree arc is that arc.** This is why removing a tree arc makes "two disconnected subnetworks"
(line 342). The proof is through `isTreeArc_iff_isBridge`. -/
theorem IsTreeArc.reach_src_of_reach_tgt {e f : E} (he : N.IsTreeArc e) (hfe : f ≠ e) (h : N.Reach (N.tgt e) (N.tgt f)) :
    N.Reach (N.tgt e) (N.src f) := by
  by_contra hsrc
  have hb := (N.isTreeArc_iff_isBridge e).1 he
  rw [SimpleGraph.isBridge_iff] at hb
  set G' := N.underlying.deleteEdges {s(N.src e, N.tgt e)} with hG'
  have hstep : ∀ g : E, s(N.src g, N.tgt g) ≠ s(N.src e, N.tgt e) → G'.Reachable (N.src g) (N.tgt g) := by
    intro g hg
    refine SimpleGraph.Adj.reachable ?_
    rw [hG', SimpleGraph.deleteEdges_adj]
    refine ⟨?_, by simpa using hg⟩
    rw [underlying, SimpleGraph.fromRel_adj]
    exact ⟨src_ne_tgt g, Or.inl (arc_src_tgt g)⟩
  have hrev : ∀ g : E, ¬ (N.src g = N.tgt e ∧ N.tgt g = N.src e) := by
    rintro g ⟨h₁, h₂⟩
    exact not_reach_tgt_src e (h₁ ▸ h₂ ▸ reach_src_tgt g)
  have h₁ : ∀ {a b}, N.Reach a b → ¬ N.Reach a (N.src e) → G'.Reachable a b := by
    intro a b hab ha
    induction hab with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b' b hab' harc ih =>
      obtain ⟨g, rfl, rfl⟩ := harc
      refine ih.trans (hstep g fun hg => ?_)
      rcases Sym2.eq_iff.1 hg with ⟨h₃, -⟩ | h₃
      · exact ha (h₃ ▸ hab')
      · exact hrev g h₃
  have h₂ : ∀ {a b}, N.Reach a b → ¬ N.Reach (N.tgt e) b → G'.Reachable a b := by
    intro a b hab hb'
    induction hab with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b' b hab' harc ih =>
      obtain ⟨g, rfl, rfl⟩ := harc
      refine (ih fun h' => hb' (h'.tail (arc_src_tgt g))).trans (hstep g fun hg => ?_)
      rcases Sym2.eq_iff.1 hg with ⟨-, h₃⟩ | h₃
      · exact hb' (h₃ ▸ Relation.ReflTransGen.refl)
      · exact hrev g h₃
  have hf : G'.Reachable (N.src f) (N.tgt f) := hstep f fun hg => by
    rcases Sym2.eq_iff.1 hg with ⟨h₃, h₄⟩ | h₃
    · exact hfe (N.simple _ _ h₃ h₄)
    · exact hrev f h₃
  exact hb (((h₂ (N.reach_root _) (not_reach_tgt_src e)).symm.trans (h₂ (N.reach_root _) hsrc)).trans
    (hf.trans (h₁ h (not_reach_tgt_src e)).symm))

omit [Finite E] in
/-- A site whose arc is below `z` has its ancestral state off what's below `z`. -/
theorem label_eq_root_of_not_reach {z : V} {i : ι} (h : N.Reach z (N.tgt (N.site i))) {t : V} (ht : ¬ N.Reach z t) :
    N.label t i = N.label N.root i := by
  by_contra hne
  exact ht (h.trans (N.reach_of_label_ne hne))

/-- **Line 341.** "In the subnetwork reached from `v′`, all of the sites in `C` have the same state they have at `v′`": below a tree arc, a site
with no arc strictly below it has one state. -/
theorem IsTreeArc.label_eq_of_reach {e : E} (he : N.IsTreeArc e) {i : ι}
    (hi : N.site i = e ∨ ¬ N.Reach (N.tgt e) (N.tgt (N.site i))) {t : V} (ht : N.Reach (N.tgt e) t) :
    N.label t i = N.label (N.tgt e) i := by
  induction t using N.wellFounded_transGen.induction with
  | _ t ih =>
    rcases Relation.ReflTransGen.cases_tail ht with rfl | ⟨c, hc, g, rfl, rfl⟩
    · rfl
    · by_cases hz : N.tgt g = N.tgt e
      · rw [hz]
      · have hge : g ≠ e := fun h => hz (h ▸ rfl)
        by_cases huniq : ∀ f, N.tgt f = N.tgt g → f = g
        · have hne : N.site i ≠ g := by
            intro hs
            rcases hi with hi | hi
            · exact hge (hs.symm.trans hi)
            · exact hi (hs ▸ ht)
          rw [N.label_tree g huniq i]
          simp only [hne, ite_false]
          exact ih _ (Relation.TransGen.single (arc_src_tgt g)) hc
        · push Not at huniq
          obtain ⟨f, hf, hfg⟩ := huniq
          have hfe : f ≠ e := fun h => hz (by rw [← hf, h])
          have hc' : N.Reach (N.tgt e) (N.src f) := he.reach_src_of_reach_tgt hfe (hf ▸ ht)
          rcases N.label_recomb g f (Ne.symm hfg) hf.symm i with h' | h'
          · rw [h']
            exact ih _ (Relation.TransGen.single (arc_src_tgt g)) hc
          · rw [h']
            exact ih _ (hf ▸ Relation.TransGen.single (arc_src_tgt f)) hc'

omit [Finite E] in
/-- The arc `e` doesn't change the site `i`, if `i` isn't on it. -/
theorem IsTreeArc.label_tgt_eq_src {e : E} (he : N.IsTreeArc e) {i : ι} (hi : N.site i ≠ e) :
    N.label (N.tgt e) i = N.label (N.src e) i := by
  rw [N.label_tree e (fun _ h => he.eq_of_tgt_eq h) i]
  simp [hi]

omit [Finite E] in
/-- The arc `e` changes the sites on it. -/
theorem IsTreeArc.label_tgt_of_site_eq {e : E} (he : N.IsTreeArc e) {i : ι} (hi : N.site i = e) :
    N.label (N.tgt e) i = !N.label (N.src e) i := by
  rw [N.label_tree e (fun _ h => he.eq_of_tgt_eq h) i]
  simp [hi]

/-! ### The sides of a tree arc in `T′` -/

theorem blobbedTree_adj {e : E} (he : N.IsTreeArc e) : N.blobbedTree.Adj (N.toBlobNode (N.src e)) (N.toBlobNode (N.tgt e)) := by
  rw [blobbedTree, SimpleGraph.fromRel_adj]
  exact ⟨N.blobbedTree_isTree.2.1 e he, Or.inl ⟨e, he, rfl, rfl⟩⟩

omit [Finite V] [Finite E] in
/-- Each edge of `T′` comes from a tree arc. -/
theorem exists_isTreeArc_of_adj {a b : N.BlobNode} (h : N.blobbedTree.Adj a b) :
    ∃ e, N.IsTreeArc e ∧ s(N.toBlobNode (N.src e), N.toBlobNode (N.tgt e)) = s(a, b) := by
  rw [blobbedTree, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨e, he, rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩
  · exact ⟨e, he, rfl⟩
  · exact ⟨e, he, Sym2.eq_swap⟩

variable (N) in
/-- The edge of `T′` of an arc. -/
def blobEdge (e : E) : Sym2 N.BlobNode := s(N.toBlobNode (N.src e), N.toBlobNode (N.tgt e))

theorem blobEdge_mem_edgeSet {e : E} (he : N.IsTreeArc e) : N.blobEdge e ∈ N.blobbedTree.edgeSet :=
  blobbedTree_adj he

theorem blobEdge_injective {e f : E} (he : N.IsTreeArc e) (hf : N.IsTreeArc f) (h : N.blobEdge e = N.blobEdge f) : e = f := by
  have := N.blobbedTree_isTree.2.2.1 (a₁ := ⟨e, he⟩) (a₂ := ⟨f, hf⟩) h
  exact congrArg Subtype.val this

/-- An arc other than the tree arc `e` doesn't leave its side of `e` in `T′`. -/
theorem sameSide_of_ne {e g : E} (he : N.IsTreeArc e) (hg : g ≠ e) :
    SameSide N.blobbedTree (N.blobEdge e) (N.toBlobNode (N.src g)) (N.toBlobNode (N.tgt g)) := by
  by_cases hgc : N.OnCycle g
  · rw [toBlobNode_eq_of_onCycle hgc]
    exact SimpleGraph.Reachable.refl _
  · refine SimpleGraph.Adj.reachable ?_
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨blobbedTree_adj hgc, fun h => hg (blobEdge_injective hgc he (Set.mem_singleton_iff.1 h))⟩

theorem sameSide_of_reach_of_not_reach_left {e : E} (he : N.IsTreeArc e) {a b : V} (hab : N.Reach a b)
    (ha : ¬ N.Reach a (N.src e)) : SameSide N.blobbedTree (N.blobEdge e) (N.toBlobNode a) (N.toBlobNode b) := by
  induction hab with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b' b hab' harc ih =>
    obtain ⟨g, rfl, rfl⟩ := harc
    exact SimpleGraph.Reachable.trans ih (sameSide_of_ne he fun h => ha (h ▸ hab'))

theorem sameSide_of_reach_of_not_reach_right {e : E} (he : N.IsTreeArc e) {a b : V} (hab : N.Reach a b)
    (hb : ¬ N.Reach (N.tgt e) b) : SameSide N.blobbedTree (N.blobEdge e) (N.toBlobNode a) (N.toBlobNode b) := by
  induction hab with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b' b hab' harc ih =>
    obtain ⟨g, rfl, rfl⟩ := harc
    exact SimpleGraph.Reachable.trans (ih fun h => hb (h.tail (arc_src_tgt g)))
      (sameSide_of_ne he fun h => hb (h ▸ Relation.ReflTransGen.refl))

/-- The two ends of a tree arc are on different sides of it in `T′`. -/
theorem IsTreeArc.not_sameSide {e : E} (he : N.IsTreeArc e) :
    ¬ SameSide N.blobbedTree (N.blobEdge e) (N.toBlobNode (N.src e)) (N.toBlobNode (N.tgt e)) :=
  SimpleGraph.isBridge_iff.1 (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 N.blobbedTree_isTree.1.isAcyclic (blobbedTree_adj he))

/-- What's on the side of `e`'s target in `T′` is what's reached from `e`'s target in `N`. -/
theorem IsTreeArc.sameSide_tgt_iff {e : E} (he : N.IsTreeArc e) (t : V) :
    SameSide N.blobbedTree (N.blobEdge e) (N.toBlobNode (N.tgt e)) (N.toBlobNode t) ↔ N.Reach (N.tgt e) t := by
  constructor
  · intro h
    by_contra hr
    have h₁ := sameSide_of_reach_of_not_reach_right he (N.reach_root t) hr
    have h₂ := sameSide_of_reach_of_not_reach_right he (N.reach_root (N.src e)) (not_reach_tgt_src e)
    exact he.not_sameSide (SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm h₂)
      (SimpleGraph.Reachable.trans h₁ (SimpleGraph.Reachable.symm h)))
  · intro h
    exact sameSide_of_reach_of_not_reach_left he h (not_reach_tgt_src e)

/-- What's on the side of `e`'s source in `T′` is what isn't reached from `e`'s target in `N`. -/
theorem IsTreeArc.sameSide_src_iff {e : E} (he : N.IsTreeArc e) (t : V) :
    SameSide N.blobbedTree (N.blobEdge e) (N.toBlobNode (N.src e)) (N.toBlobNode t) ↔ ¬ N.Reach (N.tgt e) t := by
  constructor
  · intro h hr
    exact he.not_sameSide (SimpleGraph.Reachable.trans h
      (SimpleGraph.Reachable.symm ((he.sameSide_tgt_iff t).2 hr)))
  · intro hr
    have h₁ := sameSide_of_reach_of_not_reach_right he (N.reach_root t) hr
    have h₂ := sameSide_of_reach_of_not_reach_right he (N.reach_root (N.src e)) (not_reach_tgt_src e)
    exact SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm h₂) h₁

/-- Whether a node is below a tree arc depends only on its class in `T′`. -/
theorem IsTreeArc.reach_iff_of_toBlobNode_eq {e : E} (he : N.IsTreeArc e) {t t' : V} (h : N.toBlobNode t = N.toBlobNode t') :
    N.Reach (N.tgt e) t ↔ N.Reach (N.tgt e) t' := by
  rw [← he.sameSide_tgt_iff, ← he.sameSide_tgt_iff, h]

end TreeArcs

/-! ### The tops and exits of a blob -/

section Exits

/-- The node `w` is the top of the blob `B`: it's on the blob, and no arc of the blob enters it. The label of the top on the sites of the blob is the blob's
ancestral super-character. -/
def IsBlobTop (B : Set E) (w : V) : Prop := w ∈ N.blobVerts B ∧ ∀ e ∈ B, N.tgt e ≠ w

variable {N} [Finite V]

/-- Every node of a blob has a top above it. -/
theorem exists_isBlobTop_reach {B : Set E} {z : V} (hz : z ∈ N.blobVerts B) : ∃ w, N.IsBlobTop B w ∧ N.Reach w z := by
  induction z using N.wellFounded_transGen.induction with
  | _ z ih =>
    by_cases h : ∃ e ∈ B, N.tgt e = z
    · obtain ⟨e, he, rfl⟩ := h
      obtain ⟨w, hw, hr⟩ := ih (N.src e) (Relation.TransGen.single (arc_src_tgt e)) (src_mem_blobVerts he)
      exact ⟨w, hw, hr.tail (arc_src_tgt e)⟩
    · push Not at h
      exact ⟨z, ⟨hz, h⟩, Relation.ReflTransGen.refl⟩

/-- A site off a blob has one state on the blob. -/
theorem IsBlob.label_eq_of_notMem {B : Set E} (hB : N.IsBlob B) {j : ι} (hj : N.site j ∉ B) {u v : V} (hu : u ∈ N.blobVerts B)
    (hv : v ∈ N.blobVerts B) : N.label u j = N.label v j :=
  hB.eq_of_forall_mem (g := fun z => N.label z j) (fun _ he => hB.label_src_eq_label_tgt hj he) hu hv

omit [Finite V] in
/-- A node of a blob with no arc on a cycle leaving it is a recombination node: it's the end of each cycle through it. -/
theorem IsBlob.isRecomb_of_forall {B : Set E} (hB : N.IsBlob B) {l : V} (hl : l ∈ N.blobVerts B) (hout : ∀ f, N.src f = l → ¬ N.OnCycle f) :
    N.IsRecomb l := by
  have hnext : ∀ {a : List E} {u v : V}, N.IsPath u v a → ∀ e ∈ a, N.tgt e ≠ v → ∃ f ∈ a, N.src f = N.tgt e := by
    intro a
    induction a with
    | nil => intro _ _ _ e he; exact absurd he (by simp)
    | cons g a ih =>
      intro u v hp e he hne
      obtain ⟨rfl, h₂⟩ := hp
      rcases List.mem_cons.1 he with rfl | he
      · cases a with
        | nil => exact absurd h₂ hne
        | cons f a => exact ⟨f, by simp, h₂.1⟩
      · obtain ⟨f, hf, h⟩ := ih h₂ e he hne
        exact ⟨f, List.mem_cons_of_mem _ hf, h⟩
  rcases hl with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · exact absurd (hB.onCycle_of_mem he) (hout e rfl)
  · obtain ⟨Q, ⟨w, x, p, q, hc, rfl⟩, heQ⟩ := hB.onCycle_of_mem he
    by_cases hx : N.tgt e = x
    · exact hx ▸ hc.1
    · rcases heQ with h | h
      · obtain ⟨f, hf, hsrc⟩ := hnext hc.2.1 e h hx
        exact absurd (hc.onCycle_left hf) (hout f hsrc)
      · obtain ⟨f, hf, hsrc⟩ := hnext hc.2.2.1 e h hx
        exact absurd (hc.onCycle_right hf) (hout f hsrc)

omit [Finite V] in
/-- A leaf on a blob is a recombination node. -/
theorem IsBlob.isRecomb_of_isLeaf {B : Set E} (hB : N.IsBlob B) {l : V} (hl : l ∈ N.blobVerts B) (hleaf : N.IsLeaf l) : N.IsRecomb l :=
  hB.isRecomb_of_forall hl fun f hf => absurd hf (hleaf f)

variable [Finite E]

/-- A tree arc doesn't have both ends on a blob. -/
theorem IsTreeArc.tgt_notMem_blobVerts {e : E} (he : N.IsTreeArc e) {B : Set E} (hB : N.IsBlob B) (hs : N.src e ∈ N.blobVerts B) :
    N.tgt e ∉ N.blobVerts B := fun ht =>
  N.blobbedTree_isTree.2.1 e he (hB.toBlobNode_eq hs ht)

/-- A tree arc doesn't have both ends on a blob. -/
theorem IsTreeArc.src_notMem_blobVerts {e : E} (he : N.IsTreeArc e) {B : Set E} (hB : N.IsBlob B) (ht : N.tgt e ∈ N.blobVerts B) :
    N.src e ∉ N.blobVerts B := fun hs =>
  N.blobbedTree_isTree.2.1 e he (hB.toBlobNode_eq hs ht)

omit [Finite V] [Finite E] in
/-- With blobs node-disjoint, an arc at a node of a blob that isn't an arc of the blob is a tree arc. -/
theorem isTreeArc_of_notMem (hnd : N.BlobsNodeDisjoint) {B : Set E} (hB : N.IsBlob B) {e : E}
    (hv : N.src e ∈ N.blobVerts B ∨ N.tgt e ∈ N.blobVerts B) (he : e ∉ B) : N.IsTreeArc e := by
  intro hc
  obtain ⟨B', hB', heB'⟩ := N.exists_isBlob_of_onCycle hc
  have hBB : B = B' := by
    by_contra hne
    rcases hv with hv | hv
    · exact Set.disjoint_left.1 (hnd B B' hB hB' hne) hv (src_mem_blobVerts heB')
    · exact Set.disjoint_left.1 (hnd B B' hB hB' hne) hv (tgt_mem_blobVerts heB')
  exact he (hBB ▸ heB')

omit [Finite V] [Finite E] in
/-- An arc leaving a blob is a tree arc. -/
theorem isTreeArc_of_exit (hnd : N.BlobsNodeDisjoint) {B : Set E} (hB : N.IsBlob B) {e : E} (hs : N.src e ∈ N.blobVerts B)
    (ht : N.tgt e ∉ N.blobVerts B) : N.IsTreeArc e :=
  isTreeArc_of_notMem hnd hB (Or.inl hs) fun he => ht (tgt_mem_blobVerts he)

omit [Finite V] [Finite E] in
/-- The top of a blob is the root, or the target of a tree arc. -/
theorem IsBlobTop.eq_root_or_exists (hnd : N.BlobsNodeDisjoint) {B : Set E} (hB : N.IsBlob B) {w : V} (hw : N.IsBlobTop B w) :
    w = N.root ∨ ∃ g, N.IsTreeArc g ∧ N.tgt g = w := by
  by_cases h : w = N.root
  · exact Or.inl h
  · right
    have hex : ∃ g, N.tgt g = w := by
      by_contra hne
      push Not at hne
      exact h ((N.root_iff w).1 hne)
    obtain ⟨g, hg⟩ := hex
    exact ⟨g, isTreeArc_of_notMem hnd hB (Or.inr (hg ▸ hw.1)) (fun hgB => hw.2 g hgB hg), hg⟩

/-- A tree arc into a blob enters at its top. So the tree arc into a blob is unique, and the top is unique. -/
theorem IsTreeArc.tgt_eq_of_isBlobTop (hnd : N.BlobsNodeDisjoint) {B : Set E} (hB : N.IsBlob B) {g : E} (hg : N.IsTreeArc g)
    (ht : N.tgt g ∈ N.blobVerts B) {w : V} (hw : N.IsBlobTop B w) : N.tgt g = w := by
  have hcls : N.toBlobNode (N.tgt g) = N.toBlobNode w := hB.toBlobNode_eq ht hw.1
  have hne : N.toBlobNode (N.tgt g) ≠ N.toBlobNode N.root := N.blobbedTree_isTree.2.2.2.1 g hg
  rcases hw.eq_root_or_exists hnd hB with rfl | ⟨g₀, hg₀, rfl⟩
  · exact absurd hcls hne
  · obtain ⟨e, -, hu⟩ := N.blobbedTree_isTree.2.2.2.2 _ hne
    have h₁ := hu ⟨g, hg⟩ rfl
    have h₂ := hu ⟨g₀, hg₀⟩ hcls.symm
    rw [show g = g₀ from congrArg Subtype.val (h₁.trans h₂.symm)]

/-- The top of a blob is unique. -/
theorem IsBlobTop.unique (hnd : N.BlobsNodeDisjoint) {B : Set E} (hB : N.IsBlob B) {w w' : V} (hw : N.IsBlobTop B w) (hw' : N.IsBlobTop B w') :
    w = w' := by
  rcases hw.eq_root_or_exists hnd hB with rfl | ⟨g, hg, rfl⟩
  · rcases hw'.eq_root_or_exists hnd hB with h | ⟨g, hg, rfl⟩
    · exact h.symm
    · exact (hg.tgt_eq_of_isBlobTop hnd hB hw'.1 hw).symm
  · exact hg.tgt_eq_of_isBlobTop hnd hB hw.1 hw'

/-- All of a blob is below its top. -/
theorem IsBlobTop.reach (hnd : N.BlobsNodeDisjoint) {B : Set E} (hB : N.IsBlob B) {w z : V} (hw : N.IsBlobTop B w) (hz : z ∈ N.blobVerts B) :
    N.Reach w z := by
  obtain ⟨w', hw', hr⟩ := exists_isBlobTop_reach hz
  rwa [hw.unique hnd hB hw']

/-- What's below the top of a blob is on the blob, or below a tree arc leaving it. -/
theorem IsBlobTop.position (hnd : N.BlobsNodeDisjoint) {B : Set E} (hB : N.IsBlob B) {w t : V} (hw : N.IsBlobTop B w) (h : N.Reach w t) :
    t ∈ N.blobVerts B ∨ ∃ e, N.IsTreeArc e ∧ N.src e ∈ N.blobVerts B ∧ N.tgt e ∉ N.blobVerts B ∧ N.Reach (N.tgt e) t := by
  induction h with
  | refl => exact Or.inl hw.1
  | @tail t t' _ harc ih =>
    obtain ⟨g, rfl, rfl⟩ := harc
    rcases ih with ih | ⟨e, he₁, he₂, he₃, he₄⟩
    · by_cases hg : g ∈ B
      · exact Or.inl (tgt_mem_blobVerts hg)
      · have hgt := isTreeArc_of_notMem hnd hB (Or.inl ih) hg
        exact Or.inr ⟨g, hgt, ih, hgt.tgt_notMem_blobVerts hB ih, Relation.ReflTransGen.refl⟩
    · exact Or.inr ⟨e, he₁, he₂, he₃, he₄.tail (arc_src_tgt g)⟩

/-- **Off the blob, a site of the blob has the state it has at the top of the blob**: "no site in `C` mutates outside of `b_C`". -/
theorem IsBlobTop.label_eq_of_not_reach (hnd : N.BlobsNodeDisjoint) {B : Set E} (hB : N.IsBlob B) {w t : V} (hw : N.IsBlobTop B w) {i : ι}
    (hi : N.site i ∈ B) (ht : ¬ N.Reach w t) : N.label t i = N.label w i := by
  have hr : N.Reach w (N.tgt (N.site i)) := hw.reach hnd hB (tgt_mem_blobVerts hi)
  rcases hw.eq_root_or_exists hnd hB with rfl | ⟨g, hg, rfl⟩
  · exact label_eq_root_of_not_reach hr ht
  · have hne : N.site i ≠ g := fun h => hg (hB.onCycle_of_mem (h ▸ hi))
    rw [label_eq_root_of_not_reach hr ht, hg.label_tgt_eq_src hne,
      label_eq_root_of_not_reach hr (not_reach_tgt_src g)]

/-- **Line 341.** Below a tree arc leaving a blob, the sites of the blob have the state they have at the source of the arc. -/
theorem IsBlob.label_eq_of_exit {B : Set E} (hB : N.IsBlob B) {e : E} (he : N.IsTreeArc e) (hs : N.src e ∈ N.blobVerts B) {i : ι} (hi : N.site i ∈ B)
    {t : V} (ht : N.Reach (N.tgt e) t) : N.label t i = N.label (N.src e) i := by
  have hne : N.site i ≠ e := fun h => he (hB.onCycle_of_mem (h ▸ hi))
  have hr : ¬ N.Reach (N.tgt e) (N.tgt (N.site i)) := fun h =>
    not_reach_tgt_src e ((he.reach_iff_of_toBlobNode_eq (hB.toBlobNode_eq (tgt_mem_blobVerts hi) hs)).1 h)
  rw [he.label_eq_of_reach (Or.inr hr) ht, he.label_tgt_eq_src hne]

/-- **The sequence of a blob's sites is constant on the side of a tree arc away from the blob.** This is why `T′` and `T̄` have a common refinement. -/
theorem IsTreeArc.label_eq_of_sameSide {e : E} (he : N.IsTreeArc e) {B : Set E} (hB : N.IsBlob B) {t : V} (ht : t ∈ N.blobVerts B) {i : ι} (hi : N.site i ∈ B)
    {x y : V} (hxy : SameSide N.blobbedTree (N.blobEdge e) (N.toBlobNode x) (N.toBlobNode y))
    (hxt : ¬ SameSide N.blobbedTree (N.blobEdge e) (N.toBlobNode x) (N.toBlobNode t)) : N.label x i = N.label y i := by
  have hclass : N.toBlobNode (N.tgt (N.site i)) = N.toBlobNode t := hB.toBlobNode_eq (tgt_mem_blobVerts hi) ht
  by_cases hbelow : N.Reach (N.tgt e) t
  · have hr : N.Reach (N.tgt e) (N.tgt (N.site i)) := (he.reach_iff_of_toBlobNode_eq hclass).2 hbelow
    have htside := (he.sameSide_tgt_iff t).2 hbelow
    have hx : ¬ N.Reach (N.tgt e) x := fun h =>
      hxt (SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm ((he.sameSide_tgt_iff x).2 h)) htside)
    have hy : ¬ N.Reach (N.tgt e) y := fun h =>
      hxt (SimpleGraph.Reachable.trans hxy (SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm ((he.sameSide_tgt_iff y).2 h)) htside))
    rw [label_eq_root_of_not_reach hr hx, label_eq_root_of_not_reach hr hy]
  · have hr : ¬ N.Reach (N.tgt e) (N.tgt (N.site i)) := fun h => hbelow ((he.reach_iff_of_toBlobNode_eq hclass).1 h)
    have htside := (he.sameSide_src_iff t).2 hbelow
    have hx : N.Reach (N.tgt e) x := by
      by_contra h
      exact hxt (SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm ((he.sameSide_src_iff x).2 h)) htside)
    have hy : N.Reach (N.tgt e) y := by
      by_contra h
      exact hxt (SimpleGraph.Reachable.trans hxy (SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm ((he.sameSide_src_iff y).2 h)) htside))
    rw [he.label_eq_of_reach (Or.inr hr) hx, he.label_eq_of_reach (Or.inr hr) hy]

end Exits

end Network

end Gusfield2007
