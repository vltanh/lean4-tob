module

public import Gusfield2007.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Powerset

/-!
# Gusfield et al. 2007, Section 2.1: recombination cycles and blobs

Blobs are well defined; arcs on no recombination cycle are the bridges (with the two paths lemma
`Network.exists_isCycleOn_of_paths`); the contraction of the blobs is a directed tree; blobs can be made node-disjoint.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

namespace Network

universe u v w

variable {ι : Type u} {V : Type v} {E : Type w} (N : Network ι V E)

/-- An arc on a cycle is on a blob. -/
theorem exists_isBlob_of_onCycle {e : E} (he : N.OnCycle e) : ∃ B, N.IsBlob B ∧ e ∈ B := by
  obtain ⟨Q, hQ, heQ⟩ := he
  exact ⟨_, ⟨Q, hQ, rfl⟩, Q, Relation.ReflTransGen.refl, heQ⟩

/-- **Line 139** (`g:blob_welldefined`). "The blobs in a phylogenetic network are well-defined, i.e., each blob can be
found as above, starting from any recombination cycle in the blob": two blobs with an arc in common are equal. -/
theorem IsBlob.eq_of_inter_nonempty {N : Network ι V E} {B B' : Set E} (hB : N.IsBlob B) (hB' : N.IsBlob B')
    (h : (B ∩ B').Nonempty) : B = B' := by
  obtain ⟨Q, hQ, rfl⟩ := hB
  obtain ⟨Q', hQ', rfl⟩ := hB'
  obtain ⟨e, ⟨Q₁, hQ₁, he₁⟩, ⟨Q₂, hQ₂, he₂⟩⟩ := h
  have : Std.Symm N.ShareArc := ⟨fun _ _ h => ⟨h.2.1, h.1, by rw [Set.inter_comm]; exact h.2.2⟩⟩
  have hsymm : ∀ {P P'}, Relation.ReflTransGen N.ShareArc P P' → Relation.ReflTransGen N.ShareArc P' P :=
    fun {P P'} h => (Relation.ReflTransGen.stdSymm (r := N.ShareArc)).symm P P' h
  have hcyc : ∀ {P P'}, N.IsCycle P → Relation.ReflTransGen N.ShareArc P P' → N.IsCycle P' := by
    intro P P' hP hPP'
    induction hPP' with
    | refl => exact hP
    | tail _ h _ => exact h.2.1
  have h12 : Relation.ReflTransGen N.ShareArc Q₁ Q₂ :=
    .single ⟨hcyc hQ hQ₁, hcyc hQ' hQ₂, ⟨e, he₁, he₂⟩⟩
  have hQQ' : Relation.ReflTransGen N.ShareArc Q Q' := Relation.ReflTransGen.trans hQ₁ (h12.trans (hsymm hQ₂))
  ext f
  constructor
  · rintro ⟨P, hP, hf⟩
    exact ⟨P, (hsymm hQQ').trans hP, hf⟩
  · rintro ⟨P, hP, hf⟩
    exact ⟨P, hQQ'.trans hP, hf⟩

/-- A cycle sharing an arc with a blob is in the blob. -/
theorem IsBlob.subset_of_mem {N : Network ι V E} {B Q : Set E} (hB : N.IsBlob B) (hQ : N.IsCycle Q) {e : E} (he : e ∈ B)
    (heQ : e ∈ Q) : Q ⊆ B := by
  obtain ⟨Q₀, hQ₀, rfl⟩ := hB
  obtain ⟨P, hP, heP⟩ := he
  have hPc : N.IsCycle P := by
    clear heP
    induction hP with
    | refl => exact hQ₀
    | tail _ h _ => exact h.2.1
  intro f hf
  exact ⟨Q, hP.tail ⟨hPc, hQ, e, heP, heQ⟩, hf⟩

/-! ### Directed paths -/

section Paths

variable {N}

theorem isPath_append {u w : V} {p q : List E} :
    N.IsPath u w (p ++ q) ↔ ∃ v, N.IsPath u v p ∧ N.IsPath v w q := by
  constructor
  · intro h
    induction p generalizing u with
    | nil => exact ⟨u, rfl, h⟩
    | cons e p ih =>
      obtain ⟨v, h₁, h₂⟩ := ih h.2
      exact ⟨v, ⟨h.1, h₁⟩, h₂⟩
  · rintro ⟨v, h₁, h₂⟩
    exact h₁.append h₂

theorem IsPath.eq_nil_of_self {u : V} {p : List E} (h : N.IsPath u u p) : p = [] := by
  cases p with
  | nil => rfl
  | cons e p =>
    exfalso
    have := h.1
    subst this
    exact not_reach_tgt_src e (IsPath.reach h.2)

/-- An arc on a path splits it. -/
theorem IsPath.split {u v : V} {p : List E} {e : E} (h : N.IsPath u v p) (he : e ∈ p) :
    ∃ p₁ p₂, p = p₁ ++ e :: p₂ ∧ N.IsPath u (N.src e) p₁ ∧ N.IsPath (N.tgt e) v p₂ := by
  obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem he
  obtain ⟨y, h₁, h₂⟩ := isPath_append.1 h
  obtain ⟨rfl, h₃⟩ := h₂
  exact ⟨p₁, p₂, rfl, h₁, h₃⟩

/-- The nodes of a path out of `u`. -/
def pathVerts (N : Network ι V E) (u : V) (p : List E) : List V := u :: p.map N.tgt

theorem start_mem_pathVerts (u : V) (p : List E) : u ∈ pathVerts N u p := List.mem_cons_self

theorem IsPath.end_mem_pathVerts {u v : V} {p : List E} (h : N.IsPath u v p) : v ∈ pathVerts N u p := by
  induction p generalizing u with
  | nil => cases h; exact List.mem_cons_self
  | cons e p ih =>
    have := ih h.2
    refine List.mem_cons_of_mem _ ?_
    simpa [pathVerts] using this

theorem tgt_mem_pathVerts {u : V} {p : List E} {e : E} (he : e ∈ p) : N.tgt e ∈ pathVerts N u p :=
  List.mem_cons_of_mem _ (List.mem_map_of_mem he)

theorem IsPath.src_mem_pathVerts {u v : V} {p : List E} {e : E} (h : N.IsPath u v p) (he : e ∈ p) :
    N.src e ∈ pathVerts N u p := by
  obtain ⟨p₁, p₂, rfl, h₁, -⟩ := h.split he
  have := h₁.end_mem_pathVerts
  simp only [pathVerts, List.mem_cons, List.mem_map, List.mem_append] at this ⊢
  rcases this with h | ⟨f, hf, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨f, Or.inl hf, h⟩

/-- A node on a path splits it. -/
theorem IsPath.split_vert {u v y : V} {p : List E} (h : N.IsPath u v p) (hy : y ∈ pathVerts N u p) :
    ∃ p₁ p₂, p = p₁ ++ p₂ ∧ N.IsPath u y p₁ ∧ N.IsPath y v p₂ := by
  rcases List.mem_cons.1 hy with rfl | hy
  · exact ⟨[], p, rfl, rfl, h⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
    obtain ⟨p₁, p₂, rfl, h₁, h₂⟩ := h.split he
    exact ⟨p₁ ++ [e], p₂, by simp, h₁.append ⟨rfl, rfl⟩, h₂⟩

/-- Every node on a path is reachable from its start, and reaches its end. -/
theorem IsPath.reach_of_mem {u v y : V} {p : List E} (h : N.IsPath u v p) (hy : y ∈ pathVerts N u p) :
    N.Reach u y ∧ N.Reach y v := by
  obtain ⟨p₁, p₂, -, h₁, h₂⟩ := h.split_vert hy
  exact ⟨h₁.reach, h₂.reach⟩

/-- An arc occurs once on a path. -/
theorem IsPath.notMem_of_split {u v : V} {p₁ p₂ : List E} {e : E} (h : N.IsPath u v (p₁ ++ e :: p₂)) :
    e ∉ p₁ ∧ e ∉ p₂ := by
  obtain ⟨y, h₁, h₂⟩ := isPath_append.1 h
  obtain ⟨rfl, h₃⟩ := h₂
  constructor
  · intro he
    obtain ⟨_, q, -, -, hq⟩ := h₁.split he
    exact not_reach_tgt_src e hq.reach
  · intro he
    obtain ⟨q, _, -, hq, -⟩ := h₃.split he
    exact not_reach_tgt_src e hq.reach

/-- The first node on a path with a property: the path up to it has no earlier such node. -/
theorem IsPath.exists_first (Pr : V → Prop) {u v : V} {p : List E} (h : N.IsPath u v p) (hv : Pr v) :
    ∃ x p₁ p₂, p = p₁ ++ p₂ ∧ N.IsPath u x p₁ ∧ N.IsPath x v p₂ ∧ Pr x ∧ ∀ f ∈ p₁, ¬ Pr (N.src f) := by
  induction p generalizing u with
  | nil =>
    cases h
    exact ⟨_, [], [], rfl, rfl, rfl, hv, by simp⟩
  | cons e p ih =>
    by_cases hu : Pr u
    · exact ⟨u, [], e :: p, rfl, rfl, h, hu, by simp⟩
    · obtain ⟨x, p₁, p₂, rfl, h₁, h₂, hx, hf⟩ := ih h.2
      refine ⟨x, e :: p₁, p₂, rfl, ⟨h.1, h₁⟩, h₂, hx, ?_⟩
      intro f hf'
      rcases List.mem_cons.1 hf' with rfl | hf'
      · rw [h.1]; exact hu
      · exact hf f hf'

/-- The last node on a path with a property: the path after it has no such node. -/
theorem IsPath.exists_last (Pr : V → Prop) {u v : V} {p : List E} (h : N.IsPath u v p) (hu : Pr u) :
    ∃ x p₁ p₂, p = p₁ ++ p₂ ∧ N.IsPath u x p₁ ∧ N.IsPath x v p₂ ∧ Pr x ∧ ∀ f ∈ p₂, ¬ Pr (N.tgt f) := by
  induction p using List.reverseRecOn generalizing v with
  | nil =>
    cases h
    exact ⟨u, [], [], rfl, rfl, rfl, hu, by simp⟩
  | append_singleton p e ih =>
    obtain ⟨y, h₁, h₂⟩ := isPath_append.1 h
    obtain ⟨rfl, rfl⟩ := h₂
    by_cases hv : Pr (N.tgt e)
    · exact ⟨N.tgt e, p ++ [e], [], by simp, h, rfl, hv, by simp⟩
    · obtain ⟨x, p₁, p₂, rfl, h₃, h₄, hx, hf⟩ := ih h₁
      refine ⟨x, p₁, p₂ ++ [e], by simp, h₃, h₄.append ⟨rfl, rfl⟩, hx, ?_⟩
      intro f hf'
      rcases List.mem_append.1 hf' with hf' | hf'
      · exact hf f hf'
      · rw [List.mem_singleton.1 hf']; exact hv

/-- The target of an arc on a path is the end of the path, or the source of a later arc. -/
theorem IsPath.tgt_eq_or {u v : V} {p : List E} {g : E} (h : N.IsPath u v p) (hg : g ∈ p) :
    N.tgt g = v ∨ ∃ f ∈ p, N.src f = N.tgt g := by
  obtain ⟨p₁, p₂, rfl, -, h₂⟩ := h.split hg
  cases p₂ with
  | nil => exact Or.inl h₂
  | cons f p₂ => exact Or.inr ⟨f, by simp, h₂.1⟩

/-- A nonempty path has a last arc, into its end. -/
theorem IsPath.exists_last_arc {u v : V} {p : List E} (h : N.IsPath u v p) (hp : p ≠ []) :
    ∃ p' e, p = p' ++ [e] ∧ N.IsPath u (N.src e) p' ∧ N.tgt e = v := by
  obtain ⟨p', e, rfl⟩ := List.eq_nil_or_concat' p |>.resolve_left hp
  obtain ⟨y, h₁, h₂⟩ := isPath_append.1 h
  obtain ⟨rfl, rfl⟩ := h₂
  exact ⟨p', e, rfl, h₁, rfl⟩

/-- **The two paths lemma, core.** Take a directed path through the arc `e` and another directed path to the same node that
avoids `e`, and suppose that the first path, after `e`, has no earlier node on the second. Walking back from that node along
the second path to the last node on the first gives a recombination cycle through `e`. -/
theorem exists_isCycleOn_core {w₀ x : V} {P₁ C B : List E} {e : E} (hP : N.IsPath w₀ (N.src e) P₁)
    (hC : N.IsPath (N.tgt e) x C) (hB : N.IsPath w₀ x B) (heB : e ∉ B)
    (hC' : ∀ f ∈ C, N.src f ∉ pathVerts N w₀ B) :
    ∃ w P₁₁ P₁₂ B₁ q, P₁ = P₁₁ ++ P₁₂ ∧ B = B₁ ++ q ∧ q ≠ [] ∧ N.IsPath w₀ w P₁₁ ∧ N.IsPath w₀ w B₁ ∧
      N.IsCycleOn w x (P₁₂ ++ e :: C) q := by
  classical
  obtain ⟨w, B₁, q, rfl, hB₁, hq, hw, hqf⟩ := hB.exists_last (fun y => y ∈ pathVerts N w₀ P₁)
    (start_mem_pathVerts w₀ P₁)
  obtain ⟨P₁₁, P₁₂, rfl, hP₁₁, hP₁₂⟩ := hP.split_vert hw
  have hp : N.IsPath w x (P₁₂ ++ e :: C) := hP₁₂.append ⟨rfl, hC⟩
  -- `x` is not on the part before `e`
  have hx : x ∉ pathVerts N w₀ (P₁₁ ++ P₁₂) := fun hx => by
    have := (hP.reach_of_mem hx).2
    exact not_reach_tgt_src e (hC.reach.trans this)
  have hqne : q ≠ [] := by
    rintro rfl
    have : w = x := hq
    exact hx (this ▸ hw)
  -- the arcs of `q` are on the second path, and so have their nodes on it
  have hqB : ∀ f ∈ q, f ∈ B₁ ++ q := fun f hf => List.mem_append_right _ hf
  have hdisj : ∀ f ∈ P₁₂ ++ e :: C, f ∉ q := by
    intro f hf hfq
    rcases List.mem_append.1 hf with hf | hf
    · exact hqf f hfq (tgt_mem_pathVerts (List.mem_append_right _ hf))
    · rcases List.mem_cons.1 hf with rfl | hf
      · exact heB (hqB _ hfq)
      · exact hC' f hf (hB.src_mem_pathVerts (hqB f hfq))
  refine ⟨w, P₁₁, P₁₂, B₁, q, rfl, rfl, hqne, hP₁₁, hB₁, ?_, hp, hq, ?_, ?_⟩
  · obtain ⟨_, a, ha, -, hax⟩ := hp.exists_last_arc (by simp)
    obtain ⟨_, b, hb, -, hbx⟩ := hq.exists_last_arc hqne
    refine ⟨a, b, fun hab => ?_, hax, hbx⟩
    exact hdisj a (by rw [ha]; simp) (by rw [hb, hab]; simp)
  · intro hpq
    exact hdisj e (by simp) (hpq ▸ by simp)
  · intro g hg f hf hgf
    have hfB : N.tgt f ∈ pathVerts N w₀ (B₁ ++ q) := tgt_mem_pathVerts (hqB f hf)
    rcases List.mem_append.1 hg with hg | hg
    · exact absurd (hgf ▸ tgt_mem_pathVerts (List.mem_append_right _ hg)) (hqf f hf)
    · have hnext : N.tgt g = x ∨ ∃ h ∈ C, N.src h = N.tgt g := by
        rcases List.mem_cons.1 hg with rfl | hg
        · cases C with
          | nil => exact Or.inl hC
          | cons h C => exact Or.inr ⟨h, by simp, hC.1⟩
        · exact hC.tgt_eq_or hg
      rcases hnext with hgx | ⟨h, hh, hsrc⟩
      · exact hgx
      · exact absurd (hsrc.trans hgf ▸ hfB) (hC' h hh)

/-- **The two paths lemma.** Two directed paths from `w₀` to `b`, the first through the arc `e` and the second avoiding it,
give a recombination cycle through `e`. One of its two paths, `q`, is a nonempty stretch of the second path, starting from a
node `w` on the first path before `e`. This is the fact behind the two cases in the proof of Gusfield, Eddhu, Langley 2004,
Lemma 2.1: a path that leaves a cycle and returns makes a recombination cycle sharing an edge with it. -/
theorem exists_isCycleOn_of_paths {w₀ b : V} {P₁ C B : List E} {e : E} (hP : N.IsPath w₀ (N.src e) P₁)
    (hC : N.IsPath (N.tgt e) b C) (hB : N.IsPath w₀ b B) (heB : e ∉ B) :
    ∃ w x p q P₁₁ P₁₂ B₁ B₂, P₁ = P₁₁ ++ P₁₂ ∧ B = B₁ ++ q ++ B₂ ∧ q ≠ [] ∧ N.IsPath w₀ w P₁₁ ∧ N.IsPath w₀ w B₁ ∧
      N.IsCycleOn w x p q ∧ e ∈ p := by
  classical
  obtain ⟨x, C₁, C₂, -, hC₁, -, hx, hf⟩ := hC.exists_first (fun y => y ∈ pathVerts N w₀ B) hB.end_mem_pathVerts
  obtain ⟨B', B₂, rfl, hB', -⟩ := hB.split_vert hx
  obtain ⟨w, P₁₁, P₁₂, B₁, q, h₁, rfl, hq, hP₁₁, hB₁, hcyc⟩ := exists_isCycleOn_core hP hC₁ hB'
    (fun h => heB (List.mem_append_left _ h))
    (fun f hf' h => hf f hf' (by
      simp only [pathVerts, List.mem_cons, List.mem_map, List.mem_append] at h ⊢
      rcases h with h | ⟨g, hg, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨g, Or.inl hg, h⟩))
  exact ⟨w, x, _, q, P₁₁, P₁₂, B₁, B₂, h₁, rfl, hq, hP₁₁, hB₁, hcyc, by simp⟩

theorem IsCycleOn.symm {w x : V} {p q : List E} (h : N.IsCycleOn w x p q) : N.IsCycleOn w x q p :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.1.symm, fun e he f hf hef => (h.2.2.2.2 f hf e he hef.symm).symm ▸ hef ▸ rfl⟩

/-- An arc on one of the two paths of a recombination cycle isn't on the other. -/
theorem IsCycleOn.notMem {w x : V} {p q : List E} {e : E} (h : N.IsCycleOn w x p q) (he : e ∈ p) : e ∉ q := by
  intro he'
  have hp := h.2.1
  have hq := h.2.2.1
  have hx : N.tgt e = x := h.2.2.2.2 e he e he' rfl
  obtain ⟨p₁, p₂, rfl, hp₁, hp₂⟩ := hp.split he
  obtain ⟨q₁, q₂, rfl, hq₁, hq₂⟩ := hq.split he'
  rw [hx] at hp₂ hq₂
  obtain rfl := hp₂.eq_nil_of_self
  obtain rfl := hq₂.eq_nil_of_self
  apply h.2.2.2.1
  -- both start at `w` and reach `src e`, and they can't meet before
  rcases List.eq_nil_or_concat' p₁ with rfl | ⟨p', a, rfl⟩
  · have hw : w = N.src e := hp₁
    subst hw
    obtain rfl := hq₁.eq_nil_of_self
    rfl
  · rcases List.eq_nil_or_concat' q₁ with rfl | ⟨q', b, rfl⟩
    · have hw : w = N.src e := hq₁
      subst hw
      have := hp₁.eq_nil_of_self
      simp at this
    · exfalso
      obtain ⟨y, -, hy⟩ := isPath_append.1 hp₁
      obtain ⟨y', -, hy'⟩ := isPath_append.1 hq₁
      obtain ⟨rfl, ha⟩ := hy
      obtain ⟨rfl, hb⟩ := hy'
      have ha' : N.tgt a = N.src e := ha
      have hb' : N.tgt b = N.src e := hb
      have := h.2.2.2.2 a (by simp) b (by simp) (ha'.trans hb'.symm)
      exact src_ne_tgt e (by rw [← ha', this, hx])

/-- The two arcs into a recombination node lie on one recombination cycle, whose coalescent node is a lowest common ancestor of their
sources. -/
theorem exists_isCycleOn_of_tgt_eq [Finite V] {e f : E} (hef : e ≠ f) (h : N.tgt e = N.tgt f) :
    ∃ w p q, N.IsPath w (N.src e) p ∧ N.IsPath w (N.src f) q ∧ N.IsCycleOn w (N.tgt e) (p ++ [e]) (q ++ [f]) := by
  have hne : {w | N.Reach w (N.src e) ∧ N.Reach w (N.src f)}.Nonempty := ⟨N.root, N.reach_root _, N.reach_root _⟩
  obtain ⟨w, ⟨hw₁, hw₂⟩, hmin⟩ := N.wellFounded_transGen_swap.has_min _ hne
  obtain ⟨p, hp⟩ := hw₁.exists_isPath
  obtain ⟨q, hq⟩ := hw₂.exists_isPath
  refine ⟨w, p, q, hp, hq, ⟨⟨e, f, hef, rfl, h.symm⟩, hp.append ⟨rfl, rfl⟩, hq.append ⟨rfl, h.symm⟩, ?_, ?_⟩⟩
  · intro hpq
    exact hef (by simpa using (List.append_inj' hpq rfl).2)
  · intro e' he' f' hf' hee
    rcases List.mem_append.1 he' with he' | he'
    · rcases List.mem_append.1 hf' with hf' | hf'
      · exfalso
        have h₁ : N.Reach (N.tgt e') (N.src e) := hp.reach_tgt_of_mem he'
        have h₂ : N.Reach (N.tgt e') (N.src f) := hee ▸ hq.reach_tgt_of_mem hf'
        have h₃ : Relation.TransGen N.Arc w (N.tgt e') :=
          Relation.TransGen.tail' (hp.reach_src_of_mem he') (arc_src_tgt e')
        exact hmin _ ⟨h₁, h₂⟩ h₃
      · obtain rfl : f' = f := by simpa using hf'
        exact hee.trans h.symm
    · obtain rfl : e' = e := by simpa using he'
      rfl

/-- The two arcs into a recombination node are on one recombination cycle. -/
theorem exists_isCycle_of_tgt_eq [Finite V] {e f : E} (hef : e ≠ f) (h : N.tgt e = N.tgt f) :
    ∃ Q, N.IsCycle Q ∧ e ∈ Q ∧ f ∈ Q := by
  obtain ⟨w, p, q, -, -, hc⟩ := exists_isCycleOn_of_tgt_eq hef h
  exact ⟨_, ⟨w, _, _, _, hc, rfl⟩, Or.inl (by simp), Or.inr (by simp)⟩

end Paths

/-- The graph underlying `N`: its directions are forgotten. -/
def underlying : SimpleGraph V := SimpleGraph.fromRel N.Arc

section Underlying

variable {N}

theorem underlying_adj {a b : V} : N.underlying.Adj a b ↔ a ≠ b ∧ (N.Arc a b ∨ N.Arc b a) :=
  SimpleGraph.fromRel_adj _ _ _

theorem underlying_adj_arc (e : E) : N.underlying.Adj (N.src e) (N.tgt e) :=
  underlying_adj.2 ⟨src_ne_tgt e, Or.inl ⟨e, rfl, rfl⟩⟩

/-- Distinct arcs are distinct edges of the underlying graph: there are no parallel or opposite arcs. -/
theorem s_src_tgt_injective {e f : E} (h : s(N.src f, N.tgt f) = s(N.src e, N.tgt e)) : f = e := by
  rcases Sym2.eq_iff.1 h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact N.simple _ _ h₁ h₂
  · exfalso
    have : N.Reach (N.tgt e) (N.src e) := by
      rw [← h₁, ← h₂]
      exact Relation.ReflTransGen.single ⟨f, rfl, rfl⟩
    exact not_reach_tgt_src e this

/-- The underlying graph without the arc `e`. -/
abbrev delArc (N : Network ι V E) (e : E) : SimpleGraph V := N.underlying.deleteEdges {s(N.src e, N.tgt e)}

theorem delArc_adj_arc {e f : E} (h : f ≠ e) : (N.delArc e).Adj (N.src f) (N.tgt f) := by
  rw [SimpleGraph.deleteEdges_adj]
  exact ⟨underlying_adj_arc f, fun h' => h (s_src_tgt_injective h')⟩

/-- A directed path avoiding the arc `e` connects its ends without `e`. -/
theorem reachable_delArc_of_isPath {e : E} {u v : V} {p : List E} (h : N.IsPath u v p) (he : e ∉ p) :
    (N.delArc e).Reachable u v := by
  induction p generalizing u with
  | nil => cases h; exact .refl _
  | cons f p ih =>
    obtain ⟨rfl, h₂⟩ := h
    have hf : f ≠ e := fun hf => he (hf ▸ List.mem_cons_self)
    exact (delArc_adj_arc hf).reachable.trans (ih h₂ fun h' => he (List.mem_cons_of_mem _ h'))

end Underlying

/-- The arcs on no recombination cycle are the bridges of the underlying graph. This is the fact behind the reason given
at line 141, "that cycle would correspond to a recombination cycle": a cycle of the underlying graph is not itself a
recombination cycle, since it can alternate directions several times, but each of its arcs is on one, because all nodes
are reachable from the root. -/
theorem isTreeArc_iff_isBridge [Finite V] [Finite E] (e : E) :
    N.IsTreeArc e ↔ N.underlying.IsBridge s(N.src e, N.tgt e) := by
  rw [SimpleGraph.isBridge_iff]
  constructor
  · -- a non-bridge is on a recombination cycle
    intro he hr
    apply he
    -- the nodes reached from the root without `e`
    obtain ⟨A, hA⟩ := Reach.exists_isPath (N.reach_root (N.src e))
    have heA : e ∉ A := fun h => by
      obtain ⟨-, q, -, -, hq⟩ := hA.split h
      exact not_reach_tgt_src e hq.reach
    have hcycle : ∀ {b : V} {C B : List E}, N.IsPath (N.tgt e) b C → N.IsPath N.root b B → e ∉ B → ∀ {P₁ : List E},
        N.IsPath N.root (N.src e) P₁ → N.OnCycle e := by
      intro b C B hC hB heB P₁ hP₁
      obtain ⟨w, x, p, q, -, -, -, -, -, -, -, -, -, hc, hep⟩ := exists_isCycleOn_of_paths hP₁ hC hB heB
      exact ⟨_, ⟨w, x, p, q, hc, rfl⟩, Or.inl hep⟩
    let R : Set V := {y | ∃ B, N.IsPath N.root y B ∧ e ∉ B}
    by_cases hv : N.tgt e ∈ R
    · obtain ⟨B, hB, heB⟩ := hv
      exact hcycle (C := []) rfl hB heB hA
    · obtain ⟨p⟩ := hr
      obtain ⟨d, -, hd₁, hd₂⟩ := p.exists_boundary_dart R ⟨A, hA, heA⟩ hv
      have hadj := d.adj
      rw [SimpleGraph.deleteEdges_adj] at hadj
      obtain ⟨hadj, hne⟩ := hadj
      obtain ⟨-, ⟨f, hf₁, hf₂⟩ | ⟨f, hf₁, hf₂⟩⟩ := underlying_adj.1 hadj
      · -- an arc out of `R`, other than `e`, stays in `R`
        exfalso
        have hfe : f ≠ e := fun h => hne (by
          simp only [Set.mem_singleton_iff, ← hf₁, ← hf₂, h])
        obtain ⟨B, hB, heB⟩ := hd₁
        refine hd₂ ⟨B ++ [f], hB.append ⟨hf₁, hf₂⟩, ?_⟩
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨heB, hfe.symm⟩
      · -- an arc into `R` from below `e`
        have hfe : f ≠ e := fun h => hne (by
          simp only [Set.mem_singleton_iff, ← hf₁, ← hf₂, h, Sym2.eq_swap])
        obtain ⟨B, hB, heB⟩ := hd₁
        obtain ⟨Az, hAz⟩ := Reach.exists_isPath (N.reach_root d.snd)
        have heAz : e ∈ Az := by
          by_contra h
          exact hd₂ ⟨Az, hAz, h⟩
        obtain ⟨P₁, C, -, hP₁, hC⟩ := hAz.split heAz
        have hCf : N.IsPath (N.tgt e) d.fst (C ++ [f]) := hC.append ⟨hf₁, hf₂⟩
        exact hcycle hCf hB heB hP₁
  · -- an arc on a recombination cycle isn't a bridge
    intro hb hc
    obtain ⟨Q, ⟨w, x, p, q, hcyc, rfl⟩, he⟩ := hc
    have key : ∀ {p q : List E}, N.IsCycleOn w x p q → e ∈ p → (N.delArc e).Reachable (N.src e) (N.tgt e) := by
      intro p q hcyc he
      obtain ⟨p₁, p₂, rfl, hp₁, hp₂⟩ := hcyc.2.1.split he
      obtain ⟨h₁, h₂⟩ := IsPath.notMem_of_split hcyc.2.1
      have h₃ := hcyc.notMem he
      exact (reachable_delArc_of_isPath hp₁ h₁).symm.trans
        ((reachable_delArc_of_isPath hcyc.2.2.1 h₃).trans (reachable_delArc_of_isPath hp₂ h₂).symm)
    rcases he with he | he
    · exact hb (key hcyc he)
    · exact hb (key hcyc.symm he)

/-- **Lines 140 to 142** (`g:blobtree`). "If we contract each blob in a network to a single point, the resulting network is
a directed tree `T′`". The contraction, with an edge per tree arc, is a tree, which is directed away from the class of the
root. This doesn't need blobs to be node-disjoint, since `T′` contracts the connected components of the arcs on cycles,
and two blobs sharing a node make one class.

The paper's reason, at line 141: a cycle of the graph after the contraction "would correspond to a recombination cycle". This has a
gap, repaired by `isTreeArc_iff_isBridge`: the cycle can change direction several times, but each arc of it is on a recombination
cycle. So an edge of `T′` comes from a bridge of `N`, and it's a bridge of `T′`. -/
theorem blobbedTree_isTree [Finite V] [Finite E] :
    N.blobbedTree.IsTree ∧
      (∀ e, N.IsTreeArc e → N.toBlobNode (N.src e) ≠ N.toBlobNode (N.tgt e)) ∧
      Function.Injective (fun e : {e // N.IsTreeArc e} =>
        s(N.toBlobNode (N.src e.1), N.toBlobNode (N.tgt e.1))) ∧
      (∀ e, N.IsTreeArc e → N.toBlobNode (N.tgt e) ≠ N.toBlobNode N.root) ∧
      ∀ a, a ≠ N.toBlobNode N.root → ∃! e : {e // N.IsTreeArc e}, N.toBlobNode (N.tgt e.1) = a := by
  have hbr : ∀ {e}, N.IsTreeArc e → ¬ (N.delArc e).Reachable (N.src e) (N.tgt e) := fun {e} he =>
    SimpleGraph.isBridge_iff.1 ((N.isTreeArc_iff_isBridge e).1 he)
  -- a class of `T′` is connected without any tree arc
  have hcl : ∀ {e u v}, N.IsTreeArc e → N.toBlobNode u = N.toBlobNode v → (N.delArc e).Reachable u v := by
    intro e u v he huv
    have hr : Relation.EqvGen (fun u v => ∃ f, N.OnCycle f ∧ N.src f = u ∧ N.tgt f = v) u v := Quotient.exact huv
    clear huv
    induction hr with
    | rel _ _ hab =>
      obtain ⟨f, hf, rfl, rfl⟩ := hab
      exact (delArc_adj_arc (e := e) (f := f) fun h => he (h ▸ hf)).reachable
    | refl => exact .refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have htree : ∀ e, N.IsTreeArc e → N.toBlobNode (N.src e) ≠ N.toBlobNode (N.tgt e) := fun e he h =>
    hbr he (hcl he h)
  have hroot : ∀ e, ∃ A, N.IsPath N.root (N.src e) A ∧ e ∉ A := fun e => by
    obtain ⟨A, hA⟩ := Reach.exists_isPath (N.reach_root (N.src e))
    refine ⟨A, hA, fun h => ?_⟩
    obtain ⟨-, q, -, -, hq⟩ := hA.split h
    exact not_reach_tgt_src e hq.reach
  have hadj : ∀ {a b}, N.blobbedTree.Adj a b → a ≠ b ∧ ∃ e, N.IsTreeArc e ∧
      ((N.toBlobNode (N.src e) = a ∧ N.toBlobNode (N.tgt e) = b) ∨
        (N.toBlobNode (N.src e) = b ∧ N.toBlobNode (N.tgt e) = a)) := by
    intro a b h
    obtain ⟨hne, ⟨e, he, h₁, h₂⟩ | ⟨e, he, h₁, h₂⟩⟩ := SimpleGraph.fromRel_adj _ _ _ |>.1 h
    · exact ⟨hne, e, he, Or.inl ⟨h₁, h₂⟩⟩
    · exact ⟨hne, e, he, Or.inr ⟨h₁, h₂⟩⟩
  have hinj : ∀ {e f}, N.IsTreeArc e → N.IsTreeArc f →
      s(N.toBlobNode (N.src e), N.toBlobNode (N.tgt e)) = s(N.toBlobNode (N.src f), N.toBlobNode (N.tgt f)) → e = f := by
    intro e f he hf h
    by_contra hne
    have hfe : f ≠ e := fun h => hne h.symm
    rcases Sym2.eq_iff.1 h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hbr he ((hcl he h₁).trans ((delArc_adj_arc hfe).reachable.trans (hcl he h₂.symm)))
    · exact hbr he ((hcl he h₁).trans ((delArc_adj_arc hfe).reachable.symm.trans (hcl he h₂.symm)))
  -- `T′` without an edge lifts to `N` without the arc of that edge
  have hlift : ∀ {e}, N.IsTreeArc e → ∀ {a b}, (N.blobbedTree.deleteEdges
      {s(N.toBlobNode (N.src e), N.toBlobNode (N.tgt e))}).Reachable a b →
      ∀ u v, N.toBlobNode u = a → N.toBlobNode v = b → (N.delArc e).Reachable u v := by
    intro e he a b hab
    rw [SimpleGraph.reachable_iff_reflTransGen] at hab
    induction hab with
    | refl => exact fun u v hu hv => hcl he (hu.trans hv.symm)
    | @tail c d _ hcd ih =>
      intro u v hu hv
      rw [SimpleGraph.deleteEdges_adj] at hcd
      obtain ⟨hcd, hns⟩ := hcd
      obtain ⟨-, f, hf, hc⟩ := hadj hcd
      have hfe : f ≠ e := by
        rintro rfl
        apply hns
        rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · simp [h₁, h₂]
        · simp [h₁, h₂, Sym2.eq_swap]
      rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact (ih u (N.src f) hu h₁).trans ((delArc_adj_arc hfe).reachable.trans (hcl he (h₂.trans hv.symm)))
      · exact (ih u (N.tgt f) hu h₂).trans ((delArc_adj_arc hfe).reachable.symm.trans (hcl he (h₁.trans hv.symm)))
  refine ⟨⟨?_, ?_⟩, htree, ?_, ?_, ?_⟩
  · -- connected: everything is reached from the class of the root
    have : Nonempty N.BlobNode := ⟨N.toBlobNode N.root⟩
    have hreach : ∀ v, N.blobbedTree.Reachable (N.toBlobNode N.root) (N.toBlobNode v) := by
      intro v
      have hv := N.reach_root v
      induction hv with
      | refl => exact .refl _
      | tail _ hb ih =>
        obtain ⟨f, rfl, rfl⟩ := hb
        refine ih.trans ?_
        by_cases hf : N.OnCycle f
        · have : N.toBlobNode (N.src f) = N.toBlobNode (N.tgt f) :=
            Quotient.sound (Relation.EqvGen.rel _ _ ⟨f, hf, rfl, rfl⟩)
          rw [this]
        · refine SimpleGraph.Adj.reachable (SimpleGraph.fromRel_adj _ _ _ |>.2 ⟨htree f hf, Or.inl ⟨f, hf, rfl, rfl⟩⟩)
    refine SimpleGraph.Connected.mk ?_
    intro a b
    induction a using Quotient.inductionOn with | _ u => ?_
    induction b using Quotient.inductionOn with | _ v => ?_
    exact (hreach u).symm.trans (hreach v)
  · -- acyclic: every edge is a bridge, since the arc of the edge is one
    rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
    intro a b h
    obtain ⟨-, e, he, hc⟩ := hadj h
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [SimpleGraph.isBridge_iff]
      exact fun hr => hbr he (hlift he hr _ _ rfl rfl)
    · rw [SimpleGraph.isBridge_iff, Sym2.eq_swap]
      exact fun hr => hbr he (hlift he hr.symm _ _ rfl rfl)
  · rintro ⟨e, he⟩ ⟨f, hf⟩ h
    exact Subtype.ext (hinj he hf h)
  · -- the class of the root has no tree arc in
    intro e he h
    obtain ⟨A, hA, heA⟩ := hroot e
    exact hbr he ((reachable_delArc_of_isPath hA heA).symm.trans (hcl he h.symm))
  · -- every other class has exactly one tree arc in
    intro a ha
    have hex : ∀ v, N.toBlobNode v ≠ N.toBlobNode N.root → ∃ e, N.IsTreeArc e ∧ N.toBlobNode (N.tgt e) = N.toBlobNode v := by
      intro v
      have hv := N.reach_root v
      induction hv with
      | refl => exact fun h => absurd rfl h
      | tail _ hb ih =>
        obtain ⟨f, rfl, rfl⟩ := hb
        intro hne
        by_cases hf : N.OnCycle f
        · have hcl' : N.toBlobNode (N.src f) = N.toBlobNode (N.tgt f) :=
            Quotient.sound (Relation.EqvGen.rel _ _ ⟨f, hf, rfl, rfl⟩)
          obtain ⟨e, he, h⟩ := ih (hcl' ▸ hne)
          exact ⟨e, he, h.trans hcl'⟩
        · exact ⟨f, hf, rfl⟩
    obtain ⟨v, rfl⟩ := Quotient.exists_rep a
    obtain ⟨e, he, hev⟩ := hex v ha
    refine ⟨⟨e, he⟩, hev, ?_⟩
    rintro ⟨f, hf⟩ hfv
    refine Subtype.ext ?_
    by_contra hne
    have hne' : f ≠ e := hne
    have hft : N.toBlobNode (N.tgt f) = N.toBlobNode (N.tgt e) := hfv.trans hev.symm
    obtain ⟨A, hA, heA⟩ := hroot e
    by_cases hfA : f ∈ A
    · -- the path to `src e` passes through `f`: its start reaches `src f` without `e`
      obtain ⟨A₁, A₂, rfl, hA₁, -⟩ := hA.split hfA
      have heA₁ : e ∉ A₁ := fun h => heA (List.mem_append_left _ h)
      exact hbr he ((reachable_delArc_of_isPath hA heA).symm.trans ((reachable_delArc_of_isPath hA₁ heA₁).trans
        ((delArc_adj_arc hne').reachable.trans (hcl he hft))))
    · -- it doesn't: then `f` isn't a bridge
      obtain ⟨A', hA', hfA'⟩ := hroot f
      exact hbr hf ((reachable_delArc_of_isPath hA' hfA').symm.trans ((reachable_delArc_of_isPath hA hfA).trans
        ((delArc_adj_arc hne'.symm).reachable.trans (hcl hf hft.symm))))

/-! ### Separating blobs that share a node (line 135) -/

section Separate

variable {N}

/-- `v` is a node of the blob `B`, with no arc of `B` into it, and it is a node of another blob. The new edge of line 135 goes
from `v` to a copy of `v`, which takes the arcs of `B` out of `v`. -/
structure IsSharedTop (N : Network ι V E) (B : Set E) (v : V) : Prop where
  isBlob : N.IsBlob B
  mem : v ∈ N.blobVerts B
  noArcIn : ∀ e ∈ B, N.tgt e ≠ v
  shared : ∃ B', N.IsBlob B' ∧ B' ≠ B ∧ v ∈ N.blobVerts B'

/-- The pairs of a blob and a node where a new node and a new edge are added. -/
abbrev SepTop (N : Network ι V E) : Type (max v w) := {t : Set E × V // N.IsSharedTop t.1 t.2}

/-- A blob with no arc into `v` has an arc out of `v`. -/
theorem IsSharedTop.exists_src {B : Set E} {v : V} (h : N.IsSharedTop B v) : ∃ f ∈ B, N.src f = v := by
  rcases h.mem with ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩
  · exact ⟨f, hf, rfl⟩
  · exact absurd rfl (h.noArcIn f hf)

theorem SepTop.eq_of_mem {t t' : N.SepTop} (hv : t.1.2 = t'.1.2) {f : E} (hf : f ∈ t.1.1) (hf' : f ∈ t'.1.1) : t = t' :=
  Subtype.ext (Prod.ext (IsBlob.eq_of_inter_nonempty t.2.isBlob t'.2.isBlob ⟨f, hf, hf'⟩) hv)

variable (N)

/-- The source of an old arc in the separated network: the new node, for an arc of `B` out of a shared top of `B`. -/
noncomputable def newSrc (f : E) : V ⊕ N.SepTop :=
  if h : ∃ t : N.SepTop, t.1.2 = N.src f ∧ f ∈ t.1.1 then Sum.inr h.choose else Sum.inl (N.src f)

/-- The node of the old network of a node of the separated one. -/
def sepProj : V ⊕ N.SepTop → V := Sum.elim id fun t => t.1.2

variable {N}

theorem newSrc_eq_inr (t : N.SepTop) {f : E} (h₁ : t.1.2 = N.src f) (h₂ : f ∈ t.1.1) : N.newSrc f = Sum.inr t := by
  have h : ∃ t : N.SepTop, t.1.2 = N.src f ∧ f ∈ t.1.1 := ⟨t, h₁, h₂⟩
  rw [newSrc, dite_eq_left h]
  exact congrArg Sum.inr (SepTop.eq_of_mem (h.choose_spec.1.trans h₁.symm) h.choose_spec.2 h₂)

theorem newSrc_cases (f : E) : N.newSrc f = Sum.inl (N.src f) ∨ ∃ t : N.SepTop, N.newSrc f = Sum.inr t ∧ t.1.2 = N.src f ∧ f ∈ t.1.1 := by
  by_cases h : ∃ t : N.SepTop, t.1.2 = N.src f ∧ f ∈ t.1.1
  · obtain ⟨t, h₁, h₂⟩ := h
    exact Or.inr ⟨t, newSrc_eq_inr t h₁ h₂, h₁, h₂⟩
  · left
    rw [newSrc, dite_eq_right h]

theorem newSrc_eq_inr_iff {f : E} {t : N.SepTop} : N.newSrc f = Sum.inr t ↔ t.1.2 = N.src f ∧ f ∈ t.1.1 := by
  constructor
  · intro h
    rcases newSrc_cases (N := N) f with h' | ⟨t', h', h₁, h₂⟩
    · rw [h'] at h; cases h
    · rw [h'] at h
      obtain rfl := Sum.inr.inj h
      exact ⟨h₁, h₂⟩
  · exact fun h => newSrc_eq_inr t h.1 h.2

@[simp] theorem sepProj_inl (v : V) : N.sepProj (Sum.inl v) = v := rfl

theorem sepProj_newSrc (f : E) : N.sepProj (N.newSrc f) = N.src f := by
  rcases newSrc_cases (N := N) f with h | ⟨t, h, h₁, -⟩
  · rw [h]; rfl
  · rw [h]; exact h₁

variable (N)

/-- The network of line 135: at each shared top `v` of a blob `B`, a new node with the label of `v`, a new edge from `v` to it,
and the arcs of `B` out of `v` now start at the new node. The new edges have no sites. -/
noncomputable def separate : Network ι (V ⊕ N.SepTop) (E ⊕ N.SepTop) where
  src := Sum.elim N.newSrc fun t => Sum.inl t.1.2
  tgt := Sum.elim (fun f => Sum.inl (N.tgt f)) Sum.inr
  root := Sum.inl N.root
  site i := Sum.inl (N.site i)
  label v := N.label (N.sepProj v)
  simple := by
    rintro (e | e) (f | f) h₁ h₂
    · simp only [Sum.elim_inl, Sum.inl.injEq] at h₂
      have h₃ := congrArg N.sepProj h₁
      simp only [Sum.elim_inl, sepProj_newSrc] at h₃
      rw [N.simple e f h₃ h₂]
    · cases h₂
    · cases h₂
    · simp only [Sum.elim_inr, Sum.inr.injEq] at h₂
      rw [h₂]
  acyclic := by
    have step : ∀ {a b}, (∃ e, Sum.elim N.newSrc (fun t => Sum.inl t.1.2) e = a ∧
        Sum.elim (fun f => Sum.inl (N.tgt f)) Sum.inr e = b) →
        Relation.TransGen N.Arc (N.sepProj a) (N.sepProj b) ∨ (N.sepProj a = N.sepProj b ∧ a.isLeft ∧ b.isRight) := by
      rintro a b ⟨e | t, rfl, rfl⟩
      · left
        simp only [Sum.elim_inl, sepProj_newSrc]
        exact .single ⟨e, rfl, rfl⟩
      · right
        simp [sepProj]
    have key : ∀ {a b}, Relation.TransGen (fun a b => ∃ e, Sum.elim N.newSrc (fun t => Sum.inl t.1.2) e = a ∧
        Sum.elim (fun f => Sum.inl (N.tgt f)) Sum.inr e = b) a b →
        Relation.TransGen N.Arc (N.sepProj a) (N.sepProj b) ∨ (N.sepProj a = N.sepProj b ∧ a.isLeft ∧ b.isRight) := by
      intro a b h
      induction h with
      | single h => exact step h
      | @tail c d _ h ih =>
        rcases ih with ih | ⟨h₁, h₂, h₃⟩
        · left
          rcases step h with h' | ⟨h', -⟩
          · exact ih.trans h'
          · exact h' ▸ ih
        · rcases step h with h' | ⟨-, h', -⟩
          · left
            exact h₁ ▸ h'
          · rcases c with c | c <;> simp at h₃ h'
    intro a h
    rcases key h with h | ⟨-, h₁, h₂⟩
    · exact N.acyclic _ h
    · cases a <;> simp at h₁ h₂
  root_iff := by
    rintro (v | t)
    · simp only [Sum.inl.injEq]
      rw [← N.root_iff v]
      constructor
      · intro h e he
        exact h (Sum.inl e) (by simp [he])
      · rintro h (e | t) he
        · exact h e (by simpa using he)
        · cases he
    · simp only [reduceCtorEq, iff_false]
      intro h
      exact h (Sum.inr t) rfl
  inDegree_le_two := by
    rintro (e | e) (f | f) (g | g) h₁ h₂
    · simp only [Sum.elim_inl, Sum.inl.injEq] at h₁ h₂
      rcases N.inDegree_le_two e f g h₁ h₂ with h | h | h <;> simp [h]
    · cases h₂
    · cases h₁
    · cases h₁
    · cases h₁
    · cases h₁
    · cases h₂
    · simp only [Sum.elim_inr, Sum.inr.injEq] at h₁
      exact Or.inl (by rw [h₁])
  site_not_recomb := by
    rintro i (f | f) h
    · simp only [Sum.elim_inl, Sum.inl.injEq] at h
      rw [N.site_not_recomb i f h]
    · cases h
  label_tree := by
    rintro (e | t) he i
    · have he' : ∀ f, N.tgt f = N.tgt e → f = e := fun f hf =>
        Sum.inl.inj (he (Sum.inl f) (by simp [hf]))
      have h₁ := N.label_tree e he' i
      by_cases hs : N.site i = e
      · rw [ite_eq_left hs] at h₁
        rw [ite_eq_left (show (Sum.inl (N.site i) : E ⊕ N.SepTop) = Sum.inl e by rw [hs])]
        simpa only [Sum.elim_inl, sepProj_inl, sepProj_newSrc] using h₁
      · rw [ite_eq_right hs] at h₁
        rw [ite_eq_right (fun h : (Sum.inl (N.site i) : E ⊕ N.SepTop) = Sum.inl e => hs (Sum.inl.inj h))]
        simpa only [Sum.elim_inl, sepProj_inl, sepProj_newSrc] using h₁
    · simp [sepProj]
  label_recomb := by
    rintro (e | e) (f | f) hef h i
    · simp only [Sum.elim_inl, Sum.inl.injEq] at h
      have h₁ := N.label_recomb e f (fun h' => hef (by rw [h'])) h i
      simpa only [Sum.elim_inl, sepProj_inl, sepProj_newSrc] using h₁
    · cases h
    · cases h
    · simp only [Sum.elim_inr, Sum.inr.injEq] at h
      exact absurd (by rw [h]) hef

variable {N}

@[simp] theorem separate_src_inl (f : E) : N.separate.src (Sum.inl f) = N.newSrc f := rfl
@[simp] theorem separate_src_inr (t : N.SepTop) : N.separate.src (Sum.inr t) = Sum.inl t.1.2 := rfl
@[simp] theorem separate_tgt_inl (f : E) : N.separate.tgt (Sum.inl f) = Sum.inl (N.tgt f) := rfl
@[simp] theorem separate_tgt_inr (t : N.SepTop) : N.separate.tgt (Sum.inr t) = Sum.inr t := rfl

theorem separate_isRecomb_inl (x : V) : N.separate.IsRecomb (Sum.inl x) ↔ N.IsRecomb x := by
  constructor
  · rintro ⟨e | e, f | f, hne, he, hf⟩
    · exact ⟨e, f, fun h => hne (by rw [h]), Sum.inl.inj he, Sum.inl.inj hf⟩
    · cases hf
    · cases he
    · cases he
  · rintro ⟨e, f, hne, he, hf⟩
    exact ⟨Sum.inl e, Sum.inl f, fun h => hne (Sum.inl.inj h), by simp [he], by simp [hf]⟩

theorem not_separate_isRecomb_inr (t : N.SepTop) : ¬ N.separate.IsRecomb (Sum.inr t) := by
  rintro ⟨e | e, f | f, hne, he, hf⟩
  · cases he
  · cases he
  · cases hf
  · simp only [separate_tgt_inr, Sum.inr.injEq] at he hf
    exact hne (by rw [he, hf])

theorem separate_recombCount : N.separate.recombCount = N.recombCount := by
  refine (Nat.card_eq_of_bijective (fun x : {x // N.IsRecomb x} =>
    (⟨Sum.inl x.1, (separate_isRecomb_inl x.1).2 x.2⟩ : {x // N.separate.IsRecomb x})) ⟨?_, ?_⟩).symm
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
  · rintro ⟨x | t, hx⟩
    · exact ⟨⟨x, (separate_isRecomb_inl x).1 hx⟩, rfl⟩
    · exact absurd hx (not_separate_isRecomb_inr t)

theorem separate_isLeaf_inl (y : V) : N.separate.IsLeaf (Sum.inl y) ↔ N.IsLeaf y := by
  constructor
  · intro h f hf
    rcases newSrc_cases (N := N) f with h' | ⟨t, -, ht, -⟩
    · exact h (Sum.inl f) (by simp [h', hf])
    · exact h (Sum.inr t) (by simp [ht, hf])
  · rintro h (f | t) hf
    · have := congrArg N.sepProj hf
      simp only [separate_src_inl, sepProj_newSrc] at this
      exact h f this
    · simp only [separate_src_inr, Sum.inl.injEq] at hf
      obtain ⟨f, -, hf'⟩ := t.2.exists_src
      exact h f (hf'.trans hf)

theorem not_separate_isLeaf_inr (t : N.SepTop) : ¬ N.separate.IsLeaf (Sum.inr t) := by
  intro h
  obtain ⟨f, hf, hf'⟩ := t.2.exists_src
  exact h (Sum.inl f) (newSrc_eq_inr t hf'.symm hf)

theorem separate_derives {M : Finset (ι → Bool)} (hM : N.Derives M) : N.separate.Derives M := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (y | t) hy
    · exact hM.mapsTo ((separate_isLeaf_inl y).1 hy)
    · exact absurd hy (not_separate_isLeaf_inr t)
  · rintro (y | t) hy (y' | t') hy' h
    · exact congrArg Sum.inl (hM.injOn ((separate_isLeaf_inl y).1 hy) ((separate_isLeaf_inl y').1 hy') h)
    · exact absurd hy' (not_separate_isLeaf_inr t')
    · exact absurd hy (not_separate_isLeaf_inr t)
    · exact absurd hy (not_separate_isLeaf_inr t)
  · intro r hr
    obtain ⟨y, hy, rfl⟩ := hM.surjOn hr
    exact ⟨Sum.inl y, (separate_isLeaf_inl y).2 hy, rfl⟩

theorem separate_ancestral : N.separate.ancestral = N.ancestral := rfl

theorem separate_label_newSrc (f : E) : N.separate.label (N.newSrc f) = N.label (N.src f) :=
  congrArg N.label (sepProj_newSrc f)

theorem separate_obeys [LinearOrder ι] {c : Crossover} (h : N.Obeys c) : N.separate.Obeys c := by
  cases c with
  | single =>
    rintro (x | t) hx
    · obtain ⟨e, f, hne, he, hf, L, hL⟩ := h x ((separate_isRecomb_inl x).1 hx)
      refine ⟨Sum.inl e, Sum.inl f, fun h' => hne (Sum.inl.inj h'), by simp [he], by simp [hf], L, fun i => ?_⟩
      simp only [separate_src_inl, separate_label_newSrc]
      exact hL i
    · exact absurd hx (not_separate_isRecomb_inr t)
  | multiple => trivial
  | pointwise =>
    rintro (x | t) hx
    · obtain ⟨e, f, hne, he, hf, j, hj⟩ := h x ((separate_isRecomb_inl x).1 hx)
      refine ⟨Sum.inl e, Sum.inl f, fun h' => hne (Sum.inl.inj h'), by simp [he], by simp [hf], j, fun i => ?_⟩
      simp only [separate_src_inl, separate_label_newSrc]
      exact hj i
    · exact absurd hx (not_separate_isRecomb_inr t)

/-- The old arcs of a list of arcs of the separated network. -/
def oldArcs (l : List (E ⊕ N.SepTop)) : List E := l.filterMap Sum.getLeft?

theorem mem_oldArcs {l : List (E ⊕ N.SepTop)} {f : E} : f ∈ oldArcs l ↔ Sum.inl f ∈ l := by
  simp [oldArcs, List.mem_filterMap]

/-- A path of the separated network gives a path of `N`. -/
theorem isPath_oldArcs {u v : V ⊕ N.SepTop} {l : List (E ⊕ N.SepTop)} (h : N.separate.IsPath u v l) :
    N.IsPath (N.sepProj u) (N.sepProj v) (oldArcs l) := by
  induction l generalizing u with
  | nil => cases h; rfl
  | cons a l ih =>
    obtain ⟨rfl, h₂⟩ := h
    rcases a with f | t
    · exact ⟨(sepProj_newSrc f).symm, ih h₂⟩
    · exact ih (u := N.separate.tgt (Sum.inr t)) h₂

/-- Where a new arc is on a path that ends at an old node, the next arc is an arc of the blob out of the shared top. -/
theorem IsPath.exists_next_of_inr {u : V ⊕ N.SepTop} {v : V} {l : List (E ⊕ N.SepTop)} {t : N.SepTop}
    (h : N.separate.IsPath u (Sum.inl v) l) (ht : Sum.inr t ∈ l) : ∃ f, Sum.inl f ∈ l ∧ f ∈ t.1.1 := by
  rcases h.tgt_eq_or ht with h' | ⟨a, ha, h'⟩
  · cases h'
  · rcases a with f | t'
    · exact ⟨f, ha, (newSrc_eq_inr_iff.1 h').2⟩
    · cases h'

/-- A recombination cycle of the separated network has no new arc: "the new edge" is on no recombination cycle. -/
theorem IsCycleOn.notMem_inr {w' x' : V ⊕ N.SepTop} {p' q' : List (E ⊕ N.SepTop)}
    (hc : N.separate.IsCycleOn w' x' p' q') (t : N.SepTop) : Sum.inr t ∉ p' := by
  intro ht
  obtain ⟨x, rfl⟩ : ∃ x, x' = Sum.inl x := by
    rcases x' with x | t'
    · exact ⟨x, rfl⟩
    · exact absurd hc.1 (not_separate_isRecomb_inr t')
  have hp := hc.2.1
  have hq := hc.2.2.1
  obtain ⟨f, hfp, hft⟩ := IsPath.exists_next_of_inr hp ht
  -- the old arcs of the cycle are a cycle of `N`
  have hcyc : N.IsCycleOn (N.sepProj w') x (oldArcs p') (oldArcs q') := by
    refine ⟨(separate_isRecomb_inl x).1 hc.1, isPath_oldArcs hp, isPath_oldArcs hq, ?_, ?_⟩
    · intro h
      have hf₁ : f ∈ oldArcs q' := h ▸ mem_oldArcs.2 hfp
      exact hc.notMem hfp (mem_oldArcs.1 hf₁)
    · intro e he g hg heg
      exact Sum.inl.inj (hc.2.2.2.2 _ (mem_oldArcs.1 he) _ (mem_oldArcs.1 hg) (by simp [heg]))
  -- so all its arcs are in the blob of `t`
  have hsub : ∀ g, g ∈ oldArcs p' ∨ g ∈ oldArcs q' → g ∈ t.1.1 :=
    t.2.isBlob.subset_of_mem (Q := {g | g ∈ oldArcs p' ∨ g ∈ oldArcs q'}) ⟨_, _, _, _, hcyc, rfl⟩ hft
      (Or.inl (mem_oldArcs.2 hfp))
  obtain ⟨p₁, p₂, rfl, hp₁, -⟩ := hp.split ht
  rcases List.eq_nil_or_concat' p₁ with rfl | ⟨p₀, g', rfl⟩
  · -- the new arc is first: the other path starts at the same node
    have hw : w' = Sum.inl t.1.2 := hp₁
    have hqne : q' ≠ [] := by
      rintro rfl
      have : w' = Sum.inl x := hq
      have hwx : w' = Sum.inl x := this
      subst hw
      have hpx := hc.2.1
      rw [Sum.inl.inj hwx] at hpx
      have := hpx.eq_nil_of_self
      simp at this
    obtain ⟨a, q₀, rfl⟩ := List.exists_cons_of_ne_nil hqne
    have hsrc : N.separate.src a = Sum.inl t.1.2 := hq.1.trans hw
    rcases a with h | t₂
    · have hh : h ∈ t.1.1 := hsub h (Or.inr (mem_oldArcs.2 (by simp)))
      have := newSrc_eq_inr t (by
        have h₃ := congrArg N.sepProj hsrc
        simp only [separate_src_inl, sepProj_newSrc] at h₃
        exact h₃.symm) hh
      rw [separate_src_inl, this] at hsrc
      cases hsrc
    · have hv : t₂.1.2 = t.1.2 := Sum.inl.inj hsrc
      obtain ⟨f₂, hf₂q, hf₂t⟩ := IsPath.exists_next_of_inr hq (t := t₂) (by simp)
      have hf₂ : f₂ ∈ t.1.1 := hsub f₂ (Or.inr (mem_oldArcs.2 hf₂q))
      have : t₂ = t := SepTop.eq_of_mem hv hf₂t hf₂
      subst this
      exact hc.notMem ht (by simp)
  · -- the arc before the new one enters the shared top from inside the blob
    obtain ⟨y, -, hy⟩ := isPath_append.1 hp₁
    obtain ⟨rfl, hy⟩ := hy
    have hy' : N.separate.tgt g' = Sum.inl t.1.2 := hy
    rcases g' with g | t₂
    · have hg : g ∈ t.1.1 := hsub g (Or.inl (mem_oldArcs.2 (by simp)))
      exact t.2.noArcIn g hg (Sum.inl.inj hy')
    · cases hy'

theorem IsCycleOn.old {w' x' : V ⊕ N.SepTop} {p' q' : List (E ⊕ N.SepTop)} (hc : N.separate.IsCycleOn w' x' p' q') :
    p' = (oldArcs p').map Sum.inl ∧ q' = (oldArcs q').map Sum.inl ∧
      N.IsCycleOn (N.sepProj w') (N.sepProj x') (oldArcs p') (oldArcs q') := by
  have hall : ∀ {l : List (E ⊕ N.SepTop)}, (∀ t, Sum.inr t ∉ l) → l = (oldArcs l).map Sum.inl := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      have hl' : ∀ t, Sum.inr t ∉ l := fun t h => hl t (List.mem_cons_of_mem _ h)
      rcases a with f | t
      · simp only [oldArcs, List.filterMap_cons, Sum.getLeft?_inl, List.map_cons]
        exact congrArg (Sum.inl f :: ·) (ih hl')
      · exact absurd (by simp) (hl t)
  have hp := hall hc.notMem_inr
  have hq := hall hc.symm.notMem_inr
  refine ⟨hp, hq, ?_, isPath_oldArcs hc.2.1, isPath_oldArcs hc.2.2.1, ?_, ?_⟩
  · rcases x' with x | t
    · exact (separate_isRecomb_inl x).1 hc.1
    · exact absurd hc.1 (not_separate_isRecomb_inr t)
  · intro h
    exact hc.2.2.2.1 (by rw [hp, hq, h])
  · intro e he g hg heg
    have := hc.2.2.2.2 _ (mem_oldArcs.1 he) _ (mem_oldArcs.1 hg) (by simp [heg])
    rw [separate_tgt_inl] at this
    rw [← this]
    rfl

/-- The source of an arc of the blob `B`. -/
noncomputable def sepStart (N : Network ι V E) (B : Set E) (u : V) : V ⊕ N.SepTop :=
  if h : N.IsSharedTop B u then Sum.inr ⟨(B, u), h⟩ else Sum.inl u

theorem newSrc_eq_sepStart {B : Set E} (hB : N.IsBlob B) {f : E} (hf : f ∈ B) : N.newSrc f = N.sepStart B (N.src f) := by
  by_cases h : N.IsSharedTop B (N.src f)
  · rw [sepStart, dite_eq_left h]
    exact newSrc_eq_inr ⟨(B, N.src f), h⟩ rfl hf
  · rw [sepStart, dite_eq_right h]
    rcases newSrc_cases (N := N) f with h' | ⟨t, -, h₁, h₂⟩
    · exact h'
    · exfalso
      have hB' : t.1.1 = B := IsBlob.eq_of_inter_nonempty t.2.isBlob hB ⟨f, h₂, hf⟩
      have := t.2
      rw [hB', h₁] at this
      exact h this

theorem sepStart_tgt {B : Set E} {f : E} (hf : f ∈ B) : N.sepStart B (N.tgt f) = Sum.inl (N.tgt f) := by
  rw [sepStart, dite_eq_right]
  exact fun h => h.noArcIn f hf rfl

/-- A nonempty path in a blob stays a path in the separated network. -/
theorem IsPath.sep {B : Set E} (hB : N.IsBlob B) {u v : V} {p : List E} (h : N.IsPath u v p) (hp : p ≠ [])
    (hsub : ∀ f ∈ p, f ∈ B) : N.separate.IsPath (N.sepStart B u) (Sum.inl v) (p.map Sum.inl) := by
  induction p generalizing u with
  | nil => exact absurd rfl hp
  | cons f p ih =>
    obtain ⟨rfl, h₂⟩ := h
    have hf : f ∈ B := hsub f (by simp)
    refine ⟨newSrc_eq_sepStart hB hf, ?_⟩
    rw [separate_tgt_inl]
    cases p with
    | nil =>
      have : N.tgt f = v := h₂
      simp [IsPath, this]
    | cons g p =>
      have := ih h₂ (by simp) (fun f hf => hsub f (List.mem_cons_of_mem _ hf))
      rwa [sepStart_tgt hf] at this

theorem IsCycleOn.ne_nil {w x : V} {p q : List E} (h : N.IsCycleOn w x p q) : p ≠ [] := by
  rintro rfl
  have hw : w = x := h.2.1
  subst hw
  exact h.2.2.2.1 h.2.2.1.eq_nil_of_self.symm

theorem IsCycle.sep {Q : Set E} (hQ : N.IsCycle Q) : N.separate.IsCycle (Sum.inl '' Q) := by
  obtain ⟨B, hB, hQB⟩ : ∃ B, N.IsBlob B ∧ Q ⊆ B :=
    ⟨_, ⟨Q, hQ, rfl⟩, fun e he => ⟨Q, .refl, he⟩⟩
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  refine ⟨N.sepStart B w, Sum.inl x, p.map Sum.inl, q.map Sum.inl, ⟨(separate_isRecomb_inl x).2 hc.1,
    hc.2.1.sep hB hc.ne_nil (fun f hf => hQB (Or.inl hf)),
    hc.2.2.1.sep hB hc.symm.ne_nil (fun f hf => hQB (Or.inr hf)),
    (List.map_injective_iff.2 Sum.inl_injective).ne hc.2.2.2.1, ?_⟩, ?_⟩
  · intro a ha b hb hab
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hb
    simp only [separate_tgt_inl, Sum.inl.injEq] at hab ⊢
    exact hc.2.2.2.2 e he f hf hab
  · exact image_setOf_mem_or_mem _ _ _

/-- A recombination cycle of the separated network is the image of one of `N`. -/
theorem exists_eq_image_of_isCycle {Q' : Set (E ⊕ N.SepTop)} (hQ : N.separate.IsCycle Q') :
    ∃ Q, N.IsCycle Q ∧ Q' = Sum.inl '' Q := by
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  obtain ⟨hp, hq, hc'⟩ := IsCycleOn.old hc
  refine ⟨_, ⟨_, _, _, _, hc', rfl⟩, ?_⟩
  ext a
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro (ha | ha)
    · rw [hp] at ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      exact ⟨e, Or.inl he, rfl⟩
    · rw [hq] at ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      exact ⟨e, Or.inr he, rfl⟩
  · rintro ⟨e, he | he, rfl⟩
    · exact Or.inl (mem_oldArcs.1 he)
    · exact Or.inr (mem_oldArcs.1 he)

theorem separate_onCycle (e : E) : N.separate.OnCycle (Sum.inl e) ↔ N.OnCycle e := by
  constructor
  · rintro ⟨Q', hQ', he⟩
    obtain ⟨Q, hQ, rfl⟩ := exists_eq_image_of_isCycle hQ'
    exact ⟨Q, hQ, Sum.inl_injective.mem_set_image.1 he⟩
  · rintro ⟨Q, hQ, he⟩
    exact ⟨_, hQ.sep, e, he, rfl⟩

theorem separate_isTreeArc (e : E) : N.separate.IsTreeArc (Sum.inl e) ↔ N.IsTreeArc e :=
  not_congr (separate_onCycle e)

theorem IsBlob.sep {B : Set E} (hB : N.IsBlob B) : N.separate.IsBlob (Sum.inl '' B) := by
  obtain ⟨Q, hQ, rfl⟩ := hB
  refine ⟨Sum.inl '' Q, hQ.sep, ?_⟩
  have hf : ∀ {Q₁}, Relation.ReflTransGen N.ShareArc Q Q₁ →
      Relation.ReflTransGen N.separate.ShareArc (Sum.inl '' Q) (Sum.inl '' Q₁) := by
    intro Q₁ h
    induction h with
    | refl => exact .refl
    | tail _ h ih =>
      obtain ⟨h₁, h₂, e, he, he'⟩ := h
      exact ih.tail ⟨h₁.sep, h₂.sep, Sum.inl e, ⟨e, he, rfl⟩, ⟨e, he', rfl⟩⟩
  have hb : ∀ {Q₁'}, Relation.ReflTransGen N.separate.ShareArc (Sum.inl '' Q) Q₁' →
      ∃ Q₁, Q₁' = Sum.inl '' Q₁ ∧ Relation.ReflTransGen N.ShareArc Q Q₁ := by
    intro Q₁' h
    induction h with
    | refl => exact ⟨Q, rfl, .refl⟩
    | tail _ h ih =>
      obtain ⟨Q₁, rfl, hr⟩ := ih
      obtain ⟨h₁, h₂, a, ⟨e, he, rfl⟩, ha'⟩ := h
      obtain ⟨Q₂, hQ₂, rfl⟩ := exists_eq_image_of_isCycle h₂
      obtain ⟨Q₁', hQ₁', hQ₁eq⟩ := exists_eq_image_of_isCycle h₁
      have hQ₁c : N.IsCycle Q₁ := by
        rwa [Sum.inl_injective.image_injective hQ₁eq]
      refine ⟨Q₂, rfl, hr.tail ⟨hQ₁c, hQ₂, e, he, Sum.inl_injective.mem_set_image.1 ha'⟩⟩
  ext a
  constructor
  · rintro ⟨e, ⟨Q₁, hQ₁, he⟩, rfl⟩
    exact ⟨_, hf hQ₁, e, he, rfl⟩
  · rintro ⟨Q₁', hQ₁', ha⟩
    obtain ⟨Q₁, rfl, hr⟩ := hb hQ₁'
    obtain ⟨e, he, rfl⟩ := ha
    exact ⟨e, ⟨Q₁, hr, he⟩, rfl⟩

/-- A blob of the separated network is the image of a blob of `N`. -/
theorem exists_eq_image_of_isBlob {B' : Set (E ⊕ N.SepTop)} (hB : N.separate.IsBlob B') :
    ∃ B, N.IsBlob B ∧ B' = Sum.inl '' B := by
  obtain ⟨Q', hQ', rfl⟩ := hB
  obtain ⟨Q, hQ, rfl⟩ := exists_eq_image_of_isCycle hQ'
  refine ⟨_, ⟨Q, hQ, rfl⟩, ?_⟩
  have := IsBlob.sep (N := N) ⟨Q, hQ, rfl⟩
  obtain ⟨Q₂, hQ₂, heq⟩ := this
  refine IsBlob.eq_of_inter_nonempty ⟨_, hQ', rfl⟩ ⟨Q₂, hQ₂, heq⟩ ?_
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p hc.ne_nil
  exact ⟨Sum.inl e, ⟨_, .refl, e, Or.inl he, rfl⟩, e, ⟨_, .refl, Or.inl he⟩, rfl⟩

theorem separate_exists_isBlob (i j : ι) :
    (∃ B, N.separate.IsBlob B ∧ N.separate.site i ∈ B ∧ N.separate.site j ∈ B) ↔
      ∃ B, N.IsBlob B ∧ N.site i ∈ B ∧ N.site j ∈ B := by
  constructor
  · rintro ⟨B', hB', hi, hj⟩
    obtain ⟨B, hB, rfl⟩ := exists_eq_image_of_isBlob hB'
    exact ⟨B, hB, Sum.inl_injective.mem_set_image.1 hi, Sum.inl_injective.mem_set_image.1 hj⟩
  · rintro ⟨B, hB, hi, hj⟩
    exact ⟨_, hB.sep, ⟨_, hi, rfl⟩, ⟨_, hj, rfl⟩⟩

/-- A node of the image of a blob `B` that is an old node is a node of `B`, and not a shared top of `B`: those have moved. -/
theorem mem_blobVerts_sep_inl {B : Set E} (hB : N.IsBlob B) {v : V}
    (h : Sum.inl v ∈ N.separate.blobVerts (Sum.inl '' B)) : v ∈ N.blobVerts B ∧ ¬ N.IsSharedTop B v := by
  rcases h with ⟨_, ⟨e, he, rfl⟩, h⟩ | ⟨_, ⟨e, he, rfl⟩, h⟩
  · rw [separate_src_inl, newSrc_eq_sepStart hB he] at h
    by_cases hs : N.IsSharedTop B (N.src e)
    · rw [sepStart, dite_eq_left hs] at h
      cases h
    · rw [sepStart, dite_eq_right hs] at h
      obtain rfl := Sum.inl.inj h
      exact ⟨Or.inl ⟨e, he, rfl⟩, hs⟩
  · rw [separate_tgt_inl] at h
    obtain rfl := Sum.inl.inj h
    exact ⟨Or.inr ⟨e, he, rfl⟩, fun hs => hs.noArcIn e he rfl⟩

theorem separate_blobsNodeDisjoint [Finite V] : N.separate.BlobsNodeDisjoint := by
  intro B₁' B₂' hB₁' hB₂' hne
  obtain ⟨B₁, hB₁, rfl⟩ := exists_eq_image_of_isBlob hB₁'
  obtain ⟨B₂, hB₂, rfl⟩ := exists_eq_image_of_isBlob hB₂'
  have hne' : B₁ ≠ B₂ := fun h => hne (by rw [h])
  rw [Set.disjoint_left]
  rintro (v | t) h₁ h₂
  · obtain ⟨hv₁, hn₁⟩ := mem_blobVerts_sep_inl hB₁ h₁
    obtain ⟨hv₂, hn₂⟩ := mem_blobVerts_sep_inl hB₂ h₂
    -- each blob has an arc into `v`, by the two conditions, and then those two arcs are on one cycle
    have hin : ∀ {B B'}, N.IsBlob B → N.IsBlob B' → B ≠ B' → v ∈ N.blobVerts B → v ∈ N.blobVerts B' →
        ¬ N.IsSharedTop B v → ∃ e ∈ B, N.tgt e = v := by
      intro B B' hB hB' hBB' hv hv' hn
      by_contra hno
      push Not at hno
      exact hn ⟨hB, hv, hno, B', hB', hBB'.symm, hv'⟩
    obtain ⟨e₁, he₁, ht₁⟩ := hin hB₁ hB₂ hne' hv₁ hv₂ hn₁
    obtain ⟨e₂, he₂, ht₂⟩ := hin hB₂ hB₁ hne'.symm hv₂ hv₁ hn₂
    have hee : e₁ ≠ e₂ := fun h => hne' (IsBlob.eq_of_inter_nonempty hB₁ hB₂ ⟨e₁, he₁, h ▸ he₂⟩)
    obtain ⟨Q, hQ, h₃, h₄⟩ := exists_isCycle_of_tgt_eq hee (ht₁.trans ht₂.symm)
    have hs₁ := hB₁.subset_of_mem hQ he₁ h₃
    exact hne' (IsBlob.eq_of_inter_nonempty hB₁ hB₂ ⟨e₂, hs₁ h₄, he₂⟩)
  · -- a new node is on one blob only
    have key : ∀ {B}, N.IsBlob B → Sum.inr t ∈ N.separate.blobVerts (Sum.inl '' B) → t.1.1 = B := by
      intro B hB h
      rcases h with ⟨_, ⟨e, he, rfl⟩, h⟩ | ⟨_, ⟨e, he, rfl⟩, h⟩
      · rw [separate_src_inl] at h
        exact IsBlob.eq_of_inter_nonempty t.2.isBlob hB ⟨e, (newSrc_eq_inr_iff.1 h).2, he⟩
      · cases h
    exact hne' ((key hB₁ h₁).symm.trans (key hB₂ h₂))

end Separate

/-- **Line 135** (`g:separate`). "The network can be modified so that the cycle is node-disjoint from any other cycle. The
modification requires adding one new edge and one new node, with the same sequence labeling both ends of the new edge."
Repeating this makes blobs node-disjoint (line 140). It keeps the crossover model, the ancestral sequence, the rows derived,
the number of recombination nodes, and which sites lie on a common blob. So no minimum in the paper depends on the
convention.

The paper describes the modification for one gall, and leaves it at "repeating this as needed". Here it is made at all shared
nodes at once, on blobs (`Network.separate`): a node `v` shared by blobs has an arc into it from at most one of them, because the
two arcs into a recombination node are on one cycle (`exists_isCycle_of_tgt_eq`), so `v` is a top of all the others; a new node
takes the arcs of such a blob out of `v`, and the new edge from `v` is on no cycle (`IsCycleOn.notMem_inr`). -/
theorem exists_blobsNodeDisjoint [LinearOrder ι] [Finite V] [Finite E] {c : Crossover} (hc : N.Obeys c) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.BlobsNodeDisjoint ∧
      N'.ancestral = N.ancestral ∧ N'.recombCount = N.recombCount ∧
      (∀ M, N.Derives M → N'.Derives M) ∧
      (∀ i, N'.IsTreeArc (N'.site i) ↔ N.IsTreeArc (N.site i)) ∧
      (∀ i j, (∃ B, N'.IsBlob B ∧ N'.site i ∈ B ∧ N'.site j ∈ B) ↔ ∃ B, N.IsBlob B ∧ N.site i ∈ B ∧ N.site j ∈ B) := by
  obtain ⟨a, b, N', eV, eE, h⟩ := N.separate.exists_fin_iso
  obtain ⟨h₁, h₂, h₃, h₄, -⟩ := h.invariants
  refine ⟨a, b, N', (h₂ c).2 (separate_obeys hc), h.blobsNodeDisjoint.2 separate_blobsNodeDisjoint, h₄.trans separate_ancestral,
    h₁.trans separate_recombCount, fun M hM => (h₃ M).2 (separate_derives hM), fun i => ?_, fun i j => ?_⟩
  · rw [h.site, h.isTreeArc]
    exact separate_isTreeArc (N.site i)
  · exact (h.exists_isBlob_sites i j).trans (separate_exists_isBlob i j)

end Network

end Gusfield2007
