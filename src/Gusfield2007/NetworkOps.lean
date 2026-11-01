module

public import Gusfield2007.Basic
public import Mathlib.Basic.Finite.Sum

/-!
# Gusfield et al. 2007: operations on phylogenetic networks

What the proofs of Sections 5.2, 5.3 do to a network, and what the cited bounds need:

* where a label can come from (`Network.exists_source`): "each recombination or mutation event in the ancestry creates at most one
  new type" (Myers and Griffiths 2003);
* `Network.trim`, `Network.exists_derives_of_displays`: from a network in which every row labels a node, a network deriving exactly the rows, with no more recombination
  nodes. This is what "the resulting network derives" means in the proofs: Lean's `Derives` has the rows exactly at the leaves. `Decomp.prune` is different: it keeps the leaves of the network, and adds none;
* `Network.reattach`: moving a recombination node under another node with the same label (the proof of Theorem 6);
* `PreNet`: a network given by the parents of its nodes, with sites still to be placed, which is how networks are built up.
-/

@[expose] public noncomputable section

open scoped Classical

namespace Gusfield2007

universe u v w

namespace Network

variable {ι : Type u} {V : Type v} {E : Type w} (N : Network ι V E)

variable {N}

/-- A node with no recombination has only one arc in. -/
theorem eq_of_not_isRecomb {e f : E} (h : ¬ N.IsRecomb (N.tgt e)) (hf : N.tgt f = N.tgt e) : f = e := by
  by_contra hne
  exact h ⟨f, e, hne, hf, rfl⟩

/-- A recombination node has just the two arcs. -/
theorem eq_or_eq_of_tgt {e f g : E} (hef : e ≠ f) (h : N.tgt e = N.tgt f) (hg : N.tgt g = N.tgt e) : g = e ∨ g = f := by
  rcases N.inDegree_le_two g e f hg h with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hef

/-- No site is on an arc into a recombination node. -/
theorem site_ne_of_tgt_eq {e f : E} (hef : e ≠ f) (h : N.tgt e = N.tgt f) (i : ι) : N.site i ≠ e := by
  rintro rfl
  exact hef (N.site_not_recomb i f h.symm).symm

/-- The target of the arc with a site isn't a recombination node. -/
theorem not_isRecomb_tgt_site (i : ι) : ¬ N.IsRecomb (N.tgt (N.site i)) := by
  rintro ⟨e, f, hef, he, hf⟩
  have h₁ := N.site_not_recomb i e he
  have h₂ := N.site_not_recomb i f hf
  exact hef (h₁.trans h₂.symm)

variable (N)

/-- A node other than the root and the target of the arc of `i` has a parent with its state at `i`. -/
theorem exists_parent_label_eq {v : V} {i : ι} (hroot : v ≠ N.root) (htop : v ≠ N.tgt (N.site i)) :
    ∃ g, N.tgt g = v ∧ N.label (N.src g) i = N.label v i := by
  obtain ⟨g, rfl⟩ : ∃ g, N.tgt g = v := by
    by_contra hne
    push Not at hne
    exact hroot ((N.root_iff v).1 hne)
  by_cases hu : ∀ f, N.tgt f = N.tgt g → f = g
  · have hl := N.label_tree g hu i
    rw [ite_eq_right fun hs => htop (by rw [hs])] at hl
    exact ⟨g, rfl, hl.symm⟩
  · push Not at hu
    obtain ⟨f, hf, hne⟩ := hu
    rcases N.label_recomb g f hne.symm hf.symm i with h | h
    · exact ⟨g, rfl, h.symm⟩
    · exact ⟨f, hf, h.symm⟩

/-- **Each site changes once** (lines 94 to 106): a node whose state at the site `i` differs from the root's is below the arc with `i`. -/
theorem reach_of_label_ne [Finite V] {v : V} {i : ι} (h : N.label v i ≠ N.label N.root i) : N.Reach (N.tgt (N.site i)) v := by
  induction v using N.arc_induction with
  | _ v ih =>
    by_cases htop : v = N.tgt (N.site i)
    · rw [htop]
      exact Relation.ReflTransGen.refl
    · obtain ⟨g, hg, hl⟩ := N.exists_parent_label_eq (fun hroot => h (by rw [hroot])) htop
      exact (ih g hg (hl ▸ h)).tail ⟨g, rfl, hg⟩

/-- The state at `i` of the target of the arc with `i` isn't the root's. -/
theorem label_tgt_site_ne [Finite V] (i : ι) : N.label (N.tgt (N.site i)) i ≠ N.label N.root i := by
  have hl := N.label_tree (N.site i) (fun f hf => N.site_not_recomb i f hf) i
  rw [ite_eq_left rfl] at hl
  intro h
  rw [hl] at h
  have hsrc : N.label (N.src (N.site i)) i ≠ N.label N.root i := by
    intro h'
    rw [h'] at h
    simp at h
  have := N.reach_of_label_ne hsrc
  exact N.acyclic _ (Relation.TransGen.tail' this ⟨N.site i, rfl, rfl⟩)

/-- **Where a label comes from** (`g:label_source`). The restriction to the sites `A` of a label is that of the root, of the target of an arc with a site of `A`, or of a
recombination node that isn't a copy of a parent on `A`. This is the argument of Myers and Griffiths 2003, p. 379: "each recombination or mutation event in the ancestry creates at most
one new type". -/
theorem exists_source [Finite V] (A : Set ι) (v : V) :
    ∃ u, (u = N.root ∨ (∃ i ∈ A, u = N.tgt (N.site i)) ∨ (N.IsRecomb u ∧ N.BreaksAt u A)) ∧
      ∀ i ∈ A, N.label v i = N.label u i := by
  induction v using N.arc_induction with
  | _ v ih =>
    by_cases hv : ∀ e, N.tgt e ≠ v
    · exact ⟨v, Or.inl ((N.root_iff v).1 hv), fun _ _ => rfl⟩
    · push Not at hv
      obtain ⟨e, rfl⟩ := hv
      by_cases hr : N.IsRecomb (N.tgt e)
      · by_cases hb : N.BreaksAt (N.tgt e) A
        · exact ⟨_, Or.inr (Or.inr ⟨hr, hb⟩), fun _ _ => rfl⟩
        · unfold BreaksAt at hb
          push Not at hb
          obtain ⟨g, hg, hl⟩ := hb
          obtain ⟨u, hu, hul⟩ := ih g hg
          refine ⟨u, hu, fun i hi => ?_⟩
          have := congrFun hl ⟨i, hi⟩
          exact (show N.label (N.tgt e) i = N.label (N.src g) i from this).trans (hul i hi)
      · by_cases hs : ∃ i ∈ A, N.site i = e
        · obtain ⟨i, hi, rfl⟩ := hs
          exact ⟨_, Or.inr (Or.inl ⟨i, hi, rfl⟩), fun _ _ => rfl⟩
        · push Not at hs
          obtain ⟨u, hu, hul⟩ := ih e rfl
          refine ⟨u, hu, fun i hi => ?_⟩
          have hl := N.label_tree e (fun f hf => eq_of_not_isRecomb hr hf) i
          rw [ite_eq_right (hs i hi)] at hl
          exact hl.trans (hul i hi)

/-- **The four-gamete test** (Hudson and Kaplan 1985, p. 148): two incompatible sites need a recombination that isn't a copy of a parent on them. Without one, the states at the two sites are those of the root or
of the targets of the two arcs with the sites, which is three pairs. -/
theorem exists_breaksAt_of_incompatible [Finite V] {M : Finset (ι → Bool)} (hd : ∀ r ∈ M, ∃ v, N.label v = r)
    {a b : ι} (h : Incompatible M a b) : ∃ x, N.IsRecomb x ∧ N.BreaksAt x {a, b} := by
  by_contra hno
  push Not at hno
  set pat : V → Bool × Bool := fun v => (N.label v a, N.label v b) with hpat
  have hsub : (Finset.univ : Finset (Bool × Bool)) ⊆ {pat N.root, pat (N.tgt (N.site a)), pat (N.tgt (N.site b))} := by
    rintro ⟨p, q⟩ -
    obtain ⟨r, hr, hp, hq⟩ := h p q
    obtain ⟨v, rfl⟩ := hd r hr
    obtain ⟨u, hu, hul⟩ := N.exists_source {a, b} v
    have hval : (p, q) = pat u := by
      rw [hpat]
      exact Prod.ext (hp.symm.trans (hul a (Or.inl rfl))) (hq.symm.trans (hul b (Or.inr rfl)))
    rw [hval]
    rcases hu with rfl | ⟨i, hi, rfl⟩ | ⟨hu₁, hu₂⟩
    · simp
    · rcases hi with rfl | hi
      · simp
      · rw [Set.mem_singleton_iff.1 hi]
        simp
    · exact absurd hu₂ (hno u hu₁)
  have := (Finset.card_le_card hsub).trans Finset.card_le_three
  simp at this

variable {N}

/-- A network deriving `M` shows that `M` isn't empty: it has a leaf. -/
theorem Derives.nonempty [Finite V] {M : Finset (ι → Bool)} (h : N.Derives M) : M.Nonempty := by
  obtain ⟨w, hw, -⟩ := N.exists_isLeaf_reach N.root
  exact ⟨_, h.mapsTo hw⟩

/-- Every row labels a node. -/
theorem Derives.displays {M : Finset (ι → Bool)} (h : N.Derives M) : ∀ r ∈ M, ∃ v, N.label v = r := fun _ hr => by
  obtain ⟨v, -, hv⟩ := h.surjOn hr
  exact ⟨v, hv⟩

/-! ### Trimming -/

section Trim

variable {ι : Type u} {V : Type v} {E : Type w} (N : Network ι V E) {M : Finset (ι → Bool)} (anchor : M → V)

/-- The nodes kept by the trimming: those that reach the node chosen for a row. -/
def Kept (v : V) : Prop := ∃ r, N.Reach v (anchor r)

variable {N anchor}

theorem Kept.src {e : E} (h : N.Kept anchor (N.tgt e)) : N.Kept anchor (N.src e) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, (reach_src_tgt e).trans hr⟩

variable (N anchor)

/-- `N` with only the nodes that reach a chosen node for each row, and a new pendant leaf at that node for each row. -/
def trim [Finite V] (hM : M.Nonempty) (hanchor : ∀ r : M, N.label (anchor r) = r.1) (hsite : ∀ i, N.Kept anchor (N.tgt (N.site i))) :
    Network ι ({v // N.Kept anchor v} ⊕ M) ({e // N.Kept anchor (N.tgt e)} ⊕ M) where
  src := Sum.elim (fun e => .inl ⟨N.src e.1, e.2.src⟩) (fun r => .inl ⟨anchor r, r, Relation.ReflTransGen.refl⟩)
  tgt := Sum.elim (fun e => .inl ⟨N.tgt e.1, e.2⟩) .inr
  root := .inl ⟨N.root, by
    obtain ⟨r, hr⟩ := hM
    exact ⟨⟨r, hr⟩, N.reach_root _⟩⟩
  site i := .inl ⟨N.site i, hsite i⟩
  label := Sum.elim (fun v => N.label v.1) (fun r => r.1)
  simple := by
    rintro (e | r) (f | r') h₁ h₂
    · simp only [Sum.elim_inl, Sum.inl.injEq, Subtype.mk.injEq] at h₁ h₂
      exact congrArg Sum.inl (Subtype.ext (N.simple _ _ h₁ h₂))
    · simp at h₂
    · simp at h₂
    · simpa using h₂
  acyclic := by
    obtain ⟨ρ, hρ⟩ := N.exists_rank
    refine acyclic_of_rank (Sum.elim (fun v => ρ v.1) (fun r => ρ (anchor r) + 1)) ?_
    rintro (e | r)
    · exact hρ e.1
    · exact Nat.lt_succ_self _
  root_iff := by
    rintro (v | r)
    · constructor
      · intro h
        have : ∀ e, N.tgt e ≠ v.1 := fun e he =>
          h (.inl ⟨e, he ▸ v.2⟩) (by simp only [Sum.elim_inl, Sum.inl.injEq]; exact Subtype.ext he)
        have := (N.root_iff v.1).1 this
        exact congrArg Sum.inl (Subtype.ext this)
      · intro h
        have hv : v.1 = N.root := congrArg Subtype.val (Sum.inl.inj h)
        rintro (e | r) he
        · exact (N.root_iff _).2 hv e.1 (congrArg Subtype.val (Sum.inl.inj he))
        · exact absurd he (by simp)
    · constructor
      · intro h
        exact absurd rfl (h (.inr r))
      · intro h
        simp at h
  inDegree_le_two := by
    rintro (e | r) (f | r') (g | r'') h₁ h₂ <;> simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h₁ h₂ ⊢
    · have h₁' := congrArg Subtype.val h₁
      have h₂' := congrArg Subtype.val h₂
      simp only at h₁' h₂'
      rcases N.inDegree_le_two e.1 f.1 g.1 h₁' h₂' with h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
    · exact Or.inl h₁
  site_not_recomb := by
    rintro i (e | r) h
    · simp only [Sum.elim_inl, Sum.inl.injEq] at h ⊢
      exact Subtype.ext (N.site_not_recomb i e.1 (congrArg Subtype.val h))
    · simp at h
  label_tree := by
    rintro (e | r) he i
    · have huniq : ∀ f, N.tgt f = N.tgt e.1 → f = e.1 := fun f hf => by
        have := he (.inl ⟨f, by rw [hf]; exact e.2⟩) (by simp only [Sum.elim_inl, Sum.inl.injEq]; exact Subtype.ext hf)
        exact congrArg Subtype.val (Sum.inl.inj this)
      simp only [Sum.elim_inl, Sum.inl.injEq, Subtype.ext_iff]
      exact N.label_tree e.1 huniq i
    · simp only [Sum.elim_inr, Sum.elim_inl, reduceCtorEq, ↓reduceIte]
      exact (congrFun (hanchor r) i).symm
  label_recomb := by
    rintro (e | r) (f | r') hef h i
    · simp only [Sum.elim_inl, Sum.inl.injEq, Subtype.mk.injEq] at h ⊢
      exact N.label_recomb e.1 f.1 (fun h' => hef (congrArg Sum.inl (Subtype.ext h'))) h i
    · simp at h
    · simp at h
    · simp only [Sum.elim_inr, Sum.inr.injEq] at h
      exact absurd (by rw [h]) hef

variable {N anchor}

section

variable [Finite V] {hM : M.Nonempty} {hanchor : ∀ r : M, N.label (anchor r) = r.1} {hsite : ∀ i, N.Kept anchor (N.tgt (N.site i))}

theorem trim_isLeaf_iff (x : {v // N.Kept anchor v} ⊕ M) : (N.trim anchor hM hanchor hsite).IsLeaf x ↔ ∃ r, x = .inr r := by
  constructor
  · rcases x with v | r
    · intro h
      exfalso
      obtain ⟨v, r, hv⟩ := v
      rcases Relation.ReflTransGen.cases_head hv with rfl | ⟨b, ⟨e, rfl, rfl⟩, hb⟩
      · exact h (.inr r) rfl
      · exact h (.inl ⟨e, r, hb⟩) rfl
    · exact fun _ => ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩ (e | r') he <;> simp [trim] at he

theorem trim_derives : (N.trim anchor hM hanchor hsite).Derives M := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, rfl⟩ := trim_isLeaf_iff x |>.1 hx
    exact r.2
  · intro x hx y hy hxy
    obtain ⟨r, rfl⟩ := trim_isLeaf_iff x |>.1 hx
    obtain ⟨r', rfl⟩ := trim_isLeaf_iff y |>.1 hy
    exact congrArg _ (Subtype.ext hxy)
  · intro r hr
    exact ⟨.inr ⟨r, hr⟩, (trim_isLeaf_iff _).2 ⟨_, rfl⟩, rfl⟩

theorem trim_isRecomb {v : {v // N.Kept anchor v}} (h : (N.trim anchor hM hanchor hsite).IsRecomb (.inl v)) : N.IsRecomb v.1 := by
  obtain ⟨e, f, hef, he, hf⟩ := h
  rcases e with e | r
  · rcases f with f | r
    · simp only [trim, Sum.elim_inl, Sum.inl.injEq, Subtype.ext_iff] at he hf
      exact ⟨e.1, f.1, fun h' => hef (congrArg _ (Subtype.ext h')), he, hf⟩
    · simp [trim] at hf
  · simp [trim] at he

theorem not_trim_isRecomb_inr {r : M} : ¬ (N.trim anchor hM hanchor hsite).IsRecomb (.inr r) := by
  rintro ⟨e, f, hef, he, hf⟩
  rcases e with e | r₁
  · simp [trim] at he
  · rcases f with f | r₂
    · simp [trim] at hf
    · simp only [trim, Sum.elim_inr, Sum.inr.injEq] at he hf
      exact hef (by rw [he, hf])

theorem trim_obeys [LinearOrder ι] {c : Crossover} (h : N.Obeys c) : (N.trim anchor hM hanchor hsite).Obeys c := by
  rw [obeys_iff] at h ⊢
  rintro (v | r) hx
  · obtain ⟨e, f, hef, he, hf, hrec⟩ := h v.1 (trim_isRecomb hx)
    exact ⟨.inl ⟨e, he ▸ v.2⟩, .inl ⟨f, hf ▸ v.2⟩, fun h' => hef (congrArg Subtype.val (Sum.inl.inj h')),
      congrArg Sum.inl (Subtype.ext he), congrArg Sum.inl (Subtype.ext hf), hrec⟩
  · exact absurd hx not_trim_isRecomb_inr

theorem trim_recombCount_le : (N.trim anchor hM hanchor hsite).recombCount ≤ Nat.card {x // N.IsRecomb x ∧ N.Kept anchor x} := by
  have hf : ∀ x : {x // (N.trim anchor hM hanchor hsite).IsRecomb x}, ∃ y : {x // N.IsRecomb x ∧ N.Kept anchor x}, x.1 = .inl ⟨y.1, y.2.2⟩ := by
    rintro ⟨v | r, hx⟩
    · exact ⟨⟨v.1, trim_isRecomb hx, v.2⟩, rfl⟩
    · exact absurd hx not_trim_isRecomb_inr
  choose g hg using hf
  refine Nat.card_le_card_of_injective g fun x y hxy => Subtype.ext ?_
  rw [hg x, hg y, hxy]

/-- A node of the trimmed network that breaks a set of sites breaks it in the original network: it has the same parents. -/
theorem trim_breaksAt {v : {v // N.Kept anchor v}} {C : Set ι} (h : (N.trim anchor hM hanchor hsite).BreaksAt (.inl v) C) : N.BreaksAt v.1 C := by
  intro e he
  exact h (.inl ⟨e, he ▸ v.2⟩) (congrArg Sum.inl (Subtype.ext he))

end

/-- The node of a row is below the arc of a site, if the row has the site's state off the ancestral one. -/
theorem kept_tgt_site [Finite V] (hanchor : ∀ r : M, N.label (anchor r) = r.1) {i : ι} (hs : ∃ r ∈ M, r i ≠ N.label N.root i) : N.Kept anchor (N.tgt (N.site i)) := by
  obtain ⟨r, hr, hne⟩ := hs
  exact ⟨⟨r, hr⟩, N.reach_of_label_ne (by rwa [hanchor ⟨r, hr⟩])⟩

/-- **Trimming, with the recombination nodes kept.** Given a node for each row of `M`, there's a network deriving exactly `M`, with the same ancestral sequence, in every crossover
model that `N` obeys, with no recombination nodes other than the ones above the chosen nodes. The condition on the sites says that the arc of each is kept. -/
theorem exists_trim [LinearOrder ι] [Finite V] [Finite E] (N : Network ι V E) {anchor : M → V} (hM : M.Nonempty) (hanchor : ∀ r : M, N.label (anchor r) = r.1)
    (hs : ∀ i, ∃ r ∈ M, r i ≠ N.label N.root i) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), (∀ c, N.Obeys c → N'.Obeys c) ∧ N'.Derives M ∧
      N'.ancestral = N.ancestral ∧ N'.recombCount ≤ Nat.card {x // N.IsRecomb x ∧ N.Kept anchor x} := by
  obtain ⟨a, b, N', eV, eE, h⟩ := (N.trim anchor hM hanchor fun i => kept_tgt_site hanchor (hs i)).exists_fin_iso
  obtain ⟨h₁, h₂, h₃, h₄, -⟩ := h.invariants
  refine ⟨a, b, N', fun c hc => (h₂ c).2 (trim_obeys hc), (h₃ M).2 trim_derives, h₄, ?_⟩
  rw [h₁]
  exact trim_recombCount_le

/-- **Trimming** (`g:trim`). If every row of `M` labels a node of `N` and no column of `M` is constant, then there's a network deriving `M`, with the same ancestral sequence, in every crossover model
that `N` obeys, with no more recombination nodes. A row can be at an internal node of `N`, or at a recombination node: it gets a pendant arc, as the caption of Figure 1 does. Other leaves are removed. No
site is lost: a site whose arc reaches no row would give a constant column. -/
theorem exists_derives_of_displays [LinearOrder ι] [Finite V] [Finite E] {M : Finset (ι → Bool)} (N : Network ι V E) (hM : M.Nonempty) (hC : NoConstantColumn M)
    (hd : ∀ r ∈ M, ∃ v, N.label v = r) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), (∀ c, N.Obeys c → N'.Obeys c) ∧ N'.Derives M ∧
      N'.ancestral = N.ancestral ∧ N'.recombCount ≤ N.recombCount := by
  choose anchor hanchor using fun r : M => hd r.1 r.2
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄⟩ := N.exists_trim hM hanchor fun i => hC.exists_ne _ i
  refine ⟨a, b, N', h₁, h₂, h₃, h₄.trans ?_⟩
  exact Nat.card_le_card_of_injective (fun x => (⟨x.1, x.2.1⟩ : {x // N.IsRecomb x})) fun x y h =>
    Subtype.ext (congrArg (fun z : {x // N.IsRecomb x} => z.1) h)

end Trim

/-! ### Duplicating sites -/

section Restrict

variable {ι : Type u} {V : Type v} {E : Type w} (N : Network ι V E)

/-- `N` on sites `ι`, each on the arc of `ρ i` and a copy of it: "each duplicate on its representative's arc". -/
def liftSites {κ : Type*} (N : Network κ V E) (ρ : ι → κ) : Network ι V E where
  src := N.src
  tgt := N.tgt
  root := N.root
  site i := N.site (ρ i)
  label v i := N.label v (ρ i)
  simple := N.simple
  acyclic := N.acyclic
  root_iff := N.root_iff
  inDegree_le_two := N.inDegree_le_two
  site_not_recomb i := N.site_not_recomb (ρ i)
  label_tree e he i := N.label_tree e he (ρ i)
  label_recomb e f hef h i := N.label_recomb e f hef h (ρ i)

section Topology

variable {κ : Type*} (N : Network κ V E) (ρ : ι → κ)

/-- Cycles and blobs depend only on the arcs. -/
theorem isPath_liftSites (u v : V) (p : List E) : (N.liftSites ρ).IsPath u v p ↔ N.IsPath u v p := by
  induction p generalizing u with
  | nil => exact Iff.rfl
  | cons e p ih => exact and_congr Iff.rfl (ih _)

theorem isCycle_liftSites (Q : Set E) : (N.liftSites ρ).IsCycle Q ↔ N.IsCycle Q := by
  unfold IsCycle IsCycleOn
  simp only [isPath_liftSites]
  rfl

theorem isTreeArc_liftSites (e : E) : (N.liftSites ρ).IsTreeArc e ↔ N.IsTreeArc e := by
  unfold IsTreeArc OnCycle
  simp only [isCycle_liftSites]

theorem isBlob_liftSites (B : Set E) : (N.liftSites ρ).IsBlob B ↔ N.IsBlob B := by
  have h : (N.liftSites ρ).ShareArc = N.ShareArc := by
    funext Q Q'
    simp only [ShareArc, isCycle_liftSites]
  unfold IsBlob
  simp only [isCycle_liftSites, h]

theorem blobsNodeDisjoint_liftSites : (N.liftSites ρ).BlobsNodeDisjoint ↔ N.BlobsNodeDisjoint := by
  unfold BlobsNodeDisjoint
  simp only [isBlob_liftSites]
  rfl

end Topology

end Restrict

/-! ### Reattaching a recombination node -/

section Reattach

variable {ι : Type u} {V : Type v} {E : Type w}

/-- A relation with one more arc is acyclic, if the arc closes no cycle. -/
theorem acyclic_of_add_arc {α : Type*} {r r' : α → α → Prop} {y x : α} (hr : ∀ a, ¬ Relation.TransGen r a a)
    (hle : ∀ a b, r' a b → r a b ∨ (a = y ∧ b = x)) (hxy : ¬ Relation.ReflTransGen r x y) (a : α) :
    ¬ Relation.TransGen r' a a := by
  have key : ∀ a b, Relation.TransGen r' a b →
      Relation.TransGen r a b ∨ (Relation.ReflTransGen r x b ∧ Relation.ReflTransGen r a y) := by
    intro a b h
    induction h with
    | single hab =>
      rcases hle _ _ hab with h | ⟨rfl, rfl⟩
      · exact Or.inl (Relation.TransGen.single h)
      · exact Or.inr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    | tail _ hbc ih =>
      rcases hle _ _ hbc with h | ⟨rfl, rfl⟩
      · rcases ih with ih | ⟨ih₁, ih₂⟩
        · exact Or.inl (ih.tail h)
        · exact Or.inr ⟨ih₁.tail h, ih₂⟩
      · rcases ih with ih | ⟨ih₁, ih₂⟩
        · exact Or.inr ⟨Relation.ReflTransGen.refl, ih.to_reflTransGen⟩
        · exact absurd ih₁ hxy
  intro h
  rcases key a a h with h | ⟨h₁, h₂⟩
  · exact hr a h
  · exact hxy (h₁.trans h₂)

/-- The recombination node `x`, with arcs `e`, `f` in, moved under a node `y` with its label and not below it: `f` is removed and `e` starts at `y`. "We can modify `N`, while maintaining the
conditions of the theorem, so that `N` does not contain two recombination nodes labeled by the same sequence" (line 576). -/
def reattach (N : Network ι V E) {e f : E} (hef : e ≠ f) (he : N.tgt e = N.tgt f) {y : V} (hl : N.label y = N.label (N.tgt e))
    (hy : ¬ N.Reach (N.tgt e) y) : Network ι V {g // g ≠ f} where
  src g := if g.1 = e then y else N.src g.1
  tgt g := N.tgt g.1
  root := N.root
  site i := ⟨N.site i, site_ne_of_tgt_eq hef.symm he.symm i⟩
  label := N.label
  simple := by
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ h₁ h₂
    simp only at h₁ h₂
    apply Subtype.ext
    simp only
    by_cases hx : N.tgt g = N.tgt e
    · rcases eq_or_eq_of_tgt hef he hx with h | h
      · rcases eq_or_eq_of_tgt hef he (h₂.symm.trans hx) with h' | h'
        · rw [h, h']
        · exact absurd h' hg'
      · exact absurd h hg
    · have h₁' : g ≠ e := fun h => hx (by rw [h])
      have h₂' : g' ≠ e := fun h => hx (by rw [h₂, h])
      rw [ite_eq_right h₁', ite_eq_right h₂'] at h₁
      exact N.simple _ _ h₁ h₂
  acyclic := by
    refine acyclic_of_add_arc (r := N.Arc) (y := y) (x := N.tgt e) N.acyclic ?_ hy
    rintro a b ⟨⟨g, hg⟩, rfl, rfl⟩
    simp only
    by_cases hge : g = e
    · right
      simp [hge]
    · left
      exact ⟨g, by simp [hge], rfl⟩
  root_iff v := by
    refine ⟨fun h => (N.root_iff v).1 fun g hg => ?_, fun h g => (N.root_iff v).2 h g.1⟩
    by_cases hgf : g = f
    · subst hgf
      exact h ⟨e, hef⟩ (he.trans hg)
    · exact h ⟨g, hgf⟩ hg
  inDegree_le_two a b c h₁ h₂ := by
    rcases N.inDegree_le_two a.1 b.1 c.1 h₁ h₂ with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  site_not_recomb i g h := Subtype.ext (N.site_not_recomb i g.1 h)
  label_tree := by
    rintro ⟨g, hg⟩ hu i
    simp only
    by_cases hge : g = e
    · subst hge
      rw [ite_eq_left rfl]
      have hs : ¬ (⟨N.site i, site_ne_of_tgt_eq hef.symm he.symm i⟩ : {g // g ≠ f}) = ⟨g, hg⟩ := fun h =>
        site_ne_of_tgt_eq hef he i (congrArg Subtype.val h)
      rw [ite_eq_right hs, hl]
    · rw [ite_eq_right hge]
      have huniq : ∀ k, N.tgt k = N.tgt g → k = g := by
        intro k hk
        by_cases hkf : k = f
        · subst hkf
          have hx : N.tgt g = N.tgt e := hk.symm.trans he.symm
          rcases eq_or_eq_of_tgt hef he hx with h | h
          · exact absurd h hge
          · exact absurd h hg
        · exact congrArg Subtype.val (hu ⟨k, hkf⟩ hk)
      simpa [Subtype.ext_iff] using N.label_tree g huniq i
  label_recomb := by
    rintro ⟨g, hg⟩ ⟨k, hk⟩ hgk h i
    simp only at h ⊢
    have hgk' : g ≠ k := fun h => hgk (Subtype.ext h)
    have hx : N.tgt g ≠ N.tgt e := by
      intro hx
      rcases eq_or_eq_of_tgt hef he hx with h₁ | h₁
      · rcases eq_or_eq_of_tgt hef he (h.symm.trans hx) with h₂ | h₂
        · exact hgk' (h₁.trans h₂.symm)
        · exact hk h₂
      · exact hg h₁
    have h₁ : g ≠ e := fun h' => hx (by rw [h'])
    have h₂ : k ≠ e := fun h' => hx (by rw [h, h'])
    rw [ite_eq_right h₁, ite_eq_right h₂]
    exact N.label_recomb g k hgk' h i

variable {N : Network ι V E} {e f : E} {hef : e ≠ f} {he : N.tgt e = N.tgt f} {y : V} {hl : N.label y = N.label (N.tgt e)}
  {hy : ¬ N.Reach (N.tgt e) y}

/-- The recombination nodes after `reattach`: those of `N` but `x`. -/
theorem isRecomb_reattach {v : V} : (N.reattach hef he hl hy).IsRecomb v ↔ N.IsRecomb v ∧ v ≠ N.tgt e := by
  constructor
  · rintro ⟨⟨g, hg⟩, ⟨k, hk⟩, hgk, h₁, h₂⟩
    refine ⟨⟨g, k, fun h => hgk (Subtype.ext h), h₁, h₂⟩, ?_⟩
    rintro rfl
    have hgk' : g ≠ k := fun h => hgk (Subtype.ext h)
    rcases eq_or_eq_of_tgt hef he h₁ with h | h
    · rcases eq_or_eq_of_tgt hef he h₂ with h' | h'
      · exact hgk' (h.trans h'.symm)
      · exact hk h'
    · exact hg h
  · rintro ⟨⟨g, k, hgk, h₁, h₂⟩, hv⟩
    have hgf : g ≠ f := by
      rintro rfl
      exact hv (h₁.symm.trans he.symm)
    have hkf : k ≠ f := by
      rintro rfl
      exact hv (h₂.symm.trans he.symm)
    exact ⟨⟨g, hgf⟩, ⟨k, hkf⟩, fun h => hgk (congrArg Subtype.val h), h₁, h₂⟩

/-- `reattach` lowers the number of recombination nodes. -/
theorem recombCount_reattach_lt [Finite V] : (N.reattach hef he hl hy).recombCount < N.recombCount := by
  have hsub : {v | (N.reattach hef he hl hy).IsRecomb v} ⊂ {v | N.IsRecomb v} := by
    refine ⟨fun v hv => (isRecomb_reattach.1 hv).1, fun h => ?_⟩
    have hx : N.IsRecomb (N.tgt e) := ⟨e, f, hef, rfl, he.symm⟩
    exact (isRecomb_reattach.1 (h hx)).2 rfl
  have := Set.ncard_lt_ncard hsub (Set.toFinite _)
  exact this

/-- `reattach` keeps every crossover model. -/
theorem obeys_reattach [LinearOrder ι] {c : Crossover} (h : N.Obeys c) : (N.reattach hef he hl hy).Obeys c := by
  rw [obeys_iff] at h ⊢
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := isRecomb_reattach.1 hx
  obtain ⟨g, k, hgk, h₁, h₂, hrec⟩ := h x hx₁
  have hge : g ≠ e := by
    rintro rfl
    exact hx₂ h₁.symm
  have hke : k ≠ e := by
    rintro rfl
    exact hx₂ h₂.symm
  have hgf : g ≠ f := by
    rintro rfl
    exact hx₂ (h₁.symm.trans he.symm)
  have hkf : k ≠ f := by
    rintro rfl
    exact hx₂ (h₂.symm.trans he.symm)
  refine ⟨⟨g, hgf⟩, ⟨k, hkf⟩, fun h => hgk (congrArg Subtype.val h), h₁, h₂, ?_⟩
  change Recombinant c (N.label (if g = e then y else N.src g)) (N.label (if k = e then y else N.src k)) (N.label x)
  rw [ite_eq_right hge, ite_eq_right hke]
  exact hrec

end Reattach

end Network

/-! ### Networks given by the parents of their nodes -/

/-- A network given by the parents of its nodes, some of its sites still to be placed. `par v` is the parent of a non-recombination node `v`, and the second parent, the one that supplies the suffix or the changed site, of a recombination node; `par₂ v` is the other parent of
a recombination node. `site i = some v` when the site `i` is on the arc from `par v` to `v`. -/
structure PreNet (ι : Type u) (V : Type v) where
  /-- The root. -/
  root : V
  /-- The parent. -/
  par : V → Option V
  /-- The other parent, at a recombination node. -/
  par₂ : V → Option V
  /-- The node at the end of the arc with a site. -/
  site : ι → Option V
  /-- The labels. -/
  label : V → ι → Bool
  par_eq_none : ∀ v, par v = none ↔ v = root
  par₂_root : par₂ root = none
  par₂_ne : ∀ v q, par₂ v = some q → par v ≠ some q
  acyclic : ∀ v, ¬ Relation.TransGen (fun a b => par b = some a ∨ par₂ b = some a) v v
  site_tree : ∀ i v, site i = some v → par₂ v = none ∧ v ≠ root
  label_tree : ∀ v p, par v = some p → par₂ v = none → ∀ i, label v i = if site i = some v then !label p i else label p i
  label_recomb : ∀ v p q, par v = some p → par₂ v = some q → ∀ i, label v i = label p i ∨ label v i = label q i

namespace PreNet

variable {ι : Type u} {V : Type v} (P : PreNet ι V)

/-- The number of recombination nodes. -/
def recombCount : ℕ := Nat.card {x // P.par₂ x ≠ none}

/-- The network of a `PreNet` with all its sites placed. The arcs are the nodes with a parent, and the nodes with a second parent. -/
def toNetwork (hs : ∀ i, ∃ v, P.site i = some v) : Network ι V ({v // P.par v ≠ none} ⊕ {v // P.par₂ v ≠ none}) where
  src := Sum.elim (fun v => (P.par v.1).get (Option.isSome_iff_ne_none.2 v.2)) (fun v => (P.par₂ v.1).get (Option.isSome_iff_ne_none.2 v.2))
  tgt := Sum.elim (fun v => v.1) (fun v => v.1)
  root := P.root
  site i := .inl ⟨(hs i).choose, fun h => (P.site_tree i _ (hs i).choose_spec).2 ((P.par_eq_none _).1 h)⟩
  label := P.label
  simple := by
    have hmix : ∀ (v : {v // P.par v ≠ none}) (w : {v // P.par₂ v ≠ none}),
        (P.par v.1).get (Option.isSome_iff_ne_none.2 v.2) = (P.par₂ w.1).get (Option.isSome_iff_ne_none.2 w.2) → v.1 ≠ w.1 := by
      intro v w h hvw
      have h₁ : P.par₂ w.1 = some ((P.par₂ w.1).get (Option.isSome_iff_ne_none.2 w.2)) := (Option.some_get _).symm
      refine P.par₂_ne w.1 _ h₁ ?_
      exact (congrArg P.par hvw.symm).trans ((Option.some_get _).symm.trans (congrArg some h))
    rintro (v | v) (w | w) h₁ h₂
    · exact congrArg Sum.inl (Subtype.ext h₂)
    · exact absurd h₂ (hmix v w h₁)
    · exact absurd h₂.symm (hmix w v h₁.symm)
    · exact congrArg Sum.inr (Subtype.ext h₂)
  acyclic v h := by
    refine P.acyclic v (Relation.TransGen.mono ?_ _ _ h)
    rintro a b ⟨(e | e), rfl, rfl⟩
    · exact Or.inl (Option.some_get _).symm
    · exact Or.inr (Option.some_get _).symm
  root_iff v := by
    constructor
    · intro h
      by_contra hv
      exact h (.inl ⟨v, fun h' => hv ((P.par_eq_none v).1 h')⟩) rfl
    · rintro rfl (e | e) h
      · exact e.2 ((P.par_eq_none _).2 h)
      · apply e.2
        change e.1 = _ at h
        rw [h]
        exact P.par₂_root
  inDegree_le_two := by
    rintro (e | e) (f | f) (g | g) h₁ h₂ <;> simp only [Sum.elim_inl, Sum.elim_inr] at h₁ h₂
    · exact Or.inl (congrArg Sum.inl (Subtype.ext h₁))
    · exact Or.inl (congrArg Sum.inl (Subtype.ext h₁))
    · exact Or.inr (Or.inl (congrArg Sum.inl (Subtype.ext (h₁.trans h₂))))
    · exact Or.inr (Or.inr (congrArg Sum.inr (Subtype.ext h₂)))
    · exact Or.inr (Or.inr (congrArg Sum.inl (Subtype.ext h₂)))
    · exact Or.inr (Or.inl (congrArg Sum.inr (Subtype.ext (h₁.trans h₂))))
    · exact Or.inl (congrArg Sum.inr (Subtype.ext h₁))
    · exact Or.inl (congrArg Sum.inr (Subtype.ext h₁))
  site_not_recomb := by
    rintro i (e | e) h
    · simp only [Sum.elim_inl] at h
      exact congrArg Sum.inl (Subtype.ext h)
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      exact absurd (h ▸ (P.site_tree i _ (hs i).choose_spec).1) e.2
  label_tree := by
    rintro (e | e) he i
    · have hn : P.par₂ e.1 = none := by
        by_contra hne
        have := he (.inr ⟨e.1, hne⟩) rfl
        simp at this
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 e.2
      have hl := P.label_tree e.1 p hp hn i
      simp only [Sum.elim_inl, Sum.inl.injEq, Subtype.ext_iff]
      have hget : (P.par e.1).get (Option.isSome_iff_ne_none.2 e.2) = p := by simp [hp]
      rw [hget, hl]
      have hiff : P.site i = some e.1 ↔ (hs i).choose = e.1 :=
        ⟨fun h' => Option.some_inj.1 ((hs i).choose_spec.symm.trans h'), fun h' => (hs i).choose_spec.trans (congrArg some h')⟩
      by_cases hc : (hs i).choose = e.1
      · rw [ite_eq_left hc, ite_eq_left (hiff.2 hc)]
      · rw [ite_eq_right hc, ite_eq_right fun h' => hc (hiff.1 h')]
    · have hne : P.par e.1 ≠ none := by
        intro h
        apply e.2
        rw [(P.par_eq_none _).1 h]
        exact P.par₂_root
      have := he (.inl ⟨e.1, hne⟩) rfl
      simp at this
  label_recomb := by
    rintro (e | e) (f | f) hef h i <;> simp only [Sum.elim_inl, Sum.elim_inr] at h ⊢
    · exact absurd (congrArg Sum.inl (Subtype.ext h)) hef
    · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 e.2
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 f.2
      have hl := P.label_recomb e.1 p q hp (h ▸ hq) i
      have hg₁ : (P.par e.1).get (Option.isSome_iff_ne_none.2 e.2) = p := by simp [hp]
      have hg₂ : (P.par₂ f.1).get (Option.isSome_iff_ne_none.2 f.2) = q := by simp [hq]
      rw [hg₁, hg₂]
      exact hl
    · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 f.2
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 e.2
      have hl := P.label_recomb e.1 p q (h ▸ hp) hq i
      have hg₁ : (P.par f.1).get (Option.isSome_iff_ne_none.2 f.2) = p := by simp [hp]
      have hg₂ : (P.par₂ e.1).get (Option.isSome_iff_ne_none.2 e.2) = q := by simp [hq]
      rw [hg₁, hg₂]
      exact hl.symm
    · exact absurd (congrArg Sum.inr (Subtype.ext h)) hef

/-- **A network from a `PreNet`** (`g:prenet`). If all the sites are placed and every row of `M` labels a node, there is a network deriving `M`, with the ancestral sequence of the `PreNet`. -/
theorem exists_network [LinearOrder ι] [Finite V] {c : Crossover} {M : Finset (ι → Bool)} (hs : ∀ i, ∃ v, P.site i = some v)
    (hobeys : ∀ x p q, P.par x = some p → P.par₂ x = some q → Recombinant c (P.label q) (P.label p) (P.label x))
    (hM : M.Nonempty) (hC : NoConstantColumn M) (hd : ∀ r ∈ M, ∃ v, P.label v = r) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = P.label P.root ∧ N.recombCount ≤ P.recombCount := by
  set N := P.toNetwork hs with hN
  have hrec : ∀ x, N.IsRecomb x → P.par₂ x ≠ none := by
    rintro x ⟨e | e, f | f, hef, he, hf⟩
    · exact absurd (congrArg Sum.inl (Subtype.ext (he.trans hf.symm))) hef
    · exact (hf : f.1 = x) ▸ f.2
    · exact (he : e.1 = x) ▸ e.2
    · exact (he : e.1 = x) ▸ e.2
  have hobeysN : N.Obeys c := by
    rw [Network.obeys_iff]
    intro x hx
    have hq := hrec x hx
    have hp : P.par x ≠ none := by
      intro h
      apply hq
      rw [(P.par_eq_none _).1 h]
      exact P.par₂_root
    refine ⟨.inr ⟨x, hq⟩, .inl ⟨x, hp⟩, by simp, rfl, rfl, ?_⟩
    obtain ⟨p, hp'⟩ := Option.ne_none_iff_exists'.1 hp
    obtain ⟨q, hq'⟩ := Option.ne_none_iff_exists'.1 hq
    have := hobeys x p q hp' hq'
    have hg₁ : (P.par x).get (Option.isSome_iff_ne_none.2 hp) = p := by simp [hp']
    have hg₂ : (P.par₂ x).get (Option.isSome_iff_ne_none.2 hq) = q := by simp [hq']
    change Recombinant c (P.label ((P.par₂ x).get _)) (P.label ((P.par x).get _)) (P.label x)
    rw [hg₁, hg₂]
    exact this
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄⟩ := Network.exists_derives_of_displays N hM hC hd
  refine ⟨a, b, N', h₁ c hobeysN, h₂, h₃, h₄.trans ?_⟩
  exact Set.ncard_le_ncard (s := {x | N.IsRecomb x}) (t := {x | P.par₂ x ≠ none}) hrec (Set.toFinite _)

/-- A new node, a child of `p`: by the sites `s` if there's no other parent `q`. -/
def extend (p : V) (q : Option V) (h : ι → Bool) (s : ι → Prop) (hs : ∀ j, s j → P.site j = none)
    (hq : ∀ q₀, q = some q₀ → q₀ ≠ p ∧ (∀ j, h j = P.label p j ∨ h j = P.label q₀ j) ∧ ∀ j, ¬ s j)
    (hq' : q = none → ∀ j, h j = if s j then !P.label p j else P.label p j) : PreNet ι (Option V) where
  root := some P.root
  par := fun v => match v with
    | none => some (some p)
    | some v => (P.par v).map some
  par₂ := fun v => match v with
    | none => q.map some
    | some v => (P.par₂ v).map some
  site j := if s j then some none else (P.site j).map some
  label := fun v => match v with
    | none => h
    | some v => P.label v
  par_eq_none := by
    rintro (- | v)
    · simp
    · simp [P.par_eq_none]
  par₂_root := by simp [P.par₂_root]
  par₂_ne := by
    rintro (- | v) w hw
    · simp only [Option.map_eq_some_iff] at hw
      obtain ⟨q₀, rfl, rfl⟩ := hw
      intro h'
      exact (hq q₀ rfl).1 (Option.some_inj.1 (Option.some_inj.1 h')).symm
    · simp only [Option.map_eq_some_iff] at hw
      obtain ⟨q₀, hq₀, rfl⟩ := hw
      intro h'
      simp only [Option.map_eq_some_iff] at h'
      obtain ⟨p₀, hp₀, h''⟩ := h'
      exact P.par₂_ne v q₀ hq₀ (hp₀.trans (congrArg some (Option.some_inj.1 h'')))
  acyclic := by
    have key : ∀ x y, Relation.TransGen (fun a b : Option V => (match b with
        | none => some (some p)
        | some v => (P.par v).map some) = some a ∨ (match b with
        | none => q.map some
        | some v => (P.par₂ v).map some) = some a) x y →
        ∀ b, y = some b → ∃ a, x = some a ∧ Relation.TransGen (fun a b => P.par b = some a ∨ P.par₂ b = some a) a b := by
      intro x y hxy
      induction hxy with
      | single hab =>
        rintro b rfl
        rcases hab with hab | hab <;> simp only [Option.map_eq_some_iff] at hab <;> obtain ⟨a, ha, rfl⟩ := hab
        · exact ⟨a, rfl, Relation.TransGen.single (Or.inl ha)⟩
        · exact ⟨a, rfl, Relation.TransGen.single (Or.inr ha)⟩
      | tail _ hbc ih =>
        rintro b rfl
        rcases hbc with hab | hab <;> simp only [Option.map_eq_some_iff] at hab <;> obtain ⟨a, ha, rfl⟩ := hab
        · obtain ⟨a', rfl, h'⟩ := ih a rfl
          exact ⟨a', rfl, h'.tail (Or.inl ha)⟩
        · obtain ⟨a', rfl, h'⟩ := ih a rfl
          exact ⟨a', rfl, h'.tail (Or.inr ha)⟩
    rintro (- | v) hv
    · obtain ⟨y, hy, -⟩ := Relation.TransGen.head'_iff.1 hv
      rcases y with - | y
      · rcases hy with hy | hy
        · simp at hy
        · simp only [Option.map_eq_some_iff] at hy
          obtain ⟨_, -, h'⟩ := hy
          simp at h'
      · rcases hy with hy | hy <;> simp only [Option.map_eq_some_iff] at hy <;> obtain ⟨_, -, h'⟩ := hy <;> simp at h'
    · obtain ⟨a, ha, h'⟩ := key _ _ hv v rfl
      cases ha
      exact P.acyclic _ h'
  site_tree := by
    intro i v hv
    by_cases hi : s i
    · simp only [hi, ↓reduceIte, Option.some.injEq] at hv
      subst hv
      refine ⟨?_, by simp⟩
      cases hqq : q with
      | none => rfl
      | some q₀ => exact absurd hi ((hq q₀ hqq).2.2 i)
    · simp only [hi, ↓reduceIte, Option.map_eq_some_iff] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      obtain ⟨h₁, h₂⟩ := P.site_tree i w hw
      simp [h₁, h₂]
  label_tree := by
    rintro (- | v) w hw hw₂ i
    · simp only [Option.some.injEq] at hw
      subst hw
      have hqn : q = none := by simpa using hw₂
      simp only
      rw [hq' hqn i]
      simp
    · simp only [Option.map_eq_some_iff] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      have hw₂' : P.par₂ v = none := by simpa using hw₂
      simp only
      rw [P.label_tree v w' hw' hw₂' i]
      by_cases hi : s i
      · have := hs i hi
        simp [hi, this]
      · simp [hi]
  label_recomb := by
    rintro (- | v) w w' hw hw' i
    · simp only [Option.some.injEq] at hw
      subst hw
      simp only [Option.map_eq_some_iff] at hw'
      obtain ⟨q₀, rfl, rfl⟩ := hw'
      exact (hq q₀ rfl).2.1 i
    · simp only [Option.map_eq_some_iff] at hw hw'
      obtain ⟨a, ha, rfl⟩ := hw
      obtain ⟨b, hb, rfl⟩ := hw'
      exact P.label_recomb v a b ha hb i

end PreNet

end Gusfield2007
