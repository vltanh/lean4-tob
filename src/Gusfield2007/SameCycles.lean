module

public import Gusfield2007.BlobFacts

/-!
# Gusfield et al. 2007: two networks with the same recombination cycles

A surgery on a network that only touches tree arcs doesn't change its recombination cycles. `Network.SameCycles` is what has to be checked for that: the arcs on cycles of `N` have the same ends in `N'`, through injections on nodes and arcs, and two arcs of `N'` into one node come from two arcs of `N` into one node. The rest follows: the cycles, the blobs, the nodes of the blobs, the recombination nodes, the crossover model, and being fully decomposed.

It's used for the surgeries `Network.hubNet` (line 330), `Network.rerootNet`, `Decomp.addLeaf`, `Network.entryNet` (line 329 for `IsEfficientAtEntry`) and `Network.dropRoot` (line 299 with the root at any node).
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

namespace Network

universe u

variable {ι : Type u} {V E V' E' : Type*}

/-- If the recombination cycles of `N'` are the images of those of `N`, then so are its blobs. -/
theorem isBlob_iff_of_isCycle_iff {N : Network ι V E} {N' : Network ι V' E'} (em : E → E') (hem : Function.Injective em)
    (hc : ∀ Q', N'.IsCycle Q' ↔ ∃ Q, N.IsCycle Q ∧ Q' = em '' Q) (B' : Set E') : N'.IsBlob B' ↔ ∃ B, N.IsBlob B ∧ B' = em '' B := by
  have hshare : ∀ {Q : Set E} {P' : Set E'}, Relation.ReflTransGen N'.ShareArc (em '' Q) P' → N.IsCycle Q →
      ∃ P, Relation.ReflTransGen N.ShareArc Q P ∧ P' = em '' P := by
    intro Q P' hP hQ
    induction hP with
    | refl => exact ⟨Q, Relation.ReflTransGen.refl, rfl⟩
    | tail _ hs ih =>
      obtain ⟨P₁, hP₁, rfl⟩ := ih
      obtain ⟨-, hc', k, hk, hk'⟩ := hs
      obtain ⟨P₂, hP₂, rfl⟩ := (hc _).1 hc'
      obtain ⟨a, ha, rfl⟩ := hk
      obtain ⟨a', ha', haa⟩ := hk'
      obtain rfl : a' = a := hem haa
      have hP₁c : N.IsCycle P₁ := by
        clear ha
        induction hP₁ with
        | refl => exact hQ
        | tail _ h' _ => exact h'.2.1
      exact ⟨P₂, hP₁.tail ⟨hP₁c, hP₂, a', ha, ha'⟩, rfl⟩
  have hshare' : ∀ {Q P : Set E}, Relation.ReflTransGen N.ShareArc Q P → N.IsCycle Q →
      Relation.ReflTransGen N'.ShareArc (em '' Q) (em '' P) := by
    intro Q P hP hQ
    induction hP with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih =>
      obtain ⟨hP₁, hP₂, k, hk, hk'⟩ := hs
      exact ih.tail ⟨(hc _).2 ⟨_, hP₁, rfl⟩, (hc _).2 ⟨_, hP₂, rfl⟩, em k, ⟨k, hk, rfl⟩, ⟨k, hk', rfl⟩⟩
  constructor
  · rintro ⟨Q', hQ', rfl⟩
    obtain ⟨Q, hQ, rfl⟩ := (hc _).1 hQ'
    refine ⟨_, ⟨Q, hQ, rfl⟩, ?_⟩
    ext k
    constructor
    · rintro ⟨P', hP', hk⟩
      obtain ⟨P, hP, rfl⟩ := hshare hP' hQ
      obtain ⟨a, ha, rfl⟩ := hk
      exact ⟨a, ⟨P, hP, ha⟩, rfl⟩
    · rintro ⟨a, ⟨P, hP, ha⟩, rfl⟩
      exact ⟨_, hshare' hP hQ, ⟨a, ha, rfl⟩⟩
  · rintro ⟨B, ⟨Q, hQ, rfl⟩, rfl⟩
    refine ⟨_, (hc _).2 ⟨Q, hQ, rfl⟩, ?_⟩
    ext k
    constructor
    · rintro ⟨a, ⟨P, hP, ha⟩, rfl⟩
      exact ⟨_, hshare' hP hQ, ⟨a, ha, rfl⟩⟩
    · rintro ⟨P', hP', hk⟩
      obtain ⟨P, hP, rfl⟩ := hshare hP' hQ
      obtain ⟨a, ha, rfl⟩ := hk
      exact ⟨a, ⟨P, hP, ha⟩, rfl⟩

/-- `N'` has the recombination cycles of `N`, through the injections `f` on nodes and `g` on arcs. -/
structure SameCycles (N : Network ι V E) (N' : Network ι V' E') (f : V → V') (g : E → E') : Prop where
  f_inj : Function.Injective f
  g_inj : Function.Injective g
  src : ∀ e, N.OnCycle e → N'.src (g e) = f (N.src e)
  tgt : ∀ e, N.OnCycle e → N'.tgt (g e) = f (N.tgt e)
  recomb : ∀ e' h', e' ≠ h' → N'.tgt e' = N'.tgt h' → ∃ e h, e ≠ h ∧ N.tgt e = N.tgt h ∧ g e = e' ∧ g h = h'

namespace SameCycles

variable {N : Network ι V E} {N' : Network ι V' E'} {f : V → V'} {g : E → E'} (h : SameCycles N N' f g) [Finite V]

include h

omit [Finite V] in
/-- A path on arcs of cycles of `N` is a path of `N'`. -/
theorem isPath : ∀ {l : List E} {u v : V}, N.IsPath u v l → (∀ k ∈ l, N.OnCycle k) → N'.IsPath (f u) (f v) (l.map g)
  | [], _, _, hp, _ => congrArg f hp
  | k :: _, _, _, ⟨h₁, h₂⟩, hl => by
    have hk := hl k List.mem_cons_self
    refine ⟨(h.src k hk).trans (congrArg f h₁), ?_⟩
    rw [h.tgt k hk]
    exact isPath h₂ fun k' hk' => hl k' (List.mem_cons_of_mem _ hk')

/-- A cycle of `N` is a cycle of `N'`. -/
theorem isCycleOn {w x : V} {p q : List E} (hc : N.IsCycleOn w x p q) : N'.IsCycleOn (f w) (f x) (p.map g) (q.map g) := by
  have honp : ∀ k ∈ p, N.OnCycle k := fun k hk => hc.onCycle_left hk
  have honq : ∀ k ∈ q, N.OnCycle k := fun k hk => hc.onCycle_right hk
  obtain ⟨⟨e₁, e₂, hne, h₁, h₂⟩, hp, hq, hpq, hd⟩ := hc
  have he₁ : N.OnCycle e₁ := onCycle_of_tgt_eq hne (h₁.trans h₂.symm)
  have he₂ : N.OnCycle e₂ := onCycle_of_tgt_eq hne.symm (h₂.trans h₁.symm)
  refine ⟨⟨g e₁, g e₂, h.g_inj.ne hne, by rw [h.tgt _ he₁, h₁], by rw [h.tgt _ he₂, h₂]⟩, h.isPath hp honp, h.isPath hq honq,
    fun heq => hpq (List.map_injective_iff.2 h.g_inj heq), ?_⟩
  intro a ha b hb hab
  obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  rw [h.tgt _ (honp a' ha'), h.tgt _ (honq b' hb')] at hab
  rw [h.tgt _ (honp a' ha'), hd a' ha' b' hb' (h.f_inj hab)]

theorem isCycle_image {Q : Set E} (hQ : N.IsCycle Q) : N'.IsCycle (g '' Q) := by
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  exact ⟨f w, f x, p.map g, q.map g, h.isCycleOn hc, image_setOf_mem_or_mem g p q⟩

theorem onCycle_image {e : E} (he : N.OnCycle e) : N'.OnCycle (g e) := by
  obtain ⟨Q, hQ, heQ⟩ := he
  exact ⟨_, h.isCycle_image hQ, ⟨e, heQ, rfl⟩⟩

/-- An arc on a cycle of `N'` comes from an arc on a cycle of `N`. -/
theorem onCycle_back [Finite V'] {k' : E'} (hk' : N'.OnCycle k') : ∃ k, N.OnCycle k ∧ g k = k' := by
  by_contra hno
  push Not at hno
  refine isTreeArc_of_forall_tgt_eq (N := N') (g := k') (fun f' hf' => ?_) (fun f₁ f₂ hne ht => ?_) hk'
  · by_contra hne
    obtain ⟨e, l, hel, htt, -, hl⟩ := h.recomb f' k' hne hf'
    exact hno l (onCycle_of_tgt_eq hel.symm htt.symm) hl
  · obtain ⟨e, l, hel, htt, rfl, rfl⟩ := h.recomb f₁ f₂ hne ht
    obtain ⟨w, p, q, hp, hq, hc⟩ := exists_isCycleOn_of_tgt_eq hel htt
    have honp : ∀ k ∈ p, N.OnCycle k := fun k hk => hc.onCycle_left (List.mem_append_left _ hk)
    have honq : ∀ k ∈ q, N.OnCycle k := fun k hk => hc.onCycle_right (List.mem_append_left _ hk)
    have hel₁ : N.OnCycle e := onCycle_of_tgt_eq hel htt
    have hel₂ : N.OnCycle l := onCycle_of_tgt_eq hel.symm htt.symm
    refine ⟨f w, p.map g, q.map g, ?_, ?_, ?_, ?_⟩
    · rw [h.src _ hel₁]
      exact h.isPath hp honp
    · rw [h.src _ hel₂]
      exact h.isPath hq honq
    · intro hm
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
      exact hno a (honp a ha) rfl
    · intro hm
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
      exact hno a (honq a ha) rfl

variable [Finite V']

theorem onCycle_iff {e : E} : N'.OnCycle (g e) ↔ N.OnCycle e := by
  refine ⟨fun he => ?_, h.onCycle_image⟩
  obtain ⟨k, hk, hke⟩ := h.onCycle_back he
  rwa [← h.g_inj hke]

/-- A path of `N'` on arcs of cycles, ending at a node of `N`, is a path of `N`. -/
theorem isPath_back : ∀ {l' : List E'} {u' v' : V'}, N'.IsPath u' v' l' → (∀ k ∈ l', N'.OnCycle k) → ∀ {x : V}, v' = f x →
    ∃ w l, u' = f w ∧ l' = l.map g ∧ N.IsPath w x l
  | [], _, _, hp, _, x, hx => by
    cases hp
    exact ⟨x, [], hx, rfl, rfl⟩
  | k' :: l', _, _, ⟨rfl, h₂⟩, hl, x, hx => by
    obtain ⟨k, hk, rfl⟩ := h.onCycle_back (hl k' List.mem_cons_self)
    obtain ⟨w, l, hw, hl', hp⟩ := isPath_back h₂ (fun a ha => hl a (List.mem_cons_of_mem _ ha)) hx
    rw [h.tgt k hk] at hw
    obtain rfl := h.f_inj hw
    exact ⟨N.src k, k :: l, h.src k hk, by simp [hl'], rfl, hp⟩

omit [Finite V'] in
/-- A recombination node of `N'` is a recombination node of `N`. -/
theorem exists_of_isRecomb {x' : V'} (hx : N'.IsRecomb x') : ∃ x, x' = f x ∧ N.IsRecomb x := by
  obtain ⟨e', h', hne, rfl, hh⟩ := hx
  obtain ⟨e, l, hel, htt, rfl, rfl⟩ := h.recomb e' h' hne hh.symm
  exact ⟨N.tgt e, h.tgt e (onCycle_of_tgt_eq hel htt), ⟨e, l, hel, rfl, htt.symm⟩⟩

omit [Finite V'] in
theorem isRecomb_image {x : V} (hx : N.IsRecomb x) : N'.IsRecomb (f x) := by
  obtain ⟨e, l, hne, rfl, hl⟩ := hx
  exact ⟨g e, g l, h.g_inj.ne hne, h.tgt e (onCycle_of_tgt_eq hne hl.symm), (h.tgt l (onCycle_of_tgt_eq hne.symm hl)).trans (congrArg f hl)⟩

omit [Finite V'] in
theorem isRecomb_iff {x : V} : N'.IsRecomb (f x) ↔ N.IsRecomb x := by
  refine ⟨fun hx => ?_, h.isRecomb_image⟩
  obtain ⟨y, hy, hr⟩ := h.exists_of_isRecomb hx
  rwa [h.f_inj hy]

/-- A cycle of `N'` is a cycle of `N`. -/
theorem isCycleOn_back {w' x' : V'} {p' q' : List E'} (hc : N'.IsCycleOn w' x' p' q') : ∃ w x p q, p' = p.map g ∧ q' = q.map g ∧ N.IsCycleOn w x p q := by
  have honp : ∀ k ∈ p', N'.OnCycle k := fun k hk => hc.onCycle_left hk
  have honq : ∀ k ∈ q', N'.OnCycle k := fun k hk => hc.onCycle_right hk
  obtain ⟨hrec, hp, hq, hpq, hd⟩ := hc
  obtain ⟨x, rfl, hx⟩ := h.exists_of_isRecomb hrec
  obtain ⟨w, p, rfl, rfl, hpN⟩ := h.isPath_back hp honp rfl
  obtain ⟨w₂, q, hw₂, rfl, hqN⟩ := h.isPath_back hq honq rfl
  obtain rfl := h.f_inj hw₂
  refine ⟨w, x, p, q, rfl, rfl, hx, hpN, hqN, fun heq => hpq (by rw [heq]), ?_⟩
  intro a ha b hb hab
  have ha₁ := (h.onCycle_iff).1 (honp _ (List.mem_map_of_mem ha))
  have hb₁ := (h.onCycle_iff).1 (honq _ (List.mem_map_of_mem hb))
  apply h.f_inj
  rw [← h.tgt a ha₁]
  refine hd (g a) (List.mem_map_of_mem ha) (g b) (List.mem_map_of_mem hb) ?_
  rw [h.tgt a ha₁, h.tgt b hb₁, hab]

/-- **The cycles of `N'` are those of `N`.** -/
theorem isCycle_iff (Q' : Set E') : N'.IsCycle Q' ↔ ∃ Q, N.IsCycle Q ∧ Q' = g '' Q := by
  constructor
  · rintro ⟨w', x', p', q', hc, rfl⟩
    obtain ⟨w, x, p, q, rfl, rfl, hc₀⟩ := h.isCycleOn_back hc
    exact ⟨_, ⟨w, x, p, q, hc₀, rfl⟩, (image_setOf_mem_or_mem g p q).symm⟩
  · rintro ⟨Q, hQ, rfl⟩
    exact h.isCycle_image hQ

/-- **The blobs of `N'` are those of `N`.** -/
theorem isBlob_iff (B' : Set E') : N'.IsBlob B' ↔ ∃ B, N.IsBlob B ∧ B' = g '' B :=
  isBlob_iff_of_isCycle_iff g h.g_inj h.isCycle_iff B'

omit [Finite V] [Finite V'] in
/-- The nodes of a blob of `N'` are those of `N`. -/
theorem blobVerts_image {B : Set E} (hB : N.IsBlob B) : N'.blobVerts (g '' B) = f '' N.blobVerts B := by
  ext z
  constructor
  · rintro (⟨_, ⟨a, ha, rfl⟩, rfl⟩ | ⟨_, ⟨a, ha, rfl⟩, rfl⟩)
    · exact ⟨_, src_mem_blobVerts ha, (h.src a (hB.onCycle_of_mem ha)).symm⟩
    · exact ⟨_, tgt_mem_blobVerts ha, (h.tgt a (hB.onCycle_of_mem ha)).symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩, rfl⟩
    · exact Or.inl ⟨g a, ⟨a, ha, rfl⟩, h.src a (hB.onCycle_of_mem ha)⟩
    · exact Or.inr ⟨g a, ⟨a, ha, rfl⟩, h.tgt a (hB.onCycle_of_mem ha)⟩

omit [Finite V] [Finite V'] in
theorem mem_blobVerts_iff {B : Set E} (hB : N.IsBlob B) {z : V} : f z ∈ N'.blobVerts (g '' B) ↔ z ∈ N.blobVerts B := by
  rw [h.blobVerts_image hB, h.f_inj.mem_set_image]

theorem blobsNodeDisjoint_iff : N'.BlobsNodeDisjoint ↔ N.BlobsNodeDisjoint := by
  constructor
  · intro hd B₁ B₂ hB₁ hB₂ hne
    have := hd _ _ ((h.isBlob_iff _).2 ⟨B₁, hB₁, rfl⟩) ((h.isBlob_iff _).2 ⟨B₂, hB₂, rfl⟩) (fun heq => hne (h.g_inj.image_injective heq))
    rw [h.blobVerts_image hB₁, h.blobVerts_image hB₂] at this
    exact (Set.disjoint_image_iff h.f_inj).1 this
  · intro hd B₁ B₂ hB₁ hB₂ hne
    obtain ⟨B₁, hB₁', rfl⟩ := (h.isBlob_iff _).1 hB₁
    obtain ⟨B₂, hB₂', rfl⟩ := (h.isBlob_iff _).1 hB₂
    rw [h.blobVerts_image hB₁', h.blobVerts_image hB₂']
    exact (Set.disjoint_image_iff h.f_inj).2 (hd B₁ B₂ hB₁' hB₂' fun heq => hne (by rw [heq]))

/-- `N'` is fully decomposed if and only if `N` is, if the sites are on the arcs that correspond. -/
theorem isFullyDecomposedFor_iff (hsite : ∀ i, N'.site i = g (N.site i)) {G : SimpleGraph ι} : N'.IsFullyDecomposedFor G ↔ N.IsFullyDecomposedFor G := by
  have hmem : ∀ (B : Set E) (i : ι), N'.site i ∈ g '' B ↔ N.site i ∈ B := fun B i => by
    rw [hsite, h.g_inj.mem_set_image]
  constructor
  · intro hf
    refine ⟨fun B hB => ?_, fun i hi => ?_, h.blobsNodeDisjoint_iff.1 hf.nodeDisjoint⟩
    · obtain ⟨c, hc, hi⟩ := hf.blob_component _ ((h.isBlob_iff _).2 ⟨B, hB, rfl⟩)
      exact ⟨c, hc, fun i => by rw [← hmem, hi]⟩
    · have := hf.isolated_treeArc i hi
      rw [hsite] at this
      exact fun hc => this (h.onCycle_image hc)
  · intro hf
    refine ⟨fun B' hB' => ?_, fun i hi => ?_, h.blobsNodeDisjoint_iff.2 hf.nodeDisjoint⟩
    · obtain ⟨B, hB, rfl⟩ := (h.isBlob_iff _).1 hB'
      obtain ⟨c, hc, hi⟩ := hf.blob_component B hB
      exact ⟨c, hc, fun i => by rw [hmem, hi]⟩
    · rw [hsite]
      exact fun hc => hf.isolated_treeArc i hi ((h.onCycle_iff).1 hc)

omit [Finite V'] in
/-- `N'` has the recombination nodes of `N`. -/
theorem recombCount_eq : N'.recombCount = N.recombCount := by
  refine Nat.card_congr (Equiv.ofBijective (fun x : {x // N.IsRecomb x} => (⟨f x.1, h.isRecomb_image x.2⟩ : {x // N'.IsRecomb x})) ⟨?_, ?_⟩).symm
  · intro x y hxy
    exact Subtype.ext (h.f_inj (congrArg Subtype.val hxy))
  · rintro ⟨x', hx'⟩
    obtain ⟨x, rfl, hx⟩ := h.exists_of_isRecomb hx'
    exact ⟨⟨x, hx⟩, rfl⟩

omit [Finite V'] in
/-- `N'` obeys the crossover models of `N`, if the labels agree on the nodes that correspond. -/
theorem obeys [LinearOrder ι] (hl : ∀ x, N'.label (f x) = N.label x) {c : Crossover} (hc : N.Obeys c) : N'.Obeys c := by
  cases c with
  | single =>
    intro x' hx'
    obtain ⟨x, rfl, hx⟩ := h.exists_of_isRecomb hx'
    obtain ⟨e, l, hel, he, hl', L, hL⟩ := hc x hx
    have hee : N.OnCycle e := onCycle_of_tgt_eq hel (he.trans hl'.symm)
    have hll : N.OnCycle l := onCycle_of_tgt_eq hel.symm (hl'.trans he.symm)
    refine ⟨g e, g l, h.g_inj.ne hel, by rw [h.tgt e hee, he], by rw [h.tgt l hll, hl'], L, fun i => ?_⟩
    rw [h.src e hee, h.src l hll, hl, hl, hl]
    exact hL i
  | multiple => trivial
  | pointwise =>
    intro x' hx'
    obtain ⟨x, rfl, hx⟩ := h.exists_of_isRecomb hx'
    obtain ⟨e, l, hel, he, hl', j, hL⟩ := hc x hx
    have hee : N.OnCycle e := onCycle_of_tgt_eq hel (he.trans hl'.symm)
    have hll : N.OnCycle l := onCycle_of_tgt_eq hel.symm (hl'.trans he.symm)
    refine ⟨g e, g l, h.g_inj.ne hel, by rw [h.tgt e hee, he], by rw [h.tgt l hll, hl'], j, fun i => ?_⟩
    rw [h.src e hee, h.src l hll, hl, hl, hl]
    exact hL i

end SameCycles

end Network

end Gusfield2007
