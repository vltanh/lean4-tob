module

public import External.GusfieldEtAl2004.Optimality
public import External.Gusfield1991.PerfectPhylogeny

/-!
# If there is a galled tree, there is a reduced one (Gusfield, Eddhu, Langley 2004)

See the `README.md` of this directory. Corollary 5.1 of the source: "If there is a galled-tree for `M`, then there is a reduced galled-tree for `M`. Moreover, the number of recombinations used by any reduced galled-tree for `M` is the number of non-trivial connected components in the conflict
graph, and this is the minimum number of recombinations possible over all galled-trees for `M`." Gusfield et al. 2007 cite the first sentence at line 180. It gives the first sentence of Theorem 2.7 of the source (`theorem2_7`).

## The difference from the source

Departure from the source. The source works on one gall at a time: a gall with no conflicted sites is replaced by a perfect phylogeny (the proof of Theorem 2.7), and the unconflicted sites of the other galls are moved off them one at a time, by a case analysis (Lemma 5.1, Theorem 5.1).
That analysis uses the standing assumption that the columns are distinct ("in order for the columns in `M` for `p` and `q` to be different"), which line 180 of Gusfield et al. 2007 doesn't have, and which the matrices of Section 8 of the source don't keep. Also, the claim in the proof of Theorem 2.7
that "the sequences labeling the nodes on `Q` can be derived on a perfect phylogeny" needs the sites to be unconflicted among the labels of the nodes, and they are only unconflicted among the rows: a recombination node whose parents have no other edge out has a label that makes a conflict no
row shows.

So here each non-trivial component `C` of the conflict graph gets a network of its own, from the gall that has its sites (Theorem 2.4): the gall alone, with only the sites of `C` (`gallNet`), and a new leaf for each sequence of `M(C)` other than the ancestral one, trimmed. The states on the gall are all of the
rows of `M(C)`, by Lemma 2.1. Then the construction of Theorem 1 of Gusfield et al. 2007 glues these networks over the tree of the compatible sites (`IsTBar.exists_glued`). All the compatible sites go on tree edges at once. The crossovers are those of the gall on the sites of `C`, so the model is kept. There's
one recombination node for each component, and so each blob is a single cycle (`isGalledTree_of_isFullyDecomposedFor`).

The hypothesis is the source's standing assumption that "each column has at least one entry that is 1", in the form that each column has a state other than the ancestral sequence's in some row: without it a reduced galled tree can't exist, since a site on a tree edge shows at the leaves below it.
-/

@[expose] public noncomputable section

open scoped Classical

namespace GusfieldEtAl2004

open Gusfield2007 Gusfield2007.Network Gusfield2007.Decomp

variable {ι V E : Type*}

/-! ### Blobs with one recombination node -/

section OneRecomb

variable {N : Network ι V E} {w x w' : V} {p q p' q' : List E}

/-- Two paths to one node, with no choice of arc going back, are the end of one another. -/
theorem path_suffix_of_unique {u u' : V} {l : List E} : ∀ {v : V} {l' : List E}, N.IsPath u v l → N.IsPath u' v l' → (∀ e ∈ l, ∀ f ∈ l', N.tgt e = N.tgt f → e = f) → l <:+ l' ∨ l' <:+ l := by
  induction l using List.reverseRecOn with
  | nil => exact fun _ _ _ => Or.inl List.nil_suffix
  | append_singleton l₀ a ih =>
    intro v l' h h' huniq
    rcases List.eq_nil_or_concat' l' with rfl | ⟨l₀', a', rfl⟩
    · exact Or.inr List.nil_suffix
    · obtain ⟨y, h₁, hy, hv⟩ := isPath_append.1 h
      obtain ⟨y', h₁', hy', hv'⟩ := isPath_append.1 h'
      have hv₀ : N.tgt a = v := hv
      have hv₀' : N.tgt a' = v := hv'
      have haa : a = a' := huniq a (by simp) a' (by simp) (hv₀.trans hv₀'.symm)
      subst haa
      have hyy : y' = y := hy'.symm.trans hy
      rw [hyy] at h₁'
      rcases ih h₁ h₁' (fun e he f hf => huniq e (by simp [he]) f (by simp [hf])) with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact Or.inl ⟨t, by rw [← ht]; simp⟩
      · exact Or.inr ⟨t, by rw [← ht]; simp⟩

theorem IsPath.start_eq {u u' v v' : V} {l : List E} (h : N.IsPath u v l) (h' : N.IsPath u' v' l) (hl : l ≠ []) : u = u' := by
  cases l with
  | nil => exact absurd rfl hl
  | cons e l => exact h.1.symm.trans h'.1

/-- A step of `cycle_unique`: if `p` is the end of `p'`, and `q` the end of `q'`, then the second cycle has nothing above the first, or its two paths would meet at the coalescent node of the first. -/
theorem cycle_unique_aux (hc : N.IsCycleOn w x p q) (hc' : N.IsCycleOn w' x p' q') {t t' : List E} (hp : p' = t ++ p) (hq : q' = t' ++ q) : t = [] ∧ t' = [] := by
  have hpa := hc'.2.1
  rw [hp, isPath_append] at hpa
  obtain ⟨y, h₁, h₂⟩ := hpa
  have hyw : y = w := IsPath.start_eq h₂ hc.2.1 hc.ne_nil
  rw [hyw] at h₁
  have hqa := hc'.2.2.1
  rw [hq, isPath_append] at hqa
  obtain ⟨y', h₁', h₂'⟩ := hqa
  have hyw' : y' = w := IsPath.start_eq h₂' hc.2.2.1 hc.symm.ne_nil
  rw [hyw'] at h₁'
  by_cases ht : t = []
  · subst ht
    have hw : w' = w := h₁
    rw [hw] at h₁'
    exact ⟨rfl, h₁'.eq_nil_of_self⟩
  · have ht' : t' ≠ [] := by
      rintro rfl
      have hw : w' = w := h₁'
      rw [hw] at h₁
      exact ht h₁.eq_nil_of_self
    exfalso
    obtain ⟨_, g, hg, -, hgt⟩ := h₁.exists_last_arc ht
    obtain ⟨_, g', hg', -, hgt'⟩ := h₁'.exists_last_arc ht'
    have hyx : w = x := by
      rw [← hgt]
      refine hc'.2.2.2.2 g ?_ g' ?_ (hgt.trans hgt'.symm)
      · rw [hp, hg]
        simp
      · rw [hq, hg']
        simp
    have hself : N.IsPath x x p := hyx ▸ hc.2.1
    exact hc.ne_nil hself.eq_nil_of_self

/-- Paths each way between two nodes are empty. -/
theorem paths_nil_of_both {u v : V} {t t' : List E} (h : N.IsPath u v t) (h' : N.IsPath v u t') : t = [] ∧ t' = [] := by
  have huv : u = v := Reach.antisymm h.reach h'.reach
  subst huv
  exact ⟨h.eq_nil_of_self, h'.eq_nil_of_self⟩

/-- **A blob with one recombination node is one cycle.** Two recombination cycles with one recombination node, the first with no other on it, are one cycle: going back from the node, there is no choice of arc. -/
theorem cycle_unique [Finite V] (hc : N.IsCycleOn w x p q) (hc' : N.IsCycleOn w' x p' q')
    (hrec : ∀ y, y ≠ x → y ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q} → ¬ N.IsRecomb y) :
    {e | e ∈ p ∨ e ∈ q} = {e | e ∈ p' ∨ e ∈ q'} := by
  -- arcs on two paths with the same target are the same arc, on arranged paths
  have huniq : ∀ {l l' : List E} {u u' : V}, N.IsPath u x l → N.IsPath u' x l' → (∀ e ∈ l, e ∈ {e | e ∈ p ∨ e ∈ q}) → (∀ e ∈ l', e ∈ {e | e ∈ p' ∨ e ∈ q'}) →
      (∀ a ∈ l, ∀ a' ∈ l', N.tgt a = x → N.tgt a' = x → a = a') → ∀ e ∈ l, ∀ f ∈ l', N.tgt e = N.tgt f → e = f := by
    intro l l' u u' hl hl' hall hall' hxa e he f hf hef
    by_cases hx : N.tgt e = x
    · exact hxa e he f hf hx (hef ▸ hx)
    · have hnr : ¬ N.IsRecomb (N.tgt e) := hrec _ hx (Or.inr ⟨e, hall e he, rfl⟩)
      exact (eq_of_not_isRecomb hnr hef.symm).symm
  obtain ⟨a, b, ha, hb, hab, hax, hbx⟩ := cycle_last_arcs hc
  obtain ⟨a', b', ha', hb', hab', hax', hbx'⟩ := cycle_last_arcs hc'
  -- `a` is the only arc of `p` into `x`
  have honly : ∀ {u : V} {l : List E} {c : E}, N.IsPath u x l → c ∈ l → N.tgt c = x → ∀ d ∈ l, N.tgt d = x → d = c := by
    intro u l c hl hc₁ hc₂ d hd hd₂
    exact path_eq_of_tgt_eq hl hd hc₁ (hd₂.trans hc₂.symm)
  -- the case with the last arcs matched
  have hmain : ∀ {p'' q'' : List E} {w'' : V}, N.IsCycleOn w'' x p'' q'' → {e | e ∈ p'' ∨ e ∈ q''} = {e | e ∈ p' ∨ e ∈ q'} → (∀ d ∈ p'', N.tgt d = x → d = a) → (∀ d ∈ q'', N.tgt d = x → d = b) →
      {e | e ∈ p ∨ e ∈ q} = {e | e ∈ p' ∨ e ∈ q'} := by
    intro p'' q'' w'' hc'' hset hpa hqb
    have h₁ : p <:+ p'' ∨ p'' <:+ p := path_suffix_of_unique hc.2.1 hc''.2.1 (huniq hc.2.1 hc''.2.1 (fun e he => Or.inl he) (fun e he => hset ▸ Or.inl he)
      (fun c hc₁ d hd hc₂ hd₂ => (honly hc.2.1 ha hax c hc₁ hc₂).trans (hpa d hd hd₂).symm))
    have h₂ : q <:+ q'' ∨ q'' <:+ q := path_suffix_of_unique hc.2.2.1 hc''.2.2.1 (huniq hc.2.2.1 hc''.2.2.1 (fun e he => Or.inr he) (fun e he => hset ▸ Or.inr he)
      (fun c hc₁ d hd hc₂ hd₂ => (honly hc.2.2.1 hb hbx c hc₁ hc₂).trans (hqb d hd hd₂).symm))
    rw [← hset]
    have hfin : p = p'' ∧ q = q'' := by
      rcases h₁ with ⟨t, ht⟩ | ⟨t, ht⟩ <;> rcases h₂ with ⟨t', ht'⟩ | ⟨t', ht'⟩
      · obtain ⟨h₃, h₄⟩ := cycle_unique_aux hc hc'' ht.symm ht'.symm
        rw [h₃] at ht
        rw [h₄] at ht'
        exact ⟨by simpa using ht, by simpa using ht'⟩
      · -- each coalescent node is above the other
        have h₃ := hc''.2.1
        rw [← ht, isPath_append] at h₃
        obtain ⟨y, h₄, h₅⟩ := h₃
        rw [IsPath.start_eq h₅ hc.2.1 hc.ne_nil] at h₄
        have h₆ := hc.2.2.1
        rw [← ht', isPath_append] at h₆
        obtain ⟨y', h₇, h₈⟩ := h₆
        rw [IsPath.start_eq h₈ hc''.2.2.1 hc''.symm.ne_nil] at h₇
        obtain ⟨h₉, h₁₀⟩ := paths_nil_of_both h₄ h₇
        rw [h₉] at ht
        rw [h₁₀] at ht'
        exact ⟨by simpa using ht, by simpa using ht'.symm⟩
      · have h₃ := hc.2.1
        rw [← ht, isPath_append] at h₃
        obtain ⟨y, h₄, h₅⟩ := h₃
        rw [IsPath.start_eq h₅ hc''.2.1 hc''.ne_nil] at h₄
        have h₆ := hc''.2.2.1
        rw [← ht', isPath_append] at h₆
        obtain ⟨y', h₇, h₈⟩ := h₆
        rw [IsPath.start_eq h₈ hc.2.2.1 hc.symm.ne_nil] at h₇
        obtain ⟨h₉, h₁₀⟩ := paths_nil_of_both h₄ h₇
        rw [h₉] at ht
        rw [h₁₀] at ht'
        exact ⟨by simpa using ht.symm, by simpa using ht'⟩
      · obtain ⟨h₃, h₄⟩ := cycle_unique_aux hc'' hc ht.symm ht'.symm
        rw [h₃] at ht
        rw [h₄] at ht'
        exact ⟨by simpa using ht.symm, by simpa using ht'.symm⟩
    rw [hfin.1, hfin.2]
  rcases eq_or_eq_of_tgt hab (hax.trans hbx.symm) (hax'.trans hax.symm) with rfl | rfl
  · -- the last arc of `p'` is `a`
    have hb'' : b' = b := by
      rcases eq_or_eq_of_tgt hab (hax'.trans hbx.symm) (hbx'.trans hax'.symm) with h' | h'
      · exact absurd h'.symm hab'
      · exact h'
    subst hb''
    exact hmain hc' rfl (honly hc'.2.1 ha' hax') (honly hc'.2.2.1 hb' hbx')
  · have hb'' : b' = a := by
      rcases eq_or_eq_of_tgt (Ne.symm hab) (hax'.trans hax.symm) (hbx'.trans hax'.symm) with h' | h'
      · exact absurd h'.symm hab'
      · exact h'
    subst hb''
    exact hmain hc'.symm (by ext e; exact or_comm) (honly hc'.2.2.1 hb' hbx') (honly hc'.2.1 ha' hax')

/-- A fully decomposed network with as few recombination nodes as non-trivial components is a galled tree: each blob has a recombination node, and the blobs are node-disjoint, so each has just one, and is one cycle. -/
theorem isGalledTree_of_isFullyDecomposedFor [Finite V] [Finite ι] {G : SimpleGraph ι} (h : N.IsFullyDecomposedFor G)
    (hG : ∀ c : G.ConnectedComponent, c.supp.Nontrivial → ∃ B, N.IsBlob B ∧ ∀ i ∈ c.supp, N.site i ∈ B) (hcount : N.recombCount ≤ Nat.card (Cent G)) : IsGalledTree N := by
  obtain ⟨⟨f, -⟩, hd⟩ := (isFullyDecomposedFor_iff_correspondence N G hG).1 h
  -- the recombination node of a cycle of the blob
  have hrecOf : ∀ B : {B : Set E // N.IsBlob B}, ∃ x, N.IsRecomb x ∧ x ∈ N.blobVerts B.1 := by
    rintro ⟨B, hB⟩
    obtain ⟨Q, hQ, hBQ⟩ := id hB
    obtain ⟨w, x, p, q, hc, rfl⟩ := id hQ
    obtain ⟨a, -, ha, -, -, hax, -⟩ := cycle_last_arcs hc
    have haB : a ∈ B := by
      rw [hBQ]
      exact ⟨_, Relation.ReflTransGen.refl, Or.inl ha⟩
    exact ⟨x, hc.1, Or.inr ⟨a, haB, hax⟩⟩
  choose g hgr hgv using hrecOf
  have hdisj : ∀ {B B' : Set E}, N.IsBlob B → N.IsBlob B' → ∀ v, v ∈ N.blobVerts B → v ∈ N.blobVerts B' → B = B' := by
    intro B B' hB hB' v hv hv'
    by_contra hne
    exact Set.disjoint_left.1 (hd B B' hB hB' hne) hv hv'
  have hinj : Function.Injective fun B : {B : Set E // N.IsBlob B} => (⟨g B, hgr B⟩ : {x // N.IsRecomb x}) := by
    intro B B' hBB
    have hx : g B = g B' := congrArg Subtype.val hBB
    exact Subtype.ext (hdisj B.2 B'.2 _ (hgv B) (hx ▸ hgv B'))
  have hcard : Nat.card {x // N.IsRecomb x} ≤ Nat.card {B : Set E // N.IsBlob B} := by
    rw [← Nat.card_congr f]
    exact hcount
  have hsurj := (hinj.bijective_of_nat_card_le hcard).2
  -- a recombination node of a blob is its node
  have honly : ∀ {B : Set E} (hB : N.IsBlob B) (y : V), N.IsRecomb y → y ∈ N.blobVerts B → y = g ⟨B, hB⟩ := by
    intro B hB y hy hyv
    obtain ⟨B', hB'⟩ := hsurj ⟨y, hy⟩
    have hyB' : g B' = y := congrArg Subtype.val hB'
    have heq : B'.1 = B := hdisj B'.2 hB _ (hgv B') (hyB'.symm ▸ hyv)
    have : B' = ⟨B, hB⟩ := Subtype.ext heq
    rw [← hyB', this]
  -- each cycle is in a blob, and two cycles with a node in common are in one blob
  have hblobOf : ∀ {Q : Set E}, N.IsCycle Q → ∃ B, N.IsBlob B ∧ Q ⊆ B := by
    intro Q hQ
    refine ⟨_, ⟨Q, hQ, rfl⟩, fun e he => ⟨Q, Relation.ReflTransGen.refl, he⟩⟩
  have hvertsMono : ∀ {Q B : Set E}, Q ⊆ B → N.blobVerts Q ⊆ N.blobVerts B := by
    rintro Q B hQB v (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact Or.inl ⟨e, hQB he, rfl⟩
    · exact Or.inr ⟨e, hQB he, rfl⟩
  intro Q hQ
  refine ⟨hQ, fun Q' hQ' hne => ?_⟩
  rw [Set.disjoint_left]
  intro v hv hv'
  apply hne
  obtain ⟨B, hB, hQB⟩ := hblobOf hQ
  obtain ⟨B', hB', hQB'⟩ := hblobOf hQ'
  obtain rfl := hdisj hB hB' v (hvertsMono hQB hv) (hvertsMono hQB' hv')
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  obtain ⟨w', x', p', q', hc', rfl⟩ := hQ'
  have hmem : ∀ {w₀ x₀ : V} {p₀ q₀ : List E}, N.IsCycleOn w₀ x₀ p₀ q₀ → x₀ ∈ N.blobVerts {e | e ∈ p₀ ∨ e ∈ q₀} := by
    intro w₀ x₀ p₀ q₀ hc₀
    obtain ⟨a, -, ha, -, -, hax, -⟩ := cycle_last_arcs hc₀
    exact Or.inr ⟨a, Or.inl ha, hax⟩
  have hx : x = g ⟨B, hB⟩ := honly hB x hc.1 (hvertsMono hQB (hmem hc))
  have hx' : x' = g ⟨B, hB⟩ := honly hB x' hc'.1 (hvertsMono hQB' (hmem hc'))
  obtain rfl : x' = x := hx'.trans hx.symm
  refine (cycle_unique hc hc' fun y hy hyv hr => hy ?_).symm
  rw [hx]
  exact honly hB y hr (hvertsMono hQB hyv)

end OneRecomb

/-! ### The network of a gall -/

section Piece

variable {N : Network ι V E} [Finite V] {w x : V} {p q : List E}

/-- The gall alone, with the sites `κ`, which are on it. -/
def gallNet (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) (κ : Set ι) (hκ : ∀ i ∈ κ, N.site i ∈ {e | e ∈ p ∨ e ∈ q}) :
    Network κ {v // v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}} {e // e ∈ {e | e ∈ p ∨ e ∈ q}} where
  src e := ⟨N.src e.1, Or.inl ⟨e.1, e.2, rfl⟩⟩
  tgt e := ⟨N.tgt e.1, Or.inr ⟨e.1, e.2, rfl⟩⟩
  root := ⟨w, coalescent_mem hc⟩
  site i := ⟨N.site i.1, hκ i.1 i.2⟩
  label v i := N.label v.1 i.1
  simple e f h₁ h₂ := Subtype.ext (N.simple _ _ (congrArg Subtype.val h₁) (congrArg Subtype.val h₂))
  acyclic := by
    obtain ⟨ρ, hρ⟩ := N.exists_rank
    exact acyclic_of_rank (fun v => ρ v.1) fun e => hρ e.1
  root_iff := by
    rintro ⟨v, hv⟩
    constructor
    · intro h
      refine Subtype.ext ?_
      by_contra hne
      obtain ⟨g, hg, hgt⟩ := exists_arc_of_mem hc hv hne
      exact h ⟨g, hg⟩ (Subtype.ext hgt)
    · intro h e he
      have hvw : v = w := congrArg Subtype.val h
      have hte : N.tgt e.1 = w := (congrArg Subtype.val he).trans hvw
      exact not_reach_tgt_src e.1 (hte ▸ cycle_reach_src hc e.2)
  inDegree_le_two e f g h₁ h₂ := by
    rcases N.inDegree_le_two e.1 f.1 g.1 (congrArg Subtype.val h₁) (congrArg Subtype.val h₂) with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  site_not_recomb i f h := Subtype.ext (N.site_not_recomb i.1 f.1 (congrArg Subtype.val h))
  label_tree e he i := by
    have huniq : ∀ g, N.tgt g = N.tgt e.1 → g = e.1 := by
      intro g hg
      by_contra hne
      obtain ⟨Q, hQ, hgQ, heQ⟩ := exists_isCycle_of_tgt_eq hne hg
      have heq := hG.eq_of_inter ⟨w, x, p, q, hc, rfl⟩ hQ ⟨e.1, e.2, heQ⟩
      rw [heq] at hgQ
      exact hne (congrArg Subtype.val (he ⟨g, hgQ⟩ (Subtype.ext hg)))
    have := N.label_tree e.1 huniq i.1
    simp only [Subtype.ext_iff]
    exact this
  label_recomb e f hef h i := N.label_recomb e.1 f.1 (fun h' => hef (Subtype.ext h')) (congrArg Subtype.val h) i.1

/-- The gall alone has one recombination node. -/
theorem gallNet_isRecomb {hG : IsGalledTree N} {hc : N.IsCycleOn w x p q} {κ : Set ι} {hκ : ∀ i ∈ κ, N.site i ∈ {e | e ∈ p ∨ e ∈ q}} {v : {v // v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}}}
    (h : (gallNet hG hc κ hκ).IsRecomb v) : v.1 = x := by
  obtain ⟨e, f, hef, he, hf⟩ := h
  have hne : e.1 ≠ f.1 := fun h' => hef (Subtype.ext h')
  have hte : N.tgt e.1 = v.1 := congrArg Subtype.val he
  have htf : N.tgt f.1 = v.1 := congrArg Subtype.val hf
  rcases e.2 with he' | he' <;> rcases f.2 with hf' | hf'
  · exact absurd (path_eq_of_tgt_eq hc.2.1 he' hf' (hte.trans htf.symm)) hne
  · rw [← hte]
    exact hc.2.2.2.2 _ he' _ hf' (hte.trans htf.symm)
  · rw [← htf]
    exact hc.2.2.2.2 _ hf' _ he' (htf.trans hte.symm)
  · exact absurd (path_eq_of_tgt_eq hc.2.2.1 he' hf' (hte.trans htf.symm)) hne

variable {L : Finset (ι → Bool)}

/-- "The `i, j` state-pair at `x` differs from the `i, j` state-pair at every other node on `Q`" (after the proof of Theorem 2.2 of the source), for a parent of the recombination node. -/
theorem parent_pair_ne (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) (hL : ∀ r ∈ L, ∃ v, N.label v = r) {i j : ι} (hi : N.site i ∈ {e | e ∈ p ∨ e ∈ q}) (hj : N.site j ∈ {e | e ∈ p ∨ e ∈ q})
    (hij : Incompatible L i j) {e : E} (he : e ∈ {e | e ∈ p ∨ e ∈ q}) (hx : N.tgt e = x) : N.label (N.src e) i ≠ N.label x i ∨ N.label (N.src e) j ≠ N.label x j := by
  obtain ⟨kind, τ, hτ⟩ := exists_threshold_mem hG hc
  have hrow : ∀ r ∈ L, (∀ s ∈ {s | N.site s ∈ {e | e ∈ p ∨ e ∈ q}}, r s = N.label x s) ∨ ∃ z, ∀ s ∈ {s | N.site s ∈ {e | e ∈ p ∨ e ∈ q}}, (r s ≠ N.label x s ↔ OnSide kind τ z s) := by
    intro r hr
    obtain ⟨y, rfl⟩ := hL r hr
    obtain ⟨v, hv, hyv⟩ := exists_mem_label_eq hG hc y
    rcases hτ v hv with rfl | ⟨z, hz⟩
    · exact Or.inl hyv
    · exact Or.inr ⟨z, fun s hs => by rw [hyv s hs]; exact hz s hs⟩
  rcases hτ (N.src e) (Or.inl ⟨e, he, rfl⟩) with h | ⟨z, hz⟩
  · exact absurd (hx ▸ h) (fun h' => N.src_ne_tgt e h')
  · rcases onSide_or_of_incompatible hrow hi hj hij z with h | h
    · exact Or.inl ((hz i hi).2 h)
    · exact Or.inr ((hz j hj).2 h)

/-- The gall alone, on the sites `κ`, obeys the crossover model of the network, if two of its sites are incompatible. -/
theorem gallNet_obeys [LinearOrder ι] (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) {κ : Set ι} (hκ : ∀ i ∈ κ, N.site i ∈ {e | e ∈ p ∨ e ∈ q}) (hL : ∀ r ∈ L, ∃ v, N.label v = r) {i j : ι} (hi : i ∈ κ) (hj : j ∈ κ)
    (hij : Incompatible L i j) {c : Crossover} (h : N.Obeys c) : (gallNet hG hc κ hκ).Obeys c := by
  rw [obeys_iff] at h ⊢
  intro v hv
  have hvx : v.1 = x := gallNet_isRecomb hv
  obtain ⟨e, f, hef, he, hf, hrec⟩ := h x (hvx ▸ hc.1)
  obtain ⟨a, b, ha, hb, hab, hax, hbx⟩ := cycle_last_arcs hc
  have hmem : ∀ g, N.tgt g = x → g ∈ {e | e ∈ p ∨ e ∈ q} := by
    intro g hg
    rcases eq_or_eq_of_tgt hab (hax.trans hbx.symm) (hg.trans hax.symm) with rfl | rfl
    · exact Or.inl ha
    · exact Or.inr hb
  refine ⟨⟨e, hmem e he⟩, ⟨f, hmem f hf⟩, fun h' => hef (congrArg Subtype.val h'), Subtype.ext (he.trans hvx.symm), Subtype.ext (hf.trans hvx.symm), ?_⟩
  have hv' : ∀ s : κ, (gallNet hG hc κ hκ).label v s = N.label x s.1 := fun s => by
    change N.label v.1 s.1 = _
    rw [hvx]
  cases c with
  | single =>
    obtain ⟨L₀, hL₀⟩ := hrec
    refine ⟨⟨{s | s.1 ∈ L₀}, fun s t hst hs => L₀.lower hst hs⟩, fun s => ?_⟩
    rw [hv' s, hL₀ s.1]
    rfl
  | multiple =>
    intro s
    rw [hv' s]
    exact hrec s.1
  | pointwise =>
    obtain ⟨j₀, hj₀⟩ := hrec
    -- the one site that comes from the second parent is in `κ`, for the first parent isn't a copy on `i, j`
    have hj₀κ : j₀ ∈ κ := by
      by_contra hno
      have hcopy : ∀ s ∈ κ, N.label x s = N.label (N.src e) s := fun s hs => by
        have hne : s ≠ j₀ := fun hsj => hno (hsj ▸ hs)
        rw [hj₀ s, ite_eq_right hne]
      rcases parent_pair_ne hG hc hL (hκ i hi) (hκ j hj) hij (hmem e he) he with h' | h'
      · exact h' (hcopy i hi).symm
      · exact h' (hcopy j hj).symm
    refine ⟨⟨j₀, hj₀κ⟩, fun s => ?_⟩
    rw [hv' s, hj₀ s.1]
    simp only [Subtype.ext_iff]
    rfl

/-- **The network of a non-trivial component**, from its gall (Theorem 2.4 of the source): it has the sites of the component, the ancestral sequence on them, and one leaf for each other row of `M(C)`, and at most one recombination node. The rows of `M(C)` are the labels of nodes of the gall by Lemma 2.1 of the source (`exists_mem_label_eq`). -/
theorem exists_gall_piece [LinearOrder ι] (hG : IsGalledTree N) (hL : ∀ r ∈ L, ∃ v, N.label v = r) (C : Cent (incompatGraph L)) :
    ∃ (a b : ℕ) (P : Network C.1.supp (Fin a) (Fin b)), (∀ c, N.Obeys c → P.Obeys c) ∧ P.ancestral = C.1.supp.domRestrict N.ancestral ∧
      P.Derives ((restrictRows C.1.supp L).erase (C.1.supp.domRestrict N.ancestral)) ∧ P.recombCount ≤ 1 := by
  obtain ⟨i₀, j₀, hi₀, hadj⟩ := Cent.exists_adj C
  obtain ⟨Q, hQ, hsi, hsj⟩ := exists_isCycle_of_incompatible N hL hadj
  have hj₀ : j₀ ∈ C.1.supp := (SimpleGraph.ConnectedComponent.eq.2 hadj.reachable).symm.trans hi₀
  have hκ : ∀ s ∈ C.1.supp, N.site s ∈ Q := fun s hs => theorem2_4 hG hQ hL hsi (SimpleGraph.ConnectedComponent.exact (hi₀.trans hs.symm))
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  have : Finite {e // e ∈ {e | e ∈ p ∨ e ∈ q}} := Set.Finite.to_subtype (Set.Finite.subset ((List.finite_toSet p).union (List.finite_toSet q)) fun e he => he)
  set P₀ := gallNet hG hc C.1.supp hκ with hP₀
  set T := (restrictRows C.1.supp L).erase (C.1.supp.domRestrict N.ancestral) with hT
  -- each row is the label of a node of the gall
  have hanc : ∀ r : T, ∃ v, P₀.label v = r.1 := by
    rintro ⟨r, hr⟩
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase hr)
    obtain ⟨y, rfl⟩ := hL ρ hρ
    obtain ⟨v, hv, hyv⟩ := exists_mem_label_eq hG hc y
    refine ⟨⟨v, hv⟩, ?_⟩
    funext s
    exact (hyv s.1 (hκ s.1 s.2)).symm
  choose anchor hanchor using hanc
  have hroot : P₀.label P₀.root = C.1.supp.domRestrict N.ancestral := by
    funext s
    exact label_coalescent hc (hκ s.1 s.2)
  -- each site has a row off the ancestral state
  have hs : ∀ s : C.1.supp, ∃ r ∈ T, r s ≠ P₀.label P₀.root s := by
    intro s
    obtain ⟨k, hk⟩ := exists_incompatible_of_nontrivial C.2 s.2
    obtain ⟨r, hr, h₁, -⟩ := hk (!N.ancestral s.1) true
    have hne : (!N.ancestral s.1) ≠ N.ancestral s.1 := by cases N.ancestral s.1 <;> simp
    have hrs : C.1.supp.domRestrict r s = !N.ancestral s.1 := h₁
    refine ⟨C.1.supp.domRestrict r, Finset.mem_erase.2 ⟨fun h' => ?_, Finset.mem_image_of_mem _ hr⟩, ?_⟩
    · have := congrFun h' s
      rw [hrs] at this
      exact hne this
    · rw [hroot, hrs]
      exact hne
  have hTne : T.Nonempty := by
    obtain ⟨r, hr, -⟩ := hs ⟨i₀, hi₀⟩
    exact ⟨r, hr⟩
  obtain ⟨a, b, P, h₁, h₂, h₃, h₄⟩ := P₀.exists_trim hTne hanchor hs
  refine ⟨a, b, P, fun c hc' => h₁ c (gallNet_obeys hG hc hκ hL hi₀ hj₀ hadj hc'), h₃.trans hroot, h₂, h₄.trans ?_⟩
  refine Finite.card_le_one_iff_subsingleton.2 ⟨fun y y' => ?_⟩
  refine Subtype.ext (Subtype.ext ?_)
  exact (gallNet_isRecomb y.2.1).trans (gallNet_isRecomb y'.2.1).symm

end Piece

/-! ### Gluing -/

section Glue

variable [LinearOrder ι] [Finite ι] {N : Network ι V E} [Finite V] {M : Finset (ι → Bool)}

omit [LinearOrder ι] [Finite ι] in
/-- The networks of the components have the sites of the components on their one blob. -/
theorem piece_blob {L : Finset (ι → Bool)} (C : Cent (incompatGraph L)) {S : ι → Bool} {a b : ℕ} {P : Network C.1.supp (Fin a) (Fin b)} (hanc : P.ancestral = C.1.supp.domRestrict S)
    (hder : P.Derives ((restrictRows C.1.supp L).erase (C.1.supp.domRestrict S))) (hrec : P.recombCount ≤ 1) :
    (∃! B, P.IsBlob B) ∧ ∀ i, ∃ B, P.IsBlob B ∧ P.site i ∈ B := by
  have hall : ∀ i : C.1.supp, ∃ B, P.IsBlob B ∧ P.site i ∈ B := by
    intro i
    obtain ⟨k, hk⟩ := exists_incompatible_of_nontrivial C.2 i.2
    have hkC : k ∈ C.1.supp := (SimpleGraph.ConnectedComponent.eq.2 (SimpleGraph.Adj.reachable (G := incompatGraph L) hk)).symm.trans i.2
    have hlab : ∀ r ∈ restrictRows C.1.supp L, ∃ v, P.label v = r := by
      intro r hr
      by_cases hrS : r = C.1.supp.domRestrict S
      · exact ⟨P.root, hanc.trans hrS.symm⟩
      · exact hder.displays r (Finset.mem_erase.2 ⟨hrS, hr⟩)
    have hinc : Incompatible (restrictRows C.1.supp L) i ⟨k, hkC⟩ := fun a' b' => by
      obtain ⟨r, hr, h₁, h₂⟩ := hk a' b'
      exact ⟨C.1.supp.domRestrict r, Finset.mem_image_of_mem _ hr, h₁, h₂⟩
    obtain ⟨B, hB, hi, -⟩ := exists_isBlob_of_incompatible P hlab hinc
    exact ⟨B, hB, hi⟩
  have hsub : Subsingleton {x // P.IsRecomb x} := Finite.card_le_one_iff_subsingleton.1 hrec
  refine ⟨?_, hall⟩
  obtain ⟨i, hi⟩ := C.1.exists_rep
  obtain ⟨B₀, hB₀, -⟩ := hall ⟨i, hi⟩
  refine ⟨B₀, hB₀, fun B hB => ?_⟩
  obtain ⟨Q, ⟨w, x, p, q, hc, rfl⟩, hBQ⟩ := id hB
  obtain ⟨Q₀, ⟨w₀, x₀, p₀, q₀, hc₀, rfl⟩, hBQ₀⟩ := id hB₀
  have hxx : x₀ = x := congrArg Subtype.val (Subsingleton.elim (⟨x₀, hc₀.1⟩ : {x // P.IsRecomb x}) ⟨x, hc.1⟩)
  subst hxx
  obtain ⟨e, he, he₀⟩ := cycle_share_arc hc hc₀
  refine IsBlob.eq_of_inter_nonempty hB hB₀ ⟨e, ?_, ?_⟩
  · rw [hBQ]
    exact ⟨_, Relation.ReflTransGen.refl, he⟩
  · rw [hBQ₀]
    exact ⟨_, Relation.ReflTransGen.refl, he₀⟩

omit [LinearOrder ι] [Finite ι] [Finite V] in
/-- A cycle of a galled tree is a blob. -/
theorem IsGalledTree.isBlob_of_isCycle (hG : IsGalledTree N) {Q : Set E} (hQ : N.IsCycle Q) : N.IsBlob Q := by
  have hall : ∀ Q', Relation.ReflTransGen N.ShareArc Q Q' → Q' = Q := by
    intro Q' hr
    induction hr with
    | refl => rfl
    | tail _ hs ih =>
      obtain ⟨h₁, h₂, h₃⟩ := hs
      subst ih
      exact hG.eq_of_inter h₁ h₂ h₃
  refine ⟨Q, hQ, ?_⟩
  ext e
  constructor
  · exact fun he => ⟨Q, .refl, he⟩
  · rintro ⟨Q', hr, he⟩
    rwa [hall Q' hr] at he

omit [LinearOrder ι] [Finite ι] [Finite V] in
/-- A galled tree that is fully decomposed is reduced: all the sites of a gall are those of one non-trivial component. -/
theorem isReducedGalledTree_of_isFullyDecomposedFor {G : SimpleGraph ι} (hG : IsGalledTree N) (hfd : N.IsFullyDecomposedFor G) : IsReducedGalledTree N G where
  galled := hG
  exists_conflict Q hQ := by
    obtain ⟨c, hnt, hc⟩ := hfd.blob_component Q (hG.isBlob_of_isCycle hQ)
    obtain ⟨i, j, hi, hij⟩ := Cent.exists_adj (⟨c, hnt⟩ : Cent G)
    exact ⟨i, j, (hc i).2 hi, (hc j).2 ((SimpleGraph.ConnectedComponent.eq.2 hij.reachable).symm.trans hi), hij⟩
  no_unconflicted Q hQ i hi := by
    obtain ⟨c, hnt, hc⟩ := hfd.blob_component Q (hG.isBlob_of_isCycle hQ)
    obtain ⟨j, hj, hij⟩ := hnt.exists_ne i
    exact exists_adj_of_reachable (SimpleGraph.ConnectedComponent.exact (((hc i).1 hi).trans hj.symm)) hij.symm

omit [LinearOrder ι] [Finite V] in
/-- The two facts on a network deriving `M`, fully decomposed, with as few recombination nodes as non-trivial components: it is a reduced galled tree. -/
theorem isReducedGalledTree_of_count [Finite V] {L : Finset (ι → Bool)} (hL : ∀ r ∈ L, ∃ v, N.label v = r) (hfd : N.IsFullyDecomposedFor (incompatGraph L)) (hcount : N.recombCount ≤ Nat.card (Cent (incompatGraph L))) :
    IsReducedGalledTree N (incompatGraph L) := by
  refine isReducedGalledTree_of_isFullyDecomposedFor (isGalledTree_of_isFullyDecomposedFor hfd (fun c' hc' => ?_) hcount) hfd
  obtain ⟨i, j, hi, hij⟩ := Cent.exists_adj (⟨c', hc'⟩ : Cent (incompatGraph L))
  obtain ⟨B, hB, hB', -⟩ := exists_isBlob_of_incompatible N hL hij
  refine ⟨B, hB, fun k hk => ?_⟩
  obtain ⟨c'', -, hc''⟩ := hfd.blob_component B hB
  have hic : i ∈ c''.supp := (hc'' i).1 hB'
  have hi' : i ∈ c'.supp := hi
  have hcc : c' = c'' := hi'.symm.trans hic
  exact (hc'' k).2 (hcc ▸ hk)

/-- **The gluing.** Networks with at most one recombination node for the non-trivial components of `G(M + S)`, on the rows of `M + S` other than `S`, glue to a reduced galled tree for `M` with ancestral sequence `S`: the construction of Theorem 1 of Gusfield et al. 2007, whose proof is `IsTBar.exists_glued`. -/
theorem exists_reduced_of_pieces (c : Crossover) {S : ι → Bool} (hC' : NoConstantColumn (addRow M S)) (hne : ∃ r ∈ addRow M S, r ≠ S) {a b : Cent (incompatGraph (addRow M S)) → ℕ}
    (P : ∀ C : Cent (incompatGraph (addRow M S)), Network C.1.supp (Fin (a C)) (Fin (b C))) (hob : ∀ C, (P C).Obeys c) (hanc : ∀ C, (P C).ancestral = C.1.supp.domRestrict S)
    (hder : ∀ C, (P C).Derives ((restrictRows C.1.supp (addRow M S)).erase (C.1.supp.domRestrict S))) (hrec : ∀ C, (P C).recombCount ≤ 1) :
    ∃ (a' b' : ℕ) (N' : Network ι (Fin a') (Fin b')), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧ IsReducedGalledTree N' (incompatGraph (addRow M S)) := by
  have hS : S ∈ addRow M S := mem_addRow.2 (Or.inl rfl)
  have hM' : (addRow M S).Nonempty := ⟨S, hS⟩
  have : Finite (incompatGraph (addRow M S)).ConnectedComponent := Finite.of_surjective (incompatGraph (addRow M S)).connectedComponentMk fun c => c.exists_rep
  have hP := fun C => piece_blob C (hanc C) (hder C) (hrec C)
  have hsum : ∑ᶠ C, (P C).recombCount ≤ Nat.card (Cent (incompatGraph (addRow M S))) := by
    have : Fintype (Cent (incompatGraph (addRow M S))) := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]
    exact Finset.sum_le_sum fun C _ => hrec C
  obtain ⟨n, T, φ, edge, h⟩ := exists_isTBar (addRow M S) hM' hC'
  obtain ⟨V', E', hV, hE, N₁, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h.exists_glued P hS hC' hanc hder hne
  have hob' : N₁.Obeys c := h₁ c hob
  have hfd := h₅ hP
  -- the row `S` gets a new leaf, if it is one of `M`
  obtain ⟨V₂, E₂, hV₂, hE₂, N₂, h₂₁, h₂₂, h₂₃, h₂₄, h₂₅⟩ : ∃ (V₂ E₂ : Type _) (_ : Finite V₂) (_ : Finite E₂) (N₂ : Network ι V₂ E₂), N₂.Obeys c ∧ N₂.Derives M ∧ N₂.ancestral = S ∧
      N₂.IsFullyDecomposedFor (incompatGraph (addRow M S)) ∧ N₂.recombCount ≤ Nat.card (Cent (incompatGraph (addRow M S))) := by
    by_cases hSM : S ∈ M
    · have hl : N₁.label N₁.root = S := h₂
      refine ⟨Option V', Option E', inferInstance, inferInstance, Decomp.addLeaf N₁ N₁.root, Decomp.addLeaf_obeys hob', ?_, h₂, Decomp.addLeaf_fullyDecomposed hfd, Decomp.addLeaf_recombCount.trans_le (h₆ ▸ hsum)⟩
      have hd := Decomp.addLeaf_derives h₃ h₄ (by rw [hl]; simp)
      rwa [hl, addRow_eq_of_mem hSM, Finset.insert_erase hSM] at hd
    · have heq : (addRow M S).erase S = M := Finset.erase_insert hSM
      exact ⟨V', E', hV, hE, N₁, hob', heq ▸ h₃, h₂, hfd, h₆ ▸ hsum⟩
  obtain ⟨a', b', N', eV, eE, hiso⟩ := N₂.exists_fin_iso
  obtain ⟨i₁, i₂, i₃, i₄, i₅⟩ := hiso.invariants
  have hD' : N'.Derives M := (i₃ M).2 h₂₂
  have hanc' : N'.ancestral = S := i₄.trans h₂₃
  have hlab' : ∀ r ∈ addRow M S, ∃ v, N'.label v = r := hanc' ▸ labels_addRow hD'
  exact ⟨a', b', N', (i₂ c).2 h₂₁, hD', hanc', isReducedGalledTree_of_count hlab' ((i₅ _).2 h₂₄) (i₁.trans_le h₂₅)⟩

/-- **Corollary 5.1** (`ext:cor5_1`) of the source. "If there is a galled-tree for `M`, then there is a reduced galled-tree for `M`": with the same ancestral sequence and in the same crossover model. The hypothesis is the source's standing assumption that each column has a `1`.
See the head of this file for the difference from the source. The number of recombination nodes is `IsReducedGalledTree.recombCount_eq`, and that it is the minimum over galled trees is `corollary5_1_min`. Line 180 of Gusfield et al. 2007, unrooted, is `exists_isReducedGalledTree_incompatGraph`. -/
theorem exists_isReducedGalledTree (hG : IsGalledTree N) (hD : N.Derives M) (h1 : ∀ i, ∃ r ∈ M, r i ≠ N.ancestral i) {c : Crossover} (hc : N.Obeys c) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = N.ancestral ∧ IsReducedGalledTree N' (conflictGraph N.ancestral M) := by
  have hL : ∀ r ∈ addRow M N.ancestral, ∃ v, N.label v = r := labels_addRow hD
  have hS : N.ancestral ∈ addRow M N.ancestral := mem_addRow.2 (Or.inl rfl)
  have hC' : NoConstantColumn (addRow M N.ancestral) := fun i => by
    obtain ⟨r, hr, hri⟩ := h1 i
    exact ⟨r, mem_addRow.2 (Or.inr hr), _, hS, hri⟩
  have hM : M.Nonempty := hD.nonempty
  rw [conflictGraph_eq_incompatGraph_addRow]
  by_cases hne : ∃ r ∈ addRow M N.ancestral, r ≠ N.ancestral
  · choose a b P hob hanc hder hrec using fun C : Cent (incompatGraph (addRow M N.ancestral)) => exists_gall_piece hG hL C
    exact exists_reduced_of_pieces c hC' hne P (fun C => hob C c hc) hanc hder hrec
  · -- all the rows are `S`, and so there are no sites
    push Not at hne
    have hι : IsEmpty ι := ⟨fun i => by
      obtain ⟨r, hr, hri⟩ := h1 i
      exact hri (by rw [hne r (mem_addRow.2 (Or.inr hr))])⟩
    obtain ⟨a', b', N', hr, hd, hs, -⟩ := Gusfield1991.exists_network_of_no_conflict M N.ancestral hM hC' (fun i => hι.elim i)
    have hinj := Network.tgt_injective_of_no_recomb hr
    have hcyc : ∀ Q, ¬ N'.IsCycle Q := Network.not_isCycle_of_tgt_injective hinj
    exact ⟨a', b', N', Network.obeys_of_tgt_injective hinj c, hd, hs, fun Q hQ => absurd hQ (hcyc Q), fun Q hQ => absurd hQ (hcyc Q), fun Q hQ => absurd hQ (hcyc Q)⟩

omit [LinearOrder ι] [Finite ι] in
/-- **Corollary 5.1** (`ext:cor5_1`) of the source, the minimum. "This is the minimum number of recombinations possible over all galled-trees for `M`": a reduced galled tree has as few recombination nodes as any galled tree for `M` with the same ancestral sequence. -/
theorem corollary5_1_min {V' E' : Type*} [Finite V'] {N' : Network ι V' E'} (h : IsReducedGalledTree N (conflictGraph N.ancestral M)) (hD : N.Derives M) (hG' : IsGalledTree N') (hD' : N'.Derives M) (hS : N'.ancestral = N.ancestral) :
    N.recombCount ≤ N'.recombCount := by
  rw [h.recombCount_eq hD, ← hS, conflictGraph_eq_incompatGraph_addRow]
  exact card_cent_le_recombCount hG' (labels_addRow hD')

/-- **Theorem 2.7** (`ext:thm2_7`) of the source, its first sentence. "If the conflict graph for `M` has `k` non-trivial connected components, and there is a galled-tree for `M`, then any galled-tree that minimizes the number of recombinations (over all galled-trees) uses exactly `k` recombinations." Here for the
galled trees with the ancestral sequence and in the crossover model of the given one. The source's hypothesis on the columns is needed: see the head of this file.

The source proves it by replacing a gall with no conflicted sites by a perfect phylogeny. Departure from the source: the minimum is compared with the reduced galled tree of `exists_isReducedGalledTree`, and the galled tree has a recombination node for each component by Theorem 2.6. The head of this file says why. -/
theorem theorem2_7 (hG : IsGalledTree N) (hD : N.Derives M) (h1 : ∀ i, ∃ r ∈ M, r i ≠ N.ancestral i) {c : Crossover} (hc : N.Obeys c)
    (hmin : ∀ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), IsGalledTree N' → N'.Obeys c → N'.Derives M → N'.ancestral = N.ancestral → N.recombCount ≤ N'.recombCount) :
    N.recombCount = Nat.card (Cent (conflictGraph N.ancestral M)) := by
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄⟩ := exists_isReducedGalledTree hG hD h1 hc
  have h₄' : IsReducedGalledTree N' (conflictGraph N'.ancestral M) := by
    rw [h₃]
    exact h₄
  have h₅ := h₄'.recombCount_eq h₂
  rw [h₃] at h₅
  refine le_antisymm ((hmin a b N' h₄.galled h₁ h₂ h₃).trans_eq h₅) ?_
  rw [conflictGraph_eq_incompatGraph_addRow]
  exact card_cent_le_recombCount hG (labels_addRow hD)

/-- **Gusfield et al. 2007, line 381**, for any galled tree (`g:line381_of_galled`): "the answer is yes when `M` can be derived on a galled-tree". If `M` can be derived on a galled tree with ancestral sequence `S`, in the model `c`, then it is S-min decomposable for `c`, and for multiple crossovers: there is a fully decomposed network with the least possible number of recombination nodes. -/
theorem sMinDecomposable_of_isGalledTree (hG : IsGalledTree N) (hD : N.Derives M) (h1 : ∀ i, ∃ r ∈ M, r i ≠ N.ancestral i) {c : Crossover} (hc : N.Obeys c) :
    SMinDecomposable c N.ancestral M ∧ SMinDecomposable .multiple N.ancestral M := by
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄⟩ := exists_isReducedGalledTree hG hD h1 hc
  rw [← h₃] at h₄ ⊢
  exact line381_rooted h₄ h₂ h₁

/-- **Corollary 5.1 and Theorem 8.3 of the source**, the value: if `M` can be derived on a galled tree with ancestral sequence `S`, in the model `c`, then `R_S(M)`, for `c` and for multiple crossovers, is the number of non-trivial components of `G_S(M)`. -/
theorem RS_eq_card_cent [Finite E] (hG : IsGalledTree N) (hD : N.Derives M) (h1 : ∀ i, ∃ r ∈ M, r i ≠ N.ancestral i) {c : Crossover} (hc : N.Obeys c) :
    RS c N.ancestral M = Nat.card (Cent (conflictGraph N.ancestral M)) ∧ RS .multiple N.ancestral M = Nat.card (Cent (conflictGraph N.ancestral M)) := by
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄⟩ := exists_isReducedGalledTree hG hD h1 hc
  rw [← h₃] at h₄ ⊢
  obtain ⟨h₅, h₆⟩ := reducedGalledTree_recombCount_eq_RS h₄ h₂ h₁
  have h₇ := h₄.recombCount_eq h₂
  exact ⟨h₅.symm.trans h₇, h₆.symm.trans h₇⟩

end Glue

end GusfieldEtAl2004
