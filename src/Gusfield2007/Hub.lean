module

public import Gusfield2007.Surgery

/-!
# Gusfield et al. 2007: the hub, the modification of line 330

"If `N` is not efficient, it can be easily modified to become efficient without increasing the number of recombinations used." The paper gives no modification. The one here is: given tree arcs `X`, whose sources have the sequence of a node `v₁`, add a
new node `h` with one new arc from `v₁`, and move the sources of the arcs of `X` to `h`. The recombination cycles of `N` don't change. This is what's needed for both clauses of "efficient": two exits at one node, or two external nodes with one label.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

namespace Network

universe u v w

variable {ι : Type u} {V : Type v} {E : Type w}

/-- If the recombination cycles of `N'` are the images of those of `N`, then so are its blobs. -/
theorem isBlob_iff_of_isCycle_iff {ι : Type u} {V : Type v} {E : Type w} {V' E' : Type*} {N : Network ι V E} {N' : Network ι V' E'} (em : E → E') (hem : Function.Injective em)
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

/-! ### Isomorphic networks -/

section Iso

variable {ι : Type u} {V : Type v} {E : Type w} {V' E' : Type*} {N : Network ι V E} {N' : Network ι V' E'} {eV : V ≃ V'} {eE : E ≃ E'}

/-- An isomorphic network of an efficient network is efficient. -/
theorem IsIso.isEfficient (h : N.IsIso N' eV eE) (he : N.IsEfficient) : N'.IsEfficient := by
  have hnot : ∀ {B : Set E} {e : E}, N'.tgt (eE e) ∉ N'.blobVerts (eE '' B) → N.tgt e ∉ N.blobVerts B := by
    intro B e hn hm
    rw [h.blobVerts_image] at hn
    exact hn ⟨_, hm, (h.tgt e).symm⟩
  have hmem : ∀ {B : Set E} {z : V}, eV z ∈ N'.blobVerts (eE '' B) → z ∈ N.blobVerts B := by
    intro B z hz
    rw [h.blobVerts_image] at hz
    obtain ⟨y, hy, hyz⟩ := hz
    rwa [← eV.injective hyz]
  refine ⟨?_, ?_⟩
  · rintro B₁ B₂ v v' hB₁ hB₂ ⟨hv, e, hes, het⟩ ⟨hv', e', hes', het'⟩ hlab
    obtain ⟨B₁, hB₁', rfl⟩ := h.exists_eq_image_of_isBlob hB₁
    obtain ⟨B₂, hB₂', rfl⟩ := h.exists_eq_image_of_isBlob hB₂
    obtain ⟨z, rfl⟩ := eV.surjective v
    obtain ⟨z', rfl⟩ := eV.surjective v'
    obtain ⟨e, rfl⟩ := eE.surjective e
    obtain ⟨e', rfl⟩ := eE.surjective e'
    rw [h.src] at hes hes'
    obtain rfl := eV.injective hes
    obtain rfl := eV.injective hes'
    rw [h.label, h.label] at hlab
    rw [he.label_inj B₁ B₂ _ _ hB₁' hB₂' ⟨hmem hv, e, rfl, hnot het⟩ ⟨hmem hv', e', rfl, hnot het'⟩ hlab]
  · rintro B₁ e f hB₁ hs ht hsf htf
    obtain ⟨B₁, hB₁', rfl⟩ := h.exists_eq_image_of_isBlob hB₁
    obtain ⟨e, rfl⟩ := eE.surjective e
    obtain ⟨f, rfl⟩ := eE.surjective f
    rw [h.src] at hs hsf
    rw [h.src] at hsf
    rw [he.exit_unique B₁ e f hB₁' (hmem hs) (hnot ht) (eV.injective hsf) (hnot htf)]

end Iso

/-- What's needed to move the arcs of `X` to a hub below `v₁`. -/
structure HubCond (N : Network ι V E) (X : Set E) (v₁ : V) : Prop where
  tree : ∀ e ∈ X, N.IsTreeArc e
  label : ∀ e ∈ X, N.label (N.src e) = N.label v₁
  acyc : ∀ e ∈ X, ¬ N.Reach (N.tgt e) v₁

variable [Finite V] [Finite E]

/-- The network with the arcs of `X` moved to a hub `none` below `v₁`. The node `some v` is `v`, and the arc `none` is the new one. -/
noncomputable def hubNet (N : Network ι V E) (X : Set E) (v₁ : V) (hX : N.HubCond X v₁) : Network ι (Option V) (Option E) where
  src
    | none => some v₁
    | some e => if e ∈ X then none else some (N.src e)
  tgt
    | none => none
    | some e => some (N.tgt e)
  root := some N.root
  site i := some (N.site i)
  label
    | none => N.label v₁
    | some v => N.label v
  simple := by
    rintro (_ | e) (_ | f) h₁ h₂
    · rfl
    · simp at h₂
    · simp at h₂
    · simp only [Option.some.injEq] at h₂
      by_cases he : e ∈ X
      · have h₃ := (hX.tree e he).eq_of_tgt_eq h₂.symm
        rw [h₃]
      · by_cases hf : f ∈ X
        · have h₃ := (hX.tree f hf).eq_of_tgt_eq h₂
          rw [h₃]
        · simp only [he, hf, ite_false, Option.some.injEq] at h₁
          rw [N.simple e f h₁ h₂]
  acyclic := by
    obtain ⟨ρ, hρ⟩ := N.exists_rank
    obtain ⟨K', hK'⟩ := (Set.finite_range ρ).bddAbove
    obtain ⟨K, hK⟩ : ∃ K, ∀ v, ρ v < K := ⟨K' + 1, fun v => Nat.lt_succ_of_le (hK' ⟨v, rfl⟩)⟩
    refine acyclic_of_rank (fun
      | none => K
      | some z => if N.Reach z v₁ then ρ z else K + 1 + ρ z) ?_
    rintro (_ | e)
    · change (if N.Reach v₁ v₁ then ρ v₁ else K + 1 + ρ v₁) < K
      simp only [show N.Reach v₁ v₁ from Relation.ReflTransGen.refl, ite_true]
      exact hK v₁
    · by_cases he : e ∈ X
      · simp only [he, ite_true, hX.acyc e he, ite_false]
        omega
      · simp only [he, ite_false]
        have h₁ := hρ e
        have h₂ := hK (N.src e)
        by_cases ht : N.Reach (N.tgt e) v₁
        · have hs : N.Reach (N.src e) v₁ := Relation.ReflTransGen.head (arc_src_tgt e) ht
          simp only [hs, ht, ite_true]
          exact h₁
        · simp only [ht, ite_false]
          split <;> omega
  root_iff := by
    rintro (_ | z)
    · constructor
      · intro h
        exact absurd rfl (h none)
      · intro h
        simp at h
    · constructor
      · intro h
        have : ∀ e, N.tgt e ≠ z := fun e he => h (some e) (by simp [he])
        rw [(N.root_iff z).1 this]
      · intro h
        simp only [Option.some.injEq] at h
        subst h
        rintro (_ | e) he
        · simp at he
        · exact (N.root_iff N.root).2 rfl e (by simpa using he)
  inDegree_le_two := by
    rintro (_ | e) (_ | f) (_ | g) h₁ h₂ <;> simp only [reduceCtorEq, Option.some.injEq] at h₁ h₂ <;> simp
    rcases N.inDegree_le_two e f g h₁ h₂ with h | h | h <;> simp [h]
  site_not_recomb := by
    rintro i (_ | f) h
    · simp at h
    · simp only [Option.some.injEq] at h ⊢
      exact N.site_not_recomb i f h
  label_tree := by
    rintro (_ | e) he i
    · simp
    · have huniq : ∀ f, N.tgt f = N.tgt e → f = e := fun f hf => by
        have := he (some f) (by simpa using hf)
        simpa using this
      have h := N.label_tree e huniq i
      by_cases hmem : e ∈ X
      · have hl := congrFun (hX.label e hmem) i
        simp only [hmem, ite_true, Option.some.injEq]
        rw [h, hl]
      · simp only [hmem, ite_false, Option.some.injEq]
        exact h
  label_recomb := by
    rintro (_ | e) (_ | f) hef h i
    · exact absurd rfl hef
    · simp at h
    · simp at h
    · simp only [Option.some.injEq] at h
      have hef' : e ≠ f := fun h' => hef (by rw [h'])
      have he : e ∉ X := fun he => hef' ((hX.tree e he).eq_of_tgt_eq h.symm).symm
      have hf : f ∉ X := fun hf => hef' ((hX.tree f hf).eq_of_tgt_eq h)
      simp only [he, hf, ite_false]
      exact N.label_recomb e f hef' h i

variable {N : Network ι V E} {X : Set E} {v₁ : V} {hX : N.HubCond X v₁}

omit [Finite E] in
theorem hubNet_src_none : (N.hubNet X v₁ hX).src none = some v₁ := rfl

omit [Finite E] in
theorem hubNet_tgt_none : (N.hubNet X v₁ hX).tgt none = none := rfl

omit [Finite E] in
theorem hubNet_tgt_some (e : E) : (N.hubNet X v₁ hX).tgt (some e) = some (N.tgt e) := rfl

omit [Finite E] in
theorem hubNet_src_of_mem {e : E} (he : e ∈ X) : (N.hubNet X v₁ hX).src (some e) = none := by
  simp [hubNet, he]

omit [Finite E] in
theorem hubNet_src_of_notMem {e : E} (he : e ∉ X) : (N.hubNet X v₁ hX).src (some e) = some (N.src e) := by
  simp [hubNet, he]

omit [Finite E] in
theorem hubNet_site (i : ι) : (N.hubNet X v₁ hX).site i = some (N.site i) := rfl

omit [Finite V] [Finite E] in
theorem not_mem_of_onCycle (hX : N.HubCond X v₁) {e : E} (he : N.OnCycle e) : e ∉ X := fun hm => hX.tree e hm he

omit [Finite E] in
/-- A path of `N` off `X` is a path of the hub network. -/
theorem hubNet_isPath : ∀ {l : List E} {u v : V}, N.IsPath u v l → (∀ h ∈ l, h ∉ X) →
    (N.hubNet X v₁ hX).IsPath (some u) (some v) (l.map some)
  | [], _, _, h, _ => by
    cases h
    rfl
  | g :: _, _, _, h, hl => by
    obtain ⟨rfl, h₂⟩ := h
    exact ⟨hubNet_src_of_notMem (hl g List.mem_cons_self), hubNet_isPath h₂ fun k hk => hl k (List.mem_cons_of_mem _ hk)⟩

omit [Finite E] in
/-- A cycle of `N` is a cycle of the hub network. -/
theorem hubNet_isCycleOn {w x : V} {p q : List E} (hc : N.IsCycleOn w x p q) (hX : N.HubCond X v₁) :
    (N.hubNet X v₁ hX).IsCycleOn (some w) (some x) (p.map some) (q.map some) := by
  obtain ⟨⟨e, f, hef, he, hf⟩, hp, hq, hpq, hdisj⟩ := hc
  have hrec : N.IsCycleOn w x p q := ⟨⟨e, f, hef, he, hf⟩, hp, hq, hpq, hdisj⟩
  refine ⟨⟨some e, some f, by simpa using hef, by simp [hubNet_tgt_some, he], by simp [hubNet_tgt_some, hf]⟩,
    hubNet_isPath hp (fun h hh => not_mem_of_onCycle hX (hrec.onCycle_left hh)),
    hubNet_isPath hq (fun h hh => not_mem_of_onCycle hX (hrec.onCycle_right hh)),
    fun h => hpq (List.map_injective_iff.2 (Option.some_injective _) h), ?_⟩
  intro e' he' f' hf' hee
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he'
  obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hf'
  simp only [hubNet_tgt_some, Option.some.injEq] at hee ⊢
  exact hdisj a ha c hc' hee

omit [Finite E] in
/-- The arcs into one node of the hub network have a coalescent node, by paths of `N`. -/
theorem hubNet_paths (hX : N.HubCond X v₁) {f₁ f₂ : Option E} (hne : f₁ ≠ f₂) (h : (N.hubNet X v₁ hX).tgt f₁ = (N.hubNet X v₁ hX).tgt f₂) :
    ∃ w p q, (N.hubNet X v₁ hX).IsPath w ((N.hubNet X v₁ hX).src f₁) p ∧ (N.hubNet X v₁ hX).IsPath w ((N.hubNet X v₁ hX).src f₂) q ∧
      (∀ k ∈ p, ∃ k₀, k = some k₀ ∧ N.OnCycle k₀) ∧ ∀ k ∈ q, ∃ k₀, k = some k₀ ∧ N.OnCycle k₀ := by
  rcases f₁ with _ | f₁
  · rcases f₂ with _ | f₂
    · exact absurd rfl hne
    · simp [hubNet_tgt_none, hubNet_tgt_some] at h
  · rcases f₂ with _ | f₂
    · simp [hubNet_tgt_none, hubNet_tgt_some] at h
    · simp only [hubNet_tgt_some, Option.some.injEq] at h
      have hne' : f₁ ≠ f₂ := fun h' => hne (by rw [h'])
      obtain ⟨w, p, q, hp, hq, hc⟩ := exists_isCycleOn_of_tgt_eq hne' h
      have hf₁ : f₁ ∉ X := not_mem_of_onCycle hX (hc.onCycle_left (by simp))
      have hf₂ : f₂ ∉ X := not_mem_of_onCycle hX (hc.onCycle_right (by simp))
      have honp : ∀ k ∈ p, N.OnCycle k := fun k hk => hc.onCycle_left (List.mem_append_left _ hk)
      have honq : ∀ k ∈ q, N.OnCycle k := fun k hk => hc.onCycle_right (List.mem_append_left _ hk)
      refine ⟨some w, p.map some, q.map some, ?_, ?_, ?_, ?_⟩
      · rw [hubNet_src_of_notMem hf₁]
        exact hubNet_isPath hp fun k hk => not_mem_of_onCycle hX (honp k hk)
      · rw [hubNet_src_of_notMem hf₂]
        exact hubNet_isPath hq fun k hk => not_mem_of_onCycle hX (honq k hk)
      · intro k hk
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hk
        exact ⟨a, rfl, honp a ha⟩
      · intro k hk
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hk
        exact ⟨a, rfl, honq a ha⟩

omit [Finite E] in
/-- The new arc is a tree arc. -/
theorem hubNet_isTreeArc_none (hX : N.HubCond X v₁) : (N.hubNet X v₁ hX).IsTreeArc none := by
  refine isTreeArc_of_forall_tgt_eq ?_ fun f₁ f₂ hne h => ?_
  · rintro (_ | f) hf
    · rfl
    · simp [hubNet_tgt_none, hubNet_tgt_some] at hf
  · obtain ⟨w, p, q, hp, hq, h₁, h₂⟩ := hubNet_paths hX hne h
    refine ⟨w, p, q, hp, hq, fun hn => ?_, fun hn => ?_⟩
    · obtain ⟨k₀, hk, -⟩ := h₁ none hn
      simp at hk
    · obtain ⟨k₀, hk, -⟩ := h₂ none hn
      simp at hk

omit [Finite E] in
/-- A tree arc of `N` is a tree arc of the hub network. -/
theorem hubNet_isTreeArc_some (hX : N.HubCond X v₁) {e : E} (he : N.IsTreeArc e) : (N.hubNet X v₁ hX).IsTreeArc (some e) := by
  refine isTreeArc_of_forall_tgt_eq ?_ fun f₁ f₂ hne h => ?_
  · rintro (_ | f) hf
    · simp [hubNet_tgt_none, hubNet_tgt_some] at hf
    · simp only [hubNet_tgt_some, Option.some.injEq] at hf
      rw [he.eq_of_tgt_eq hf]
  · obtain ⟨w, p, q, hp, hq, h₁, h₂⟩ := hubNet_paths hX hne h
    refine ⟨w, p, q, hp, hq, fun hn => ?_, fun hn => ?_⟩
    · obtain ⟨k₀, hk, hk'⟩ := h₁ _ hn
      simp only [Option.some.injEq] at hk
      exact he (hk ▸ hk')
    · obtain ⟨k₀, hk, hk'⟩ := h₂ _ hn
      simp only [Option.some.injEq] at hk
      exact he (hk ▸ hk')

omit [Finite E] in
/-- An arc on a cycle of the hub network is an arc on a cycle of `N`. -/
theorem hubNet_onCycle (hX : N.HubCond X v₁) {e' : Option E} (he : (N.hubNet X v₁ hX).OnCycle e') : ∃ e, e' = some e ∧ N.OnCycle e := by
  rcases e' with _ | e
  · exact absurd he (hubNet_isTreeArc_none hX)
  · refine ⟨e, rfl, ?_⟩
    by_contra hnot
    exact hubNet_isTreeArc_some hX hnot he

omit [Finite E] in
/-- A path of the hub network on arcs of cycles is a path of `N`. -/
theorem hubNet_unmap_path (hX : N.HubCond X v₁) : ∀ {l : List (Option E)} {u v : Option V}, (N.hubNet X v₁ hX).IsPath u v l →
    (∀ k ∈ l, (N.hubNet X v₁ hX).OnCycle k) → ∀ {x : V}, v = some x → ∃ w l₀, u = some w ∧ l = l₀.map some ∧ N.IsPath w x l₀
  | [], _, _, h, _, x, hx => by
    cases h
    exact ⟨x, [], hx, rfl, rfl⟩
  | k :: l, _, _, h, hl, x, hx => by
    obtain ⟨rfl, h₂⟩ := h
    obtain ⟨k₀, rfl, hk₀⟩ := hubNet_onCycle hX (hl k List.mem_cons_self)
    obtain ⟨w, l₀, hw, hl₀, hp⟩ := hubNet_unmap_path hX h₂ (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk')) hx
    simp only [hubNet_tgt_some, Option.some.injEq] at hw
    refine ⟨N.src k₀, k₀ :: l₀, hubNet_src_of_notMem (not_mem_of_onCycle hX hk₀), by simp [hl₀], rfl, ?_⟩
    rw [hw]
    exact hp

omit [Finite E] in
/-- A cycle of the hub network is a cycle of `N`. -/
theorem hubNet_unmap_cycle (hX : N.HubCond X v₁) {w' x' : Option V} {p' q' : List (Option E)} (hc : (N.hubNet X v₁ hX).IsCycleOn w' x' p' q') :
    ∃ w x p q, p' = p.map some ∧ q' = q.map some ∧ N.IsCycleOn w x p q := by
  obtain ⟨⟨e', f', hef, he, hf⟩, hp, hq, hpq, hdisj⟩ := id hc
  have hmem : ∀ {k}, (k ∈ p' ∨ k ∈ q') → (N.hubNet X v₁ hX).OnCycle k := by
    intro k hk
    rcases hk with hk | hk
    · exact hc.onCycle_left hk
    · exact hc.onCycle_right hk
  rcases e' with _ | e
  · rcases f' with _ | f
    · exact absurd rfl hef
    · simp [hubNet_tgt_none, hubNet_tgt_some] at he hf
      subst he
      simp at hf
  · rcases f' with _ | f
    · simp only [hubNet_tgt_none, hubNet_tgt_some] at he hf
      subst hf
      simp at he
    · simp only [hubNet_tgt_some] at he hf
      subst he
      simp only [Option.some.injEq] at hf
      obtain ⟨w, p, hw, rfl, hpN⟩ := hubNet_unmap_path hX hp (fun k hk => hmem (Or.inl hk)) rfl
      obtain ⟨w₂, q, hw₂, rfl, hqN⟩ := hubNet_unmap_path hX hq (fun k hk => hmem (Or.inr hk)) rfl
      have hww : w₂ = w := by
        rw [hw] at hw₂
        simpa using hw₂.symm
      subst hww
      refine ⟨w₂, N.tgt e, p, q, rfl, rfl, ⟨e, f, fun h' => hef (by rw [h']), rfl, hf⟩, hpN, hqN, fun h' => hpq (by rw [h']), ?_⟩
      intro a ha c hc' hac
      have := hdisj (some a) (List.mem_map_of_mem ha) (some c) (List.mem_map_of_mem hc') (by simp [hubNet_tgt_some, hac])
      simpa [hubNet_tgt_some] using this

omit [Finite E] in
/-- **The cycles of the hub network are those of `N`.** -/
theorem hubNet_isCycle_iff (hX : N.HubCond X v₁) (Q' : Set (Option E)) :
    (N.hubNet X v₁ hX).IsCycle Q' ↔ ∃ Q, N.IsCycle Q ∧ Q' = some '' Q := by
  constructor
  · rintro ⟨w', x', p', q', hc, rfl⟩
    obtain ⟨w, x, p, q, rfl, rfl, hc₀⟩ := hubNet_unmap_cycle hX hc
    refine ⟨_, ⟨w, x, p, q, hc₀, rfl⟩, ?_⟩
    ext k
    simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_image]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · exact ⟨a, Or.inl ha, rfl⟩
      · exact ⟨a, Or.inr ha, rfl⟩
    · rintro ⟨a, ha | ha, rfl⟩
      · exact Or.inl ⟨a, ha, rfl⟩
      · exact Or.inr ⟨a, ha, rfl⟩
  · rintro ⟨Q, ⟨w, x, p, q, hc, rfl⟩, rfl⟩
    refine ⟨_, _, _, _, hubNet_isCycleOn hc hX, ?_⟩
    ext k
    simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_image]
    constructor
    · rintro ⟨a, ha | ha, rfl⟩
      · exact Or.inl ⟨a, ha, rfl⟩
      · exact Or.inr ⟨a, ha, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · exact ⟨a, Or.inl ha, rfl⟩
      · exact ⟨a, Or.inr ha, rfl⟩

omit [Finite E] in
/-- **The blobs of the hub network are those of `N`.** -/
theorem hubNet_isBlob_iff (hX : N.HubCond X v₁) (B' : Set (Option E)) :
    (N.hubNet X v₁ hX).IsBlob B' ↔ ∃ B, N.IsBlob B ∧ B' = some '' B :=
  isBlob_iff_of_isCycle_iff some (Option.some_injective _) (hubNet_isCycle_iff hX) B'

omit [Finite E] in
/-- The nodes of a blob of the hub network are those of `N`. -/
theorem hubNet_blobVerts (hX : N.HubCond X v₁) {B : Set E} (hB : N.IsBlob B) : (N.hubNet X v₁ hX).blobVerts (some '' B) = some '' N.blobVerts B := by
  have hsrc : ∀ {a}, a ∈ B → (N.hubNet X v₁ hX).src (some a) = some (N.src a) := fun ha =>
    hubNet_src_of_notMem (not_mem_of_onCycle hX (hB.onCycle_of_mem ha))
  ext z
  constructor
  · rintro (⟨_, ⟨a, ha, rfl⟩, rfl⟩ | ⟨_, ⟨a, ha, rfl⟩, rfl⟩)
    · exact ⟨_, src_mem_blobVerts ha, (hsrc ha).symm⟩
    · exact ⟨_, tgt_mem_blobVerts ha, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩, rfl⟩
    · exact Or.inl ⟨some a, ⟨a, ha, rfl⟩, hsrc ha⟩
    · exact Or.inr ⟨some a, ⟨a, ha, rfl⟩, rfl⟩

omit [Finite E] in
/-- Blobs that are node-disjoint stay so. -/
theorem hubNet_blobsNodeDisjoint (hX : N.HubCond X v₁) (h : N.BlobsNodeDisjoint) : (N.hubNet X v₁ hX).BlobsNodeDisjoint := by
  intro B₁ B₂ hB₁ hB₂ hne
  obtain ⟨B₁, hB₁', rfl⟩ := (hubNet_isBlob_iff hX _).1 hB₁
  obtain ⟨B₂, hB₂', rfl⟩ := (hubNet_isBlob_iff hX _).1 hB₂
  rw [hubNet_blobVerts hX hB₁', hubNet_blobVerts hX hB₂']
  have hne' : B₁ ≠ B₂ := fun h' => hne (by rw [h'])
  exact (Set.disjoint_image_iff (Option.some_injective _)).2 (h B₁ B₂ hB₁' hB₂' hne')

omit [Finite E] in
/-- **The hub network is fully decomposed, if `N` is.** "If `N` is fully-decomposed, then the efficient network derived from it is also fully-decomposed" (line 330). -/
theorem hubNet_isFullyDecomposedFor (hX : N.HubCond X v₁) {G : SimpleGraph ι} (hf : N.IsFullyDecomposedFor G) :
    (N.hubNet X v₁ hX).IsFullyDecomposedFor G where
  blob_component B' hB' := by
    obtain ⟨B, hB, rfl⟩ := (hubNet_isBlob_iff hX _).1 hB'
    obtain ⟨c, hc, hi⟩ := hf.blob_component B hB
    refine ⟨c, hc, fun i => ?_⟩
    rw [← hi i, hubNet_site]
    simp
  isolated_treeArc i hi := hubNet_isTreeArc_some hX (hf.isolated_treeArc i hi)
  nodeDisjoint := hubNet_blobsNodeDisjoint hX hf.nodeDisjoint

omit [Finite E] in
theorem hubNet_isRecomb_some {z : V} : (N.hubNet X v₁ hX).IsRecomb (some z) ↔ N.IsRecomb z := by
  constructor
  · rintro ⟨e, f, hef, he, hf⟩
    rcases e with _ | e
    · simp [hubNet_tgt_none] at he
    · rcases f with _ | f
      · simp [hubNet_tgt_none] at hf
      · exact ⟨e, f, fun h => hef (by rw [h]), by simpa [hubNet_tgt_some] using he, by simpa [hubNet_tgt_some] using hf⟩
  · rintro ⟨e, f, hef, rfl, hf⟩
    exact ⟨some e, some f, by simpa using hef, rfl, by simp [hubNet_tgt_some, hf]⟩

omit [Finite E] in
theorem hubNet_not_isRecomb_none : ¬ (N.hubNet X v₁ hX).IsRecomb none := by
  rintro ⟨e, f, hef, he, hf⟩
  rcases e with _ | e
  · rcases f with _ | f
    · exact hef rfl
    · simp [hubNet_tgt_some] at hf
  · simp [hubNet_tgt_some] at he

omit [Finite E] in
/-- The hub network has the recombination nodes of `N`. -/
theorem hubNet_recombCount : (N.hubNet X v₁ hX).recombCount = N.recombCount := by
  refine Nat.card_congr ⟨fun x => ⟨?_, ?_⟩, fun x => ⟨some x.1, hubNet_isRecomb_some.2 x.2⟩, ?_, ?_⟩
  · exact (x.1).getD v₁
  · obtain ⟨_ | z, hz⟩ := x
    · exact absurd hz hubNet_not_isRecomb_none
    · exact hubNet_isRecomb_some.1 hz
  · rintro ⟨_ | z, hz⟩
    · exact absurd hz hubNet_not_isRecomb_none
    · rfl
  · rintro ⟨z, hz⟩
    rfl

omit [Finite E] in
/-- The hub network obeys the crossover models of `N`. -/
theorem hubNet_obeys [LinearOrder ι] (hX : N.HubCond X v₁) {c : Crossover} (hc : N.Obeys c) : (N.hubNet X v₁ hX).Obeys c := by
  have hsrc : ∀ {e f : E}, e ≠ f → N.tgt e = N.tgt f → (N.hubNet X v₁ hX).src (some e) = some (N.src e) := fun hef h =>
    hubNet_src_of_notMem (not_mem_of_onCycle hX (onCycle_of_tgt_eq hef h))
  cases c with
  | single =>
    rintro (_ | z) hx
    · exact absurd hx hubNet_not_isRecomb_none
    · obtain ⟨e, f, hef, he, hf, L, hL⟩ := hc z (hubNet_isRecomb_some.1 hx)
      refine ⟨some e, some f, by simpa using hef, by simp [hubNet_tgt_some, he], by simp [hubNet_tgt_some, hf], L, fun i => ?_⟩
      rw [hsrc hef (he.trans hf.symm), hsrc hef.symm (hf.trans he.symm)]
      exact hL i
  | multiple => trivial
  | pointwise =>
    rintro (_ | z) hx
    · exact absurd hx hubNet_not_isRecomb_none
    · obtain ⟨e, f, hef, he, hf, j, hL⟩ := hc z (hubNet_isRecomb_some.1 hx)
      refine ⟨some e, some f, by simpa using hef, by simp [hubNet_tgt_some, he], by simp [hubNet_tgt_some, hf], j, fun i => ?_⟩
      rw [hsrc hef (he.trans hf.symm), hsrc hef.symm (hf.trans he.symm)]
      exact hL i

omit [Finite E] in
/-- The hub network derives what `N` derives, if the arcs of `X` don't leave a new leaf. -/
theorem hubNet_derives {M : Finset (ι → Bool)} (hd : N.Derives M) (hne : X.Nonempty) (hv : ¬ N.IsLeaf v₁)
    (hsrc : ∀ e ∈ X, N.src e = v₁ ∨ ∃ f, f ∉ X ∧ N.src f = N.src e) : (N.hubNet X v₁ hX).Derives M := by
  have hleaf : ∀ {z : V}, (N.hubNet X v₁ hX).IsLeaf (some z) ↔ N.IsLeaf z := by
    intro z
    constructor
    · intro hz e he
      subst he
      by_cases hm : e ∈ X
      · rcases hsrc e hm with h₁ | ⟨f, hf, h₂⟩
        · exact hz none (by rw [hubNet_src_none, h₁])
        · exact hz (some f) (by rw [hubNet_src_of_notMem hf, h₂])
      · exact hz (some e) (hubNet_src_of_notMem hm)
    · intro hz e' he'
      rcases e' with _ | e
      · have h₁ : v₁ = z := by simpa [hubNet_src_none] using he'
        exact hv (h₁ ▸ hz)
      · by_cases hm : e ∈ X
        · rw [hubNet_src_of_mem hm] at he'
          simp at he'
        · rw [hubNet_src_of_notMem hm] at he'
          exact hz e (by simpa using he')
  have hnone : ¬ (N.hubNet X v₁ hX).IsLeaf none := by
    obtain ⟨e, he⟩ := hne
    exact fun h => h (some e) (hubNet_src_of_mem he)
  refine ⟨?_, ?_, ?_⟩
  · rintro (_ | z) hz
    · exact absurd hz hnone
    · exact hd.mapsTo (hleaf.1 hz)
  · rintro (_ | z) hz (_ | y) hy hzy
    · rfl
    · exact absurd hz hnone
    · exact absurd hy hnone
    · rw [hd.injOn (hleaf.1 hz) (hleaf.1 hy) hzy]
  · intro r hr
    obtain ⟨z, hz, rfl⟩ := hd.surjOn hr
    exact ⟨some z, hleaf.2 hz, rfl⟩

variable (N) in
/-- The arcs leaving a blob, that are measured in the proof that a network can be made efficient. -/
noncomputable def exitCount : ℕ := Nat.card {e // N.IsTreeArc e ∧ N.OnBlob (N.src e)}

/-- **Moving two exits to a hub lowers the number of exits.** -/
theorem hubNet_exitCount_lt (hX : N.HubCond X v₁) {e₀ e₁ : E} (he₀ : e₀ ∈ X) (he₁ : e₁ ∈ X) (hne : e₀ ≠ e₁) (hb : ∀ e ∈ X, N.OnBlob (N.src e)) :
    (N.hubNet X v₁ hX).exitCount < N.exitCount := by
  have hm : ∀ x : {e' // (N.hubNet X v₁ hX).IsTreeArc e' ∧ (N.hubNet X v₁ hX).OnBlob ((N.hubNet X v₁ hX).src e')},
      ∃ y : {e // N.IsTreeArc e ∧ N.OnBlob (N.src e)}, (x.1 = none ∧ y.1 = e₀) ∨ (x.1 = some y.1 ∧ y.1 ∉ X) := by
    rintro ⟨_ | e, ht, hOn⟩
    · exact ⟨⟨e₀, hX.tree e₀ he₀, hb e₀ he₀⟩, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨B', hB', hv⟩ := hOn
      obtain ⟨B, hB, rfl⟩ := (hubNet_isBlob_iff hX _).1 hB'
      rw [hubNet_blobVerts hX hB] at hv
      have hmem : e ∉ X := by
        intro hm
        rw [hubNet_src_of_mem hm] at hv
        obtain ⟨z, -, hz⟩ := hv
        simp at hz
      rw [hubNet_src_of_notMem hmem] at hv
      obtain ⟨z, hz, hzs⟩ := hv
      obtain rfl : z = N.src e := by simpa using hzs
      have hte : N.IsTreeArc e := by
        intro hc
        obtain ⟨Q, hQ, heQ⟩ := hc
        exact ht ⟨some '' Q, (hubNet_isCycle_iff hX _).2 ⟨Q, hQ, rfl⟩, ⟨e, heQ, rfl⟩⟩
      exact ⟨⟨e, hte, B, hB, hz⟩, Or.inr ⟨rfl, hmem⟩⟩
  choose g hg using hm
  have hinj : Function.Injective g := by
    rintro x y hxy
    rcases hg x with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;> rcases hg y with ⟨hy, hy'⟩ | ⟨hy, hy'⟩
    · exact Subtype.ext (hx.trans hy.symm)
    · rw [hxy] at hx'
      rw [hx'] at hy'
      exact absurd he₀ hy'
    · rw [hxy] at hx'
      rw [hy'] at hx'
      exact absurd he₀ hx'
    · refine Subtype.ext ?_
      rw [hx, hy, hxy]
  have hnotsurj : ¬ Function.Surjective g := by
    intro hs
    obtain ⟨x, hx⟩ := hs ⟨e₁, hX.tree e₁ he₁, hb e₁ he₁⟩
    rcases hg x with ⟨-, h⟩ | ⟨-, h⟩
    · rw [hx] at h
      exact hne h.symm
    · rw [hx] at h
      exact h he₁
  have := Fintype.ofFinite {e // N.IsTreeArc e ∧ N.OnBlob (N.src e)}
  have := Fintype.ofFinite {e' // (N.hubNet X v₁ hX).IsTreeArc e' ∧ (N.hubNet X v₁ hX).OnBlob ((N.hubNet X v₁ hX).src e')}
  rw [exitCount, exitCount, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_not_surjective g hinj hnotsurj

/-! ### Moving the root down -/

section Reroot

variable {ι : Type u} {V : Type v} {E : Type w}

/-- The root has one arc out of it, and that arc is the only arc into its target. -/
structure RerootCond (N : Network ι V E) (a : E) : Prop where
  src_root : N.src a = N.root
  uniq_out : ∀ f, N.src f = N.root → f = a
  uniq_in : ∀ f, N.tgt f = N.tgt a → f = a

theorem tgt_ne_root (N : Network ι V E) (e : E) : N.tgt e ≠ N.root := fun h => (N.root_iff N.root).2 rfl e h

variable [Finite V]

/-- The network with the arc out of the root turned round. The target of the arc is the new root, and the old root is a leaf with its label, on that arc: "Line 418 itself places a root on an edge" and this moves it to the end of the edge. -/
noncomputable def rerootNet (N : Network ι V E) (a : E) (ha : N.RerootCond a) : Network ι V E where
  src e := if e = a then N.tgt a else N.src e
  tgt e := if e = a then N.root else N.tgt e
  root := N.tgt a
  site := N.site
  label := N.label
  simple e f h₁ h₂ := by
    by_cases he : e = a
    · by_cases hf : f = a
      · rw [he, hf]
      · simp only [he, hf, ite_true, ite_false] at h₂
        exact absurd h₂.symm (N.tgt_ne_root f)
    · by_cases hf : f = a
      · simp only [he, hf, ite_true, ite_false] at h₂
        exact absurd h₂ (N.tgt_ne_root e)
      · simp only [he, hf, ite_false] at h₁ h₂
        exact N.simple e f h₁ h₂
  acyclic := by
    obtain ⟨ρ, hρ⟩ := N.exists_rank
    obtain ⟨K, hK⟩ := (Set.finite_range ρ).bddAbove
    have hlt : ∀ v, ρ v < K + 1 := fun v => Nat.lt_succ_of_le (hK ⟨v, rfl⟩)
    refine acyclic_of_rank (fun v => if v = N.root then K + 1 else ρ v) fun e => ?_
    by_cases he : e = a
    · simp only [he, ite_true, N.tgt_ne_root a, ite_false]
      exact hlt _
    · have hs : N.src e ≠ N.root := fun h => he (ha.uniq_out e h)
      simp only [he, ite_false, hs, N.tgt_ne_root e]
      exact hρ e
  root_iff v := by
    constructor
    · intro h
      by_contra hne
      by_cases hv : v = N.root
      · exact h a (by simp [hv])
      · have hex : ∃ g, N.tgt g = v := by
          by_contra hno
          push Not at hno
          exact hv ((N.root_iff v).1 hno)
        obtain ⟨g, rfl⟩ := hex
        have hga : g ≠ a := fun h' => hne (by rw [h'])
        exact h g (by simp [hga])
    · rintro rfl e he
      by_cases hea : e = a
      · simp only [hea, ite_true] at he
        exact N.tgt_ne_root a he.symm
      · simp only [hea, ite_false] at he
        exact hea (ha.uniq_in e he)
  inDegree_le_two e f g h₁ h₂ := by
    by_cases he : e = a
    · by_cases hf : f = a
      · exact Or.inl (by rw [he, hf])
      · simp only [he, hf, ite_true, ite_false] at h₁
        exact absurd h₁.symm (N.tgt_ne_root f)
    · by_cases hf : f = a
      · simp only [he, hf, ite_true, ite_false] at h₁
        exact absurd h₁ (N.tgt_ne_root e)
      · by_cases hg : g = a
        · simp only [hf, hg, ite_true, ite_false] at h₂
          exact absurd h₂ (N.tgt_ne_root f)
        · simp only [he, hf, hg, ite_false] at h₁ h₂
          exact N.inDegree_le_two e f g h₁ h₂
  site_not_recomb i f h := by
    by_cases hs : N.site i = a
    · by_cases hf : f = a
      · rw [hf, hs]
      · simp only [hs, hf, ite_true, ite_false] at h
        exact absurd h (N.tgt_ne_root f)
    · by_cases hf : f = a
      · simp only [hs, hf, ite_true, ite_false] at h
        exact absurd h.symm (N.tgt_ne_root _)
      · simp only [hs, hf, ite_false] at h
        exact N.site_not_recomb i f h
  label_tree e he i := by
    by_cases hea : e = a
    · subst hea
      have h := N.label_tree e ha.uniq_in i
      rw [ha.src_root] at h
      simp only [ite_true]
      by_cases hs : N.site i = e
      · simp only [hs, ite_true] at h ⊢
        rw [h]
        simp
      · simp only [hs, ite_false] at h ⊢
        exact h.symm
    · have huniq : ∀ f, N.tgt f = N.tgt e → f = e := by
        intro f hf
        have hfa : f ≠ a := fun h' => hea (ha.uniq_in e (by rw [← hf, h']))
        exact he f (by simp [hfa, hea, hf])
      simp only [hea, ite_false]
      exact N.label_tree e huniq i
  label_recomb e f hef h i := by
    by_cases he : e = a
    · by_cases hf : f = a
      · exact absurd (he.trans hf.symm) hef
      · simp only [he, hf, ite_true, ite_false] at h
        exact absurd h.symm (N.tgt_ne_root f)
    · by_cases hf : f = a
      · simp only [he, hf, ite_true, ite_false] at h
        exact absurd h (N.tgt_ne_root e)
      · simp only [he, hf, ite_false] at h ⊢
        exact N.label_recomb e f hef h i

variable {N : Network ι V E} {a : E} {ha : N.RerootCond a}

theorem rerootNet_src_ne {e : E} (he : e ≠ a) : (N.rerootNet a ha).src e = N.src e := by simp [rerootNet, he]

theorem rerootNet_tgt_ne {e : E} (he : e ≠ a) : (N.rerootNet a ha).tgt e = N.tgt e := by simp [rerootNet, he]

theorem rerootNet_src_self : (N.rerootNet a ha).src a = N.tgt a := by simp [rerootNet]

theorem rerootNet_tgt_self : (N.rerootNet a ha).tgt a = N.root := by simp [rerootNet]

theorem rerootNet_label : (N.rerootNet a ha).label = N.label := rfl

omit [Finite V] in
/-- The arc out of the root isn't on a cycle. -/
theorem RerootCond.isTreeArc (ha : N.RerootCond a) : N.IsTreeArc a :=
  isTreeArc_of_cut (N := N) (fun z => z ≠ N.root) (N.tgt_ne_root a) (by simp [ha.src_root]) (fun f _ => N.tgt_ne_root f)
    (fun f _ hs => ha.uniq_out f (by simpa using hs)) ha.uniq_in

/-- The arc to the old root isn't on a cycle. -/
theorem rerootNet_isTreeArc_self (ha : N.RerootCond a) : (N.rerootNet a ha).IsTreeArc a := by
  refine isTreeArc_of_cut (N := N.rerootNet a ha) (fun z => z = N.root) rerootNet_tgt_self ?_ ?_ ?_ ?_
  · rw [rerootNet_src_self]
    exact N.tgt_ne_root a
  · intro f hf
    by_cases hfa : f = a
    · rw [hfa, rerootNet_src_self] at hf
      exact absurd hf (N.tgt_ne_root a)
    · rw [rerootNet_src_ne hfa] at hf
      exact absurd (ha.uniq_out f hf) hfa
  · intro f hf _
    by_contra hfa
    rw [rerootNet_tgt_ne hfa] at hf
    exact N.tgt_ne_root f hf
  · intro f hf
    by_contra hfa
    rw [rerootNet_tgt_self, rerootNet_tgt_ne hfa] at hf
    exact N.tgt_ne_root f hf

theorem rerootNet_isPath (ha : N.RerootCond a) {l : List E} : ∀ {u v : V}, a ∉ l → ((N.rerootNet a ha).IsPath u v l ↔ N.IsPath u v l) := by
  induction l with
  | nil => exact fun _ => Iff.rfl
  | cons e l ih =>
    intro u v h
    have he : e ≠ a := fun h' => h (h' ▸ List.mem_cons_self)
    have hl : a ∉ l := fun h' => h (List.mem_cons_of_mem _ h')
    simp only [IsPath, rerootNet_src_ne he, rerootNet_tgt_ne he, ih hl]

theorem rerootNet_isRecomb {x : V} : (N.rerootNet a ha).IsRecomb x ↔ N.IsRecomb x := by
  have hne : ∀ {e f : E}, e ≠ f → (N.rerootNet a ha).tgt e = (N.rerootNet a ha).tgt f → e ≠ a := by
    intro e f hef h hea
    by_cases hf : f = a
    · exact hef (hea.trans hf.symm)
    · rw [hea, rerootNet_tgt_self, rerootNet_tgt_ne hf] at h
      exact N.tgt_ne_root f h.symm
  have hne' : ∀ {e f : E}, e ≠ f → N.tgt e = N.tgt f → e ≠ a := by
    intro e f hef h hea
    exact hef (hea.trans (ha.uniq_in f (by rw [← h, hea])).symm)
  constructor
  · rintro ⟨e, f, hef, he, hf⟩
    have h₁ := hne hef (he.trans hf.symm)
    have h₂ := hne hef.symm (hf.trans he.symm)
    exact ⟨e, f, hef, (rerootNet_tgt_ne h₁).symm.trans he, (rerootNet_tgt_ne h₂).symm.trans hf⟩
  · rintro ⟨e, f, hef, he, hf⟩
    have h₁ := hne' hef (he.trans hf.symm)
    have h₂ := hne' hef.symm (hf.trans he.symm)
    exact ⟨e, f, hef, (rerootNet_tgt_ne h₁).trans he, (rerootNet_tgt_ne h₂).trans hf⟩

/-- **The cycles of the network with the root moved are those of `N`.** -/
theorem rerootNet_isCycleOn (ha : N.RerootCond a) {w x : V} {p q : List E} : (N.rerootNet a ha).IsCycleOn w x p q ↔ N.IsCycleOn w x p q := by
  constructor
  · intro hc
    have hp : a ∉ p := fun h => rerootNet_isTreeArc_self ha (hc.onCycle_left h)
    have hq : a ∉ q := fun h => rerootNet_isTreeArc_self ha (hc.onCycle_right h)
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hc
    refine ⟨rerootNet_isRecomb.1 h₁, (rerootNet_isPath ha hp).1 h₂, (rerootNet_isPath ha hq).1 h₃, h₄, fun e he f hf hef => ?_⟩
    have hea : e ≠ a := fun h => hp (h ▸ he)
    have hfa : f ≠ a := fun h => hq (h ▸ hf)
    have := h₅ e he f hf (by rw [rerootNet_tgt_ne hea, rerootNet_tgt_ne hfa, hef])
    rwa [rerootNet_tgt_ne hea] at this
  · intro hc
    have hp : a ∉ p := fun h => ha.isTreeArc (hc.onCycle_left h)
    have hq : a ∉ q := fun h => ha.isTreeArc (hc.onCycle_right h)
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hc
    refine ⟨rerootNet_isRecomb.2 h₁, (rerootNet_isPath ha hp).2 h₂, (rerootNet_isPath ha hq).2 h₃, h₄, fun e he f hf hef => ?_⟩
    have hea : e ≠ a := fun h => hp (h ▸ he)
    have hfa : f ≠ a := fun h => hq (h ▸ hf)
    rw [rerootNet_tgt_ne hea, rerootNet_tgt_ne hfa] at hef
    rw [rerootNet_tgt_ne hea]
    exact h₅ e he f hf hef

theorem rerootNet_isCycle (ha : N.RerootCond a) (Q : Set E) : (N.rerootNet a ha).IsCycle Q ↔ N.IsCycle Q := by
  unfold IsCycle
  simp only [rerootNet_isCycleOn ha]

theorem rerootNet_onCycle (ha : N.RerootCond a) (e : E) : (N.rerootNet a ha).OnCycle e ↔ N.OnCycle e := by
  unfold OnCycle
  simp only [rerootNet_isCycle ha]

theorem rerootNet_isBlob (ha : N.RerootCond a) (B : Set E) : (N.rerootNet a ha).IsBlob B ↔ N.IsBlob B := by
  rw [isBlob_iff_of_isCycle_iff (N := N) (N' := N.rerootNet a ha) id Function.injective_id (fun Q' => by simp [rerootNet_isCycle ha])]
  simp

theorem rerootNet_blobVerts (ha : N.RerootCond a) {B : Set E} (hB : N.IsBlob B) : (N.rerootNet a ha).blobVerts B = N.blobVerts B := by
  have hne : ∀ {e}, e ∈ B → e ≠ a := fun he h => ha.isTreeArc (hB.onCycle_of_mem (h ▸ he))
  ext z
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · rw [rerootNet_src_ne (hne he)]
      exact src_mem_blobVerts he
    · rw [rerootNet_tgt_ne (hne he)]
      exact tgt_mem_blobVerts he
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact Or.inl ⟨e, he, rerootNet_src_ne (hne he)⟩
    · exact Or.inr ⟨e, he, rerootNet_tgt_ne (hne he)⟩

/-- The network with the root moved is fully decomposed, if `N` is. -/
theorem rerootNet_isFullyDecomposedFor (ha : N.RerootCond a) {G : SimpleGraph ι} (hf : N.IsFullyDecomposedFor G) : (N.rerootNet a ha).IsFullyDecomposedFor G where
  blob_component B hB := hf.blob_component B ((rerootNet_isBlob ha B).1 hB)
  isolated_treeArc i hi := fun hc => hf.isolated_treeArc i hi ((rerootNet_onCycle ha _).1 hc)
  nodeDisjoint := by
    intro B₁ B₂ h₁ h₂ hne
    have h₁' := (rerootNet_isBlob ha B₁).1 h₁
    have h₂' := (rerootNet_isBlob ha B₂).1 h₂
    rw [rerootNet_blobVerts ha h₁', rerootNet_blobVerts ha h₂']
    exact hf.nodeDisjoint B₁ B₂ h₁' h₂' hne

theorem rerootNet_obeys [LinearOrder ι] (ha : N.RerootCond a) {c : Crossover} (hc : N.Obeys c) : (N.rerootNet a ha).Obeys c := by
  have hne : ∀ {e f : E}, e ≠ f → N.tgt e = N.tgt f → e ≠ a := by
    intro e f hef h hea
    exact hef (hea.trans (ha.uniq_in f (by rw [← h, hea])).symm)
  cases c with
  | single =>
    intro x hx
    obtain ⟨e, f, hef, he, hf, L, hL⟩ := hc x (rerootNet_isRecomb.1 hx)
    have h₁ := hne hef (he.trans hf.symm)
    have h₂ := hne hef.symm (hf.trans he.symm)
    refine ⟨e, f, hef, (rerootNet_tgt_ne h₁).trans he, (rerootNet_tgt_ne h₂).trans hf, L, fun i => ?_⟩
    rw [rerootNet_src_ne h₁, rerootNet_src_ne h₂]
    exact hL i
  | multiple => trivial
  | pointwise =>
    intro x hx
    obtain ⟨e, f, hef, he, hf, j, hL⟩ := hc x (rerootNet_isRecomb.1 hx)
    have h₁ := hne hef (he.trans hf.symm)
    have h₂ := hne hef.symm (hf.trans he.symm)
    refine ⟨e, f, hef, (rerootNet_tgt_ne h₁).trans he, (rerootNet_tgt_ne h₂).trans hf, j, fun i => ?_⟩
    rw [rerootNet_src_ne h₁, rerootNet_src_ne h₂]
    exact hL i

/-- The leaves of the network with the root moved are the old root and the leaves of `N`, if the target of the arc wasn't a leaf. -/
theorem rerootNet_isLeaf (ha : N.RerootCond a) (hy : ¬ N.IsLeaf (N.tgt a)) (v : V) : (N.rerootNet a ha).IsLeaf v ↔ v = N.root ∨ N.IsLeaf v := by
  constructor
  · intro h
    by_cases hv : v = N.root
    · exact Or.inl hv
    · refine Or.inr fun e he => ?_
      by_cases hea : e = a
      · exact hv (he.symm.trans (hea ▸ ha.src_root))
      · exact h e ((rerootNet_src_ne hea).trans he)
  · rintro (rfl | hl) e he
    · by_cases hea : e = a
      · rw [hea, rerootNet_src_self] at he
        exact N.tgt_ne_root a he
      · rw [rerootNet_src_ne hea] at he
        exact hea (ha.uniq_out e he)
    · by_cases hea : e = a
      · rw [hea, rerootNet_src_self] at he
        exact hy (he ▸ hl)
      · rw [rerootNet_src_ne hea] at he
        exact hl e he

/-- The network with the root moved derives the rows of `N` and the sequence at the old root. -/
theorem rerootNet_derives (ha : N.RerootCond a) (hy : ¬ N.IsLeaf (N.tgt a)) {M : Finset (ι → Bool)} (hd : N.Derives M) (hS : N.ancestral ∉ M) [DecidableEq (ι → Bool)] :
    (N.rerootNet a ha).Derives (insert N.ancestral M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rcases (rerootNet_isLeaf ha hy v).1 hv with rfl | hl
    · exact Finset.mem_coe.2 (Finset.mem_insert_self _ _)
    · exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 (hd.mapsTo hl)))
  · intro u hu v hv huv
    rw [rerootNet_label] at huv
    rcases (rerootNet_isLeaf ha hy u).1 hu with rfl | hlu <;> rcases (rerootNet_isLeaf ha hy v).1 hv with rfl | hlv
    · rfl
    · have h' : N.label v ∈ (M : Set (ι → Bool)) := hd.mapsTo hlv
      rw [← huv] at h'
      exact absurd (Finset.mem_coe.1 h') hS
    · have h' : N.label u ∈ (M : Set (ι → Bool)) := hd.mapsTo hlu
      rw [huv] at h'
      exact absurd (Finset.mem_coe.1 h') hS
    · exact hd.injOn hlu hlv huv
  · intro r hr
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hr) with rfl | hrM
    · exact ⟨N.root, (rerootNet_isLeaf ha hy _).2 (Or.inl rfl), rfl⟩
    · obtain ⟨v, hv, rfl⟩ := hd.surjOn hrM
      exact ⟨v, (rerootNet_isLeaf ha hy _).2 (Or.inr hv), rfl⟩

end Reroot

end Network

end Gusfield2007
