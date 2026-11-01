module

public import Gusfield2007.SameCycles
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
/-- **The hub network has the recombination cycles of `N`**: the arcs of `X` are tree arcs, and the new arc ends at the hub, with no other arc into it. -/
theorem hubNet_sameCycles (hX : N.HubCond X v₁) : SameCycles N (N.hubNet X v₁ hX) some some where
  f_inj := Option.some_injective _
  g_inj := Option.some_injective _
  src _ he := hubNet_src_of_notMem (not_mem_of_onCycle hX he)
  tgt _ _ := rfl
  recomb := by
    rintro (_ | e) (_ | l) hne ht
    · exact absurd rfl hne
    · simp [hubNet_tgt_none, hubNet_tgt_some] at ht
    · simp [hubNet_tgt_none, hubNet_tgt_some] at ht
    · exact ⟨e, l, fun h => hne (by rw [h]), by simpa [hubNet_tgt_some] using ht, rfl, rfl⟩

omit [Finite E] in
/-- **The cycles of the hub network are those of `N`.** -/
theorem hubNet_isCycle_iff (hX : N.HubCond X v₁) (Q' : Set (Option E)) :
    (N.hubNet X v₁ hX).IsCycle Q' ↔ ∃ Q, N.IsCycle Q ∧ Q' = some '' Q :=
  (hubNet_sameCycles hX).isCycle_iff Q'

omit [Finite E] in
/-- **The blobs of the hub network are those of `N`.** -/
theorem hubNet_isBlob_iff (hX : N.HubCond X v₁) (B' : Set (Option E)) :
    (N.hubNet X v₁ hX).IsBlob B' ↔ ∃ B, N.IsBlob B ∧ B' = some '' B :=
  (hubNet_sameCycles hX).isBlob_iff B'

omit [Finite E] in
/-- The nodes of a blob of the hub network are those of `N`. -/
theorem hubNet_blobVerts (hX : N.HubCond X v₁) {B : Set E} (hB : N.IsBlob B) : (N.hubNet X v₁ hX).blobVerts (some '' B) = some '' N.blobVerts B :=
  (hubNet_sameCycles hX).blobVerts_image hB

omit [Finite E] in
/-- Blobs that are node-disjoint stay so. -/
theorem hubNet_blobsNodeDisjoint (hX : N.HubCond X v₁) (h : N.BlobsNodeDisjoint) : (N.hubNet X v₁ hX).BlobsNodeDisjoint :=
  (hubNet_sameCycles hX).blobsNodeDisjoint_iff.2 h

omit [Finite E] in
/-- **The hub network is fully decomposed, if `N` is.** "If `N` is fully-decomposed, then the efficient network derived from it is also fully-decomposed" (line 330). -/
theorem hubNet_isFullyDecomposedFor (hX : N.HubCond X v₁) {G : SimpleGraph ι} (hf : N.IsFullyDecomposedFor G) :
    (N.hubNet X v₁ hX).IsFullyDecomposedFor G :=
  ((hubNet_sameCycles hX).isFullyDecomposedFor_iff hubNet_site).2 hf

omit [Finite E] in
theorem hubNet_isRecomb_some {z : V} : (N.hubNet X v₁ hX).IsRecomb (some z) ↔ N.IsRecomb z :=
  (hubNet_sameCycles hX).isRecomb_iff

omit [Finite E] in
theorem hubNet_not_isRecomb_none : ¬ (N.hubNet X v₁ hX).IsRecomb none := fun h => by
  obtain ⟨x, hx, -⟩ := (hubNet_sameCycles hX).exists_of_isRecomb h
  simp at hx

omit [Finite E] in
/-- The hub network has the recombination nodes of `N`. -/
theorem hubNet_recombCount : (N.hubNet X v₁ hX).recombCount = N.recombCount :=
  (hubNet_sameCycles hX).recombCount_eq

omit [Finite E] in
/-- The hub network obeys the crossover models of `N`. -/
theorem hubNet_obeys [LinearOrder ι] (hX : N.HubCond X v₁) {c : Crossover} (hc : N.Obeys c) : (N.hubNet X v₁ hX).Obeys c :=
  (hubNet_sameCycles hX).obeys (fun _ => rfl) hc

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

/-- The network with the arc out of the root turned round. The target of the arc is the new root, and the old root is a leaf with its label, on that arc. Line 418 places a root on an edge, and this moves it to the end of the edge. -/
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

/-- **The network with the root moved has the recombination cycles of `N`**: the arc out of the root isn't on a cycle of either. -/
theorem rerootNet_sameCycles (ha : N.RerootCond a) : SameCycles N (N.rerootNet a ha) id id where
  f_inj := Function.injective_id
  g_inj := Function.injective_id
  src _ he := rerootNet_src_ne fun h => ha.isTreeArc (h ▸ he)
  tgt _ he := rerootNet_tgt_ne fun h => ha.isTreeArc (h ▸ he)
  recomb e f hef h := by
    have hne : ∀ {e f : E}, e ≠ f → (N.rerootNet a ha).tgt e = (N.rerootNet a ha).tgt f → e ≠ a := by
      intro e f hef h hea
      by_cases hf : f = a
      · exact hef (hea.trans hf.symm)
      · rw [hea, rerootNet_tgt_self, rerootNet_tgt_ne hf] at h
        exact N.tgt_ne_root f h.symm
    refine ⟨e, f, hef, ?_, rfl, rfl⟩
    rw [← rerootNet_tgt_ne (ha := ha) (hne hef h), ← rerootNet_tgt_ne (ha := ha) (hne hef.symm h.symm)]
    exact h

theorem rerootNet_isRecomb {x : V} : (N.rerootNet a ha).IsRecomb x ↔ N.IsRecomb x :=
  (rerootNet_sameCycles ha).isRecomb_iff

theorem rerootNet_onCycle (ha : N.RerootCond a) (e : E) : (N.rerootNet a ha).OnCycle e ↔ N.OnCycle e :=
  (rerootNet_sameCycles ha).onCycle_iff

/-- The network with the root moved is fully decomposed, if `N` is. -/
theorem rerootNet_isFullyDecomposedFor (ha : N.RerootCond a) {G : SimpleGraph ι} (hf : N.IsFullyDecomposedFor G) : (N.rerootNet a ha).IsFullyDecomposedFor G :=
  ((rerootNet_sameCycles ha).isFullyDecomposedFor_iff fun _ => rfl).2 hf

theorem rerootNet_obeys [LinearOrder ι] (ha : N.RerootCond a) {c : Crossover} (hc : N.Obeys c) : (N.rerootNet a ha).Obeys c :=
  (rerootNet_sameCycles ha).obeys (fun _ => rfl) hc

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
