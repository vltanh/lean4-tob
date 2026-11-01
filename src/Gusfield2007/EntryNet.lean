module

public import Gusfield2007.SameCycles
public import Gusfield2007.Uniqueness

/-!
# Gusfield et al. 2007: line 329 for the definition of "efficient" that counts the entry node

Line 329 says that a network "can be easily modified to become efficient without increasing the number of recombinations used". `exists_isEfficient` proves that for the printed definition. Here it's proved for `Network.IsEfficientAtEntry`, which also counts the arc entering a blob (`exists_isEfficientAtEntry_of_fullyDecomposed`, `exists_isEfficientAtEntry_of_any`).

What's left to do on an efficient network is to remove an exit at a node with the label of the top of an entered blob. The surgery is `Network.entryNet`: subdivide the arc entering the blob by a new node `n`, with the sites of the arc above `n`, so that `n` has the label of the top, and move the exit to `n`. The recombination cycles don't change (`Network.SameCycles`). If the exit was the only arc out of its node, that node is a recombination node, which is then useless: a recombination node goes, and the argument of `exists_isEfficient_core` applies.

This is the surgery that moves the row of `topNet` up to a new node on its entering arc, giving `topNet'`.
-/

@[expose] public noncomputable section

open scoped Classical

namespace Gusfield2007

namespace Network

universe u v w

variable {ι : Type u} {V : Type v} {E : Type w}

/-- What's needed to subdivide the arc `g`, and to move the arcs of `X` to the new node. The label of the new node is that of the target of `g`. -/
structure EntryCond (N : Network ι V E) (g : E) (X : Set E) : Prop where
  g_tree : N.IsTreeArc g
  g_notMem : g ∉ X
  tree : ∀ e ∈ X, N.IsTreeArc e
  label : ∀ e ∈ X, N.label (N.src e) = N.label (N.tgt g)
  acyc : ∀ e ∈ X, ¬ N.Reach (N.tgt e) (N.src g)

variable {N : Network ι V E} {g : E} {X : Set E}

theorem EntryCond.notMem_of_onCycle (hX : N.EntryCond g X) {e : E} (he : N.OnCycle e) : e ∉ X := fun hm => hX.tree e hm he

/-- The source of an arc of the network with the arc `g` subdivided. -/
def entrySrc (N : Network ι V E) (X : Set E) : Option E → Option V
  | none => none
  | some e => if e ∈ X then none else some (N.src e)

/-- The target of an arc of the network with the arc `g` subdivided. The arc `some g` is the part above the new node, and the arc `none` the part below it. -/
def entryTgt (N : Network ι V E) (g : E) : Option E → Option V
  | none => some (N.tgt g)
  | some e => if e = g then none else some (N.tgt e)

theorem EntryCond.ne_of_onCycle (hX : N.EntryCond g X) {e : E} (he : N.OnCycle e) : e ≠ g := fun hm => hX.g_tree (hm ▸ he)

variable [Finite V]

/-- Two arcs into one node of the new network are two arcs into one node of `N`. -/
theorem EntryCond.entryTgt_eq (hX : N.EntryCond g X) {a b : Option E} (hne : a ≠ b) (h : entryTgt N g a = entryTgt N g b) :
    ∃ e f, a = some e ∧ b = some f ∧ e ≠ f ∧ N.tgt e = N.tgt f := by
  rcases a with _ | e <;> rcases b with _ | f
  · exact absurd rfl hne
  · simp only [entryTgt] at h
    by_cases hf : f = g
    · simp [hf] at h
    · simp only [hf, ite_false, Option.some.injEq] at h
      exact absurd (hX.g_tree.eq_of_tgt_eq h.symm) hf
  · simp only [entryTgt] at h
    by_cases he : e = g
    · simp [he] at h
    · simp only [he, ite_false, Option.some.injEq] at h
      exact absurd (hX.g_tree.eq_of_tgt_eq h) he
  · refine ⟨e, f, rfl, rfl, fun h' => hne (by rw [h']), ?_⟩
    simp only [entryTgt] at h
    by_cases he : e = g
    · by_cases hf : f = g
      · exact absurd (by rw [he, hf]) hne
      · simp [he, hf] at h
    · by_cases hf : f = g
      · simp [he, hf] at h
      · simpa [he, hf] using h

/-- The network with the arc `g` subdivided by a new node `none`, and the arcs of `X` moved to the new node. -/
noncomputable def entryNet (N : Network ι V E) (g : E) (X : Set E) (hX : N.EntryCond g X) : Network ι (Option V) (Option E) where
  src := entrySrc N X
  tgt := entryTgt N g
  root := some N.root
  site i := some (N.site i)
  label
    | none => N.label (N.tgt g)
    | some v => N.label v
  simple a b h₁ h₂ := by
    by_contra hne
    obtain ⟨e, f, rfl, rfl, hef, ht⟩ := hX.entryTgt_eq hne h₂
    have he : e ∉ X := hX.notMem_of_onCycle (onCycle_of_tgt_eq hef ht)
    have hf : f ∉ X := hX.notMem_of_onCycle (onCycle_of_tgt_eq hef.symm ht.symm)
    simp only [entrySrc, he, hf, ite_false, Option.some.injEq] at h₁
    exact hef (N.simple e f h₁ ht)
  acyclic := by
    obtain ⟨ρ, hρ⟩ := N.exists_rank
    obtain ⟨K', hK'⟩ := (Set.finite_range ρ).bddAbove
    obtain ⟨K, hK⟩ : ∃ K, ∀ v, ρ v < K := ⟨K' + 1, fun v => Nat.lt_succ_of_le (hK' ⟨v, rfl⟩)⟩
    refine acyclic_of_rank (fun
      | none => K
      | some z => if N.Reach z (N.src g) then ρ z else K + 1 + ρ z) ?_
    have hnot : ¬ N.Reach (N.tgt g) (N.src g) := not_reach_tgt_src g
    rintro (_ | e)
    · simp only [entrySrc, entryTgt, hnot, ite_false]
      omega
    · by_cases heg : e = g
      · subst heg
        simp only [entrySrc, hX.g_notMem, ite_false, entryTgt, ite_true, show N.Reach (N.src e) (N.src e) from Relation.ReflTransGen.refl]
        exact hK _
      · by_cases he : e ∈ X
        · simp only [entrySrc, he, ite_true, entryTgt, heg, ite_false, hX.acyc e he]
          omega
        · simp only [entrySrc, he, ite_false, entryTgt, heg]
          have h₁ := hρ e
          have h₂ := hK (N.src e)
          by_cases ht : N.Reach (N.tgt e) (N.src g)
          · have hs : N.Reach (N.src e) (N.src g) := Relation.ReflTransGen.head (arc_src_tgt e) ht
            simp only [hs, ht, ite_true]
            exact h₁
          · simp only [ht, ite_false]
            split <;> omega
  root_iff := by
    rintro (_ | z)
    · constructor
      · intro h
        exact absurd (by simp [entryTgt]) (h (some g))
      · intro h
        simp at h
    · constructor
      · intro h
        by_cases hz : z = N.tgt g
        · exact absurd (by simp [entryTgt, hz]) (h none)
        · have : ∀ e, N.tgt e ≠ z := fun e he => by
            have heg : e ≠ g := fun h' => hz (by rw [← he, h'])
            exact h (some e) (by simp [entryTgt, heg, he])
          rw [(N.root_iff z).1 this]
      · intro h
        simp only [Option.some.injEq] at h
        subst h
        rintro (_ | e) he
        · simp only [entryTgt, Option.some.injEq] at he
          exact (N.root_iff N.root).2 rfl g he
        · simp only [entryTgt] at he
          by_cases heg : e = g
          · simp [heg] at he
          · simp only [heg, ite_false, Option.some.injEq] at he
            exact (N.root_iff N.root).2 rfl e he
  inDegree_le_two a b c h₁ h₂ := by
    by_cases hab : a = b
    · exact Or.inl hab
    by_cases hbc : b = c
    · exact Or.inr (Or.inr hbc)
    by_cases hac : a = c
    · exact Or.inr (Or.inl hac)
    exfalso
    obtain ⟨e, f, rfl, rfl, hef, ht⟩ := hX.entryTgt_eq hab h₁
    obtain ⟨f', j, hf', rfl, hfj, ht'⟩ := hX.entryTgt_eq hbc h₂
    obtain rfl := Option.some.inj hf'
    rcases N.inDegree_le_two e f j ht ht' with h | h | h
    · exact hef h
    · exact hac (by rw [h])
    · exact hfj h
  site_not_recomb i a h := by
    by_contra hne
    obtain ⟨e, f, rfl, hf, hef, ht⟩ := hX.entryTgt_eq hne h
    obtain rfl := Option.some.inj hf
    exact hef (N.site_not_recomb i e ht)
  label_tree a ha i := by
    rcases a with _ | e
    · simp [entryTgt, entrySrc]
    · by_cases heg : e = g
      · subst heg
        have huniq : ∀ f, N.tgt f = N.tgt e → f = e := fun f hf => hX.g_tree.eq_of_tgt_eq hf
        simp only [entryTgt, ite_true, entrySrc, hX.g_notMem, ite_false, Option.some.injEq]
        exact N.label_tree e huniq i
      · have huniq : ∀ f, N.tgt f = N.tgt e → f = e := fun f hf => by
          by_contra hne
          have hfg : f ≠ g := by
            rintro rfl
            exact heg (hX.g_tree.eq_of_tgt_eq hf.symm)
          have := ha (some f) (by simp [entryTgt, heg, hfg, hf])
          exact hne (Option.some.inj this)
        have h := N.label_tree e huniq i
        by_cases hm : e ∈ X
        · have hl := congrFun (hX.label e hm) i
          simp only [entryTgt, heg, ite_false, entrySrc, hm, ite_true, Option.some.injEq]
          rw [h, hl]
        · simp only [entryTgt, heg, ite_false, entrySrc, hm, Option.some.injEq]
          exact h
  label_recomb a b hne h i := by
    obtain ⟨e, f, rfl, rfl, hef, ht⟩ := hX.entryTgt_eq hne h
    have heC := onCycle_of_tgt_eq hef ht
    have hfC := onCycle_of_tgt_eq hef.symm ht.symm
    simp only [entryTgt, hX.ne_of_onCycle heC, ite_false, entrySrc, hX.notMem_of_onCycle heC, hX.notMem_of_onCycle hfC]
    exact N.label_recomb e f hef ht i

variable {hX : N.EntryCond g X}

theorem entryNet_src_none : (N.entryNet g X hX).src none = none := rfl

theorem entryNet_tgt_none : (N.entryNet g X hX).tgt none = some (N.tgt g) := rfl

theorem entryNet_tgt_self : (N.entryNet g X hX).tgt (some g) = none := by
  change entryTgt N g (some g) = none
  simp [entryTgt]

theorem entryNet_tgt_of_ne {e : E} (he : e ≠ g) : (N.entryNet g X hX).tgt (some e) = some (N.tgt e) := by
  change entryTgt N g (some e) = _
  simp [entryTgt, he]

theorem entryNet_src_of_mem {e : E} (he : e ∈ X) : (N.entryNet g X hX).src (some e) = none := by
  change entrySrc N X (some e) = none
  simp [entrySrc, he]

theorem entryNet_src_of_notMem {e : E} (he : e ∉ X) : (N.entryNet g X hX).src (some e) = some (N.src e) := by
  change entrySrc N X (some e) = _
  simp [entrySrc, he]

/-- **The recombination cycles of `entryNet` are those of `N`.** -/
theorem entryNet_sameCycles (hX : N.EntryCond g X) : SameCycles N (N.entryNet g X hX) some some where
  f_inj := Option.some_injective _
  g_inj := Option.some_injective _
  src _ he := entryNet_src_of_notMem (hX.notMem_of_onCycle he)
  tgt _ he := entryNet_tgt_of_ne (hX.ne_of_onCycle he)
  recomb a b hne h := by
    obtain ⟨e, f, rfl, rfl, hef, ht⟩ := hX.entryTgt_eq hne h
    exact ⟨e, f, hef, ht, rfl, rfl⟩

theorem entryNet_not_isLeaf_none : ¬ (N.entryNet g X hX).IsLeaf none := fun h => h none rfl

/-- `entryNet` derives what `N` derives, if no node loses all its arcs. -/
theorem entryNet_derives {M : Finset (ι → Bool)} (hd : N.Derives M) (hsrc : ∀ e ∈ X, ∃ f, f ∉ X ∧ N.src f = N.src e) : (N.entryNet g X hX).Derives M := by
  have hleaf : ∀ {z : V}, (N.entryNet g X hX).IsLeaf (some z) ↔ N.IsLeaf z := by
    intro z
    constructor
    · intro hz e he
      subst he
      by_cases hm : e ∈ X
      · obtain ⟨f, hf, h₂⟩ := hsrc e hm
        exact hz (some f) (by rw [entryNet_src_of_notMem hf, h₂])
      · exact hz (some e) (entryNet_src_of_notMem hm)
    · intro hz e' he'
      rcases e' with _ | e
      · simp [entryNet_src_none] at he'
      · by_cases hm : e ∈ X
        · rw [entryNet_src_of_mem hm] at he'
          simp at he'
        · rw [entryNet_src_of_notMem hm] at he'
          exact hz e (by simpa using he')
  refine ⟨?_, ?_, ?_⟩
  · rintro (_ | z) hz
    · exact absurd hz entryNet_not_isLeaf_none
    · exact hd.mapsTo (hleaf.1 hz)
  · rintro (_ | z) hz (_ | y) hy hzy
    · rfl
    · exact absurd hz entryNet_not_isLeaf_none
    · exact absurd hy entryNet_not_isLeaf_none
    · rw [hd.injOn (hleaf.1 hz) (hleaf.1 hy) hzy]
  · intro r hr
    obtain ⟨z, hz, rfl⟩ := hd.surjOn hr
    exact ⟨some z, hleaf.2 hz, rfl⟩

/-- An arc of `entryNet` leaving a blob is an arc of `N` leaving the blob, that isn't moved. -/
theorem entryNet_exit (hX : N.EntryCond g X) [Finite E] {B : Set E} (hB : N.IsBlob B) {a : Option E} (hs : (N.entryNet g X hX).src a ∈ (N.entryNet g X hX).blobVerts (some '' B))
    (ht : (N.entryNet g X hX).tgt a ∉ (N.entryNet g X hX).blobVerts (some '' B)) :
    ∃ e, a = some e ∧ e ∉ X ∧ (N.entryNet g X hX).src a = some (N.src e) ∧ N.src e ∈ N.blobVerts B ∧ N.tgt e ∉ N.blobVerts B := by
  have hC := entryNet_sameCycles hX
  rw [hC.blobVerts_image hB] at hs ht
  rcases a with _ | e
  · rw [entryNet_src_none] at hs
    obtain ⟨z, -, hz⟩ := hs
    simp at hz
  · by_cases hm : e ∈ X
    · rw [entryNet_src_of_mem hm] at hs
      obtain ⟨z, -, hz⟩ := hs
      simp at hz
    · rw [entryNet_src_of_notMem hm] at hs
      obtain ⟨z, hz, hzs⟩ := hs
      obtain rfl : z = N.src e := by simpa using hzs
      refine ⟨e, rfl, hm, entryNet_src_of_notMem hm, hz, ?_⟩
      by_cases heg : e = g
      · subst heg
        exact hX.g_tree.tgt_notMem_blobVerts hB hz
      · rw [entryNet_tgt_of_ne heg] at ht
        exact fun h' => ht ⟨_, h', rfl⟩

/-- **`entryNet` keeps an efficient network efficient.** It has fewer external nodes. -/
theorem entryNet_isEfficient (hX : N.EntryCond g X) [Finite E] (he : N.IsEfficient) : (N.entryNet g X hX).IsEfficient := by
  have hC := entryNet_sameCycles hX
  refine ⟨?_, ?_⟩
  · rintro B₁ B₂ v v' hB₁ hB₂ ⟨hv, e, hes, het⟩ ⟨hv', e', hes', het'⟩ hlab
    obtain ⟨B₁, hB₁', rfl⟩ := (hC.isBlob_iff _).1 hB₁
    obtain ⟨B₂, hB₂', rfl⟩ := (hC.isBlob_iff _).1 hB₂
    subst hes
    subst hes'
    obtain ⟨e₀, rfl, -, hs₀, hm₀, ht₀⟩ := entryNet_exit hX hB₁' hv het
    obtain ⟨e₁, rfl, -, hs₁, hm₁, ht₁⟩ := entryNet_exit hX hB₂' hv' het'
    rw [hs₀, hs₁] at hlab ⊢
    have := he.label_inj B₁ B₂ _ _ hB₁' hB₂' ⟨hm₀, e₀, rfl, ht₀⟩ ⟨hm₁, e₁, rfl, ht₁⟩ hlab
    rw [this]
  · intro B a b hB hs ht hsf htf
    obtain ⟨B, hB', rfl⟩ := (hC.isBlob_iff _).1 hB
    obtain ⟨e₀, rfl, -, hs₀, hm₀, ht₀⟩ := entryNet_exit hX hB' hs ht
    obtain ⟨e₁, rfl, -, hs₁, hm₁, ht₁⟩ := entryNet_exit hX hB' (hsf ▸ hs) htf
    rw [hs₀, hs₁] at hsf
    rw [he.exit_unique B e₀ e₁ hB' hm₀ ht₀ (Option.some.inj hsf) ht₁]

/-- **Moving an exit lowers the number of exits.** -/
theorem entryNet_exitCount_lt (hX : N.EntryCond g X) [Finite E] {e₀ : E} (he₀ : e₀ ∈ X) (hb : N.OnBlob (N.src e₀)) :
    (N.entryNet g X hX).exitCount < N.exitCount := by
  have hC := entryNet_sameCycles hX
  have hm : ∀ x : {e' // (N.entryNet g X hX).IsTreeArc e' ∧ (N.entryNet g X hX).OnBlob ((N.entryNet g X hX).src e')},
      ∃ y : {e // N.IsTreeArc e ∧ N.OnBlob (N.src e)}, x.1 = some y.1 ∧ y.1 ∉ X := by
    rintro ⟨a, ht, hOn⟩
    obtain ⟨B', hB', hv⟩ := hOn
    obtain ⟨B, hB, rfl⟩ := (hC.isBlob_iff _).1 hB'
    rw [hC.blobVerts_image hB] at hv
    rcases a with _ | e
    · rw [entryNet_src_none] at hv
      obtain ⟨z, -, hz⟩ := hv
      simp at hz
    · by_cases hmem : e ∈ X
      · rw [entryNet_src_of_mem hmem] at hv
        obtain ⟨z, -, hz⟩ := hv
        simp at hz
      · rw [entryNet_src_of_notMem hmem] at hv
        obtain ⟨z, hz, hzs⟩ := hv
        obtain rfl : z = N.src e := by simpa using hzs
        exact ⟨⟨e, fun hc => ht (hC.onCycle_image hc), B, hB, hz⟩, rfl, hmem⟩
  choose k hk using hm
  have hinj : Function.Injective k := fun x y hxy => Subtype.ext (by rw [(hk x).1, (hk y).1, hxy])
  have hnotsurj : ¬ Function.Surjective k := by
    intro hs
    obtain ⟨x, hx⟩ := hs ⟨e₀, hX.tree e₀ he₀, hb⟩
    have := (hk x).2
    rw [hx] at this
    exact this he₀
  have := Fintype.ofFinite {e // N.IsTreeArc e ∧ N.OnBlob (N.src e)}
  have := Fintype.ofFinite {e' // (N.entryNet g X hX).IsTreeArc e' ∧ (N.entryNet g X hX).OnBlob ((N.entryNet g X hX).src e')}
  rw [exitCount, exitCount, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_not_surjective k hinj hnotsurj

end Network

/-! ### Isomorphic networks -/

section Iso

variable {ι V E V' E' : Type*} {N : Network ι V E} {N' : Network ι V' E'} {eV : V ≃ V'} {eE : E ≃ E'}

/-- An isomorphic network of a network efficient at the entry nodes is efficient at the entry nodes. -/
theorem Network.IsIso.isEfficientAtEntry (h : N.IsIso N' eV eE) (he : N.IsEfficientAtEntry) : N'.IsEfficientAtEntry := by
  have hback : ∀ {B : Set E} {a : E} {v : V}, N'.CrossesAt (eE '' B) (eE a) (eV v) → N.CrossesAt B a v := by
    rintro B a v ⟨hv, h₁⟩
    have hmem : ∀ {z : V}, eV z ∈ N'.blobVerts (eE '' B) ↔ z ∈ N.blobVerts B := fun {z} => by
      rw [h.blobVerts_image, eV.injective.mem_set_image]
    refine ⟨hmem.1 hv, ?_⟩
    rcases h₁ with ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩
    · rw [h.src] at h₂
      rw [h.tgt] at h₃
      exact Or.inl ⟨eV.injective h₂, fun hm => h₃ (hmem.2 hm)⟩
    · rw [h.tgt] at h₂
      rw [h.src] at h₃
      exact Or.inr ⟨eV.injective h₂, fun hm => h₃ (hmem.2 hm)⟩
  refine ⟨?_, ?_⟩
  · rintro B₁ v v' hB₁ ⟨a, ha⟩ ⟨b, hb⟩ hlab
    obtain ⟨B₁, hB₁', rfl⟩ := h.exists_eq_image_of_isBlob hB₁
    obtain ⟨z, rfl⟩ := eV.surjective v
    obtain ⟨z', rfl⟩ := eV.surjective v'
    obtain ⟨a, rfl⟩ := eE.surjective a
    obtain ⟨b, rfl⟩ := eE.surjective b
    rw [h.label, h.label] at hlab
    rw [he.label_inj B₁ z z' hB₁' ⟨a, hback ha⟩ ⟨b, hback hb⟩ hlab]
  · rintro B₁ a b v hB₁ ha hb
    obtain ⟨B₁, hB₁', rfl⟩ := h.exists_eq_image_of_isBlob hB₁
    obtain ⟨z, rfl⟩ := eV.surjective v
    obtain ⟨a, rfl⟩ := eE.surjective a
    obtain ⟨b, rfl⟩ := eE.surjective b
    rw [he.edge_unique B₁ a b z hB₁' (hback ha) (hback hb)]

end Iso

/-! ### The induction -/

section Main

universe u

variable {ι : Type u} [LinearOrder ι] [Finite ι]

/-- **The modification, by induction** on the number of recombination nodes and then the number of exits, within a class `P` of networks, from an efficient network. As long as there's an exit at a node with the label of the top of an entered blob, `entryNet` moves it above the blob. If it's the only arc out of its node, that node is a recombination node, and it goes: then the class has to supply a network with no more recombination nodes than what's left (`hPreduce`), and `exists_isEfficient_core` makes it efficient again. -/
theorem exists_isEfficientAtEntry_core (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M)
    (P : ∀ (V E : Type), Network ι V E → Prop) (hPnd : ∀ (V E : Type) (N : Network ι V E), P V E N → N.BlobsNodeDisjoint)
    (hPhub : ∀ (V E : Type) [Finite V] [Finite E] (N : Network ι V E) (X : Set E) (v₁ : V) (hX : N.HubCond X v₁), P V E N → P (Option V) (Option E) (N.hubNet X v₁ hX))
    (hPentry : ∀ (V E : Type) [Finite V] [Finite E] (N : Network ι V E) (g : E) (X : Set E) (hX : N.EntryCond g X), P V E N → P (Option V) (Option E) (N.entryNet g X hX))
    (hPreduce : ∀ (V E : Type) [Finite V] [Finite E] (N : Network ι V E), P V E N → ∀ (V₃ E₃ : Type u) [Finite V₃] [Finite E₃] (N₃ : Network ι V₃ E₃), N₃.Obeys c → N₃.Derives M → N₃.ancestral = S →
      (∀ x, N₃.IsRecomb x → ∃ z, N.IsRecomb z ∧ ∀ C : Set ι, N₃.BreaksAt x C → N.BreaksAt z C) →
      ∃ (V' E' : Type) (_ : Finite V') (_ : Finite E') (N' : Network ι V' E'), P V' E' N' ∧ N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧ N'.recombCount ≤ N₃.recombCount) :
    ∀ (K n : ℕ) (V E : Type) [Finite V] [Finite E] (N : Network ι V E), P V E N → N.Obeys c → N.Derives M → N.ancestral = S → N.IsEfficient → N.recombCount = K → N.exitCount = n →
      ∃ (V' E' : Type) (_ : Finite V') (_ : Finite E') (N' : Network ι V' E'), P V' E' N' ∧ N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧ N'.IsEfficient ∧ N'.IsEfficientAtEntry ∧ N'.recombCount ≤ K := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ihK =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro V E _ _ N hP hc hd hS he hK hn
      have hnd := hPnd V E N hP
      by_cases hgood : N.NoAncestralExitAtEntered
      · exact ⟨V, E, inferInstance, inferInstance, N, hP, hc, hd, hS, he, (Network.isEfficientAtEntry_iff hnd).2 ⟨he.perBlob, hgood⟩, hK.le⟩
      unfold Network.NoAncestralExitAtEntered at hgood
      push Not at hgood
      obtain ⟨B, e₀, w, hB, hw, hwr, hs, ht, hall⟩ := hgood
      have hlab : N.label (N.src e₀) = N.label w := hB.label_eq_of_forall hs hw.1 hall
      obtain ⟨g, hg, hgw⟩ := (hw.eq_root_or_exists hnd hB).resolve_left hwr
      have ht₀ : N.IsTreeArc e₀ := Network.isTreeArc_of_exit hnd hB hs ht
      have hreach : N.Reach w (N.src e₀) := hw.reach hnd hB hs
      have hge : g ≠ e₀ := fun h => ht (h ▸ hgw ▸ hw.1)
      by_cases hother : ∃ f, f ≠ e₀ ∧ N.src f = N.src e₀
      · -- The exit moves to the entering arc.
        have hX : N.EntryCond g {e₀} := by
          refine ⟨hg, hge, fun e he' => ?_, fun e he' => ?_, fun e he' hr => ?_⟩
          · rw [Set.mem_singleton_iff.1 he']
            exact ht₀
          · rw [Set.mem_singleton_iff.1 he', hgw, hlab]
          · rw [Set.mem_singleton_iff.1 he'] at hr
            have h₁ : N.Reach (N.src g) w := hgw ▸ Relation.ReflTransGen.single (Network.arc_src_tgt g)
            exact Network.not_reach_tgt_src e₀ (hr.trans (h₁.trans hreach))
        have hSC := Network.entryNet_sameCycles hX
        obtain ⟨f, hf, hfs⟩ := hother
        refine ihn _ (hn ▸ Network.entryNet_exitCount_lt hX (Set.mem_singleton e₀) ⟨B, hB, hs⟩) (Option V) (Option E) (N.entryNet g {e₀} hX) (hPentry V E N g {e₀} hX hP) (hSC.obeys (fun _ => rfl) hc)
          (Network.entryNet_derives hd fun e he' => ⟨f, hf, by rw [hfs, Set.mem_singleton_iff.1 he']⟩) hS (Network.entryNet_isEfficient hX he) ?_ rfl
        rw [hSC.recombCount_eq, hK]
      · -- Its node is a recombination node, and it goes.
        push Not at hother
        have honly : ∀ f, N.src f = N.src e₀ → f = e₀ := fun f hf => by
          by_contra hne
          exact hother f hne hf
        have horec : N.IsRecomb (N.src e₀) := hB.isRecomb_of_forall hs fun f hf hc' => ht₀ (honly f hf ▸ hc')
        have hwo : w ≠ N.src e₀ := by
          rintro rfl
          obtain ⟨e, f, hef, he₁, hf₁⟩ := horec
          exact hef ((hg.eq_of_tgt_eq (he₁.trans hgw.symm)).trans (hg.eq_of_tgt_eq (hf₁.trans hgw.symm)).symm)
        have hX : N.HubCond {e₀} w := by
          refine ⟨fun e he' => ?_, fun e he' => ?_, fun e he' hr => ?_⟩
          · rw [Set.mem_singleton_iff.1 he']
            exact ht₀
          · rw [Set.mem_singleton_iff.1 he', hlab]
          · rw [Set.mem_singleton_iff.1 he'] at hr
            exact Network.not_reach_tgt_src e₀ (hr.trans hreach)
        have hex : ∀ r' : M, ∃ l : V, N.IsLeaf l ∧ N.label l = r'.1 := fun r' => by
          obtain ⟨l, hl, hlr⟩ := hd.surjOn r'.2
          exact ⟨l, hl, hlr⟩
        choose lf hlf hlf' using hex
        have hc₁ : ∀ r' : M, (N.hubNet {e₀} w hX).label (some (lf r')) = r'.1 := hlf'
        have hsites : ∀ i, (N.hubNet {e₀} w hX).Kept (fun r' : M => some (lf r')) ((N.hubNet {e₀} w hX).tgt ((N.hubNet {e₀} w hX).site i)) :=
          fun i => Network.kept_tgt_site hc₁ (hC.exists_ne _ i)
        have hbreak : ∀ {z : V}, N.IsRecomb z → ∀ {C : Set ι}, (N.hubNet {e₀} w hX).BreaksAt (some z) C → N.BreaksAt z C := by
          rintro z ⟨e₁, f₁, hne₁, rfl, hf₁⟩ C hb k hk
          have hkX : k ∉ ({e₀} : Set E) := by
            by_cases hke : k = e₁
            · rw [hke]
              exact Network.not_mem_of_onCycle hX (Network.onCycle_of_tgt_eq hne₁ hf₁.symm)
            · exact Network.not_mem_of_onCycle hX (Network.onCycle_of_tgt_eq hke hk)
          have := hb (some k) (by rw [Network.hubNet_tgt_some, hk])
          rwa [Network.hubNet_src_of_notMem hkX] at this
        have hlt : Nat.card {x // (N.hubNet {e₀} w hX).IsRecomb x ∧ (N.hubNet {e₀} w hX).Kept (fun r' : M => some (lf r')) x} < K := by
          have hm : ∀ x : {x // (N.hubNet {e₀} w hX).IsRecomb x ∧ (N.hubNet {e₀} w hX).Kept (fun r' : M => some (lf r')) x},
              ∃ y : {x // N.IsRecomb x}, x.1 = some y.1 := by
            rintro ⟨_ | z, hx, -⟩
            · exact absurd hx Network.hubNet_not_isRecomb_none
            · exact ⟨⟨z, Network.hubNet_isRecomb_some.1 hx⟩, rfl⟩
          choose k hk using hm
          have hkinj : Function.Injective k := fun x y hxy => Subtype.ext (by rw [hk x, hk y, hxy])
          have hnsurj : ¬ Function.Surjective k := by
            intro hsj
            obtain ⟨x, hx⟩ := hsj ⟨N.src e₀, horec⟩
            have hxo : x.1 = some (N.src e₀) := by rw [hk x, hx]
            obtain ⟨r', hre'⟩ := x.2.2
            rw [hxo] at hre'
            rcases Relation.ReflTransGen.cases_head hre' with h | ⟨b, ⟨f, hf₁, -⟩, -⟩
            · have hlo : N.src e₀ = lf r' := by simpa using h
              exact hlf r' e₀ hlo
            · rcases f with _ | f
              · have hro' : w = N.src e₀ := by simpa [Network.hubNet_src_none] using hf₁
                exact hwo hro'
              · by_cases hfX : f ∈ ({e₀} : Set E)
                · rw [Network.hubNet_src_of_mem hfX] at hf₁
                  simp at hf₁
                · rw [Network.hubNet_src_of_notMem hfX] at hf₁
                  have hfo : N.src f = N.src e₀ := by simpa using hf₁
                  exact hfX (honly f hfo)
          have := Fintype.ofFinite {x // N.IsRecomb x}
          have := Fintype.ofFinite {x // (N.hubNet {e₀} w hX).IsRecomb x ∧ (N.hubNet {e₀} w hX).Kept (fun r' : M => some (lf r')) x}
          rw [← hK, Network.recombCount, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          exact Fintype.card_lt_of_injective_not_surjective k hkinj hnsurj
        have hN₃ := Network.trim_recombCount_le (N := N.hubNet {e₀} w hX) (hM := hM) (hanchor := hc₁) (hsite := hsites)
        obtain ⟨V₄, E₄, i₁, i₂, N₄, h₀₄, h₁₄, h₂₄, h₃₄, h₄₄⟩ := hPreduce V E N hP _ _ ((N.hubNet {e₀} w hX).trim (fun r' : M => some (lf r')) hM hc₁ hsites)
          (Network.trim_obeys (Network.hubNet_obeys hX hc)) Network.trim_derives hS (by
            rintro (⟨_ | z, hv⟩ | r') hx
            · exact absurd (Network.trim_isRecomb hx) Network.hubNet_not_isRecomb_none
            · have hz := Network.hubNet_isRecomb_some.1 (Network.trim_isRecomb hx)
              exact ⟨z, hz, fun C hb => hbreak hz (Network.trim_breaksAt hb)⟩
            · exact absurd hx Network.not_trim_isRecomb_inr)
        have hN₄ : N₄.recombCount < K := lt_of_le_of_lt (h₄₄.trans hN₃) hlt
        obtain ⟨V₅, E₅, i₃, i₄, N₅, h₀₅, h₁₅, h₂₅, h₃₅, h₄₅, h₅₅⟩ := exists_isEfficient_core c M S hM hC P hPnd hPhub hPreduce _ _ V₄ E₄ N₄ h₀₄ h₁₄ h₂₄ h₃₄ rfl rfl
        have hN₅ : N₅.recombCount < K := lt_of_le_of_lt h₅₅ hN₄
        obtain ⟨V', E', i₅, i₆, N', k₀, k₁, k₂, k₃, k₄, k₅, k₆⟩ := ihK _ hN₅ _ V₅ E₅ N₅ h₀₅ h₁₅ h₂₅ h₃₅ h₄₅ rfl rfl
        exact ⟨V', E', i₅, i₆, N', k₀, k₁, k₂, k₃, k₄, k₅, k₆.trans hN₅.le⟩

/-- **Line 329 for `IsEfficientAtEntry`, without increasing recombinations** (`g:efficient_entry_norecomb`). "If `N` is not efficient, it can be easily modified to become efficient without increasing the number of recombinations used. Also, if `N` is fully-decomposed, then the efficient network derived from it is also fully-decomposed", with the entry node of a blob counted, for both graphs, `G(M)` and `G_S(M)`. The network is also efficient in the printed sense, with the same ancestral sequence.

Departure from the paper: it gives no modification, for the printed definition. The one here is `exists_isEfficient`, followed by `Network.entryNet`. Gusfield's book (*ReCombinatorics*, MIT Press, 2014) states that there's a canonical network for `M`, as its Theorem 7.3.2. Of its proof, only the first sentence could be read, in a snippet, so this wasn't compared with it, and it isn't known whether that proof keeps the number of recombinations.

The network needn't have `T′ = T̄`, since a network with the fewest recombination nodes can have tree arcs in the networks at its central nodes: this is about the count, and `exists_realization` is about `T′`. -/
theorem exists_isEfficientAtEntry_of_fullyDecomposed {V E : Type*} [Finite V] [Finite E] (N : Network ι V E) {c : Crossover} {M : Finset (ι → Bool)} {G : SimpleGraph ι} (hC : NoConstantColumn M) (hc : N.Obeys c) (hd : N.Derives M)
    (hG : G = incompatGraph M ∨ G = conflictGraph N.ancestral M) (hf : N.IsFullyDecomposedFor G) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = N.ancestral ∧ N'.IsFullyDecomposedFor G ∧ N'.IsEfficient ∧ N'.IsEfficientAtEntry ∧ N'.recombCount ≤ N.recombCount := by
  obtain ⟨l, hl, -⟩ := Network.exists_isLeaf_reach (N := N) N.root
  have hM : M.Nonempty := ⟨_, hd.mapsTo hl⟩
  have hG' : ∀ i j, G.Reachable i j ↔ (conflictGraph N.ancestral M).Reachable i j := by
    rcases hG with rfl | rfl
    · exact fun i j => (reachable_conflictGraph_iff hd hf i j).symm
    · exact fun _ _ => Iff.rfl
  obtain ⟨a₀, b₀, N₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_isEfficient N hC hc hd hG hf
  have hfS := h₄.of_reachable_iff hG'
  obtain ⟨V', E', i₁, i₂, N', h₀', h₁', h₂', h₃', h₄', h₅', h₆'⟩ := exists_isEfficientAtEntry_core c M N.ancestral hM hC (fun _ _ N' => N'.IsFullyDecomposedFor (conflictGraph N.ancestral M)) (fun _ _ _ h => h.nodeDisjoint)
    (fun _ _ _ _ _ _ _ hX h => Network.hubNet_isFullyDecomposedFor hX h)
    (fun _ _ _ _ _ _ _ hX h => ((Network.entryNet_sameCycles hX).isFullyDecomposedFor_iff fun _ => rfl).2 h)
    (by
      intro V E _ _ N₁ hf₁ V₃ E₃ _ _ N₃ k₁ k₂ k₃ hrec
      have hz : ∀ x, N₃.IsRecomb x → N₃.IsZeroComponent (conflictGraph N.ancestral M) x ∨ N₃.IsOneComponent (conflictGraph N.ancestral M) x := by
        intro x hx
        obtain ⟨z, hz, hb⟩ := hrec x hx
        by_cases hex : ∃ C : (conflictGraph N.ancestral M).ConnectedComponent, N₃.BreaksAt x C.supp
        · obtain ⟨C, hC'⟩ := hex
          exact Or.inr ⟨C, hC', fun C' hC'' => hf₁.breaksAt_unique hz (hb _ hC'') (hb _ hC')⟩
        · push Not at hex
          exact Or.inl hex
      have h5 := lemma5 hC N₃ k₁ k₂ k₃ hz
      obtain ⟨a, b, N₄, l₁, l₂, l₃, l₄, l₅⟩ := theorem3 c M N.ancestral hM hC
      exact ⟨Fin a, Fin b, inferInstance, inferInstance, N₄, l₄, l₁, l₂, l₃, l₅.trans_le h5⟩)
    _ _ (Fin a₀) (Fin b₀) N₀ (hfS) h₁ h₂ h₃ h₅ rfl rfl
  obtain ⟨a, b, N'', eV, eE, hiso⟩ := N'.exists_fin_iso
  obtain ⟨k₁, k₂, k₃, k₄, k₅⟩ := hiso.invariants
  refine ⟨a, b, N'', (k₂ c).2 h₁', (k₃ M).2 h₂', k₄.trans h₃', ((k₅ _).2 h₀').of_reachable_iff fun i j => (hG' i j).symm, hiso.isEfficient h₄', hiso.isEfficientAtEntry h₅', ?_⟩
  rw [k₁]
  exact h₆'.trans h₆

/-- **Line 329 for `IsEfficientAtEntry`, for any network** (`g:efficient_entry_any`). `N` needn't be fully decomposed. The convention of line 140 comes first, and the rest is as in `exists_isEfficient_of_any`. -/
theorem exists_isEfficientAtEntry_of_any {V E : Type*} [Finite V] [Finite E] (N : Network ι V E) {c : Crossover} {M : Finset (ι → Bool)} (hC : NoConstantColumn M) (hc : N.Obeys c) (hd : N.Derives M) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = N.ancestral ∧ N'.BlobsNodeDisjoint ∧ N'.IsEfficient ∧ N'.IsEfficientAtEntry ∧ N'.recombCount ≤ N.recombCount := by
  obtain ⟨l, hl, -⟩ := Network.exists_isLeaf_reach (N := N) N.root
  have hM : M.Nonempty := ⟨_, hd.mapsTo hl⟩
  obtain ⟨a₀, b₀, N₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_isEfficient_of_any N hC hc hd
  obtain ⟨V', E', i₁, i₂, N', h₀', h₁', h₂', h₃', h₄', h₅', h₆'⟩ := exists_isEfficientAtEntry_core c M N.ancestral hM hC (fun _ _ N' => N'.BlobsNodeDisjoint) (fun _ _ _ h => h)
    (fun _ _ _ _ _ _ _ hX h => Network.hubNet_blobsNodeDisjoint hX h)
    (fun _ _ _ _ _ _ _ hX h => (Network.entryNet_sameCycles hX).blobsNodeDisjoint_iff.2 h)
    (by
      intro V E _ _ _ _ V₃ E₃ _ _ N₃ k₁ k₂ k₃ _
      obtain ⟨a, b, N₄, l₁, l₂, l₃, l₄, l₅, -, -⟩ := N₃.exists_blobsNodeDisjoint k₁
      exact ⟨Fin a, Fin b, inferInstance, inferInstance, N₄, l₂, l₁, l₅ M k₂, l₃.trans k₃, l₄.le⟩)
    _ _ (Fin a₀) (Fin b₀) N₀ h₄ h₁ h₂ h₃ h₅ rfl rfl
  obtain ⟨a, b, N'', eV, eE, hiso⟩ := N'.exists_fin_iso
  obtain ⟨k₁, k₂, k₃, k₄, -⟩ := hiso.invariants
  refine ⟨a, b, N'', (k₂ c).2 h₁', (k₃ M).2 h₂', k₄.trans h₃', hiso.blobsNodeDisjoint.2 h₀', hiso.isEfficient h₄', hiso.isEfficientAtEntry h₅', ?_⟩
  rw [k₁]
  exact h₆'.trans h₆

end Main

end Gusfield2007
