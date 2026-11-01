module

public import Gusfield2007.Uniqueness

/-!
# Gusfield et al. 2007, Section 3.7: the hypotheses of Theorem 4 can be met

The corrected Theorem 4 (`theorem4`, `theorem4_entry`) has hypotheses that the printed theorem doesn't. This module shows that they aren't vacuous: for every `M` with at least three rows, there's an efficient fully decomposed network whose `T′` is `T̄`, with all of the hypotheses, and with its root at
an interior node of `T̄` (`exists_realization`).

The network is that of the proof of Theorem 1 (line 299), with each central node inflated to a network all of whose arcs are on cycles, and with the root at a row `S` of `M`. There the row `S` has no leaf, and the root has one arc: turn it round (`Network.rerootNet`). So the old root becomes the leaf of `S`, and the root
moves to the neighbour of `S` in `T̄`, which is an interior node since `M` has at least three rows. Line 299 lets the root of `T̄` be any node; this is the case of the neighbour of a row, and `Gusfield2007.RootedFrame` has the others (`exists_network_rooted_at`).

So there's an efficient fully decomposed network for every `M` in the sense of `IsEfficientAtEntry` too (`exists_isEfficientAtEntry`), which is line 329 for that definition. That the modification doesn't increase the number of recombinations is `exists_isEfficientAtEntry_of_fullyDecomposed`, in `Gusfield2007.EntryNet`.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

universe u v

section Proj

variable {ι V E W : Type*} [Finite V] [Finite E] {N : Network ι V E} {T : SimpleGraph W}

/-- `T′` is a graph `T`, given a map `τ` from the nodes of `N` to the nodes of `T`, that's constant exactly on the classes of `T′`, and that takes the tree arcs of `N` onto the edges of `T`. -/
theorem Network.exists_blobbedTree_iso_of_proj (τ : V → W) (h₁ : ∀ e, N.OnCycle e → τ (N.src e) = τ (N.tgt e))
    (h₂ : ∀ u v, τ u = τ v → N.toBlobNode u = N.toBlobNode v) (h₃ : Function.Surjective τ)
    (h₄ : ∀ e, N.IsTreeArc e → T.Adj (τ (N.src e)) (τ (N.tgt e)))
    (h₅ : ∀ x y, T.Adj x y → ∃ e, N.IsTreeArc e ∧ s(τ (N.src e), τ (N.tgt e)) = s(x, y)) :
    ∃ f : N.blobbedTree ≃g T, ∀ v, f (N.toBlobNode v) = τ v := by
  let g : N.BlobNode → W := Quotient.lift τ fun u v huv => N.eq_of_toBlobNode_eq τ h₁ (Quotient.sound huv)
  have hbij : Function.Bijective g := by
    refine ⟨fun a b hab => ?_, fun w => ?_⟩
    · obtain ⟨u, rfl⟩ : ∃ u, N.toBlobNode u = a := Quotient.exists_rep a
      obtain ⟨v, rfl⟩ : ∃ v, N.toBlobNode v = b := Quotient.exists_rep b
      exact h₂ u v hab
    · obtain ⟨v, rfl⟩ := h₃ w
      exact ⟨N.toBlobNode v, rfl⟩
  refine ⟨⟨Equiv.ofBijective g hbij, ?_⟩, fun _ => rfl⟩
  intro a b
  obtain ⟨u, rfl⟩ : ∃ u, N.toBlobNode u = a := Quotient.exists_rep a
  obtain ⟨v, rfl⟩ : ∃ v, N.toBlobNode v = b := Quotient.exists_rep b
  constructor
  · intro hadj
    obtain ⟨e, he, hs⟩ := h₅ _ _ hadj
    have hA := Network.blobbedTree_adj he
    rcases Sym2.eq_iff.1 hs with ⟨h, h'⟩ | ⟨h, h'⟩
    · rwa [h₂ _ _ h, h₂ _ _ h'] at hA
    · rw [h₂ _ _ h, h₂ _ _ h'] at hA
      exact hA.symm
  · intro hadj
    obtain ⟨e, he, hs⟩ := Network.exists_isTreeArc_of_adj hadj
    have hA := h₄ e he
    rcases Sym2.eq_iff.1 hs with ⟨h, h'⟩ | ⟨h, h'⟩
    · have k₁ : τ (N.src e) = τ u := N.eq_of_toBlobNode_eq τ h₁ h
      have k₂ : τ (N.tgt e) = τ v := N.eq_of_toBlobNode_eq τ h₁ h'
      rw [k₁, k₂] at hA
      exact hA
    · have k₁ : τ (N.src e) = τ v := N.eq_of_toBlobNode_eq τ h₁ h
      have k₂ : τ (N.tgt e) = τ u := N.eq_of_toBlobNode_eq τ h₁ h'
      rw [k₁, k₂] at hA
      exact hA.symm

/-- Isomorphic networks have isomorphic trees `T′`. -/
theorem Network.IsIso.exists_blobbedTree_iso {V' E' : Type*} [Finite V'] [Finite E'] {N' : Network ι V' E'} {eV : V ≃ V'} {eE : E ≃ E'} (h : N.IsIso N' eV eE) :
    ∃ f : N'.blobbedTree ≃g N.blobbedTree, ∀ v, f (N'.toBlobNode (eV v)) = N.toBlobNode v := by
  have h₁ : ∀ e, N'.OnCycle e → N.toBlobNode (eV.symm (N'.src e)) = N.toBlobNode (eV.symm (N'.tgt e)) := by
    intro e he
    obtain ⟨e, rfl⟩ := eE.surjective e
    simpa [h.src, h.tgt] using Network.toBlobNode_eq_of_onCycle ((h.onCycle e).1 he)
  have h₂ : ∀ u v, N.toBlobNode (eV.symm u) = N.toBlobNode (eV.symm v) → N'.toBlobNode u = N'.toBlobNode v := by
    intro u v huv
    obtain ⟨u, rfl⟩ := eV.surjective u
    obtain ⟨v, rfl⟩ := eV.surjective v
    simp only [Equiv.symm_apply_apply] at huv
    refine N.eq_of_toBlobNode_eq (fun z => N'.toBlobNode (eV z)) (fun e he => ?_) huv
    have := Network.toBlobNode_eq_of_onCycle (N := N') ((h.onCycle e).2 he)
    rwa [h.src, h.tgt] at this
  have h₃ : Function.Surjective fun z => N.toBlobNode (eV.symm z) := by
    intro a
    obtain ⟨u, rfl⟩ : ∃ u, N.toBlobNode u = a := Quotient.exists_rep a
    exact ⟨eV u, by simp⟩
  have h₄ : ∀ e, N'.IsTreeArc e → N.blobbedTree.Adj (N.toBlobNode (eV.symm (N'.src e))) (N.toBlobNode (eV.symm (N'.tgt e))) := by
    intro e he
    obtain ⟨e, rfl⟩ := eE.surjective e
    have he' : N.IsTreeArc e := fun hc => he ((h.onCycle e).2 hc)
    simpa [h.src, h.tgt] using Network.blobbedTree_adj he'
  have h₅ : ∀ x y, N.blobbedTree.Adj x y → ∃ e, N'.IsTreeArc e ∧ s(N.toBlobNode (eV.symm (N'.src e)), N.toBlobNode (eV.symm (N'.tgt e))) = s(x, y) := by
    intro x y hxy
    obtain ⟨e, he, hs⟩ := Network.exists_isTreeArc_of_adj hxy
    refine ⟨eE e, fun hc => he ((h.onCycle e).1 hc), ?_⟩
    simpa [h.src, h.tgt] using hs
  obtain ⟨f, hf⟩ := Network.exists_blobbedTree_iso_of_proj (N := N') (T := N.blobbedTree) (fun z => N.toBlobNode (eV.symm z)) h₁ h₂ h₃ h₄ h₅
  exact ⟨f, fun v => by rw [hf]; simp⟩

end Proj

section Reroot

variable {ι V E : Type*} [Finite V] {N : Network ι V E} {a : E} {ha : N.RerootCond a}

/-- Turning the arc round doesn't change which nodes the arcs join. -/
theorem Network.rerootNet_ends (e : E) : s((N.rerootNet a ha).src e, (N.rerootNet a ha).tgt e) = s(N.src e, N.tgt e) := by
  by_cases he : e = a
  · subst he
    rw [Network.rerootNet_src_self, Network.rerootNet_tgt_self, ← ha.src_root, Sym2.eq_swap]
  · rw [Network.rerootNet_src_ne he, Network.rerootNet_tgt_ne he]

end Reroot

section Realize

variable {ι : Type u} [LinearOrder ι] [Finite ι] {M : Finset (ι → Bool)} {W : Type v} [Finite W] {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W}

open Decomp in
/-- The construction: the network of line 299, rooted at a row, with its arc out of the root turned round. -/
theorem exists_realization_aux (c : Crossover) (hC : NoConstantColumn M) (h3 : 3 ≤ M.card) (h : IsTBar M T φ edge) :
    ∃ (V E : Type (max u v)) (_ : Finite V) (_ : Finite E) (N : Network ι V E), N.Obeys c ∧ N.Derives M ∧ N.IsFullyDecomposedFor (incompatGraph M) ∧
      ∃ f : N.blobbedTree ≃g T, (∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) ∧ f (N.toBlobNode N.root) ∉ Set.range φ := by
  obtain ⟨S, hS⟩ : M.Nonempty := Finset.card_pos.1 (by omega)
  -- The networks for the central nodes.
  have hinf := fun C => exists_inflate_piece c (M := M) C S
  choose a b P hob hanc hder hall huniq using hinf
  have : Finite (incompatGraph M).ConnectedComponent :=
    Finite.of_surjective (incompatGraph M).connectedComponentMk fun c => c.exists_rep
  have hD := h.frame_valid P S hS hanc hder hC
  -- The neighbour of the row `S`.
  have hinj : ∀ {r r' : M}, (r : ι → Bool) ≠ r' → φ r ≠ φ r' := fun {r r'} hr heq => hr (congrArg Subtype.val (h.label_injective heq))
  obtain ⟨r₁, hr₁, hr₁S⟩ := Finset.exists_mem_ne (show 1 < M.card by omega) S
  obtain ⟨y, hy, -⟩ := exists_adj_separating h.isTree (hinj (r := ⟨S, hS⟩) (r' := ⟨r₁, hr₁⟩) (Ne.symm hr₁S))
  have hyρ : y ≠ φ ⟨S, hS⟩ := (T.ne_of_adj hy).symm
  have hpar : h.par (φ ⟨S, hS⟩) y = φ ⟨S, hS⟩ := by
    rcases h.adj_cases (ρ := φ ⟨S, hS⟩) hy with ⟨-, h₂⟩ | ⟨h₁, -⟩
    · exact h₂.symm
    · exact absurd rfl h₁
  have hnbr : ∀ z, T.Adj (φ ⟨S, hS⟩) z → z = y := fun z hz =>
    (Set.ncard_le_one_iff (Set.toFinite _)).1 ((h.mem_range_iff _).1 ⟨_, rfl⟩) hz hy
  -- It's not a row: there's a third row.
  have hyrow : y ∉ Set.range φ := by
    rintro ⟨r, rfl⟩
    obtain ⟨r', hr', hne₁, hne₂⟩ : ∃ r' ∈ M, r' ≠ S ∧ r' ≠ r.1 := by
      have h₄ := Finset.pred_card_le_card_erase (s := M) (a := S)
      have h₅ := Finset.pred_card_le_card_erase (s := M.erase S) (a := r.1)
      obtain ⟨r', hr'⟩ : ((M.erase S).erase r.1).Nonempty := by
        rw [← Finset.card_pos]
        omega
      obtain ⟨h₆, h₇⟩ := Finset.mem_erase.1 hr'
      obtain ⟨h₈, h₉⟩ := Finset.mem_erase.1 h₇
      exact ⟨r', h₉, h₈, h₆⟩
    have ht₁ : φ ⟨S, hS⟩ ≠ φ ⟨r', hr'⟩ := hinj (Ne.symm hne₁)
    have ht₂ : φ r ≠ φ ⟨r', hr'⟩ := hinj (Ne.symm hne₂)
    obtain ⟨w₁, hw₁, -, -, hd₁⟩ := exists_adj_separating h.isTree ht₁
    obtain ⟨w₂, hw₂, -, -, hd₂⟩ := exists_adj_separating h.isTree ht₂
    obtain rfl := hnbr w₁ hw₁
    have hw₂' : w₂ = φ ⟨S, hS⟩ := (Set.ncard_le_one_iff (Set.toFinite _)).1 ((h.mem_range_iff _).1 ⟨_, rfl⟩) hw₂ hy.symm
    rw [hw₂'] at hd₂
    exact lt_asymm hd₁ hd₂
  let D := h.frame P S hS
  have hnotcen : ∀ r : M, φ r ∉ Set.range D.center := by
    rintro r ⟨C, hC'⟩
    have hz : h.side (IsTBar.charOf C.1 r.2) (h.center C.1) = false := h.side_center C.2 rfl
    have hC'' : h.center C.1 = φ r := hC'
    rw [hC'', h.side_row] at hz
    rw [show charValue (IsTBar.charOf C.1 r.2) (r : ι → Bool) = true from IsTBar.charValue_charOf C.1 r.2] at hz
    exact absurd hz (by simp)
  have hlabel : ∀ r : M, (D.net hD).label (.inl ⟨φ r, hnotcen r⟩) = (r : ι → Bool) := fun r => by
    funext i
    exact h.lam_row r i
  have hanc' : (D.net hD).ancestral = S := hlabel ⟨S, hS⟩
  have hrowleaf : ∀ r : M, (r : ι → Bool) ≠ S → (D.net hD).IsLeaf (.inl ⟨φ r, hnotcen r⟩) := by
    intro r hrS
    refine (GlueData.isLeaf_net_inl hD _).2 fun c hc hpar' => ?_
    change h.par (φ ⟨S, hS⟩) c = φ r at hpar'
    have hne₁ : φ r ≠ φ ⟨S, hS⟩ := hinj hrS
    obtain ⟨hadj, -, hdist⟩ := h.par_spec (ρ := φ ⟨S, hS⟩) hc
    obtain ⟨hadj₁, -, hdist₁⟩ := h.par_spec (ρ := φ ⟨S, hS⟩) hne₁
    rw [hpar'] at hadj hdist
    have hbeq : c = h.par (φ ⟨S, hS⟩) (φ r) :=
      (Set.ncard_le_one_iff (Set.toFinite _)).1 ((h.mem_range_iff _).1 ⟨_, rfl⟩) hadj.symm hadj₁
    rw [← hbeq] at hdist₁
    exact lt_asymm hdist hdist₁
  have hderives := h.frame_derives P S hS hder hD ⟨r₁, hr₁, hr₁S⟩
  -- The arc to turn round.
  let a₀ : D.Arcs := .inl ⟨y, hyρ⟩
  have ha : (D.net hD).RerootCond a₀ := by
    refine ⟨?_, ?_, ?_⟩
    · change D.outNode y = .inl ⟨D.ρ, _⟩
      have hnc : D.par y ∉ Set.range D.center := by
        change h.par (φ ⟨S, hS⟩) y ∉ _
        rw [hpar]
        exact hnotcen _
      rw [D.outNode_of_not hnc]
      congr 1
      exact Subtype.ext hpar
    · intro f hf
      cases f with
      | inl c =>
        have ht := congrArg D.toTree hf
        change D.toTree (D.outNode c.1) = φ ⟨S, hS⟩ at ht
        rw [D.toTree_outNode] at ht
        have hadj := (h.par_spec (ρ := φ ⟨S, hS⟩) c.2).1
        change T.Adj c.1 (D.par c.1) at hadj
        rw [ht] at hadj
        have := hnbr _ hadj.symm
        exact congrArg Sum.inl (Subtype.ext this)
      | inr f =>
        obtain ⟨C, e⟩ := f
        exact absurd hf (by simp [GlueData.net, GlueData.arcSrc])
    · exact fun f hf => GlueData.arcTgt_inl _ hf
  have htoTree_tgt : D.toTree ((D.net hD).tgt a₀) = y := D.toTree_inNode y
  have hyleaf : ¬ (D.net hD).IsLeaf ((D.net hD).tgt a₀) := by
    intro hl
    have hm := hderives.mapsTo hl
    obtain ⟨hne₁, hmem₁⟩ := Finset.mem_erase.1 (Finset.mem_coe.1 hm)
    have hlab := hlabel ⟨_, hmem₁⟩
    have heq := hderives.injOn hl (hrowleaf ⟨_, hmem₁⟩ hne₁) hlab.symm
    rw [heq] at htoTree_tgt
    exact hyrow ⟨_, htoTree_tgt⟩
  have hrder : ((D.net hD).rerootNet a₀ ha).Derives M := by
    have h₁ := Network.rerootNet_derives ha hyleaf hderives (by rw [hanc']; exact Finset.notMem_erase S M)
    rwa [hanc', Finset.insert_erase hS] at h₁
  have hP : ∀ C, (∃! B, (P C).IsBlob B) ∧ ∀ i, ∃ B, (P C).IsBlob B ∧ (P C).site i ∈ B := fun C =>
    ⟨huniq C, fun i => (P C).exists_isBlob_of_onCycle (hall C _)⟩
  -- The arcs on cycles are those of the networks.
  have hinl : ∀ c : {c : W // c ≠ D.ρ}, ¬ (D.net hD).OnCycle (.inl c) := by
    rintro c ⟨Q, ⟨w, x, p, q, hc, rfl⟩, hm⟩
    rcases hm with hm | hm
    · exact (GlueData.not_mem_cycle_inl hD hc c).1 hm
    · exact (GlueData.not_mem_cycle_inl hD hc c).2 hm
  have hinr : ∀ C (e : Fin (b C)), (D.net hD).OnCycle (.inr ⟨C, e⟩) := by
    intro C e
    obtain ⟨Q, hQ, hm⟩ := hall C e
    exact ⟨_, (GlueData.emb_piece hD C).isCycle_image hQ, ⟨e, hm, rfl⟩⟩
  have hne_inr : ∀ C (e : Fin (b C)), (Sum.inr ⟨C, e⟩ : D.Arcs) ≠ a₀ := fun C e => Sum.inr_ne_inl
  -- The nodes of a network are one class.
  have hpiece : ∀ C (x : Fin (a C)), ((D.net hD).rerootNet a₀ ha).toBlobNode (.inr ⟨C, x⟩) = ((D.net hD).rerootNet a₀ ha).toBlobNode (.inr ⟨C, (P C).root⟩) := by
    intro C x
    have hr := (P C).reach_root x
    induction hr with
    | refl => rfl
    | tail _ hs ih =>
      obtain ⟨g, hg, hg'⟩ := hs
      rw [← ih, ← hg, ← hg']
      have h₁ := Network.toBlobNode_eq_of_onCycle (N := (D.net hD).rerootNet a₀ ha) (e := .inr ⟨C, g⟩) ((Network.rerootNet_onCycle ha _).2 (hinr C g))
      rw [Network.rerootNet_src_ne (hne_inr C g), Network.rerootNet_tgt_ne (hne_inr C g)] at h₁
      exact h₁.symm
  have hmapends : ∀ e, s(D.toTree (((D.net hD).rerootNet a₀ ha).src e), D.toTree (((D.net hD).rerootNet a₀ ha).tgt e)) = s(D.toTree ((D.net hD).src e), D.toTree ((D.net hD).tgt e)) := by
    intro e
    simpa using congrArg (Sym2.map D.toTree) (Network.rerootNet_ends (ha := ha) e)
  have hends : ∀ c : {c : W // c ≠ D.ρ}, s(D.toTree ((D.net hD).src (.inl c)), D.toTree ((D.net hD).tgt (.inl c))) = s(D.par c.1, c.1) := by
    intro c
    change s(D.toTree (D.outNode c.1), D.toTree (D.inNode c.1)) = _
    rw [D.toTree_outNode, D.toTree_inNode]
  have hτ₁ : ∀ e, ((D.net hD).rerootNet a₀ ha).OnCycle e → D.toTree (((D.net hD).rerootNet a₀ ha).src e) = D.toTree (((D.net hD).rerootNet a₀ ha).tgt e) := by
    intro e he
    cases e with
    | inl c => exact absurd ((Network.rerootNet_onCycle ha _).1 he) (hinl c)
    | inr e =>
      obtain ⟨C, e⟩ := e
      rw [Network.rerootNet_src_ne (hne_inr C e), Network.rerootNet_tgt_ne (hne_inr C e)]
      rfl
  have hτ₂ : ∀ u v, D.toTree u = D.toTree v → ((D.net hD).rerootNet a₀ ha).toBlobNode u = ((D.net hD).rerootNet a₀ ha).toBlobNode v := by
    intro u v huv
    cases u with
    | inl u =>
      cases v with
      | inl v =>
        have : u = v := Subtype.ext huv
        rw [this]
      | inr v =>
        obtain ⟨C, x⟩ := v
        exact absurd ⟨C, huv.symm⟩ u.2
    | inr u =>
      obtain ⟨C, x⟩ := u
      cases v with
      | inl v => exact absurd ⟨C, huv⟩ v.2
      | inr v =>
        obtain ⟨C', x'⟩ := v
        obtain rfl : C = C' := D.center_inj huv
        rw [hpiece C x, hpiece C x']
  have hτ₄ : ∀ e, ((D.net hD).rerootNet a₀ ha).IsTreeArc e → T.Adj (D.toTree (((D.net hD).rerootNet a₀ ha).src e)) (D.toTree (((D.net hD).rerootNet a₀ ha).tgt e)) := by
    intro e he
    cases e with
    | inl c =>
      rw [← SimpleGraph.mem_edgeSet, hmapends, hends]
      exact (h.par_spec (ρ := φ ⟨S, hS⟩) c.2).1.symm
    | inr e =>
      obtain ⟨C, e⟩ := e
      exact absurd ((Network.rerootNet_onCycle ha _).2 (hinr C e)) he
  have hτ₅ : ∀ x y, T.Adj x y → ∃ e, ((D.net hD).rerootNet a₀ ha).IsTreeArc e ∧ s(D.toTree (((D.net hD).rerootNet a₀ ha).src e), D.toTree (((D.net hD).rerootNet a₀ ha).tgt e)) = s(x, y) := by
    intro x₁ x₂ hx
    have hta : ∀ c : {c : W // c ≠ D.ρ}, ((D.net hD).rerootNet a₀ ha).IsTreeArc (.inl c) := fun c hc => hinl c ((Network.rerootNet_onCycle ha _).1 hc)
    rcases h.adj_cases (ρ := φ ⟨S, hS⟩) hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · refine ⟨.inl ⟨x₂, h₁⟩, hta _, ?_⟩
      rw [hmapends, hends]
      change s(h.par (φ ⟨S, hS⟩) x₂, x₂) = _
      rw [← h₂]
    · refine ⟨.inl ⟨x₁, h₁⟩, hta _, ?_⟩
      rw [hmapends, hends]
      change s(h.par (φ ⟨S, hS⟩) x₁, x₁) = _
      rw [← h₂, Sym2.eq_swap]
  obtain ⟨f, hf⟩ := Network.exists_blobbedTree_iso_of_proj (N := (D.net hD).rerootNet a₀ ha) (T := T) D.toTree hτ₁ hτ₂ (fun w => ⟨D.inNode w, D.toTree_inNode w⟩) hτ₄ hτ₅
  refine ⟨D.Vtx, D.Arcs, inferInstance, inferInstance, (D.net hD).rerootNet a₀ ha, Network.rerootNet_obeys ha (GlueData.net_obeys hD hob), hrder,
    Network.rerootNet_isFullyDecomposedFor ha (GlueData.net_fullyDecomposed hD hP), f, fun v r hr hv hvr => ?_, ?_⟩
  · have hrl : ((D.net hD).rerootNet a₀ ha).IsLeaf (.inl ⟨φ ⟨r, hr⟩, hnotcen ⟨r, hr⟩⟩) := by
      refine (Network.rerootNet_isLeaf ha hyleaf _).2 ?_
      by_cases hrS : r = S
      · subst hrS
        exact Or.inl rfl
      · exact Or.inr (hrowleaf ⟨r, hr⟩ hrS)
    have heq := hrder.injOn hv hrl (hvr.trans (hlabel ⟨r, hr⟩).symm)
    rw [hf, heq]
    rfl
  · rw [hf]
    change D.toTree ((D.net hD).tgt a₀) ∉ _
    rw [htoTree_tgt]
    exact hyrow

/-- **Theorem 4 isn't vacuous** (`g:thm4_realizable`). For every `M` with at least three rows, and in any model, there's an efficient fully decomposed network for `M` whose `T′` is `T̄`, respecting the rows, with all of the hypotheses of `theorem4` and `theorem4_entry`. Its root is at an interior node of `T̄`,
of degree at least three in `T′`. It's the network of line 299, with the row `S` moved off the root: see the module docstring. With fewer than three rows, `T̄` has at most one edge, and it has no interior node.

The conditions come from `T′ ≅ T̄`, by `theorem4_iff` and `theorem4_entry`. -/
theorem exists_realization (c : Crossover) (hC : NoConstantColumn M) (h3 : 3 ≤ M.card) (h : IsTBar M T φ edge) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.IsFullyDecomposedFor (incompatGraph M) ∧ N.IsEfficient ∧ N.IsEfficientAtEntry ∧
      N.IsTreeNormalStructural ∧ N.DegreeCond ∧
      (∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) ∧
      3 ≤ (N.blobbedTree.neighborSet (N.toBlobNode N.root)).ncard := by
  obtain ⟨V, E, _, _, N₀, h₁, h₂, h₄, f₀, hrow, hroot⟩ := exists_realization_aux c hC h3 h
  obtain ⟨a, b, N, eV, eE, hiso⟩ := N₀.exists_fin_iso
  obtain ⟨-, k₂, k₃, -, k₅⟩ := hiso.invariants
  obtain ⟨g, hg⟩ := hiso.exists_blobbedTree_iso
  have hd := (k₃ M).2 h₂
  have hfd := (k₅ _).2 h₄
  have hiso' : ∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩ := by
    refine ⟨g.trans f₀, fun v r hr hv hvr => ?_⟩
    obtain ⟨v, rfl⟩ := eV.surjective v
    change f₀ (g (N.toBlobNode (eV v))) = _
    rw [hg]
    refine hrow v r hr ((hiso.isLeaf v).1 hv) ?_
    rw [← hvr, hiso.label]
  obtain ⟨he, hn, hdeg⟩ := (theorem4_iff hd hfd h).1 hiso'
  obtain ⟨hee, -, -⟩ := (theorem4_entry hd hfd h).1 hiso'
  refine ⟨a, b, N, (k₂ c).2 h₁, hd, hfd, he, hee, hn, hdeg, hiso', ?_⟩
  have hrt : N.root = eV N₀.root := hiso.root
  have hdeg₁ : (N.blobbedTree.neighborSet (N.toBlobNode N.root)).ncard = (T.neighborSet (f₀ (N₀.toBlobNode N₀.root))).ncard := by
    have h₆ := SempleSteel2003.ncard_neighborSet_iso (g.trans f₀) (N.toBlobNode N.root)
    have h₇ : (g.trans f₀) (N.toBlobNode N.root) = f₀ (N₀.toBlobNode N₀.root) := by
      rw [hrt]
      change f₀ (g (N.toBlobNode (eV N₀.root))) = _
      rw [hg]
    rw [← h₆, h₇]
  have hne₁ : ¬ (T.neighborSet (f₀ (N₀.toBlobNode N₀.root))).ncard ≤ 1 := fun hle => hroot ((h.mem_range_iff _).2 hle)
  have hne₂ := h.degree_ne_two (f₀ (N₀.toBlobNode N₀.root))
  rw [hdeg₁]
  omega

/-- **Line 329, for `IsEfficientAtEntry`** (`g:efficient_entry_exists`). "So for any `M`, there is a efficient fully-decomposed phylogenetic network for `M`", where an external node can be entered from outside. With at least three rows, that's `exists_realization`; with fewer, `M` has no incompatible pair, and the network of Theorem 1
has no blob.

This is existence, from `T′ ≅ T̄`. Line 329 also says that the modification doesn't increase the number of recombinations: `exists_isEfficient`, `exists_isEfficient_of_any` prove that for the printed definition, and `exists_isEfficientAtEntry_of_fullyDecomposed`, `exists_isEfficientAtEntry_of_any`, in `Gusfield2007.EntryNet`, for this one. Those don't have `T′ ≅ T̄`, since a network with the fewest recombination nodes can have tree arcs in the networks at its central nodes. -/
theorem exists_isEfficientAtEntry (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.IsFullyDecomposedFor (incompatGraph M) ∧ N.IsEfficientAtEntry := by
  by_cases h3 : 3 ≤ M.card
  · obtain ⟨n, T, φ, edge, hT⟩ := exists_isTBar M hM hC
    obtain ⟨a, b, N, h₁, h₂, h₄, -, h₅, -⟩ := exists_realization c hC h3 hT
    exact ⟨a, b, N, h₁, h₂, h₄, h₅⟩
  · obtain ⟨a, b, N, h₁, h₂, h₄⟩ := theorem1 c M hM hC
    have hno : ∀ B, ¬ N.IsBlob B := by
      intro B hB
      obtain ⟨C, hnt, -⟩ := h₄.blob_component B hB
      have h₅ := four_le_card_restrictRows hnt
      have h₆ : (restrictRows C.supp M).card ≤ M.card := Finset.card_image_le
      omega
    exact ⟨a, b, N, h₁, h₂, h₄, ⟨fun B _ _ hB => absurd hB (hno B), fun B _ _ _ hB => absurd hB (hno B)⟩⟩

end Realize

end Gusfield2007
