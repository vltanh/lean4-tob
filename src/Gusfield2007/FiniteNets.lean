module

public import Gusfield2007.BlobFacts
public import Gusfield2007.ExplicitNetworks

/-!
# Gusfield et al. 2007: checking explicit networks by computation

Tools for the networks of the counterexamples of Sections 3.7 and 4.2. A network on `Fin a`, `Fin b` is built by `mkNet`, from conditions that `decide` can check. A `GallCover` lists its blobs by colouring the arcs and the nodes, and it gives
what the statements ask for: which arcs are on cycles, what the blobs are, and whether the network is fully decomposed and efficient. This module has no classical instance, so that the conditions can be decided.
-/

@[expose] public section

namespace Gusfield2007

variable {ι V E : Type*} {κ : Type*}

namespace Network

/-- A cut with decidable membership shows an arc is a tree arc (`isTreeArc_of_cut`). -/
theorem isTreeArc_of_cut' (N : Network ι V E) (D : V → Bool) {e : E} (ht : D (N.tgt e) = true) (hs : D (N.src e) = false)
    (hout : ∀ f, D (N.src f) = true → D (N.tgt f) = true) (hin : ∀ f, D (N.tgt f) = true → D (N.src f) = false → f = e)
    (huniq : ∀ f, N.tgt f = N.tgt e → f = e) : N.IsTreeArc e :=
  isTreeArc_of_cut (N := N) (fun z => D z = true) ht (by simp [hs]) hout (fun f hf hs' => hin f hf (by simpa using hs')) huniq

/-- A diamond is a recombination cycle: `w` to `a` to `x`, and `w` to `b` to `x`. -/
theorem isCycle_of_diamond (N : Network ι V E) {e₁ e₂ f₁ f₂ : E} (h₁ : N.src e₁ = N.src f₁) (h₂ : N.tgt e₁ = N.src e₂) (h₃ : N.tgt f₁ = N.src f₂)
    (h₄ : N.tgt e₂ = N.tgt f₂) (hne : e₂ ≠ f₂) (h₅ : N.tgt e₁ ≠ N.tgt f₁) (h₆ : N.tgt e₁ ≠ N.tgt e₂) (h₇ : N.tgt f₁ ≠ N.tgt e₂) :
    N.IsCycle {g | g ∈ [e₁, e₂] ∨ g ∈ [f₁, f₂]} := by
  refine ⟨N.src e₁, N.tgt e₂, [e₁, e₂], [f₁, f₂], ⟨⟨e₂, f₂, hne, rfl, h₄.symm⟩, ⟨rfl, h₂.symm, rfl⟩, ⟨h₁.symm, h₃.symm, h₄.symm⟩, ?_, ?_⟩, rfl⟩
  · intro h
    exact hne (by simpa using congrArg List.tail h)
  · intro a ha c hc hac
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hc
    rcases ha with rfl | rfl <;> rcases hc with rfl | rfl
    · exact absurd hac h₅
    · exact absurd (hac.trans h₄.symm) h₆
    · exact absurd hac.symm h₇
    · rfl

end Network

/-- A list of the blobs of `N`, by colours: `ac` gives the colour of each arc on a cycle, and `vc` the colour of each node on a blob. Each blob is one cycle here. -/
structure GallCover (N : Network ι V E) (ac : E → Option κ) (vc : V → Option κ) : Prop where
  cycle : ∀ k, N.IsCycle {e | ac e = some k}
  tree : ∀ e, ac e = none → N.IsTreeArc e
  color : ∀ e k, ac e = some k → vc (N.src e) = some k ∧ vc (N.tgt e) = some k
  vert : ∀ v k, vc v = some k → ∃ e, ac e = some k ∧ (N.src e = v ∨ N.tgt e = v)

namespace GallCover

variable {N : Network ι V E} {ac : E → Option κ} {vc : V → Option κ}

theorem onCycle_iff (h : GallCover N ac vc) (e : E) : N.OnCycle e ↔ ∃ k, ac e = some k := by
  constructor
  · intro hc
    cases he : ac e with
    | none => exact absurd hc (h.tree e he)
    | some k => exact ⟨k, rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨_, h.cycle k, hk⟩

theorem isTreeArc_iff (h : GallCover N ac vc) (e : E) : N.IsTreeArc e ↔ ac e = none := by
  constructor
  · intro ht
    cases he : ac e with
    | none => rfl
    | some k => exact absurd ((h.onCycle_iff e).2 ⟨k, he⟩) ht
  · exact h.tree e

/-- The colour of a node doesn't change along an arc on a cycle. -/
theorem vc_eq_of_onCycle (h : GallCover N ac vc) {e : E} (he : N.OnCycle e) : vc (N.src e) = vc (N.tgt e) := by
  obtain ⟨k, hk⟩ := (h.onCycle_iff e).1 he
  rw [(h.color e k hk).1, (h.color e k hk).2]

/-- A cycle with an arc of colour `k` has only arcs of colour `k`. -/
theorem subset_of_mem (h : GallCover N ac vc) {Q : Set E} (hQ : N.IsCycle Q) {e : E} {k : κ} (he : e ∈ Q) (hk : ac e = some k) :
    Q ⊆ {g | ac g = some k} := by
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  intro a ha
  have hconst : ∀ g, (g ∈ p ∨ g ∈ q) → vc (N.src g) = vc (N.tgt g) := fun g hg =>
    h.vc_eq_of_onCycle (by
      rcases hg with hg | hg
      · exact hc.onCycle_left hg
      · exact hc.onCycle_right hg)
  have h₁ := (hc.eq_of_forall hconst he).1
  have h₂ := (hc.eq_of_forall hconst ha).1
  have hak : N.OnCycle a := by
    rcases ha with hg | hg
    · exact hc.onCycle_left hg
    · exact hc.onCycle_right hg
  obtain ⟨l, hl⟩ := (h.onCycle_iff a).1 hak
  have h₃ := (h.color a l hl).1
  have h₄ := (h.color e k hk).1
  rw [h₂, ← h₁, h₄] at h₃
  have : k = l := by simpa using h₃
  change ac a = some k
  rw [this, hl]

theorem isBlob_color (h : GallCover N ac vc) (k : κ) : N.IsBlob {e | ac e = some k} := by
  refine ⟨_, h.cycle k, ?_⟩
  ext a
  constructor
  · intro ha
    exact ⟨_, Relation.ReflTransGen.refl, ha⟩
  · rintro ⟨P, hP, ha⟩
    have key : ∀ P, Relation.ReflTransGen N.ShareArc {e | ac e = some k} P → P ⊆ {e | ac e = some k} := by
      intro P hP
      induction hP with
      | refl => exact subset_rfl
      | tail _ hs ih =>
        obtain ⟨-, hc, g, hg, hg'⟩ := hs
        exact h.subset_of_mem hc hg' (ih hg)
    exact key P hP ha

theorem isBlob_iff (h : GallCover N ac vc) (B : Set E) : N.IsBlob B ↔ ∃ k, B = {e | ac e = some k} := by
  constructor
  · intro hB
    obtain ⟨Q, ⟨w, x, p, q, hc, rfl⟩, rfl⟩ := id hB
    have hne : ∃ e, e ∈ p ∨ e ∈ q := by
      by_contra hne
      push Not at hne
      apply hc.2.2.2.1
      rw [List.eq_nil_iff_forall_not_mem.2 fun e he => (hne e).1 he, List.eq_nil_iff_forall_not_mem.2 fun e he => (hne e).2 he]
    obtain ⟨e, he⟩ := hne
    have he' : N.OnCycle e := by
      rcases he with he | he
      · exact hc.onCycle_left he
      · exact hc.onCycle_right he
    obtain ⟨k, hk⟩ := (h.onCycle_iff e).1 he'
    exact ⟨k, hB.eq_of_inter_nonempty (h.isBlob_color k) ⟨e, ⟨_, Relation.ReflTransGen.refl, he⟩, hk⟩⟩
  · rintro ⟨k, rfl⟩
    exact h.isBlob_color k

theorem vc_eq_of_mem_blobVerts (h : GallCover N ac vc) {k : κ} {v : V} (hv : v ∈ N.blobVerts {e | ac e = some k}) : vc v = some k := by
  rcases hv with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · exact (h.color e k he).1
  · exact (h.color e k he).2

theorem mem_blobVerts_iff (h : GallCover N ac vc) {k : κ} {v : V} : v ∈ N.blobVerts {e | ac e = some k} ↔ vc v = some k := by
  refine ⟨h.vc_eq_of_mem_blobVerts, fun hv => ?_⟩
  obtain ⟨e, he, rfl | rfl⟩ := h.vert v k hv
  · exact Network.src_mem_blobVerts he
  · exact Network.tgt_mem_blobVerts he

theorem nodeDisjoint (h : GallCover N ac vc) : N.BlobsNodeDisjoint := by
  intro B B' hB hB' hne
  obtain ⟨k, rfl⟩ := (h.isBlob_iff B).1 hB
  obtain ⟨l, rfl⟩ := (h.isBlob_iff B').1 hB'
  refine Set.disjoint_left.2 fun v hv hv' => hne ?_
  have := (h.vc_eq_of_mem_blobVerts hv).symm.trans (h.vc_eq_of_mem_blobVerts hv')
  have hkl : k = l := by simpa using this
  rw [hkl]

theorem onBlob_iff (h : GallCover N ac vc) (v : V) : N.OnBlob v ↔ ∃ k, vc v = some k := by
  constructor
  · rintro ⟨B, hB, hv⟩
    obtain ⟨k, rfl⟩ := (h.isBlob_iff B).1 hB
    exact ⟨k, h.vc_eq_of_mem_blobVerts hv⟩
  · rintro ⟨k, hk⟩
    exact ⟨_, h.isBlob_color k, h.mem_blobVerts_iff.2 hk⟩

/-- Nodes of one class of `T′` have the same colour, or are equal if off the blobs. -/
theorem eq_of_toBlobNode_eq (h : GallCover N ac vc) {u v : V} (huv : N.toBlobNode u = N.toBlobNode v) :
    vc u = vc v ∧ (vc u = none → u = v) := by
  refine ⟨N.eq_of_toBlobNode_eq vc (fun _ he => h.vc_eq_of_onCycle he) huv, fun hu => ?_⟩
  have hg := N.eq_of_toBlobNode_eq (fun z => if vc z = none then some z else none) (fun e he => by
    obtain ⟨k, hk⟩ := (h.onCycle_iff e).1 he
    simp [(h.color e k hk).1, (h.color e k hk).2]) huv
  have hv : vc v = none := by
    rw [← N.eq_of_toBlobNode_eq vc (fun _ he => h.vc_eq_of_onCycle he) huv, hu]
  simpa [hu, hv] using hg

/-- Nodes of one colour are in one class of `T′`. -/
theorem toBlobNode_eq_of_vc_eq (h : GallCover N ac vc) {u v : V} {k : κ} (hu : vc u = some k) (hv : vc v = some k) :
    N.toBlobNode u = N.toBlobNode v :=
  (h.isBlob_color k).toBlobNode_eq (h.mem_blobVerts_iff.2 hu) (h.mem_blobVerts_iff.2 hv)

/-- **The network is fully decomposed**, given a colouring `sc` of the sites by the components of `G(M)`, each of diameter at most two. -/
theorem isFullyDecomposedFor₂ (h : GallCover N ac vc) {σ : Type*} {M : Finset (ι → Bool)} (sc : ι → σ)
    (hadj : ∀ i j, Incompatible M i j → sc i = sc j)
    (hadj' : ∀ i j, sc i = sc j → i = j ∨ Incompatible M i j ∨ ∃ l, Incompatible M i l ∧ Incompatible M l j)
    (hb : ∀ k, ∃ i₀ j₀, i₀ ≠ j₀ ∧ sc i₀ = sc j₀ ∧ ∀ i, ac (N.site i) = some k ↔ sc i = sc i₀)
    (hi : ∀ i, (∀ j, ¬ Incompatible M i j) → ac (N.site i) = none) : N.IsFullyDecomposedFor (incompatGraph M) := by
  have hreach : ∀ i j, (incompatGraph M).Reachable i j ↔ sc i = sc j := by
    intro i j
    constructor
    · intro hr
      rw [SimpleGraph.reachable_iff_reflTransGen] at hr
      induction hr with
      | refl => rfl
      | tail _ hadj₁ ih => exact ih.trans (hadj _ _ hadj₁)
    · intro hs
      rcases hadj' i j hs with rfl | h' | ⟨l, h₁, h₂⟩
      · exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable h'
      · exact (SimpleGraph.Adj.reachable h₁).trans (SimpleGraph.Adj.reachable h₂)
  refine ⟨?_, ?_, h.nodeDisjoint⟩
  · intro B hB
    obtain ⟨k, rfl⟩ := (h.isBlob_iff B).1 hB
    obtain ⟨i₀, j₀, hne, hs, hk⟩ := hb k
    refine ⟨(incompatGraph M).connectedComponentMk i₀, ⟨i₀, rfl, j₀, ?_, hne⟩, fun i => ?_⟩
    · exact SimpleGraph.ConnectedComponent.eq.2 ((hreach j₀ i₀).2 hs.symm)
    · rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq, hreach, ← hk]
      rfl
  · intro i hij
    exact h.tree _ (hi i hij)

/-- **The network is fully decomposed**, given a colouring `sc` of the sites by the components of `G(M)`, each of size at most two. -/
theorem isFullyDecomposedFor (h : GallCover N ac vc) {σ : Type*} {M : Finset (ι → Bool)} (sc : ι → σ)
    (hadj : ∀ i j, Incompatible M i j → sc i = sc j) (hadj' : ∀ i j, sc i = sc j → i = j ∨ Incompatible M i j)
    (hb : ∀ k, ∃ i₀ j₀, i₀ ≠ j₀ ∧ sc i₀ = sc j₀ ∧ ∀ i, ac (N.site i) = some k ↔ sc i = sc i₀)
    (hi : ∀ i, (∀ j, ¬ Incompatible M i j) → ac (N.site i) = none) : N.IsFullyDecomposedFor (incompatGraph M) :=
  h.isFullyDecomposedFor₂ sc hadj (fun i j hs => (hadj' i j hs).imp_right Or.inl) hb hi

/-- **The network is efficient.** -/
theorem isEfficient [DecidableEq κ] (h : GallCover N ac vc)
    (hl : ∀ u v, (∃ e, N.src e = u ∧ (∃ k, vc u = some k) ∧ vc (N.tgt e) ≠ vc u) → (∃ e, N.src e = v ∧ (∃ k, vc v = some k) ∧ vc (N.tgt e) ≠ vc v) →
      N.label u = N.label v → u = v)
    (hx : ∀ e f, (∃ k, vc (N.src e) = some k) → vc (N.tgt e) ≠ vc (N.src e) → N.src f = N.src e → vc (N.tgt f) ≠ vc (N.src e) → e = f) : N.IsEfficient where
  label_inj := by
    rintro B B' v v' hB hB' ⟨hv, e, he, ht⟩ ⟨hv', e', he', ht'⟩ hlab
    obtain ⟨k, rfl⟩ := (h.isBlob_iff B).1 hB
    obtain ⟨k', rfl⟩ := (h.isBlob_iff B').1 hB'
    have h₁ := h.vc_eq_of_mem_blobVerts hv
    have h₂ := h.vc_eq_of_mem_blobVerts hv'
    refine hl v v' ⟨e, he, ⟨k, h₁⟩, ?_⟩ ⟨e', he', ⟨k', h₂⟩, ?_⟩ hlab
    · rw [h₁]
      exact fun h' => ht (h.mem_blobVerts_iff.2 h')
    · rw [h₂]
      exact fun h' => ht' (h.mem_blobVerts_iff.2 h')
  exit_unique := by
    rintro B e f hB hs ht hsf htf
    obtain ⟨k, rfl⟩ := (h.isBlob_iff B).1 hB
    have h₁ := h.vc_eq_of_mem_blobVerts hs
    refine hx e f ⟨k, h₁⟩ ?_ hsf ?_
    · rw [h₁]
      exact fun h' => ht (h.mem_blobVerts_iff.2 h')
    · rw [h₁]
      exact fun h' => htf (h.mem_blobVerts_iff.2 h')

/-- The number of tree arcs, by colour. -/
theorem treeness_eq [Fintype E] [DecidableEq κ] (h : GallCover N ac vc) : N.treeness = Fintype.card {e // ac e = none} := by
  rw [Network.treeness, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight (h.isTreeArc_iff))

end GallCover

/-- A table of nodes or arcs. -/
def tbl {k n : ℕ} [NeZero k] (l : List ℕ) (i : Fin n) : Fin k := Fin.ofNat k (l.getD i.val 0)

/-- A table of the labels of nodes. -/
def bitsOf {m a : ℕ} (l : List (List ℕ)) (v : Fin a) : Fin m → Bool := ofBits (l.getD v.val [])

/-- A table of colours: `0` for no colour, and `k + 1` for the colour `k`. -/
def colourOf {k n : ℕ} [NeZero k] (l : List ℕ) (i : Fin n) : Option (Fin k) :=
  match l.getD i.val 0 with
  | 0 => none
  | c + 1 => some (Fin.ofNat k c)

namespace GallCover

variable {m a b n : ℕ} {N : Network (Fin m) (Fin a) (Fin b)} {ac : Fin b → Option (Fin n)} {vc : Fin a → Option (Fin n)}

/-- A `GallCover` from the cycles, with conditions that can be decided: a cut for each tree arc. -/
theorem of_cycle (hcycle : ∀ k, N.IsCycle {e | ac e = some k}) (cut : Fin b → Fin a → Bool)
    (hcut : ∀ e, ac e = none → cut e (N.tgt e) = true ∧ cut e (N.src e) = false ∧ (∀ f, cut e (N.src f) = true → cut e (N.tgt f) = true) ∧
      (∀ f, cut e (N.tgt f) = true → cut e (N.src f) = false → f = e) ∧ ∀ f, N.tgt f = N.tgt e → f = e)
    (hcolor : ∀ e k, ac e = some k → vc (N.src e) = some k ∧ vc (N.tgt e) = some k)
    (hvert : ∀ v k, vc v = some k → ∃ e, ac e = some k ∧ (N.src e = v ∨ N.tgt e = v)) : GallCover N ac vc where
  cycle := hcycle
  tree e he := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hcut e he
    exact N.isTreeArc_of_cut' (cut e) h₁ h₂ h₃ h₄ h₅
  color := hcolor
  vert := hvert

/-- A `GallCover` from conditions that can be decided: the four arcs of the diamond of each colour, and a cut for each tree arc. -/
theorem of_decide (e₁ e₂ f₁ f₂ : Fin n → Fin b) (cut : Fin b → Fin a → Bool)
    (hdia : ∀ k, N.src (e₁ k) = N.src (f₁ k) ∧ N.tgt (e₁ k) = N.src (e₂ k) ∧ N.tgt (f₁ k) = N.src (f₂ k) ∧ N.tgt (e₂ k) = N.tgt (f₂ k) ∧ e₂ k ≠ f₂ k ∧
      N.tgt (e₁ k) ≠ N.tgt (f₁ k) ∧ N.tgt (e₁ k) ≠ N.tgt (e₂ k) ∧ N.tgt (f₁ k) ≠ N.tgt (e₂ k) ∧ ∀ g, ac g = some k ↔ g = e₁ k ∨ g = e₂ k ∨ g = f₁ k ∨ g = f₂ k)
    (hcut : ∀ e, ac e = none → cut e (N.tgt e) = true ∧ cut e (N.src e) = false ∧ (∀ f, cut e (N.src f) = true → cut e (N.tgt f) = true) ∧
      (∀ f, cut e (N.tgt f) = true → cut e (N.src f) = false → f = e) ∧ ∀ f, N.tgt f = N.tgt e → f = e)
    (hcolor : ∀ e k, ac e = some k → vc (N.src e) = some k ∧ vc (N.tgt e) = some k)
    (hvert : ∀ v k, vc v = some k → ∃ e, ac e = some k ∧ (N.src e = v ∨ N.tgt e = v)) : GallCover N ac vc :=
  of_cycle (fun k => by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := hdia k
    have := N.isCycle_of_diamond h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
    convert this using 1
    ext g
    simp only [Set.mem_ofPred_eq, h₉, List.mem_cons, List.not_mem_nil, or_false]
    tauto) cut hcut hcolor hvert

end GallCover

/-- With at most one arc into each node, no arc has a colour. -/
theorem GallCover.of_tgt_injective {ι V E : Type*} {N : Network ι V E} (h : Function.Injective N.tgt) :
    GallCover (κ := Empty) N (fun _ => none) (fun _ => none) where
  cycle k := k.elim
  tree e _ := Network.isTreeArc_of_tgt_injective h e
  color _ k := k.elim
  vert _ k := k.elim

namespace GallCover

variable {m a b : ℕ} {N : Network (Fin m) (Fin a) (Fin b)} {κ : Type*} {ac : Fin b → Option κ} {vc : Fin a → Option κ}

/-- Every node of `T′` of degree at most two has a leaf of `N`, if each node that isn't a leaf has three tree arcs out of its class, to three other classes. -/
theorem degree_cond (h : GallCover N ac vc) (w₁ w₂ w₃ : Fin a → Fin b)
    (hw : ∀ z, (∀ e, N.src e ≠ z) ∨
      ((ac (w₁ z) = none ∧ ac (w₂ z) = none ∧ ac (w₃ z) = none) ∧
        ((N.src (w₁ z) = z ∨ (vc z ≠ none ∧ vc z = vc (N.src (w₁ z)))) ∧ (N.src (w₂ z) = z ∨ (vc z ≠ none ∧ vc z = vc (N.src (w₂ z)))) ∧
          (N.src (w₃ z) = z ∨ (vc z ≠ none ∧ vc z = vc (N.src (w₃ z))))) ∧
        ((vc (N.tgt (w₁ z)) ≠ vc (N.tgt (w₂ z)) ∨ (vc (N.tgt (w₁ z)) = none ∧ N.tgt (w₁ z) ≠ N.tgt (w₂ z))) ∧
          (vc (N.tgt (w₁ z)) ≠ vc (N.tgt (w₃ z)) ∨ (vc (N.tgt (w₁ z)) = none ∧ N.tgt (w₁ z) ≠ N.tgt (w₃ z))) ∧
          (vc (N.tgt (w₂ z)) ≠ vc (N.tgt (w₃ z)) ∨ (vc (N.tgt (w₂ z)) = none ∧ N.tgt (w₂ z) ≠ N.tgt (w₃ z)))))) :
    ∀ v, (N.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, N.IsLeaf l ∧ N.toBlobNode l = v := by
  intro v hv
  obtain ⟨z, rfl⟩ : ∃ z, N.toBlobNode z = v := Quotient.exists_rep v
  rcases hw z with hz | ⟨⟨h₁, h₂, h₃⟩, ⟨s₁, s₂, s₃⟩, d₁, d₂, d₃⟩
  · exact ⟨z, hz, rfl⟩
  · exfalso
    have hclass : ∀ e, (N.src e = z ∨ (vc z ≠ none ∧ vc z = vc (N.src e))) → N.toBlobNode (N.src e) = N.toBlobNode z := by
      intro e he
      rcases he with he | ⟨hn, he⟩
      · rw [he]
      · cases hk : vc z with
        | none => exact absurd hk hn
        | some k => exact h.toBlobNode_eq_of_vc_eq (he ▸ hk) hk
    have hadj : ∀ e, ac e = none → (N.src e = z ∨ (vc z ≠ none ∧ vc z = vc (N.src e))) →
        N.toBlobNode (N.tgt e) ∈ N.blobbedTree.neighborSet (N.toBlobNode z) := by
      intro e he hs
      have := Network.blobbedTree_adj (h.tree e he)
      rwa [hclass e hs] at this
    have hsep : ∀ {x y : Fin a}, (vc x ≠ vc y ∨ (vc x = none ∧ x ≠ y)) → N.toBlobNode x ≠ N.toBlobNode y := by
      intro x y hxy hc
      obtain ⟨h₁', h₂'⟩ := h.eq_of_toBlobNode_eq hc
      rcases hxy with hxy | ⟨hx, hne⟩
      · exact hxy h₁'
      · exact hne (h₂' hx)
    have h3 : 2 < (N.blobbedTree.neighborSet (N.toBlobNode z)).ncard :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).2 ⟨_, _, _, hadj _ h₁ s₁, hadj _ h₂ s₂, hadj _ h₃ s₃, hsep d₁, hsep d₂, hsep d₃⟩
    omega

/-- Every node of `T′` of degree at most two has a leaf of `N`, if each node that isn't a leaf has three tree arcs at its class, in either direction, to three other classes. `y` gives the other ends of the arcs. -/
theorem degree_cond₂ (h : GallCover N ac vc) (w₁ w₂ w₃ : Fin a → Fin b) (y₁ y₂ y₃ : Fin a → Fin a)
    (hw : ∀ z, (∀ e, N.src e ≠ z) ∨
      ((ac (w₁ z) = none ∧ ac (w₂ z) = none ∧ ac (w₃ z) = none) ∧
        (((N.src (w₁ z) = z ∨ (vc z ≠ none ∧ vc z = vc (N.src (w₁ z)))) ∧ N.tgt (w₁ z) = y₁ z) ∨ ((N.tgt (w₁ z) = z ∨ (vc z ≠ none ∧ vc z = vc (N.tgt (w₁ z)))) ∧ N.src (w₁ z) = y₁ z)) ∧
        (((N.src (w₂ z) = z ∨ (vc z ≠ none ∧ vc z = vc (N.src (w₂ z)))) ∧ N.tgt (w₂ z) = y₂ z) ∨ ((N.tgt (w₂ z) = z ∨ (vc z ≠ none ∧ vc z = vc (N.tgt (w₂ z)))) ∧ N.src (w₂ z) = y₂ z)) ∧
        (((N.src (w₃ z) = z ∨ (vc z ≠ none ∧ vc z = vc (N.src (w₃ z)))) ∧ N.tgt (w₃ z) = y₃ z) ∨ ((N.tgt (w₃ z) = z ∨ (vc z ≠ none ∧ vc z = vc (N.tgt (w₃ z)))) ∧ N.src (w₃ z) = y₃ z)) ∧
        ((vc (y₁ z) ≠ vc (y₂ z) ∨ (vc (y₁ z) = none ∧ y₁ z ≠ y₂ z)) ∧ (vc (y₁ z) ≠ vc (y₃ z) ∨ (vc (y₁ z) = none ∧ y₁ z ≠ y₃ z)) ∧
          (vc (y₂ z) ≠ vc (y₃ z) ∨ (vc (y₂ z) = none ∧ y₂ z ≠ y₃ z))))) :
    ∀ v, (N.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, N.IsLeaf l ∧ N.toBlobNode l = v := by
  intro v hv
  obtain ⟨z, rfl⟩ : ∃ z, N.toBlobNode z = v := Quotient.exists_rep v
  rcases hw z with hz | ⟨⟨h₁, h₂, h₃⟩, s₁, s₂, s₃, d₁, d₂, d₃⟩
  · exact ⟨z, hz, rfl⟩
  · exfalso
    have hclass : ∀ x, (x = z ∨ (vc z ≠ none ∧ vc z = vc x)) → N.toBlobNode x = N.toBlobNode z := by
      intro x he
      rcases he with he | ⟨hn, he⟩
      · rw [he]
      · cases hk : vc z with
        | none => exact absurd hk hn
        | some k => exact h.toBlobNode_eq_of_vc_eq (he ▸ hk) hk
    have hadj : ∀ e y, ac e = none → (((N.src e = z ∨ (vc z ≠ none ∧ vc z = vc (N.src e))) ∧ N.tgt e = y) ∨ ((N.tgt e = z ∨ (vc z ≠ none ∧ vc z = vc (N.tgt e))) ∧ N.src e = y)) →
        N.toBlobNode y ∈ N.blobbedTree.neighborSet (N.toBlobNode z) := by
      intro e y he hs
      have hA := Network.blobbedTree_adj (h.tree e he)
      rcases hs with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
      · rwa [hclass _ hs] at hA
      · rw [hclass _ hs] at hA
        exact hA.symm
    have hsep : ∀ {x y : Fin a}, (vc x ≠ vc y ∨ (vc x = none ∧ x ≠ y)) → N.toBlobNode x ≠ N.toBlobNode y := by
      intro x y hxy hc
      obtain ⟨h₁', h₂'⟩ := h.eq_of_toBlobNode_eq hc
      rcases hxy with hxy | ⟨hx, hne⟩
      · exact hxy h₁'
      · exact hne (h₂' hx)
    have h3 : 2 < (N.blobbedTree.neighborSet (N.toBlobNode z)).ncard :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).2 ⟨_, _, _, hadj _ _ h₁ s₁, hadj _ _ h₂ s₂, hadj _ _ h₃ s₃, hsep d₁, hsep d₂, hsep d₃⟩
    omega

end GallCover

end Gusfield2007
