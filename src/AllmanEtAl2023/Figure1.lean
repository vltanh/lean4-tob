module

public import AllmanEtAl2023.Figures

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Figure 1, and the claims about it

The caption of Figure 1 (the PMC manuscript): "A species network `𝒩⁺`, with edge lengths in coalescent units. Red indicates hybrid nodes and hybrid edges. The lowest stable ancestor (LSA) of the network is `v`. This network has 6 non-trivial blobs (a 5-blob, two 3-blobs, and three 2-blobs), and a single trivial 3-blob." And Section 2: "in Fig. 1L, the child edges of `v` are both tree edges and non-cut, while the parent edge of `v` is tree and cut."

The network was read from the panel L of the figure, in the PMC page's image. It has 51 nodes and 69 edges, too many to compute its blobs quickly with `FigureCheck.reachSet`. So here the blobs are given as a colouring `col`, and checked by certificates, for each edge (`BlobCert`):

* an edge joining two colours is a cut edge: a set of nodes that only it crosses (`isBridge_of_side`);
* an edge inside a colour isn't: a short walk between its ends inside the colour, without it (`not_isBridge_of_mem_iterate`);
* each node is joined inside its colour to the node that names it.

From these, `blobOf` is the colouring (`BlobCert.blobOf_eq_iff`), and `BlobCert.isTrivialBlob_iff`, `BlobCert.blobDegree_blobOf`, `BlobCert.ncard_blobs` compute what the caption says.

Also here: the middle panel's blobs and the right panel's `T_rd(𝒩⁻)` (`fig1_panelR`); Figure 2R, "a single 2-blob in a non-binary network, formed from two 2-cycles sharing a single node" (`fig2R_blob`); that the induced network on a B-quartet "can even be a tree" (`fig3_induced_tree`); and examples for "those of degree 2 or 3 may correspond to trivial or non-trivial blobs" (`fig1_degree_examples`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph
open scoped Classical

namespace AllmanEtAl2023.FigureCheck

open InPassing

/-! ### Certificates for the blobs of a numbered graph -/

section Cert

variable {n m : ℕ} {src tgt : Fin m → Fin n}

/-- A node reached in `j` steps of `stepSet` is joined by a walk. -/
theorem walks_of_mem_iterate {F : Finset (Fin m)} (j : ℕ) {u w : Fin n} (h : w ∈ (stepSet src tgt F)^[j] {u}) :
    (graphOf src tgt).Walks (F : Set (Fin m)) u w := by
  induction j generalizing w with
  | zero =>
    rw [Finset.mem_singleton.mp h]
    exact .refl
  | succ j ih =>
    rw [Function.iterate_succ_apply'] at h
    rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact ih h
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨he₁, he₂⟩ := Finset.mem_filter.mp he
        exact (ih he₂).tail ⟨e, he₁, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨he₁, he₂⟩ := Finset.mem_filter.mp he
      exact (ih he₂).tail ⟨e, he₁, Or.inr ⟨rfl, rfl⟩⟩

/-- An edge whose ends are joined without it isn't a cut edge. -/
theorem not_isBridge_of_mem_iterate {F : Finset (Fin m)} {e : Fin m} (he : e ∉ F) (j : ℕ) (h : tgt e ∈ (stepSet src tgt F)^[j] {src e}) :
    ¬ (graphOf src tgt).underlying.IsBridge e := by
  rw [isBridge_iff_not_walks_delete, not_not]
  refine walks_mono (fun f hf => ?_) (walks_of_mem_iterate j h)
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro rfl
  exact he (Finset.mem_coe.mp hf)

/-- An edge is a cut edge if it is the only one crossing a set of nodes. -/
theorem isBridge_of_side {e : Fin m} {S : Finset (Fin n)} (h : ∀ f, ((src f ∈ S ∧ tgt f ∉ S) ∨ (tgt f ∈ S ∧ src f ∉ S)) ↔ f = e) :
    (graphOf src tgt).underlying.IsBridge e :=
  ((graphOf src tgt).isBridge_iff e).2 ⟨(S : Set (Fin n)), fun f => by simpa [DirectedMultigraph.Crosses] using h f⟩

/-- The edges inside the colour of `v`. -/
def monoEdges (src tgt : Fin m → Fin n) (col : Fin n → Fin n) (v : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun f => col (src f) = col v ∧ col (tgt f) = col v

/-- **The blobs from a colouring**: if the cut edges are the edges between colours, and each node is in the blob of the node that names its colour, the blobs are the colours. -/
theorem blobOf_eq_iff_of_col {G : DirectedMultigraph (Fin n) (Fin m)} {col : Fin n → Fin n} (hbr : ∀ {e}, G.underlying.IsBridge e ↔ col (G.source e) ≠ col (G.target e))
    (hrep : ∀ v, SameBlobIn G Set.univ v (col v)) {u w : Fin n} : blobOf G u = blobOf G w ↔ col u = col w := by
  have hnc : ∀ {f : Fin m}, f ∈ nonCutsIn G Set.univ → col (G.source f) = col (G.target f) := by
    intro f hf
    by_contra hc
    exact hf.2 (isCutIn_univ_iff.2 (hbr.2 hc))
  rw [← sameBlobIn_univ_iff]
  constructor
  · intro hw
    induction hw with
    | refl => rfl
    | tail _ hstep ih =>
      obtain ⟨f, hf, (⟨hs, ht⟩ | ⟨hs, ht⟩)⟩ := hstep
      · rw [ih, ← hs, ← ht]
        exact hnc hf
      · rw [ih, ← hs, ← ht]
        exact (hnc hf).symm
  · intro hc
    have h1 := hrep u
    have h2 := hrep w
    rw [hc] at h1
    exact h1.trans (G.walks_symm h2)

/-- **A certificate for the blobs of a graph**: a colouring of the nodes, with the sets that the edges between colours alone cross, in at most `K` steps inside each colour. -/
structure BlobCert (src tgt : Fin m → Fin n) (col : Fin n → Fin n) (side : Fin m → Finset (Fin n)) (K : ℕ) : Prop where
  /-- An edge between two colours is the only one crossing its set. -/
  cross : ∀ e, col (src e) ≠ col (tgt e) → ∀ f, ((src f ∈ side e ∧ tgt f ∉ side e) ∨ (tgt f ∈ side e ∧ src f ∉ side e)) ↔ f = e
  /-- An edge inside a colour has its ends joined inside the colour without it. -/
  inner : ∀ e, col (src e) = col (tgt e) → tgt e ∈ (stepSet src tgt ((monoEdges src tgt col (src e)).erase e))^[K] {src e}
  /-- A node is joined inside its colour to the node that names the colour. -/
  conn : ∀ v, col v ∈ (stepSet src tgt (monoEdges src tgt col v))^[K] {v}

namespace BlobCert

variable {col : Fin n → Fin n} {side : Fin m → Finset (Fin n)} {K : ℕ}

theorem isBridge_iff (h : BlobCert src tgt col side K) {e : Fin m} : (graphOf src tgt).underlying.IsBridge e ↔ col (src e) ≠ col (tgt e) := by
  constructor
  · intro hb hc
    exact not_isBridge_of_mem_iterate (Finset.notMem_erase e _) K (h.inner e hc) hb
  · exact fun hc => isBridge_of_side (h.cross e hc)

/-- **The blobs are the colours.** -/
theorem blobOf_eq_iff (h : BlobCert src tgt col side K) {u w : Fin n} : blobOf (graphOf src tgt) u = blobOf (graphOf src tgt) w ↔ col u = col w := by
  refine blobOf_eq_iff_of_col (fun {e} => h.isBridge_iff) fun v => ?_
  refine walks_mono (fun f hf => ?_) (walks_of_mem_iterate K (h.conn v))
  obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
  refine ⟨Set.mem_univ f, fun hc => ?_⟩
  exact h.isBridge_iff.1 (isCutIn_univ_iff.1 hc) (h1.trans h2.symm)

/-- A blob is trivial if its colour has one node. -/
theorem isTrivialBlob_iff (h : BlobCert src tgt col side K) {v : Fin n} :
    IsTrivialBlob (graphOf src tgt) (blobOf (graphOf src tgt) v) ↔ ∀ w, col w = col v → w = v := by
  constructor
  · rintro ⟨x, hx⟩ w hw
    have h1 : w ∈ blobNodes (graphOf src tgt) (blobOf (graphOf src tgt) v) := h.blobOf_eq_iff.2 hw
    have h2 : v ∈ blobNodes (graphOf src tgt) (blobOf (graphOf src tgt) v) := rfl
    rw [hx] at h1 h2
    exact h1.trans h2.symm
  · intro hall
    refine ⟨v, Set.eq_singleton_iff_unique_mem.2 ⟨rfl, fun w hw => hall w (h.blobOf_eq_iff.1 hw)⟩⟩

/-- The cut edges at a blob. -/
def incidentCol (src tgt : Fin m → Fin n) (col : Fin n → Fin n) (v : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun e => col (src e) ≠ col (tgt e) ∧ (col (src e) = col v ∨ col (tgt e) = col v)

theorem incidentCutEdges_eq (h : BlobCert src tgt col side K) (v : Fin n) :
    incidentCutEdges (graphOf src tgt) (blobOf (graphOf src tgt) v) = (incidentCol src tgt col v : Finset (Fin m)) := by
  ext e
  simp only [incidentCutEdges, IsIncidentToBlob, Set.mem_ofPred_eq, h.isBridge_iff, h.blobOf_eq_iff, incidentCol, Finset.coe_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, (⟨h1, -⟩ | ⟨h1, -⟩)⟩
    · exact ⟨hne, Or.inl h1⟩
    · exact ⟨hne, Or.inr h1⟩
  · rintro ⟨hne, (h1 | h1)⟩
    · exact ⟨hne, Or.inl ⟨h1, fun h2 => hne (h1.trans h2.symm)⟩⟩
    · exact ⟨hne, Or.inr ⟨h1, fun h2 => hne (h2.trans h1.symm)⟩⟩

theorem cutDegree_blobOf (h : BlobCert src tgt col side K) (v : Fin n) :
    cutDegree (graphOf src tgt) (blobOf (graphOf src tgt) v) = (incidentCol src tgt col v).card := by
  rw [cutDegree, h.incidentCutEdges_eq, Set.ncard_coe_finset]

/-- The degree of a blob, with the root `r`. -/
theorem blobDegree_blobOf {k : ℕ} {r : Fin n} {ℓ : Fin k → Fin n} (h : BlobCert src tgt col side K) (v : Fin n) :
    blobDegree (finNetwork src tgt r ℓ) (blobOf (finNetwork src tgt r ℓ).graph v) =
      if col r = col v then (incidentCol src tgt col v).card + 1 else (incidentCol src tgt col v).card := by
  unfold blobDegree
  have hd : cutDegree (finNetwork src tgt r ℓ).graph (blobOf (finNetwork src tgt r ℓ).graph v) = (incidentCol src tgt col v).card := h.cutDegree_blobOf v
  rw [hd]
  have hb : blobOf (finNetwork src tgt r ℓ).graph (finNetwork src tgt r ℓ).root = blobOf (finNetwork src tgt r ℓ).graph v ↔ col r = col v := h.blobOf_eq_iff
  simp only [hb]

/-- **Counting blobs**, by their colours. `reps` has one node of each colour. -/
theorem ncard_blobs (h : BlobCert src tgt col side K) {reps : Finset (Fin n)} (hreps : ∀ v, col v ∈ reps) (hfix : ∀ v ∈ reps, col v = v)
    (P : (graphOf src tgt).BlobVertex → Prop) (P' : Fin n → Prop) [DecidablePred P'] (hP : ∀ v, P (blobOf (graphOf src tgt) v) ↔ P' v) :
    {b | P b}.ncard = (reps.filter P').card := by
  have hset : {b | P b} = (fun v => blobOf (graphOf src tgt) v) '' ((reps.filter P' : Finset (Fin n)) : Set (Fin n)) := by
    ext b
    obtain ⟨v, rfl⟩ := Quotient.exists_rep b
    change P (blobOf (graphOf src tgt) v) ↔ _
    constructor
    · intro hv
      have hc : blobOf (graphOf src tgt) (col v) = blobOf (graphOf src tgt) v := h.blobOf_eq_iff.2 (hfix _ (hreps v))
      refine ⟨col v, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hreps v, (hP _).1 ?_⟩), hc⟩
      rw [hc]
      exact hv
    · rintro ⟨w, hw, hwv⟩
      have hw' := (hP w).2 (Finset.mem_filter.1 (Finset.mem_coe.1 hw)).2
      change blobOf (graphOf src tgt) w = blobOf (graphOf src tgt) v at hwv
      rwa [hwv] at hw'
  rw [hset, Set.InjOn.ncard_image, Set.ncard_coe_finset]
  intro u hu w hw huw
  have h1 := h.blobOf_eq_iff.1 huw
  rwa [hfix u (Finset.mem_filter.1 (Finset.mem_coe.1 hu)).1, hfix w (Finset.mem_filter.1 (Finset.mem_coe.1 hw)).1] at h1

end BlobCert

end Cert

/-! ### The LSA of a numbered network -/

section LSA

variable {n m k : ℕ} {src tgt : Fin m → Fin n} {r : Fin n} {ℓ : Fin k → Fin n}

/-- A directed path, as a list of nodes. -/
theorem hasPathAvoiding_of_chain {x : Fin n} {P : List (Fin n)} (hP : List.IsChain (fun a b => ∃ e, src e = a ∧ tgt e = b) (x :: P)) {w : Fin n} (hw : w ∉ x :: P) :
    Relation.ReflTransGen (fun a b => (graphOf src tgt).Adj a b ∧ a ≠ w ∧ b ≠ w) x ((x :: P).getLast (List.cons_ne_nil _ _)) := by
  induction P generalizing x with
  | nil => exact .refl
  | cons y P ih =>
    have hc := List.isChain_cons_cons.1 hP
    have hnw := not_or.1 (List.mem_cons.not.1 hw)
    have hr := ih hc.2 hnw.2
    rw [List.getLast_cons (List.cons_ne_nil _ _)]
    refine Relation.ReflTransGen.head ⟨hc.1, ?_, ?_⟩ hr
    · exact hnw.1 ∘ Eq.symm
    · exact fun h => hnw.2 (h ▸ List.mem_cons_self)

/-- **The LSA, from two paths**: if `v` is on every path from the root to the taxa, by the set `S` that is entered only at `v`, and two paths from the root to taxa have in common only nodes above `v` or `v`, then `v` is the LSA. -/
theorem isLSA_of_paths {v : Fin n} {S : Finset (Fin n)} (hrS : r ∉ S) (hS : ∀ e, src e ∉ S → tgt e ∈ S → tgt e = v) (hleaf : ∀ x, ℓ x ∈ S)
    {P₁ P₂ : List (Fin n)} {x₁ x₂ : Fin k} (h₁ : List.IsChain (fun a b => ∃ e, src e = a ∧ tgt e = b) (r :: P₁)) (h₂ : List.IsChain (fun a b => ∃ e, src e = a ∧ tgt e = b) (r :: P₂))
    (hl₁ : (r :: P₁).getLast (List.cons_ne_nil _ _) = ℓ x₁) (hl₂ : (r :: P₂).getLast (List.cons_ne_nil _ _) = ℓ x₂)
    (habove : ∀ u, u ∈ r :: P₁ → u ∈ r :: P₂ → u ≠ v → (graphOf src tgt).Reaches u v) :
    IsLSA (finNetwork src tgt r ℓ) (Set.range (finNetwork src tgt r ℓ).leaf) v := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ ⟨hrv, hxv, hw⟩
    -- nodes on a path avoiding `v` from the root are out of `S`
    have key : ∀ y, Relation.ReflTransGen (fun a b => (finNetwork src tgt r ℓ).graph.Adj a b ∧ a ≠ v ∧ b ≠ v) r y → y ∉ S := by
      intro y hy
      induction hy with
      | refl => exact hrS
      | tail _ hstep ih =>
        obtain ⟨⟨e, hs, ht⟩, -, hne⟩ := hstep
        intro hmem
        have hs' : src e = _ := hs
        have ht' : tgt e = _ := ht
        exact hne ((ht'.symm.trans (hS e (hs' ▸ ih) (ht' ▸ hmem))))
    exact key _ hw (hleaf x)
  · intro u hu huv
    have onP : ∀ {P : List (Fin n)} {x : Fin k}, List.IsChain (fun a b => ∃ e, src e = a ∧ tgt e = b) (r :: P) →
        (r :: P).getLast (List.cons_ne_nil _ _) = ℓ x → u ∈ r :: P := by
      intro P x hc hl
      by_contra hno
      have hr := hasPathAvoiding_of_chain hc hno
      rw [hl] at hr
      refine hu (ℓ x) ⟨x, rfl⟩ ⟨fun h => hno (h ▸ List.mem_cons_self), fun h => hno ?_, hr⟩
      have h' : ℓ x = u := h
      rw [← h', ← hl]
      exact List.getLast_mem _
    exact habove u (onP h₁ hl₁) (onP h₂ hl₂) huv

end LSA

end AllmanEtAl2023.FigureCheck

namespace AllmanEtAl2023.Figures

open InPassing FigureCheck

/-! ### Figure 1 -/

section Fig1

/-- The sources of the edges of Figure 1L. The taxa `a, …, g` are `0, …, 6`. The nodes are numbered from the taxa up: the root is `50`, its hybrid child `49`, then the 2-blob `45–48`, then `v = 44`. -/
def src1 : Fin 69 → Fin 51 := ![50, 50, 49, 48, 48, 47, 47, 46, 45, 44, 44, 38, 38, 26, 26, 35, 35, 43, 43, 41, 41, 42, 42, 36, 36, 40, 40, 39, 34, 31, 32, 27, 22, 21, 17, 13, 13, 9, 37, 37, 33, 33, 28, 28, 23, 23, 10, 10, 19, 19, 30, 30, 24, 24, 29, 29, 25, 25, 18, 18, 14, 14, 7, 15, 12, 20, 16, 11, 8]

/-- The targets of the edges of Figure 1L. -/
def tgt1 : Fin 69 → Fin 51 := ![49, 49, 48, 46, 47, 46, 45, 45, 44, 38, 43, 26, 35, 21, 21, 32, 22, 41, 42, 39, 36, 39, 40, 32, 31, 34, 37, 34, 31, 27, 27, 22, 17, 17, 13, 9, 9, 0, 33, 29, 28, 30, 15, 23, 10, 19, 1, 2, 3, 12, 24, 20, 15, 16, 20, 25, 11, 18, 7, 14, 7, 6, 5, 12, 8, 16, 11, 8, 4]

/-- The taxa of Figure 1. -/
def leaf1 : Fin 7 → Fin 51 := Fin.castLE (by norm_num)

/-- **The network of Figure 1L.** -/
def fig1 : RootedNetwork (Fin 51) (Fin 69) (Fin 7) := finNetwork src1 tgt1 50 leaf1

/-- The blobs of Figure 1L, each named by its highest node: `50`, `48`, `44`, `37`, `18`, `13` are the six non-trivial ones. -/
def col1 : Fin 51 → Fin 51 := ![0, 1, 2, 3, 4, 5, 6, 18, 37, 13, 10, 37, 37, 13, 18, 37, 37, 44, 18, 37, 37, 44, 44, 37, 37, 37, 44, 44, 37, 37, 37, 44, 44, 37, 44, 44, 44, 37, 44, 44, 44, 44, 44, 44, 44, 48, 48, 48, 48, 50, 50]

/-- The sets that the cut edges of Figure 1L alone cross. -/
def side1 (e : Fin 69) : Finset (Fin 51) :=
  if e = 2 then Finset.univ.filter fun v => v.1 ≤ 48
  else if e = 8 then Finset.univ.filter fun v => v.1 ≤ 44
  else if e = 26 then {1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 18, 19, 20, 23, 24, 25, 28, 29, 30, 33, 37}
  else if e = 34 then {0, 9, 13}
  else if e = 37 then {0}
  else if e = 44 then {1, 2, 10}
  else if e = 46 then {1}
  else if e = 47 then {2}
  else if e = 48 then {3}
  else if e = 57 then {5, 6, 7, 14, 18}
  else if e = 61 then {6}
  else if e = 62 then {5}
  else if e = 68 then {4}
  else ∅

theorem blobCert1 : BlobCert src1 tgt1 col1 side1 6 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The nodes that name the blobs. -/
def reps1 : Finset (Fin 51) := {0, 1, 2, 3, 4, 5, 6, 10, 13, 18, 37, 44, 48, 50}

theorem isBinaryNetwork_fig1 : IsBinaryNetwork fig1 :=
  isBinaryNetwork_finNetwork (by decide +kernel) (by decide +kernel) (by decide +kernel) (Fin.castLE_injective _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fig1_blobDegree (v : Fin 51) :
    blobDegree fig1 (blobOf fig1.graph v) = if col1 50 = col1 v then (BlobCert.incidentCol src1 tgt1 col1 v).card + 1 else (BlobCert.incidentCol src1 tgt1 col1 v).card :=
  blobCert1.blobDegree_blobOf v

theorem fig1_isTrivialBlob_iff (v : Fin 51) : IsTrivialBlob fig1.graph (blobOf fig1.graph v) ↔ ∀ w, col1 w = col1 v → w = v :=
  blobCert1.isTrivialBlob_iff

/-- **"This network has 6 non-trivial blobs (a 5-blob, two 3-blobs, and three 2-blobs), and a single trivial 3-blob"** (`a:claim:fig1-blobs`, the caption of Figure 1). The trivial blobs of degree 1 are the seven taxa. -/
theorem fig1_blobs :
    {b | ¬ IsTrivialBlob fig1.graph b}.ncard = 6 ∧
      {b | ¬ IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 5}.ncard = 1 ∧
      {b | ¬ IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 3}.ncard = 2 ∧
      {b | ¬ IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 2}.ncard = 3 ∧
      {b | IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 3}.ncard = 1 ∧
      {b | IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 1}.ncard = 7 := by
  have hreps : ∀ v, col1 v ∈ reps1 := by decide +kernel
  have hfix : ∀ v ∈ reps1, col1 v = v := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show {b | ¬ IsTrivialBlob fig1.graph b}.ncard = _ from
      blobCert1.ncard_blobs hreps hfix (fun b => ¬ IsTrivialBlob fig1.graph b) (fun v => ¬ ∀ w, col1 w = col1 v → w = v) fun v => not_congr (fig1_isTrivialBlob_iff v)]
    decide +kernel
  · rw [show {b | ¬ IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 5}.ncard = _ from
      blobCert1.ncard_blobs hreps hfix (fun b => ¬ IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 5)
        (fun v => (¬ ∀ w, col1 w = col1 v → w = v) ∧ (if col1 50 = col1 v then (BlobCert.incidentCol src1 tgt1 col1 v).card + 1 else (BlobCert.incidentCol src1 tgt1 col1 v).card) = 5)
        fun v => and_congr (not_congr (fig1_isTrivialBlob_iff v)) (by rw [← fig1_blobDegree v]; rfl)]
    decide +kernel
  · rw [show {b | ¬ IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 3}.ncard = _ from
      blobCert1.ncard_blobs hreps hfix (fun b => ¬ IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 3)
        (fun v => (¬ ∀ w, col1 w = col1 v → w = v) ∧ (if col1 50 = col1 v then (BlobCert.incidentCol src1 tgt1 col1 v).card + 1 else (BlobCert.incidentCol src1 tgt1 col1 v).card) = 3)
        fun v => and_congr (not_congr (fig1_isTrivialBlob_iff v)) (by rw [← fig1_blobDegree v]; rfl)]
    decide +kernel
  · rw [show {b | ¬ IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 2}.ncard = _ from
      blobCert1.ncard_blobs hreps hfix (fun b => ¬ IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 2)
        (fun v => (¬ ∀ w, col1 w = col1 v → w = v) ∧ (if col1 50 = col1 v then (BlobCert.incidentCol src1 tgt1 col1 v).card + 1 else (BlobCert.incidentCol src1 tgt1 col1 v).card) = 2)
        fun v => and_congr (not_congr (fig1_isTrivialBlob_iff v)) (by rw [← fig1_blobDegree v]; rfl)]
    decide +kernel
  · rw [show {b | IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 3}.ncard = _ from
      blobCert1.ncard_blobs hreps hfix (fun b => IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 3)
        (fun v => (∀ w, col1 w = col1 v → w = v) ∧ (if col1 50 = col1 v then (BlobCert.incidentCol src1 tgt1 col1 v).card + 1 else (BlobCert.incidentCol src1 tgt1 col1 v).card) = 3)
        fun v => and_congr (fig1_isTrivialBlob_iff v) (by rw [← fig1_blobDegree v]; rfl)]
    decide +kernel
  · rw [show {b | IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 1}.ncard = _ from
      blobCert1.ncard_blobs hreps hfix (fun b => IsTrivialBlob fig1.graph b ∧ blobDegree fig1 b = 1)
        (fun v => (∀ w, col1 w = col1 v → w = v) ∧ (if col1 50 = col1 v then (BlobCert.incidentCol src1 tgt1 col1 v).card + 1 else (BlobCert.incidentCol src1 tgt1 col1 v).card) = 1)
        fun v => and_congr (fig1_isTrivialBlob_iff v) (by rw [← fig1_blobDegree v]; rfl)]
    decide +kernel

theorem nontrivial_fin7 : Nontrivial (Fin 7) := inferInstance

/-- **"The lowest stable ancestor (LSA) of the network is `v`"** (`a:claim:fig1-lsa`, the caption of Figure 1): the node `44`. It is entered only by the edge from `45`, and the paths to `a` through its left child and to `b` through its right child have in common only nodes above it. -/
theorem fig1_lsa : lsaNode isBinaryNetwork_fig1 nontrivial_fin7 = 44 := by
  have hP := isBinaryNetwork_fig1.isPhylogenetic
  have hL : IsLSA fig1 (Set.range fig1.leaf) 44 := by
    refine isLSA_of_paths (S := Finset.univ.filter fun v => v.1 ≤ 44) (P₁ := [49, 48, 46, 45, 44, 38, 26, 21, 17, 13, 9, 0]) (P₂ := [49, 48, 46, 45, 44, 43, 42, 40, 37, 33, 28, 23, 10, 1])
      (x₁ := 0) (x₂ := 1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl ?_
    have hstep : ∀ a b : Fin 51, (∃ e, src1 e = a ∧ tgt1 e = b) → (graphOf src1 tgt1).Adj a b := fun _ _ h => h
    have h45 : (graphOf src1 tgt1).Reaches 45 44 := .single (hstep 45 44 (by decide +kernel))
    have h46 : (graphOf src1 tgt1).Reaches 46 44 := .head (hstep 46 45 (by decide +kernel)) h45
    have h48 : (graphOf src1 tgt1).Reaches 48 44 := .head (hstep 48 46 (by decide +kernel)) h46
    have h49 : (graphOf src1 tgt1).Reaches 49 44 := .head (hstep 49 48 (by decide +kernel)) h48
    have h50 : (graphOf src1 tgt1).Reaches 50 44 := .head (hstep 50 49 (by decide +kernel)) h49
    have hmem : ∀ u : Fin 51, u ∈ ([50, 49, 48, 46, 45, 44, 38, 26, 21, 17, 13, 9, 0] : List (Fin 51)) → u ∈ ([50, 49, 48, 46, 45, 44, 43, 42, 40, 37, 33, 28, 23, 10, 1] : List (Fin 51)) →
        u = 50 ∨ u = 49 ∨ u = 48 ∨ u = 46 ∨ u = 45 ∨ u = 44 := by decide +kernel
    intro u h₁ h₂ hne
    rcases hmem u h₁ h₂ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h50
    · exact h49
    · exact h48
    · exact h46
    · exact h45
    · exact absurd rfl hne
  exact ((existsUnique_isLSA (Z := Set.range fig1.leaf) hP ⟨fig1.leaf 0, 0, rfl⟩).unique (isLSA_lsaNode isBinaryNetwork_fig1 nontrivial_fin7) hL)

/-- **"The child edges of `v` are both tree edges and non-cut, while the parent edge of `v` is tree and cut"** (`a:claim:fig1-edges`, Section 2): the edges `9`, `10` and `8`. -/
theorem fig1_edges_at_v :
    ({e | fig1.graph.source e = 44} : Set (Fin 69)) = {9, 10} ∧ ({e | fig1.graph.target e = 44} : Set (Fin 69)) = {8} ∧
      fig1.IsTreeArc 9 ∧ fig1.IsTreeArc 10 ∧ fig1.IsTreeArc 8 ∧
      ¬ fig1.graph.underlying.IsBridge 9 ∧ ¬ fig1.graph.underlying.IsBridge 10 ∧ fig1.graph.underlying.IsBridge 8 := by
  have hbr : ∀ e : Fin 69, fig1.graph.underlying.IsBridge e ↔ col1 (src1 e) ≠ col1 (tgt1 e) := fun e => blobCert1.isBridge_iff
  have htree : ∀ e : Fin 69, (Finset.univ.filter fun f => tgt1 f = tgt1 e).card = 1 → fig1.IsTreeArc e := by
    intro e he
    have h := indegree_finNetwork (src := src1) (tgt := tgt1) (r := 50) (ℓ := leaf1) (tgt1 e)
    change fig1.graph.indegree (fig1.graph.target e) = 1
    exact h.trans he
  refine ⟨?_, ?_, htree _ (by decide +kernel), htree _ (by decide +kernel), htree _ (by decide +kernel), ?_, ?_, ?_⟩
  · ext e
    have : src1 e = 44 ↔ e = 9 ∨ e = 10 := by
      revert e
      decide +kernel
    exact this
  · ext e
    have : tgt1 e = 44 ↔ e = 8 := by
      revert e
      decide +kernel
    exact this
  · rw [hbr, not_not]
    decide +kernel
  · rw [hbr, not_not]
    decide +kernel
  · rw [hbr]
    decide +kernel

/-- **The panel R of Figure 1, the reduced unrooted tree of blobs**: `{b, c}` and `{f, g}` are sides of cut edges, and `a`, `b`, `d`, `e`, `f` are around one blob, the 5-blob, so the tree of blobs has the 5-multifurcation of the panel. That the 3-blob of the LSA leaves no node is the general `BlobStructure.not_liesIn_of_three`. -/
theorem fig1_panelR :
    fig1.HasCutSplit (({1, 2} : Finset (Fin 7)) : Set (Fin 7)) ∧ fig1.HasCutSplit (({5, 6} : Finset (Fin 7)) : Set (Fin 7)) ∧
      IsDeterminedBy fig1.graph fig1.leaf (blobOf fig1.graph 37) {0, 1, 3, 4, 5} ∧ blobDegree fig1 (blobOf fig1.graph 37) = 5 := by
  refine ⟨⟨44, ((side1 44 : Finset (Fin 51)) : Set (Fin 51)), fun f => ?_, ?_⟩, ⟨57, ((side1 57 : Finset (Fin 51)) : Set (Fin 51)), fun f => ?_, ?_⟩, ?_, ?_⟩
  · have h : ∀ f : Fin 69, ((src1 f ∈ side1 44 ∧ tgt1 f ∉ side1 44) ∨ (tgt1 f ∈ side1 44 ∧ src1 f ∉ side1 44)) ↔ f = 44 := by decide +kernel
    simpa [DirectedMultigraph.Crosses, fig1, finNetwork] using h f
  · have h : ∀ x : Fin 7, leaf1 x ∈ side1 44 ↔ x ∈ ({1, 2} : Finset (Fin 7)) := by decide +kernel
    ext x
    simpa [fig1, finNetwork] using h x
  · have h : ∀ f : Fin 69, ((src1 f ∈ side1 57 ∧ tgt1 f ∉ side1 57) ∨ (tgt1 f ∈ side1 57 ∧ src1 f ∉ side1 57)) ↔ f = 57 := by decide +kernel
    simpa [DirectedMultigraph.Crosses, fig1, finNetwork] using h f
  · have h : ∀ x : Fin 7, leaf1 x ∈ side1 57 ↔ x ∈ ({5, 6} : Finset (Fin 7)) := by decide +kernel
    ext x
    simpa [fig1, finNetwork] using h x
  · refine ⟨by decide, fun s hs t ht hst hw => ?_⟩
    -- the taxa are in different components of what remains
    have hcol : ∀ s ∈ ({0, 1, 3, 4, 5} : Finset (Fin 7)), ∀ t ∈ ({0, 1, 3, 4, 5} : Finset (Fin 7)), s ≠ t →
        ∃ e, e ∈ BlobCert.incidentCol src1 tgt1 col1 37 ∧ (leaf1 s ∈ side1 e ∧ leaf1 t ∉ side1 e ∨ leaf1 t ∈ side1 e ∧ leaf1 s ∉ side1 e) ∧ ∀ f, ((src1 f ∈ side1 e ∧ tgt1 f ∉ side1 e) ∨ (tgt1 f ∈ side1 e ∧ src1 f ∉ side1 e)) ↔ f = e := by
      decide +kernel
    obtain ⟨e, he, hsep, hcross⟩ := hcol s hs t ht hst
    have hinc : e ∈ incidentCutEdges fig1.graph (blobOf fig1.graph 37) := by
      have := blobCert1.incidentCutEdges_eq 37
      rw [show incidentCutEdges fig1.graph (blobOf fig1.graph 37) = _ from this]
      exact Finset.mem_coe.2 he
    have hsame := fig1.graph.mem_iff_mem_of_walks (F := (incidentCutEdges fig1.graph (blobOf fig1.graph 37))ᶜ) (S := ((side1 e : Finset (Fin 51)) : Set (Fin 51))) (fun f hf hc => hf (by
      have : f = e := (hcross f).1 (by simpa [DirectedMultigraph.Crosses, fig1, finNetwork] using hc)
      exact this ▸ hinc)) hw
    have hsame' : leaf1 s ∈ side1 e ↔ leaf1 t ∈ side1 e := by simpa [fig1, finNetwork] using hsame
    rcases hsep with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (hsame'.1 h1)
    · exact h2 (hsame'.2 h1)
  · rw [show blobDegree fig1 (blobOf fig1.graph 37) = _ from fig1_blobDegree 37]
    decide +kernel

end Fig1

/-! ### Figure 2R -/

section Fig2R

/-- The sources of the edges of a rooted network with the blob of Figure 2R. The taxa are `0`, `1`, the bottom hybrid node `2`, the node shared by the two 2-cycles `3`, their top `4`, the root `5`. -/
def src2R : Fin 7 → Fin 6 := ![5, 5, 4, 4, 3, 3, 2]

/-- The targets of the edges of the network of Figure 2R. -/
def tgt2R : Fin 7 → Fin 6 := ![4, 1, 3, 3, 2, 2, 0]

/-- **The network of Figure 2R**, with a root above the blob. -/
def fig2R : RootedNetwork (Fin 6) (Fin 7) (Fin 2) := finNetwork src2R tgt2R 5 (Fin.castLE (by norm_num))

/-- **"A single 2-blob in a non-binary network, formed from two 2-cycles sharing a single node"** (`a:claim:fig2R`, the caption of Figure 2): the node `3` has degree 4, the 2-cycles `{2, 3}` and `{4, 5}` have no edge in common, and their nodes are in one blob, of degree 2. -/
theorem fig2R_blob :
    (Finset.univ.filter fun e => src2R e = 3 ∨ tgt2R e = 3).card = 4 ∧
      blobOf fig2R.graph 2 = blobOf fig2R.graph 3 ∧ blobOf fig2R.graph 3 = blobOf fig2R.graph 4 ∧ blobDegree fig2R (blobOf fig2R.graph 3) = 2 := by
  refine ⟨by decide +kernel, ?_, ?_, ?_⟩
  · have h : (3 : Fin 6) ∈ FigureCheck.blobSet src2R tgt2R Finset.univ 2 := by decide +kernel
    have h' := sameBlobIn_iff.2 h
    rw [Finset.coe_univ] at h'
    exact sameBlobIn_univ_iff.1 h'
  · have h : (4 : Fin 6) ∈ FigureCheck.blobSet src2R tgt2R Finset.univ 3 := by decide +kernel
    have h' := sameBlobIn_iff.2 h
    rw [Finset.coe_univ] at h'
    exact sameBlobIn_univ_iff.1 h'
  · rw [fig2R, blobDegree_finNetwork]
    decide +kernel

end Fig2R

/-! ### More on Figure 3 -/

section Fig3

/-- **"The induced network on a B-quartet ... can even be a tree"** (`a:claim:b-quartet-tree`, Section 2): `{a, b, d, e}` is a B-quartet of the network of Figure 3, and among the edges above these taxa no two enter one node. -/
theorem fig3_induced_tree :
    IsBlobQuartet fig3 {0, 1, 3, 4} ∧ ∀ f ∈ fig3.ancestralArcs (({0, 1, 3, 4} : Finset (Fin 6)) : Set (Fin 6)), ∀ g ∈ fig3.ancestralArcs (({0, 1, 3, 4} : Finset (Fin 6)) : Set (Fin 6)),
      fig3.graph.target f = fig3.graph.target g → f = g := by
  refine ⟨fig3_isBlobQuartet.2, ?_⟩
  rw [fig3, ancestralArcs_eq (by decide)]
  have h : ∀ f ∈ arcsOf src3 tgt3 leaf3 {0, 1, 3, 4}, ∀ g ∈ arcsOf src3 tgt3 leaf3 {0, 1, 3, 4}, tgt3 f = tgt3 g → f = g := by decide +kernel
  exact fun f hf g hg hfg => h f (Finset.mem_coe.1 hf) g (Finset.mem_coe.1 hg) hfg

/-- **"However, `{a, b, c, f}` is a B-quartet on both the full and the induced networks"** (`a:claim:fig3-abcf`, after Definition 13). -/
theorem fig3_abcf : IsBlobQuartet fig3 {0, 1, 2, 5} ∧ InducedHasStarTopology isBinaryNetwork_fig3 0 1 2 5 (by decide) :=
  ⟨⟨by decide, _, isDeterminedBy_of_cert (C := cycle3) (col := col3) (v := 10) (by decide) (by decide +kernel)⟩,
    inducedHasStarTopology_of_cert _ _ (v := 10) (C := cycle3) (col := col3) (by decide +kernel) (by decide +kernel)⟩

end Fig3

/-- **"Nodes ... of degree 2 or 3 may correspond to trivial or non-trivial blobs in the network"** (`a:claim:degree-examples`, Section 2). The degree of a node of the tree of blobs is `cutDegree` (`nodeDegree_bridgeQuotient`). Degree 3: the node `10` of Figure 1 is trivial, and `18` isn't. Degree 2: the blob of `13` of Figure 1 isn't trivial, and the root of Figure 3 is. -/
theorem fig1_degree_examples :
    (IsTrivialBlob fig1.graph (blobOf fig1.graph 10) ∧ cutDegree fig1.graph (blobOf fig1.graph 10) = 3) ∧
      (¬ IsTrivialBlob fig1.graph (blobOf fig1.graph 18) ∧ cutDegree fig1.graph (blobOf fig1.graph 18) = 3) ∧
      (¬ IsTrivialBlob fig1.graph (blobOf fig1.graph 13) ∧ cutDegree fig1.graph (blobOf fig1.graph 13) = 2) ∧
      (IsTrivialBlob fig3.graph (blobOf fig3.graph 12) ∧ cutDegree fig3.graph (blobOf fig3.graph 12) = 2) := by
  have hc : ∀ v, cutDegree fig1.graph (blobOf fig1.graph v) = (BlobCert.incidentCol src1 tgt1 col1 v).card := blobCert1.cutDegree_blobOf
  refine ⟨⟨(fig1_isTrivialBlob_iff 10).2 (by decide +kernel), ?_⟩, ⟨mt (fig1_isTrivialBlob_iff 18).1 (by decide +kernel), ?_⟩, ⟨mt (fig1_isTrivialBlob_iff 13).1 (by decide +kernel), ?_⟩, ?_, ?_⟩
  · rw [hc]
    decide +kernel
  · rw [hc]
    decide +kernel
  · rw [hc]
    decide +kernel
  · refine ⟨12, Set.eq_singleton_iff_unique_mem.2 ⟨rfl, fun w hw => ?_⟩⟩
    have h0 : SameBlobIn (graphOf src3 tgt3) Set.univ 12 w := sameBlobIn_univ_iff.2 (Eq.symm hw)
    have h1 : w ∈ FigureCheck.blobSet src3 tgt3 Finset.univ 12 := by
      refine sameBlobIn_iff.1 ?_
      rw [Finset.coe_univ]
      exact h0
    have h2 : FigureCheck.blobSet src3 tgt3 Finset.univ 12 = {12} := by decide +kernel
    rw [h2] at h1
    exact Finset.mem_singleton.1 h1
  · have h : cutDegree (graphOf src3 tgt3) (blobOf (graphOf src3 tgt3) 12) = (incidentOf src3 tgt3 Finset.univ 12).card := by
      rw [cutDegree, incidentCutEdges_blobOf, ← Set.ncard_coe_finset (incidentOf src3 tgt3 Finset.univ 12), ← incidentCuts_eq, Finset.coe_univ]
    refine h.trans ?_
    decide +kernel

end AllmanEtAl2023.Figures
