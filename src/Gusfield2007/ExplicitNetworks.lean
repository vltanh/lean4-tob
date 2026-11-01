module

public import Gusfield2007.Basic
public import Gusfield2007.Examples

/-!
# Gusfield et al. 2007: explicit networks, from lists of numbers

A small network, given as lists of numbers, with its conditions checked by the kernel: the upper bounds on `R` and `R_S` for the figures. The vertices are numbered so that arcs go up and the root is `0`, and the
label of a vertex is a number, whose bit `i` is the state of the site `i`.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

namespace Network

/-- A network on `Fin a` and `Fin b`, from conditions that can be decided. The arcs go up in `Fin a`, which shows it's acyclic. -/
def mkNet {m a b : ℕ} (src tgt : Fin b → Fin a) (root : Fin a) (site : Fin m → Fin b) (label : Fin a → Fin m → Bool)
    (h₁ : ∀ e f, src e = src f → tgt e = tgt f → e = f)
    (h₂ : ∀ e, (src e).val < (tgt e).val)
    (h₃ : ∀ v, (∀ e, tgt e ≠ v) ↔ v = root)
    (h₄ : ∀ e f g, tgt e = tgt f → tgt f = tgt g → e = f ∨ e = g ∨ f = g)
    (h₅ : ∀ i f, tgt f = tgt (site i) → f = site i)
    (h₆ : ∀ e, (∀ f, tgt f = tgt e → f = e) → ∀ i, label (tgt e) i = xor (decide (site i = e)) (label (src e) i))
    (h₇ : ∀ e f, e ≠ f → tgt e = tgt f → ∀ i, label (tgt e) i = label (src e) i ∨ label (tgt e) i = label (src f) i) :
    Network (Fin m) (Fin a) (Fin b) where
  src := src
  tgt := tgt
  root := root
  site := site
  label := label
  simple := h₁
  acyclic := acyclic_of_rank (fun v => v.val) h₂
  root_iff := h₃
  inDegree_le_two := h₄
  site_not_recomb := h₅
  label_tree e he i := by
    have := h₆ e he i
    by_cases hs : site i = e <;> simp_all
  label_recomb := h₇

variable {m a b : ℕ}

theorem derives_of_decide (N : Network (Fin m) (Fin a) (Fin b)) {M : Finset (Fin m → Bool)}
    (h₁ : ∀ v, (∀ e, N.src e ≠ v) → N.label v ∈ M)
    (h₂ : ∀ u v, (∀ e, N.src e ≠ u) → (∀ e, N.src e ≠ v) → N.label u = N.label v → u = v)
    (h₃ : ∀ r ∈ M, ∃ v, (∀ e, N.src e ≠ v) ∧ N.label v = r) : N.Derives M :=
  ⟨fun v hv => h₁ v hv, fun u hu v hv huv => h₂ u v hu hv huv, fun r hr => h₃ r hr⟩

/-- An explicit network with single crossovers: at each recombination node, a prefix of the sites from one parent, and the rest from the other. -/
theorem obeys_single_of_prefix (N : Network (Fin m) (Fin a) (Fin b))
    (hs : ∀ x, (∃ e f, e ≠ f ∧ N.tgt e = x ∧ N.tgt f = x) → ∃ e f, e ≠ f ∧ N.tgt e = x ∧ N.tgt f = x ∧ ∃ n : Fin (m + 1), ∀ i,
      N.label x i = if i.val < n.val then N.label (N.src e) i else N.label (N.src f) i) : N.Obeys .single := by
  rintro x ⟨e₀, f₀, h₁, h₂, h₃⟩
  obtain ⟨e, f, hef, he, hf, n, hn⟩ := hs x ⟨e₀, f₀, h₁, h₂, h₃⟩
  let L : LowerSet (Fin m) := ⟨{i | i.val < n.val}, fun a b hba ha => show b.val < n.val from lt_of_le_of_lt (show b.val ≤ a.val from hba) ha⟩
  refine ⟨e, f, hef, he, hf, L, fun i => ?_⟩
  have hn' := hn i
  by_cases hi : i.val < n.val
  · have hi' : i ∈ L := hi
    simp only [hi, hi', ↓reduceIte] at hn' ⊢
    exact hn'
  · have hi' : i ∉ L := hi
    simp only [hi, hi', ↓reduceIte] at hn' ⊢
    exact hn'

/-- An explicit network obeys all the crossover models, if at each recombination node it has a prefix for `single`, and one site for `pointwise`. -/
theorem obeys_of_decide (N : Network (Fin m) (Fin a) (Fin b))
    (hs : ∀ x, (∃ e f, e ≠ f ∧ N.tgt e = x ∧ N.tgt f = x) → ∃ e f, e ≠ f ∧ N.tgt e = x ∧ N.tgt f = x ∧ ∃ n : Fin (m + 1), ∀ i,
      N.label x i = if i.val < n.val then N.label (N.src e) i else N.label (N.src f) i)
    (hp : ∀ x, (∃ e f, e ≠ f ∧ N.tgt e = x ∧ N.tgt f = x) → ∃ e f, e ≠ f ∧ N.tgt e = x ∧ N.tgt f = x ∧ ∃ j, ∀ i,
      N.label x i = if i = j then N.label (N.src f) i else N.label (N.src e) i) (c : Crossover) : N.Obeys c := by
  cases c with
  | single => exact N.obeys_single_of_prefix hs
  | multiple => trivial
  | pointwise =>
    rintro x ⟨e₀, f₀, h₁, h₂, h₃⟩
    obtain ⟨e, f, hef, he, hf, j, hn⟩ := hp x ⟨e₀, f₀, h₁, h₂, h₃⟩
    refine ⟨e, f, hef, he, hf, j, fun i => ?_⟩
    have := hn i
    by_cases hi : i = j <;> simp_all

end Network

/-- A network on `m` sites, `a` vertices and `b` arcs, as lists of numbers. -/
structure NetSpec (m a b : ℕ) where
  /-- The source of each arc. -/
  srcs : List ℕ
  /-- The target of each arc. -/
  tgts : List ℕ
  /-- The arc of each site. -/
  sites : List ℕ
  /-- The label of each vertex. -/
  labels : List ℕ

namespace NetSpec

variable {m a b : ℕ} [NeZero a] [NeZero b] (s : NetSpec m a b)

/-- The source of an arc. -/
def src (e : Fin b) : Fin a := Fin.ofNat a (s.srcs.getD e 0)

/-- The target of an arc. -/
def tgt (e : Fin b) : Fin a := Fin.ofNat a (s.tgts.getD e 0)

/-- The arc of a site. -/
def site (i : Fin m) : Fin b := Fin.ofNat b (s.sites.getD i 0)

/-- The label of a vertex. -/
def label (v : Fin a) (i : Fin m) : Bool := (s.labels.getD v 0).testBit i

/-- The conditions for `s` to be a network, with the root `0`, and arcs going up. -/
abbrev Valid : Prop :=
  (∀ e f, s.src e = s.src f → s.tgt e = s.tgt f → e = f) ∧
  (∀ e, (s.src e).val < (s.tgt e).val) ∧
  (∀ v, (∀ e, s.tgt e ≠ v) ↔ v = 0) ∧
  (∀ e f g, s.tgt e = s.tgt f → s.tgt f = s.tgt g → e = f ∨ e = g ∨ f = g) ∧
  (∀ i f, s.tgt f = s.tgt (s.site i) → f = s.site i) ∧
  (∀ e, (∀ f, s.tgt f = s.tgt e → f = e) → ∀ i,
    s.label (s.tgt e) i = if s.site i = e then !s.label (s.src e) i else s.label (s.src e) i) ∧
  (∀ e f, e ≠ f → s.tgt e = s.tgt f → ∀ i, s.label (s.tgt e) i = s.label (s.src e) i ∨ s.label (s.tgt e) i = s.label (s.src f) i)

variable {s}

/-- The network given by valid lists. -/
def toNetwork (h : s.Valid) : Network (Fin m) (Fin a) (Fin b) :=
  Network.mkNet s.src s.tgt 0 s.site s.label h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 (fun e he i => by
    rw [h.2.2.2.2.2.1 e he i]
    by_cases hs : s.site i = e <;> simp [hs]) h.2.2.2.2.2.2

variable (s) in
/-- The vertex is a recombination node. -/
abbrev IsRec (x : Fin a) : Prop := ∃ e f, e ≠ f ∧ s.tgt e = x ∧ s.tgt f = x

variable (s) in
/-- The number of recombination nodes. -/
def recombs : ℕ := (Finset.univ.filter s.IsRec).card

theorem recombCount_toNetwork (h : s.Valid) : (toNetwork h).recombCount = s.recombs :=
  Nat.subtype_card _ fun x => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl

variable (s) in
/-- The conditions for `s` to derive `M`. -/
abbrev DerivesCheck (M : Finset (Fin m → Bool)) : Prop :=
  (∀ v, (∀ e, s.src e ≠ v) → s.label v ∈ M) ∧
  (∀ u v, (∀ e, s.src e ≠ u) → (∀ e, s.src e ≠ v) → s.label u = s.label v → u = v) ∧
  (∀ r ∈ M, ∃ v, (∀ e, s.src e ≠ v) ∧ s.label v = r)

theorem derives_toNetwork (h : s.Valid) {M : Finset (Fin m → Bool)} (hd : s.DerivesCheck M) : (toNetwork h).Derives M :=
  Network.derives_of_decide _ hd.1 hd.2.1 hd.2.2

variable (s) in
/-- The condition for the recombination nodes of `s` to be single crossovers. -/
abbrev SingleCheck : Prop :=
  ∀ x, s.IsRec x → ∃ e f, e ≠ f ∧ s.tgt e = x ∧ s.tgt f = x ∧ ∃ t : Fin (m + 1), ∀ i : Fin m,
    s.label x i = if i.val < t.val then s.label (s.src e) i else s.label (s.src f) i

theorem obeys_single_toNetwork (h : s.Valid) (hs : s.SingleCheck) : (toNetwork h).Obeys .single :=
  Network.obeys_single_of_prefix _ hs

theorem R_le (h : s.Valid) {M : Finset (Fin m → Bool)} (hd : s.DerivesCheck M) {c : Crossover} (hc : (toNetwork h).Obeys c) :
    R c M ≤ s.recombs := by
  rw [← recombCount_toNetwork h]
  exact Nat.sInf_le ⟨a, b, toNetwork h, hc, derives_toNetwork h hd, rfl⟩

theorem RS_le (h : s.Valid) {M : Finset (Fin m → Bool)} (hd : s.DerivesCheck M) {c : Crossover} (hc : (toNetwork h).Obeys c)
    {S : Fin m → Bool} (hS : s.label 0 = S) : RS c S M ≤ s.recombs := by
  rw [← recombCount_toNetwork h]
  exact Nat.sInf_le ⟨a, b, toNetwork h, hc, derives_toNetwork h hd, hS, rfl⟩

end NetSpec

end Gusfield2007
