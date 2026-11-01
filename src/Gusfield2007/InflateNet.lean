module

public import Gusfield2007.DecompNet
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum

/-!
# Gusfield et al. 2007: a network deriving any sequences from any ancestral sequence

The construction behind line 299: "any super-character in `M` that is associated with `C` can be derived from `S(C)` using at most one
mutation per site, if an unlimited number of recombination nodes are allowed. This is true even if only single-crossovers are allowed". The paper
gives no construction; this is one, in all three crossover models at once.

The sites are numbered `0, ..., n` in order. A *spine* `spine 0 → spine 1 → ... → spine n` changes the sites `0, ..., n - 1`, in order, and a node `u` below
the root changes the site `n`. The recombination of `spine n` and `u` is the node `z`, with every site changed. Then, for each target `t`, a *chain*
`z → chain t n → ... → chain t 0` restores the sites of `t` that aren't changed, one at a time, from `n` down to `0`, each by a recombination with a node of the spine.
The node `chain t l` has the sites before `l` changed, and it agrees with `t` from `l` on. So `chain t 0` is `t`.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

namespace Decomp

namespace Inflate

universe u v

/-- The nodes. -/
inductive Node (n : ℕ) (T : Type v) : Type v where
  | spine (j : Fin (n + 1)) : Node n T
  | u : Node n T
  | z : Node n T
  | chain (t : T) (l : Fin (n + 1)) : Node n T

/-- The arcs. -/
inductive Arc (n : ℕ) (T : Type v) : Type v where
  | step (j : Fin n) : Arc n T
  | rootU : Arc n T
  | uZ : Arc n T
  | spineZ : Arc n T
  | up (t : T) (l : Fin (n + 1)) : Arc n T
  | side (t : T) (l : Fin (n + 1)) : Arc n T

instance {n : ℕ} {T : Type v} [Finite T] : Finite (Node n T) := by
  refine Finite.of_injective (β := Fin (n + 1) ⊕ Bool ⊕ T × Fin (n + 1)) (fun x => match x with
    | .spine j => .inl j
    | .u => .inr (.inl true)
    | .z => .inr (.inl false)
    | .chain t l => .inr (.inr (t, l))) ?_
  intro a b h
  cases a <;> cases b <;> simp_all

instance {n : ℕ} {T : Type v} [Finite T] : Finite (Arc n T) := by
  refine Finite.of_injective (β := Fin n ⊕ Fin 3 ⊕ (T × Fin (n + 1)) ⊕ (T × Fin (n + 1))) (fun x => match x with
    | .step j => .inl j
    | .rootU => .inr (.inl 0)
    | .uZ => .inr (.inl 1)
    | .spineZ => .inr (.inl 2)
    | .up t l => .inr (.inr (.inl (t, l)))
    | .side t l => .inr (.inr (.inr (t, l)))) ?_
  intro a b h
  cases a <;> cases b <;> simp_all

variable {κ : Type u} [LinearOrder κ] {n : ℕ} (e : κ ≃o Fin (n + 1)) (T : Finset (κ → Bool)) (S₀ : κ → Bool)

/-- The target `t` has the state of `S₀` changed at the site number `l`. -/
def Flips (t : κ → Bool) (l : Fin (n + 1)) : Prop := t (e.symm l) ≠ S₀ (e.symm l)

/-- The parent of `chain t l` that has the sites after `l`. -/
noncomputable def upSrc (t : {t // t ∈ T}) (l : Fin (n + 1)) : Node n {t // t ∈ T} :=
  if h : l.1 < n then .chain t ⟨l.1 + 1, by omega⟩ else .z

/-- The parent of `chain t l` with the state of `t` at `l`, and the sites before `l` changed. -/
noncomputable def sideSrc (t : {t // t ∈ T}) (l : Fin (n + 1)) : Node n {t // t ∈ T} :=
  if h : l.1 < n then (if Flips e S₀ t.1 l then .spine ⟨l.1 + 1, by omega⟩ else .spine l) else
    (if Flips e S₀ t.1 l then .u else .spine l)

/-- The source of an arc. -/
noncomputable def src : Arc n {t // t ∈ T} → Node n {t // t ∈ T}
  | .step j => .spine j.castSucc
  | .rootU => .spine 0
  | .uZ => .u
  | .spineZ => .spine (Fin.last n)
  | .up t l => upSrc T t l
  | .side t l => sideSrc e T S₀ t l

/-- The target of an arc. -/
def tgt : Arc n {t // t ∈ T} → Node n {t // t ∈ T}
  | .step j => .spine j.succ
  | .rootU => .u
  | .uZ => .z
  | .spineZ => .z
  | .up t l => .chain t l
  | .side t l => .chain t l

/-- The other arc into the target of an arc, if any. -/
def other : Arc n {t // t ∈ T} → Arc n {t // t ∈ T}
  | .step j => .step j
  | .rootU => .rootU
  | .uZ => .spineZ
  | .spineZ => .uZ
  | .up t l => .side t l
  | .side t l => .up t l

omit [LinearOrder κ] in
variable {T} in
theorem tgt_eq_iff (f g : Arc n {t // t ∈ T}) : tgt T f = tgt T g ↔ f = g ∨ f = other T g := by
  cases f <;> cases g <;> simp [tgt, other, Fin.succ_inj]

/-- A rank, increasing along arcs. -/
def rank : Node n {t // t ∈ T} → ℕ
  | .spine j => j.1
  | .u => 1
  | .z => n + 2
  | .chain _ l => n + 3 + (n - l.1)

/-- The arc that a site is on. -/
def siteArc (i : κ) : Arc n {t // t ∈ T} :=
  if h : (e i).1 < n then .step ⟨(e i).1, h⟩ else .rootU

/-- The labels. -/
def lab : Node n {t // t ∈ T} → κ → Bool
  | .spine j, i => if (e i).1 < j.1 then !S₀ i else S₀ i
  | .u, i => if (e i).1 = n then !S₀ i else S₀ i
  | .z, i => !S₀ i
  | .chain t l, i => if (e i).1 < l.1 then !S₀ i else t.1 i

variable {T S₀}

theorem e_symm_val {l : Fin (n + 1)} {i : κ} : i = e.symm l ↔ (e i).1 = l.1 := by
  constructor
  · rintro rfl
    simp
  · intro h
    have : e i = l := Fin.ext h
    rw [← this]
    simp

theorem chain_flip_eq (t : {t // t ∈ T}) (l : Fin (n + 1)) (h : Flips e S₀ t.1 l) {i : κ} (hi : (e i).1 = l.1) : t.1 i = !S₀ i := by
  have : i = e.symm l := (e_symm_val e).2 hi
  subst this
  revert h
  unfold Flips
  cases t.1 _ <;> cases S₀ _ <;> simp

theorem chain_noflip_eq (t : {t // t ∈ T}) (l : Fin (n + 1)) (h : ¬ Flips e S₀ t.1 l) {i : κ} (hi : (e i).1 = l.1) : t.1 i = S₀ i := by
  have : i = e.symm l := (e_symm_val e).2 hi
  subst this
  revert h
  unfold Flips
  cases t.1 _ <;> cases S₀ _ <;> simp

/-- The label of `chain t l`, by the form for a recombination in one site. -/
theorem lab_chain_pointwise (t : {t // t ∈ T}) (l : Fin (n + 1)) (i : κ) :
    lab e T S₀ (.chain t l) i = if i = e.symm l then lab e T S₀ (sideSrc e T S₀ t l) i else lab e T S₀ (upSrc T t l) i := by
  have hl := l.2
  by_cases hi : (e i).1 = l.1
  · rw [ite_eq_left ((e_symm_val e).2 hi)]
    by_cases hf : Flips e S₀ t.1 l
    · have ht := chain_flip_eq e t l hf hi
      unfold sideSrc
      by_cases hn : l.1 < n
      · simp [lab, hn, hf, hi, ht]
      · have hln : l.1 = n := by omega
        simp [lab, hf, hi, ht, hln]
    · have ht := chain_noflip_eq e t l hf hi
      unfold sideSrc
      by_cases hn : l.1 < n
      · simp [lab, hn, hf, hi, ht]
      · simp [lab, hn, hf, hi, ht]
  · have hne : i ≠ e.symm l := fun h' => hi ((e_symm_val e).1 h')
    rw [ite_eq_right hne]
    unfold upSrc
    by_cases hn : l.1 < n
    · have : (e i).1 < l.1 + 1 ↔ (e i).1 < l.1 := by omega
      simp [lab, hn, this]
    · have : (e i).1 < l.1 := by
        have := (e i).2
        omega
      simp [lab, hn, this]

/-- The label of `chain t l`, by the form for a single crossover: the sites up to `l` from one parent, and the others from the other parent. -/
theorem lab_chain_single (t : {t // t ∈ T}) (l : Fin (n + 1)) (i : κ) :
    lab e T S₀ (.chain t l) i = if (¬ l.1 < n ∧ Flips e S₀ t.1 l) ∨ l.1 < (e i).1 then lab e T S₀ (upSrc T t l) i else lab e T S₀ (sideSrc e T S₀ t l) i := by
  rw [lab_chain_pointwise]
  by_cases hi : (e i).1 = l.1
  · rw [ite_eq_left ((e_symm_val e).2 hi)]
    by_cases hc : ¬ l.1 < n ∧ Flips e S₀ t.1 l
    · have ht := chain_flip_eq e t l hc.2 hi
      have hn : (e i).1 = n := by have := l.2; omega
      simp only [hc, true_or, ite_true, and_self, not_false_eq_true]
      unfold sideSrc upSrc
      simp [hc, lab, hn]
    · have hlt : ¬ l.1 < (e i).1 := by omega
      have hcond : ¬ ((¬ l.1 < n ∧ Flips e S₀ t.1 l) ∨ l.1 < (e i).1) := fun h => h.elim hc hlt
      rw [ite_eq_right hcond]
  · have hne : i ≠ e.symm l := fun h' => hi ((e_symm_val e).1 h')
    rw [ite_eq_right hne]
    by_cases hlt : l.1 < (e i).1
    · simp [hlt]
    · have hlt' : (e i).1 < l.1 := by omega
      by_cases hc : ¬ l.1 < n ∧ Flips e S₀ t.1 l
      · simp [hc]
      · simp only [hlt, or_false, hc, ite_false]
        unfold sideSrc upSrc
        by_cases hn : l.1 < n
        · have h₂ : (e i).1 < l.1 + 1 := by omega
          by_cases hf : Flips e S₀ t.1 l <;> simp [hn, hf, lab, hlt', h₂]
        · have hf : ¬ Flips e S₀ t.1 l := fun hf => hc ⟨hn, hf⟩
          simp [hn, hf, lab, hlt']

theorem rank_src_lt (a : Arc n {t // t ∈ T}) : rank T (src e T S₀ a) < rank T (tgt T a) := by
  cases a with
  | step j => simp [src, tgt, rank]
  | rootU => simp [src, tgt, rank]
  | uZ => simp [src, tgt, rank]
  | spineZ => simp [src, tgt, rank]
  | up t l =>
    simp only [src, tgt, upSrc]
    by_cases h : l.1 < n
    · simp only [h, ↓reduceDIte, rank]
      omega
    · simp only [h, ↓reduceDIte, rank]
      omega
  | side t l =>
    simp only [src, tgt, sideSrc]
    have hl := l.2
    by_cases h : l.1 < n <;> by_cases hf : Flips e S₀ t.1 l <;> simp only [h, hf, ↓reduceDIte, ↓reduceIte, rank] <;> omega

/-- The network, for a nonempty set of targets. -/
noncomputable def net : Network κ (Node n {t // t ∈ T}) (Arc n {t // t ∈ T}) where
  src := src e T S₀
  tgt := tgt T
  root := .spine 0
  site := siteArc e T
  label := lab e T S₀
  simple f g h₁ h₂ := by
    rcases (tgt_eq_iff f g).1 h₂ with h | h
    · exact h
    · subst h
      cases g with
      | step j => rfl
      | rootU => rfl
      | uZ => simp [src, other] at h₁
      | spineZ => simp [src, other] at h₁
      | up t l =>
        exfalso
        simp only [src, other, upSrc, sideSrc] at h₁
        split_ifs at h₁
      | side t l =>
        exfalso
        simp only [src, other, upSrc, sideSrc] at h₁
        split_ifs at h₁
  acyclic := Network.acyclic_of_rank (rank T) (rank_src_lt e)
  root_iff v := by
    constructor
    · intro hv
      cases v with
      | spine j =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j => exact absurd rfl (hv (.step j))
      | u => exact absurd rfl (hv .rootU)
      | z => exact absurd rfl (hv .uZ)
      | chain t l => exact absurd rfl (hv (.up t l))
    · rintro rfl f hf
      cases f <;> simp [tgt, Fin.succ_ne_zero] at hf
  inDegree_le_two f g h h₁ h₂ := by
    rcases (tgt_eq_iff f g).1 h₁ with h₃ | h₃
    · exact Or.inl h₃
    · rcases (tgt_eq_iff h g).1 h₂.symm with h₄ | h₄
      · exact Or.inr (Or.inr h₄.symm)
      · exact Or.inr (Or.inl (h₃.trans h₄.symm))
  site_not_recomb i f hf := by
    rcases (tgt_eq_iff f _).1 hf with h | h
    · exact h
    · rw [h]
      unfold siteArc
      split_ifs <;> rfl
  label_tree f hf i := by
    cases f with
    | step j =>
      have hiff : siteArc e T i = .step j ↔ (e i).1 = j.1 := by
        unfold siteArc
        split_ifs with h
        · simp [Fin.ext_iff]
        · simp only [false_iff]
          have := j.2
          omega
      simp only [hiff, src, tgt, lab, Fin.val_succ, Fin.val_castSucc]
      by_cases h : (e i).1 = j.1
      · simp [h]
      · have : (e i).1 < j.1 + 1 ↔ (e i).1 < j.1 := by omega
        simp [h, this]
    | rootU =>
      have hiff : siteArc e T i = .rootU ↔ (e i).1 = n := by
        unfold siteArc
        have := (e i).2
        split_ifs with h
        · simp only [false_iff]
          omega
        · simp only [true_iff]
          omega
      simp only [hiff, src, tgt, lab]
      by_cases h : (e i).1 = n <;> simp [h]
    | uZ => exact absurd (hf .spineZ rfl) (by simp)
    | spineZ => exact absurd (hf .uZ rfl) (by simp)
    | up t l => exact absurd (hf (.side t l) rfl) (by simp)
    | side t l => exact absurd (hf (.up t l) rfl) (by simp)
  label_recomb f g hne ht i := by
    rcases (tgt_eq_iff f g).1 ht with h | h
    · exact absurd h hne
    · subst h
      cases g with
      | step j => exact absurd rfl hne
      | rootU => exact absurd rfl hne
      | uZ =>
        by_cases h : (e i).1 = n
        · right
          simp [other, src, tgt, lab, h]
        · left
          have : (e i).1 < n := by
            have := (e i).2
            omega
          simp [other, src, tgt, lab, this]
      | spineZ =>
        by_cases h : (e i).1 = n
        · left
          simp [other, src, tgt, lab, h]
        · right
          have : (e i).1 < n := by
            have := (e i).2
            omega
          simp [other, src, tgt, lab, this]
      | up t l =>
        change lab e T S₀ (.chain t l) i = lab e T S₀ (sideSrc e T S₀ t l) i ∨ lab e T S₀ (.chain t l) i = lab e T S₀ (upSrc T t l) i
        rw [lab_chain_pointwise]
        by_cases h : i = e.symm l
        · left
          simp [h]
        · right
          simp [h]
      | side t l =>
        change lab e T S₀ (.chain t l) i = lab e T S₀ (upSrc T t l) i ∨ lab e T S₀ (.chain t l) i = lab e T S₀ (sideSrc e T S₀ t l) i
        rw [lab_chain_pointwise]
        by_cases h : i = e.symm l
        · right
          simp [h]
        · left
          simp [h]

theorem net_isRecomb {x : Node n {t // t ∈ T}} : (net e (T := T) (S₀ := S₀)).IsRecomb x ↔ x = .z ∨ ∃ t l, x = .chain t l := by
  constructor
  · rintro ⟨f, g, hne, rfl, hg⟩
    rcases (tgt_eq_iff g f).1 hg with h | h
    · exact absurd h.symm hne
    · subst h
      cases f with
      | step j => exact absurd rfl hne
      | rootU => exact absurd rfl hne
      | uZ => exact Or.inl rfl
      | spineZ => exact Or.inl rfl
      | up t l => exact Or.inr ⟨t, l, rfl⟩
      | side t l => exact Or.inr ⟨t, l, rfl⟩
  · rintro (rfl | ⟨t, l, rfl⟩)
    · exact ⟨.uZ, .spineZ, by simp, rfl, rfl⟩
    · exact ⟨.up t l, .side t l, by simp, rfl, rfl⟩

theorem net_obeys (c : Crossover) : (net e (T := T) (S₀ := S₀)).Obeys c := by
  cases c with
  | single =>
    intro x hx
    rcases (net_isRecomb e).1 hx with rfl | ⟨t, l, rfl⟩
    · refine ⟨.spineZ, .uZ, by simp, rfl, rfl, ⟨{i | (e i).1 < n}, ?_⟩, fun i => ?_⟩
      · intro a b hab ha
        have : e b ≤ e a := e.monotone hab
        have h₂ : (e b).1 ≤ (e a).1 := this
        have h₃ : (e a).1 < n := ha
        exact lt_of_le_of_lt h₂ h₃
      · split_ifs with h
        · have h' : (e i).1 < n := h
          change lab e T S₀ .z i = lab e T S₀ (.spine (Fin.last n)) i
          simp [lab, h']
        · have h' : ¬ (e i).1 < n := h
          have : (e i).1 = n := by
            have := (e i).2
            omega
          change lab e T S₀ .z i = lab e T S₀ .u i
          simp [lab, this]
    · refine ⟨.side t l, .up t l, by simp, rfl, rfl, ⟨{i | ¬ ((¬ l.1 < n ∧ Flips e S₀ t.1 l) ∨ l.1 < (e i).1)}, ?_⟩, fun i => ?_⟩
      · intro a b hab ha hcon
        apply ha
        rcases hcon with h | h
        · exact Or.inl h
        · refine Or.inr (lt_of_lt_of_le h ?_)
          exact e.monotone hab
      · have h₀ := lab_chain_single (S₀ := S₀) e t l i
        split_ifs with h
        · have h' : ¬ ((¬ l.1 < n ∧ Flips e S₀ t.1 l) ∨ l.1 < (e i).1) := h
          rw [ite_eq_right h'] at h₀
          exact h₀
        · have h' : (¬ l.1 < n ∧ Flips e S₀ t.1 l) ∨ l.1 < (e i).1 := not_not.1 h
          rw [ite_eq_left h'] at h₀
          exact h₀
  | multiple => trivial
  | pointwise =>
    intro x hx
    rcases (net_isRecomb e).1 hx with rfl | ⟨t, l, rfl⟩
    · refine ⟨.spineZ, .uZ, by simp, rfl, rfl, e.symm (Fin.last n), fun i => ?_⟩
      change lab e T S₀ .z i = if i = e.symm (Fin.last n) then lab e T S₀ .u i else lab e T S₀ (.spine (Fin.last n)) i
      by_cases h : i = e.symm (Fin.last n)
      · have : (e i).1 = n := by
          rw [h]
          simp
        simp [h, lab]
      · have : (e i).1 ≠ n := fun h' => h ((e_symm_val e).2 h')
        have h₂ : (e i).1 < n := by
          have := (e i).2
          omega
        simp [h, lab, h₂]
    · exact ⟨.up t l, .side t l, by simp, rfl, rfl, e.symm l, lab_chain_pointwise e t l⟩

theorem net_ancestral : (net e (T := T) (S₀ := S₀)).ancestral = S₀ := by
  funext i
  simp [Network.ancestral, net, lab]

theorem net_isLeaf (hT : T.Nonempty) (x : Node n {t // t ∈ T}) : (net e (T := T) (S₀ := S₀)).IsLeaf x ↔ ∃ t, x = .chain t 0 := by
  constructor
  · intro hx
    cases x with
    | spine j =>
      exfalso
      induction j using Fin.lastCases with
      | last => exact hx .spineZ rfl
      | cast j => exact hx (.step j) rfl
    | u => exact absurd rfl (hx .uZ)
    | z =>
      obtain ⟨t, ht⟩ := hT
      refine absurd ?_ (hx (.up ⟨t, ht⟩ (Fin.last n)))
      simp [net, src, upSrc]
    | chain t l =>
      induction l using Fin.cases with
      | zero => exact ⟨t, rfl⟩
      | succ l =>
        refine absurd ?_ (hx (.up t l.castSucc))
        simp [net, src, upSrc]
        rfl
  · rintro ⟨t, rfl⟩ a ha
    cases a with
    | step j => simp [net, src] at ha
    | rootU => simp [net, src] at ha
    | uZ => simp [net, src] at ha
    | spineZ => simp [net, src] at ha
    | up t' l =>
      simp only [net, src, upSrc] at ha
      split_ifs at ha
      simp at ha
    | side t' l =>
      simp only [net, src, sideSrc] at ha
      split_ifs at ha

theorem net_derives (hT : T.Nonempty) : (net e (T := T) (S₀ := S₀)).Derives T := by
  have hlab : ∀ t : {t // t ∈ T}, (net e (T := T) (S₀ := S₀)).label (.chain t 0) = t.1 := by
    intro t
    funext i
    simp [net, lab]
  refine ⟨fun x hx => ?_, fun a ha b hb hab => ?_, fun r hr => ?_⟩
  · obtain ⟨t, rfl⟩ := (net_isLeaf e hT x).1 hx
    rw [hlab]
    exact t.2
  · obtain ⟨t, rfl⟩ := (net_isLeaf e hT a).1 ha
    obtain ⟨t', rfl⟩ := (net_isLeaf e hT b).1 hb
    rw [hlab, hlab] at hab
    rw [Subtype.ext hab]
  · exact ⟨.chain ⟨r, hr⟩ 0, (net_isLeaf e hT _).2 ⟨_, rfl⟩, hlab ⟨r, hr⟩⟩

/-- The path down the spine. -/
theorem exists_spinePath (j : Fin (n + 1)) : ∃ p, (net e (T := T) (S₀ := S₀)).IsPath (.spine 0) (.spine j) p ∧
    (∀ a ∈ p, ∃ j', tgt T a = .spine j') ∧ ∀ j' : Fin n, j'.1 < j.1 → Arc.step j' ∈ p := by
  induction j using Fin.induction with
  | zero => exact ⟨[], rfl, by simp, by simp⟩
  | succ j ih =>
    obtain ⟨p, hp, h₁, h₂⟩ := ih
    have hstep : (net e (T := T) (S₀ := S₀)).IsPath (.spine j.castSucc) (.spine j.succ) [Arc.step j] := ⟨rfl, rfl⟩
    refine ⟨p ++ [.step j], hp.append hstep, ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact h₁ a ha
      · simp only [List.mem_singleton] at ha
        subst ha
        exact ⟨_, rfl⟩
    · intro j' hj'
      have hj'' : j'.1 ≤ j.1 := by
        simp only [Fin.val_succ] at hj'
        omega
      rcases Nat.lt_or_ge j'.1 j.1 with h | h
      · exact List.mem_append_left _ (h₂ j' h)
      · have : j' = j := Fin.ext (by omega)
        subst this
        simp

/-- The path along a chain. -/
theorem exists_chainPath (t : {t // t ∈ T}) : ∀ (d : ℕ) (l : Fin (n + 1)), n - l.1 = d → ∃ q, (net e (T := T) (S₀ := S₀)).IsPath .z (.chain t l) q ∧
    (∀ a ∈ q, ∃ l', tgt T a = .chain t l') ∧ Arc.up t l ∈ q := by
  intro d
  induction d with
  | zero =>
    intro l hl
    have hn : ¬ l.1 < n := by omega
    refine ⟨[.up t l], ⟨by simp [net, src, upSrc, hn], rfl⟩, ?_, by simp⟩
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact ⟨_, rfl⟩
  | succ d ih =>
    intro l hl
    have hn : l.1 < n := by omega
    obtain ⟨q, hq, h₁, -⟩ := ih ⟨l.1 + 1, by omega⟩ (by
      simp only
      omega)
    have hup : (net e (T := T) (S₀ := S₀)).IsPath (.chain t ⟨l.1 + 1, by omega⟩) (.chain t l) [Arc.up t l] :=
      ⟨by simp [net, src, upSrc, hn], rfl⟩
    refine ⟨q ++ [.up t l], hq.append hup, ?_, by simp⟩
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact h₁ a ha
    · simp only [List.mem_singleton] at ha
      subst ha
      exact ⟨_, rfl⟩

/-- Every arc is on a recombination cycle with the arc from `u` to `z`. -/
theorem exists_cycle (a : Arc n {t // t ∈ T}) : ∃ Q, (net e (T := T) (S₀ := S₀)).IsCycle Q ∧ a ∈ Q ∧ Arc.uZ ∈ Q := by
  -- The cycle at `z`.
  have hz : ∃ p, (net e (T := T) (S₀ := S₀)).IsCycleOn (.spine 0) .z p [.rootU, .uZ] ∧ .spineZ ∈ p ∧ ∀ j : Fin n, Arc.step j ∈ p := by
    obtain ⟨p, hp, h₁, h₂⟩ := exists_spinePath (S₀ := S₀) (T := T) e (Fin.last n)
    have hsz : (net e (T := T) (S₀ := S₀)).IsPath (.spine (Fin.last n)) .z [Arc.spineZ] := ⟨rfl, rfl⟩
    refine ⟨p ++ [.spineZ], ⟨⟨.uZ, .spineZ, by simp, rfl, rfl⟩, hp.append hsz, ⟨rfl, rfl, rfl⟩, ?_, ?_⟩, by simp, ?_⟩
    · intro heq
      have hmem : Arc.rootU ∈ p ++ [Arc.spineZ] := by rw [heq]; simp
      rcases List.mem_append.1 hmem with h | h
      · obtain ⟨j, hj⟩ := h₁ _ h
        simp [tgt] at hj
      · simp at h
    · intro f hf g hg hfg
      rcases List.mem_append.1 hf with hf | hf
      · obtain ⟨j, hj⟩ := h₁ _ hf
        change tgt T f = tgt T g at hfg
        rw [hj] at hfg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl <;> simp [tgt] at hfg
      · simp only [List.mem_singleton] at hf
        subst hf
        rfl
    · exact fun j => List.mem_append_left _ (h₂ j (by simp))
  -- The cycle at `chain t l`.
  have hc : ∀ (t : {t // t ∈ T}) (l : Fin (n + 1)), ∃ Q, (net e (T := T) (S₀ := S₀)).IsCycle Q ∧ Arc.up t l ∈ Q ∧ Arc.side t l ∈ Q ∧ Arc.uZ ∈ Q := by
    intro t l
    obtain ⟨q, hq, hq₁, hq₂⟩ := exists_chainPath (S₀ := S₀) (T := T) e t _ l rfl
    have hsrc : sideSrc e T S₀ t l = .u ∨ ∃ j, sideSrc e T S₀ t l = .spine j := by
      unfold sideSrc
      split_ifs
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl⟩
    rcases hsrc with hs | ⟨j, hs⟩
    · refine ⟨_, ⟨.u, .chain t l, [.side t l], .uZ :: q, ⟨⟨.up t l, .side t l, by simp, rfl, rfl⟩, ⟨hs, rfl⟩, ⟨rfl, hq⟩, ?_, ?_⟩, rfl⟩,
        Or.inr (List.mem_cons_of_mem _ hq₂), Or.inl (by simp), Or.inr (by simp)⟩
      · intro heq
        have : Arc.uZ ∈ [Arc.side t l] := by rw [heq]; simp
        simp at this
      · intro f hf g hg hfg
        simp only [List.mem_singleton] at hf
        subst hf
        rfl
    · obtain ⟨p, hp, h₁, -⟩ := exists_spinePath (S₀ := S₀) (T := T) e j
      have hsd : (net e (T := T) (S₀ := S₀)).IsPath (.spine j) (.chain t l) [Arc.side t l] := ⟨hs, rfl⟩
      refine ⟨_, ⟨.spine 0, .chain t l, p ++ [.side t l], .rootU :: .uZ :: q, ⟨⟨.up t l, .side t l, by simp, rfl, rfl⟩,
        hp.append hsd, ⟨rfl, rfl, hq⟩, ?_, ?_⟩, rfl⟩,
        Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq₂)), Or.inl (by simp), Or.inr (by simp)⟩
      · intro heq
        have hmem : Arc.rootU ∈ p ++ [Arc.side t l] := by rw [heq]; simp
        rcases List.mem_append.1 hmem with h | h
        · obtain ⟨j', hj'⟩ := h₁ _ h
          simp [tgt] at hj'
        · simp at h
      · intro f hf g hg hfg
        rcases List.mem_append.1 hf with hf | hf
        · obtain ⟨j', hj'⟩ := h₁ _ hf
          change tgt T f = tgt T g at hfg
          rw [hj'] at hfg
          rcases List.mem_cons.1 hg with rfl | hg
          · simp [tgt] at hfg
          · rcases List.mem_cons.1 hg with rfl | hg
            · simp [tgt] at hfg
            · obtain ⟨l', hl'⟩ := hq₁ _ hg
              rw [hl'] at hfg
              simp at hfg
        · simp only [List.mem_singleton] at hf
          subst hf
          rfl
  obtain ⟨p, hzc, hz₁, hz₂⟩ := hz
  have hQ₀ : (net e (T := T) (S₀ := S₀)).IsCycle {f | f ∈ p ∨ f ∈ [Arc.rootU, Arc.uZ]} := ⟨_, _, _, _, hzc, rfl⟩
  have huZ : Arc.uZ ∈ {f | f ∈ p ∨ f ∈ [Arc.rootU, (Arc.uZ : Arc n {t // t ∈ T})]} := Or.inr (by simp)
  cases a with
  | step j => exact ⟨_, hQ₀, Or.inl (hz₂ j), huZ⟩
  | rootU => exact ⟨_, hQ₀, Or.inr (by simp), huZ⟩
  | uZ => exact ⟨_, hQ₀, huZ, huZ⟩
  | spineZ => exact ⟨_, hQ₀, Or.inl hz₁, huZ⟩
  | up t l =>
    obtain ⟨Q, hQ, h₁, -, h₃⟩ := hc t l
    exact ⟨Q, hQ, h₁, h₃⟩
  | side t l =>
    obtain ⟨Q, hQ, -, h₂, h₃⟩ := hc t l
    exact ⟨Q, hQ, h₂, h₃⟩

end Inflate

variable {ι : Type*} {V E V' E' : Type*}

/-- The properties of a network with one blob, on all of its arcs, pass to a copy. -/
theorem onCycle_unique_of_iso {N : Network ι V E} {N' : Network ι V' E'} {eV : V ≃ V'} {eE : E ≃ E'} (h : N.IsIso N' eV eE)
    (h₁ : ∀ e, N.OnCycle e) (h₂ : ∃! B, N.IsBlob B) : (∀ e, N'.OnCycle e) ∧ ∃! B, N'.IsBlob B := by
  refine ⟨fun a => by simpa using (h.onCycle (eE.symm a)).2 (h₁ _), ?_⟩
  obtain ⟨B₀, hB₀, huniq⟩ := h₂
  refine ⟨eE '' B₀, h.isBlob_image hB₀, fun B' hB' => ?_⟩
  obtain ⟨B, hB, rfl⟩ := h.exists_eq_image_of_isBlob hB'
  rw [huniq B hB]

/-- **Line 299**, the construction: all sequences on at least one site can be derived from any ancestral sequence, in any model, with one blob
containing all arcs. -/
theorem exists_inflate_net {κ : Type*} [LinearOrder κ] [Fintype κ] (c : Crossover) (hκ : 1 ≤ Fintype.card κ)
    (T : Finset (κ → Bool)) (hT : T.Nonempty) (S₀ : κ → Bool) :
    ∃ (a b : ℕ) (N : Network κ (Fin a) (Fin b)), N.Obeys c ∧ N.ancestral = S₀ ∧ N.Derives T ∧
      (∀ e, N.OnCycle e) ∧ ∃! B, N.IsBlob B := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card κ = n + 1 := ⟨Fintype.card κ - 1, by omega⟩
  let e : κ ≃o Fin (n + 1) := (Fintype.orderIsoFinOfCardEq κ hn).symm
  let N₀ := Inflate.net e (T := T) (S₀ := S₀)
  have hall : ∀ a, N₀.OnCycle a := fun a => by
    obtain ⟨Q, hQ, ha, -⟩ := Inflate.exists_cycle (S₀ := S₀) (T := T) e a
    exact ⟨Q, hQ, ha⟩
  have huniq : ∃! B, N₀.IsBlob B := by
    obtain ⟨Q₀, hQ₀, -, hu₀⟩ := Inflate.exists_cycle (S₀ := S₀) (T := T) e .uZ
    refine ⟨_, ⟨Q₀, hQ₀, rfl⟩, ?_⟩
    rintro B ⟨Q, hQ, rfl⟩
    -- A cycle has an arc.
    obtain ⟨a, ha⟩ : Q.Nonempty := by
      obtain ⟨w, x, p, q, ⟨-, -, -, hpq, -⟩, rfl⟩ := hQ
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      have hp : p = [] := List.eq_nil_iff_forall_not_mem.2 fun a ha => by
        have : a ∈ ({f | f ∈ p ∨ f ∈ q} : Set _) := Or.inl ha
        rw [hcon] at this
        exact this
      have hq : q = [] := List.eq_nil_iff_forall_not_mem.2 fun a ha => by
        have : a ∈ ({f | f ∈ p ∨ f ∈ q} : Set _) := Or.inr ha
        rw [hcon] at this
        exact this
      exact hpq (hp.trans hq.symm)
    obtain ⟨Q₁, hQ₁, ha₁, hu₁⟩ := Inflate.exists_cycle (S₀ := S₀) (T := T) e a
    have hB₁ : N₀.IsBlob (⋃₀ {Q' | Relation.ReflTransGen N₀.ShareArc Q₁ Q'}) := ⟨Q₁, hQ₁, rfl⟩
    have h₁ := Network.IsBlob.eq_of_inter_nonempty (N := N₀) ⟨Q, hQ, rfl⟩ hB₁
      ⟨a, ⟨Q, Relation.ReflTransGen.refl, ha⟩, ⟨Q₁, Relation.ReflTransGen.refl, ha₁⟩⟩
    have h₂ := Network.IsBlob.eq_of_inter_nonempty (N := N₀) hB₁ ⟨Q₀, hQ₀, rfl⟩
      ⟨.uZ, ⟨Q₁, Relation.ReflTransGen.refl, hu₁⟩, ⟨Q₀, Relation.ReflTransGen.refl, hu₀⟩⟩
    exact h₁.trans h₂
  obtain ⟨a, b, N', eV, eE, hiso⟩ := N₀.exists_fin_iso
  obtain ⟨-, h₂, h₃, h₄, -⟩ := hiso.invariants
  obtain ⟨h₅, h₆⟩ := onCycle_unique_of_iso hiso hall huniq
  exact ⟨a, b, N', (h₂ c).2 (Inflate.net_obeys e c), h₄.trans (Inflate.net_ancestral e),
    (h₃ T).2 (Inflate.net_derives e hT), h₅, h₆⟩

end Decomp

end Gusfield2007
