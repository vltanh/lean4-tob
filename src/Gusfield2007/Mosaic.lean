module

public import Gusfield2007.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma

/-!
# Gusfield et al. 2007: the network for `M_d(C)`

Line 643: "It is straightforward to show that `R¹(M_d(C₁)) = R¹(M_d(C₂)) = 2d`". The paper needs `≥` only, and it doesn't give the network for `≤`. Here is one. The sites are in `n + 1` consecutive segments, numbered by `seg`, and the rows are the
sequences `0…0`, the even segments, the odd segments, and `1…1`. The even and the odd segments mutate on two arcs from the root. A chain of `n` single crossovers then gives `1…1`, one more segment at a time.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

/-- The vertices of the network, with `n` recombination nodes. -/
inductive MosaicV (n : ℕ) where
  | root | leaf0 | even | leafEven | odd | leafOdd
  | recomb (j : Fin n)

/-- The arcs of the network: two into each recombination node. -/
inductive MosaicE (n : ℕ) where
  | toLeaf0 | toEven | toLeafEven | toOdd | toLeafOdd
  | main (j : Fin n)
  | other (j : Fin n)

namespace Mosaic

variable {n : ℕ}

instance : Finite (MosaicV n) := by
  let f : MosaicV n → Fin 6 ⊕ Fin n := fun v => match v with
    | .root => .inl 0 | .leaf0 => .inl 1 | .even => .inl 2 | .leafEven => .inl 3 | .odd => .inl 4 | .leafOdd => .inl 5
    | .recomb j => .inr j
  refine Finite.of_injective f fun u v h => ?_
  cases u <;> cases v <;> simp_all [f]

instance : Finite (MosaicE n) := by
  let f : MosaicE n → Fin 5 ⊕ (Fin n ⊕ Fin n) := fun v => match v with
    | .toLeaf0 => .inl 0 | .toEven => .inl 1 | .toLeafEven => .inl 2 | .toOdd => .inl 3 | .toLeafOdd => .inl 4
    | .main j => .inr (.inl j) | .other j => .inr (.inr j)
  refine Finite.of_injective f fun u v h => ?_
  cases u <;> cases v <;> simp_all [f]

/-- The source of an arc. -/
def src : MosaicE n → MosaicV n
  | .toLeaf0 | .toEven | .toOdd => .root
  | .toLeafEven => .even
  | .toLeafOdd => .odd
  | .main j => if h : j.val = 0 then .even else .recomb ⟨j.val - 1, by have := j.2; omega⟩
  | .other j => if j.val % 2 = 0 then .odd else .even

/-- The target of an arc. -/
def tgt : MosaicE n → MosaicV n
  | .toLeaf0 => .leaf0
  | .toEven => .even
  | .toLeafEven => .leafEven
  | .toOdd => .odd
  | .toLeafOdd => .leafOdd
  | .main j => .recomb j
  | .other j => .recomb j

/-- A rank that increases along the arcs. -/
def rank : MosaicV n → ℕ
  | .root => 0
  | .leaf0 | .even | .odd => 1
  | .leafEven | .leafOdd => 2
  | .recomb j => j.val + 2

theorem rank_lt (e : MosaicE n) : rank (src e) < rank (tgt e) := by
  cases e with
  | main j =>
    simp only [src, tgt]
    split_ifs with h
    · simp [rank]
    · have := j.2
      simp only [rank]
      omega
  | other j =>
    simp only [src, tgt]
    split_ifs <;> simp [rank]
  | _ => simp [src, tgt, rank]

theorem tgt_eq : ∀ e f : MosaicE n, tgt e = tgt f →
    e = f ∨ ∃ j, (e = .main j ∧ f = .other j) ∨ (e = .other j ∧ f = .main j) := by
  intro e f h
  cases e <;> cases f <;> simp_all [tgt]

theorem main_ne_other (j : Fin n) : src (MosaicE.main j) ≠ src (MosaicE.other j) := by
  simp only [src]
  split_ifs <;> first | (simp; done) | omega

variable {ι : Type} (seg : ι → ℕ)

/-- The sequence with `1` on the segments of parity `x`. -/
def parity (x : ℕ) (i : ι) : Bool := decide (seg i % 2 = x)

/-- The label of a recombination node, in the chain: `1` on the segments up to `j`, and from then on on those of the parity of `j`. -/
def chain (j : ℕ) (i : ι) : Bool := decide (seg i ≤ j) || decide (seg i % 2 = j % 2)

theorem chain_zero : chain seg 0 = parity seg 0 := by
  funext i
  simp only [chain, parity]
  by_cases h : seg i = 0
  · simp [h]
  · simp [h]

theorem chain_succ (j : ℕ) (i : ι) : chain seg (j + 1) i = if seg i ≤ j then chain seg j i else parity seg ((j + 1) % 2) i := by
  simp only [chain, parity]
  by_cases h : seg i ≤ j
  · have : seg i ≤ j + 1 := by omega
    simp [h, this]
  · by_cases h' : seg i = j + 1
    · simp [h']
    · have : ¬ seg i ≤ j + 1 := by omega
      simp [h, this]

/-- The label of a vertex. -/
def label : MosaicV n → ι → Bool
  | .root | .leaf0 => fun _ => false
  | .even | .leafEven => parity seg 0
  | .odd | .leafOdd => parity seg 1
  | .recomb j => chain seg (j.val + 1)

theorem label_src_main (j : Fin n) : label seg (src (MosaicE.main j)) = chain seg j.val := by
  simp only [src]
  split_ifs with h
  · rw [h, chain_zero]
    rfl
  · simp only [label]
    congr 1
    omega

theorem label_src_other (j : Fin n) : label seg (src (MosaicE.other j)) = parity seg ((j.val + 1) % 2) := by
  simp only [src]
  split_ifs with h
  · have : (j.val + 1) % 2 = 1 := by omega
    rw [this]
    rfl
  · have : (j.val + 1) % 2 = 0 := by omega
    rw [this]
    rfl

/-- The network. -/
def net : Network ι (MosaicV n) (MosaicE n) where
  src := src
  tgt := tgt
  root := .root
  site i := if seg i % 2 = 0 then .toEven else .toOdd
  label := label seg
  simple e f h₁ h₂ := by
    rcases tgt_eq e f h₂ with h | ⟨j, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact h
    · exact absurd h₁ (main_ne_other j)
    · exact absurd h₁.symm (main_ne_other j)
  acyclic := Network.acyclic_of_rank rank rank_lt
  root_iff v := by
    constructor
    · intro h
      cases v with
      | root => rfl
      | leaf0 => exact absurd rfl (h .toLeaf0)
      | even => exact absurd rfl (h .toEven)
      | leafEven => exact absurd rfl (h .toLeafEven)
      | odd => exact absurd rfl (h .toOdd)
      | leafOdd => exact absurd rfl (h .toLeafOdd)
      | recomb j => exact absurd rfl (h (.main j))
    · rintro rfl e
      cases e <;> simp [tgt]
  inDegree_le_two e f g h₁ h₂ := by
    rcases tgt_eq e f h₁ with h | ⟨j, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl h
    · rcases tgt_eq _ g h₂ with h | ⟨j', ⟨h, rfl⟩ | ⟨h, rfl⟩⟩
      · exact Or.inr (Or.inr h)
      · simp at h
      · simp only [MosaicE.other.injEq] at h
        subst h
        exact Or.inr (Or.inl rfl)
    · rcases tgt_eq _ g h₂ with h | ⟨j', ⟨h, rfl⟩ | ⟨h, rfl⟩⟩
      · exact Or.inr (Or.inr h)
      · simp only [MosaicE.main.injEq] at h
        subst h
        exact Or.inr (Or.inl rfl)
      · simp at h
  site_not_recomb i f h := by
    have key : ∀ e : MosaicE n, (e = .toEven ∨ e = .toOdd) → tgt f = tgt e → f = e := by
      rintro e (rfl | rfl) hf <;>
      · rcases tgt_eq f _ hf with h' | ⟨j, ⟨-, h'⟩ | ⟨-, h'⟩⟩
        · exact h'
        · simp at h'
        · simp at h'
    exact key _ (by split_ifs <;> simp) h
  label_tree e he i := by
    cases e with
    | toLeaf0 => simp only [tgt, src, label]; split_ifs <;> simp_all
    | toEven =>
      simp only [tgt, src, label, parity]
      by_cases hi : seg i % 2 = 0 <;> simp [hi]
    | toLeafEven => simp only [tgt, src, label]; split_ifs <;> simp_all
    | toOdd =>
      simp only [tgt, src, label, parity]
      by_cases hi : seg i % 2 = 0
      · simp [hi]
      · have : seg i % 2 = 1 := by omega
        simp [this]
    | toLeafOdd => simp only [tgt, src, label]; split_ifs <;> simp_all
    | main j => exact absurd (he (.other j) rfl) (by simp)
    | other j => exact absurd (he (.main j) rfl) (by simp)
  label_recomb e f hef h i := by
    have key : ∀ (j : Fin n), label seg (tgt (MosaicE.main j)) i = label seg (src (MosaicE.main j)) i ∨
        label seg (tgt (MosaicE.main j)) i = label seg (src (MosaicE.other j)) i := fun j => by
      rw [label_src_main, label_src_other]
      simp only [tgt, label]
      rw [chain_succ]
      split_ifs <;> simp
    rcases tgt_eq e f h with h' | ⟨j, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact absurd h' hef
    · exact key j
    · exact (key j).symm

theorem isRecomb_iff (x : MosaicV n) : (net seg).IsRecomb x ↔ ∃ j, x = .recomb j := by
  constructor
  · rintro ⟨e, f, hef, rfl, hf⟩
    rcases tgt_eq e f hf.symm with h | ⟨j, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    · exact absurd h hef
    · exact ⟨j, rfl⟩
    · exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨.main j, .other j, by simp, rfl, rfl⟩

theorem recombCount_net : (net (n := n) seg).recombCount = n := by
  have hb : Function.Bijective fun j : Fin n => (⟨.recomb j, (isRecomb_iff seg _).2 ⟨j, rfl⟩⟩ : {x // (net (n := n) seg).IsRecomb x}) := by
    refine ⟨fun a b h => ?_, fun ⟨x, hx⟩ => ?_⟩
    · simpa using h
    · obtain ⟨j, rfl⟩ := (isRecomb_iff seg x).1 hx
      exact ⟨j, rfl⟩
  have := Nat.card_congr (Equiv.ofBijective _ hb)
  simpa [Network.recombCount] using this.symm

theorem obeys_net [LinearOrder ι] (hmono : Monotone seg) : (net (n := n) seg).Obeys .single := fun x hx => by
  obtain ⟨j, rfl⟩ := (isRecomb_iff seg x).1 hx
  refine ⟨.main j, .other j, by simp, rfl, rfl, ⟨{i | seg i ≤ j.val}, fun a b hab ha => le_trans (hmono hab) ha⟩, fun i => ?_⟩
  change chain seg (j.val + 1) i = if i ∈ _ then label seg (src (MosaicE.main j)) i else label seg (src (MosaicE.other j)) i
  rw [label_src_main, label_src_other, chain_succ]
  by_cases hi : seg i ≤ j.val
  · have hm : i ∈ (⟨{i | seg i ≤ j.val}, fun a b hab ha => le_trans (hmono hab) ha⟩ : LowerSet ι) := hi
    simp [hi, hm]
  · have hm : i ∉ (⟨{i | seg i ≤ j.val}, fun a b hab ha => le_trans (hmono hab) ha⟩ : LowerSet ι) := hi
    simp [hi, hm]

theorem isLeaf_iff (hn : 0 < n) (v : MosaicV n) :
    (net (n := n) seg).IsLeaf v ↔ v = .leaf0 ∨ v = .leafEven ∨ v = .leafOdd ∨ v = .recomb ⟨n - 1, by omega⟩ := by
  constructor
  · intro h
    cases v with
    | root => exact absurd rfl (h .toLeaf0)
    | leaf0 => simp
    | even => exact absurd rfl (h .toLeafEven)
    | leafEven => simp
    | odd => exact absurd rfl (h .toLeafOdd)
    | leafOdd => simp
    | recomb j =>
      by_cases hj : j.val + 1 < n
      · refine absurd ?_ (h (.main ⟨j.val + 1, hj⟩))
        simp [net, src]
      · have : j = ⟨n - 1, by omega⟩ := Fin.ext (by have := j.2; simp only; omega)
        simp [this]
  · intro h e
    change src e ≠ v
    rcases h with rfl | rfl | rfl | rfl
    · cases e with
      | main j =>
        simp only [src]
        split_ifs <;> simp
      | other j =>
        simp only [src]
        split_ifs <;> simp
      | _ => simp [src]
    · cases e with
      | main j =>
        simp only [src]
        split_ifs <;> simp
      | other j =>
        simp only [src]
        split_ifs <;> simp
      | _ => simp [src]
    · cases e with
      | main j =>
        simp only [src]
        split_ifs <;> simp
      | other j =>
        simp only [src]
        split_ifs <;> simp
      | _ => simp [src]
    · cases e with
      | main j =>
        simp only [src]
        split_ifs with h
        · simp
        · intro heq
          have h' := congrArg Fin.val (MosaicV.recomb.inj heq)
          have := j.2
          simp only at h'
          omega
      | other j =>
        simp only [src]
        split_ifs <;> simp
      | _ => simp [src]

end Mosaic

open Mosaic in
/-- **The network for `M_d(C)`**. The rows `0…0`, the even segments, the odd segments, `1…1` have a network with one single crossover for each change of segment. -/
theorem R_single_le_of_mosaic {ι : Type} [LinearOrder ι] [Finite ι] (seg : ι → ℕ) (hmono : Monotone seg) {n : ℕ} (hn : 0 < n) (hle : ∀ i, seg i ≤ n) {i₀ i₁ : ι}
    (h₀ : seg i₀ % 2 = 0) (h₁ : seg i₁ % 2 = 1) {M : Finset (ι → Bool)}
    (hM : ∀ r, r ∈ M ↔ r = (fun _ => false) ∨ r = parity seg 0 ∨ r = parity seg 1 ∨ r = fun _ => true) :
    R .single M ≤ n := by
  have hone : chain seg n = fun _ => true := by
    funext i
    simp [chain, hle i]
  have hlast : label seg (MosaicV.recomb (n := n) ⟨n - 1, by omega⟩) = fun _ => true := by
    change chain seg (n - 1 + 1) = _
    rw [Nat.sub_add_cancel hn, hone]
  have hv₀ : parity seg 0 i₀ = true := by simp [parity, h₀]
  have hv₁ : parity seg 1 i₁ = true := by simp [parity, h₁]
  have hv₀' : parity seg 1 i₀ = false := by simp [parity, h₀]
  have hv₁' : parity seg 0 i₁ = false := by simp [parity, h₁]
  have hd : (net (n := n) seg).Derives M := by
    refine ⟨fun v hv => ?_, fun u hu v hv huv => ?_, fun r hr => ?_⟩
    · rw [Finset.mem_coe, hM]
      rcases (isLeaf_iff seg hn v).1 hv with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr hlast))
    · change label seg u = label seg v at huv
      rcases (isLeaf_iff seg hn u).1 hu with rfl | rfl | rfl | rfl <;> rcases (isLeaf_iff seg hn v).1 hv with rfl | rfl | rfl | rfl
      · rfl
      · simpa [label, hv₀] using (congrFun huv i₀)
      · simpa [label, hv₁] using (congrFun huv i₁)
      · rw [hlast] at huv
        simpa [label] using (congrFun huv i₀)
      · simpa [label, hv₀] using (congrFun huv i₀)
      · rfl
      · simpa [label, hv₀, hv₀'] using (congrFun huv i₀)
      · rw [hlast] at huv
        simpa [label, hv₁'] using (congrFun huv i₁)
      · simpa [label, hv₁] using (congrFun huv i₁)
      · simpa [label, hv₀, hv₀'] using (congrFun huv i₀)
      · rfl
      · rw [hlast] at huv
        simpa [label, hv₀'] using (congrFun huv i₀)
      · rw [hlast] at huv
        simpa [label] using (congrFun huv i₀)
      · rw [hlast] at huv
        simpa [label, hv₁'] using (congrFun huv i₁)
      · rw [hlast] at huv
        simpa [label, hv₀'] using (congrFun huv i₀)
      · rfl
    · rw [Finset.mem_coe, hM] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨.leaf0, (isLeaf_iff seg hn _).2 (Or.inl rfl), rfl⟩
      · exact ⟨.leafEven, (isLeaf_iff seg hn _).2 (Or.inr (Or.inl rfl)), rfl⟩
      · exact ⟨.leafOdd, (isLeaf_iff seg hn _).2 (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
      · exact ⟨.recomb ⟨n - 1, by omega⟩, (isLeaf_iff seg hn _).2 (Or.inr (Or.inr (Or.inr rfl))), hlast⟩
  have := R_le_recombCount (net (n := n) seg) (obeys_net seg hmono) hd
  rwa [recombCount_net] at this

/-- A matrix on no sites has no recombination. -/
theorem R_eq_zero_of_isEmpty {ι : Type} [LinearOrder ι] [IsEmpty ι] (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) : R c M = 0 := by
  have hone : ∀ r r' : ι → Bool, r = r' := fun r r' => funext fun i => isEmptyElim i
  let N : Network ι (Fin 1) (Fin 0) :=
    { src := Fin.elim0
      tgt := Fin.elim0
      root := 0
      site := fun i => isEmptyElim i
      label := fun _ i => isEmptyElim i
      simple := fun e => e.elim0
      acyclic := Network.acyclic_of_rank (fun v => v.val) fun e => e.elim0
      root_iff := fun v => ⟨fun _ => Subsingleton.elim _ _, fun _ e => e.elim0⟩
      inDegree_le_two := fun e => e.elim0
      site_not_recomb := fun i => isEmptyElim i
      label_tree := fun e => e.elim0
      label_recomb := fun e => e.elim0 }
  have hc : N.recombCount = 0 := Network.recombCount_eq_zero_of_tgt_injective fun e => e.elim0
  have ho : N.Obeys c := Network.obeys_of_tgt_injective (fun e => e.elim0) c
  have hd : N.Derives M := by
    obtain ⟨r₀, hr₀⟩ := hM
    refine ⟨fun v _ => ?_, fun u _ v _ _ => Subsingleton.elim _ _, fun r _ => ⟨0, fun e => e.elim0, hone _ _⟩⟩
    rw [Finset.mem_coe, hone (N.label v) r₀]
    exact hr₀
  exact Nat.le_zero.1 (Nat.sInf_le ⟨1, 0, N, ho, hd, hc⟩)

end Gusfield2007
