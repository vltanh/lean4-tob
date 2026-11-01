module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic

/-!
# The Log-det distance

"A similar approach might use the Log-det distance, drawing on results of [6] for ultrametric networks." (ECToBlob, the paper's
text, lines 1433-1434.)

The sentence claims nothing: "might". What it rests on is written here.

* `logDetDist`: the distance from the matrix `F` of joint frequencies of the bases of two taxa, with `f_a`, `f_b` its marginals and
  `g_a`, `g_b` their products: `d = -(1/k) (ln |det F| - (1/2) ln (g_a g_b))` (Steel 1994; [6], Section 2.5).
* `logDetDist_markov`: **additivity at a node that separates two taxa**, under one Markov model on one tree: if `F_xy = F_xu D_u⁻¹ F_uy`,
  then `d(x,y) = d(x,u) + d(u,y)`.
* `logDetDist_path`: additivity along a path, so the distance of a Markov model on a tree is a tree metric.
* `sumOfPairs_logDet`: on a tree `ab|cd` with internal nodes `u`, `v`, this gives `SP_ac|bd = SP_ad|bc = SP_ab|cd + 2 d(u,v)`, and on a
  star, equal sums. These are the shapes that `ECToBlob.SumOfPairs.SPForward` asks.
* `not_logDet_additive_mixture`: **additivity fails for a mixture**. The model of [6] is a mixture over gene trees and substitution
  classes, whose `F` is a convex combination of such matrices, so it is not tree-additive: [6] uses instead the equalities and
  inequalities of distances between three taxa on an ultrametric network (its Propositions 3 to 5), under hypotheses and with a
  proof (its Lemma 9 and Proposition 2) that this file does not cover. So the sentence's "similar approach" would run on rooted
  triples, not on the four-point condition.

The positivity `0 < d(u,v)` is a hypothesis of a strict inequality on the tree, and it is not proved here: Mathlib has no Hadamard
determinant inequality.

## References

* M. Steel, *Recovering a tree from the leaf colourations it generates under a Markov model*, Appl. Math. Lett. 7 (1994), 19-24.
  Not read: the definition is quoted from [6] and from Rhodes, Baños, Xu, Ané 2025, Section 6.3, both read.
* E. S. Allman, H. Baños, J. A. Rhodes, *Identifiability of species network topologies from genomic sequences using the logDet
  distance*, J. Math. Biol. 84 (2022), 35: read in its arXiv version.
-/

@[expose] public noncomputable section

open Finset Matrix

namespace ECToBlob.LogDet

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The sums of the rows of a matrix: the marginal of the first taxon. -/
def rowSum (F : Matrix n n ℝ) (i : n) : ℝ := ∑ j, F i j

/-- The sums of the columns of a matrix: the marginal of the second taxon. -/
def colSum (F : Matrix n n ℝ) (j : n) : ℝ := ∑ i, F i j

/-- **The Log-det distance** of a matrix of joint frequencies: `-(1/k) (ln |det F| - (1/2) ln (g_a g_b))`, for `k` bases. -/
def logDetDist (F : Matrix n n ℝ) : ℝ :=
  -(1 / (Fintype.card n : ℝ)) *
    (Real.log |F.det| - (1 / 2) * Real.log ((∏ i, rowSum F i) * ∏ j, colSum F j))

/-- `F_xu D_u⁻¹ F_uy`: the joint frequencies of `x`, `y`, under a Markov model with `u` on the path between them, and `f` the
frequencies at `u`. -/
def compose (F : Matrix n n ℝ) (f : n → ℝ) (G : Matrix n n ℝ) : Matrix n n ℝ :=
  F * diagonal (fun k => (f k)⁻¹) * G

variable {F G : Matrix n n ℝ} {f : n → ℝ}

theorem compose_apply (F : Matrix n n ℝ) (f : n → ℝ) (G : Matrix n n ℝ) (i j : n) :
    compose F f G i j = ∑ k, F i k * (f k)⁻¹ * G k j := by
  unfold compose
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]

theorem rowSum_compose (hf : ∀ k, f k ≠ 0) (hG : rowSum G = f) : rowSum (compose F f G) = rowSum F := by
  funext i
  unfold rowSum
  simp only [compose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum]
  have : ∑ j, G k j = f k := congrFun hG k
  rw [this]
  field_simp [hf k]

theorem colSum_compose (hf : ∀ k, f k ≠ 0) (hF : colSum F = f) : colSum (compose F f G) = colSum G := by
  funext j
  unfold colSum
  simp only [compose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have : ∑ i, F i k = f k := congrFun hF k
  rw [this]
  field_simp [hf k]

/-- **Additivity at a separating node**: under a Markov model, `d(x,y) = d(x,u) + d(u,y)`, where `f` is the frequencies at `u`, the
marginal of both matrices. -/
theorem logDetDist_markov (hf : ∀ k, 0 < f k) (hF : colSum F = f) (hG : rowSum G = f)
    (hF₀ : F.det ≠ 0) (hG₀ : G.det ≠ 0) (hr : ∀ i, 0 < rowSum F i) (hc : ∀ j, 0 < colSum G j) :
    logDetDist (compose F f G) = logDetDist F + logDetDist G := by
  have hf₀ : ∀ k, f k ≠ 0 := fun k => (hf k).ne'
  have hprod : 0 < ∏ k, f k := Finset.prod_pos fun k _ => hf k
  have hgr : 0 < ∏ i, rowSum F i := Finset.prod_pos fun i _ => hr i
  have hgc : 0 < ∏ j, colSum G j := Finset.prod_pos fun j _ => hc j
  have hdet : (compose F f G).det = F.det * (∏ k, f k)⁻¹ * G.det := by
    unfold compose
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_inv_distrib]
  have hcF : ∏ j, colSum F j = ∏ k, f k := by rw [hF]
  have hrG : ∏ i, rowSum G i = ∏ k, f k := by rw [hG]
  unfold logDetDist
  rw [rowSum_compose hf₀ hG, colSum_compose hf₀ hF, hdet, abs_mul, abs_mul, abs_inv, abs_of_pos hprod, hcF, hrG,
    Real.log_mul (mul_ne_zero (abs_ne_zero.2 hF₀) (inv_ne_zero hprod.ne')) (abs_ne_zero.2 hG₀),
    Real.log_mul (abs_ne_zero.2 hF₀) (inv_ne_zero hprod.ne'), Real.log_inv,
    Real.log_mul hgr.ne' hgc.ne', Real.log_mul hgr.ne' hprod.ne', Real.log_mul hprod.ne' hgc.ne']
  ring

/-! ### A Markov model on a tree -/

section Model

variable {U : Type*}

/-- **What a Markov model on a tree gives**: matrices `F x y` of joint frequencies for the nodes `U`, with the frequencies `f u` at
each node as their marginals, and nonzero determinants. `Sep u x y` says that `u` is on the path from `x` to `y`: then the Markov
property gives `F x y = F x u D_u⁻¹ F u y`. -/
structure MarkovData (F : U → U → Matrix n n ℝ) (f : U → n → ℝ) : Prop where
  pos : ∀ u k, 0 < f u k
  row : ∀ x y, rowSum (F x y) = f x
  col : ∀ x y, colSum (F x y) = f y
  det : ∀ x y, (F x y).det ≠ 0
  symm : ∀ x y, F y x = (F x y)ᵀ

/-- `u` separates `x` from `y`: the Markov property at `u`. -/
def Sep (F : U → U → Matrix n n ℝ) (f : U → n → ℝ) (u x y : U) : Prop :=
  F x y = compose (F x u) (f u) (F u y)

variable {F : U → U → Matrix n n ℝ} {f : U → n → ℝ}

omit [DecidableEq n] in
/-- The Log-det distance is symmetric. -/
theorem logDetDist_transpose [DecidableEq n] (G : Matrix n n ℝ) : logDetDist Gᵀ = logDetDist G := by
  unfold logDetDist
  have h₁ : ∀ i, rowSum Gᵀ i = colSum G i := fun _ => rfl
  have h₂ : ∀ j, colSum Gᵀ j = rowSum G j := fun _ => rfl
  simp only [h₁, h₂, Matrix.det_transpose, mul_comm (∏ i, colSum G i)]

/-- The distance of a Markov model on a tree is additive at a node on the path between two nodes. -/
theorem logDetDist_sep (h : MarkovData F f) {u x y : U} (hs : Sep F f u x y) :
    logDetDist (F x y) = logDetDist (F x u) + logDetDist (F u y) := by
  rw [hs]
  exact logDetDist_markov (h.pos u) (h.col x u) (h.row u y) (h.det x u) (h.det u y)
    (fun i => by rw [h.row]; exact h.pos x i) (fun j => by rw [h.col]; exact h.pos y j)

/-- The nodes of the list separate, in turn, what is before them from the end of the path. -/
def PathSep (F : U → U → Matrix n n ℝ) (f : U → n → ℝ) : U → List U → U → Prop
  | _, [], _ => True
  | x, u :: p, y => Sep F f u x y ∧ PathSep F f u p y

/-- The sum of the distances of the edges of a path. -/
def pathLength (F : U → U → Matrix n n ℝ) : U → List U → U → ℝ
  | x, [], y => logDetDist (F x y)
  | x, u :: p, y => logDetDist (F x u) + pathLength F u p y

/-- (`ecto:sec10_logdet_path`) **Tree additivity**: along a path, the distance is the sum of the distances of the edges. So the distance of a Markov model on a
tree is a tree metric, with these edge lengths. -/
theorem logDetDist_path (h : MarkovData F f) (x : U) (p : List U) (y : U) (hp : PathSep F f x p y) :
    logDetDist (F x y) = pathLength F x p y := by
  induction p generalizing x with
  | nil => rfl
  | cons u p ih =>
    rw [logDetDist_sep h hp.1, pathLength, ih u hp.2]

/-- **The four-point shapes on a tree `ab|cd`** with internal nodes `u`, `v`: the node `u` separates `a`, `b` from all else, and `v`
separates `c`, `d`. Then `SP_ac|bd = SP_ad|bc = SP_ab|cd + 2 d(u,v)`. -/
theorem sumOfPairs_logDet (h : MarkovData F f) {a b c d u v : U}
    (hab : Sep F f u a b) (hcd : Sep F f v c d) (hac₁ : Sep F f u a c) (hac₂ : Sep F f v u c)
    (hbd₁ : Sep F f u b d) (hbd₂ : Sep F f v u d) (had₁ : Sep F f u a d) (hbc₁ : Sep F f u b c) :
    logDetDist (F a c) + logDetDist (F b d) =
        logDetDist (F a b) + logDetDist (F c d) + 2 * logDetDist (F u v) ∧
      logDetDist (F a d) + logDetDist (F b c) =
        logDetDist (F a b) + logDetDist (F c d) + 2 * logDetDist (F u v) := by
  have hsym : logDetDist (F u c) = logDetDist (F u v) + logDetDist (F v c) := logDetDist_sep h hac₂
  have hsym' : logDetDist (F u d) = logDetDist (F u v) + logDetDist (F v d) := logDetDist_sep h hbd₂
  have hs : ∀ x y, logDetDist (F y x) = logDetDist (F x y) := fun x y => by
    rw [h.symm x y, logDetDist_transpose]
  rw [logDetDist_sep h hab, logDetDist_sep h hcd, logDetDist_sep h hac₁, logDetDist_sep h hbd₁,
    logDetDist_sep h had₁, logDetDist_sep h hbc₁, hsym, hsym']
  constructor <;> linarith [hs u b, hs c v, hs v c, hs d v, hs v d, hs b u]

/-- **On a star at `u`**, the three sums of pairs are equal. -/
theorem sumOfPairs_logDet_star (h : MarkovData F f) {a b c d u : U} (hab : Sep F f u a b)
    (hcd : Sep F f u c d) (hac : Sep F f u a c) (hbd : Sep F f u b d) (had : Sep F f u a d)
    (hbc : Sep F f u b c) :
    logDetDist (F a b) + logDetDist (F c d) = logDetDist (F a c) + logDetDist (F b d) ∧
      logDetDist (F a c) + logDetDist (F b d) = logDetDist (F a d) + logDetDist (F b c) := by
  have hs : ∀ x y, logDetDist (F y x) = logDetDist (F x y) := fun x y => by
    rw [h.symm x y, logDetDist_transpose]
  rw [logDetDist_sep h hab, logDetDist_sep h hcd, logDetDist_sep h hac, logDetDist_sep h hbd,
    logDetDist_sep h had, logDetDist_sep h hbc]
  constructor <;> linarith [hs u b, hs u c, hs u d, hs b u, hs c u, hs d u]

end Model

/-! ### A mixture is not additive -/

/-- The symmetric joint frequencies on two bases with uniform marginals, of determinant `t / 4`. -/
def twoState (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 + t) / 4, (1 - t) / 4; (1 - t) / 4, (1 + t) / 4]

/-- Composition multiplies the parameters. -/
theorem compose_twoState (s t : ℝ) : compose (twoState s) (fun _ => 1 / 2) (twoState t) = twoState (s * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compose, twoState, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The distance of `twoState t` is `-(1/2) ln |t|`. -/
theorem logDetDist_twoState {t : ℝ} (ht : t ≠ 0) : logDetDist (twoState t) = -(1 / 2) * Real.log |t| := by
  have hrow : ∀ i, rowSum (twoState t) i = 1 / 2 := by
    intro i
    fin_cases i <;> simp [rowSum, twoState, Fin.sum_univ_two] <;> ring
  have hcol : ∀ j, colSum (twoState t) j = 1 / 2 := by
    intro j
    fin_cases j <;> simp [colSum, twoState, Fin.sum_univ_two] <;> ring
  have hdet : (twoState t).det = t / 4 := by
    simp only [twoState, Matrix.det_fin_two_of]
    ring
  unfold logDetDist
  simp only [hrow, hcol, hdet, Fin.prod_univ_two, Fintype.card_fin]
  have h₄ : |t / 4| = |t| / 4 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [h₄, Real.log_div (abs_ne_zero.2 ht) (by norm_num)]
  have h₁ : Real.log (1 / 2 * (1 / 2) * (1 / 2 * (1 / 2))) = -2 * Real.log 4 := by
    rw [show (1 / 2 * (1 / 2) * (1 / 2 * (1 / 2)) : ℝ) = (4 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    push_cast
    ring
  rw [h₁]
  push_cast
  ring

/-- (`ecto:sec10_logdet_mixture`) **A mixture is not additive.** Take the path `x — u — y` under two Markov models, with parameters `1`, `1` on its two edges and
`1/2`, `1/2`, in equal proportions. The matrices of joint frequencies of the mixture are `twoState (3/4)` on each edge, and
`twoState (5/8)` from end to end, and the Log-det distance is not additive: `(3/4)² ≠ 5/8`. So the distance from concatenated
sequences under a mixture of trees, the model of [6], need not be a tree metric, on a tree. -/
theorem not_logDet_additive_mixture :
    (1 / 2 : ℝ) • twoState 1 + (1 / 2 : ℝ) • twoState (1 / 2) = twoState (3 / 4) ∧
      (1 / 2 : ℝ) • compose (twoState 1) (fun _ => 1 / 2) (twoState 1) +
        (1 / 2 : ℝ) • compose (twoState (1 / 2)) (fun _ => 1 / 2) (twoState (1 / 2)) = twoState (5 / 8) ∧
      logDetDist (twoState (5 / 8)) ≠ logDetDist (twoState (3 / 4)) + logDetDist (twoState (3 / 4)) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [twoState] <;> norm_num
  · rw [compose_twoState, compose_twoState]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twoState] <;> norm_num
  · rw [logDetDist_twoState (by norm_num), logDetDist_twoState (by norm_num)]
    intro h
    have hab : |(5 / 8 : ℝ)| = 5 / 8 := abs_of_pos (by norm_num)
    have hab' : |(3 / 4 : ℝ)| = 3 / 4 := abs_of_pos (by norm_num)
    rw [hab, hab'] at h
    have h₂ : Real.log (5 / 8) = Real.log ((3 / 4) * (3 / 4)) := by
      rw [Real.log_mul (by norm_num) (by norm_num)]
      linarith
    have := Real.log_injOn_pos (Set.mem_Ioi.2 (by norm_num)) (Set.mem_Ioi.2 (by norm_num)) h₂
    norm_num at this

end ECToBlob.LogDet
