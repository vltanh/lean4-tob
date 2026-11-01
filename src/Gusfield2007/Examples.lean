module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.List.GetD

/-!
# Gusfield et al. 2007: the matrices of the figures

The matrices of Figures 5, 6 and 8 and the matrix `M_d` of Theorem 11, as printed. Sites are numbered from 1 in the paper and
from 0 here. They are computable, with no classical instance, so that facts about them can be decided.
-/

@[expose] public section

namespace Gusfield2007

/-- A row, from its bits. -/
def ofBits {m : ℕ} (l : List ℕ) : Fin m → Bool := fun i => l.getD i 0 == 1

/-- The matrix of Figures 1, 2 and 3: the rows `a, b, c, d, e, f, g`. -/
def fig1 : Finset (Fin 5 → Bool) :=
  {ofBits [0, 0, 0, 1, 0], ofBits [1, 0, 0, 1, 0], ofBits [0, 0, 1, 0, 0], ofBits [1, 0, 1, 0, 0], ofBits [0, 1, 1, 0, 0], ofBits [0, 1, 1, 0, 1], ofBits [0, 0, 1, 0, 1]}

/-- The component `C` of Figure 3: the sites 1, 3, 4 of the paper. -/
def fig1C : Set (Fin 5) := {i | i = 0 ∨ i = 2 ∨ i = 3}

/-- The matrix of Figure 5. -/
def fig5 : Finset (Fin 8 → Bool) :=
  {ofBits [1, 1, 1, 1, 0, 0, 0, 0], ofBits [1, 1, 0, 0, 0, 0, 0, 0], ofBits [1, 1, 1, 0, 0, 0, 0, 0],
   ofBits [0, 0, 1, 1, 0, 0, 0, 0], ofBits [0, 1, 1, 1, 0, 0, 0, 0], ofBits [0, 0, 0, 0, 1, 1, 1, 1],
   ofBits [0, 0, 0, 0, 1, 1, 0, 0], ofBits [0, 0, 0, 0, 1, 1, 1, 0], ofBits [0, 0, 0, 0, 0, 0, 1, 1],
   ofBits [0, 0, 0, 0, 0, 1, 1, 1]}

/-- The component of Figure 5 with the first four sites. -/
def fig5C₁ : Set (Fin 8) := {i | i.val < 4}

/-- The component of Figure 5 with the last four sites. -/
def fig5C₂ : Set (Fin 8) := {i | 4 ≤ i.val}

/-- The rows of the matrix of Figure 6. -/
def fig6Table : List (List ℕ) :=
  [[0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 1, 0], [0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 1], [1, 0, 0, 0, 0, 1]]

/-- The matrix `M₁` of Figure 6. -/
def fig6 : Finset (Fin 6 → Bool) :=
  (List.finRange 6).toFinset.image fun t : Fin 6 => ofBits (fig6Table.getD t.val [])

/-- The component `C₁` of Figure 6: the sites 2, 3, 5 of the paper. -/
def fig6C₁ : Set (Fin 6) := {1, 2, 4}

/-- The component `C₂` of Figure 6: the sites 1, 4, 6 of the paper. -/
def fig6C₂ : Set (Fin 6) := {0, 3, 5}

/-- The matrix of Figure 8. -/
def fig8 : Finset (Fin 10 → Bool) :=
  {ofBits [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ofBits [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ofBits [1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   ofBits [1, 1, 1, 0, 0, 0, 0, 0, 0, 0], ofBits [0, 1, 0, 1, 0, 0, 0, 0, 0, 0], ofBits [0, 1, 0, 1, 1, 0, 0, 0, 0, 0],
   ofBits [1, 0, 1, 1, 1, 0, 0, 0, 0, 0], ofBits [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ofBits [0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
   ofBits [0, 0, 0, 0, 0, 1, 1, 1, 0, 0], ofBits [0, 0, 0, 0, 0, 0, 1, 0, 1, 0], ofBits [0, 0, 0, 0, 0, 0, 1, 0, 1, 1],
   ofBits [0, 0, 0, 0, 0, 1, 0, 1, 1, 1]}

/-- The component of Figure 8 with the sites 1 through 5 (line 618). -/
def fig8C₁ : Set (Fin 10) := {i | i.val < 5}

/-- The component of Figure 8 with the sites 6 through 10 (line 618). -/
def fig8C₂ : Set (Fin 10) := {i | 5 ≤ i.val}

/-- The matrix `M_d` of Theorem 11: `d` copies of the matrix of Figure 6, side by side (line 635). -/
def Md (d : ℕ) : Finset (Fin (6 * d) → Bool) :=
  (List.finRange 6).toFinset.image fun (t : Fin 6) (j : Fin (6 * d)) =>
    (ofBits (fig6Table.getD t.val []) : Fin 6 → Bool) ⟨j.val % 6, Nat.mod_lt _ (by decide)⟩

/-- The component `C₁` of `G(M_d)`: the columns of type `x` or `y` (line 641). -/
def MdC₁ (d : ℕ) : Set (Fin (6 * d)) := {j | j.val % 6 = 1 ∨ j.val % 6 = 2 ∨ j.val % 6 = 4}

/-- The component `C₂` of `G(M_d)`: the columns of type `u` or `v` (line 641). -/
def MdC₂ (d : ℕ) : Set (Fin (6 * d)) := {j | j.val % 6 = 0 ∨ j.val % 6 = 3 ∨ j.val % 6 = 5}

/-- A smaller counterexample to the multiple-crossover conjecture than Figure 8, with 7 rows and 6 sites against 13 and 10. It isn't in the paper: an independent review of the statements found it. -/
def evenRows : Finset (Fin 6 → Bool) :=
  {ofBits [0, 0, 0, 0, 0, 0], ofBits [0, 0, 0, 0, 1, 1], ofBits [0, 0, 0, 1, 0, 1], ofBits [0, 0, 0, 1, 1, 0], ofBits [0, 1, 1, 0, 0, 0],
   ofBits [1, 0, 1, 0, 0, 0], ofBits [1, 1, 0, 0, 0, 0]}

/-- The component of `evenRows` with the first three sites. -/
def evenC₁ : Set (Fin 6) := {i | i.val < 3}

/-- The component of `evenRows` with the last three sites. -/
def evenC₂ : Set (Fin 6) := {i | 3 ≤ i.val}

/-- The rows `0`, `1` on one site: the shortest counterexample to Theorem 4 as printed. -/
def oneSiteRows : Finset (Fin 1 → Bool) := {fun _ => false, fun _ => true}

/-- The rows `00`, `01`, `10`, `11`: the first counterexample to Theorem 4 as printed. -/
def fourGametes : Finset (Fin 2 → Bool) :=
  {ofBits [0, 0], ofBits [0, 1], ofBits [1, 0], ofBits [1, 1]}

/-- Seven rows, with sites 1, 2 in one component, 3, 4 in another, and 5 compatible: the second counterexample to Theorem 4
as printed. -/
def topRows : Finset (Fin 5 → Bool) :=
  {ofBits [0, 0, 0, 0, 0], ofBits [0, 1, 0, 0, 0], ofBits [1, 0, 0, 0, 0], ofBits [1, 1, 0, 0, 1],
   ofBits [1, 1, 0, 1, 1], ofBits [1, 1, 1, 0, 1], ofBits [1, 1, 1, 1, 1]}

/-- Four rows on four sites, each with a single 1: the counterexample to the sentence of Section 4.2. -/
def starRows : Finset (Fin 4 → Bool) :=
  {ofBits [1, 0, 0, 0], ofBits [0, 1, 0, 0], ofBits [0, 0, 1, 0], ofBits [0, 0, 0, 1]}

/-- The rows `00`, `11`: the counterexample to the sentence at line 560. -/
def twoEqualColumns : Finset (Fin 2 → Bool) := {ofBits [0, 0], ofBits [1, 1]}

end Gusfield2007
