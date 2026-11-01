module

public import Gusfield2007.Defs

/-!
# The Hudson-Kaplan lower bound

Stated with `sorry`. See the `README.md` of this directory.
-/

@[expose] public section

open scoped Classical

namespace HudsonKaplan1985

open Gusfield2007

variable {ι : Type*} [LinearOrder ι] [Finite ι]

/-- **The Hudson-Kaplan bound** (`ext:hudson_kaplan`): a set of pairs of incompatible sites, whose intervals don't overlap (they can share an
endpoint), has at most `R¹(M)` elements. -/
theorem card_le_R (M : Finset (ι → Bool)) (P : Finset (ι × ι)) (hP : ∀ p ∈ P, p.1 < p.2 ∧ Incompatible M p.1 p.2)
    (hd : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1) : P.card ≤ R .single M := by
  sorry

end HudsonKaplan1985
