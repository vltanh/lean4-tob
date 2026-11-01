module

public import Gusfield2007.Defs
public import Gusfield2007.TimeOrdered

/-!
# The bound of Song and Hein by ordered-SPR operations

Stated with `sorry`. See the `README.md` of this directory.
-/

@[expose] public section

open scoped Classical

namespace SongHein2005

open Gusfield2007

/-- **The fact of Song and Hein 2005** (`ext:song_hein`) (Gusfield et al., line 654): "if `P = T_1, T_2, ..., T_m` is a sequence of time-ordered leaf-labeled trees in which `T_i` is compatible with site `i`
in `M`, for all `i`, then `R¹(M) ≤ L(P)`". -/
theorem R_le_sprLength {m : ℕ} (M : Finset (Fin m → Bool)) (hM : M.Nonempty) (P : Fin m → TimeOrderedTree M)
    (hP : ∀ i, (P i).CompatibleWith fun r => (r : Fin m → Bool) i) :
    (R .single M : ℕ∞) ≤ sprLength (List.ofFn P) := by
  sorry

end SongHein2005
