module

public import Gusfield2007.Defs

/-!
# The haplotype bound of Myers and Griffiths

Stated with `sorry`. See the `README.md` of this directory.
-/

@[expose] public section

open scoped Classical

namespace MyersGriffiths2003

open Gusfield2007

variable {ι : Type*} [LinearOrder ι] [Finite ι]

/-- **The haplotype bound** (`ext:haplotype_bound`): `H(M) ≤ R(M)`, and so `H(M) ≤ R¹(M)` (Gusfield et al., line 559). -/
theorem haplotypeBound_le_R (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) :
    haplotypeBound M ≤ R c M := by
  sorry

/-- **The equality case of the haplotype bound** (`ext:haplotype_equality`) (Gusfield et al., lines 560 to 564), when the columns of `M + S` are
distinct: a network for `M` with ancestral sequence `S` and `H(M + S)` recombination nodes has every node visible. The
printed sentence has no hypothesis on the columns, and is false without it. -/
theorem allVisible_of_eq {V E : Type*} [Finite V] [Finite E] (N : Network ι V E) {M : Finset (ι → Bool)}
    {S : ι → Bool} (hd : N.Derives M) (hS : N.ancestral = S)
    (hinj : Function.Injective fun i : ι => fun r : addRow M S => (r : ι → Bool) i)
    (h : (N.recombCount : ℤ) = haplotypeBound (addRow M S)) : N.AllVisible M S := by
  sorry

end MyersGriffiths2003
