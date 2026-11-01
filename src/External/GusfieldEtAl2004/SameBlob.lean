module

public import Gusfield2007.Defs

/-!
# Sites of one component lie on one blob (Gusfield, Eddhu, Langley 2004)

Stated with `sorry`. See the `README.md` of this directory.
-/

@[expose] public section

open scoped Classical

namespace GusfieldEtAl2004

open Gusfield2007

variable {ι V E : Type*} [Finite V] [Finite E]

/-- **Gusfield, Eddhu, Langley 2004** (`ext:same_blob`). Two sites incompatible in a set of sequences that label nodes of `N` are on one blob. This doesn't depend on the
number of crossovers. -/
theorem exists_isBlob_of_incompatible (N : Network ι V E) {L : Finset (ι → Bool)}
    (hL : ∀ r ∈ L, ∃ v, N.label v = r) {i j : ι} (h : Incompatible L i j) :
    ∃ B, N.IsBlob B ∧ N.site i ∈ B ∧ N.site j ∈ B := by
  sorry

end GusfieldEtAl2004
