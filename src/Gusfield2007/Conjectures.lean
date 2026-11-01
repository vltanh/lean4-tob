module

public import Gusfield2007.Uniqueness

/-!
# Gusfield et al. 2007, Section 5.1: the Full-Decomposition Optimality Conjectures

The relations between the four conjectures, the computation of `F` and `F_S`, and the example of Figure 5. The conjectures
themselves are in `Gusfield2007.Defs`, and their refutations in `Gusfield2007.Counterexamples`.
-/

@[expose] public noncomputable section

open scoped Classical

namespace Gusfield2007

universe u

variable {ι : Type u} [LinearOrder ι] [Finite ι]

/-- A fully decomposed network is a network: `R(M) ≤ F(M)`. -/
theorem R_le_F (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) : R c M ≤ F c M := by
  have hne : {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧
      N.IsFullyDecomposedFor (incompatGraph M) ∧ N.recombCount = k}.Nonempty := by
    obtain ⟨a, b, N, h₁, h₂, h₃⟩ := theorem1 c M hM hC
    exact ⟨_, a, b, N, h₁, h₂, h₃, rfl⟩
  obtain ⟨a, b, N, h₁, h₂, -, h₄⟩ := Nat.sInf_mem hne
  exact Nat.sInf_le ⟨a, b, N, h₁, h₂, h₄⟩

/-- A fully decomposed network with ancestral sequence `S` is such a network: `R_S(M) ≤ F_S(M)`. -/
theorem RS_le_FS (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    RS c S M ≤ FS c S M := by
  have hne : {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.IsFullyDecomposedFor (conflictGraph S M) ∧ N.recombCount = k}.Nonempty := by
    obtain ⟨a, b, N, h₁, h₂, h₃, h₄⟩ := theorem1_rooted c M S hM hC
    exact ⟨_, a, b, N, h₁, h₂, h₃, h₄, rfl⟩
  obtain ⟨a, b, N, h₁, h₂, h₃, -, h₅⟩ := Nat.sInf_mem hne
  exact Nat.sInf_le ⟨a, b, N, h₁, h₂, h₃, h₅⟩

/-- **Line 413** (`g:compute_FS`). "Even if `M` is not S-min or S-min-1 decomposable, this method will find the minimum number of
recombination nodes, denoted `F_S(M)` and `F¹_S(M)`, used in any fully decomposed network for `M` with ancestral sequence `S`". -/
theorem FS_eq_sum (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    FS c S M = ∑ᶠ C : (conflictGraph S M).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M) := by
  sorry

/-- **Line 403** (`g:rooted_equiv`). "The rooted conjectures are equivalent to the conjectures that
`R_S(M) = Σ_{C ∈ G_S(M)} R_{S(C)}(M(C))` and `R¹_S(M) = Σ_{C ∈ G_S(M)} R¹_{S(C)}(M(C))`". -/
theorem sMinDecomposable_iff (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    SMinDecomposable c S M ↔
      RS c S M = ∑ᶠ C : (conflictGraph S M).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M) := by
  sorry

/-- **Line 635** (`g:F_ge_sum`). "Clearly, `F¹(M) ≥ Σ_{C ∈ G(M)} R¹(M(C))`". -/
theorem sum_R_le_F (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∑ᶠ C : (incompatGraph M).ConnectedComponent, R c (restrictRows C.supp M) ≤ F c M := by
  sorry

/-- **Line 403** (`g:rooted_implies_unrooted`), one input at a time, in the form that the paper's sentence proves: "letting `S` be the
ancestral sequence that appears in the optimal phylogenetic network using `R(M)` recombination nodes". The hypothesis that `G_S(M)`
has the components of `G(M)` is an addition. Without it, the network that S-min decomposability gives is fully decomposed with
respect to `G_S(M)`, not `G(M)`, and it isn't fully decomposed for `M` if `S` merges components. So line 403, and line 425
("when `M` is S-min decomposable for all `S`, then `M` is min-decomposable"), have a gap on one `M`. Whether the printed form is true on
one `M` is `MinDecomposableOfForallS`, open here. Between the conjectures, the implication holds because the rooted ones are false:
`rootedConjecture_imp_unrootedConjecture`. -/
theorem minDecomposable_of_sMinDecomposable {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool}
    (h : SMinDecomposable c S M) (hopt : RS c S M = R c M)
    (hG : ∀ i j, (conflictGraph S M).Reachable i j ↔ (incompatGraph M).Reachable i j) : MinDecomposable c M := by
  sorry

/-- The sentence at line 425, on one `M`: "when `M` is S-min (respectively S-min-1) decomposable for all `S`, then `M` is
min-decomposable (respectively min-1 decomposable)". Its proof at line 403 has a gap, and we have no counterexample. -/
def MinDecomposableOfForallS (c : Crossover) (M : Finset (ι → Bool)) : Prop :=
  (∀ S, SMinDecomposable c S M) → MinDecomposable c M

/-- **Line 420** (`g:lower_bound_sum`). "When the appropriate conjecture holds for an input `M`, we can also compute lower bounds on `R(M)`,
`R¹(M)` [...] by computing bounds separately for each `M(C)`, adding these bounds together for a valid overall lower bound." -/
theorem sum_R_le_of_minDecomposable {c : Crossover} {M : Finset (ι → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (h : MinDecomposable c M) : ∑ᶠ C : (incompatGraph M).ConnectedComponent, R c (restrictRows C.supp M) ≤ R c M := by
  sorry

section ComputeF

variable {W : Type*}

/-- The cost of the component `C`, for the root placed at the node `v` of `T̄` (line 416). If `v` is on the 1-side of a character
of `C`, its super-character is the ancestral sequence of the blob of `C`, and the cost is a rooted problem; otherwise `v` is the
centre `v_C`, and the ancestral sequence of the blob is free. A non-trivial `C` has at most one such character, by Lemma 4, and a
trivial `C` has cost zero either way. -/
def rootCost (c : Crossover) (M : Finset (ι → Bool)) (T : SimpleGraph W) (φ : M → W) (edge : SuperChar M → Sym2 W) (v : W)
    (C : (incompatGraph M).ConnectedComponent) : ℕ :=
  if h : ∃ (S₀ : C.supp → Bool) (hS₀ : S₀ ∈ restrictRows C.supp M) (r : M),
      charValue (⟨C, ⟨S₀, hS₀⟩⟩ : SuperChar M) r = true ∧ SameSide T (edge ⟨C, ⟨S₀, hS₀⟩⟩) (φ r) v then
    RS c h.choose (restrictRows C.supp M)
  else R c (restrictRows C.supp M)

/-- **Lines 416, 418** (`g:compute_F`). "Even if `M` is not min-decomposable or min-1 decomposable, the procedure above will correctly compute
`F(M)` or `F¹(M)`": the procedure tries each interior node `v` of `T̄` as the root, solves a rooted problem for each component except
the one with centre `v`, and an unrooted one for that. The correctness is said to follow "from Theorem 4 and the fact that placing the root of
`T̄` at a leaf or on the interior of an edge will not reduce the number of required recombinations" (line 418).

Theorem 4 as printed being false, the proof has to go through `theorem4_splits` after moving a network to `IsTreeNormal`, or through
`F_eq_sInf_roots`. When `T̄` has no interior node, the set is empty and `sInf` is `0`, which is right: there's no non-trivial
component. -/
theorem F_eq_sInf_interior (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) [Finite W]
    {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W} (hT : IsTBar M T φ edge) :
    F c M = sInf {k | ∃ v, 2 ≤ (T.neighborSet v).ncard ∧
      k = ∑ᶠ C : (incompatGraph M).ConnectedComponent, rootCost c M T φ edge v C} := by
  sorry

/-- **`g:compute_F_roots`**, a form of `g:compute_F` without `T̄`. A network fully decomposed for `G(M)`, with ancestral sequence `S`, has
`G_S(M)` with the components of `G(M)` by the converse, and for such `S`, `F_S(M)` is the sum. So `F(M)` is the minimum of the sums over such
`S`. -/
theorem F_eq_sInf_roots (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    F c M = sInf {k | ∃ S : ι → Bool, (∀ i j, (conflictGraph S M).Reachable i j ↔ (incompatGraph M).Reachable i j) ∧
      k = ∑ᶠ C : (conflictGraph S M).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M)} := by
  sorry

end ComputeF

end Gusfield2007
