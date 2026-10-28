module

public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.NormNum

/-!
Finite checks for the preliminary source audit. These prove the displayed
arithmetic/counterexamples only, not the papers' network or consistency results.
Taxa 0 and 1 belong to the same block; 2, 3, 4 and 5 are singleton blocks.
-/

@[expose] public section
namespace SourceChecks

/-- Four taxa from distinct blocks of sizes (2,1,1,1,1). -/
def crossBlockQuartets : Finset (Finset (Fin 6)) :=
  (Finset.univ.powersetCard 4).filter (fun q => ¬ (0 ∈ q ∧ 1 ∈ q))

/-- ECToBlob equation (3.3): the actual family has nine four-taxon subsets. -/
theorem actualQuartetCount : crossBlockQuartets.card = 9 := by decide

/-- Two representative tuples, each containing five taxa and hence five quartets. -/
theorem representativeQuartetCount : 2 * Nat.choose 5 4 = 10 := by decide

/-- With all relevant CF entries 1/3, the two sides of printed (3.3) disagree. -/
theorem equation3_3_countingMismatch :
    (crossBlockQuartets.card : ℚ) / 3 = 3 ∧
    (2 * Nat.choose 5 4 : ℚ) / 3 = 10 / 3 ∧ (3 : ℚ) ≠ 10 / 3 := by
  norm_num [actualQuartetCount]

/-- For N=5, exactly four other quartets share three taxa with a fixed quartet. -/
def quartetNeighbours : Finset (Finset (Fin 5)) :=
  (Finset.univ.powersetCard 4).filter
    (fun q => (q ∩ ({0, 1, 2, 3} : Finset (Fin 5))).card = 3)

/-- TINNiK's printed count 4(N−1) gives 16 rather than 4 at N=5. -/
theorem neighbourCountMismatch :
    quartetNeighbours.card = 4 ∧ quartetNeighbours.card ≠ 4 * (5 - 1) := by decide

/-- The clipping in Bon cannot be omitted: min(1,2·3/4) differs from 2·3/4. -/
theorem bonferroniClipping :
    min (1 : ℚ) (2 * (3 / 4)) = 1 ∧
    min (1 : ℚ) (2 * (3 / 4)) ≠ 2 * (3 / 4) := by norm_num

end SourceChecks

#print axioms SourceChecks.actualQuartetCount
#print axioms SourceChecks.representativeQuartetCount
#print axioms SourceChecks.equation3_3_countingMismatch
#print axioms SourceChecks.neighbourCountMismatch
#print axioms SourceChecks.bonferroniClipping
