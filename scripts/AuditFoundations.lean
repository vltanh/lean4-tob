module

public meta import Lean.Elab.Command
import all Basic.Analysis.FiniteOptimization
import all Basic.Analysis.SpecialFunctions.Erf
import all Basic.Combinatorics.DirectedMultigraph
import all Basic.Combinatorics.MultigraphBlobs
import all Basic.Combinatorics.MultigraphConnectivity
import all Basic.Combinatorics.MultigraphCutUniqueness
import all Basic.Phylogenetics.AncestralRestriction
import all Basic.Phylogenetics.ConcordanceFactor
import all Basic.Phylogenetics.Hierarchy
import all Basic.Phylogenetics.HierarchyGraph
import all Basic.Phylogenetics.HierarchyParents
import all Basic.Phylogenetics.Network
import all Basic.Phylogenetics.Quartet
import all Basic.Phylogenetics.Star
import all Basic.Phylogenetics.TreeTopology
import all TINNiK.Statistics.Definitions

/-!
Audit every declaration in the currently implemented libraries, including private
and auxiliary declarations. This is an axiom audit of the current foundations;
it is not the final paper-result, proof-route or Palomar audit. Its structure
follows the invoked formalize-math-paper skill's Audit.lean template.
-/

open Lean Elab Command

namespace FoundationsAudit

meta def libraryModule (m : Name) : Bool :=
  (`Basic).isPrefixOf m || (`TINNiK).isPrefixOf m ||
    (`TOBQMC).isPrefixOf m || (`ECToBlob).isPrefixOf m || (`External).isPrefixOf m

elab "#audit_foundations" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut bad : Array Name := #[]
  for m in env.header.moduleNames, d in env.header.moduleData do
    if libraryModule m then
      for c in d.constNames do
        let axs ← liftCoreM <| collectAxioms c
        checked := checked + 1
        if axs.any (!allowed.contains ·) then
          bad := bad.push c
          logError m!"{c} uses unexpected axioms: {axs}"
  if checked == 0 then throwError "No library declarations were checked."
  if !bad.isEmpty then throwError "{bad.size} declarations failed the axiom audit."
  logInfo m!"Checked {checked} library declarations: standard axioms only. No paper-result completion claim."

end FoundationsAudit

#audit_foundations
