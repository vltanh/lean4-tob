module

public import Basic.Phylogenetics.NetworkCuts

/-!
# Networks with hybrid arcs deleted

Allman, Baños, Mitchell, Rhodes 2023 prove their Theorem 1 at boundary parameters: an inheritance
probability `0` effectively deletes a hybrid arc. So this file keeps the network and its vertices, and
reads reachability, domination and cut splits off a set `D` of deleted arcs. For `D = ∅` these are the
notions of `Basic/Phylogenetics/NetworkCuts.lean` (`reachesOff_empty_iff`, `dominatesOff_empty_iff`,
`isBelowOff_empty_iff`).
-/

@[expose] public section

open Finset

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} (N : RootedNetwork V E X) (D : Set E)

/-- `u` reaches `v` along arcs outside `D`. -/
def ReachesOff : V → V → Prop :=
  Relation.ReflTransGen fun a b => ∃ f, f ∉ D ∧ N.graph.source f = a ∧ N.graph.target f = b

/-- With the arcs `D` deleted, every directed path from the root to the taxon `x` uses the arc `e`. -/
def DominatesOff (e : E) (x : X) : Prop := ¬ N.ReachesOff (insert e D) N.root (N.leaf x)

/-- With the arcs `D` deleted, the taxon `x` is below the arc `e`. -/
def IsBelowOff (e : E) (x : X) : Prop := e ∉ D ∧ N.ReachesOff D (N.graph.target e) (N.leaf x)

/-- With the arcs `D` deleted, the arc `e` dominates all taxa of `P`, and no taxon of `Q` is below it. -/
def SeparatesOff (e : E) (P Q : Set X) : Prop :=
  (∀ x ∈ P, N.DominatesOff D e x) ∧ ∀ x ∈ Q, ¬ N.IsBelowOff D e x

/-- `D` deletes only hybrid arcs, and leaves every non-root vertex a parent. Then every vertex is
still reached from the root. -/
structure IsDeletion : Prop where
  hybrid : ∀ e ∈ D, N.IsHybridArc e
  parent : ∀ v, v ≠ N.root → ∃ f, f ∉ D ∧ N.graph.target f = v

variable [Fintype X] [DecidableEq X]

/-- With the arcs `D` deleted, the arc `e` induces the split of the quartet tree `s`. -/
def SplitOffAt (e : E) (s : QuartetTree X) : Prop :=
  ∃ P ∈ s.val, N.SeparatesOff D e (P : Set X) ((s.taxa \ P : Finset X) : Set X)

variable {N D}

omit [Fintype X] [DecidableEq X] in
theorem reachesOff_empty_iff {u v : V} : N.ReachesOff ∅ u v ↔ N.graph.Reaches u v := by
  have h : (fun a b => ∃ f, f ∉ (∅ : Set E) ∧ N.graph.source f = a ∧ N.graph.target f = b) =
      N.graph.Adj := by
    funext a b
    simp [DirectedMultigraph.Adj]
  simp only [ReachesOff, DirectedMultigraph.Reaches, h]

omit [Fintype X] [DecidableEq X] in
theorem dominatesOff_empty_iff {e : E} {x : X} : N.DominatesOff ∅ e x ↔ N.Dominates e x := by
  have h : (fun a b => ∃ f, f ∉ (insert e ∅ : Set E) ∧ N.graph.source f = a ∧ N.graph.target f = b) =
      fun a b => ∃ f, f ≠ e ∧ N.graph.source f = a ∧ N.graph.target f = b := by
    funext a b
    simp
  simp only [DominatesOff, Dominates, ReachesOff, AvoidingReach, h]

omit [Fintype X] [DecidableEq X] in
theorem isBelowOff_empty_iff {e : E} {x : X} : N.IsBelowOff ∅ e x ↔ N.IsBelow e x := by
  simp [IsBelowOff, IsBelow, reachesOff_empty_iff]

end Phylogenetics.RootedNetwork
