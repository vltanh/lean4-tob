module

public import Gusfield2007.Blobs
public import Gusfield2007.NetworkOps

/-!
# Sites of one component lie on one blob (Gusfield, Eddhu, Langley 2004)

See the `README.md` of this directory. The source proves that two sites in conflict are together on a recombination cycle (the
"general fact" in the proof of its Theorem 2.2). Gusfield et al. 2007 cite only that they're on one blob, which is proved here.
-/

@[expose] public section

open scoped Classical

namespace GusfieldEtAl2004

open Gusfield2007 Gusfield2007.Network

variable {ι V E : Type*} {N : Network ι V E} [Finite V]

/-- A node with the state of the root at `i` is reached from the root through such nodes. -/
theorem exists_path_unflipped (i : ι) (v : V) (hv : N.label v i = N.label N.root i) :
    ∃ p, N.IsPath N.root v p ∧ ∀ g ∈ p, N.label (N.tgt g) i = N.label N.root i := by
  revert hv
  refine N.arc_induction (P := fun v => N.label v i = N.label N.root i →
    ∃ p, N.IsPath N.root v p ∧ ∀ g ∈ p, N.label (N.tgt g) i = N.label N.root i) (fun v ih hv => ?_) v
  by_cases hroot : v = N.root
  · exact ⟨[], hroot.symm, by simp⟩
  obtain ⟨g', hg', hs⟩ := N.exists_parent_label_eq hroot fun htop => N.label_tgt_site_ne i (htop ▸ hv)
  obtain ⟨p, hp, hall⟩ := ih g' hg' (hs.trans hv)
  refine ⟨p ++ [g'], hp.append ⟨rfl, hg'⟩, fun h hh => ?_⟩
  rcases List.mem_append.1 hh with h₁ | h₁
  · exact hall h h₁
  · rw [List.mem_singleton.1 h₁, hg']
    exact hv

/-- A node with the other state at `i` is reached from the target of the arc of `i` through such nodes. -/
theorem exists_path_flipped (i : ι) (v : V) (hv : N.label v i ≠ N.label N.root i) :
    ∃ p, N.IsPath (N.tgt (N.site i)) v p ∧ ∀ g ∈ p, N.label (N.src g) i ≠ N.label N.root i := by
  revert hv
  refine N.arc_induction (P := fun v => N.label v i ≠ N.label N.root i →
    ∃ p, N.IsPath (N.tgt (N.site i)) v p ∧ ∀ g ∈ p, N.label (N.src g) i ≠ N.label N.root i) (fun v ih hv => ?_) v
  by_cases htop : v = N.tgt (N.site i)
  · exact ⟨[], htop.symm, by simp⟩
  obtain ⟨g', hg', hs⟩ := N.exists_parent_label_eq (fun hroot => hv (by rw [hroot])) htop
  obtain ⟨p, hp, hall⟩ := ih g' hg' (hs ▸ hv)
  refine ⟨p ++ [g'], hp.append ⟨rfl, hg'⟩, fun h hh => ?_⟩
  rcases List.mem_append.1 hh with h₁ | h₁
  · exact hall h h₁
  · rw [List.mem_singleton.1 h₁, hs]
    exact hv

/-- The parent `src e` of a recombination node has the other state at `i`, and the parent `src f` the state of the root: tracing the two states up gives
a recombination cycle through the arc of `i`, and `e`, `f`. -/
theorem exists_isCycle_of_flipped {e f : E} (hef : e ≠ f) (ht : N.tgt e = N.tgt f) {i : ι}
    (he : N.label (N.src e) i ≠ N.label N.root i) (hf : N.label (N.src f) i = N.label N.root i) :
    ∃ Q, N.IsCycle Q ∧ e ∈ Q ∧ f ∈ Q ∧ N.site i ∈ Q := by
  obtain ⟨P₁, hP₁⟩ := Reach.exists_isPath (N.reach_root (N.src (N.site i)))
  obtain ⟨pf, hpf, hpfall⟩ := exists_path_flipped (N := N) i _ he
  obtain ⟨pu, hpu, hpuall⟩ := exists_path_unflipped (N := N) i _ hf
  have hC : N.IsPath (N.tgt (N.site i)) (N.tgt e) (pf ++ [e]) := hpf.append ⟨rfl, rfl⟩
  have hB : N.IsPath N.root (N.tgt e) (pu ++ [f]) := hpu.append ⟨rfl, ht.symm⟩
  have hCsrc : ∀ g ∈ pf ++ [e], N.label (N.src g) i ≠ N.label N.root i := fun g hg => by
    rcases List.mem_append.1 hg with h | h
    · exact hpfall g h
    · rw [List.mem_singleton.1 h]
      exact he
  have heB : N.site i ∉ pu ++ [f] := fun h => by
    rcases List.mem_append.1 h with h | h
    · exact N.label_tgt_site_ne i (hpuall _ h)
    · have hsf : N.site i = f := List.mem_singleton.1 h
      have : e = N.site i := N.site_not_recomb i e (by rw [hsf, ht])
      exact hef (this.trans hsf)
  have hC' : ∀ g ∈ pf ++ [e], N.src g ∉ pathVerts N N.root (pu ++ [f]) := by
    intro g hg hmem
    have hsrc := hCsrc g hg
    rcases List.mem_cons.1 hmem with h | h
    · rw [h] at hsrc
      exact hsrc rfl
    · obtain ⟨h', hh', hgh⟩ := List.mem_map.1 h
      rcases List.mem_append.1 hh' with h₁ | h₁
      · rw [← hgh] at hsrc
        exact hsrc (hpuall _ h₁)
      · have hfh : h' = f := List.mem_singleton.1 h₁
        have hgx : N.src g = N.tgt e := by rw [← hgh, hfh, ht]
        obtain ⟨_, r, -, -, hr⟩ := hC.split hg
        exact not_reach_tgt_src g (hgx ▸ hr.reach)
  obtain ⟨w, -, P₁₂, B₁, q, -, hBq, hq, -, -, hcyc⟩ := exists_isCycleOn_core hP₁ hC hB heB hC'
  refine ⟨_, ⟨w, N.tgt e, _, q, hcyc, rfl⟩, Or.inl (by simp), Or.inr ?_, Or.inl (by simp)⟩
  -- `f` is the last arc of `q`
  obtain ⟨q', z, rfl⟩ := List.eq_nil_or_concat' q |>.resolve_left hq
  have hz : z = f := by
    have := congrArg List.getLast? hBq
    simp only [← List.append_assoc, List.getLast?_append, List.getLast?_singleton, Option.some_or] at this
    exact (Option.some.inj this).symm
  simp [hz]

/-- Parents of a recombination node with different states at `i`: a recombination cycle through the arc of `i`, and both arcs into the node. -/
theorem exists_isCycle_of_label_ne {e f : E} (hef : e ≠ f) (ht : N.tgt e = N.tgt f) {i : ι}
    (h : N.label (N.src e) i ≠ N.label (N.src f) i) : ∃ Q, N.IsCycle Q ∧ e ∈ Q ∧ f ∈ Q ∧ N.site i ∈ Q := by
  by_cases he : N.label (N.src e) i = N.label N.root i
  · have hf : N.label (N.src f) i ≠ N.label N.root i := fun hf => h (he.trans hf.symm)
    obtain ⟨Q, h₁, h₂, h₃, h₄⟩ := exists_isCycle_of_flipped hef.symm ht.symm hf he
    exact ⟨Q, h₁, h₃, h₂, h₄⟩
  · have hf : N.label (N.src f) i = N.label N.root i := by
      revert h he
      cases N.label (N.src e) i <;> cases N.label (N.src f) i <;> cases N.label N.root i <;> simp
    exact exists_isCycle_of_flipped hef ht he hf

/-- **Gusfield, Eddhu, Langley 2004** (`ext:same_blob`). Two sites incompatible in a set of sequences that label nodes of `N` are on one blob. This doesn't depend on the
number of crossovers.

The source (the proof of its Theorem 2.2) removes the other sites, contracts edges, and at each recombination node deletes one arc, to reach a perfect phylogeny on the two sites, which has
no conflict. It claims, without proof, that an arc can be deleted so that the leaves keep their labels, and it concludes that the sites are on one cycle.

Departure from the source: the network isn't changed, and the claim isn't needed. A recombination node that is a copy of a parent on `{i, j}` is where the source's deletion is possible. If
every recombination node is such a copy, then the states at `i`, `j` are those of a perfect phylogeny, and only three pairs occur (`Network.exists_breaksAt_of_incompatible`), which is the
source's conclusion. If not, a node `x` breaks `{i, j}`, and its parents differ at both sites: tracing the states up gives a cycle through the arc of `i` and both arcs into `x`, and another
through the arc of `j` (`exists_isCycle_of_label_ne`). The two cycles share an arc, which gives "one blob", the form that Gusfield et al. 2007 cite. The source's stronger "one cycle" isn't
proved. -/
theorem exists_isBlob_of_incompatible (N : Network ι V E) {L : Finset (ι → Bool)}
    (hL : ∀ r ∈ L, ∃ v, N.label v = r) {i j : ι} (h : Incompatible L i j) :
    ∃ B, N.IsBlob B ∧ N.site i ∈ B ∧ N.site j ∈ B := by
  obtain ⟨x, ⟨e, f, hef, he, hf⟩, hb⟩ := N.exists_breaksAt_of_incompatible hL h
  have hrow : ∀ g, N.tgt g = x → ¬ (N.label x i = N.label (N.src g) i ∧ N.label x j = N.label (N.src g) j) := by
    rintro g hg ⟨h₁, h₂⟩
    refine hb g hg (funext ?_)
    rintro ⟨k, rfl | rfl⟩
    · exact h₁
    · exact h₂
  have ht : N.tgt e = N.tgt f := he.trans hf.symm
  have hi := N.label_recomb e f hef ht i
  have hj := N.label_recomb e f hef ht j
  rw [he] at hi hj
  have hne : N.label (N.src e) i ≠ N.label (N.src f) i ∧ N.label (N.src e) j ≠ N.label (N.src f) j := by
    have h₁ := hrow e he
    have h₂ := hrow f hf
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact absurd ⟨hi, hj⟩ h₁
    · exact ⟨fun hc => h₂ ⟨hi.trans hc, hj⟩, fun hc => h₁ ⟨hi, hj.trans hc.symm⟩⟩
    · exact ⟨fun hc => h₁ ⟨hi.trans hc.symm, hj⟩, fun hc => h₂ ⟨hi, hj.trans hc⟩⟩
    · exact absurd ⟨hi, hj⟩ h₂
  obtain ⟨Qi, hQi, heQi, -, hsi⟩ := exists_isCycle_of_label_ne hef ht hne.1
  obtain ⟨Qj, hQj, heQj, -, hsj⟩ := exists_isCycle_of_label_ne hef ht hne.2
  obtain ⟨B, hB, heB⟩ := N.exists_isBlob_of_onCycle ⟨Qi, hQi, heQi⟩
  exact ⟨B, hB, hB.subset_of_mem hQi heB heQi hsi, hB.subset_of_mem hQj heB heQj hsj⟩

end GusfieldEtAl2004
