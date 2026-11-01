module

public import Gusfield2007.Blobs
public import Gusfield2007.NetworkOps

/-!
# Sites of one component lie on one blob (Gusfield, Eddhu, Langley 2004)

See the `README.md` of this directory. The source proves that two sites in conflict are together on a recombination cycle (the
"general fact" in the proof of its Theorem 2.2). Gusfield et al. 2007 cite only that they're on one blob (`exists_isBlob_of_incompatible`). The source's form, one cycle, is `exists_isCycle_of_conflict` and
`exists_isCycle_of_incompatible`.
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
through the arc of `j` (`exists_isCycle_of_label_ne`). The two cycles share an arc, which gives "one blob", the form that Gusfield et al. 2007 cite. The source's stronger "one cycle" is
`exists_isCycle_of_incompatible`. -/
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

/-! ### One cycle -/

omit [Finite V] in
/-- On a path along which the arcs start at nodes with the other state at `i`, ending at a node with that state, the arcs end at nodes with that state too. -/
theorem tgt_ne_of_src_ne {i : ι} {u v : V} {p : List E} (hp : N.IsPath u v p) (hall : ∀ g ∈ p, N.label (N.src g) i ≠ N.label N.root i)
    (hv : N.label v i ≠ N.label N.root i) {g : E} (hg : g ∈ p) : N.label (N.tgt g) i ≠ N.label N.root i := by
  rcases hp.tgt_eq_or hg with h | ⟨f, hf, h⟩
  · rwa [h]
  · rw [← h]
    exact hall f hf

/-- The two paths lemma for the arc of a site: a path out of the arc of `j` to the parent `src e` of a recombination node, along nodes with the other state at `j`, and a parent `src f`
with the state of the root at `j`, give a recombination cycle through the arc of `j`, the path, and `e` and `f`. -/
theorem exists_isCycle_of_path_flipped {e f : E} (hef : e ≠ f) (ht : N.tgt e = N.tgt f) {j : ι} {C : List E}
    (hC : N.IsPath (N.tgt (N.site j)) (N.src e) C) (hall : ∀ g ∈ C, N.label (N.src g) j ≠ N.label N.root j)
    (he : N.label (N.src e) j ≠ N.label N.root j) (hf : N.label (N.src f) j = N.label N.root j) :
    ∃ Q, N.IsCycle Q ∧ N.site j ∈ Q ∧ (∀ g ∈ C, g ∈ Q) ∧ e ∈ Q := by
  obtain ⟨P₁, hP₁⟩ := Reach.exists_isPath (N.reach_root (N.src (N.site j)))
  obtain ⟨pu, hpu, hpuall⟩ := exists_path_unflipped (N := N) j _ hf
  have hC₂ : N.IsPath (N.tgt (N.site j)) (N.tgt e) (C ++ [e]) := hC.append ⟨rfl, rfl⟩
  have hB : N.IsPath N.root (N.tgt e) (pu ++ [f]) := hpu.append ⟨rfl, ht.symm⟩
  have hsrc : ∀ g ∈ C ++ [e], N.label (N.src g) j ≠ N.label N.root j := fun g hg => by
    rcases List.mem_append.1 hg with h | h
    · exact hall g h
    · rw [List.mem_singleton.1 h]
      exact he
  have heB : N.site j ∉ pu ++ [f] := fun h => by
    rcases List.mem_append.1 h with h | h
    · exact N.label_tgt_site_ne j (hpuall _ h)
    · have hsf : N.site j = f := List.mem_singleton.1 h
      have : e = N.site j := N.site_not_recomb j e (by rw [hsf, ht])
      exact hef (this.trans hsf)
  have hC' : ∀ g ∈ C ++ [e], N.src g ∉ pathVerts N N.root (pu ++ [f]) := by
    intro g hg hmem
    have hs := hsrc g hg
    rcases List.mem_cons.1 hmem with h | h
    · rw [h] at hs
      exact hs rfl
    · obtain ⟨h', hh', hgh⟩ := List.mem_map.1 h
      rcases List.mem_append.1 hh' with h₁ | h₁
      · rw [← hgh] at hs
        exact hs (hpuall _ h₁)
      · have hfh : h' = f := List.mem_singleton.1 h₁
        have hgx : N.src g = N.tgt e := by rw [← hgh, hfh, ht]
        obtain ⟨_, r, -, -, hr⟩ := hC₂.split hg
        exact not_reach_tgt_src g (hgx ▸ hr.reach)
  obtain ⟨w, -, P₁₂, -, q, -, -, -, -, -, hcyc⟩ := exists_isCycleOn_core hP₁ hC₂ hB heB hC'
  exact ⟨_, ⟨w, N.tgt e, _, q, hcyc, rfl⟩, Or.inl (by simp), fun g hg => Or.inl (by simp [hg]), Or.inl (by simp)⟩

/-- **One cycle, when the arc of `i` is below that of `j`**, or is the same arc: its target has the other state at `j`. A node with the other state at `i` and the state of the root at `j` makes `j` come back. At the first such
node, the state at `i` comes along a path through the arc of `i`, on which `j` has the other state, and the state at `j` from a parent with the state of the root. This is the array W2 or W3 of the source's Theorem 2.2. -/
theorem exists_isCycle_of_below {i j : ι} (hb : N.label (N.tgt (N.site i)) j ≠ N.label N.root j)
    (h : ∃ v, N.label v i ≠ N.label N.root i ∧ N.label v j = N.label N.root j) :
    ∃ Q, N.IsCycle Q ∧ N.site i ∈ Q ∧ N.site j ∈ Q := by
  obtain ⟨v, hv, hmin⟩ := N.wellFounded_transGen.has_min {v | N.label v i ≠ N.label N.root i ∧ N.label v j = N.label N.root j} h
  obtain ⟨hvi, hvj⟩ : N.label v i ≠ N.label N.root i ∧ N.label v j = N.label N.root j := hv
  have hroot : v ≠ N.root := fun h' => hvi (by rw [h'])
  obtain ⟨e, he, hei⟩ := N.exists_parent_label_eq (i := i) hroot (fun h' => hb (by rw [← h']; exact hvj))
  obtain ⟨f, hf, hfj⟩ := N.exists_parent_label_eq (i := j) hroot (fun h' => N.label_tgt_site_ne j (by rw [← h']; exact hvj))
  have hbelow : ∀ y, N.Reach y (N.src e) → N.label y i ≠ N.label N.root i → N.label y j ≠ N.label N.root j := by
    intro y hy hyi hyj
    exact hmin y ⟨hyi, hyj⟩ (Relation.TransGen.tail' hy ⟨e, rfl, he⟩)
  have hei' : N.label (N.src e) i ≠ N.label N.root i := by rwa [hei]
  have hej : N.label (N.src e) j ≠ N.label N.root j := hbelow _ Relation.ReflTransGen.refl hei'
  have hfj' : N.label (N.src f) j = N.label N.root j := hfj.trans hvj
  have hef : e ≠ f := by
    rintro rfl
    exact hej hfj'
  have ht : N.tgt e = N.tgt f := he.trans hf.symm
  obtain ⟨Ci, hCi, hCiall⟩ := exists_path_flipped (N := N) i _ hei'
  have hCij : ∀ g ∈ Ci, N.label (N.src g) j ≠ N.label N.root j := fun g hg =>
    hbelow _ ((reach_src_tgt g).trans (hCi.reach_tgt_of_mem hg)) (hCiall g hg)
  by_cases hsame : N.site i = N.site j
  · obtain ⟨Q, hQ, hj, -, -⟩ := exists_isCycle_of_path_flipped hef ht (j := j) (C := Ci) (hsame ▸ hCi) hCij hej hfj'
    exact ⟨Q, hQ, hsame ▸ hj, hj⟩
  · have hsrc : N.label (N.src (N.site i)) j ≠ N.label N.root j := by
      have hl := N.label_tree (N.site i) (fun g hg => N.site_not_recomb i g hg) j
      rw [ite_eq_right (Ne.symm hsame)] at hl
      rwa [← hl]
    obtain ⟨Cj, hCj, hCjall⟩ := exists_path_flipped (N := N) j _ hsrc
    have hC : N.IsPath (N.tgt (N.site j)) (N.src e) (Cj ++ N.site i :: Ci) := hCj.append ⟨rfl, hCi⟩
    have hall : ∀ g ∈ Cj ++ N.site i :: Ci, N.label (N.src g) j ≠ N.label N.root j := by
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact hCjall g hg
      · rcases List.mem_cons.1 hg with rfl | hg
        · exact hsrc
        · exact hCij g hg
    obtain ⟨Q, hQ, hj, hC', -⟩ := exists_isCycle_of_path_flipped hef ht hC hall hej hfj'
    exact ⟨Q, hQ, hC' _ (by simp), hj⟩

/-- **One cycle, when neither arc is below the other**: the targets of the two arcs have the state of the root at the other site. At the first node with the other state at both sites, the two states come from different parents, along paths through
the two arcs that meet only above them. This is the array W1 of the source's Theorem 2.2. -/
theorem exists_isCycle_of_cross {i j : ι} (hi : N.label (N.tgt (N.site i)) j = N.label N.root j) (hj : N.label (N.tgt (N.site j)) i = N.label N.root i)
    (h : ∃ v, N.label v i ≠ N.label N.root i ∧ N.label v j ≠ N.label N.root j) :
    ∃ Q, N.IsCycle Q ∧ N.site i ∈ Q ∧ N.site j ∈ Q := by
  obtain ⟨v, hv, hmin⟩ := N.wellFounded_transGen.has_min {v | N.label v i ≠ N.label N.root i ∧ N.label v j ≠ N.label N.root j} h
  obtain ⟨hvi, hvj⟩ : N.label v i ≠ N.label N.root i ∧ N.label v j ≠ N.label N.root j := hv
  have hroot : v ≠ N.root := fun h' => hvi (by rw [h'])
  have htopi : v ≠ N.tgt (N.site i) := fun h' => hvj (by rw [h']; exact hi)
  have htopj : v ≠ N.tgt (N.site j) := fun h' => hvi (by rw [h']; exact hj)
  obtain ⟨e, he, hei⟩ := N.exists_parent_label_eq (i := i) hroot htopi
  obtain ⟨f, hf, hfj⟩ := N.exists_parent_label_eq (i := j) hroot htopj
  have hbelow : ∀ y, Relation.TransGen N.Arc y v → N.label y i ≠ N.label N.root i → N.label y j = N.label N.root j := by
    intro y hy hyi
    by_contra hyj
    exact hmin y ⟨hyi, hyj⟩ hy
  have hei' : N.label (N.src e) i ≠ N.label N.root i := by rwa [hei]
  have hfj' : N.label (N.src f) j ≠ N.label N.root j := by rwa [hfj]
  have harc : ∀ {g : E}, N.tgt g = v → Relation.TransGen N.Arc (N.src g) v := fun {g} hg => Relation.TransGen.single ⟨g, rfl, hg⟩
  have hej : N.label (N.src e) j = N.label N.root j := hbelow _ (harc he) hei'
  have hfi : N.label (N.src f) i = N.label N.root i := by
    by_contra hne
    exact hfj' (hbelow _ (harc hf) hne)
  have hef : e ≠ f := by
    rintro rfl
    exact hfj' hej
  have hne : N.site i ≠ N.site j := fun h' => N.label_tgt_site_ne j (by rw [← h']; exact hi)
  -- the paths through the two arcs
  obtain ⟨Ci, hCi, hCiall⟩ := exists_path_flipped (N := N) i _ hei'
  obtain ⟨Cj, hCj, hCjall⟩ := exists_path_flipped (N := N) j _ hfj'
  have hsrci : N.label (N.src (N.site i)) j = N.label N.root j := by
    have hl := N.label_tree (N.site i) (fun g hg => N.site_not_recomb i g hg) j
    rw [ite_eq_right (Ne.symm hne)] at hl
    rw [← hl]
    exact hi
  have hsrcj : N.label (N.src (N.site j)) i = N.label N.root i := by
    have hl := N.label_tree (N.site j) (fun g hg => N.site_not_recomb j g hg) i
    rw [ite_eq_right hne] at hl
    rw [← hl]
    exact hj
  obtain ⟨Ai, hAi, hAiall⟩ := exists_path_unflipped (N := N) j _ hsrci
  obtain ⟨Aj, hAj, hAjall⟩ := exists_path_unflipped (N := N) i _ hsrcj
  -- on the second path after the arc of `j`, the state at `i` is the root's, and that at `j` isn't
  have hCjt : ∀ g ∈ Cj, N.label (N.tgt g) j ≠ N.label N.root j := fun g hg => tgt_ne_of_src_ne hCj hCjall hfj' hg
  have hCji : ∀ g ∈ Cj, N.label (N.tgt g) i = N.label N.root i := by
    intro g hg
    by_contra hne'
    refine hCjt g hg ?_
    exact hbelow _ (Relation.TransGen.tail' (hCj.reach_tgt_of_mem hg) ⟨f, rfl, hf⟩) hne'
  have hC : N.IsPath (N.tgt (N.site i)) v (Ci ++ [e]) := hCi.append ⟨rfl, he⟩
  have hB : N.IsPath N.root v (Aj ++ N.site j :: (Cj ++ [f])) := hAj.append ⟨rfl, hCj.append ⟨rfl, hf⟩⟩
  -- the arcs of the second path end at `v`, or at a node with the state of the root at `i`
  have hBi : ∀ g ∈ Aj ++ N.site j :: (Cj ++ [f]), N.tgt g = v ∨ N.label (N.tgt g) i = N.label N.root i := by
    intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | hg | rfl
    · exact Or.inr (hAjall g hg)
    · exact Or.inr hj
    · exact Or.inr (hCji g hg)
    · exact Or.inl hf
  have heB : N.site i ∉ Aj ++ N.site j :: (Cj ++ [f]) := fun hm => by
    rcases hBi _ hm with h' | h'
    · exact htopi h'.symm
    · exact N.label_tgt_site_ne i h'
  have hC' : ∀ g ∈ Ci ++ [e], N.src g ∉ pathVerts N N.root (Aj ++ N.site j :: (Cj ++ [f])) := by
    intro g hg hmem
    have hs : N.label (N.src g) i ≠ N.label N.root i := by
      rcases List.mem_append.1 hg with h' | h'
      · exact hCiall g h'
      · rw [List.mem_singleton.1 h']
        exact hei'
    rcases List.mem_cons.1 hmem with h' | h'
    · rw [h'] at hs
      exact hs rfl
    · obtain ⟨g', hg', hgg⟩ := List.mem_map.1 h'
      rcases hBi g' hg' with h₁ | h₁
      · obtain ⟨_, r, -, -, hr⟩ := hC.split hg
        have hsv : N.src g = v := hgg.symm.trans h₁
        exact not_reach_tgt_src g (hsv ▸ hr.reach)
      · exact hs (by rw [← hgg]; exact h₁)
  obtain ⟨w, P₁₁, P₁₂, B₁, q, hsplit, hBq, -, hP₁₁, hB₁, hcyc⟩ := exists_isCycleOn_core hAi hC hB heB hC'
  refine ⟨_, ⟨w, v, _, q, hcyc, rfl⟩, Or.inl (by simp), Or.inr ?_⟩
  -- the node `w` has the state of the root at `j`, so the arc of `j` comes after it
  have hwj : N.label w j = N.label N.root j := by
    rcases List.mem_cons.1 hP₁₁.end_mem_pathVerts with h' | h'
    · rw [h']
    · obtain ⟨g, hg, hgw⟩ := List.mem_map.1 h'
      rw [← hgw]
      exact hAiall g (by rw [hsplit]; exact List.mem_append_left _ hg)
  have hmemB : N.site j ∈ B₁ ++ q := by
    rw [← hBq]
    simp
  rcases List.mem_append.1 hmemB with hm | hm
  · exfalso
    obtain ⟨B', a, hB', -, ha⟩ := hB₁.exists_last_arc (fun h' => by simp [h'] at hm)
    have haB : a ∈ Aj ++ N.site j :: (Cj ++ [f]) := by
      rw [hBq, hB']
      simp
    have hreach : N.Reach (N.tgt (N.site j)) w := by
      obtain ⟨_, r, -, -, hr⟩ := hB₁.split hm
      exact hr.reach
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at haB
    rcases haB with ha' | rfl | ha' | rfl
    · have h₁ : N.Reach w (N.src (N.site j)) := ha ▸ hAj.reach_tgt_of_mem ha'
      exact not_reach_tgt_src _ (hreach.trans h₁)
    · exact N.label_tgt_site_ne j (ha ▸ hwj)
    · exact hCjt a ha' (ha ▸ hwj)
    · exact hvj (by rw [← hf, ha]; exact hwj)
  · exact hm

/-- **Gusfield, Eddhu, Langley 2004, the proof of Theorem 2.2** (`ext:same_cycle`). "If `i` and `j` conflict and `N` is a phylogenetic network for `M` (not necessarily a galled-tree), then `i` and `j` must be together on some
recombination cycle in `N`." Here for any set of rows that label nodes of `N`, and any number of crossovers.

Departure from the source: it removes the other sites, contracts edges, and at each recombination node deletes one arc, to reach a perfect phylogeny on the two sites. Its claim that this keeps the labels of the leaves has no proof, and no arc can be deleted at a
node that takes one site from each parent, when the parents differ at both: such a node has a cycle through each site, and the source's argument doesn't say why these are one cycle. So Lean traces the states up instead: if the arc of one site is below
that of the other (`exists_isCycle_of_below`) a state of one has to come back, and otherwise (`exists_isCycle_of_cross`) the first node with both other states has them from different parents. In each case two paths through the two arcs, along which a state is
inherited, can't meet below the arcs. -/
theorem exists_isCycle_of_conflict (N : Network ι V E) {L : Finset (ι → Bool)} (hL : ∀ r ∈ L, ∃ v, N.label v = r) {i j : ι} (h : Conflict N.ancestral L i j) :
    ∃ Q, N.IsCycle Q ∧ N.site i ∈ Q ∧ N.site j ∈ Q := by
  have hrow : ∀ a b : Bool, (a ≠ N.ancestral i ∨ b ≠ N.ancestral j) → ∃ v, N.label v i = a ∧ N.label v j = b := by
    intro a b hab
    obtain ⟨r, hr, h₁, h₂⟩ := h a b hab
    obtain ⟨v, rfl⟩ := hL r hr
    exact ⟨v, h₁, h₂⟩
  have hne : ∀ b : Bool, (!b) ≠ b := fun b => by cases b <;> simp
  by_cases hb : N.label (N.tgt (N.site i)) j ≠ N.label N.root j
  · obtain ⟨v, h₁, h₂⟩ := hrow (!N.ancestral i) (N.ancestral j) (Or.inl (hne _))
    exact exists_isCycle_of_below hb ⟨v, by rw [h₁]; exact hne _, h₂⟩
  by_cases ha : N.label (N.tgt (N.site j)) i ≠ N.label N.root i
  · obtain ⟨v, h₁, h₂⟩ := hrow (N.ancestral i) (!N.ancestral j) (Or.inr (hne _))
    obtain ⟨Q, hQ, h₃, h₄⟩ := exists_isCycle_of_below ha ⟨v, by rw [h₂]; exact hne _, h₁⟩
    exact ⟨Q, hQ, h₄, h₃⟩
  push Not at hb ha
  obtain ⟨v, h₁, h₂⟩ := hrow (!N.ancestral i) (!N.ancestral j) (Or.inl (hne _))
  exact exists_isCycle_of_cross hb ha ⟨v, by rw [h₁]; exact hne _, by rw [h₂]; exact hne _⟩

/-- **Gusfield, Eddhu, Langley 2004, the proof of Theorem 2.2**, unrooted (`ext:same_cycle`). Two sites incompatible in a set of rows that label nodes of `N` are on one recombination cycle. -/
theorem exists_isCycle_of_incompatible (N : Network ι V E) {L : Finset (ι → Bool)} (hL : ∀ r ∈ L, ∃ v, N.label v = r) {i j : ι} (h : Incompatible L i j) :
    ∃ Q, N.IsCycle Q ∧ N.site i ∈ Q ∧ N.site j ∈ Q :=
  exists_isCycle_of_conflict N hL fun a b _ => h a b

end GusfieldEtAl2004
