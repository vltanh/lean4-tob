module

public import Gusfield2007.Decomposition
public import Gusfield2007.Examples

/-!
# Gusfield et al. 2007, Sections 3.7 and 4.2: uniqueness of `T̄`, and the most tree-like network

**Theorem 4 is false as printed, and so is the characterization of Section 4.2.** The printed statements are kept here as
definitions (`Theorem4Printed`, `MostTreeLikePrinted`), with their counterexamples, and with the closest true statements.

There are several separate failures.

1. A leaf can be a recombination node, in a blob. Then its row has no pendant edge in `T′`, while `T̄` has one (`fourGametes`,
   with `11` a recombination leaf of `01` and `10`).
2. The root can have degree two, and an arc can have no site. Then `T′` isn't literally `T̄`. Section 4.2 assumes away only a node
   of in-degree and out-degree one. `theorem4Printed_false_rootDegreeTwo` proves this case, on the rows `0`, `1`.
3. The essential one, which is an error in the proof. At line 342, the proof says that when the edge `e = (v, v′)` leaving a blob
   is removed, "in the other subnetwork, no leaf label contains `S_v(C)`". This fails when `v` has the same label on `C` as the
   entry node of the blob and rows lie above the blob: those rows also contain `S_v(C)`. Take `topRows`, with the blob of the
   sites 3, 4 entered by an arc with the site 5, and the row `11001` hanging from the entry node of that blob. This network is
   efficient and fully decomposed, and has no recombination leaf. In `T′` the row `11001` is on the same side as the
   rows `11011`, `11101`, `11111` of the edge entering the blob. `T̄` has the split `{11011, 11101, 11111} | rest`, which `T′`
   doesn't have: `T̄` has nine edges and `T′` eight. Moving that row up to a new node on the entering arc gives another efficient
   fully decomposed network, whose `T′` is `T̄`. So `T′` isn't invariant. A reading of "external" that counts the entering
   edge would repair this, but then the top of a blob entered with no site would share its label with the node it hangs from,
   and no efficient network would exist for `M` of Figure 2.

What's true: `theorem4_splits` and `theorem4`, under `IsTreeNormal`, and `treeSplits_compatible` for every network.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

universe u

variable {ι : Type u} [LinearOrder ι]

/-- The form of the statement of Theorem 4, for the networks satisfying `P`: for an efficient fully decomposed network
for `M`, the undirected `T′` is isomorphic to `T̄`, by an isomorphism that respects the rows at the leaves. -/
def Theorem4Form (c : Crossover) (M : Finset (ι → Bool))
    (P : ∀ {a b : ℕ}, Network ι (Fin a) (Fin b) → Prop) : Prop :=
  ∀ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c → N.Derives M →
    N.IsFullyDecomposedFor (incompatGraph M) → N.IsEfficient → P N →
    ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : M → Fin n) (edge : SuperChar M → Sym2 (Fin n)), IsTBar M T φ edge →
      ∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r →
        f (N.toBlobNode v) = φ ⟨r, hr⟩

/-- **Theorem 4 as printed** (`g:thm4_printed`). "If `N` is any efficient fully-decomposed network for `M`, and `T′` is created
by contracting each blob of `N` to a single node, then after the directed edges in `T′` are made undirected, the resulting tree
is necessarily the tree `T̄` defined in the proof of Theorem 1" (line 334). False: see below. -/
def Theorem4Printed (c : Crossover) (M : Finset (ι → Bool)) : Prop :=
  Theorem4Form c M fun _ => True

/-- **Line 330** (`g:efficient`). "If `N` is not efficient, it can be easily modified to become efficient without increasing the
number of recombinations used. Also, if `N` is fully-decomposed, then the efficient network derived from it is also
fully-decomposed." For both graphs, `G(M)` and `G_S(M)`. -/
theorem exists_isEfficient {V E : Type*} [Finite V] [Finite E] [Finite ι] (N : Network ι V E) {c : Crossover}
    {M : Finset (ι → Bool)} {G : SimpleGraph ι} (hc : N.Obeys c) (hd : N.Derives M)
    (hG : G = incompatGraph M ∨ G = conflictGraph N.ancestral M) (hf : N.IsFullyDecomposedFor G) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = N.ancestral ∧
      N'.IsFullyDecomposedFor G ∧ N'.IsEfficient ∧ N'.recombCount ≤ N.recombCount := by
  sorry

/-- **Line 330** (`g:efficient_exists`). "So for any `M`, there is a efficient fully-decomposed phylogenetic network for `M`." -/
theorem exists_efficient_fullyDecomposed [Finite ι] (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧
      N.IsFullyDecomposedFor (incompatGraph M) ∧ N.IsEfficient := by
  obtain ⟨a, b, N, h₁, h₂, h₃⟩ := theorem1 c M hM hC
  obtain ⟨a', b', N', h₁', h₂', -, h₄', h₅', -⟩ := exists_isEfficient N h₁ h₂ (Or.inl rfl) h₃
  exact ⟨a', b', N', h₁', h₂', h₄', h₅'⟩

section RootDegreeTwo

/-- The network with a root, a leaf `0`, and a leaf `1` below an arc with the site. -/
def rootDegreeTwoNet : Network (Fin 1) (Fin 3) (Fin 2) where
  src := fun _ => 0
  tgt := Fin.succ
  root := 0
  site := fun _ => 1
  label := fun v _ => decide (v = 2)
  simple := by decide
  acyclic := Network.acyclic_of_rank (fun v : Fin 3 => v.val) (by decide)
  root_iff := by decide
  inDegree_le_two := by decide
  site_not_recomb := by decide
  label_tree := by
    intro e _ i
    fin_cases e <;> fin_cases i <;> simp
  label_recomb := by
    intro e f hef h
    exact absurd h (by revert e f; decide)

theorem rootDegreeTwoNet_tgt_injective : Function.Injective rootDegreeTwoNet.tgt :=
  Fin.succ_injective _

theorem rootDegreeTwoNet_derives : rootDegreeTwoNet.Derives oneSiteRows := by
  have hleaf : ∀ v : Fin 3, rootDegreeTwoNet.IsLeaf v ↔ v ≠ 0 := by
    intro v
    change (∀ _ : Fin 2, (0 : Fin 3) ≠ v) ↔ v ≠ 0
    exact ⟨fun h => (h 0).symm, fun h _ => h.symm⟩
  refine ⟨fun v hv => ?_, fun u hu v hv huv => ?_, fun r hr => ?_⟩
  · have hv' := (hleaf v).1 hv
    fin_cases v
    · exact absurd rfl hv'
    · simp [rootDegreeTwoNet, oneSiteRows]
    · simp [rootDegreeTwoNet, oneSiteRows]
  · have hu' := (hleaf u).1 hu
    have hv' := (hleaf v).1 hv
    have h0 : decide (u = 2) = decide (v = 2) := congrFun huv 0
    clear huv hu hv
    revert hu' hv' h0
    revert u v
    decide
  · have hr' : r = (fun _ => false) ∨ r = fun _ => true := by simpa [oneSiteRows] using hr
    rcases hr' with rfl | rfl
    · exact ⟨1, (hleaf 1).2 (by decide), by funext i; simp [rootDegreeTwoNet]⟩
    · exact ⟨2, (hleaf 2).2 (by decide), by funext i; simp [rootDegreeTwoNet]⟩

/-- The labelling of `T̄` for the rows `0`, `1`. -/
def oneSiteLabel (r : oneSiteRows) : Fin 2 := if r.1 0 = true then 1 else 0

theorem oneSiteLabel_eq_iff (x y : oneSiteRows) : oneSiteLabel x = oneSiteLabel y ↔ x.1 0 = y.1 0 := by
  unfold oneSiteLabel
  cases x.1 0 <;> cases y.1 0 <;> simp

theorem oneSite_bot_reachable {a b : Fin 2}
    (h : SameSide (SimpleGraph.pathGraph 2) s((0 : Fin 2), (1 : Fin 2)) a b) : a = b := by
  have hbot : (SimpleGraph.pathGraph 2).deleteEdges {s((0 : Fin 2), (1 : Fin 2))} = ⊥ := by
    ext u v
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, SimpleGraph.bot_adj, iff_false, not_and, not_not]
    intro huv
    have hne := huv.ne
    revert hne
    revert u v
    decide
  unfold SameSide at h
  rw [hbot, SimpleGraph.reachable_bot] at h
  exact h

/-- `T̄` for the rows `0`, `1` is one edge. -/
theorem oneSite_isTBar : IsTBar oneSiteRows (SimpleGraph.pathGraph 2) oneSiteLabel
    (fun _ => s((0 : Fin 2), (1 : Fin 2))) := by
  have hsub : ∀ v : Fin 2, ((SimpleGraph.pathGraph 2).neighborSet v).ncard ≤ 1 := by
    intro v
    rw [Set.ncard_le_one_iff_subsingleton]
    intro a ha b hb
    have ha' : a ≠ v := (SimpleGraph.Adj.ne ((SimpleGraph.mem_neighborSet _ _ _).1 ha)).symm
    have hb' : b ≠ v := (SimpleGraph.Adj.ne ((SimpleGraph.mem_neighborSet _ _ _).1 hb)).symm
    clear ha hb
    revert ha' hb'
    revert a b v
    decide
  have hrange : ∀ v, v ∈ Set.range oneSiteLabel := by
    intro v
    have h₀ : (fun _ => false : Fin 1 → Bool) ∈ oneSiteRows := by simp [oneSiteRows]
    have h₁ : (fun _ => true : Fin 1 → Bool) ∈ oneSiteRows := by simp [oneSiteRows]
    fin_cases v
    · exact ⟨⟨_, h₀⟩, by simp [oneSiteLabel]⟩
    · exact ⟨⟨_, h₁⟩, by simp [oneSiteLabel]⟩
  refine { isTree := SimpleGraph.isTree_pathGraph.2 (by decide), label_injective := ?_, mem_range_iff := ?_, edge_mem := ?_,
           split := ?_, internal_labelled := ?_, degree_ne_two := ?_ }
  · intro x y hxy
    exact Subtype.ext (funext fun i => by
      have : i = 0 := Subsingleton.elim _ _
      rw [this]
      exact (oneSiteLabel_eq_iff x y).1 hxy)
  · exact fun v => ⟨fun _ => hsub v, fun _ => hrange v⟩
  · intro _
    exact (SimpleGraph.mem_edgeSet _).2 (by simp [SimpleGraph.pathGraph_adj])
  · rintro ⟨c, S, hS⟩ x y
    by_cases hxy : x.1 0 = y.1 0
    · have hxy' : x = y := Subtype.ext (funext fun i => by rw [Subsingleton.elim i 0]; exact hxy)
      subst hxy'
      exact ⟨fun _ => SimpleGraph.Reachable.refl _, fun _ => rfl⟩
    · refine ⟨fun heq => ?_, fun hr => absurd ((oneSiteLabel_eq_iff x y).1 (oneSite_bot_reachable hr)) hxy⟩
      exfalso
      obtain ⟨r, -, rfl⟩ := mem_restrictRows.1 hS
      obtain ⟨i₀, hi₀⟩ := c.nonempty_supp
      have h0 : (0 : Fin 1) ∈ c.supp := by rwa [Subsingleton.elim (0 : Fin 1) i₀]
      have hiff : ∀ z : Fin 1 → Bool, c.supp.domRestrict z = c.supp.domRestrict r ↔ z 0 = r 0 := by
        intro z
        refine ⟨fun h => congrFun h ⟨0, h0⟩, fun h => funext fun i => ?_⟩
        have : (i : Fin 1) = 0 := Subsingleton.elim _ _
        simp only [Set.domRestrict, this]
        exact h
      simp only [charValue, decide_eq_decide, hiff] at heq
      revert heq hxy
      cases x.1 0 <;> cases y.1 0 <;> cases r 0 <;> simp
  · intro u v _ hu
    exact absurd (hrange u) hu
  · intro v h
    have := hsub v
    omega

/-- **The shortest counterexample to Theorem 4 as printed, failure 2** (`g:thm4_false_root`). `M = {0, 1}` on one site, in any crossover model. The network with a root and two leaves
is efficient and fully decomposed, since it has no blob. Its `T′` has three nodes, and `T̄` has two. So `T′` isn't literally `T̄`; a root of degree two has to be suppressed. -/
theorem theorem4Printed_false_rootDegreeTwo (c : Crossover) : ¬ Theorem4Printed c oneSiteRows := by
  intro h
  have hinj := rootDegreeTwoNet_tgt_injective
  obtain ⟨f, -⟩ := h 3 2 rootDegreeTwoNet (Network.obeys_of_tgt_injective hinj c) rootDegreeTwoNet_derives
    (Network.isFullyDecomposedFor_of_tgt_injective hinj _) (Network.isEfficient_of_tgt_injective hinj) trivial 2 _ _ _
    oneSite_isTBar
  have hle := Fintype.card_le_of_injective _ (f.injective.comp (Network.toBlobNode_injective_of_tgt_injective hinj))
  simp at hle

end RootDegreeTwo

/-- **Counterexample to Theorem 4 as printed, failure 1** (`g:thm4_false_leaf`). `M = {00, 01, 10, 11}`, with `11` a recombination
leaf of `01` and `10`, and a leaf at the root and at each of `01`, `10`, in any model: `T′` has three edges, and `T̄` has four. It's checked by a script, outside Lean. -/
theorem theorem4Printed_false_recombLeaf (c : Crossover) : ¬ Theorem4Printed c fourGametes := by
  sorry

/-- **Counterexample to Theorem 4, failure 3** (`g:thm4_false_top`). With no recombination leaf, with every node of `T′` of degree at
most two a leaf, and with sites on all the arcs off the blobs that aren't pendant, Theorem 4 still fails, on `topRows`, in
any model. The network: a blob on `00000, 01000, 10000, 11000` with the sites 1, 2; an arc with the site 5 from `11000` to `11001`; a blob on
`11001, 11011, 11101, 11111` with the sites 3, 4; and a pendant arc at each node of the two blobs other than `11000`. It's checked by a script, outside Lean. -/
theorem theorem4_false_top (c : Crossover) :
    ¬ Theorem4Form c topRows fun {a b} (N : Network (Fin 5) (Fin a) (Fin b)) =>
        (∀ x, N.IsRecomb x → ¬ N.IsLeaf x) ∧
        (∀ e, N.IsTreeArc e → ¬ N.OnBlob (N.src e) → ¬ N.OnBlob (N.tgt e) → ¬ N.IsLeaf (N.tgt e) → ∃ i, N.site i = e) ∧
        (∀ v, (N.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, N.IsLeaf l ∧ N.toBlobNode l = v) := by
  sorry

/-- **The closest true form of Theorem 4, on splits** (`g:thm4_splits`). The proof at lines 340 to 344 shows that the splits of `T′`
and `T̄` agree, and it's their non-trivial splits that agree, under `IsTreeNormal`. Departure from the paper: the
hypothesis `IsTreeNormal` is added, because the statement is false without it (above). Under it, the argument of the paper
goes through, and handles also the entering edge of a blob, which the proof doesn't mention, and which gets the character of
the ancestral super-character. -/
theorem theorem4_splits {V E : Type*} [Finite V] [Finite E] [Finite ι] (N : Network ι V E) {M : Finset (ι → Bool)}
    (hd : N.Derives M) (hC : NoConstantColumn M) (hf : N.IsFullyDecomposedFor (incompatGraph M)) (he : N.IsEfficient)
    (hn : N.IsTreeNormal) {A : Set (ι → Bool)} (hA : A ⊆ M) (h₁ : 2 ≤ A.encard)
    (h₂ : 2 ≤ ((M : Set (ι → Bool)) \ A).encard) :
    A ∈ N.treeSplits M ↔ A ∈ charSplits M := by
  sorry

/-- **The closest true form of Theorem 4** (`g:thm4`). Under `IsTreeNormal`, and if every node of `T′` of degree at most two is a
leaf of `N` (no root of degree two off a blob, and no node of in-degree and out-degree one), then `T′` is `T̄`. The proof is
`theorem4_splits` and the Splits Equivalence Theorem (line 344). Departure from the paper: the two hypotheses are added, because
the statement is false without them. -/
theorem theorem4 [Finite ι] (c : Crossover) (M : Finset (ι → Bool)) (hC : NoConstantColumn M) :
    Theorem4Form c M fun {a b} (N : Network ι (Fin a) (Fin b)) =>
      N.IsTreeNormal ∧ ∀ v, (N.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, N.IsLeaf l ∧ N.toBlobNode l = v := by
  sorry

/-- **`g:tree_compatible`**. Every split of a tree arc of any network for `M` is compatible with every character of `B`. So `T′` and `T̄`
always have a common refinement, whether or not the network is fully decomposed. This is what's left of the invariance when
the assumptions of `theorem4` fail. The reason: each non-trivial component is on one blob, so on one side of the tree arc its
sequence is constant. -/
theorem treeSplits_compatible {V E : Type*} [Finite V] [Finite E] [Finite ι] (N : Network ι V E)
    {M : Finset (ι → Bool)} (hd : N.Derives M) {A : Set (ι → Bool)} (hA : A ∈ N.treeSplits M) (k : SuperChar M) :
    A ∩ charSide k = ∅ ∨ A \ charSide k = ∅ ∨ (M : Set (ι → Bool)) \ A ∩ charSide k = ∅ ∨
      ((M : Set (ι → Bool)) \ A) \ charSide k = ∅ := by
  sorry

/-- **Section 4.2 as printed** (`g:treeness`). "With the above definition of treeness, it is clear that a phylogenetic network `N` is
the most tree-like if and only if `T̄` is the resulting undirected tree, after the blobs of `N` are contracted, and all the
edges are made undirected" (line 373), among networks with no node of in-degree and out-degree one (line 364). False: see
below. -/
def MostTreeLikePrinted (c : Crossover) (M : Finset (ι → Bool)) : Prop :=
  ∀ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c → N.Derives M →
    (∀ e f, N.tgt e = N.src f → (∀ g, N.tgt g = N.tgt e → g = e) → (∀ g, N.src g = N.src f → g = f) → False) →
    ((∀ (a' b' : ℕ) (N' : Network ι (Fin a') (Fin b')), N'.Obeys c → N'.Derives M →
        (∀ e f, N'.tgt e = N'.src f → (∀ g, N'.tgt g = N'.tgt e → g = e) → (∀ g, N'.src g = N'.src f → g = f) → False) →
        N'.treeness ≤ N.treeness) ↔
      ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : M → Fin n) (edge : SuperChar M → Sym2 (Fin n)), IsTBar M T φ edge →
        ∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩)

/-- **Counterexample to Section 4.2** (`g:treeness_false`). `starRows` has a network whose `T′` is `T̄`, the star with four edges, and a
network with six tree arcs and the same leaves, by resolving the star with two arcs that have no site. So the network with `T′ = T̄`
isn't the most tree-like. More: a cycle with no site adds tree arcs, so that treeness has no maximum at all on many `M`. -/
theorem mostTreeLikePrinted_false (c : Crossover) : ¬ MostTreeLikePrinted c starRows := by
  sorry

end Gusfield2007
