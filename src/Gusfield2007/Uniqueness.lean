module

public import Gusfield2007.Decomposition
public import Gusfield2007.Examples
public import Gusfield2007.Hub
public import Gusfield2007.TreeFacts
public import Gusfield2007.CounterexampleNets

/-!
# Gusfield et al. 2007, Sections 3.7 and 4.2: uniqueness of `T̄`, and the most tree-like network

**Theorem 4 is false with the printed definition of "efficient", because that definition omits the entry node of a blob, and true with the entry node counted, up to two conventions and site-free arcs. The characterization of Section 4.2 is false too.** The printed statements are kept here as
definitions (`Theorem4Printed`, `Theorem4Form`, `MostTreeLikePrinted`), with their counterexamples, and with the closest true statements.

## Theorem 4

1. **The definition.** Lines 326 to 328 call `v` external if "there is an edge from `v` to some node outside of `b`", which leaves out the node where the blob is entered. The proof uses more: at line 341, each super-character labels an external node, which fails for the super-character of the top of the blob, and at line 342, "in the other subnetwork, no leaf label contains
   `S_v(C)`", which fails if an exit is at the top and rows lie above the blob.
2. **The repair.** It is in print, and not ours: Gusfield, *ReCombinatorics* (MIT Press, 2014), Section 7.3.5, counts an external node "without regard to edge direction", defines canonical networks, and states the theorem for them as its Theorem 7.3.3 (read only in snippets: `docs/REPORT.md`, E42). `Network.IsEfficientAtEntry` is a weaker condition in the same spirit: it compares labels on one blob at a time, and counts the entering arc among the arcs of its node. Then lines 341 and 342 are true (`Network.IsEfficientAtEntry.existsUnique_port`, `Network.IsEfficientAtEntry.line342Claim`), the case of a blob at the root needs no exemption, since it has no entering arc (`fourRootNet_isEfficientAtEntry`), and Theorem 4
   holds, in both directions (`theorem4_entry`). `Network.isEfficientAtEntry_iff` relates it to the printed definition. Comparing labels over all the blobs, as the printed definition does, isn't needed by the proof, and it's implied by `T′ ≅ T̄` (`Network.isEfficient_of_iso`). Line 329 holds for this definition (`exists_isEfficientAtEntry`, in `Gusfield2007.Realizability`), for existence.
3. **The counterexamples for the printed definition.** Take `topRows`, with the blob of the sites 3, 4 entered by an arc with the site 5, and the row `11001` hanging from the entry node of that blob. This network is efficient in the printed sense and fully decomposed, and has no recombination leaf. The split `{00000, 01000, 10000, 11001} | {11011, 11101, 11111}` of `T̄` isn't in `T′`:
   `theorem4_false_top`. It isn't efficient at the entry node: `topNet_not_isEfficientAtEntry`. The count of edges is a poor witness, since it depends on the reading: with rows at leaves, `T̄` has nine edges and `T′` eight, and under line 264's reading `T̄` has eight too. Moving that row up to a new node on the entering arc gives another efficient fully decomposed network, whose `T′` is `T̄`. So `T′` isn't invariant:
   `topRows_not_invariant`. A smaller instance is `{0000, 0001, 0010, 0110, 1010, 1110}`, with one blob and a root of degree 3: `theorem4_false_small`.
4. **Line 341** is false for the printed definition on the paper's own networks. In Figure 2 made efficient, the super-character `00` of `{2, 5}` labels no external node: `line341_false_fig2`. There `T′` is `T̄`, so this is a gap in the proof, and not a further failure of the theorem. The proof never handles the edges entering a blob.
5. **A third failure, site-free arcs.** A perfect phylogeny with a site-free arc that isn't pendant is efficient and fully decomposed, and `T′` has a split that `T̄` lacks: `theorem4_false_siteFree`, `fiveNet_split`. Line 97 allows such arcs, and the statement must exclude them, which is why `RegularArcs` has `arc_labelled`. The same example is against line 156: `perfectPhylogeny_not_invariant`, and
   `perfectPhylogeny_invariant` is what's true.
6. **Two conventions, which aren't errors.** A root of degree two (`M = {0, 1}`, `theorem4Printed_false_rootDegreeTwo`): every network for two rows has it, and line 418 itself places a root on an edge, so read `T′` with the root suppressed. A recombination leaf (`fourGametes`, `theorem4Printed_false_recombLeaf`): Figure 1's caption speaks of the sequence "exiting" a recombination node, and line 341 needs it, so give a
   recombination node a pendant arc.

What's true: `theorem4_splits`, `theorem4`, and exactly `theorem4_iff` and `theorem4_entry`; and `treeSplits_compatible`, for every network. These hypotheses can be met, for every `M` with at least three rows: `exists_realization`, in `Gusfield2007.Realizability`.

## Section 4.2

Treeness counts the edges of `T′`, among networks whose blobs are node-disjoint, with no node of in-degree and out-degree one (line 364). `MostTreeLikePrinted` is false (`mostTreeLikePrinted_false`). Stronger: `treeness_example₁`, `treeness_example₂`. The positive form, with structural conditions on the network, is `treeness_le_and_eq_iff`; `treeness_nonFD_example` and `treeness_strict_example` show what it covers.
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

/-- A fully decomposed network doesn't merge components: with its ancestral sequence `S`, the graphs `G_S(M)` and `G(M)` have the same components. The one direction
is "`G_S(M)` contains `G(M)`", and the other is the converse for `G_S(M)`. This is the condition that `hG` of `minDecomposable_of_sMinDecomposable` needs. -/
theorem reachable_conflictGraph_iff {V E : Type*} [Finite V] [Finite E] {N : Network ι V E} {M : Finset (ι → Bool)} (hd : N.Derives M)
    (hf : N.IsFullyDecomposedFor (incompatGraph M)) (i j : ι) :
    (conflictGraph N.ancestral M).Reachable i j ↔ (incompatGraph M).Reachable i j := by
  constructor
  · intro h
    by_cases hij : i = j
    · rw [hij]
    · have hmem₁ : i ∈ ((conflictGraph N.ancestral M).connectedComponentMk i).supp := rfl
      have hmem₂ : j ∈ ((conflictGraph N.ancestral M).connectedComponentMk i).supp :=
        SimpleGraph.ConnectedComponent.eq.2 h.symm
      obtain ⟨B, hB, hsub⟩ := converse_rooted N hd rfl _ ⟨i, hmem₁, j, hmem₂, hij⟩
      obtain ⟨c₀, -, hc₀⟩ := hf.blob_component B hB
      have h₁ := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 ((hc₀ i).1 (hsub i hmem₁))
      have h₂ := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 ((hc₀ j).1 (hsub j hmem₂))
      exact SimpleGraph.ConnectedComponent.eq.1 (h₁.trans h₂.symm)
  · refine fun h => h.mono fun a b hab x y _ => ?_
    exact hab x y

section Efficient

variable [Finite ι]

/-- **The modification of line 330, by induction** on the number of recombination nodes, and then the number of exits of blobs, within a class `P` of networks. If a network isn't efficient, the hub makes a network with fewer exits, unless a node loses all its
arcs. Then a recombination node goes, and the class has to supply a network with no more recombination nodes than what's left (`hPreduce`). -/
theorem exists_isEfficient_core (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M)
    (P : ∀ (V E : Type), Network ι V E → Prop) (hPnd : ∀ (V E : Type) (N : Network ι V E), P V E N → N.BlobsNodeDisjoint)
    (hPhub : ∀ (V E : Type) [Finite V] [Finite E] (N : Network ι V E) (X : Set E) (v₁ : V) (hX : N.HubCond X v₁), P V E N → P (Option V) (Option E) (N.hubNet X v₁ hX))
    (hPreduce : ∀ (V E : Type) [Finite V] [Finite E] (N : Network ι V E), P V E N → ∀ (V₃ E₃ : Type u) [Finite V₃] [Finite E₃] (N₃ : Network ι V₃ E₃), N₃.Obeys c → N₃.Derives M → N₃.ancestral = S →
      (∀ x, N₃.IsRecomb x → ∃ z, N.IsRecomb z ∧ ∀ C : Set ι, N₃.BreaksAt x C → N.BreaksAt z C) →
      ∃ (V' E' : Type) (_ : Finite V') (_ : Finite E') (N' : Network ι V' E'), P V' E' N' ∧ N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧ N'.recombCount ≤ N₃.recombCount) :
    ∀ (K n : ℕ) (V E : Type) [Finite V] [Finite E] (N : Network ι V E), P V E N → N.Obeys c → N.Derives M → N.ancestral = S → N.recombCount = K → N.exitCount = n →
      ∃ (V' E' : Type) (_ : Finite V') (_ : Finite E') (N' : Network ι V' E'), P V' E' N' ∧ N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧ N'.IsEfficient ∧ N'.recombCount ≤ K := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ihK =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro V E _ _ N hP hc hd hS hK hn
      by_cases he : N.IsEfficient
      · exact ⟨V, E, inferInstance, inferInstance, N, hP, hc, hd, hS, he, hK.le⟩
      have hnd := hPnd V E N hP
      -- the hub with the exits still leaving a network deriving `M`
      have hhub : ∀ (X : Set E) (v₁ : V) (hX : N.HubCond X v₁), X.Nonempty → ¬ N.IsLeaf v₁ →
          (∀ e ∈ X, N.src e = v₁ ∨ ∃ f, f ∉ X ∧ N.src f = N.src e) → (∀ e ∈ X, N.OnBlob (N.src e)) → (∃ e₀ ∈ X, ∃ e₁ ∈ X, e₀ ≠ e₁) →
          ∃ (V' E' : Type) (_ : Finite V') (_ : Finite E') (N' : Network ι V' E'), P V' E' N' ∧ N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧ N'.IsEfficient ∧ N'.recombCount ≤ K := by
        intro X v₁ hX hne hv hsrc hb ⟨e₀, he₀, e₁, he₁, h₀₁⟩
        refine ihn _ (hn ▸ Network.hubNet_exitCount_lt hX he₀ he₁ h₀₁ hb) (Option V) (Option E) (N.hubNet X v₁ hX) (hPhub V E N X v₁ hX hP) (Network.hubNet_obeys hX hc)
          (Network.hubNet_derives hd hne hv hsrc) hS ?_ rfl
        rw [Network.hubNet_recombCount, hK]
      by_cases hu : ∀ B e f, N.IsBlob B → N.src e ∈ N.blobVerts B → N.tgt e ∉ N.blobVerts B → N.src f = N.src e → N.tgt f ∉ N.blobVerts B → e = f
      · -- two external nodes with one label
        have hli : ¬ ∀ B B' v v', N.IsBlob B → N.IsBlob B' → N.IsExternal B v → N.IsExternal B' v' → N.label v = N.label v' → v = v' :=
          fun h => he ⟨h, hu⟩
        push Not at hli
        obtain ⟨B₁, B₂, v, v', hB₁, hB₂, ⟨hvm, e, hes, het⟩, ⟨hvm', e', hes', het'⟩, hlab, hne⟩ := hli
        have hkey : ∀ (r o : V) (B_r B_o : Set E) (e_r e_o : E), N.IsBlob B_r → N.IsBlob B_o → r ∈ N.blobVerts B_r → o ∈ N.blobVerts B_o → N.src e_r = r → N.src e_o = o →
            N.IsTreeArc e_r → N.IsTreeArc e_o → r ≠ o → N.label o = N.label r →
            (∀ g, ((N.src g = r ∨ N.src g = o) ∧ N.IsTreeArc g) → ¬ N.Reach (N.tgt g) r) →
            ∃ (V' E' : Type) (_ : Finite V') (_ : Finite E') (N' : Network ι V' E'), P V' E' N' ∧ N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧ N'.IsEfficient ∧ N'.recombCount ≤ K := by
          intro r o B_r B_o e_r e_o hB_r hB_o hr ho hsr hso htr hto hro hlb hacyc
          set X : Set E := {g | (N.src g = r ∨ N.src g = o) ∧ N.IsTreeArc g} with hXdef
          have hX : N.HubCond X r := ⟨fun g hg => hg.2, fun g hg => by
            rcases hg.1 with h | h
            · rw [h]
            · rw [h, hlb], fun g hg => hacyc g hg⟩
          have her : e_r ∈ X := ⟨Or.inl hsr, htr⟩
          have heo : e_o ∈ X := ⟨Or.inr hso, hto⟩
          have hre : e_r ≠ e_o := fun h => hro (by rw [← hsr, ← hso, h])
          have honb : ∀ g ∈ X, N.OnBlob (N.src g) := by
            intro g hg
            rcases hg.1 with h | h
            · exact ⟨B_r, hB_r, h ▸ hr⟩
            · exact ⟨B_o, hB_o, h ▸ ho⟩
          by_cases hsink : ∃ f, N.src f = o ∧ ¬ N.IsTreeArc f
          · obtain ⟨f, hfo, hft⟩ := hsink
            refine hhub X r hX ⟨_, her⟩ (fun hl => hl e_r hsr) ?_ honb ⟨e_r, her, e_o, heo, hre⟩
            intro g hg
            rcases hg.1 with h | h
            · exact Or.inl h
            · exact Or.inr ⟨f, fun hm => hft hm.2, hfo.trans h.symm⟩
          · -- the other node becomes a leaf, and a recombination node goes
            push Not at hsink
            have horec : N.IsRecomb o := hB_o.isRecomb_of_forall ho fun f hf hc' => hsink f hf hc'
            have hex : ∀ r' : M, ∃ l : V, N.IsLeaf l ∧ N.label l = r'.1 := fun r' => by
              obtain ⟨l, hl, hlr⟩ := hd.surjOn r'.2
              exact ⟨l, hl, hlr⟩
            choose lf hlf hlf' using hex
            have hc₁ : ∀ r' : M, (N.hubNet X r hX).label (some (lf r')) = r'.1 := hlf'
            have hsites : ∀ i, (N.hubNet X r hX).Kept (fun r' : M => some (lf r')) ((N.hubNet X r hX).tgt ((N.hubNet X r hX).site i)) :=
              fun i => Network.kept_tgt_site hc₁ (hC.exists_ne _ i)
            have hbreak : ∀ {z : V}, N.IsRecomb z → ∀ {C : Set ι}, (N.hubNet X r hX).BreaksAt (some z) C → N.BreaksAt z C := by
              rintro z ⟨e₁, f₁, hne₁, rfl, hf₁⟩ C hb g hg
              have hgX : g ∉ X := by
                by_cases hge : g = e₁
                · rw [hge]
                  exact Network.not_mem_of_onCycle hX (Network.onCycle_of_tgt_eq hne₁ hf₁.symm)
                · exact Network.not_mem_of_onCycle hX (Network.onCycle_of_tgt_eq hge hg)
              have := hb (some g) (by rw [Network.hubNet_tgt_some, hg])
              rwa [Network.hubNet_src_of_notMem hgX] at this
            -- the count is strict
            have hlt : Nat.card {x // (N.hubNet X r hX).IsRecomb x ∧ (N.hubNet X r hX).Kept (fun r' : M => some (lf r')) x} < K := by
              have hm : ∀ x : {x // (N.hubNet X r hX).IsRecomb x ∧ (N.hubNet X r hX).Kept (fun r' : M => some (lf r')) x},
                  ∃ y : {x // N.IsRecomb x}, x.1 = some y.1 := by
                rintro ⟨_ | z, hx, -⟩
                · exact absurd hx Network.hubNet_not_isRecomb_none
                · exact ⟨⟨z, Network.hubNet_isRecomb_some.1 hx⟩, rfl⟩
              choose g hg using hm
              have hginj : Function.Injective g := fun x y hxy => Subtype.ext (by rw [hg x, hg y, hxy])
              have hnsurj : ¬ Function.Surjective g := by
                intro hs
                obtain ⟨x, hx⟩ := hs ⟨o, horec⟩
                have hxo : x.1 = some o := by rw [hg x, hx]
                obtain ⟨r', hre'⟩ := x.2.2
                rw [hxo] at hre'
                rcases Relation.ReflTransGen.cases_head hre' with h | ⟨b, ⟨f, hf₁, -⟩, -⟩
                · have hlo : o = lf r' := by simpa using h
                  exact hlf r' e_o (hso.trans hlo)
                · rcases f with _ | f
                  · have hro' : r = o := by simpa [Network.hubNet_src_none] using hf₁
                    exact hro hro'
                  · by_cases hfX : f ∈ X
                    · rw [Network.hubNet_src_of_mem hfX] at hf₁
                      simp at hf₁
                    · rw [Network.hubNet_src_of_notMem hfX] at hf₁
                      have hfo : N.src f = o := by simpa using hf₁
                      exact hfX ⟨Or.inr hfo, hsink f hfo⟩
              have := Fintype.ofFinite {x // N.IsRecomb x}
              have := Fintype.ofFinite {x // (N.hubNet X r hX).IsRecomb x ∧ (N.hubNet X r hX).Kept (fun r' : M => some (lf r')) x}
              rw [← hK, Network.recombCount, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
              exact Fintype.card_lt_of_injective_not_surjective g hginj hnsurj
            have hN₃ := Network.trim_recombCount_le (N := N.hubNet X r hX) (hM := hM) (hanchor := hc₁) (hsite := hsites)
            obtain ⟨V₄, E₄, i₁, i₂, N₄, h₀₄, h₁₄, h₂₄, h₃₄, h₄₄⟩ := hPreduce V E N hP _ _ ((N.hubNet X r hX).trim (fun r' : M => some (lf r')) hM hc₁ hsites)
              (Network.trim_obeys (Network.hubNet_obeys hX hc)) Network.trim_derives hS (by
                rintro (⟨_ | z, hv⟩ | r') hx
                · exact absurd (Network.trim_isRecomb hx) Network.hubNet_not_isRecomb_none
                · have hz := Network.hubNet_isRecomb_some.1 (Network.trim_isRecomb hx)
                  exact ⟨z, hz, fun C hb => hbreak hz (Network.trim_breaksAt hb)⟩
                · exact absurd hx Network.not_trim_isRecomb_inr)
            have hN₄ : N₄.recombCount < K := lt_of_le_of_lt (h₄₄.trans hN₃) hlt
            obtain ⟨V', E', i₃, i₄, N', h₀', h₁', h₂', h₃', h₄', h₅'⟩ := ihK _ hN₄ _ V₄ E₄ N₄ h₀₄ h₁₄ h₂₄ h₃₄ rfl rfl
            exact ⟨V', E', i₃, i₄, N', h₀', h₁', h₂', h₃', h₄', h₅'.trans hN₄.le⟩
        have ht₁ : N.IsTreeArc e := Network.isTreeArc_of_exit hnd hB₁ (hes ▸ hvm) (het)
        have ht₂ : N.IsTreeArc e' := Network.isTreeArc_of_exit hnd hB₂ (hes' ▸ hvm') (het')
        by_cases hacyc : ∀ g, ((N.src g = v ∨ N.src g = v') ∧ N.IsTreeArc g) → ¬ N.Reach (N.tgt g) v
        · exact hkey v v' B₁ B₂ e e' hB₁ hB₂ hvm hvm' hes hes' ht₁ ht₂ hne hlab.symm hacyc
        · push Not at hacyc
          obtain ⟨g, ⟨hg₁, hg₂⟩, hg₃⟩ := hacyc
          have hgv' : N.src g = v' := by
            rcases hg₁ with h | h
            · exact absurd (h ▸ hg₃) (Network.not_reach_tgt_src g)
            · exact h
          refine hkey v' v B₂ B₁ e' e hB₂ hB₁ hvm' hvm hes' hes ht₂ ht₁ (Ne.symm hne) hlab ?_
          rintro k ⟨hk₁, hk₂⟩ hk₃
          rcases hk₁ with h | h
          · exact Network.not_reach_tgt_src k (h ▸ hk₃)
          · -- `v'` above `v` above `v'`
            have h₁ : N.Reach v' v := hgv' ▸ Relation.ReflTransGen.head (Network.arc_src_tgt g) hg₃
            exact Network.not_reach_tgt_src k (h ▸ (hk₃.trans h₁))
      · -- two exits at one node
        push Not at hu
        obtain ⟨B, e, f, hB, hs, ht, hsf, htf, hef⟩ := hu
        have hte := Network.isTreeArc_of_exit hnd hB hs ht
        have htf' := Network.isTreeArc_of_exit hnd hB (hsf ▸ hs) htf
        set X : Set E := {g | N.src g = N.src e ∧ N.IsTreeArc g} with hXdef
        have hX : N.HubCond X (N.src e) := ⟨fun g hg => hg.2, fun g hg => by rw [hg.1], fun g hg h =>
          Network.not_reach_tgt_src g (hg.1 ▸ h)⟩
        exact hhub X (N.src e) hX ⟨e, rfl, hte⟩ (fun hl => hl e rfl) (fun g hg => Or.inl hg.1)
          (fun g hg => ⟨B, hB, hg.1 ▸ hs⟩) ⟨e, ⟨rfl, hte⟩, f, ⟨hsf, htf'⟩, hef⟩

/-- The induction for fully decomposed networks: when a recombination node goes, Lemma 5 and Theorem 3 give a fully decomposed network with no more recombination nodes. -/
theorem exists_isEfficient_aux (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∀ (K n : ℕ) (V E : Type) [Finite V] [Finite E] (N : Network ι V E), N.IsFullyDecomposedFor (conflictGraph S M) → N.Obeys c → N.Derives M → N.ancestral = S →
      N.recombCount = K → N.exitCount = n →
      ∃ (V' E' : Type) (_ : Finite V') (_ : Finite E') (N' : Network ι V' E'), N'.IsFullyDecomposedFor (conflictGraph S M) ∧ N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧
        N'.IsEfficient ∧ N'.recombCount ≤ K := by
  refine exists_isEfficient_core c M S hM hC (fun _ _ N => N.IsFullyDecomposedFor (conflictGraph S M)) (fun _ _ _ h => h.nodeDisjoint)
    (fun _ _ _ _ _ _ _ hX h => Network.hubNet_isFullyDecomposedFor hX h) ?_
  intro V E _ _ N hf V₃ E₃ _ _ N₃ h₁ h₂ h₃ hrec
  have hz : ∀ x, N₃.IsRecomb x → N₃.IsZeroComponent (conflictGraph S M) x ∨ N₃.IsOneComponent (conflictGraph S M) x := by
    intro x hx
    obtain ⟨z, hz, hb⟩ := hrec x hx
    by_cases hex : ∃ C : (conflictGraph S M).ConnectedComponent, N₃.BreaksAt x C.supp
    · obtain ⟨C, hC'⟩ := hex
      exact Or.inr ⟨C, hC', fun C' hC'' => hf.breaksAt_unique hz (hb _ hC'') (hb _ hC')⟩
    · push Not at hex
      exact Or.inl hex
  have h5 := lemma5 hC N₃ h₁ h₂ h₃ hz
  obtain ⟨a, b, N₄, k₁, k₂, k₃, k₄, k₅⟩ := theorem3 c M S hM hC
  exact ⟨Fin a, Fin b, inferInstance, inferInstance, N₄, k₄, k₁, k₂, k₃, k₅.trans_le h5⟩

/-- **Line 330** (`g:efficient`). "If `N` is not efficient, it can be easily modified to become efficient without increasing the
number of recombinations used. Also, if `N` is fully-decomposed, then the efficient network derived from it is also
fully-decomposed." For both graphs, `G(M)` and `G_S(M)`. The paper gives no modification, and it isn't so easy: moving the exits of a node to another node with the same label can leave a recombination node as a new leaf. Then a recombination node is
wasted, and Lemma 5 and Theorem 3 give a fully decomposed network with fewer of them. So the proof is by induction, in `exists_isEfficient_core`, and uses the paper's standing assumption, that no column is constant. For a network that isn't fully decomposed, see `exists_isEfficient_of_any`. -/
theorem exists_isEfficient {V E : Type*} [Finite V] [Finite E] (N : Network ι V E) {c : Crossover}
    {M : Finset (ι → Bool)} {G : SimpleGraph ι} (hC : NoConstantColumn M) (hc : N.Obeys c) (hd : N.Derives M)
    (hG : G = incompatGraph M ∨ G = conflictGraph N.ancestral M) (hf : N.IsFullyDecomposedFor G) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = N.ancestral ∧
      N'.IsFullyDecomposedFor G ∧ N'.IsEfficient ∧ N'.recombCount ≤ N.recombCount := by
  obtain ⟨l, hl, -⟩ := Network.exists_isLeaf_reach (N := N) N.root
  have hM : M.Nonempty := ⟨_, hd.mapsTo hl⟩
  -- the graphs have the same components
  have hG' : ∀ i j, G.Reachable i j ↔ (conflictGraph N.ancestral M).Reachable i j := by
    rcases hG with rfl | rfl
    · exact fun i j => (reachable_conflictGraph_iff hd hf i j).symm
    · exact fun _ _ => Iff.rfl
  have hfS := hf.of_reachable_iff hG'
  obtain ⟨a₀, b₀, N₀, eV₀, eE₀, hiso₀⟩ := N.exists_fin_iso
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hiso₀.invariants
  obtain ⟨V', E', i₁, i₂, N', h₄', h₁', h₂', h₃', h₅', h₆'⟩ := exists_isEfficient_aux c M N.ancestral hM hC _ _ (Fin a₀) (Fin b₀) N₀ ((h₅ _).2 hfS) ((h₂ c).2 hc)
    ((h₃ M).2 hd) h₄ rfl rfl
  obtain ⟨a, b, N'', eV, eE, hiso⟩ := N'.exists_fin_iso
  obtain ⟨k₁, k₂, k₃, k₄, k₅⟩ := hiso.invariants
  refine ⟨a, b, N'', (k₂ c).2 h₁', (k₃ M).2 h₂', k₄.trans h₃', ((k₅ _).2 h₄').of_reachable_iff fun i j => (hG' i j).symm, hiso.isEfficient h₅', ?_⟩
  rw [k₁]
  exact h₆'.trans h₁.le

/-- **Line 329 for any network** (`g:efficient_any`): "If `N` is not efficient, it can be easily modified to become efficient without increasing the number of recombinations used." Here `N` needn't be fully decomposed. The convention of line 140 comes first, by `exists_blobsNodeDisjoint`, and
when a recombination node goes, the rest is trimmed and the convention is restored. The standing assumption says that trimming keeps all the sites. -/
theorem exists_isEfficient_of_any {V E : Type*} [Finite V] [Finite E] (N : Network ι V E) {c : Crossover} {M : Finset (ι → Bool)} (hC : NoConstantColumn M) (hc : N.Obeys c)
    (hd : N.Derives M) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = N.ancestral ∧ N'.BlobsNodeDisjoint ∧ N'.IsEfficient ∧ N'.recombCount ≤ N.recombCount := by
  obtain ⟨l, hl, -⟩ := Network.exists_isLeaf_reach (N := N) N.root
  have hM : M.Nonempty := ⟨_, hd.mapsTo hl⟩
  obtain ⟨a₀, b₀, N₀, h₁, h₂, h₃, h₄, h₅, -, -⟩ := N.exists_blobsNodeDisjoint hc
  obtain ⟨V', E', i₁, i₂, N', h₀', h₁', h₂', h₃', h₄', h₅'⟩ := exists_isEfficient_core c M N.ancestral hM hC (fun _ _ N => N.BlobsNodeDisjoint) (fun _ _ _ h => h)
    (fun _ _ _ _ _ _ _ hX h => Network.hubNet_blobsNodeDisjoint hX h) (by
      intro V E _ _ _ _ V₃ E₃ _ _ N₃ k₁ k₂ k₃ _
      obtain ⟨a, b, N₄, l₁, l₂, l₃, l₄, l₅, -, -⟩ := N₃.exists_blobsNodeDisjoint k₁
      exact ⟨Fin a, Fin b, inferInstance, inferInstance, N₄, l₂, l₁, l₅ M k₂, l₃.trans k₃, l₄.le⟩)
    _ _ (Fin a₀) (Fin b₀) N₀ h₂ h₁ (h₅ M hd) h₃ rfl rfl
  obtain ⟨a, b, N'', eV, eE, hiso⟩ := N'.exists_fin_iso
  obtain ⟨k₁, k₂, k₃, k₄, -⟩ := hiso.invariants
  refine ⟨a, b, N'', (k₂ c).2 h₁', (k₃ M).2 h₂', k₄.trans h₃', hiso.blobsNodeDisjoint.2 h₀', hiso.isEfficient h₄', ?_⟩
  rw [k₁]
  exact h₅'.trans h₄.le

end Efficient

/-- **Line 330** (`g:efficient_exists`). "So for any `M`, there is a efficient fully-decomposed phylogenetic network for `M`." -/
theorem exists_efficient_fullyDecomposed [Finite ι] (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧
      N.IsFullyDecomposedFor (incompatGraph M) ∧ N.IsEfficient := by
  obtain ⟨a, b, N, h₁, h₂, h₃⟩ := theorem1 c M hM hC
  obtain ⟨a', b', N', h₁', h₂', -, h₄', h₅', -⟩ := exists_isEfficient N hC h₁ h₂ (Or.inl rfl) h₃
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

/-- **Theorem 4 as printed fails on a root of degree two** (`g:thm4_false_root`). `M = {0, 1}` on one site, in any crossover model. The network with a root and two leaves
is efficient and fully decomposed, since it has no blob. Its `T′` has three nodes, and `T̄` has two. This is a convention of the paper and not an error: every network for two rows has such a root, and line 418 itself places a root on an edge. Read `T′` with the root suppressed. -/
theorem theorem4Printed_false_rootDegreeTwo (c : Crossover) : ¬ Theorem4Printed c oneSiteRows := by
  intro h
  have hinj := rootDegreeTwoNet_tgt_injective
  obtain ⟨f, -⟩ := h 3 2 rootDegreeTwoNet (Network.obeys_of_tgt_injective hinj c) rootDegreeTwoNet_derives
    (Network.isFullyDecomposedFor_of_tgt_injective hinj _) (Network.isEfficient_of_tgt_injective hinj) trivial 2 _ _ _
    oneSite_isTBar
  have hle := Fintype.card_le_of_injective _ (f.injective.comp (Network.toBlobNode_injective_of_tgt_injective hinj))
  simp at hle

end RootDegreeTwo

section Normal

variable {V E : Type*} {N : Network ι V E} {M : Finset (ι → Bool)}

/-- What all the conditions for `T′ ≅ T̄` have in common. No recombination node is a leaf: that's a convention of the paper (Figure 1's caption, line 341). And an arc that isn't pendant, with both ends off the blobs, has a site, so that it carries a character.
That is a case line 97 allows and the statement must exclude: `theorem4_false_siteFree` shows that the theorem fails on one. -/
structure Network.RegularArcs (N : Network ι V E) : Prop where
  recomb_not_leaf : ∀ x, N.IsRecomb x → ¬ N.IsLeaf x
  arc_labelled : ∀ e, N.IsTreeArc e → ¬ N.OnBlob (N.src e) → ¬ N.OnBlob (N.tgt e) → ¬ N.IsLeaf (N.tgt e) → ∃ i, N.site i = e

/-- **The claim of line 342**, with the conditions of `RegularArcs`: "if we remove edge `e` from `N`, two disconnected subnetworks are created [...] in the other subnetwork, no leaf label contains `S_v(C)`". It's a hypothesis here and not a structural condition. On efficient networks it's equivalent to
`Network.IsTreeNormalStructural` (`Network.isTreeNormalStructural_iff_line342Claim`). -/
structure Network.Line342Claim (N : Network ι V E) : Prop extends N.RegularArcs where
  exit_split : ∀ B e v, N.IsBlob B → N.src e ∈ N.blobVerts B → N.tgt e ∉ N.blobVerts B → N.IsLeaf v →
    ¬ N.Reach (N.tgt e) v → ∃ i, N.site i ∈ B ∧ N.label v i ≠ N.label (N.src e) i

/-- The degree condition of Theorem 4: every node of `T′` of degree at most two has a leaf of `N`. It excludes a root of degree one or two off a blob, and a node of in-degree and out-degree one. It's a convention of the paper: read `T′` with the root suppressed (line 418), and line 364 assumes the second. -/
def Network.DegreeCond (N : Network ι V E) : Prop :=
  ∀ v, (N.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, N.IsLeaf l ∧ N.toBlobNode l = v

/-- The conditions under which the counterexamples to Theorem 4 still work: `RegularArcs` and the degree condition. So it's neither of the paper's conventions that makes them fail. -/
structure Network.IsRegular (N : Network ι V E) : Prop extends N.RegularArcs where
  degree : N.DegreeCond

/-- Lines 326 to 328 for one blob at a time: no two external nodes of one blob have one label, and each external node has exactly one edge off the blob. The printed `IsEfficient` compares external nodes of all the blobs, which the proof of Theorem 4 doesn't use; it's implied by `T′ ≅ T̄`
(`theorem4_iff`). -/
structure Network.IsEfficientPerBlob (N : Network ι V E) : Prop where
  label_inj : ∀ B v v', N.IsBlob B → N.IsExternal B v → N.IsExternal B v' → N.label v = N.label v' → v = v'
  exit_unique : ∀ B e f, N.IsBlob B → N.src e ∈ N.blobVerts B → N.tgt e ∉ N.blobVerts B →
    N.src f = N.src e → N.tgt f ∉ N.blobVerts B → e = f

omit [LinearOrder ι] in
theorem Network.IsEfficient.perBlob (he : N.IsEfficient) : N.IsEfficientPerBlob :=
  ⟨fun B v v' hB h₁ h₂ hl => he.label_inj B B v v' hB hB h₁ h₂ hl, he.exit_unique⟩

omit [LinearOrder ι] in
theorem Network.arcSide_subset (hd : N.Derives M) (e : E) : N.arcSide e ⊆ M := by
  rintro _ ⟨v, hv, -, rfl⟩
  exact hd.mapsTo hv

omit [LinearOrder ι] in
theorem Network.mem_arcSide_iff (hd : N.Derives M) {l : V} (hl : N.IsLeaf l) (e : E) :
    N.label l ∈ N.arcSide e ↔ N.Reach (N.tgt e) l := by
  constructor
  · rintro ⟨v, hv, hr, hvl⟩
    rwa [← hd.injOn hv hl hvl]
  · exact fun h => ⟨l, hl, h, rfl⟩

omit [LinearOrder ι] in
theorem mem_charSide_iff {k : SuperChar M} {r : ι → Bool} :
    r ∈ charSide k ↔ r ∈ M ∧ k.1.supp.domRestrict r = k.2.1 := by
  simp [charSide, charValue]

omit [LinearOrder ι] in
theorem charSplits_diff {X : Set (ι → Bool)} (h : X ∈ charSplits M) : (M : Set (ι → Bool)) \ X ∈ charSplits M := by
  obtain ⟨k, rfl | rfl⟩ := h
  · exact ⟨k, Or.inr rfl⟩
  · refine ⟨k, Or.inl (Set.sdiff_sdiff_cancel_left ?_)⟩
    exact fun r hr => (mem_charSide_iff.1 hr).1

omit [LinearOrder ι] in
theorem Network.treeSplits_diff (hd : N.Derives M) {X : Set (ι → Bool)} (h : X ∈ N.treeSplits M) : (M : Set (ι → Bool)) \ X ∈ N.treeSplits M := by
  obtain ⟨e, he, rfl | rfl⟩ := h
  · exact ⟨e, he, Or.inr rfl⟩
  · exact ⟨e, he, Or.inl (Set.sdiff_sdiff_cancel_left (N.arcSide_subset hd e))⟩

variable [Finite V] [Finite E]

omit [LinearOrder ι] in
/-- **A site on a tree arc splits the rows as the arc does.** The rows with its state below the arc are the rows below the arc. -/
theorem Network.IsTreeArc.label_eq_iff_reach {e : E} (he : N.IsTreeArc e) {i : ι} (hi : N.site i = e) {t : V} :
    N.label t i = N.label (N.tgt e) i ↔ N.Reach (N.tgt e) t := by
  have hr : N.Reach (N.tgt e) (N.tgt (N.site i)) := hi ▸ Relation.ReflTransGen.refl
  constructor
  · intro h
    by_contra hnot
    have h₁ := Network.label_eq_root_of_not_reach hr hnot
    have h₂ := Network.label_eq_root_of_not_reach hr (Network.not_reach_tgt_src e)
    rw [he.label_tgt_of_site_eq hi, h₁, h₂] at h
    simp at h
  · exact fun h => he.label_eq_of_reach (Or.inl hi) h

/-- All the sites of a component are on one side of a tree arc: on one blob, for a non-trivial one, by the converse of Theorem 1. -/
theorem Network.IsTreeArc.reach_site_iff {e : E} (he : N.IsTreeArc e) (hd : N.Derives M) (c : (incompatGraph M).ConnectedComponent) {i j : ι}
    (hi : i ∈ c.supp) (hj : j ∈ c.supp) : N.Reach (N.tgt e) (N.tgt (N.site i)) ↔ N.Reach (N.tgt e) (N.tgt (N.site j)) := by
  by_cases hij : i = j
  · rw [hij]
  · obtain ⟨B, hB, hsub⟩ := converse N hd c ⟨i, hi, j, hj, hij⟩
    exact he.reach_iff_of_toBlobNode_eq (hB.toBlobNode_eq (Network.tgt_mem_blobVerts (hsub i hi)) (Network.tgt_mem_blobVerts (hsub j hj)))

/-- **`g:tree_compatible`**. Every split of a tree arc of any network for `M` is compatible with every character of `B`. So `T′` and `T̄`
always have a common refinement, whether or not the network is fully decomposed. This is what's left of the invariance when
the assumptions of `theorem4` fail. The reason: each non-trivial component is on one blob, so on one side of the tree arc its
sequence is constant. -/
theorem treeSplits_compatible (N : Network ι V E) (hd : N.Derives M) {A : Set (ι → Bool)} (hA : A ∈ N.treeSplits M) (k : SuperChar M) :
    A ∩ charSide k = ∅ ∨ A \ charSide k = ∅ ∨ (M : Set (ι → Bool)) \ A ∩ charSide k = ∅ ∨
      ((M : Set (ι → Bool)) \ A) \ charSide k = ∅ := by
  obtain ⟨e, he, hA'⟩ := hA
  have hconst : ∀ D : Set (ι → Bool), D ⊆ M → (∀ r ∈ D, ∀ r' ∈ D, k.1.supp.domRestrict r = k.1.supp.domRestrict r') →
      D ∩ charSide k = ∅ ∨ D \ charSide k = ∅ := by
    intro D hD hc
    by_cases hex : ∃ r, r ∈ D ∩ charSide k
    · obtain ⟨r, hr, hr'⟩ := hex
      right
      ext r'
      simp only [Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro hr''
      refine mem_charSide_iff.2 ⟨hD hr'', (hc r' hr'' r hr).trans (mem_charSide_iff.1 hr').2⟩
    · left
      exact Set.eq_empty_iff_forall_notMem.2 fun r hr => hex ⟨r, hr⟩
  have hsub := N.arcSide_subset hd e
  have hdd : (M : Set (ι → Bool)) \ ((M : Set (ι → Bool)) \ N.arcSide e) = N.arcSide e := Set.sdiff_sdiff_cancel_left hsub
  by_cases hall : ∃ i ∈ k.1.supp, N.Reach (N.tgt e) (N.tgt (N.site i))
  · obtain ⟨i₀, hi₀, hr₀⟩ := hall
    have hc := hconst ((M : Set (ι → Bool)) \ N.arcSide e) Set.sdiff_subset (by
      rintro r ⟨hr, hr'⟩ r' ⟨hr₁, hr₁'⟩
      obtain ⟨l, hl, rfl⟩ := hd.surjOn hr
      obtain ⟨l', hl', rfl⟩ := hd.surjOn hr₁
      have h₁ : ¬ N.Reach (N.tgt e) l := fun h => hr' ((N.mem_arcSide_iff hd hl e).2 h)
      have h₂ : ¬ N.Reach (N.tgt e) l' := fun h => hr₁' ((N.mem_arcSide_iff hd hl' e).2 h)
      funext i
      have hi : N.Reach (N.tgt e) (N.tgt (N.site i)) := (he.reach_site_iff hd k.1 hi₀ i.2).1 hr₀
      exact (Network.label_eq_root_of_not_reach hi h₁).trans (Network.label_eq_root_of_not_reach hi h₂).symm)
    rcases hA' with rfl | rfl
    · rcases hc with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · rcases hc with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · push Not at hall
    have hc := hconst (N.arcSide e) hsub (by
      rintro _ ⟨l, hl, hr, rfl⟩ _ ⟨l', hl', hr', rfl⟩
      funext i
      exact (he.label_eq_of_reach (Or.inr (hall i.1 i.2)) hr).trans (he.label_eq_of_reach (Or.inr (hall i.1 i.2)) hr').symm)
    rcases hA' with rfl | rfl
    · rcases hc with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [hdd]
      rcases hc with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))

omit [LinearOrder ι] in
/-- If no row off the exit has the super-character at its source, the split of the exit is the split of that super-character: "edge `e` defines exactly the same bi-partition
of the sequences in `M` that is defined by the split `K` in `T̄`" (line 343). -/
theorem Network.charSide_eq_arcSide_of_exit (hd : N.Derives M) {B : Set E} (hB : N.IsBlob B)
    {c : (incompatGraph M).ConnectedComponent} (hiff : ∀ i, N.site i ∈ B ↔ i ∈ c.supp) {e : E} (he : N.IsTreeArc e) (hs : N.src e ∈ N.blobVerts B)
    (hexit : ∀ l, N.IsLeaf l → ¬ N.Reach (N.tgt e) l → ∃ i, N.site i ∈ B ∧ N.label l i ≠ N.label (N.src e) i) {S₀ : c.supp → Bool} (hS₀ : S₀ ∈ restrictRows c.supp M)
    (hl : c.supp.domRestrict (N.label (N.src e)) = S₀) :
    charSide (⟨c, ⟨S₀, hS₀⟩⟩ : SuperChar M) = N.arcSide e := by
  ext r
  rw [mem_charSide_iff]
  constructor
  · rintro ⟨hr, hrS⟩
    obtain ⟨l, hl', rfl⟩ := hd.surjOn hr
    refine (N.mem_arcSide_iff hd hl' e).2 ?_
    by_contra hnot
    obtain ⟨i, hi, hne⟩ := hexit l hl' hnot
    exact hne (congrFun (hrS.trans hl.symm) ⟨i, (hiff i).1 hi⟩)
  · rintro ⟨l, hl', hr, rfl⟩
    refine ⟨hd.mapsTo hl', Eq.trans ?_ hl⟩
    funext i
    exact hB.label_eq_of_exit he hs ((hiff i.1).2 i.2) hr

omit [LinearOrder ι] in
/-- If no exit of a blob carries its ancestral super-character, the split of the arc entering the blob is the split of that super-character. The proof at
lines 340 to 344 doesn't handle this edge. -/
theorem Network.charSide_eq_diff_arcSide_of_top (hd : N.Derives M) (hr₀ : ∀ x, N.IsRecomb x → ¬ N.IsLeaf x) (hnd : N.BlobsNodeDisjoint) {B : Set E} (hB : N.IsBlob B)
    {c : (incompatGraph M).ConnectedComponent} (hiff : ∀ i, N.site i ∈ B ↔ i ∈ c.supp) {g : E} (htop : N.IsBlobTop B (N.tgt g))
    (hexit : ∀ e, N.IsTreeArc e → N.src e ∈ N.blobVerts B → N.tgt e ∉ N.blobVerts B → ∃ i, N.site i ∈ B ∧ N.label (N.src e) i ≠ N.label (N.tgt g) i)
    {S₀ : c.supp → Bool} (hS₀ : S₀ ∈ restrictRows c.supp M) (hl : c.supp.domRestrict (N.label (N.tgt g)) = S₀) :
    charSide (⟨c, ⟨S₀, hS₀⟩⟩ : SuperChar M) = (M : Set (ι → Bool)) \ N.arcSide g := by
  ext r
  rw [mem_charSide_iff]
  constructor
  · rintro ⟨hr, hrS⟩
    refine ⟨hr, ?_⟩
    obtain ⟨v, hv, rfl⟩ := hd.surjOn hr
    intro hbelow
    have hr' := (N.mem_arcSide_iff hd hv g).1 hbelow
    rcases htop.position hnd hB hr' with hvB | ⟨e, he₁, he₂, he₃, he₄⟩
    · exact hr₀ v (hB.isRecomb_of_isLeaf hvB hv) hv
    · obtain ⟨i, hi, hne⟩ := hexit e he₁ he₂ he₃
      refine hne ?_
      rw [← hB.label_eq_of_exit he₁ he₂ hi he₄]
      have hi' : i ∈ c.supp := (hiff i).1 hi
      exact (congrFun hrS ⟨i, hi'⟩).trans (congrFun hl ⟨i, hi'⟩).symm
  · rintro ⟨hr, hnot⟩
    refine ⟨hr, ?_⟩
    obtain ⟨v, hv, rfl⟩ := hd.surjOn hr
    have hv' : ¬ N.Reach (N.tgt g) v := fun h => hnot ((N.mem_arcSide_iff hd hv g).2 h)
    refine Eq.trans ?_ hl
    funext i
    exact htop.label_eq_of_not_reach hnd hB ((hiff i.1).2 i.2) hv'

omit [LinearOrder ι] in
/-- The sequence of the trivial component of a site on a tree arc is that of the arc's split. -/
theorem Network.charSide_eq_arcSide_of_site (hd : N.Derives M) {e : E} (he : N.IsTreeArc e) {i : ι} (hi : N.site i = e)
    {c : (incompatGraph M).ConnectedComponent} (hc : ∀ j, j ∈ c.supp ↔ j = i) {S₀ : c.supp → Bool} (hS₀ : S₀ ∈ restrictRows c.supp M) :
    (S₀ ⟨i, (hc i).2 rfl⟩ = N.label (N.tgt e) i → charSide (⟨c, ⟨S₀, hS₀⟩⟩ : SuperChar M) = N.arcSide e) ∧
      (S₀ ⟨i, (hc i).2 rfl⟩ ≠ N.label (N.tgt e) i → charSide (⟨c, ⟨S₀, hS₀⟩⟩ : SuperChar M) = (M : Set (ι → Bool)) \ N.arcSide e) := by
  have hrow : ∀ r : ι → Bool, c.supp.domRestrict r = S₀ ↔ r i = S₀ ⟨i, (hc i).2 rfl⟩ := by
    intro r
    constructor
    · intro h
      exact congrFun h ⟨i, (hc i).2 rfl⟩
    · intro h
      funext j
      obtain ⟨j, hj⟩ := j
      obtain rfl := (hc j).1 hj
      exact h
  constructor
  · intro h
    ext r
    rw [mem_charSide_iff]
    change r ∈ M ∧ c.supp.domRestrict r = S₀ ↔ _
    rw [hrow, h]
    constructor
    · rintro ⟨hr, hri⟩
      obtain ⟨l, hl, rfl⟩ := hd.surjOn hr
      exact (N.mem_arcSide_iff hd hl e).2 (he.label_eq_iff_reach hi |>.1 hri)
    · rintro ⟨l, hl, hr, rfl⟩
      exact ⟨hd.mapsTo hl, he.label_eq_iff_reach hi |>.2 hr⟩
  · intro h
    ext r
    rw [mem_charSide_iff]
    change r ∈ M ∧ c.supp.domRestrict r = S₀ ↔ _
    rw [hrow]
    constructor
    · rintro ⟨hr, hri⟩
      refine ⟨hr, ?_⟩
      obtain ⟨l, hl, rfl⟩ := hd.surjOn hr
      intro hmem
      have := he.label_eq_iff_reach hi |>.2 ((N.mem_arcSide_iff hd hl e).1 hmem)
      exact h (hri.symm.trans this)
    · rintro ⟨hr, hnot⟩
      refine ⟨hr, ?_⟩
      obtain ⟨l, hl, rfl⟩ := hd.surjOn hr
      have h₁ : N.label l i ≠ N.label (N.tgt e) i := fun h' =>
        hnot ((N.mem_arcSide_iff hd hl e).2 (he.label_eq_iff_reach hi |>.1 h'))
      revert h h₁
      cases N.label l i <;> cases N.label (N.tgt e) i <;> cases S₀ ⟨i, (hc i).2 rfl⟩ <;> simp

/-- The component of a site on a tree arc is trivial, by the converse of Theorem 1. -/
theorem Network.mem_supp_iff_of_isTreeArc (hd : N.Derives M) {i : ι} (hi : N.IsTreeArc (N.site i)) (j : ι) :
    j ∈ ((incompatGraph M).connectedComponentMk i).supp ↔ j = i := by
  constructor
  · intro hj
    by_contra hne
    obtain ⟨B, hB, hsub⟩ := converse N hd ((incompatGraph M).connectedComponentMk i) ⟨i, rfl, j, hj, Ne.symm hne⟩
    exact hi (hB.onCycle_of_mem (hsub i rfl))
  · rintro rfl
    rfl

omit [LinearOrder ι] in
/-- Under the claim of line 342, if a row is off a blob, no exit carries the blob's ancestral super-character. -/
theorem Network.exit_ne_top_of_line342 (hn : N.Line342Claim) (hnd : N.BlobsNodeDisjoint) {B : Set E} (hB : N.IsBlob B) {w : V} (hw : N.IsBlobTop B w) {e : E}
    (hs : N.src e ∈ N.blobVerts B) (ht : N.tgt e ∉ N.blobVerts B) {l : V} (hl : N.IsLeaf l) (hoff : ¬ N.Reach w l) : ∃ i, N.site i ∈ B ∧ N.label (N.src e) i ≠ N.label w i := by
  have hnot : ¬ N.Reach (N.tgt e) l := fun h => hoff ((hw.reach hnd hB hs).trans ((Network.reach_src_tgt e).trans h))
  obtain ⟨i, hi, hne⟩ := hn.exit_split B e l hB hs ht hl hnot
  refine ⟨i, hi, fun h => hne ?_⟩
  rw [hw.label_eq_of_not_reach hnd hB hi hoff, h]

/-- **Lines 341 to 344: each character of `B` is the split of a tree arc**, under the claim of line 342. -/
theorem Network.charSide_mem_treeSplits (hd : N.Derives M) (hf : N.IsFullyDecomposedFor (incompatGraph M)) (hn : N.Line342Claim) (k : SuperChar M) :
    charSide k ∈ N.treeSplits M := by
  obtain ⟨c, S₀, hS₀⟩ := k
  by_cases hnt : c.supp.Nontrivial
  · obtain ⟨B, hB, hsub⟩ := converse N hd c hnt
    obtain ⟨c₀, -, hc₀⟩ := hf.blob_component B hB
    obtain ⟨i₀, hi₀⟩ := hnt.nonempty
    have hcc : c = c₀ := by
      rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hi₀,
        ← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 ((hc₀ i₀).1 (hsub i₀ hi₀))]
    subst hcc
    obtain ⟨z, hzB⟩ : (N.blobVerts B).Nonempty := ⟨_, Network.src_mem_blobVerts (hsub i₀ hi₀)⟩
    obtain ⟨w, hw, -⟩ := Network.exists_isBlobTop_reach hzB
    have hnd := hf.nodeDisjoint
    by_cases hex : ∃ e, N.IsTreeArc e ∧ N.src e ∈ N.blobVerts B ∧ N.tgt e ∉ N.blobVerts B ∧ c.supp.domRestrict (N.label (N.src e)) = S₀
    · obtain ⟨e, he₁, he₂, he₃, he₄⟩ := hex
      exact ⟨e, he₁, Or.inl (N.charSide_eq_arcSide_of_exit hd hB hc₀ he₁ he₂ (fun l hl hnot => hn.exit_split B e l hB he₂ he₃ hl hnot) hS₀ he₄)⟩
    · push Not at hex
      obtain ⟨r₀, hr₀, hr₀S⟩ := mem_restrictRows.1 hS₀
      obtain ⟨l₀, hl₀, rfl⟩ := hd.surjOn hr₀
      have hnot : ¬ N.Reach w l₀ := by
        intro hr
        rcases hw.position hnd hB hr with h | ⟨e, he₁, he₂, he₃, he₄⟩
        · exact hn.recomb_not_leaf l₀ (hB.isRecomb_of_isLeaf h hl₀) hl₀
        · refine hex e he₁ he₂ he₃ ?_
          rw [← hr₀S]
          funext i
          exact (hB.label_eq_of_exit he₁ he₂ ((hc₀ i.1).2 i.2) he₄).symm
      rcases hw.eq_root_or_exists hnd hB with rfl | ⟨g, hg, rfl⟩
      · exact absurd (N.reach_root l₀) hnot
      · refine ⟨g, hg, Or.inr ?_⟩
        have hex : ∀ e, N.IsTreeArc e → N.src e ∈ N.blobVerts B → N.tgt e ∉ N.blobVerts B → ∃ i, N.site i ∈ B ∧ N.label (N.src e) i ≠ N.label (N.tgt g) i :=
          fun e _ he₂ he₃ => N.exit_ne_top_of_line342 hn hnd hB hw he₂ he₃ hl₀ hnot
        refine N.charSide_eq_diff_arcSide_of_top hd hn.recomb_not_leaf hnd hB hc₀ hw hex hS₀ ?_
        rw [← hr₀S]
        funext i
        exact (hw.label_eq_of_not_reach hnd hB ((hc₀ i.1).2 i.2) hnot).symm
  · obtain ⟨i, hi⟩ := c.nonempty_supp
    have hc : ∀ j, j ∈ c.supp ↔ j = i := by
      intro j
      constructor
      · intro hj
        by_contra hne
        exact hnt ⟨j, hj, i, hi, hne⟩
      · rintro rfl
        exact hi
    have hti : N.IsTreeArc (N.site i) := hf.isolated_treeArc i fun j hj => by
      have hjm : j ∈ c.supp := by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hi ⊢
        rw [← hi]
        exact SimpleGraph.ConnectedComponent.eq.2 hj.reachable.symm
      exact hj.ne ((hc j).1 hjm).symm
    obtain ⟨h₁, h₂⟩ := N.charSide_eq_arcSide_of_site hd hti rfl hc hS₀
    by_cases h : S₀ ⟨i, (hc i).2 rfl⟩ = N.label (N.tgt (N.site i)) i
    · exact ⟨_, hti, Or.inl (h₁ h)⟩
    · exact ⟨_, hti, Or.inr (h₂ h)⟩

/-- **Each non-trivial split of a tree arc is a character of `B`**, on what's needed of that arc: the blob at an end of the arc has the sites of one component (not nec. a non-trivial one), the two exit properties hold, and the arc has a site if it's off the blobs. -/
theorem Network.arcSide_mem_charSplits_of (hd : N.Derives M) (hnd : N.BlobsNodeDisjoint) (hone : ∀ B, N.IsBlob B → ∃ c : (incompatGraph M).ConnectedComponent, ∀ i, N.site i ∈ B ↔ i ∈ c.supp)
    (hr : N.RegularArcs) {e : E} (he : N.IsTreeArc e) (hne : ((M : Set (ι → Bool)) \ N.arcSide e).Nonempty) (hne₂ : (N.arcSide e).encard ≠ 1)
    (hexit : ∀ B, N.IsBlob B → N.src e ∈ N.blobVerts B → ∀ l, N.IsLeaf l → ¬ N.Reach (N.tgt e) l → ∃ i, N.site i ∈ B ∧ N.label l i ≠ N.label (N.src e) i)
    (htop : ∀ B, N.IsBlob B → N.IsBlobTop B (N.tgt e) → ∀ f, N.IsTreeArc f → N.src f ∈ N.blobVerts B → N.tgt f ∉ N.blobVerts B →
      ∃ i, N.site i ∈ B ∧ N.label (N.src f) i ≠ N.label (N.tgt e) i) : N.arcSide e ∈ charSplits M := by
  obtain ⟨lb, hlb, hrb⟩ := Network.exists_isLeaf_reach (N := N) (N.tgt e)
  by_cases hsite : ∃ i, N.site i = e
  · obtain ⟨i, hi⟩ := hsite
    have hti : N.IsTreeArc (N.site i) := hi ▸ he
    have hc := N.mem_supp_iff_of_isTreeArc (M := M) hd hti
    have hS₀ : ((incompatGraph M).connectedComponentMk i).supp.domRestrict (N.label (N.tgt e)) ∈
        restrictRows ((incompatGraph M).connectedComponentMk i).supp M := by
      refine mem_restrictRows.2 ⟨N.label lb, hd.mapsTo hlb, ?_⟩
      funext j
      obtain ⟨j, hj⟩ := j
      obtain rfl := (hc j).1 hj
      exact he.label_eq_iff_reach hi |>.2 hrb
    exact ⟨_, Or.inl ((N.charSide_eq_arcSide_of_site hd he hi hc hS₀).1 rfl).symm⟩
  by_cases hs : ∃ B, N.IsBlob B ∧ N.src e ∈ N.blobVerts B
  · obtain ⟨B, hB, hsB⟩ := hs
    obtain ⟨c, hc⟩ := hone B hB
    have hS₀ : c.supp.domRestrict (N.label (N.src e)) ∈ restrictRows c.supp M := by
      refine mem_restrictRows.2 ⟨N.label lb, hd.mapsTo hlb, ?_⟩
      funext i
      exact hB.label_eq_of_exit he hsB ((hc i.1).2 i.2) hrb
    exact ⟨_, Or.inl (N.charSide_eq_arcSide_of_exit hd hB hc he hsB (hexit B hB hsB) hS₀ rfl).symm⟩
  by_cases ht : ∃ B, N.IsBlob B ∧ N.tgt e ∈ N.blobVerts B
  · obtain ⟨B, hB, htB⟩ := ht
    obtain ⟨c, hc⟩ := hone B hB
    have htp : N.IsBlobTop B (N.tgt e) := ⟨htB, fun f hf' h => he (hB.onCycle_of_mem ((he.eq_of_tgt_eq h) ▸ hf'))⟩
    obtain ⟨r₀, hr₀, hr₀'⟩ := hne
    obtain ⟨l₀, hl₀, rfl⟩ := hd.surjOn hr₀
    have hnot : ¬ N.Reach (N.tgt e) l₀ := fun h => hr₀' ((N.mem_arcSide_iff hd hl₀ e).2 h)
    have hS₀ : c.supp.domRestrict (N.label (N.tgt e)) ∈ restrictRows c.supp M := by
      refine mem_restrictRows.2 ⟨N.label l₀, hr₀, ?_⟩
      funext i
      exact htp.label_eq_of_not_reach hnd hB ((hc i.1).2 i.2) hnot
    have h := N.charSide_eq_diff_arcSide_of_top hd hr.recomb_not_leaf hnd hB hc htp (htop B hB htp) hS₀ rfl
    have h₂ := charSplits_diff (⟨_, Or.inl rfl⟩ : charSide (⟨c, ⟨_, hS₀⟩⟩ : SuperChar M) ∈ charSplits M)
    rw [h, Set.sdiff_sdiff_cancel_left (N.arcSide_subset hd e)] at h₂
    exact h₂
  · exfalso
    have hleaf : ¬ N.IsLeaf (N.tgt e) := by
      intro hl
      refine hne₂ ?_
      have : N.arcSide e = {N.label (N.tgt e)} := by
        ext r
        constructor
        · rintro ⟨v, hv, hr', rfl⟩
          rcases Relation.ReflTransGen.cases_head hr' with h | ⟨b, ⟨g, hg, -⟩, -⟩
          · rw [h]; rfl
          · exact absurd hg (hl g)
        · rintro rfl
          exact ⟨_, hl, Relation.ReflTransGen.refl, rfl⟩
      rw [this, Set.encard_singleton]
    exact hsite (hr.arc_labelled e he hs ht hleaf)

/-- **Lines 341 to 344: each non-trivial split of a tree arc is a character of `B`**, under the claim of line 342. Here `hne` is that a row isn't below the arc,
and `hne₂` that the arc has at least two rows below it. -/
theorem Network.arcSide_mem_charSplits (hd : N.Derives M) (hf : N.IsFullyDecomposedFor (incompatGraph M)) (hn : N.Line342Claim) {e : E} (he : N.IsTreeArc e)
    (hne : ((M : Set (ι → Bool)) \ N.arcSide e).Nonempty) (hne₂ : (N.arcSide e).encard ≠ 1) : N.arcSide e ∈ charSplits M := by
  have hnd := hf.nodeDisjoint
  refine N.arcSide_mem_charSplits_of hd hnd (fun B hB => ?_) hn.toRegularArcs he hne hne₂ ?_ ?_
  · obtain ⟨c, -, hc⟩ := hf.blob_component B hB
    exact ⟨c, hc⟩
  · intro B hB hsB l hl hnot
    exact hn.exit_split B e l hB hsB (he.tgt_notMem_blobVerts hB hsB) hl hnot
  · intro B hB htp f _ hf₂ hf₃
    obtain ⟨r₀, hr₀, hr₀'⟩ := hne
    obtain ⟨l₀, hl₀, rfl⟩ := hd.surjOn hr₀
    exact N.exit_ne_top_of_line342 hn hnd hB htp hf₂ hf₃ hl₀ fun h => hr₀' ((N.mem_arcSide_iff hd hl₀ e).2 h)

/-- **The proof of Theorem 4 on splits**, with `exit_split` in its printed form as a hypothesis: the claim of line 342. -/
theorem Network.mem_treeSplits_iff_of_line342 (hd : N.Derives M) (hf : N.IsFullyDecomposedFor (incompatGraph M)) (hn : N.Line342Claim)
    {A : Set (ι → Bool)} (hA : A ⊆ M) (h₁ : 2 ≤ A.encard) (h₂ : 2 ≤ ((M : Set (ι → Bool)) \ A).encard) :
    A ∈ N.treeSplits M ↔ A ∈ charSplits M := by
  have hnonempty : ∀ X : Set (ι → Bool), 2 ≤ X.encard → X.Nonempty := fun X hX => by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    simp at hX
  have hne1 : ∀ X : Set (ι → Bool), 2 ≤ X.encard → X.encard ≠ 1 := fun X hX h => by
    rw [h] at hX
    simp at hX
  have hdd := Set.sdiff_sdiff_cancel_left hA
  constructor
  · rintro ⟨e, he, hAe⟩
    have hsub := N.arcSide_subset hd e
    rcases hAe with rfl | rfl
    · exact N.arcSide_mem_charSplits hd hf hn he (hnonempty _ h₂) (hne1 _ h₁)
    · rw [Set.sdiff_sdiff_cancel_left hsub] at h₂
      exact charSplits_diff (N.arcSide_mem_charSplits hd hf hn he (hnonempty _ h₁) (hne1 _ h₂))
  · rintro ⟨k, rfl | rfl⟩
    · exact N.charSide_mem_treeSplits hd hf hn k
    · exact N.treeSplits_diff hd (N.charSide_mem_treeSplits hd hf hn k)

/-- **No exit of a blob at a node carrying the blob's ancestral super-character**, the label of its top on its sites, if a row lies off the blob. It's what the claim of line 342 says, structurally (`Network.isTreeNormalStructural_iff_line342Claim`).

The exemption "unless the blob is at the root" is `NoAncestralExitAtEntered`, a stronger condition. A blob at the root can have a row at its top (`fourGametes_rootExit`). And so can a blob with no row above it but a site-free arc, for which the conclusion of `theorem4_splits` still holds
(`theorem4_splits_siteFreeRoot`). -/
def Network.NoAncestralExit (N : Network ι V E) : Prop :=
  ∀ B e w, N.IsBlob B → N.IsBlobTop B w → (∃ l, N.IsLeaf l ∧ ¬ N.Reach w l) → N.src e ∈ N.blobVerts B → N.tgt e ∉ N.blobVerts B →
    ∃ i, N.site i ∈ B ∧ N.label (N.src e) i ≠ N.label w i

/-- The same with the entered blobs exempt only at the root: no exit of a blob with an entering arc carries its ancestral super-character. -/
def Network.NoAncestralExitAtEntered (N : Network ι V E) : Prop :=
  ∀ B e w, N.IsBlob B → N.IsBlobTop B w → w ≠ N.root → N.src e ∈ N.blobVerts B → N.tgt e ∉ N.blobVerts B →
    ∃ i, N.site i ∈ B ∧ N.label (N.src e) i ≠ N.label w i

omit [LinearOrder ι] [Finite E] in
theorem Network.NoAncestralExitAtEntered.noAncestralExit (h : N.NoAncestralExitAtEntered) : N.NoAncestralExit := by
  rintro B e w hB hw ⟨l, -, hl⟩ hs ht
  exact h B e w hB hw (fun hr => hl (hr ▸ N.reach_root l)) hs ht

/-- The conditions under which `T′` is `T̄`, with the degree condition (Section 3.7): `RegularArcs`, and no exit of a blob carries the ancestral super-character, if a row lies off the blob. -/
structure Network.IsTreeNormalStructural (N : Network ι V E) : Prop extends N.RegularArcs where
  noAncestralExit : N.NoAncestralExit

omit [LinearOrder ι] in
/-- On an efficient network, the structural condition gives the claim of line 342. -/
theorem Network.IsTreeNormalStructural.line342Claim (hn : N.IsTreeNormalStructural) (hnd : N.BlobsNodeDisjoint) (he : N.IsEfficientPerBlob) : N.Line342Claim where
  toRegularArcs := hn.toRegularArcs
  exit_split := by
    intro B e l hB hs ht hl hnot
    by_contra hne
    push Not at hne
    have het := Network.isTreeArc_of_exit hnd hB hs ht
    obtain ⟨w, hw, -⟩ := Network.exists_isBlobTop_reach hs
    by_cases hr : N.Reach w l
    · rcases hw.position hnd hB hr with h | ⟨e', he₁, he₂, he₃, he₄⟩
      · exact hn.recomb_not_leaf l (hB.isRecomb_of_isLeaf h hl) hl
      · have hlab : N.label (N.src e') = N.label (N.src e) := by
          funext i
          by_cases hi : N.site i ∈ B
          · exact (hB.label_eq_of_exit he₁ he₂ hi he₄).symm.trans (hne i hi)
          · exact hB.label_eq_of_notMem hi he₂ hs
        have hsrc : N.src e' = N.src e := he.label_inj B _ _ hB ⟨he₂, e', rfl, he₃⟩ ⟨hs, e, rfl, ht⟩ hlab
        have hee : e' = e := (he.exit_unique B e e' hB hs ht hsrc he₃).symm
        exact hnot (hee ▸ he₄)
    · obtain ⟨i, hi, hne'⟩ := hn.noAncestralExit B e w hB hw ⟨l, hl, hr⟩ hs ht
      exact hne' ((hne i hi).symm.trans (hw.label_eq_of_not_reach hnd hB hi hr))

omit [LinearOrder ι] in
/-- **The structural condition is the claim of line 342**, on an efficient network. -/
theorem Network.isTreeNormalStructural_iff_line342Claim (hnd : N.BlobsNodeDisjoint) (he : N.IsEfficientPerBlob) : N.IsTreeNormalStructural ↔ N.Line342Claim := by
  refine ⟨fun hn => hn.line342Claim hnd he, fun hn => ⟨hn.toRegularArcs, ?_⟩⟩
  rintro B e w hB hw ⟨l, hl, hoff⟩ hs ht
  exact N.exit_ne_top_of_line342 hn hnd hB hw hs ht hl hoff

/-- **The closest true form of Theorem 4, on splits** (`g:thm4_splits`). The proof at lines 340 to 344 shows that the splits of `T′`
and `T̄` agree, and it's their non-trivial splits that agree, under `IsTreeNormalStructural`. Departure from the paper: the
hypothesis `IsTreeNormalStructural` is added, because the statement is false without it (`theorem4_false_top`, `theorem4_false_siteFree`), and `IsEfficientPerBlob` replaces `IsEfficient`, the proof needing no more. Under them, the argument of the paper
goes through, and handles also the entering edge of a blob, which the proof doesn't mention, and which gets the character of
the ancestral super-character.

The standing assumption isn't used. -/
theorem theorem4_splits (N : Network ι V E) (hd : N.Derives M) (hf : N.IsFullyDecomposedFor (incompatGraph M)) (he : N.IsEfficientPerBlob)
    (hn : N.IsTreeNormalStructural) {A : Set (ι → Bool)} (hA : A ⊆ M) (h₁ : 2 ≤ A.encard)
    (h₂ : 2 ≤ ((M : Set (ι → Bool)) \ A).encard) :
    A ∈ N.treeSplits M ↔ A ∈ charSplits M :=
  N.mem_treeSplits_iff_of_line342 hd hf (hn.line342Claim hf.nodeDisjoint he) hA h₁ h₂

end Normal

section Theorem4

variable {V E : Type*} [Finite V] [Finite E] {N : Network ι V E} {M : Finset (ι → Bool)}

omit [LinearOrder ι] in
/-- Which side of a tree arc a node is on, in `T′`, is whether it's below the arc in `N`. -/
theorem Network.IsTreeArc.sameSide_iff {e : E} (he : N.IsTreeArc e) (x y : V) :
    SameSide N.blobbedTree (N.blobEdge e) (N.toBlobNode x) (N.toBlobNode y) ↔ (N.Reach (N.tgt e) x ↔ N.Reach (N.tgt e) y) := by
  by_cases hx : N.Reach (N.tgt e) x
  · have h₁ := (he.sameSide_tgt_iff x).2 hx
    constructor
    · intro h
      exact iff_of_true hx ((he.sameSide_tgt_iff y).1 (h₁.trans h))
    · intro h
      exact h₁.symm.trans ((he.sameSide_tgt_iff y).2 (h.1 hx))
  · have h₁ := (he.sameSide_src_iff x).2 hx
    constructor
    · intro h
      exact iff_of_false hx ((he.sameSide_src_iff y).1 (h₁.trans h))
    · intro h
      exact h₁.symm.trans ((he.sameSide_src_iff y).2 fun hy => hx (h.2 hy))

variable (N) in
/-- The class in `T′` of the leaf of a row. -/
noncomputable def Network.rowClass (hd : N.Derives M) (r : M) : N.BlobNode :=
  N.toBlobNode (hd.surjOn r.2).choose

omit [LinearOrder ι] [Finite V] [Finite E] in
theorem Network.rowClass_eq (hd : N.Derives M) {r : M} {l : V} (hl : N.IsLeaf l) (hr : N.label l = r) : N.rowClass hd r = N.toBlobNode l := by
  have h := (hd.surjOn r.2).choose_spec
  rw [Network.rowClass, hd.injOn h.1 hl (h.2.trans hr.symm)]

omit [LinearOrder ι] in
/-- On the side of a tree arc, the rows of `T′` are those below it, or those not below it. -/
theorem Network.IsTreeArc.sameSide_rowClass_iff {e : E} (he : N.IsTreeArc e) (hd : N.Derives M) (x y : M) :
    SameSide N.blobbedTree (N.blobEdge e) (N.rowClass hd x) (N.rowClass hd y) ↔ (x.1 ∈ N.arcSide e ↔ y.1 ∈ N.arcSide e) := by
  obtain ⟨hlx, hx⟩ := hd.surjOn x.2 |>.choose_spec
  obtain ⟨hly, hy⟩ := hd.surjOn y.2 |>.choose_spec
  have h₁ := N.mem_arcSide_iff hd hlx e
  have h₂ := N.mem_arcSide_iff hd hly e
  rw [hx] at h₁
  rw [hy] at h₂
  rw [h₁, h₂]
  exact he.sameSide_iff _ _

section TBar

variable {W : Type*} {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W}

/-- The sets of rows that are sides of the edges of a tree are closed under complement, if both sides are nonempty. -/
theorem compl_mem_splitSides {X W : Type*} {T : SimpleGraph W} {φ : X → W} (hT : T.IsTree) {A : Set X} (hA : A ∈ SempleSteel2003.splitSides T φ)
    (hne : Aᶜ.Nonempty) : Aᶜ ∈ SempleSteel2003.splitSides T φ := by
  obtain ⟨e, he, x, rfl⟩ := hA
  obtain ⟨y, hy⟩ := hne
  refine ⟨e, he, y, ?_⟩
  ext z
  constructor
  · intro hz
    by_contra hc
    exact hz (SimpleGraph.Reachable.trans (sameSide_of_not_sameSide (T := T) (e := e) (x := φ x) (y := φ z) (z := φ y) hT.connected
      (fun h => hy h) (fun h => hc (SimpleGraph.Reachable.symm h))) (SimpleGraph.Reachable.refl _))
  · intro hz hxz
    exact hy (SimpleGraph.Reachable.trans hxz (SimpleGraph.Reachable.symm hz))

omit [LinearOrder ι] in
/-- A side of an edge of a connected graph is what that edge splits off. -/
theorem exists_edge_of_mem_splitSides {X : Type*} {φ : X → W} (hT : T.Connected) {A : Set X} (hA : A ∈ SempleSteel2003.splitSides T φ) :
    ∃ e ∈ T.edgeSet, ∀ x y, SameSide T e (φ x) (φ y) ↔ (x ∈ A ↔ y ∈ A) := by
  obtain ⟨e, he, x₀, rfl⟩ := hA
  exact ⟨e, he, fun x y => sameSide_iff_mem_edgeSide hT e x₀ x y⟩

omit [LinearOrder ι] in
/-- The character `k` of `B` is the split of its edge of `T̄`. -/
theorem IsTBar.charSide_mem_splitSides (hT : IsTBar M T φ edge) (k : SuperChar M) :
    {y : M | y.1 ∈ charSide k} ∈ SempleSteel2003.splitSides T φ := by
  obtain ⟨r, hr, hrS⟩ := mem_restrictRows.1 k.2.2
  have hk : charValue k r = true := by
    simp [charValue, hrS]
  refine ⟨edge k, hT.edge_mem k, ⟨r, hr⟩, ?_⟩
  ext y
  change y.1 ∈ charSide k ↔ _
  rw [charSide, Set.mem_ofPred_eq, SempleSteel2003.edgeSide, Set.mem_ofPred_eq]
  have hs := hT.split k ⟨r, hr⟩ y
  simp only [hk] at hs
  constructor
  · rintro ⟨-, hy⟩
    exact hs.1 hy.symm
  · intro h
    exact ⟨y.2, (hs.2 h).symm⟩

omit [LinearOrder ι] in
/-- A row that isn't the only one is the split of the pendant edge of its leaf of `T̄`. -/
theorem IsTBar.singleton_mem_splitSides [Finite W] (hT : IsTBar M T φ edge) (r : M) {r' : M} (hne : r' ≠ r) :
    ({r} : Set M) ∈ SempleSteel2003.splitSides T φ := by
  have hφ : φ r ≠ φ r' := fun h => hne (hT.label_injective h).symm
  obtain ⟨u, hu, -⟩ := SempleSteel2003.exists_adj_reachable_deleteEdges hT.isTree.connected hφ
  refine ⟨s(φ r, u), hu, r, ?_⟩
  ext y
  simp only [Set.mem_singleton_iff, SempleSteel2003.edgeSide, Set.mem_ofPred_eq]
  have hdeg := (hT.mem_range_iff (φ r)).1 ⟨r, rfl⟩
  constructor
  · rintro rfl
    exact SimpleGraph.Reachable.refl _
  · intro h
    exact hT.label_injective (eq_of_sameSide_of_ncard_le_one hdeg hu h)

omit [LinearOrder ι] in
/-- A set of rows, with a row on each side, is a side of an edge of `T̄`, if it's a single row, or all but one, or a split of a character of `B`. -/
theorem IsTBar.mem_splitSides_of_charSplits [Finite W] (hT : IsTBar M T φ edge) {A : Set (ι → Bool)} {y₁ y₀ : M} (hy₁ : y₁.1 ∈ A) (hy₀ : y₀.1 ∉ A)
    (hsp : 2 ≤ A.encard → 2 ≤ ((M : Set (ι → Bool)) \ A).encard → A ∈ charSplits M) : {y : M | y.1 ∈ A} ∈ SempleSteel2003.splitSides T φ := by
  by_cases h1 : A.encard = 1
  · obtain ⟨r, hr⟩ := Set.encard_eq_one.1 h1
    have hy₁r : y₁.1 = r := by
      rw [hr] at hy₁
      exact hy₁
    have hset : {y : M | y.1 ∈ A} = {y₁} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, hr, Subtype.ext_iff, hy₁r]
    rw [hset]
    exact hT.singleton_mem_splitSides y₁ (r' := y₀) fun h => hy₀ (h ▸ hy₁)
  by_cases h2 : ((M : Set (ι → Bool)) \ A).encard = 1
  · obtain ⟨r, hr⟩ := Set.encard_eq_one.1 h2
    have hmem₀ : ∀ y : M, y.1 ∉ A ↔ y.1 = r := by
      intro y
      have : y.1 ∈ (M : Set (ι → Bool)) \ A ↔ y.1 ∉ A := by simp
      rw [← this, hr]
      rfl
    have hset : {y : M | y.1 ∈ A} = {y₀}ᶜ := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, Subtype.ext_iff]
      rw [(hmem₀ y₀).1 hy₀, ← hmem₀ y, not_not]
    rw [hset]
    exact compl_mem_splitSides hT.isTree (hT.singleton_mem_splitSides y₀ (r' := y₁) fun h => hy₀ (h ▸ hy₁)) ⟨y₁, fun h => hy₀ (h ▸ hy₁)⟩
  have hge₁ : 2 ≤ A.encard := by
    have h₀ : A.Nonempty := ⟨y₁.1, hy₁⟩
    have := lt_of_le_of_ne (Set.one_le_encard_iff_nonempty.2 h₀) (Ne.symm h1)
    exact (Order.add_one_le_of_lt this).trans_eq' one_add_one_eq_two.symm
  have hge₂ : 2 ≤ ((M : Set (ι → Bool)) \ A).encard := by
    have h₀ : ((M : Set (ι → Bool)) \ A).Nonempty := ⟨y₀.1, y₀.2, hy₀⟩
    have := lt_of_le_of_ne (Set.one_le_encard_iff_nonempty.2 h₀) (Ne.symm h2)
    exact (Order.add_one_le_of_lt this).trans_eq' one_add_one_eq_two.symm
  obtain ⟨k, hk | hk⟩ := hsp hge₁ hge₂
  · rw [hk]
    exact hT.charSide_mem_splitSides k
  · have hset : {y : M | y.1 ∈ A} = {y : M | y.1 ∈ charSide k}ᶜ := by
      ext y
      rw [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_ofPred_eq, hk]
      simp
    rw [hset]
    refine compl_mem_splitSides hT.isTree (hT.charSide_mem_splitSides k) ?_
    rw [hk] at hy₁
    exact ⟨y₁, fun h => hy₁.2 h⟩

end TBar

omit [LinearOrder ι] [Finite V] [Finite E] in
/-- `T′` with its rows is an `X`-tree, under the degree condition of Theorem 4. -/
theorem Network.rowClass_labelled (hd : N.Derives M) (hdeg : N.DegreeCond)
    (v : N.BlobNode) (h : (N.blobbedTree.neighborSet v).ncard ≤ 2) : v ∈ Set.range (N.rowClass hd) := by
  obtain ⟨l, hl, rfl⟩ := hdeg v h
  exact ⟨⟨N.label l, hd.mapsTo hl⟩, N.rowClass_eq hd hl rfl⟩

omit [LinearOrder ι] in
/-- A tree arc has a row below it and, if each node of `T′` of degree at most two has a row, one not below it. -/
theorem Network.IsTreeArc.exists_rows {e : E} (he : N.IsTreeArc e) (hd : N.Derives M)
    (hlab : ∀ v, (N.blobbedTree.neighborSet v).ncard ≤ 2 → v ∈ Set.range (N.rowClass hd)) : (∃ y : M, y.1 ∈ N.arcSide e) ∧ ∃ y : M, y.1 ∉ N.arcSide e := by
  constructor
  · obtain ⟨l, hl, hr⟩ := Network.exists_isLeaf_reach N (N.tgt e)
    exact ⟨⟨N.label l, hd.mapsTo hl⟩, (N.mem_arcSide_iff hd hl e).2 hr⟩
  · obtain ⟨y, h₁, -⟩ := exists_label_sameSide N.blobbedTree_isTree.1 hlab (N.blobEdge e) (N.blobEdge e) (N.toBlobNode (N.src e))
    refine ⟨y, ?_⟩
    obtain ⟨hly, hy⟩ := hd.surjOn y.2 |>.choose_spec
    rw [← hy, N.mem_arcSide_iff hd hly e, ← he.sameSide_src_iff]
    exact h₁

omit [LinearOrder ι] in
/-- A tree arc's sides in `T′`, as sets of rows. -/
theorem Network.IsTreeArc.edgeSide_eq {e : E} (he : N.IsTreeArc e) (hd : N.Derives M) (x : M) :
    SempleSteel2003.edgeSide N.blobbedTree (N.rowClass hd) (N.blobEdge e) x =
      if x.1 ∈ N.arcSide e then {y : M | y.1 ∈ N.arcSide e} else {y : M | y.1 ∈ N.arcSide e}ᶜ := by
  ext y
  have h := he.sameSide_rowClass_iff hd x y
  change SameSide _ _ _ _ ↔ _
  rw [h]
  by_cases hx : x.1 ∈ N.arcSide e <;> simp [hx]

omit [LinearOrder ι] in
/-- A tree arc with a row on each side gives a split of `T′`. -/
theorem Network.IsTreeArc.mem_splitSides {e : E} (he : N.IsTreeArc e) (hd : N.Derives M) {A : Set M}
    (hA : (∃ x : M, x.1 ∈ N.arcSide e ∧ A = {y : M | y.1 ∈ N.arcSide e}) ∨ (∃ x : M, x.1 ∉ N.arcSide e ∧ A = {y : M | y.1 ∈ N.arcSide e}ᶜ)) :
    A ∈ SempleSteel2003.splitSides N.blobbedTree (N.rowClass hd) := by
  rcases hA with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · exact ⟨N.blobEdge e, Network.blobEdge_mem_edgeSet he, x, by rw [he.edgeSide_eq hd x]; simp [hx]⟩
  · exact ⟨N.blobEdge e, Network.blobEdge_mem_edgeSet he, x, by rw [he.edgeSide_eq hd x]; simp [hx]⟩

omit [LinearOrder ι] [Finite V] [Finite E] in
/-- The arc into a leaf that isn't a recombination node is a tree arc, and its split is the row. -/
theorem Network.exists_pendant (hrl : ∀ x, N.IsRecomb x → ¬ N.IsLeaf x) {l : V} (hl : N.IsLeaf l) (hroot : l ≠ N.root) :
    ∃ g, N.IsTreeArc g ∧ N.arcSide g = {N.label l} := by
  have hex : ∃ g, N.tgt g = l := by
    by_contra hne
    push Not at hne
    exact hroot ((N.root_iff l).1 hne)
  obtain ⟨g, rfl⟩ := hex
  have hg : N.IsTreeArc g := by
    intro hc
    obtain ⟨B, hB, hgB⟩ := N.exists_isBlob_of_onCycle hc
    exact hrl _ (hB.isRecomb_of_isLeaf (Network.tgt_mem_blobVerts hgB) hl) hl
  refine ⟨g, hg, ?_⟩
  ext r
  constructor
  · rintro ⟨v, hv, hr, rfl⟩
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨b, ⟨f, hf, -⟩, -⟩
    · rw [h]; rfl
    · exact absurd hf (hl f)
  · rintro rfl
    exact ⟨_, hl, Relation.ReflTransGen.refl, rfl⟩

variable {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W}

/-- **Line 344**: the splits of `T′` and of `T̄` are equal. So far this is the argument of the paper, for all splits, the trivial ones included. -/
theorem Network.splitSides_eq (hd : N.Derives M) (hf : N.IsFullyDecomposedFor (incompatGraph M)) (heff : N.IsEfficientPerBlob) (hs : N.IsTreeNormalStructural)
    (hdeg : N.DegreeCond) (hT : IsTBar M T φ edge) :
    SempleSteel2003.splitSides N.blobbedTree (N.rowClass hd) = SempleSteel2003.splitSides T φ := by
  have hn := hs.line342Claim hf.nodeDisjoint heff
  have hlab := N.rowClass_labelled hd hdeg
  have htree := N.blobbedTree_isTree.1
  have hrow : ∀ r : M, ∃ l, N.IsLeaf l ∧ N.label l = r.1 := fun r => hd.surjOn r.2
  ext A
  constructor
  · rintro ⟨e', he', x, rfl⟩
    induction e' using Sym2.ind with
    | _ a b =>
      obtain ⟨e, he, heq⟩ := Network.exists_isTreeArc_of_adj he'
      have heq' : N.blobEdge e = s(a, b) := heq
      rw [← heq', he.edgeSide_eq hd x]
      -- a row below the arc, and one not below
      obtain ⟨⟨y₁, hy₁⟩, ⟨y₀, hy₀⟩⟩ := he.exists_rows hd hlab
      have hmem : {y : M | y.1 ∈ N.arcSide e} ∈ SempleSteel2003.splitSides T φ :=
        hT.mem_splitSides_of_charSplits hy₁ hy₀ fun hge₁ hge₂ =>
          (theorem4_splits N hd hf heff hs (N.arcSide_subset hd e) hge₁ hge₂).1 ⟨e, he, Or.inl rfl⟩
      by_cases hx : x.1 ∈ N.arcSide e
      · simpa [hx] using hmem
      · have : {y : M | y.1 ∈ N.arcSide e}ᶜ ∈ SempleSteel2003.splitSides T φ :=
          compl_mem_splitSides hT.isTree hmem ⟨x, hx⟩
        simpa [hx] using this
  · rintro ⟨e', he', x, rfl⟩
    induction e' using Sym2.ind with
    | _ a b =>
      have hab : T.Adj a b := he'
      -- a label at one end
      have hpendant : ∀ {a b : W} (r : M), T.Adj (φ r) b → a = φ r → x ∉ ({r} : Set M) ∨ x = r →
          SempleSteel2003.edgeSide T φ s(φ r, b) x ∈ SempleSteel2003.splitSides N.blobbedTree (N.rowClass hd) := by
        intro _ b r hrb _ _
        have hdegr := (hT.mem_range_iff (φ r)).1 ⟨r, rfl⟩
        obtain ⟨l, hl, hlr⟩ := hrow r
        have hrroot : l ≠ N.root := by
          intro hroot
          obtain ⟨y, h₁, -⟩ := exists_label_sameSide hT.isTree hT.labelled s(φ r, b) s(φ r, b) b
          obtain ⟨l', hl', hlr'⟩ := hrow y
          have hne : y ≠ r := by
            rintro rfl
            exact SempleSteel2003.not_reachable_deleteEdges hT.isTree.isAcyclic hrb (SameSide.symm h₁)
          have hlroot : l' = l := by
            have := N.reach_root l'
            rw [← hroot] at this
            rcases Relation.ReflTransGen.cases_head this with h | ⟨_, ⟨f, hf, -⟩, -⟩
            · exact h.symm
            · exact absurd hf (hl f)
          exact hne (Subtype.ext (by rw [← hlr', ← hlr, hlroot]))
        obtain ⟨g, hg, hside⟩ := N.exists_pendant hn.recomb_not_leaf hl hrroot
        have hsingle : ∀ y : M, y.1 ∈ N.arcSide g ↔ y = r := by
          intro y
          rw [hside, Set.mem_singleton_iff, hlr, Subtype.ext_iff]
        by_cases hxr : x = r
        · subst hxr
          refine hg.mem_splitSides hd (Or.inl ⟨x, (hsingle x).2 rfl, ?_⟩)
          ext y
          simp only [SempleSteel2003.edgeSide, Set.mem_ofPred_eq, hsingle]
          constructor
          · intro h
            exact hT.label_injective (eq_of_sameSide_of_ncard_le_one hdegr hrb h)
          · rintro rfl
            exact SimpleGraph.Reachable.refl _
        · refine hg.mem_splitSides hd (Or.inr ⟨x, fun h => hxr ((hsingle x).1 h), ?_⟩)
          ext y
          simp only [SempleSteel2003.edgeSide, Set.mem_ofPred_eq, Set.mem_compl_iff, hsingle]
          constructor
          · rintro h rfl
            have := eq_of_sameSide_of_ncard_le_one hdegr hrb (SameSide.symm h)
            exact hxr (hT.label_injective this)
          · intro hy
            have hne₁ : ¬ SameSide T s(φ r, b) (φ x) (φ r) := fun h =>
              hxr (hT.label_injective (eq_of_sameSide_of_ncard_le_one hdegr hrb (SameSide.symm h)))
            have hne₂ : ¬ SameSide T s(φ r, b) (φ y) (φ r) := fun h =>
              hy (hT.label_injective (eq_of_sameSide_of_ncard_le_one hdegr hrb (SameSide.symm h)))
            exact sameSide_of_not_sameSide hT.isTree.connected hne₁ hne₂
      by_cases ha : a ∈ Set.range φ
      · obtain ⟨r, rfl⟩ := ha
        exact hpendant r hab rfl (by tauto)
      · by_cases hb : b ∈ Set.range φ
        · obtain ⟨r, rfl⟩ := hb
          rw [Sym2.eq_swap]
          exact hpendant r hab.symm rfl (by tauto)
        · obtain ⟨k, hk⟩ := hT.internal_labelled a b hab ha hb
          rw [← hk]
          obtain ⟨e, he, hes⟩ := N.charSide_mem_treeSplits hd hf hn k
          have hedge : ∀ y : M, y ∈ SempleSteel2003.edgeSide T φ (edge k) x ↔ (charValue k x.1 = charValue k y.1) := by
            intro y
            exact (hT.split k x y).symm
          have hmemc : ∀ y : M, y.1 ∈ charSide k ↔ charValue k y.1 = true := fun y => by
            simp [charSide, y.2]
          refine he.mem_splitSides hd ?_
          rcases hes with hes | hes
          · by_cases hxk : charValue k x.1 = true
            · refine Or.inl ⟨x, ?_, ?_⟩
              · rw [← hes]
                exact (hmemc x).2 hxk
              · ext y
                rw [hedge y, hxk, Set.mem_ofPred_eq, ← hes, hmemc y]
                exact eq_comm
            · refine Or.inr ⟨x, ?_, ?_⟩
              · rw [← hes]
                exact fun h => hxk ((hmemc x).1 h)
              · ext y
                rw [hedge y, Set.mem_compl_iff, Set.mem_ofPred_eq, ← hes, hmemc y]
                cases hx' : charValue k x.1 <;> cases hy' : charValue k y.1 <;> simp_all
          · have hmemc' : ∀ y : M, y.1 ∈ N.arcSide e ↔ charValue k y.1 = false := by
              intro y
              have h₁ : y.1 ∉ charSide k ↔ y.1 ∈ N.arcSide e := by
                rw [hes]
                simp
              rw [← h₁, hmemc y]
              simp
            by_cases hxk : charValue k x.1 = true
            · refine Or.inr ⟨x, ?_, ?_⟩
              · rw [hmemc' x, hxk]
                simp
              · ext y
                rw [hedge y, Set.mem_compl_iff, Set.mem_ofPred_eq, hmemc' y, hxk]
                cases hy' : charValue k y.1 <;> simp
            · refine Or.inl ⟨x, ?_, ?_⟩
              · rw [hmemc' x]
                simpa using hxk
              · ext y
                have hxf : charValue k x.1 = false := by simpa using hxk
                rw [hedge y, Set.mem_ofPred_eq, hmemc' y, hxf]
                exact eq_comm

/-- **Theorem 4, under `IsTreeNormalStructural`**, and the degree condition. The proof is the paper's: the splits agree, and the Splits Equivalence Theorem applies. -/
theorem Network.exists_iso_of_isTreeNormalStructural (hd : N.Derives M) (hf : N.IsFullyDecomposedFor (incompatGraph M)) (he : N.IsEfficientPerBlob) (hn : N.IsTreeNormalStructural)
    (hdeg : N.DegreeCond) (hT : IsTBar M T φ edge) :
    ∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩ := by
  have : Nonempty M := by
    obtain ⟨l, hl, -⟩ := Network.exists_isLeaf_reach (N := N) N.root
    exact ⟨⟨_, hd.mapsTo hl⟩⟩
  have hx₁ : SempleSteel2003.IsXTree N.blobbedTree (N.rowClass hd) := ⟨N.blobbedTree_isTree.1, N.rowClass_labelled hd hdeg⟩
  have hx₂ : SempleSteel2003.IsXTree T φ := ⟨hT.isTree, hT.labelled⟩
  obtain ⟨f, hf'⟩ := SempleSteel2003.xTree_unique hx₁ hx₂ (N.splitSides_eq hd hf he hn hdeg hT)
  refine ⟨f, fun v r hr hv hvr => ?_⟩
  rw [← hf' ⟨r, hr⟩, N.rowClass_eq hd hv hvr]

/-- **The closest true form of Theorem 4** (`g:thm4`). Under `IsTreeNormalStructural`, and if every node of `T′` of degree at most two is a
leaf of `N` (no root of degree two off a blob, and no node of in-degree and out-degree one), then `T′` is `T̄`. The proof is
`theorem4_splits` and the Splits Equivalence Theorem (line 344). Departure from the paper: the hypotheses are added, because
the statement is false without them; by `theorem4_iff`, they're also necessary. The standing assumption isn't used, but it's what provides `T̄`.

What each hypothesis does:
- No recombination leaf, and the degree condition, are conventions of the paper rather than errors: read `T′` with a root of degree two suppressed (line 418), and give a recombination node a pendant arc (Figure 1's caption, line 341).
- `arc_labelled` is a case line 97 allows and the statement must exclude, so that the theorem fails as printed on it. The proof at lines 341 to 344 considers only the edges leaving a blob, so it never meets such an arc. `theorem4_false_siteFree` is a perfect phylogeny, efficient and fully decomposed, for which it fails.
- `noAncestralExit` is the error of line 342: it's the printed definition of "efficient" at lines 326 to 328 that omits the entry node of a blob. With the entry node, Theorem 4 holds: `theorem4_entry`. Then it needs only the other hypotheses.

`Gusfield2007.Realizability` shows that the hypotheses aren't vacuous: there's such a network for every `M` with at least three rows. -/
theorem theorem4 (c : Crossover) (M : Finset (ι → Bool)) :
    Theorem4Form c M fun {a b} (N : Network ι (Fin a) (Fin b)) =>
      N.IsTreeNormalStructural ∧ N.DegreeCond := by
  intro a b N _ hd hf he hP n T φ edge hT
  exact N.exists_iso_of_isTreeNormalStructural hd hf he.perBlob hP.1 hP.2 hT

omit [LinearOrder ι] [Finite W] in
/-- The edges of the star of a character at its centre are distinct: on the far side of an edge, there's only one super-character of the component. -/
theorem IsTBar.edge_injective_of_center (hT : IsTBar M T φ edge) {c : (incompatGraph M).ConnectedComponent} {v : W}
    (hv' : ∀ k : SuperChar M, k.1 = c → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v) {k₁ k₂ : SuperChar M} (h₁ : k₁.1 = c)
    (h₂ : k₂.1 = c) (h : edge k₁ = edge k₂) : k₁ = k₂ := by
  obtain ⟨c₁, S₁, hS₁⟩ := k₁
  obtain ⟨c₂, S₂, hS₂⟩ := k₂
  obtain rfl : c₁ = c := h₁
  obtain rfl : c₂ = c₁ := h₂
  obtain ⟨r₁, hr₁, hr₁S⟩ := mem_restrictRows.1 hS₁
  obtain ⟨r₂, hr₂, hr₂S⟩ := mem_restrictRows.1 hS₂
  have ht₁ : charValue (⟨c₂, ⟨S₁, hS₁⟩⟩ : SuperChar M) r₁ = true := by simp [charValue, hr₁S]
  have ht₂ : charValue (⟨c₂, ⟨S₂, hS₂⟩⟩ : SuperChar M) r₂ = true := by simp [charValue, hr₂S]
  have h₃ := hv' ⟨c₂, ⟨S₁, hS₁⟩⟩ rfl ⟨r₁, hr₁⟩ ht₁
  have h₄ := hv' ⟨c₂, ⟨S₂, hS₂⟩⟩ rfl ⟨r₂, hr₂⟩ ht₂
  rw [← h] at h₄
  have h₅ := sameSide_of_not_sameSide hT.isTree.connected h₃ h₄
  have h₆ := (hT.split ⟨c₂, ⟨S₁, hS₁⟩⟩ ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩).2 h₅
  simp only [ht₁] at h₆
  have h₇ : c₂.supp.domRestrict r₂ = S₁ := by simpa [charValue] using h₆.symm
  have h₈ : S₁ = S₂ := h₇.symm.trans hr₂S
  subst h₈
  rfl

omit [LinearOrder ι] in
/-- The centre of a non-trivial component has at least two neighbours. -/
theorem IsTBar.two_le_ncard_center (hT : IsTBar M T φ edge) {c : (incompatGraph M).ConnectedComponent} (hnt : c.supp.Nontrivial) {v : W}
    (hv : ∀ k : SuperChar M, k.1 = c → v ∈ edge k)
    (hv' : ∀ k : SuperChar M, k.1 = c → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v) : 2 ≤ (T.neighborSet v).ncard := by
  have h4 := four_le_card_restrictRows hnt
  obtain ⟨S₁, hS₁, S₂, hS₂, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (restrictRows c.supp M).card)
  obtain ⟨y₁, hy₁⟩ := hv ⟨c, ⟨S₁, hS₁⟩⟩ rfl
  obtain ⟨y₂, hy₂⟩ := hv ⟨c, ⟨S₂, hS₂⟩⟩ rfl
  have ha₁ : T.Adj v y₁ := by
    have := hT.edge_mem ⟨c, ⟨S₁, hS₁⟩⟩
    rwa [hy₁] at this
  have ha₂ : T.Adj v y₂ := by
    have := hT.edge_mem ⟨c, ⟨S₂, hS₂⟩⟩
    rwa [hy₂] at this
  have hyy : y₁ ≠ y₂ := by
    rintro rfl
    have := hT.edge_injective_of_center hv' (k₁ := ⟨c, ⟨S₁, hS₁⟩⟩) (k₂ := ⟨c, ⟨S₂, hS₂⟩⟩) rfl rfl (hy₁.trans hy₂.symm)
    have h' : S₁ = S₂ := by simpa using this
    exact hne h'
  exact (Set.one_lt_ncard_iff (Set.toFinite _)).2 ⟨y₁, y₂, ha₁, ha₂, hyy⟩

omit [LinearOrder ι] in
/-- **The centre of a component in `T̄` is its blob in `T′`**, if `T′` is `T̄`. Otherwise, an edge at the centre, towards the blob, has on its other side at least two super-characters of the component; but on the
side of a tree arc away from a blob, the sequence of the blob's sites is constant. This uses `four_le_card_restrictRows` and `adj_center_labelled`, that is, Lemma 4 and line 277. -/
theorem Network.center_eq (hT : IsTBar M T φ edge) (hd : N.Derives M) (f : N.blobbedTree ≃g T)
    (hfr : ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) {B : Set E} (hB : N.IsBlob B)
    {c : (incompatGraph M).ConnectedComponent} (hnt : c.supp.Nontrivial) (hiff : ∀ i, N.site i ∈ B ↔ i ∈ c.supp) {t : V} (ht : t ∈ N.blobVerts B) {v : W}
    (hv : ∀ k : SuperChar M, k.1 = c → v ∈ edge k)
    (hv' : ∀ k : SuperChar M, k.1 = c → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v) : f (N.toBlobNode t) = v := by
  have hiso : ∀ (e : Sym2 N.BlobNode) (a b : N.BlobNode), SameSide T (e.map f) (f a) (f b) ↔ SameSide N.blobbedTree e a b := SempleSteel2003.reachable_deleteEdges_iso f
  by_contra hne
  have hfb : f (f.symm v) = v := f.apply_symm_apply v
  have hne' : f.symm v ≠ N.toBlobNode t := fun h => hne (by rw [← h, hfb])
  obtain ⟨u, hu, hus⟩ := SempleSteel2003.exists_adj_reachable_deleteEdges N.blobbedTree_isTree.1.connected hne'
  have hu' : T.Adj v (f u) := by
    have := f.map_adj_iff.2 hu
    rwa [hfb] at this
  obtain ⟨k, hk₁, hk₂⟩ := adj_center_labelled hT hnt hv hv' hu'
  obtain ⟨e, he, heq⟩ := Network.exists_isTreeArc_of_adj hu
  have hE : N.blobEdge e = s(f.symm v, u) := heq
  have hmap : (s(f.symm v, u)).map f = edge k := by
    rw [hk₂, Sym2.map_mk, hfb]
  obtain ⟨c', S, hS⟩ := k
  obtain rfl : c' = c := hk₁
  have h4 := four_le_card_restrictRows hnt
  have h3 : 1 < ((restrictRows c'.supp M).erase S).card := by
    rw [Finset.card_erase_of_mem hS]
    omega
  obtain ⟨S₁, hS₁, S₂, hS₂, hne₁₂⟩ := Finset.one_lt_card.1 h3
  obtain ⟨hS₁n, hS₁m⟩ := Finset.mem_erase.1 hS₁
  obtain ⟨hS₂n, hS₂m⟩ := Finset.mem_erase.1 hS₂
  obtain ⟨r₁, hr₁, hr₁S⟩ := mem_restrictRows.1 hS₁m
  obtain ⟨r₂, hr₂, hr₂S⟩ := mem_restrictRows.1 hS₂m
  obtain ⟨r₀, hr₀, hr₀S⟩ := mem_restrictRows.1 hS
  obtain ⟨l₁, hl₁, rfl⟩ := hd.surjOn hr₁
  obtain ⟨l₂, hl₂, rfl⟩ := hd.surjOn hr₂
  have ht₀ : charValue (⟨c', ⟨S, hS⟩⟩ : SuperChar M) r₀ = true := by simp [charValue, hr₀S]
  have hside : ∀ (l : V) (hl : N.IsLeaf l), c'.supp.domRestrict (N.label l) ≠ S →
      SameSide N.blobbedTree (N.blobEdge e) (N.toBlobNode l) (f.symm v) := by
    intro l hl hlS
    have hfalse : charValue (⟨c', ⟨S, hS⟩⟩ : SuperChar M) (N.label l) = false := by simp [charValue, hlS]
    have hn₁ : ¬ SameSide T (edge ⟨c', ⟨S, hS⟩⟩) (φ ⟨N.label l, hd.mapsTo hl⟩) (φ ⟨r₀, hr₀⟩) := fun h => by
      have := (hT.split ⟨c', ⟨S, hS⟩⟩ _ _).2 h
      simp only [hfalse, ht₀] at this
      exact absurd this (by simp)
    have hn₂ : ¬ SameSide T (edge ⟨c', ⟨S, hS⟩⟩) v (φ ⟨r₀, hr₀⟩) := fun h => hv' _ rfl ⟨r₀, hr₀⟩ ht₀ h.symm
    have h₃ := sameSide_of_not_sameSide hT.isTree.connected hn₁ hn₂
    rw [hE, ← hiso, hmap, hfr l _ (hd.mapsTo hl) hl rfl, hfb]
    exact h₃
  have hs₁ := hside l₁ hl₁ (fun h => hS₁n (hr₁S.symm.trans h))
  have hs₂ := hside l₂ hl₂ (fun h => hS₂n (hr₂S.symm.trans h))
  have hadj := SempleSteel2003.not_reachable_deleteEdges N.blobbedTree_isTree.1.isAcyclic hu
  refine hne₁₂ ?_
  rw [← hr₁S, ← hr₂S]
  funext j
  refine he.label_eq_of_sameSide hB ht ((hiff j.1).2 j.2) (hs₁.trans hs₂.symm) fun h => hadj ?_
  rw [hE] at h hs₁
  exact hs₁.symm.trans (h.trans hus.symm)

/-- **The converse of Theorem 4.** If `T′` is `T̄` then the structural conditions hold. -/
theorem Network.isTreeNormalStructural_of_iso (hT : IsTBar M T φ edge) (hd : N.Derives M) (hf : N.IsFullyDecomposedFor (incompatGraph M))
    (f : N.blobbedTree ≃g T) (hfr : ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) :
    N.IsTreeNormalStructural ∧ N.DegreeCond := by
  have hnd := hf.nodeDisjoint
  have hconn := N.blobbedTree_isTree.1
  have hiso : ∀ (e : Sym2 N.BlobNode) (a b : N.BlobNode), SameSide T (e.map f) (f a) (f b) ↔ SameSide N.blobbedTree e a b := SempleSteel2003.reachable_deleteEdges_iso f
  have hdeg : N.DegreeCond := by
    intro v hv
    have h₂ := SempleSteel2003.ncard_neighborSet_iso f v
    obtain ⟨r, hr⟩ := hT.labelled (f v) (by omega)
    obtain ⟨l, hl, hlr⟩ := hd.surjOn r.2
    refine ⟨l, hl, f.injective ?_⟩
    rw [hfr l r.1 r.2 hl hlr, ← hr]
  have hlab := N.rowClass_labelled hd hdeg
  have hcenter : ∀ {B : Set E}, N.IsBlob B → ∃ (c : (incompatGraph M).ConnectedComponent) (v : W), c.supp.Nontrivial ∧ (∀ i, N.site i ∈ B ↔ i ∈ c.supp) ∧
      (∀ k : SuperChar M, k.1 = c → v ∈ edge k) ∧
      (∀ k : SuperChar M, k.1 = c → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v) ∧
      ∀ t ∈ N.blobVerts B, f (N.toBlobNode t) = v := by
    intro B hB
    obtain ⟨c, hnt, hiff⟩ := hf.blob_component B hB
    obtain ⟨v, hv, hv', -⟩ := lemma4 hT c
    exact ⟨c, v, hnt, hiff, hv, hv' hnt, fun t ht => N.center_eq hT hd f hfr hB hnt hiff ht hv (hv' hnt)⟩
  refine ⟨⟨⟨?recomb, ?arc⟩, ?exit⟩, hdeg⟩
  case recomb =>
    rintro x ⟨e₁, f₁, hne, rfl, hf₁⟩ hl
    obtain ⟨B, hB, he₁B, -⟩ := Network.exists_isBlob_of_tgt_eq hne hf₁.symm
    obtain ⟨c, v, hnt, -, hv, hv', hall⟩ := hcenter hB
    have h₁ := hall _ (Network.tgt_mem_blobVerts he₁B)
    rw [hfr _ _ (hd.mapsTo hl) hl rfl] at h₁
    have h₂ := (hT.mem_range_iff v).1 ⟨_, h₁⟩
    have h₃ := hT.two_le_ncard_center hnt hv hv'
    omega
  case exit =>
    rintro B e w hB hw ⟨l₀, hl₀, hnot₀⟩ hs ht
    have hwr : w ≠ N.root := fun h => hnot₀ (h ▸ N.reach_root l₀)
    by_contra hcon
    push Not at hcon
    obtain ⟨c, v, -, hiff, -, hv', hall⟩ := hcenter hB
    have het := Network.isTreeArc_of_exit hnd hB hs ht
    obtain ⟨g, hg, rfl⟩ := (hw.eq_root_or_exists hnd hB).resolve_left hwr
    have hx₀' : SameSide N.blobbedTree (N.blobEdge g) (N.toBlobNode (N.src g)) (N.toBlobNode l₀) := (hg.sameSide_src_iff l₀).2 hnot₀
    obtain ⟨l₁, hl₁, hr₁⟩ := Network.exists_isLeaf_reach (N := N) (N.tgt e)
    have hc₀ : c.supp.domRestrict (N.label l₀) = c.supp.domRestrict (N.label (N.tgt g)) := by
      funext i
      exact hw.label_eq_of_not_reach hnd hB ((hiff i.1).2 i.2) hnot₀
    have hc₁ : c.supp.domRestrict (N.label l₁) = c.supp.domRestrict (N.label (N.tgt g)) := by
      funext i
      have hi := (hiff i.1).2 i.2
      exact (hB.label_eq_of_exit het hs hi hr₁).trans (hcon i.1 hi)
    have hS : c.supp.domRestrict (N.label (N.tgt g)) ∈ restrictRows c.supp M :=
      mem_restrictRows.2 ⟨_, hd.mapsTo hl₀, hc₀⟩
    set k : SuperChar M := ⟨c, ⟨_, hS⟩⟩ with hk
    have ht₀ : charValue k (N.label l₀) = true := decide_eq_true hc₀
    have ht₁ : charValue k (N.label l₁) = true := decide_eq_true hc₁
    have hss : SameSide T (edge k) (φ ⟨_, hd.mapsTo hl₀⟩) (φ ⟨_, hd.mapsTo hl₁⟩) :=
      (hT.split k _ _).1 (ht₀.trans ht₁.symm)
    have hfsymm : ((edge k).map f.symm).map f = edge k := by
      rw [Sym2.map_map]
      simp
    have hss' : SameSide N.blobbedTree ((edge k).map f.symm) (N.toBlobNode l₀) (N.toBlobNode l₁) := by
      rw [← hiso, hfsymm, hfr l₀ _ (hd.mapsTo hl₀) hl₀ rfl, hfr l₁ _ (hd.mapsTo hl₁) hl₁ rfl]
      exact hss
    have hcls : N.toBlobNode (N.src e) = N.toBlobNode (N.tgt g) := hB.toBlobNode_eq hs hw.1
    have ha₀ : N.blobbedTree.Adj (N.toBlobNode (N.tgt g)) (N.toBlobNode (N.src g)) := (Network.blobbedTree_adj hg).symm
    have ha₁ : N.blobbedTree.Adj (N.toBlobNode (N.tgt g)) (N.toBlobNode (N.tgt e)) := by
      rw [← hcls]
      exact Network.blobbedTree_adj het
    have hne : N.toBlobNode (N.src g) ≠ N.toBlobNode (N.tgt e) := by
      intro h
      have hee : N.blobEdge g = N.blobEdge e := by
        change s(_, _) = s(_, _)
        rw [h, hcls, Sym2.eq_swap]
      have := Network.blobEdge_injective hg het hee
      exact ht (this ▸ hw.1)
    have hl₀' : SameSide N.blobbedTree s(N.toBlobNode (N.tgt g), N.toBlobNode (N.src g)) (N.toBlobNode (N.src g)) (N.toBlobNode l₀) := by
      rw [Sym2.eq_swap]
      exact hx₀'
    have hl₁' : SameSide N.blobbedTree s(N.toBlobNode (N.tgt g), N.toBlobNode (N.tgt e)) (N.toBlobNode (N.tgt e)) (N.toBlobNode l₁) := by
      rw [← hcls]
      exact (het.sameSide_tgt_iff l₁).2 hr₁
    have hb := sameSide_left_of_sameSide hconn ha₀ ha₁ hne hl₀' hl₁' hss'
    have hb' := (hiso _ _ _).2 hb
    rw [hfsymm, hfr l₀ _ (hd.mapsTo hl₀) hl₀ rfl, hall _ hw.1] at hb'
    exact hv' k rfl ⟨_, hd.mapsTo hl₀⟩ ht₀ hb'.symm
  case arc =>
    intro e he hu hz hzl
    have hoff : ∀ {t}, ¬ N.OnBlob t → ¬ N.IsLeaf t → f (N.toBlobNode t) ∉ Set.range φ := by
      rintro t ht₁ ht₂ ⟨r, hr⟩
      obtain ⟨l, hl, hlr⟩ := hd.surjOn r.2
      have hcls : N.toBlobNode l = N.toBlobNode t := f.injective (by rw [hfr l r.1 r.2 hl hlr, hr])
      rcases Network.eq_or_exists_isBlob_of_toBlobNode_eq hnd hcls with rfl | ⟨B, hB, -, h⟩
      · exact ht₂ hl
      · exact ht₁ ⟨B, hB, h⟩
    have huleaf : ¬ N.IsLeaf (N.src e) := fun h => h e rfl
    have hadj := f.map_adj_iff.2 (Network.blobbedTree_adj he)
    obtain ⟨k, hk⟩ := hT.internal_labelled _ _ hadj (hoff hu huleaf) (hoff hz hzl)
    obtain ⟨c, S₀, hS₀⟩ := k
    by_cases hnt : c.supp.Nontrivial
    · exfalso
      obtain ⟨B, hB, hsub⟩ := converse N hd c hnt
      obtain ⟨c₀, -, hc₀⟩ := hf.blob_component B hB
      obtain ⟨i₀, hi₀⟩ := hnt.nonempty
      have hcc : c = c₀ := by
        rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hi₀,
          ← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 ((hc₀ i₀).1 (hsub i₀ hi₀))]
      subst hcc
      obtain ⟨v, hv, hv', -⟩ := lemma4 hT c
      have htB : N.src (N.site i₀) ∈ N.blobVerts B := Network.src_mem_blobVerts (hsub i₀ hi₀)
      have hcen := N.center_eq hT hd f hfr hB hnt hc₀ htB hv (hv' hnt)
      have hvm := hv ⟨c, ⟨S₀, hS₀⟩⟩ rfl
      rw [hk, Sym2.mem_iff] at hvm
      have honblob : ∀ {t}, f (N.toBlobNode t) = v → N.OnBlob t := by
        intro t ht
        have hcls : N.toBlobNode t = N.toBlobNode (N.src (N.site i₀)) := f.injective (ht.trans hcen.symm)
        rcases Network.eq_or_exists_isBlob_of_toBlobNode_eq hnd hcls with rfl | ⟨B', hB', h, -⟩
        · exact ⟨B, hB, htB⟩
        · exact ⟨B', hB', h⟩
      rcases hvm with h | h
      · exact hu (honblob h.symm)
      · exact hz (honblob h.symm)
    · obtain ⟨i, hi⟩ := c.nonempty_supp
      have hc : ∀ j, j ∈ c.supp ↔ j = i := by
        intro j
        constructor
        · intro hj
          by_contra hne
          exact hnt ⟨j, hj, i, hi, hne⟩
        · rintro rfl
          exact hi
      have hti : N.IsTreeArc (N.site i) := hf.isolated_treeArc i fun j hj => by
        have hjm : j ∈ c.supp := by
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hi ⊢
          rw [← hi]
          exact SimpleGraph.ConnectedComponent.eq.2 hj.reachable.symm
        exact hj.ne ((hc j).1 hjm).symm
      refine ⟨i, ?_⟩
      have hrow : ∀ r : ι → Bool, charValue (⟨c, ⟨S₀, hS₀⟩⟩ : SuperChar M) r = decide (r i = S₀ ⟨i, (hc i).2 rfl⟩) := by
        intro r
        simp only [charValue, decide_eq_decide]
        constructor
        · intro h
          exact congrFun h ⟨i, (hc i).2 rfl⟩
        · intro h
          funext j
          obtain ⟨j, hj⟩ := j
          obtain rfl := (hc j).1 hj
          exact h
      refine (Network.blobEdge_injective hti he ?_)
      refine edge_eq_of_sameSide_iff N.blobbedTree_isTree.1 hlab (Network.blobEdge_mem_edgeSet hti) fun x y => ?_
      rw [hti.sameSide_rowClass_iff hd x y, ← hiso (N.blobEdge e)]
      have hmapE : (N.blobEdge e).map f = edge ⟨c, ⟨S₀, hS₀⟩⟩ := by
        rw [hk]
        rfl
      rw [hmapE]
      have hfx : ∀ x : M, f (N.rowClass hd x) = φ x := by
        intro x
        obtain ⟨hl, hlr⟩ := hd.surjOn x.2 |>.choose_spec
        rw [N.rowClass_eq hd hl hlr, hfr _ x.1 x.2 hl hlr]
      rw [hfx, hfx, ← hT.split ⟨c, ⟨S₀, hS₀⟩⟩ x y, hrow, hrow]
      have hbelow : ∀ z : M, z.1 ∈ N.arcSide (N.site i) ↔ z.1 i = N.label (N.tgt (N.site i)) i := by
        intro z
        obtain ⟨hl, hlr⟩ := hd.surjOn z.2 |>.choose_spec
        rw [← hlr, N.mem_arcSide_iff hd hl]
        exact (hti.label_eq_iff_reach rfl).symm
      rw [hbelow, hbelow]
      cases x.1 i <;> cases y.1 i <;> cases N.label (N.tgt (N.site i)) i <;> cases S₀ ⟨i, (hc i).2 rfl⟩ <;> simp

omit [LinearOrder ι] in
/-- If the degree condition holds, there's a row off each blob with an entering arc. So then `NoAncestralExit` and `NoAncestralExitAtEntered` are the same. -/
theorem Network.exists_leaf_off_top (hd : N.Derives M) (hdeg : N.DegreeCond) (hnd : N.BlobsNodeDisjoint) {B : Set E} (hB : N.IsBlob B) {w : V} (hw : N.IsBlobTop B w) (hwr : w ≠ N.root) :
    ∃ l, N.IsLeaf l ∧ ¬ N.Reach w l := by
  obtain ⟨g, hg, rfl⟩ := (hw.eq_root_or_exists hnd hB).resolve_left hwr
  obtain ⟨x₀, hx₀, -⟩ := exists_label_sameSide N.blobbedTree_isTree.1 (N.rowClass_labelled hd hdeg) (N.blobEdge g) (N.blobEdge g) (N.toBlobNode (N.src g))
  obtain ⟨hl₀, -⟩ := hd.surjOn x₀.2 |>.choose_spec
  exact ⟨_, hl₀, (hg.sameSide_src_iff _).1 hx₀⟩

omit [LinearOrder ι] in
theorem Network.NoAncestralExit.atEntered (h : N.NoAncestralExit) (hd : N.Derives M) (hdeg : N.DegreeCond) (hnd : N.BlobsNodeDisjoint) : N.NoAncestralExitAtEntered :=
  fun B e w hB hw hwr hs ht => h B e w hB hw (N.exists_leaf_off_top hd hdeg hnd hB hw hwr) hs ht

omit [LinearOrder ι] in
/-- Whether a node of a blob is below its top doesn't depend on the node: a blob's nodes are in one class of `T′`. -/
theorem Network.IsBlobTop.reach_iff (hnd : N.BlobsNodeDisjoint) {B : Set E} (hB : N.IsBlob B) {w : V} (hw : N.IsBlobTop B w) {t t' : V} (h : N.toBlobNode t = N.toBlobNode t') :
    N.Reach w t ↔ N.Reach w t' := by
  rcases hw.eq_root_or_exists hnd hB with rfl | ⟨g, hg, rfl⟩
  · exact iff_of_true (N.reach_root t) (N.reach_root t')
  · exact hg.reach_iff_of_toBlobNode_eq h

/-- **If `T′` is `T̄`, the network is efficient.** Two exits of one blob with one label would be at one edge of the star of its centre. For two blobs, one of them isn't above the other, and then its exit carries its ancestral super-character. -/
theorem Network.isEfficient_of_iso (hT : IsTBar M T φ edge) (hd : N.Derives M) (hf : N.IsFullyDecomposedFor (incompatGraph M))
    (f : N.blobbedTree ≃g T) (hfr : ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) : N.IsEfficient := by
  have hnd := hf.nodeDisjoint
  have hiso : ∀ (e : Sym2 N.BlobNode) (a b : N.BlobNode), SameSide T (e.map f) (f a) (f b) ↔ SameSide N.blobbedTree e a b := SempleSteel2003.reachable_deleteEdges_iso f
  obtain ⟨hs, hdeg⟩ := N.isTreeNormalStructural_of_iso hT hd hf f hfr
  have hstrong := hs.noAncestralExit.atEntered hd hdeg hnd
  -- Two exits of a blob with one label are one arc.
  have hsame : ∀ {B : Set E} {e e' : E}, N.IsBlob B → N.src e ∈ N.blobVerts B → N.tgt e ∉ N.blobVerts B → N.src e' ∈ N.blobVerts B → N.tgt e' ∉ N.blobVerts B →
      N.label (N.src e) = N.label (N.src e') → e = e' := by
    intro B e e' hB hs₁ ht₁ hs₂ ht₂ hlab
    obtain ⟨c, hnt, hiff⟩ := hf.blob_component B hB
    obtain ⟨v, hv, hv', -⟩ := lemma4 hT c
    have hcen : ∀ {t}, t ∈ N.blobVerts B → f (N.toBlobNode t) = v := fun ht => N.center_eq hT hd f hfr hB hnt hiff ht hv (hv' hnt)
    have hexit : ∀ {g : E}, N.src g ∈ N.blobVerts B → N.tgt g ∉ N.blobVerts B → ∃ hS : c.supp.domRestrict (N.label (N.src g)) ∈ restrictRows c.supp M,
        edge ⟨c, ⟨_, hS⟩⟩ = (N.blobEdge g).map f := by
      intro g hs₀ ht₀
      have hg := Network.isTreeArc_of_exit hnd hB hs₀ ht₀
      have hadj : T.Adj v (f (N.toBlobNode (N.tgt g))) := by
        have := f.map_adj_iff.2 (Network.blobbedTree_adj hg)
        rwa [hcen hs₀] at this
      obtain ⟨k, hk₁, hk₂⟩ := adj_center_labelled hT hnt hv (hv' hnt) hadj
      have hmap : (N.blobEdge g).map f = s(v, f (N.toBlobNode (N.tgt g))) := by
        change s(f _, f _) = _
        rw [hcen hs₀]
      obtain ⟨l, hl, hrl⟩ := Network.exists_isLeaf_reach (N := N) (N.tgt g)
      obtain ⟨r', hr'⟩ := exists_charValue_eq_true k
      have hn₁ : ¬ SameSide T (edge k) (φ r') v := hv' hnt k hk₁ r' hr'
      have hn₂ : ¬ SameSide T (edge k) (φ ⟨_, hd.mapsTo hl⟩) v := by
        intro hss
        have h₁ := (hg.sameSide_tgt_iff l).2 hrl
        have h₂ := (hiso _ _ _).2 h₁
        rw [hmap, hfr l _ (hd.mapsTo hl) hl rfl] at h₂
        rw [hk₂] at hss
        have h₃ := h₂.trans hss
        exact SempleSteel2003.not_reachable_deleteEdges hT.isTree.isAcyclic hadj (SameSide.symm h₃)
      have hss := sameSide_of_not_sameSide hT.isTree.connected hn₁ hn₂
      have hval : charValue k (N.label l) = true := ((hT.split k r' ⟨_, hd.mapsTo hl⟩).2 hss).symm.trans hr'
      have hk₃ : k.1.supp.domRestrict (N.label l) = k.2.1 := by simpa [charValue] using hval
      obtain ⟨c', S₀, hS₀⟩ := k
      obtain rfl : c' = c := hk₁
      have hS₁ : S₀ = c'.supp.domRestrict (N.label (N.src g)) := by
        refine hk₃.symm.trans ?_
        funext i
        exact hB.label_eq_of_exit hg hs₀ ((hiff i.1).2 i.2) hrl
      subst hS₁
      exact ⟨hS₀, hk₂.trans hmap.symm⟩
    obtain ⟨hS₁, hk₁⟩ := hexit hs₁ ht₁
    obtain ⟨hS₂, hk₂⟩ := hexit hs₂ ht₂
    have hedge : ∀ {S₁ S₂ : c.supp → Bool} (h₁ : S₁ ∈ restrictRows c.supp M) (h₂ : S₂ ∈ restrictRows c.supp M), S₁ = S₂ → edge ⟨c, ⟨S₁, h₁⟩⟩ = edge ⟨c, ⟨S₂, h₂⟩⟩ := by
      rintro S₁ S₂ h₁ h₂ rfl
      rfl
    have hE : (N.blobEdge e).map f = (N.blobEdge e').map f := by
      rw [← hk₁, ← hk₂]
      exact hedge _ _ (congrArg _ hlab)
    exact Network.blobEdge_injective (Network.isTreeArc_of_exit hnd hB hs₁ ht₁) (Network.isTreeArc_of_exit hnd hB hs₂ ht₂) (Sym2.map.injective f.injective hE)
  -- Two blobs: one of them isn't above the other.
  have hnotbelow : ∀ {B B' : Set E} {u u' : V} {e' : E} {w' : V}, N.IsBlob B → N.IsBlob B' → u ∈ N.blobVerts B → N.IsBlobTop B' w' → N.src e' = u' → u' ∈ N.blobVerts B' →
      N.tgt e' ∉ N.blobVerts B' → N.label u = N.label u' → ¬ N.Reach w' u → False := by
    intro B B' u u' e' w' _ hB' _ hw' hes hu' ht' hlab hnr
    have hwr : w' ≠ N.root := fun h => hnr (h ▸ N.reach_root u)
    obtain ⟨i, hi, hne⟩ := hstrong B' e' w' hB' hw' hwr (hes ▸ hu') ht'
    refine hne ?_
    rw [hes, ← hlab]
    exact hw'.label_eq_of_not_reach hnd hB' hi hnr
  refine ⟨?_, fun B e e' hB hs₁ ht₁ hsf ht₂ => hsame hB hs₁ ht₁ (hsf ▸ hs₁) ht₂ (by rw [hsf])⟩
  rintro B B' v v' hB hB' ⟨hv, e, hes, het⟩ ⟨hv', e', hes', het'⟩ hlab
  by_cases hBB : B = B'
  · subst hBB
    have := hsame hB (hes ▸ hv) (het) (hes' ▸ hv') (het') (by rw [hes, hes', hlab])
    rw [← hes, ← hes', this]
  · exfalso
    obtain ⟨w, hw, -⟩ := Network.exists_isBlobTop_reach hv
    obtain ⟨w', hw', -⟩ := Network.exists_isBlobTop_reach hv'
    by_cases h₁ : N.Reach w' v
    · by_cases h₂ : N.Reach w v'
      · -- each top is above the other
        have h₃ : N.Reach w' w := (hw'.reach_iff hnd hB' (hB.toBlobNode_eq hv hw.1)).1 h₁
        have h₄ : N.Reach w w' := (hw.reach_iff hnd hB (hB'.toBlobNode_eq hv' hw'.1)).1 h₂
        have hww : w = w' := by
          rcases Relation.ReflTransGen.cases_head h₃ with h | ⟨b, hb, hbw⟩
          · exact h.symm
          · exact absurd h₄ (fun h₅ => N.acyclic _ (Relation.TransGen.trans_left (Relation.TransGen.head' hb hbw) h₅))
        exact Set.disjoint_left.1 (hnd B B' hB hB' hBB) hw.1 (hww ▸ hw'.1)
      · exact hnotbelow hB' hB hv' hw hes hv het hlab.symm h₂
    · exact hnotbelow hB hB' hv hw' hes' hv' het' hlab h₁

/-- **Theorem 4 exactly** (`g:thm4_iff`): given that `N` is fully decomposed, `T′` is `T̄` if and only if `N` is efficient, and `IsTreeNormalStructural` and the degree condition hold. So these conditions lose nothing, and `NoAncestralExit` is the whole content of the error at line 342.

"No exit at a node carrying the blob's ancestral super-character", with no exemption, is too strong: a blob at the root has to be exempt, for "only if": see `fourGametes_rootExit`. For this "if and only if", the form of the exemption doesn't matter, by `Network.NoAncestralExit.atEntered`. -/
theorem theorem4_iff {V E : Type*} [Finite V] [Finite E] {N : Network ι V E} {M : Finset (ι → Bool)} (hd : N.Derives M)
    (hf : N.IsFullyDecomposedFor (incompatGraph M)) {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W}
    {edge : SuperChar M → Sym2 W} (hT : IsTBar M T φ edge) :
    (∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) ↔
      N.IsEfficient ∧ N.IsTreeNormalStructural ∧ N.DegreeCond := by
  constructor
  · rintro ⟨f, hfr⟩
    exact ⟨N.isEfficient_of_iso hT hd hf f hfr, N.isTreeNormalStructural_of_iso hT hd hf f hfr⟩
  · rintro ⟨he, hn, hdeg⟩
    exact N.exists_iso_of_isTreeNormalStructural hd hf he.perBlob hn hdeg hT

/-! ### Theorem 4 with the entry node -/

/-- The arc `e` joins the node `v` of the blob `B` to a node off `B`, in either direction. -/
def Network.CrossesAt (N : Network ι V E) (B : Set E) (e : E) (v : V) : Prop :=
  v ∈ N.blobVerts B ∧ ((N.src e = v ∧ N.tgt e ∉ N.blobVerts B) ∨ (N.tgt e = v ∧ N.src e ∉ N.blobVerts B))

/-- **Efficient, counting the entry node of a blob** (`g:efficient_entry`). The idea isn't ours: Gusfield, *ReCombinatorics* (MIT Press, 2014), Section 7.3.5, counts an external node "without regard to edge direction". A canonical network of the book is efficient in this sense, and not conversely. This is lines 326 to 328 with "external" read as "has an edge to or from a node outside of `b`", and with labels compared on one blob at a time: no two such nodes of a blob have one label, and each of them has exactly
one edge to or from a node off the blob. So the entering edge counts as one of the edges of its node. With this definition, Theorem 4 holds (`theorem4_entry`) up to its conventions and site-free arcs, and lines 341 and 342 are true (`Network.IsEfficientAtEntry.existsUnique_port`,
`Network.IsEfficientAtEntry.line342Claim`). A blob at the root has no entering edge, so there's no exemption to make. The module docstring says what it means for the printed definition.

The labels have to be compared on one blob at a time. Over all the blobs, `fig2Net` would fail: its node `00100` leaves the first blob, and the second blob is entered at a node with that label, on a site-free arc. And the entering arc has to count among the arcs of its node, and not only among the nodes: in `topNet`, one node has both the entering arc and an exit, so that no two nodes have one label, and only `edge_unique` catches it. -/
structure Network.IsEfficientAtEntry (N : Network ι V E) : Prop where
  label_inj : ∀ B v v', N.IsBlob B → (∃ e, N.CrossesAt B e v) → (∃ e, N.CrossesAt B e v') → N.label v = N.label v' → v = v'
  edge_unique : ∀ B e f v, N.IsBlob B → N.CrossesAt B e v → N.CrossesAt B f v → e = f

omit [LinearOrder ι] [Finite V] [Finite E] in
/-- Efficient at the entry nodes implies efficient on each blob. -/
theorem Network.IsEfficientAtEntry.perBlob (he : N.IsEfficientAtEntry) : N.IsEfficientPerBlob where
  label_inj := by
    rintro B v v' hB ⟨hv, e, hes, het⟩ ⟨hv', e', hes', het'⟩ hl
    exact he.label_inj B v v' hB ⟨e, hv, Or.inl ⟨hes, het⟩⟩ ⟨e', hv', Or.inl ⟨hes', het'⟩⟩ hl
  exit_unique B e f hB hs ht hsf htf :=
    he.edge_unique B e f (N.src e) hB ⟨hs, Or.inl ⟨rfl, ht⟩⟩ ⟨hs, Or.inl ⟨hsf, htf⟩⟩

omit [LinearOrder ι] [Finite E] in
/-- A node of a blob with the same label on the sites of the blob as another has the same label. -/
theorem Network.IsBlob.label_eq_of_forall {B : Set E} (hB : N.IsBlob B) {u v : V} (hu : u ∈ N.blobVerts B) (hv : v ∈ N.blobVerts B) (h : ∀ i, N.site i ∈ B → N.label u i = N.label v i) :
    N.label u = N.label v := by
  funext i
  by_cases hi : N.site i ∈ B
  · exact h i hi
  · exact hB.label_eq_of_notMem hi hu hv

omit [LinearOrder ι] in
/-- An arc entering a blob enters at its top, which isn't the root. -/
theorem Network.CrossesAt.eq_top (hnd : N.BlobsNodeDisjoint) {B : Set E} (hB : N.IsBlob B) {e : E} {v w : V} (ht : N.tgt e = v) (hv : v ∈ N.blobVerts B) (hs : N.src e ∉ N.blobVerts B)
    (hw : N.IsBlobTop B w) : v = w ∧ w ≠ N.root ∧ N.IsTreeArc e := by
  have htr := Network.isTreeArc_of_notMem hnd hB (Or.inr (ht ▸ hv)) fun he => hs (Network.src_mem_blobVerts he)
  have hvw := htr.tgt_eq_of_isBlobTop hnd hB (ht ▸ hv) hw
  refine ⟨ht.symm.trans hvw, fun hr => (N.root_iff N.root).2 rfl e ?_, htr⟩
  rw [hvw, hr]

omit [LinearOrder ι] in
/-- **`IsEfficientAtEntry` is efficiency on each blob and no exit at the top of a blob with an entering arc.** This is the relation to the printed definition and to `NoAncestralExit`. -/
theorem Network.isEfficientAtEntry_iff (hnd : N.BlobsNodeDisjoint) : N.IsEfficientAtEntry ↔ N.IsEfficientPerBlob ∧ N.NoAncestralExitAtEntered := by
  constructor
  · intro he
    refine ⟨he.perBlob, ?_⟩
    intro B e w hB hw hwr hs ht
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg, hgw⟩ := (hw.eq_root_or_exists hnd hB).resolve_left hwr
    have hg₁ : N.CrossesAt B g w := ⟨hw.1, Or.inr ⟨hgw, hg.src_notMem_blobVerts hB (hgw ▸ hw.1)⟩⟩
    have he₁ : N.CrossesAt B e (N.src e) := ⟨hs, Or.inl ⟨rfl, ht⟩⟩
    have hlab := hB.label_eq_of_forall hs hw.1 hcon
    have huw := he.label_inj B _ _ hB ⟨e, he₁⟩ ⟨g, hg₁⟩ hlab
    have heg := he.edge_unique B e g w hB (huw ▸ he₁) hg₁
    exact ht (heg ▸ hgw ▸ hw.1)
  · rintro ⟨hp, hs⟩
    have hcases : ∀ {B : Set E} {e : E} {v w : V}, N.IsBlob B → N.IsBlobTop B w → N.CrossesAt B e v → (N.IsExternal B v ∧ N.src e = v ∧ N.tgt e ∉ N.blobVerts B) ∨ (v = w ∧ w ≠ N.root ∧ N.tgt e = v ∧ N.IsTreeArc e) := by
      rintro B e v w hB hw ⟨hv, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
      · exact Or.inl ⟨⟨hv, e, h₁, h₂⟩, h₁, h₂⟩
      · obtain ⟨h₃, h₄, h₅⟩ := Network.CrossesAt.eq_top hnd hB h₁ hv h₂ hw
        exact Or.inr ⟨h₃, h₄, h₁, h₅⟩
    have hnotop : ∀ {B : Set E} {u w : V}, N.IsBlob B → N.IsBlobTop B w → w ≠ N.root → N.IsExternal B u → N.label u ≠ N.label w := by
      rintro B u w hB hw hwr ⟨hu, e, rfl, ht⟩ hl
      obtain ⟨i, -, hne⟩ := hs B e w hB hw hwr hu ht
      exact hne (congrFun hl i)
    refine ⟨?_, ?_⟩
    · rintro B v v' hB ⟨e, he⟩ ⟨e', he'⟩ hl
      obtain ⟨w, hw, -⟩ := Network.exists_isBlobTop_reach he.1
      rcases hcases hB hw he with ⟨h₁, -⟩ | ⟨rfl, h₂, -⟩ <;> rcases hcases hB hw he' with ⟨h₃, -⟩ | ⟨h₄, h₅, -⟩
      · exact hp.label_inj B v v' hB h₁ h₃ hl
      · subst h₄
        exact absurd hl (hnotop hB hw h₅ h₁)
      · exact absurd hl.symm (hnotop hB hw h₂ h₃)
      · exact h₄.symm
    · rintro B e f v hB he hf
      obtain ⟨w, hw, -⟩ := Network.exists_isBlobTop_reach he.1
      rcases hcases hB hw he with ⟨h₁, h₂, h₃⟩ | ⟨rfl, h₂, h₃, h₄⟩ <;> rcases hcases hB hw hf with ⟨h₅, h₆, h₇⟩ | ⟨h₅, h₆, h₇, h₈⟩
      · exact hp.exit_unique B e f hB (h₂ ▸ he.1) h₃ (h₆.trans h₂.symm) h₇
      · subst h₅
        exact absurd rfl (hnotop hB hw h₆ h₁)
      · exact absurd rfl (hnotop hB hw h₂ h₅)
      · exact (h₄.eq_of_tgt_eq (h₇.trans h₃.symm)).symm

omit [LinearOrder ι] in
/-- **Line 342 is true**, for `IsEfficientAtEntry`, with no recombination leaf: "in the other subnetwork, no leaf label contains `S_v(C)`". -/
theorem Network.IsEfficientAtEntry.line342Claim (he : N.IsEfficientAtEntry) (hnd : N.BlobsNodeDisjoint) (hr : N.RegularArcs) : N.Line342Claim :=
  (⟨hr, ((Network.isEfficientAtEntry_iff hnd).1 he).2.noAncestralExit⟩ : N.IsTreeNormalStructural).line342Claim hnd he.perBlob

omit [LinearOrder ι] in
/-- **Line 341 is true**, for `IsEfficientAtEntry`, with no recombination leaf: "each super-character derived from `C` labels exactly one external node of `b_C`", where an external node can be entered from outside. -/
theorem Network.IsEfficientAtEntry.existsUnique_port (he : N.IsEfficientAtEntry) (hd : N.Derives M) (hnd : N.BlobsNodeDisjoint) (hr : ∀ x, N.IsRecomb x → ¬ N.IsLeaf x) {B : Set E} (hB : N.IsBlob B)
    {c : (incompatGraph M).ConnectedComponent} (hiff : ∀ i, N.site i ∈ B ↔ i ∈ c.supp) {S₀ : c.supp → Bool} (hS₀ : S₀ ∈ restrictRows c.supp M) :
    ∃! v, (∃ e, N.CrossesAt B e v) ∧ c.supp.domRestrict (N.label v) = S₀ := by
  obtain ⟨r₀, hr₀, hrS⟩ := mem_restrictRows.1 hS₀
  obtain ⟨l₀, hl₀, rfl⟩ := hd.surjOn hr₀
  have hex : ∃ v, (∃ e, N.CrossesAt B e v) ∧ c.supp.domRestrict (N.label v) = S₀ := by
    have hne : (N.blobVerts B).Nonempty := by
      obtain ⟨Q, hQ, rfl⟩ := id hB
      obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
      obtain ⟨e, f, hef, he₁, hf₁⟩ := hc.1
      obtain ⟨B', hB', he', -⟩ := Network.exists_isBlob_of_tgt_eq hef (he₁.trans hf₁.symm)
      by_cases hp : p = []
      · have hq : q ≠ [] := fun h => hc.2.2.2.1 (by rw [hp, h])
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil q hq
        exact ⟨_, Network.src_mem_blobVerts (e := a) ⟨_, Relation.ReflTransGen.refl, Or.inr ha⟩⟩
      · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil p hp
        exact ⟨_, Network.src_mem_blobVerts (e := a) ⟨_, Relation.ReflTransGen.refl, Or.inl ha⟩⟩
    obtain ⟨z, hz⟩ := hne
    obtain ⟨w, hw, -⟩ := Network.exists_isBlobTop_reach hz
    by_cases hreach : N.Reach w l₀
    · rcases hw.position hnd hB hreach with h | ⟨e, he₁, he₂, he₃, he₄⟩
      · exact absurd hl₀ (hr l₀ (hB.isRecomb_of_isLeaf h hl₀))
      · refine ⟨N.src e, ⟨e, he₂, Or.inl ⟨rfl, he₃⟩⟩, Eq.trans ?_ hrS⟩
        funext i
        exact (hB.label_eq_of_exit he₁ he₂ ((hiff i.1).2 i.2) he₄).symm
    · have hwr : w ≠ N.root := fun h => hreach (h ▸ N.reach_root l₀)
      obtain ⟨g, hg, hgw⟩ := (hw.eq_root_or_exists hnd hB).resolve_left hwr
      refine ⟨w, ⟨g, hw.1, Or.inr ⟨hgw, hg.src_notMem_blobVerts hB (hgw ▸ hw.1)⟩⟩, Eq.trans ?_ hrS⟩
      funext i
      exact (hw.label_eq_of_not_reach hnd hB ((hiff i.1).2 i.2) hreach).symm
  obtain ⟨v, hv₁, hv₂⟩ := hex
  refine ⟨v, ⟨hv₁, hv₂⟩, ?_⟩
  rintro v' ⟨hv₁', hv₂'⟩
  obtain ⟨e, he₁⟩ := hv₁
  obtain ⟨e', he₁'⟩ := hv₁'
  refine he.label_inj B _ _ hB ⟨e', he₁'⟩ ⟨e, he₁⟩ (hB.label_eq_of_forall he₁'.1 he₁.1 fun i hi => ?_)
  exact (congrFun hv₂' ⟨i, (hiff i).1 hi⟩).trans (congrFun hv₂ ⟨i, (hiff i).1 hi⟩).symm

/-- **Theorem 4, with the entry node counted** (`g:thm4_entry`). For a fully decomposed network, `T′` is `T̄` if and only if `N` is efficient in the sense of `IsEfficientAtEntry`, and it has the conventions of the paper (no recombination leaf, and the degree condition), and no site-free arc
with both ends off the blobs that isn't pendant (`RegularArcs`). So the printed theorem fails because line 327 omits the entry node from "external", and on site-free arcs. The repair of the definition is in print: Gusfield, *ReCombinatorics* (MIT Press, 2014), Section 7.3.5, states the theorem for canonical networks, a stricter class, as its Theorem 7.3.3, of which we read only snippets (`docs/REPORT.md`, E42). What this adds is the characterization in both directions, and the check in the kernel. -/
theorem theorem4_entry {V E : Type*} [Finite V] [Finite E] {N : Network ι V E} {M : Finset (ι → Bool)} (hd : N.Derives M)
    (hf : N.IsFullyDecomposedFor (incompatGraph M)) {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W}
    {edge : SuperChar M → Sym2 W} (hT : IsTBar M T φ edge) :
    (∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) ↔
      N.IsEfficientAtEntry ∧ N.RegularArcs ∧ N.DegreeCond := by
  have hnd := hf.nodeDisjoint
  rw [theorem4_iff hd hf hT]
  constructor
  · rintro ⟨he, hn, hdeg⟩
    exact ⟨(Network.isEfficientAtEntry_iff hnd).2 ⟨he.perBlob, hn.noAncestralExit.atEntered hd hdeg hnd⟩, hn.toRegularArcs, hdeg⟩
  · rintro ⟨he, hr, hdeg⟩
    have hn : N.IsTreeNormalStructural := ⟨hr, ((Network.isEfficientAtEntry_iff hnd).1 he).2.noAncestralExit⟩
    obtain ⟨f, hfr⟩ := N.exists_iso_of_isTreeNormalStructural hd hf he.perBlob hn hdeg hT
    exact ⟨N.isEfficient_of_iso hT hd hf f hfr, hn, hdeg⟩

end Theorem4

section Counterexamples

omit [LinearOrder ι] in
/-- An explicit network has no recombination leaf, if a recombination node has an arc out of it. -/
theorem GallCover.recomb_not_leaf {V E : Type*} {N : Network ι V E} (hr : ∀ e f, e ≠ f → N.tgt e = N.tgt f → ∃ g, N.src g = N.tgt e) :
    ∀ x, N.IsRecomb x → ¬ N.IsLeaf x := by
  rintro x ⟨e, f, hne, rfl, hf⟩ hleaf
  obtain ⟨g, hg⟩ := hr e f hne hf.symm
  exact hleaf g hg

omit [LinearOrder ι] in
/-- An explicit network has a site on each arc with both ends off the blobs that isn't pendant, from its colours. -/
theorem GallCover.arc_labelled {V E κ : Type*} {N : Network ι V E} {ac : E → Option κ} {vc : V → Option κ} (h : GallCover N ac vc)
    (hl : ∀ e, ac e = none → vc (N.src e) = none → vc (N.tgt e) = none → (∃ g, N.src g = N.tgt e) → ∃ i, N.site i = e) :
    ∀ e, N.IsTreeArc e → ¬ N.OnBlob (N.src e) → ¬ N.OnBlob (N.tgt e) → ¬ N.IsLeaf (N.tgt e) → ∃ i, N.site i = e := by
  intro e he hu hz hzl
  have hnone : ∀ {v}, ¬ N.OnBlob v → vc v = none := by
    intro v hv
    cases hk : vc v with
    | none => rfl
    | some k => exact absurd ((h.onBlob_iff v).2 ⟨k, hk⟩) hv
  refine hl e ((h.isTreeArc_iff e).1 he) (hnone hu) (hnone hz) ?_
  by_contra hne
  push Not at hne
  exact hzl hne

omit [LinearOrder ι] in
/-- What an explicit network needs for `NoAncestralExitAtEntered`, from its colours. -/
theorem GallCover.noAncestralExitAtEntered {V E κ : Type*} {N : Network ι V E} {ac : E → Option κ} {vc : V → Option κ} (h : GallCover N ac vc)
    (htop : ∀ k e w, vc (N.src e) = some k → vc (N.tgt e) ≠ some k → vc w = some k → (∀ f, ac f = some k → N.tgt f ≠ w) → w ≠ N.root →
      ∃ i, ac (N.site i) = some k ∧ N.label (N.src e) i ≠ N.label w i) : N.NoAncestralExitAtEntered := by
  rintro B e w hB hw hwr hs ht
  obtain ⟨k, rfl⟩ := (h.isBlob_iff B).1 hB
  obtain ⟨i, hi, hne⟩ := htop k e w (h.mem_blobVerts_iff.1 hs) (fun h' => ht (h.mem_blobVerts_iff.2 h')) (h.mem_blobVerts_iff.1 hw.1) hw.2 hwr
  exact ⟨i, hi, hne⟩

omit [LinearOrder ι] in
/-- What an explicit network needs for `IsTreeNormalStructural`, from its colours. -/
theorem GallCover.isTreeNormalStructural {V E κ : Type*} [Finite V] {N : Network ι V E} {ac : E → Option κ} {vc : V → Option κ} (h : GallCover N ac vc)
    (hr : ∀ e f, e ≠ f → N.tgt e = N.tgt f → ∃ g, N.src g = N.tgt e)
    (htop : ∀ k e w, vc (N.src e) = some k → vc (N.tgt e) ≠ some k → vc w = some k → (∀ f, ac f = some k → N.tgt f ≠ w) → w ≠ N.root →
      ∃ i, ac (N.site i) = some k ∧ N.label (N.src e) i ≠ N.label w i)
    (hl : ∀ e, ac e = none → vc (N.src e) = none → vc (N.tgt e) = none → (∃ g, N.src g = N.tgt e) → ∃ i, N.site i = e) : N.IsTreeNormalStructural where
  recomb_not_leaf := GallCover.recomb_not_leaf hr
  arc_labelled := h.arc_labelled hl
  noAncestralExit := (h.noAncestralExitAtEntered htop).noAncestralExit

omit [LinearOrder ι] in
/-- An exit at the top of a blob that isn't at the root, in an explicit network, contradicts `NoAncestralExitAtEntered`. -/
theorem GallCover.not_noAncestralExitAtEntered {V E κ : Type*} {N : Network ι V E} {ac : E → Option κ} {vc : V → Option κ} (h : GallCover N ac vc) {e : E} {k : κ}
    (hs : vc (N.src e) = some k) (ht : vc (N.tgt e) ≠ some k) (htop : ∀ f, ac f = some k → N.tgt f ≠ N.src e) (hroot : N.src e ≠ N.root) : ¬ N.NoAncestralExitAtEntered := by
  intro hna
  have hsm := h.mem_blobVerts_iff.2 hs
  obtain ⟨i, -, hne⟩ := hna {g | ac g = some k} e (N.src e) (h.isBlob_color k) ⟨hsm, htop⟩ hroot hsm fun h' => ht (h.mem_blobVerts_iff.1 h')
  exact hne rfl

/-- **Theorem 4 as printed fails on a recombination leaf** (`g:thm4_false_leaf`). `M = {00, 01, 10, 11}`, with `11` a recombination
leaf of `01` and `10`, and a leaf at the root and at each of `01`, `10`, in any model: `T′` has three edges, and `T̄` has four.

This is a convention of the paper, and not an error: Figure 1's caption speaks of the sequence "exiting" a recombination node, and line 341 needs it. Give a recombination node a pendant arc, and the example disappears. -/
theorem theorem4Printed_false_recombLeaf (c : Crossover) : ¬ Theorem4Printed c fourGametes := by
  intro h
  obtain ⟨n, T, φ, edge, hT⟩ := exists_isTBar fourGametes ⟨ofBits [0, 0], by simp [fourGametes]⟩ noConstantColumn_fourGametes
  obtain ⟨f, hfr⟩ := h 7 7 fourNet (fourNet_obeys c) fourNet_derives fourNet_fullyDecomposed fourNet_efficient trivial n T φ edge hT
  exact (fourNet.isTreeNormalStructural_of_iso hT fourNet_derives fourNet_fullyDecomposed f hfr).1.recomb_not_leaf 3 fourNet_recomb fourNet_leaf

/-- `T′` of `topNet` isn't `T̄`: the row `11001` hangs from the top of an entered blob. -/
theorem topNet_not_iso {n : ℕ} {T : SimpleGraph (Fin n)} {φ : topRows → Fin n} {edge : SuperChar topRows → Sym2 (Fin n)} (hT : IsTBar topRows T φ edge) :
    ¬ ∃ f : topNet.blobbedTree ≃g T, ∀ v r (hr : r ∈ topRows), topNet.IsLeaf v → topNet.label v = r → f (topNet.toBlobNode v) = φ ⟨r, hr⟩ := by
  rintro ⟨f, hfr⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := topNet_exit
  obtain ⟨hs, hdeg⟩ := topNet.isTreeNormalStructural_of_iso hT topNet_derives topNet_fullyDecomposed f hfr
  exact topNet_cover.not_noAncestralExitAtEntered h₁ h₂ h₃ h₄ (hs.noAncestralExit.atEntered topNet_derives hdeg topNet_cover.nodeDisjoint)

/-- **Theorem 4 is false, by the error at line 342** (`g:thm4_false_top`). With no recombination leaf, with every node of `T′` of degree at
most two a leaf, and with sites on all the arcs with both ends off the blobs that aren't pendant, Theorem 4 still fails, on `topRows`, in
any model. The network: a blob on `00000, 01000, 10000, 11000` with the sites 1, 2; an arc with the site 5 from `11000` to `11001`; a blob on
`11001, 11011, 11101, 11111` with the sites 3, 4; and a pendant arc at each node of the two blobs other than `11000`. It's efficient and fully decomposed.

The split `{00000, 01000, 10000, 11001} | {11011, 11101, 11111}` of `T̄` is missing from `T′`: the first side has the super-character `00` of the sites 3, 4 and the second doesn't, but in `T′` the row `11001` hangs from the blob of 3, 4.
The count of edges depends on the reading: with rows at leaves, `T̄` has nine edges and `T′` eight, and under line 264's reading, `T̄` has eight as well. So it's the split that's to be quoted.

A smaller instance is `theorem4_false_small`. The proof is by the converse, `theorem4_iff`. -/
theorem theorem4_false_top (c : Crossover) :
    ¬ Theorem4Form c topRows fun {a b} (N : Network (Fin 5) (Fin a) (Fin b)) => N.IsRegular := by
  intro h
  have hP : topNet.IsRegular := ⟨⟨GallCover.recomb_not_leaf topNet_hr, topNet_cover.arc_labelled topNet_hl⟩, topNet_degree⟩
  obtain ⟨n, T, φ, edge, hT⟩ := exists_isTBar topRows ⟨ofBits [0, 0, 0, 0, 0], by simp [topRows]⟩ noConstantColumn_topRows
  exact topNet_not_iso hT (h 15 16 topNet (topNet_obeys c) topNet_derives topNet_fullyDecomposed topNet_efficient hP n T φ edge hT)

/-- **`T′` isn't invariant over efficient fully decomposed networks** (`g:thm4_top_moved`). For `topRows`, the row `11001` hangs from the top of a blob in `topNet`, and from a new node on the arc entering that blob in `topNet'`. Both are efficient and fully decomposed, in the printed sense, with all of `IsRegular`. The second has `T′ = T̄`, and the first
doesn't. This is what the paper's "invariant underlying structure" (line 346) excludes. -/
theorem topRows_not_invariant (c : Crossover) {n : ℕ} {T : SimpleGraph (Fin n)} {φ : topRows → Fin n} {edge : SuperChar topRows → Sym2 (Fin n)} (hT : IsTBar topRows T φ edge) :
    topNet.Obeys c ∧ topNet'.Obeys c ∧ topNet.Derives topRows ∧ topNet'.Derives topRows ∧ topNet.IsFullyDecomposedFor (incompatGraph topRows) ∧ topNet'.IsFullyDecomposedFor (incompatGraph topRows) ∧ topNet.IsEfficient ∧ topNet'.IsEfficient ∧
      topNet.IsRegular ∧ topNet'.IsRegular ∧
      (∃ f : topNet'.blobbedTree ≃g T, ∀ v r (hr : r ∈ topRows), topNet'.IsLeaf v → topNet'.label v = r → f (topNet'.toBlobNode v) = φ ⟨r, hr⟩) ∧
      ¬ ∃ f : topNet.blobbedTree ≃g T, ∀ v r (hr : r ∈ topRows), topNet.IsLeaf v → topNet.label v = r → f (topNet.toBlobNode v) = φ ⟨r, hr⟩ := by
  have hs := topNet'_cover.isTreeNormalStructural topNet'_hr topNet'_htop topNet'_hl
  refine ⟨topNet_obeys c, topNet'_obeys c, topNet_derives, topNet'_derives, topNet_fullyDecomposed, topNet'_fullyDecomposed, topNet_efficient, topNet'_efficient,
    ⟨⟨GallCover.recomb_not_leaf topNet_hr, topNet_cover.arc_labelled topNet_hl⟩, topNet_degree⟩, ⟨hs.toRegularArcs, topNet'_degree⟩, ?_, topNet_not_iso hT⟩
  exact theorem4 c topRows 16 17 topNet' (topNet'_obeys c) topNet'_derives topNet'_fullyDecomposed topNet'_efficient ⟨hs, topNet'_degree⟩ n T φ edge hT

/-- **`topNet` isn't efficient, once the entry node counts** (`g:thm4_top_entry`). The arc entering the blob of the sites 3, 4, and the arc of the row `11001`, are at one node. So the counterexample of `theorem4_false_top` isn't one for `IsEfficientAtEntry`. -/
theorem topNet_not_isEfficientAtEntry : ¬ topNet.IsEfficientAtEntry := by
  intro he
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := topNet_entry
  have hc₁ : topNet.CrossesAt {e | topNetAc e = some 1} 4 (topNet.tgt 4) :=
    ⟨topNet_cover.mem_blobVerts_iff.2 h₁, Or.inr ⟨rfl, fun hm => h₂ (topNet_cover.mem_blobVerts_iff.1 hm)⟩⟩
  have hc₂ : topNet.CrossesAt {e | topNetAc e = some 1} 12 (topNet.tgt 4) :=
    ⟨topNet_cover.mem_blobVerts_iff.2 h₁, Or.inl ⟨h₅.symm, fun hm => h₄ (topNet_cover.mem_blobVerts_iff.1 hm)⟩⟩
  exact h₆ (he.edge_unique _ 4 12 _ (topNet_cover.isBlob_color 1) hc₁ hc₂)

/-- **The smaller instance of the error at line 342** (`g:thm4_false_small`), with one blob, and a root of degree 3: `{0000, 0001, 0010, 0110, 1010, 1110}`. The row `0010` hangs from the top of the blob, which has the sites 1, 2, and
which is entered by an arc with the site 3 from the root. The split `{0000, 0001, 0010} | {0110, 1010, 1110}` of `T̄` is missing from `T′`. -/
theorem theorem4_false_small (c : Crossover) :
    ¬ Theorem4Form c smallRows fun {a b} (N : Network (Fin 4) (Fin a) (Fin b)) => N.IsRegular := by
  intro h
  have hP : smallNet.IsRegular := ⟨⟨GallCover.recomb_not_leaf smallNet_hr, smallNet_cover.arc_labelled smallNet_hl⟩, smallNet_degree⟩
  obtain ⟨n, T, φ, edge, hT⟩ := exists_isTBar smallRows ⟨ofBits [0, 0, 0, 0], by simp [smallRows]⟩ noConstantColumn_smallRows
  obtain ⟨f, hfr⟩ := h 11 11 smallNet (smallNet_obeys c) smallNet_derives smallNet_fullyDecomposed smallNet_efficient hP n T φ edge hT
  obtain ⟨h₁, h₂, h₃, h₄⟩ := smallNet_exit
  obtain ⟨hs, hdeg⟩ := smallNet.isTreeNormalStructural_of_iso hT smallNet_derives smallNet_fullyDecomposed f hfr
  exact smallNet_cover.not_noAncestralExitAtEntered h₁ h₂ h₃ h₄ (hs.noAncestralExit.atEntered smallNet_derives hdeg smallNet_cover.nodeDisjoint)

/-- **A blob at the root can have an exit at the top** (`g:thm4_root_exit`). For `fourGametes`, take a blob at the root, and a pendant arc at each of its four nodes. Then `T′` is `T̄`, and a row hangs from the node carrying the ancestral super-character. So
`Network.NoAncestralExit` has to exempt a blob at the root: without the exemption, the "only if" of `theorem4_iff` would be false. -/
theorem fourGametes_rootExit (c : Crossover) {n : ℕ} {T : SimpleGraph (Fin n)} {φ : fourGametes → Fin n} {edge : SuperChar fourGametes → Sym2 (Fin n)}
    (hT : IsTBar fourGametes T φ edge) :
    fourRootNet.Obeys c ∧ fourRootNet.Derives fourGametes ∧ fourRootNet.IsFullyDecomposedFor (incompatGraph fourGametes) ∧ fourRootNet.IsEfficient ∧
      (∃ f : fourRootNet.blobbedTree ≃g T, ∀ v r (hr : r ∈ fourGametes), fourRootNet.IsLeaf v → fourRootNet.label v = r → f (fourRootNet.toBlobNode v) = φ ⟨r, hr⟩) ∧
      ∃ B e, fourRootNet.IsBlob B ∧ fourRootNet.IsBlobTop B (fourRootNet.src e) ∧ fourRootNet.tgt e ∉ fourRootNet.blobVerts B := by
  refine ⟨fourRootNet_obeys c, fourRootNet_derives, fourRootNet_fullyDecomposed, fourRootNet_efficient, ?_, _, 4, fourRootNet_cover.isBlob_color 0, ?_, ?_⟩
  · exact theorem4 c fourGametes 8 8 fourRootNet (fourRootNet_obeys c) fourRootNet_derives fourRootNet_fullyDecomposed fourRootNet_efficient
      ⟨fourRootNet_cover.isTreeNormalStructural fourRootNet_hr fourRootNet_htop fourRootNet_hl, fourRootNet_degree⟩ n T φ edge hT
  · exact ⟨fourRootNet_cover.mem_blobVerts_iff.2 fourRootNet_exit.1, fourRootNet_exit.2.2⟩
  · exact fun h => fourRootNet_exit.2.1 (fourRootNet_cover.mem_blobVerts_iff.1 h)

/-- **A blob at the root needs no exemption, once the entry node counts** (`g:thm4_root_entry`). `fourRootNet` has a row at the top of a blob, and it's efficient in the sense of `IsEfficientAtEntry`: the blob has no entering arc. -/
theorem fourRootNet_isEfficientAtEntry : fourRootNet.IsEfficientAtEntry := by
  obtain ⟨n, T, φ, edge, hT⟩ := exists_isTBar fourGametes ⟨ofBits [0, 0], by simp [fourGametes]⟩ noConstantColumn_fourGametes
  obtain ⟨-, hd, hf, -, hiso, -⟩ := fourGametes_rootExit .multiple hT
  exact ((theorem4_entry hd hf hT).1 hiso).1

/-- **The exemption of `theorem4_splits` is "no row off the top"** (`g:thm4_splits_rootfree`). The example is `fourRootNet` with a new root above its root, on an arc with no site. The blob has an entering arc and a row at its top, so that `NoAncestralExitAtEntered` fails, and yet no row is above the blob, and the
non-trivial splits of `T′` and `T̄` agree. (`T′` isn't `T̄`, since its root has degree one and no row: this network fails the degree condition.) -/
theorem theorem4_splits_siteFreeRoot :
    fourRootNet'.Derives fourGametes ∧ fourRootNet'.IsFullyDecomposedFor (incompatGraph fourGametes) ∧ fourRootNet'.IsEfficient ∧ ¬ fourRootNet'.NoAncestralExitAtEntered ∧ fourRootNet'.IsTreeNormalStructural ∧
      ∀ A : Set (Fin 2 → Bool), A ⊆ fourGametes → 2 ≤ A.encard → 2 ≤ ((fourGametes : Set (Fin 2 → Bool)) \ A).encard → (A ∈ fourRootNet'.treeSplits fourGametes ↔ A ∈ charSplits fourGametes) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := fourRootNet'_exit
  have hs : fourRootNet'.IsTreeNormalStructural := by
    refine ⟨⟨GallCover.recomb_not_leaf fourRootNet'_hr, fourRootNet'_cover.arc_labelled fourRootNet'_hl⟩, ?_⟩
    rintro B e w hB hw ⟨l, hl, hoff⟩ -
    exfalso
    obtain ⟨k, rfl⟩ := (fourRootNet'_cover.isBlob_iff B).1 hB
    obtain rfl : k = 0 := Subsingleton.elim _ _
    have hw' : w = fourRootNet'.src 5 := h₆ w (fourRootNet'_cover.mem_blobVerts_iff.1 hw.1) hw.2
    apply hoff
    rw [hw']
    rcases Relation.ReflTransGen.cases_head (fourRootNet'.reach_root l) with h | ⟨b, ⟨g, hg, hg'⟩, hb⟩
    · exact absurd (fourRootNet'_root.trans h) (hl 0)
    · rw [← h₅ g hg, hg']
      exact hb
  exact ⟨fourRootNet'_derives, fourRootNet'_fullyDecomposed, fourRootNet'_efficient, fourRootNet'_cover.not_noAncestralExitAtEntered h₁ h₂ h₃ h₄, hs,
    fun A hA hA₁ hA₂ => theorem4_splits fourRootNet' fourRootNet'_derives fourRootNet'_fullyDecomposed fourRootNet'_efficient.perBlob hs hA hA₁ hA₂⟩

/-- **A third failure of Theorem 4, on a site-free arc** (`g:thm4_false_sitefree`). The rows `10000, 01000, 00100, 00010, 00001`, with the root having arcs to the first two, and a site-free arc to a node with the other three. This is a perfect phylogeny, so it's efficient and fully decomposed, in any model; no recombination node, no blob, so no exit at
the top of a blob, and every node of `T′` of degree at most two has a leaf. Yet `T′` has an edge more than `T̄`, which is a star (`fiveNet_split`). Line 97 allows such arcs, and the proof at lines 341 to 344 considers only the edges leaving a blob and the character edges, so it never meets them. So `arc_labelled` can't be dropped from `theorem4`, and it isn't
one of the failures the entry node accounts for. -/
theorem theorem4_false_siteFree (c : Crossover) :
    ¬ Theorem4Form c fiveRows fun {a b} (N : Network (Fin 5) (Fin a) (Fin b)) => (∀ x, N.IsRecomb x → ¬ N.IsLeaf x) ∧ N.NoAncestralExit ∧ N.DegreeCond := by
  intro h
  have hna : fiveNet.NoAncestralExit := fun B _ _ hB => absurd hB (Network.not_isBlob_of_tgt_injective fiveNet_tgt_injective B)
  have hfd := Network.isFullyDecomposedFor_of_tgt_injective (G := incompatGraph fiveRows) fiveNet_tgt_injective
  obtain ⟨n, T, φ, edge, hT⟩ := exists_isTBar fiveRows ⟨_, fiveBelow_facts.2.2.2.2.1⟩ noConstantColumn_fiveRows
  obtain ⟨f, hfr⟩ := h 7 6 fiveNet (Network.obeys_of_tgt_injective fiveNet_tgt_injective c) fiveNet_derives hfd (Network.isEfficient_of_tgt_injective fiveNet_tgt_injective)
    ⟨GallCover.recomb_not_leaf fiveNet_hr, hna, fiveNet_degree⟩ n T φ edge hT
  obtain ⟨hs, -⟩ := fiveNet.isTreeNormalStructural_of_iso hT fiveNet_derives hfd f hfr
  obtain ⟨hne, hg⟩ := fiveNet_siteFree
  have hnb : ∀ v, ¬ fiveNet.OnBlob v := fun _ ⟨B, hB, _⟩ => Network.not_isBlob_of_tgt_injective fiveNet_tgt_injective B hB
  obtain ⟨i, hi⟩ := hs.arc_labelled 0 (Network.isTreeArc_of_tgt_injective fiveNet_tgt_injective 0) (hnb _) (hnb _) (fun hl => by
    obtain ⟨g, hg'⟩ := hg
    exact hl g hg')
  exact hne i hi

/-- The split of `theorem4_false_siteFree`: the arc with no site has the rows `00100, 00010, 00001` below it, which is a split of `T′` and not a split of `T̄`. -/
theorem fiveNet_split {n : ℕ} {T : SimpleGraph (Fin n)} {φ : fiveRows → Fin n} {edge : SuperChar fiveRows → Sym2 (Fin n)} (hT : IsTBar fiveRows T φ edge) :
    {y : fiveRows | y.1 ∈ fiveNet.arcSide 0} ∈ SempleSteel2003.splitSides fiveNet.blobbedTree (fiveNet.rowClass fiveNet_derives) ∧
      {y : fiveRows | y.1 ∈ fiveNet.arcSide 0} ∉ SempleSteel2003.splitSides T φ := by
  obtain ⟨hb₁, hb₂, hb₃, hb₄, hm₁, hm₂, hm₃, hm₄, hn₁, hn₂⟩ := fiveBelow_facts
  have hside : ∀ y : fiveRows, y ∈ {y : fiveRows | y.1 ∈ fiveNet.arcSide 0} ↔ y.1 ∈ fiveBelow := by
    intro y
    change y.1 ∈ fiveNet.arcSide 0 ↔ _
    rw [fiveNet_arcSide, Finset.mem_coe]
  refine ⟨(Network.isTreeArc_of_tgt_injective fiveNet_tgt_injective 0).mem_splitSides fiveNet_derives (Or.inl ⟨⟨_, hm₁⟩, (hside _).2 hb₁, rfl⟩), fun hmem => ?_⟩
  have hstar : fiveStarNet.IsTreeNormalStructural :=
    ⟨⟨GallCover.recomb_not_leaf fiveStarNet_hr, fun e _ _ _ hg => fiveStarNet_hl e (by
      by_contra hne
      push Not at hne
      exact hg hne)⟩, fun B _ _ hB => absurd hB (Network.not_isBlob_of_tgt_injective fiveStarNet_tgt_injective B)⟩
  rw [← fiveStarNet.splitSides_eq fiveStarNet_derives (Network.isFullyDecomposedFor_of_tgt_injective fiveStarNet_tgt_injective _)
    (Network.isEfficient_of_tgt_injective fiveStarNet_tgt_injective).perBlob hstar fiveStarNet_degree hT] at hmem
  obtain ⟨e, he, x, hx⟩ := hmem
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨g, hg, heq⟩ := Network.exists_isTreeArc_of_adj he
    have heq' : fiveStarNet.blobEdge g = s(a, b) := heq
    rw [← heq', hg.edgeSide_eq fiveStarNet_derives x] at hx
    split_ifs at hx with hxg
    · have h₁ : (⟨_, hm₁⟩ : fiveRows) ∈ {y : fiveRows | y.1 ∈ fiveNet.arcSide 0} := (hside _).2 hb₁
      have h₂ : (⟨_, hm₂⟩ : fiveRows) ∈ {y : fiveRows | y.1 ∈ fiveNet.arcSide 0} := (hside _).2 hb₂
      rw [hx] at h₁ h₂
      exact hn₁ (fiveStarNet_arcSide_subsingleton g h₁ h₂)
    · have h₁ : (⟨_, hm₃⟩ : fiveRows) ∉ {y : fiveRows | y.1 ∈ fiveNet.arcSide 0} := fun h' => hb₃ ((hside _).1 h')
      have h₂ : (⟨_, hm₄⟩ : fiveRows) ∉ {y : fiveRows | y.1 ∈ fiveNet.arcSide 0} := fun h' => hb₄ ((hside _).1 h')
      rw [hx, Set.notMem_compl_iff] at h₁ h₂
      exact hn₂ (fiveStarNet_arcSide_subsingleton g h₁ h₂)

/-- **Line 341's second half fails for the printed definition** (`g:line341_false`). "Each super-character derived from `C` labels exactly one external node of `b_C`." This is Figure 2 made efficient: the node `00100` has one arc off the first blob, to a new node `00100` with the row and the arc to the second blob. It's efficient and fully decomposed, and `T′` is
even `T̄`, so that Theorem 4 holds for it. But the super-character `00` of the component `{2, 5}` labels no external node of its blob: it's at the top of the blob, which has no arc out of the blob. So the proof's claim at line 341 is about a different notion of external node. With `IsEfficientAtEntry`, which this network has, the claim is true, by
`Network.IsEfficientAtEntry.existsUnique_port`. -/
theorem line341_false_fig2 (c : Crossover) :
    fig2Net.Obeys c ∧ fig2Net.Derives fig2Rows ∧ fig2Net.IsFullyDecomposedFor (incompatGraph fig2Rows) ∧ fig2Net.IsEfficient ∧ fig2Net.IsEfficientAtEntry ∧
      (∀ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : fig2Rows → Fin n) (edge : SuperChar fig2Rows → Sym2 (Fin n)), IsTBar fig2Rows T φ edge →
        ∃ f : fig2Net.blobbedTree ≃g T, ∀ v r (hr : r ∈ fig2Rows), fig2Net.IsLeaf v → fig2Net.label v = r → f (fig2Net.toBlobNode v) = φ ⟨r, hr⟩) ∧
      ∃ (C : (incompatGraph fig2Rows).ConnectedComponent) (B : Set (Fin 18)) (S₀ : C.supp → Bool), fig2Net.IsBlob B ∧ (∀ i, fig2Net.site i ∈ B ↔ i ∈ C.supp) ∧ S₀ ∈ restrictRows C.supp fig2Rows ∧
        ∀ v, fig2Net.IsExternal B v → C.supp.domRestrict (fig2Net.label v) ≠ S₀ := by
  obtain ⟨⟨r, hr, hr₁, hr₄⟩, hs₁, hs₄, hv⟩ := fig2Net_noPort
  obtain ⟨C, -, hC⟩ := fig2Net_fullyDecomposed.blob_component _ (fig2Net_cover.isBlob_color 1)
  have h₁ : (1 : Fin 5) ∈ C.supp := (hC 1).1 hs₁
  have h₄ : (4 : Fin 5) ∈ C.supp := (hC 4).1 hs₄
  refine ⟨fig2Net_obeys c, fig2Net_derives, fig2Net_fullyDecomposed, fig2Net_efficient,
    (Network.isEfficientAtEntry_iff fig2Net_cover.nodeDisjoint).2 ⟨fig2Net_efficient.perBlob, fig2Net_cover.noAncestralExitAtEntered fig2Net_htop⟩,
    fun n T φ edge hT => theorem4 c fig2Rows 17 18 fig2Net (fig2Net_obeys c) fig2Net_derives fig2Net_fullyDecomposed fig2Net_efficient
      ⟨fig2Net_cover.isTreeNormalStructural fig2Net_hr fig2Net_htop fig2Net_hl, fig2Net_degree⟩ n T φ edge hT,
    C, _, C.supp.domRestrict r, fig2Net_cover.isBlob_color 1, hC, mem_restrictRows.2 ⟨r, hr, rfl⟩, ?_⟩
  rintro v ⟨hvm, e, hes, het⟩ heq
  refine hv v (fig2Net_cover.mem_blobVerts_iff.1 hvm) ⟨e, hes, fun h => het (fig2Net_cover.mem_blobVerts_iff.2 h)⟩ ⟨?_, ?_⟩
  · exact (congrFun heq ⟨1, h₁⟩).trans hr₁
  · exact (congrFun heq ⟨4, h₄⟩).trans hr₄

end Counterexamples

/-! ### Section 4.2 -/

section Treeness

variable {V E : Type*} [Finite V] [Finite E]

omit [LinearOrder ι] in
/-- The treeness is the number of edges of `T′`. -/
theorem Network.treeness_eq_ncard_edgeSet (N : Network ι V E) : N.treeness = N.blobbedTree.edgeSet.ncard := by
  rw [Network.treeness, ← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective (fun e : {e // N.IsTreeArc e} => ⟨N.blobEdge e.1, Network.blobEdge_mem_edgeSet e.2⟩) ⟨?_, ?_⟩)
  · intro e f hef
    exact Subtype.ext (Network.blobEdge_injective e.2 f.2 (congrArg Subtype.val hef))
  · rintro ⟨x, hx⟩
    induction x using Sym2.ind with
    | _ a b =>
      obtain ⟨e, he, heq⟩ := Network.exists_isTreeArc_of_adj (N := N) (a := a) (b := b) hx
      exact ⟨⟨e, he⟩, Subtype.ext heq⟩

/-- **Section 4.2 as printed** (`g:treeness`). "With the above definition of treeness, it is clear that a phylogenetic network `N` is
the most tree-like if and only if `T̄` is the resulting undirected tree, after the blobs of `N` are contracted, and all the
edges are made undirected" (line 373), among networks with no two blobs sharing a node and no node of in-degree and out-degree one (line 364). False: see
below. -/
def MostTreeLikePrinted (c : Crossover) (M : Finset (ι → Bool)) : Prop :=
  ∀ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c → N.Derives M → N.BlobsNodeDisjoint →
    (∀ e f, N.tgt e = N.src f → (∀ g, N.tgt g = N.tgt e → g = e) → (∀ g, N.src g = N.src f → g = f) → False) →
    ((∀ (a' b' : ℕ) (N' : Network ι (Fin a') (Fin b')), N'.Obeys c → N'.Derives M → N'.BlobsNodeDisjoint →
        (∀ e f, N'.tgt e = N'.src f → (∀ g, N'.tgt g = N'.tgt e → g = e) → (∀ g, N'.src g = N'.src f → g = f) → False) →
        N'.treeness ≤ N.treeness) ↔
      ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : M → Fin n) (edge : SuperChar M → Sym2 (Fin n)), IsTBar M T φ edge →
        ∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩)

/-- **Counterexample to Section 4.2** (`g:treeness_false`). `starRows` has a network whose `T′` is `T̄`, the star with four edges, and a
network with six tree arcs and the same leaves, by resolving the star with two arcs that have no site. So the network with `T′ = T̄`
isn't the most tree-like. Not counting a site-free arc with both ends off the blobs escapes this example, but not `treeness_example₁`, `treeness_example₂`. -/
theorem mostTreeLikePrinted_false (c : Crossover) : ¬ MostTreeLikePrinted c starRows := by
  intro h
  have hstr : starNet.IsTreeNormalStructural :=
    starNet_cover.isTreeNormalStructural starNet_hr (fun k => k.elim) fun e _ _ _ hg => starNet_hl e hg
  have hR := theorem4 c starRows 5 4 starNet (Network.obeys_of_tgt_injective starNet_tgt_injective c) starNet_derives
    (Network.isFullyDecomposedFor_of_tgt_injective starNet_tgt_injective _) (Network.isEfficient_of_tgt_injective starNet_tgt_injective)
    ⟨hstr, starNet_degree⟩
  have hL := (h 5 4 starNet (Network.obeys_of_tgt_injective starNet_tgt_injective c) starNet_derives starNet_cover.nodeDisjoint starNet_noOneOne).2 hR
    7 6 starNet' (Network.obeys_of_tgt_injective starNet'_tgt_injective c) starNet'_derives starNet'_cover.nodeDisjoint starNet'_noOneOne
  rw [starNet_cover.treeness_eq, starNet'_cover.treeness_eq] at hL
  exact absurd hL (by decide +kernel)

/-- **The first stronger example of Section 4.2** (`g:treeness_example1`). The rows `0000 0001 0010 0100 1000 1100`, with `0010` hanging from the top of the blob through an arc with the site 3. It's efficient and fully decomposed, with
no node of in-degree and out-degree one, and no site-free arc with both ends off the blobs that isn't pendant; the arc from the root to the top of the blob is site-free, with one end on the blob. Its treeness is `7`, which is the number of edges of `T̄`, yet `T′` isn't `T̄`. -/
theorem treeness_example₁ (c : Crossover) :
    ∃ (a b : ℕ) (N : Network (Fin 4) (Fin a) (Fin b)), N.Obeys c ∧ N.Derives treenessRows₁ ∧ N.IsFullyDecomposedFor (incompatGraph treenessRows₁) ∧ N.IsEfficient ∧
      (∀ e f, N.tgt e = N.src f → (∀ g, N.tgt g = N.tgt e → g = e) → (∀ g, N.src g = N.src f → g = f) → False) ∧
      (∀ e, N.IsTreeArc e → ¬ N.OnBlob (N.src e) → ¬ N.OnBlob (N.tgt e) → ¬ N.IsLeaf (N.tgt e) → ∃ i, N.site i = e) ∧ N.treeness = 7 ∧
      ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : treenessRows₁ → Fin n) (edge : SuperChar treenessRows₁ → Sym2 (Fin n)), IsTBar treenessRows₁ T φ edge →
        T.edgeSet.ncard = 7 ∧ ¬ ∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ treenessRows₁), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩ := by
  refine ⟨11, 11, treenessNet₁', treenessNet₁'_obeys c, treenessNet₁'_derives, treenessNet₁'_fullyDecomposed, treenessNet₁'_efficient, treenessNet₁'_noOneOne, ?_, ?_, ?_⟩
  · exact treenessNet₁'_cover.arc_labelled treenessNet₁'_hl
  · rw [treenessNet₁'_cover.treeness_eq, treenessAc₁_card]
  · intro n T φ edge hT
    refine ⟨?_, ?_⟩
    · obtain ⟨f, -⟩ := theorem4 c treenessRows₁ 11 11 treenessNet₁ (treenessNet₁_obeys c) treenessNet₁_derives treenessNet₁_fullyDecomposed treenessNet₁_efficient
        ⟨treenessNet₁_cover.isTreeNormalStructural treenessNet₁_hr treenessNet₁_htop treenessNet₁_hl, treenessNet₁_degree⟩ n T φ edge hT
      rw [ncard_edgeSet_iso f, ← Network.treeness_eq_ncard_edgeSet, treenessNet₁_cover.treeness_eq, treenessAc₁_card]
    · rintro ⟨f, hfr⟩
      obtain ⟨h₁, h₂, h₃, h₄⟩ := treenessNet₁'_exit
      obtain ⟨hs, hdeg⟩ := treenessNet₁'.isTreeNormalStructural_of_iso hT treenessNet₁'_derives treenessNet₁'_fullyDecomposed f hfr
      exact treenessNet₁'_cover.not_noAncestralExitAtEntered h₁ h₂ h₃ h₄ (hs.noAncestralExit.atEntered treenessNet₁'_derives hdeg treenessNet₁'_cover.nodeDisjoint)

/-- **The second stronger example of Section 4.2** (`g:treeness_example2`). The rows `00000 00001 00010 00100 01000 10000 11000`, with two rows below a site-free exit at the top of the blob. It's efficient and fully decomposed, with
no node of in-degree and out-degree one, and no site-free arc with both ends off the blobs that isn't pendant; its other site-free arcs are at the blob, from the root to the top and from the top to the node of the two rows. Its treeness is `9`, more than the `8` edges of `T̄`. So counting the edges of `T′`, even without site-free arcs with both ends
off the blobs, doesn't make `T̄` the most tree-like. Two narrower counts, by hand and not in Lean: counting the edges with a site ties, at `3 = 3`, with `T′` not `T̄`; counting the edges with a character of `B`, as line 264 labels `T̄`, gives `6 < 7`. -/
theorem treeness_example₂ (c : Crossover) :
    ∃ (a b : ℕ) (N : Network (Fin 5) (Fin a) (Fin b)), N.Obeys c ∧ N.Derives treenessRows₂ ∧ N.IsFullyDecomposedFor (incompatGraph treenessRows₂) ∧ N.IsEfficient ∧
      (∀ e f, N.tgt e = N.src f → (∀ g, N.tgt g = N.tgt e → g = e) → (∀ g, N.src g = N.src f → g = f) → False) ∧
      (∀ e, N.IsTreeArc e → ¬ N.OnBlob (N.src e) → ¬ N.OnBlob (N.tgt e) → ¬ N.IsLeaf (N.tgt e) → ∃ i, N.site i = e) ∧ N.treeness = 9 ∧
      ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : treenessRows₂ → Fin n) (edge : SuperChar treenessRows₂ → Sym2 (Fin n)), IsTBar treenessRows₂ T φ edge →
        T.edgeSet.ncard = 8 := by
  refine ⟨13, 13, treenessNet₂', treenessNet₂'_obeys c, treenessNet₂'_derives, treenessNet₂'_fullyDecomposed, treenessNet₂'_efficient, treenessNet₂'_noOneOne, ?_, ?_, ?_⟩
  · exact treenessNet₂'_cover.arc_labelled treenessNet₂'_hl
  · rw [treenessNet₂'_cover.treeness_eq, treenessAc₂'_card]
  · intro n T φ edge hT
    obtain ⟨f, -⟩ := theorem4 c treenessRows₂ 12 12 treenessNet₂ (treenessNet₂_obeys c) treenessNet₂_derives treenessNet₂_fullyDecomposed treenessNet₂_efficient
      ⟨treenessNet₂_cover.isTreeNormalStructural treenessNet₂_hr treenessNet₂_htop treenessNet₂_hl, treenessNet₂_degree⟩ n T φ edge hT
    rw [ncard_edgeSet_iso f, ← Network.treeness_eq_ncard_edgeSet, treenessNet₂_cover.treeness_eq, treenessAc₂_card]

variable {M : Finset (ι → Bool)} {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W}

omit [LinearOrder ι] in
/-- The engine of `treeness_le_and_eq_iff`: where every node of `T′` of degree at most two has a leaf of `N`, and every non-trivial split of a tree arc is a split of a character of `B`, the treeness is at most the number of edges of `T̄`, with equality if and only if `T′` is `T̄`. The condition on splits is close to
the conclusion: `treeness_le_and_eq_iff` is the statement to quote, with conditions on `N`. -/
theorem treeness_le_of_charSplits (N : Network ι V E) (hd : N.Derives M)
    (hdeg : ∀ v, (N.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, N.IsLeaf l ∧ N.toBlobNode l = v)
    (hsp : ∀ A ∈ N.treeSplits M, 2 ≤ A.encard → 2 ≤ ((M : Set (ι → Bool)) \ A).encard → A ∈ charSplits M) (hT : IsTBar M T φ edge) :
    N.treeness ≤ T.edgeSet.ncard ∧
      (N.treeness = T.edgeSet.ncard ↔
        ∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) := by
  have htree := N.blobbedTree_isTree.1
  have hlab := N.rowClass_labelled hd hdeg
  have hrows : Nonempty M := by
    obtain ⟨l, hl, -⟩ := Network.exists_isLeaf_reach (N := N) N.root
    exact ⟨⟨_, hd.mapsTo hl⟩⟩
  -- each edge of `T′` has an edge of `T̄` with the same split
  have hmap : ∀ e : N.blobbedTree.edgeSet, ∃ e' : T.edgeSet, ∀ x y : M,
      SameSide N.blobbedTree e.1 (N.rowClass hd x) (N.rowClass hd y) ↔ SameSide T e'.1 (φ x) (φ y) := by
    rintro ⟨e', he'⟩
    induction e' using Sym2.ind with
    | _ a b =>
      obtain ⟨e, he, heq⟩ := Network.exists_isTreeArc_of_adj he'
      have heq' : N.blobEdge e = s(a, b) := heq
      simp only [← heq']
      obtain ⟨⟨y₁, hy₁⟩, ⟨y₀, hy₀⟩⟩ := he.exists_rows hd hlab
      obtain ⟨e', he'', hs⟩ := exists_edge_of_mem_splitSides hT.isTree.connected
        (hT.mem_splitSides_of_charSplits hy₁ hy₀ fun h₁ h₂ => hsp _ ⟨e, he, Or.inl rfl⟩ h₁ h₂)
      refine ⟨⟨e', he''⟩, fun x y => ?_⟩
      rw [he.sameSide_rowClass_iff hd x y, hs x y]
      rfl
  choose g hg using hmap
  have hinj : Function.Injective g := by
    intro e₁ e₂ h₁₂
    refine Subtype.ext (edge_eq_of_sameSide_iff htree hlab e₁.2 fun x y => ?_)
    rw [hg e₁ x y, hg e₂ x y, h₁₂]
  have hcard : Nat.card N.blobbedTree.edgeSet ≤ Nat.card T.edgeSet := Nat.card_le_card_of_injective g hinj
  have hle : N.treeness ≤ T.edgeSet.ncard := by
    rw [N.treeness_eq_ncard_edgeSet, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hcard
  refine ⟨hle, ⟨fun heq => ?_, ?_⟩⟩
  · have hcard' : Nat.card T.edgeSet ≤ Nat.card N.blobbedTree.edgeSet := by
      rw [N.treeness_eq_ncard_edgeSet, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at heq
      exact heq.ge
    have hbij : Function.Bijective g := (Function.Injective.bijective_of_nat_card_le hinj hcard')
    have hx₁ : SempleSteel2003.IsXTree N.blobbedTree (N.rowClass hd) := ⟨htree, hlab⟩
    have hx₂ : SempleSteel2003.IsXTree T φ := ⟨hT.isTree, hT.labelled⟩
    have hsplit : SempleSteel2003.splitSides N.blobbedTree (N.rowClass hd) = SempleSteel2003.splitSides T φ := by
      ext A
      constructor
      · rintro ⟨e, he, x, rfl⟩
        refine ⟨(g ⟨e, he⟩).1, (g ⟨e, he⟩).2, x, ?_⟩
        ext y
        exact hg ⟨e, he⟩ x y
      · rintro ⟨e', he', x, rfl⟩
        obtain ⟨e, he⟩ := hbij.2 ⟨e', he'⟩
        refine ⟨e.1, e.2, x, ?_⟩
        ext y
        have := hg e x y
        rw [he] at this
        exact this.symm
    obtain ⟨f, hf'⟩ := SempleSteel2003.xTree_unique hx₁ hx₂ hsplit
    refine ⟨f, fun v r hr hv hvr => ?_⟩
    rw [← hf' ⟨r, hr⟩, N.rowClass_eq hd hv hvr]
  · rintro ⟨f, -⟩
    rw [ncard_edgeSet_iso f, N.treeness_eq_ncard_edgeSet]

/-- **Non-pendant arcs at a blob have ports of their own.** An arc crossing a blob that isn't pendant, whether it leaves or enters, is the only arc crossing that blob at a node with the label of its end on the blob. Two pendant arcs can share a label, so this is weaker than `IsEfficientAtEntry`. -/
def Network.NonPendantPortsDistinct (N : Network ι V E) : Prop :=
  ∀ B e f u v, N.IsBlob B → N.CrossesAt B e u → N.CrossesAt B f v → ¬ N.IsLeaf (N.tgt e) → N.label u = N.label v → e = f

/-- With `RegularArcs`, each non-trivial split of a tree arc of a network whose blobs have the sites of one component and whose non-pendant ports are distinct is a character of `B`. -/
theorem Network.mem_charSplits_of_portsDistinct {N : Network ι V E} (hd : N.Derives M) (hnd : N.BlobsNodeDisjoint)
    (hone : ∀ B, N.IsBlob B → ∃ c : (incompatGraph M).ConnectedComponent, ∀ i, N.site i ∈ B ↔ i ∈ c.supp) (hr : N.RegularArcs) (hp : N.NonPendantPortsDistinct) :
    ∀ A ∈ N.treeSplits M, 2 ≤ A.encard → 2 ≤ ((M : Set (ι → Bool)) \ A).encard → A ∈ charSplits M := by
  have key : ∀ e, N.IsTreeArc e → ((M : Set (ι → Bool)) \ N.arcSide e).Nonempty → (N.arcSide e).encard ≠ 1 → N.arcSide e ∈ charSplits M := by
    intro e he hne hne₂
    have hleaf : ¬ N.IsLeaf (N.tgt e) := by
      intro hl
      refine hne₂ ?_
      have : N.arcSide e = {N.label (N.tgt e)} := by
        ext r
        constructor
        · rintro ⟨v, hv, hr', rfl⟩
          rcases Relation.ReflTransGen.cases_head hr' with h | ⟨b, ⟨g, hg, -⟩, -⟩
          · rw [h]; rfl
          · exact absurd hg (hl g)
        · rintro rfl
          exact ⟨_, hl, Relation.ReflTransGen.refl, rfl⟩
      rw [this, Set.encard_singleton]
    refine N.arcSide_mem_charSplits_of hd hnd hone hr he hne hne₂ ?_ ?_
    · intro B hB hsB l hl hnot
      by_contra hcon
      push Not at hcon
      have ht : N.tgt e ∉ N.blobVerts B := he.tgt_notMem_blobVerts hB hsB
      have hc₁ : N.CrossesAt B e (N.src e) := ⟨hsB, Or.inl ⟨rfl, ht⟩⟩
      obtain ⟨w, hw, -⟩ := Network.exists_isBlobTop_reach hsB
      by_cases hreach : N.Reach w l
      · rcases hw.position hnd hB hreach with h | ⟨e', he₁, he₂, he₃, he₄⟩
        · exact hr.recomb_not_leaf l (hB.isRecomb_of_isLeaf h hl) hl
        · have hlab : N.label (N.src e) = N.label (N.src e') :=
            hB.label_eq_of_forall hsB he₂ fun i hi => (hcon i hi).symm.trans (hB.label_eq_of_exit he₁ he₂ hi he₄)
          have hee := hp B e e' _ _ hB hc₁ ⟨he₂, Or.inl ⟨rfl, he₃⟩⟩ hleaf hlab
          exact hnot (hee ▸ he₄)
      · have hwr : w ≠ N.root := fun h => hreach (h ▸ N.reach_root l)
        obtain ⟨g, hg, hgw⟩ := (hw.eq_root_or_exists hnd hB).resolve_left hwr
        have hc₂ : N.CrossesAt B g w := ⟨hw.1, Or.inr ⟨hgw, hg.src_notMem_blobVerts hB (hgw ▸ hw.1)⟩⟩
        have hlab : N.label (N.src e) = N.label w :=
          hB.label_eq_of_forall hsB hw.1 fun i hi => (hcon i hi).symm.trans (hw.label_eq_of_not_reach hnd hB hi hreach)
        have hee := hp B e g _ _ hB hc₁ hc₂ hleaf hlab
        exact ht (hee ▸ hgw ▸ hw.1)
    · intro B hB htp f _ hf₂ hf₃
      by_contra hcon
      push Not at hcon
      have hc₁ : N.CrossesAt B e (N.tgt e) := ⟨htp.1, Or.inr ⟨rfl, he.src_notMem_blobVerts hB htp.1⟩⟩
      have hc₂ : N.CrossesAt B f (N.src f) := ⟨hf₂, Or.inl ⟨rfl, hf₃⟩⟩
      have hlab : N.label (N.tgt e) = N.label (N.src f) := hB.label_eq_of_forall htp.1 hf₂ fun i hi => (hcon i hi).symm
      have hee := hp B e f _ _ hB hc₁ hc₂ hleaf hlab
      exact hf₃ (hee ▸ htp.1)
  have hnonempty : ∀ X : Set (ι → Bool), 2 ≤ X.encard → X.Nonempty := fun X hX => by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    simp at hX
  have hne1 : ∀ X : Set (ι → Bool), 2 ≤ X.encard → X.encard ≠ 1 := fun X hX h => by
    rw [h] at hX
    simp at hX
  rintro A ⟨e, he, rfl | rfl⟩ h₁ h₂
  · exact key e he (hnonempty _ h₂) (hne1 _ h₁)
  · rw [Set.sdiff_sdiff_cancel_left (N.arcSide_subset hd e)] at h₂
    exact charSplits_diff (key e he (hnonempty _ h₁) (hne1 _ h₂))

/-- **The positive form of Section 4.2** (`g:treeness_positive`). Line 373 says "the most tree-like if and only if `T̄`". This is what's true: among networks

- whose blobs each have the sites of one component of `G(M)`, not nec. a non-trivial one (`hone`, with `hnd`, line 364),
- with no recombination leaf, and no site-free arc with both ends off the blobs that isn't pendant (`RegularArcs`),
- where an arc crossing a blob that isn't pendant is the only arc crossing it at a node of its label (`NonPendantPortsDistinct`),
- and where every node of `T′` of degree at most two has a leaf of `N` (`DegreeCond`),

the treeness is at most the number of edges of `T̄`, with equality if and only if `T′` is `T̄`.

So `N` needn't be fully decomposed, or efficient: `treeness_nonFD_example` attains equality with neither, and `treeness_strict_example` shows that the inequality can be strict for a fully decomposed network. Each counterexample fails exactly one condition: `treeness_example₁` and `treeness_example₂` have
an exit at the top of an entered blob, against `NonPendantPortsDistinct`; `treeness_positive_needs_root` has a root of degree one, against `DegreeCond`; `mostTreeLikePrinted_false` has a site-free arc, against `RegularArcs`.

What this doesn't say: a blob merging two components, or with no site, fails `hone`. Whether the inequality holds for those isn't proved here or refuted. The splits of the tree arcs aren't all characters of `B` then, so this argument doesn't apply. "No site-free blob" is part of `hone`.

Departure from the paper: line 373 has no conditions, and it's false without them. Its reasoning (lines 364 to 373) counts the edges of `T′` and takes `T̄` to have the most, which is `treeness_le_of_charSplits` once the splits are known. -/
theorem treeness_le_and_eq_iff (N : Network ι V E) (hd : N.Derives M) (hnd : N.BlobsNodeDisjoint)
    (hone : ∀ B, N.IsBlob B → ∃ c : (incompatGraph M).ConnectedComponent, ∀ i, N.site i ∈ B ↔ i ∈ c.supp) (hr : N.RegularArcs) (hp : N.NonPendantPortsDistinct) (hdeg : N.DegreeCond)
    (hT : IsTBar M T φ edge) :
    N.treeness ≤ T.edgeSet.ncard ∧
      (N.treeness = T.edgeSet.ncard ↔
        ∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) :=
  treeness_le_of_charSplits N hd hdeg (N.mem_charSplits_of_portsDistinct hd hnd hone hr hp) hT

omit [LinearOrder ι] [Finite V] [Finite E] in
/-- What an explicit network needs for `NonPendantPortsDistinct` when it has no entering arc and only pendant exits. -/
theorem GallCover.nonPendantPortsDistinct {κ : Type*} {N : Network ι V E} {ac : E → Option κ} {vc : V → Option κ} (h : GallCover N ac vc)
    (hexit : ∀ k e, vc (N.src e) = some k → vc (N.tgt e) ≠ some k → ∀ g, N.src g ≠ N.tgt e) (hentry : ∀ k e, vc (N.tgt e) = some k → vc (N.src e) = some k) :
    N.NonPendantPortsDistinct := by
  rintro B e f u v hB ⟨hu, h₁⟩ - hl -
  obtain ⟨k, rfl⟩ := (h.isBlob_iff B).1 hB
  rcases h₁ with ⟨rfl, ht⟩ | ⟨rfl, hs⟩
  · exact absurd (fun g => hexit k e (h.mem_blobVerts_iff.1 hu) (fun h' => ht (h.mem_blobVerts_iff.2 h')) g) hl
  · exact absurd (h.mem_blobVerts_iff.2 (hentry k e (h.mem_blobVerts_iff.1 hu))) hs

/-- **The positive form reaches networks that aren't fully decomposed** (`g:treeness_nonFD`). The rows `00, 01, 10`, compatible, in a network whose blob has only the site 1, with pendant arcs at its top, at one parent and at its recombination node. It isn't fully decomposed, and it isn't efficient, since the top and the recombination node have one label. It has the
conditions of `treeness_le_and_eq_iff`, and its `T′` is `T̄`, with `3` edges. -/
theorem treeness_nonFD_example (c : Crossover) {n : ℕ} {T : SimpleGraph (Fin n)} {φ : threeRows → Fin n} {edge : SuperChar threeRows → Sym2 (Fin n)} (hT : IsTBar threeRows T φ edge) :
    threeBlobNet.Obeys c ∧ threeBlobNet.Derives threeRows ∧ ¬ threeBlobNet.IsFullyDecomposedFor (incompatGraph threeRows) ∧ ¬ threeBlobNet.IsEfficient ∧
      threeBlobNet.BlobsNodeDisjoint ∧ (∀ B, threeBlobNet.IsBlob B → ∃ c : (incompatGraph threeRows).ConnectedComponent, ∀ i, threeBlobNet.site i ∈ B ↔ i ∈ c.supp) ∧
      threeBlobNet.RegularArcs ∧ threeBlobNet.NonPendantPortsDistinct ∧ threeBlobNet.DegreeCond ∧ threeBlobNet.treeness = 3 ∧ T.edgeSet.ncard = 3 ∧
      ∃ f : threeBlobNet.blobbedTree ≃g T, ∀ v r (hr : r ∈ threeRows), threeBlobNet.IsLeaf v → threeBlobNet.label v = r → f (threeBlobNet.toBlobNode v) = φ ⟨r, hr⟩ := by
  obtain ⟨hp₁, hp₂, hp₃⟩ := threeBlobNet_ports
  have hone : ∀ B, threeBlobNet.IsBlob B → ∃ c : (incompatGraph threeRows).ConnectedComponent, ∀ i, threeBlobNet.site i ∈ B ↔ i ∈ c.supp := by
    intro B hB
    obtain ⟨k, rfl⟩ := (threeBlobNet_cover.isBlob_iff B).1 hB
    obtain rfl : k = 0 := Subsingleton.elim _ _
    refine ⟨(incompatGraph threeRows).connectedComponentMk 0, fun i => ?_⟩
    change threeBlobAc (threeBlobNet.site i) = some 0 ↔ _
    rw [hp₃, SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    constructor
    · rintro rfl
      exact SimpleGraph.Reachable.refl _
    · intro hreach
      rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
      rcases Relation.ReflTransGen.cases_head hreach with h | ⟨b, hb, -⟩
      · exact h
      · exact absurd hb (threeRows_compatible i b)
  have hr : threeBlobNet.RegularArcs := ⟨GallCover.recomb_not_leaf threeBlobNet_hr, threeBlobNet_cover.arc_labelled threeBlobNet_hl⟩
  have hp : threeBlobNet.NonPendantPortsDistinct := threeBlobNet_cover.nonPendantPortsDistinct (fun k => by obtain rfl : k = 0 := Subsingleton.elim _ _; exact hp₁) (fun k => by obtain rfl : k = 0 := Subsingleton.elim _ _; exact hp₂)
  have hcount : T.edgeSet.ncard = 3 := by
    obtain ⟨f, -⟩ := theorem4 c threeRows 4 3 threeNet (Network.obeys_of_tgt_injective threeNet_tgt_injective c) threeNet_derives
      (Network.isFullyDecomposedFor_of_tgt_injective threeNet_tgt_injective _) (Network.isEfficient_of_tgt_injective threeNet_tgt_injective)
      ⟨threeNet_cover.isTreeNormalStructural threeNet_hr (fun k => k.elim) (fun e _ _ _ hg => threeNet_hl e hg), threeNet_degree⟩ n T φ edge hT
    rw [ncard_edgeSet_iso f, ← Network.treeness_eq_ncard_edgeSet, threeNet_cover.treeness_eq]
    decide +kernel
  have htr : threeBlobNet.treeness = 3 := by
    rw [threeBlobNet_cover.treeness_eq, threeBlobAc_card]
  refine ⟨threeBlobNet_obeys c, threeBlobNet_derives, threeBlobNet_not_fullyDecomposed, threeBlobNet_not_isEfficient, threeBlobNet_cover.nodeDisjoint, hone, hr, hp, threeBlobNet_degree, htr, hcount, ?_⟩
  exact (treeness_le_and_eq_iff threeBlobNet threeBlobNet_derives threeBlobNet_cover.nodeDisjoint hone hr hp threeBlobNet_degree hT).2.1 (htr.trans hcount.symm)

/-- **The inequality can be strict** (`g:treeness_strict`). The rows `000, 010, 100, 110, 111`, with a blob at the root, and two pendant arcs at its recombination node. It's fully decomposed, and has the conditions of `treeness_le_and_eq_iff`, and it isn't efficient. Its treeness is `5`, and `T̄` has `6` edges, which `pendantHubNet` attains
by a hub for the two rows. -/
theorem treeness_strict_example (c : Crossover) {n : ℕ} {T : SimpleGraph (Fin n)} {φ : pendantRows → Fin n} {edge : SuperChar pendantRows → Sym2 (Fin n)} (hT : IsTBar pendantRows T φ edge) :
    pendantNet.Obeys c ∧ pendantNet.Derives pendantRows ∧ pendantNet.IsFullyDecomposedFor (incompatGraph pendantRows) ∧ ¬ pendantNet.IsEfficient ∧
      pendantNet.RegularArcs ∧ pendantNet.NonPendantPortsDistinct ∧ pendantNet.DegreeCond ∧ pendantNet.treeness = 5 ∧ T.edgeSet.ncard = 6 := by
  obtain ⟨hp₁, hp₂⟩ := pendantNet_ports
  refine ⟨pendantNet_obeys c, pendantNet_derives, pendantNet_fullyDecomposed, pendantNet_not_isEfficient,
    ⟨GallCover.recomb_not_leaf pendantNet_hr, pendantNet_cover.arc_labelled pendantNet_hl⟩,
    pendantNet_cover.nonPendantPortsDistinct (fun k => by obtain rfl : k = 0 := Subsingleton.elim _ _; exact hp₁) (fun k => by obtain rfl : k = 0 := Subsingleton.elim _ _; exact hp₂), pendantNet_degree, ?_, ?_⟩
  · rw [pendantNet_cover.treeness_eq, pendantAc_card]
  · obtain ⟨f, -⟩ := theorem4 c pendantRows 10 10 pendantHubNet (pendantHubNet_obeys c) pendantHubNet_derives pendantHubNet_fullyDecomposed pendantHubNet_efficient
      ⟨pendantHubNet_cover.isTreeNormalStructural pendantHubNet_hr pendantHubNet_htop pendantHubNet_hl, pendantHubNet_degree⟩ n T φ edge hT
    rw [ncard_edgeSet_iso f, ← Network.treeness_eq_ncard_edgeSet, pendantHubNet_cover.treeness_eq, pendantHubAc_card]

omit [LinearOrder ι] in
/-- With at most one arc into each node, the neighbours in `T′` of a node are the neighbours of the node. -/
theorem Network.ncard_neighborSet_of_tgt_injective {N : Network ι V E} (h : Function.Injective N.tgt) (z : V) :
    (N.blobbedTree.neighborSet (N.toBlobNode z)).ncard = Set.ncard {y | ∃ e, (N.src e = z ∧ N.tgt e = y) ∨ (N.tgt e = z ∧ N.src e = y)} := by
  have hinj := Network.toBlobNode_injective_of_tgt_injective h
  have heq : N.blobbedTree.neighborSet (N.toBlobNode z) = N.toBlobNode '' {y | ∃ e, (N.src e = z ∧ N.tgt e = y) ∨ (N.tgt e = z ∧ N.src e = y)} := by
    ext a
    obtain ⟨y, rfl⟩ : ∃ y, N.toBlobNode y = a := Quotient.exists_rep a
    constructor
    · intro hadj
      obtain ⟨e, -, he⟩ := Network.exists_isTreeArc_of_adj hadj
      refine ⟨y, ⟨e, ?_⟩, rfl⟩
      rcases Sym2.eq_iff.1 he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨hinj h₁, hinj h₂⟩
      · exact Or.inr ⟨hinj h₂, hinj h₁⟩
    · rintro ⟨y', ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hy'⟩
      · rw [← hy']
        exact Network.blobbedTree_adj (Network.isTreeArc_of_tgt_injective h e)
      · rw [← hy']
        exact (Network.blobbedTree_adj (Network.isTreeArc_of_tgt_injective h e)).symm
  rw [heq, Set.ncard_image_of_injective _ hinj]

omit [Finite V] [Finite E] in
/-- **The positive form needs the root** (`g:treeness_positive_root`). The rows `00, 01, 10` have a network with no blob, and a new root above the star, on a site-free arc. It has no node of degree two in `T′`, and it has no non-trivial split at all, since it has three rows. But its treeness is `4`, and
`T̄` has `3` edges. So a node of `T′` of degree one with no row has to be excluded, and the positive form without that exclusion is false. This is why `treeness_le_and_eq_iff` has `DegreeCond`. -/
theorem treeness_positive_needs_root (c : Crossover) (n : ℕ) (T : SimpleGraph (Fin n)) (φ : threeRows → Fin n) (edge : SuperChar threeRows → Sym2 (Fin n))
    (hT : IsTBar threeRows T φ edge) :
    threeNet'.Obeys c ∧ threeNet'.Derives threeRows ∧ (∀ B, ¬ threeNet'.IsBlob B) ∧ (∀ v, (threeNet'.blobbedTree.neighborSet v).ncard ≠ 2) ∧
      (∀ A ∈ threeNet'.treeSplits threeRows, 2 ≤ A.encard → 2 ≤ ((threeRows : Set (Fin 2 → Bool)) \ A).encard → A ∈ charSplits threeRows) ∧
      threeNet'.treeness = 4 ∧ T.edgeSet.ncard = 3 := by
  refine ⟨Network.obeys_of_tgt_injective threeNet'_tgt_injective c, threeNet'_derives, Network.not_isBlob_of_tgt_injective threeNet'_tgt_injective, ?_, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨z, rfl⟩ : ∃ z, threeNet'.toBlobNode z = v := Quotient.exists_rep v
    rw [Network.ncard_neighborSet_of_tgt_injective threeNet'_tgt_injective]
    have hset : {y | ∃ e, (threeNet'.src e = z ∧ threeNet'.tgt e = y) ∨ (threeNet'.tgt e = z ∧ threeNet'.src e = y)} =
        ↑(Finset.univ.filter fun y => ∃ e, (threeNet'.src e = z ∧ threeNet'.tgt e = y) ∨ (threeNet'.tgt e = z ∧ threeNet'.src e = y)) := by
      ext y
      simp
    rw [hset, Set.ncard_coe_finset]
    exact threeNet'_degree z
  · rintro A ⟨e, -, hA⟩ h₁ h₂
    exfalso
    have hsub : A ⊆ threeRows := by
      rcases hA with rfl | rfl
      · exact threeNet'.arcSide_subset threeNet'_derives e
      · exact Set.sdiff_subset
    have hadd := Set.encard_sdiff_add_encard_of_subset hsub
    rw [Set.encard_coe_eq_coe_finsetCard, threeRows_card] at hadd
    have h₄ : (2 : ℕ∞) + 2 ≤ 3 := by
      calc (2 : ℕ∞) + 2 ≤ ((threeRows : Set (Fin 2 → Bool)) \ A).encard + A.encard := add_le_add h₂ h₁
        _ = 3 := hadd
    exact absurd h₄ (by decide)
  · rw [threeNet'_cover.treeness_eq]
    decide +kernel
  · obtain ⟨f, -⟩ := theorem4 c threeRows 4 3 threeNet (Network.obeys_of_tgt_injective threeNet_tgt_injective c) threeNet_derives
      (Network.isFullyDecomposedFor_of_tgt_injective threeNet_tgt_injective _) (Network.isEfficient_of_tgt_injective threeNet_tgt_injective)
      ⟨threeNet_cover.isTreeNormalStructural threeNet_hr (fun k => k.elim) (fun e _ _ _ hg => threeNet_hl e hg), threeNet_degree⟩ n T φ edge hT
    rw [ncard_edgeSet_iso f, ← Network.treeness_eq_ncard_edgeSet, threeNet_cover.treeness_eq]
    decide +kernel

/-- **Line 156: the undirected tree of a perfect phylogeny is invariant** (`g:pp_invariant`), for networks with no recombination node, with no site-free arc that isn't pendant, and with the degree condition: a reading of "perfect phylogeny" under which line 156 is true, given `perfectPhylogeny_not_invariant`. Any two have the one `T′`, respecting the rows: it's `T̄`, by `theorem4_iff`.

Departure from the paper: line 156 says "invariant over all perfect phylogenies", with "phylogenetic network without recombination cycles", and that's false for those: `perfectPhylogeny_not_invariant`. -/
theorem perfectPhylogeny_invariant [Finite ι] {V' E' : Type*} [Finite V'] [Finite E'] {N : Network ι V E} {N' : Network ι V' E'} (hC : NoConstantColumn M)
    (ht : Function.Injective N.tgt) (ht' : Function.Injective N'.tgt) (hd : N.Derives M) (hd' : N'.Derives M) (hr : N.RegularArcs) (hr' : N'.RegularArcs) (hdeg : N.DegreeCond) (hdeg' : N'.DegreeCond) :
    ∃ f : N.blobbedTree ≃g N'.blobbedTree, ∀ v v', N.IsLeaf v → N'.IsLeaf v' → N.label v = N'.label v' → f (N.toBlobNode v) = N'.toBlobNode v' := by
  obtain ⟨l, hl, -⟩ := Network.exists_isLeaf_reach (N := N) N.root
  obtain ⟨n, T', φ', edge', hT⟩ := exists_isTBar M ⟨_, hd.mapsTo hl⟩ hC
  obtain ⟨f₁, hf₁⟩ := (theorem4_iff hd (Network.isFullyDecomposedFor_of_tgt_injective ht _) hT).2 ⟨Network.isEfficient_of_tgt_injective ht,
    ⟨hr, fun B _ _ hB => absurd hB (Network.not_isBlob_of_tgt_injective ht B)⟩, hdeg⟩
  obtain ⟨f₂, hf₂⟩ := (theorem4_iff hd' (Network.isFullyDecomposedFor_of_tgt_injective ht' _) hT).2 ⟨Network.isEfficient_of_tgt_injective ht',
    ⟨hr', fun B _ _ hB => absurd hB (Network.not_isBlob_of_tgt_injective ht' B)⟩, hdeg'⟩
  refine ⟨f₁.trans f₂.symm, fun v v' hv hv' hl' => ?_⟩
  apply f₂.injective
  change f₂ (f₂.symm (f₁ (N.toBlobNode v))) = _
  rw [RelIso.apply_symm_apply, hf₁ v _ (hd.mapsTo hv) hv rfl, hf₂ v' _ (hd.mapsTo hv) hv' hl'.symm]

/-- **Line 156 without the conventions** (`g:pp_not_invariant`). `fiveNet` and `fiveStarNet` are two networks for one matrix with no recombination cycle, both with the degree condition, whose undirected trees aren't isomorphic: the first has six edges, and the second five. So a site-free arc that isn't pendant has to be contracted, as it isn't in line 97. -/
theorem perfectPhylogeny_not_invariant :
    fiveNet.Derives fiveRows ∧ fiveStarNet.Derives fiveRows ∧ Function.Injective fiveNet.tgt ∧ Function.Injective fiveStarNet.tgt ∧ fiveNet.DegreeCond ∧ fiveStarNet.DegreeCond ∧
      IsEmpty (fiveNet.blobbedTree ≃g fiveStarNet.blobbedTree) := by
  refine ⟨fiveNet_derives, fiveStarNet_derives, fiveNet_tgt_injective, fiveStarNet_tgt_injective, fiveNet_degree, fiveStarNet_degree, ⟨fun f => ?_⟩⟩
  have h := ncard_edgeSet_iso f
  rw [← Network.treeness_eq_ncard_edgeSet, ← Network.treeness_eq_ncard_edgeSet, fiveNet_treeness, fiveStarNet_treeness] at h
  omega

end Treeness

end Gusfield2007
