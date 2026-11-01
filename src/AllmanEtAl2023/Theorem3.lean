module

public import AllmanEtAl2023.Lemma3
public import AllmanEtAl2023.Claims
public import AllmanEtAl2023.Corollary1

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Theorem 3

"All B-quartets can be identified from the quartet `CF`s using `CF`-detectability and applications of the B-quartet Inference Rule."
`CFInferred p` is that procedure, on the CFs `p`: a function of the CFs alone. It holds of exactly the B-quartets, for generic parameters.
The rule in it is the printed one of Theorem 2, whose third hypothesis is on the induced network, that is, read off the CF of the third
set: the paper's proof shows that its part (a) suffices. Both directions are stated: "identified" needs that nothing else is inferred, which
is Theorem 2, and the proof's "all" is the induction.

The proof's first sentence reduces the theorem to the statement on topologies, which does not mention parameters: "Since the B-quartet
Inference Rule does not depend on parameters, we have only to show that this information together with the inference rule is enough to
identify all B-quartets". That is `theorem3_core`, whose induction follows the paper's, on networks:

* the base case: the network's four taxa are detected;
* "Passing to the induced network on those taxa, all edges in `ℬ` are retained. If this network has fewer than `n` taxa, then the inductive hypothesis gives" the claim:
  `exists_representatives_induced`, and `TopologyInferredA.image`, for "and by Corollary 2 on `𝒩⁺`";
* "If `{a, b, c, d}` remains a B-quartet, then we may delete that taxon";
* otherwise `{a, b, c, d}` is a T-quartet on `𝒩′`, Lemma 3 twice, the inductive hypothesis, and Inference Rule (a).

**What the paper does not say.** The inductive hypothesis speaks of the induced 4-taxon networks of an induced network. These must be, as far as their quartets go, the induced 4-taxon
networks of `𝒩⁺`, for what the hypothesis detects there to count here: `TopologyInferredA.image` uses `inducedHasQuartetTopology_induced` and `inducedHasStarTopology_induced`.

**The sentences of the paper not used.** "Theorem 1 thus shows that `CF_abcd` is `(ab|cd)`-cut" is not used in `theorem3_core`: its rule reads the topology. The description of a
network whose taxa cannot be reduced, by chains of 2-blobs, isn't used by the argument after it.

**"Although the proof of Theorem 3 shows that only part (a) of Theorem 2 is needed"**: the induction is on `TopologyInferredA`, the closure with part (a) alone (`theorem3_core_partA`, `theorem3_partA`), and `theorem3_core` follows from it.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

universe u v w

namespace AllmanEtAl2023

section Core

variable {V E X : Type*} [DecidableEq X] {N : RootedNetwork V E X}

/-- The closure of the first sentence of the proof of Theorem 3: what the topologies of the reduced unrooted trees of blobs of the induced
4-taxon networks give, with the Inference Rule. -/
inductive TopologyInferred (hN : IsBinaryNetwork N) : Finset X → Prop
  | detected (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) :
      InducedHasStarTopology hN a b c d h → TopologyInferred hN {a, b, c, d}
  | rule (a b c d e : X) (t q : Finset X) :
      ({a, b, c, d, e} : Finset X).card = 5 →
      TopologyInferred hN {a, b, c, d} → TopologyInferred hN {b, c, d, e} →
      t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      (InducedTreeSeparates hN t a e ∨ InducedIsBlobQuartet hN t) →
      q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      TopologyInferred hN q

/-- `TopologyInferred`, with part (a) of the Inference Rule alone: "only part (a) of Theorem 2 is needed". -/
inductive TopologyInferredA (hN : IsBinaryNetwork N) : Finset X → Prop
  | detected (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) :
      InducedHasStarTopology hN a b c d h → TopologyInferredA hN {a, b, c, d}
  | rule (a b c d e : X) (t q : Finset X) :
      ({a, b, c, d, e} : Finset X).card = 5 →
      TopologyInferredA hN {a, b, c, d} → TopologyInferredA hN {b, c, d, e} →
      t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      InducedTreeSeparates hN t a e →
      q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      TopologyInferredA hN q

/-- Part (a) of the rule is a part of the rule. -/
theorem TopologyInferredA.topologyInferred {hN : IsBinaryNetwork N} {Q : Finset X} (h : TopologyInferredA hN Q) : TopologyInferred hN Q := by
  induction h with
  | detected a b c d h hs => exact .detected a b c d h hs
  | rule a b c d e t q h5 _ _ ht hr hq ih₁ ih₂ => exact .rule a b c d e t q h5 ih₁ ih₂ ht (Or.inl hr) hq

/-- A set of four taxa detected by its topology is a B-quartet of its induced network, and so of the network, by Corollary 2. -/
theorem isBlobQuartet_of_inducedHasStarTopology (hN : IsBinaryNetwork N) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hs : InducedHasStarTopology hN a b c d h) : IsBlobQuartet N {a, b, c, d} := by
  have : Finite X := hN.finite_taxa
  let _ : Fintype X := Fintype.ofFinite X
  have hB := (Bridges.isBlobQuartetOnInduced_self_iff hN h).mpr ((Bridges.inducedHasStarTopology_iff hN h).mp hs)
  exact corollary2 hN _ _ subset_rfl hB

/-- **Soundness**: the Inference Rule, Theorem 2, infers only B-quartets. -/
theorem TopologyInferred.isBlobQuartet {hN : IsBinaryNetwork N} {Q : Finset X} (h : TopologyInferred hN Q) : IsBlobQuartet N Q := by
  induction h with
  | detected a b c d h hs => exact isBlobQuartet_of_inducedHasStarTopology hN h hs
  | rule a b c d e t q h5 _ _ ht hr hq ih₁ ih₂ =>
    obtain ⟨h₁, h₂, h₃⟩ := theorem2 hN h5 ih₁ ih₂ ht hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃

/-- A separation in a quartet tree of `Y` is one in the tree as a quartet tree of `X`. -/
theorem separated_map {Y : Set X} {s : QuartetTree Y} {a e : Y} (h : Separated s a e) :
    Separated (s.map Subtype.val_injective) a.1 e.1 := by
  obtain ⟨ha, he, hn⟩ := h
  refine ⟨?_, ?_, fun B hB => ?_⟩
  · rw [QuartetTree.map_taxa]
    exact Finset.mem_image_of_mem _ ha
  · rw [QuartetTree.map_taxa]
    exact Finset.mem_image_of_mem _ he
  · rw [QuartetTree.map_val] at hB
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
    rintro ⟨h₁, h₂⟩
    obtain ⟨a', ha', haa⟩ := Finset.mem_image.mp h₁
    obtain ⟨e', he', hee⟩ := Finset.mem_image.mp h₂
    have ha2 : a' = a := Subtype.ext haa
    have he2 : e' = e := Subtype.ext hee
    subst ha2
    subst he2
    exact hn C hC ⟨ha', he'⟩

/-- Four distinct taxa of `Y` are four distinct taxa of `X`. -/
theorem card_val_four {Y : Set X} {a b c d : Y} (h : ({a, b, c, d} : Finset Y).card = 4) :
    ({a.1, b.1, c.1, d.1} : Finset X).card = 4 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  exact TreeMetric.card_four_of_ne (fun h' => hab (Subtype.ext h')) (fun h' => hac (Subtype.ext h')) (fun h' => had (Subtype.ext h'))
    (fun h' => hbc (Subtype.ext h')) (fun h' => hbd (Subtype.ext h')) (fun h' => hcd (Subtype.ext h'))

/-- The rule's sets on `Y`, on `X`. -/
theorem image_val_four {Y : Set X} (a b c d : Y) :
    ({a, b, c, d} : Finset Y).image Subtype.val = ({a.1, b.1, c.1, d.1} : Finset X) := by
  simp [Finset.image_insert, Finset.image_singleton]

/-- **What the Inference Rule's third hypothesis (a) says on an induced network** is what it says on `𝒩⁺` (`a:claim:induced-induced`). -/
theorem InducedTreeSeparates.image (hN : IsBinaryNetwork N) {Y : Set X} (hY : Y.Nontrivial) {t : Finset Y} {a e : Y}
    (h : InducedTreeSeparates (induced_isBinaryNetwork hN Y hY) t a e) :
    InducedTreeSeparates hN (t.image Subtype.val) a.1 e.1 := by
  obtain ⟨u, v, w, z, h4, rfl, htop, hsep⟩ := h
  refine ⟨u.1, v.1, w.1, z.1, card_val_four h4, (image_val_four u v w z).symm,
    (inducedHasQuartetTopology_induced hN hY h4 (card_val_four h4)).mp htop, ?_⟩
  rw [← Bridges.map_quartetTree h4 (card_val_four h4)]
  exact separated_map hsep

/-- **What is inferred on an induced network is inferred on `𝒩⁺`**: "and by Corollary 2 on `𝒩⁺`". The induced 4-taxon networks of `𝒩⁺_Y` are those of `𝒩⁺`, as far as quartets go, which the
paper doesn't say (`a:claim:induced-induced`). -/
theorem TopologyInferredA.image (hN : IsBinaryNetwork N) {Y : Set X} (hY : Y.Nontrivial) {Q : Finset Y}
    (h : TopologyInferredA (induced_isBinaryNetwork hN Y hY) Q) : TopologyInferredA hN (Q.image Subtype.val) := by
  induction h with
  | detected a b c d h hs =>
    rw [image_val_four]
    exact .detected _ _ _ _ (card_val_four h) ((inducedHasStarTopology_induced hN hY h (card_val_four h)).mp hs)
  | rule a b c d e t q h5 _ _ ht hr hq ih₁ ih₂ =>
    rw [image_val_four] at ih₁ ih₂
    obtain ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩ := ne_of_card_five h5
    have sn : ∀ {x y : Y}, x ≠ y → x.1 ≠ y.1 := fun hxy h' => hxy (Subtype.ext h')
    have h5' : ({a.1, b.1, c.1, d.1, e.1} : Finset X).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [sn hab, sn hac, sn had, sn hae]),
        Finset.card_insert_of_notMem (by simp [sn hbc, sn hbd, sn hbe]),
        Finset.card_insert_of_notMem (by simp [sn hcd, sn hce]), Finset.card_pair (sn hde)]
    have hmem : ∀ {r : Finset Y}, r ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset Y)) →
        r.image Subtype.val ∈ ({{a.1, b.1, c.1, e.1}, {a.1, b.1, d.1, e.1}, {a.1, c.1, d.1, e.1}} : Finset (Finset X)) := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
      rcases hr with rfl | rfl | rfl
      · exact Or.inl (image_val_four _ _ _ _)
      · exact Or.inr (Or.inl (image_val_four _ _ _ _))
      · exact Or.inr (Or.inr (image_val_four _ _ _ _))
    exact .rule a.1 b.1 c.1 d.1 e.1 _ _ h5' ih₁ ih₂ (hmem ht) (InducedTreeSeparates.image hN hY hr) (hmem hq)

/-- Four taxa, named. -/
theorem exists_eq_of_card_four {Q : Finset X} (h : Q.card = 4) : ∃ a b c d : X, ({a, b, c, d} : Finset X) = Q := by
  obtain ⟨a, t, hat, rfl, ht⟩ := Finset.card_eq_succ.mp h
  obtain ⟨b, c, d, -, -, -, rfl⟩ := Finset.card_eq_three.mp ht
  exact ⟨a, b, c, d, rfl⟩

/-- A set of four taxa that is not a B-quartet on the network induced on `Y` is a T-quartet there. -/
theorem exists_isTreeQuartet_of_not_isBlobQuartetOnInduced (hN : IsBinaryNetwork N) {Y : Set X} {hY : Y.Nontrivial} {Q : Finset X}
    (hQ : (Q : Set X) ⊆ Y) (h4 : Q.card = 4) (hT : ¬ IsBlobQuartetOnInduced hN Y hY Q) :
    ∃ Q' : Finset Y, Q'.image Subtype.val = Q ∧ IsTreeQuartet (induced hN Y hY) Q' := by
  unfold IsBlobQuartetOnInduced at hT
  refine ⟨_, ?_, ?_, hT⟩
  · ext x
    simp only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hQ h, h⟩⟩
  · rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => hQ hx), h4]

theorem insert_dcba (a b c d : X) : ({d, c, b, a} : Finset X) = {a, b, c, d} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem insert_dcbα (b c d α : X) : ({d, c, b, α} : Finset X) = {b, c, α, d} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **The last step of the proof of Theorem 3.** "Applying Lemma 3 twice, we conclude that `{a, b, c, α}` and `{b, c, d, α}` are B-quartets on the networks induced from `𝒩⁺` by removing `d` and `a`
respectively. As these are networks on `n - 1` taxa, the inductive hypothesis ensures that they can be detected as B-quartets. ... An application of Inference Rule (a) of Theorem 2 then establishes the
claim." The hypothesis `hstep` is the inductive hypothesis, with Corollary 2. -/
theorem topologyInferred_of_cut (hN : IsBinaryNetwork N)
    (hstep : ∀ (Y : Set X) (hY : Y.Nontrivial), Y ≠ Set.univ → ∀ q : Finset X, (q : Set X) ⊆ Y →
      IsBlobQuartetOnInduced hN Y hY q → TopologyInferredA hN q)
    {a b c d α : X} (h4 : ({a, b, c, d} : Finset X).card = 4) (hαa : α ≠ a) (hαb : α ≠ b) (hαc : α ≠ c) (hαd : α ≠ d)
    (hQ : IsBlobQuartet N {a, b, c, d}) (hα : ({α}ᶜ : Set X).Nontrivial)
    (hcut : HasCutEdgeSeparating (induced hN ({α}ᶜ : Set X) hα) (Subtype.val ⁻¹' {a, b}) (Subtype.val ⁻¹' {c, d}))
    (hcut' : HasCutEdgeSeparating (induced hN ({α}ᶜ : Set X) hα) (Subtype.val ⁻¹' {d, c}) (Subtype.val ⁻¹' {b, a}))
    (htop : InducedHasQuartetTopology hN a b c d h4) : TopologyInferredA hN {a, b, c, d} := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h4
  have hntd : ({d}ᶜ : Set X).Nontrivial := ⟨a, had, b, hbd, hab⟩
  have hnta : ({a}ᶜ : Set X).Nontrivial := ⟨d, had.symm, c, hac.symm, hcd.symm⟩
  have hL₁ := lemma3 hN h4 hαa hαb hαc hαd hQ hα hcut hntd
  have h4r : ({d, c, b, a} : Finset X).card = 4 :=
    TreeMetric.card_four_of_ne hcd.symm hbd.symm had.symm hbc.symm hac.symm hab.symm
  have hL₂ := lemma3 hN h4r hαd hαc hαb hαa ((insert_dcba a b c d).symm ▸ hQ) hα hcut' hnta
  have hneuniv : ∀ z : X, ({z}ᶜ : Set X) ≠ Set.univ := fun z h => by
    have : z ∈ ({z}ᶜ : Set X) := h ▸ Set.mem_univ z
    exact this rfl
  have hI₁ := hstep _ hntd (hneuniv d) {a, b, c, α} (by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact had
    · exact hbd
    · exact hcd
    · exact hαd) hL₁
  have hI₂ := hstep _ hnta (hneuniv a) {d, c, b, α} (by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact had.symm
    · exact hac.symm
    · exact hab.symm
    · exact hαa) hL₂
  rw [insert_dcbα] at hI₂
  have h5 : ({a, b, c, α, d} : Finset X).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, hαa.symm]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, hαb.symm]),
      Finset.card_insert_of_notMem (by simp [hcd, hαc.symm]), Finset.card_pair hαd]
  exact .rule a b c α d {a, b, c, d} {a, b, c, d} h5 hI₁ hI₂ (by simp)
    ⟨a, b, c, d, h4, rfl, htop, separated_quartetTree h4⟩ (by simp)

end Core

/-- **The induction of the proof of Theorem 3**, on the number of taxa, for all networks. -/
theorem topologyInferredA_of_isBlobQuartet (n : ℕ) :
    ∀ (X : Type u) (V : Type v) (E : Type w) [DecidableEq X] (N : RootedNetwork V E X) (hN : IsBinaryNetwork N),
      Nat.card X = n → ∀ Q : Finset X, IsBlobQuartet N Q → TopologyInferredA hN Q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X V E _ N hN hn Q hQ
    have hP := hN.isPhylogenetic
    have : Finite X := hP.finite_taxa
    let _ : Fintype X := Fintype.ofFinite X
    have h4 := hQ.1
    -- passing to an induced network on fewer taxa, "the inductive hypothesis gives" the claim
    have hstep : ∀ (Y : Set X) (hY : Y.Nontrivial), Y ≠ Set.univ → ∀ q : Finset X, (q : Set X) ⊆ Y →
        IsBlobQuartetOnInduced hN Y hY q → TopologyInferredA hN q := by
      intro Y hY hne q hq hB
      have hlt : Nat.card Y < n := by
        rw [← hn, Nat.card_coe_set_eq, ← Set.ncard_univ]
        exact Set.ncard_lt_ncard (Set.ssubset_univ_iff.mpr hne) (Set.toFinite _)
      have hind := ih _ hlt Y _ _ (induced hN Y hY) (induced_isBinaryNetwork hN Y hY) rfl _ hB
      have himg := TopologyInferredA.image hN hY hind
      have heq : (q.subtype (· ∈ Y)).image Subtype.val = q := by
        ext x
        simp only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_right, exists_eq_right]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hq h, h⟩⟩
      rwa [heq] at himg
    by_cases hQu : Q = Finset.univ
    · -- the base case
      obtain ⟨a, b, c, d, rfl⟩ := exists_eq_of_card_four h4
      refine .detected a b c d h4 ((Bridges.inducedHasStarTopology_iff hN h4).mpr ?_)
      rw [Bridges.isTreelike_iff_resolves hP h4]
      have hR := (Bridges.isBlobQuartet_iff_not_resolves hN h4).mp hQ
      rwa [← hQu] at hR
    -- "Choose one taxon from each component which contains a taxon"
    obtain ⟨B, hB⟩ := hQ.2
    obtain ⟨R, hQR, -, -, hRnt, hBR⟩ := exists_representatives_induced hN hB h4
    by_cases hRu : R = Finset.univ
    · -- "If `{a, b, c, d}` remains a B-quartet, then we may delete that taxon"
      by_cases hrem : ∃ α, α ∉ Q ∧ ∃ hα : ({α}ᶜ : Set X).Nontrivial, IsBlobQuartetOnInduced hN ({α}ᶜ : Set X) hα Q
      · obtain ⟨α, hαQ, hα, hBα⟩ := hrem
        refine hstep _ hα (fun h => ?_) Q (fun x hx hxα => hαQ (hxα ▸ hx)) hBα
        have : α ∈ ({α}ᶜ : Set X) := h ▸ Set.mem_univ α
        exact this rfl
      -- "fix some `α ∈ X \ {a, b, c, d}`"
      obtain ⟨α, hαQ⟩ : ∃ α, α ∉ Q := by
        by_contra hno
        push Not at hno
        exact hQu (Finset.eq_univ_iff_forall.mpr hno)
      have hQsub : (Q : Set X) ⊆ ({α}ᶜ : Set X) := fun x hx hxα => hαQ (hxα ▸ hx)
      have hα : ({α}ᶜ : Set X).Nontrivial :=
        (nontrivial_coe_of_card_four h4).mono hQsub
      have hT : ¬ IsBlobQuartetOnInduced hN ({α}ᶜ : Set X) hα Q := fun h => hrem ⟨α, hαQ, hα, h⟩
      let _ : Fintype ↥({α}ᶜ : Set X) := Fintype.ofFinite _
      have hN' := induced_isBinaryNetwork hN ({α}ᶜ : Set X) hα
      have hX' : Nontrivial ↥({α}ᶜ : Set X) := hα.coe_sort
      -- "There must be a cut edge `e₀` in `𝒩′` that separates two of `a, b, c, d`, say `a, b`, from the others"
      obtain ⟨Q', hQ'img, hTq⟩ := exists_isTreeQuartet_of_not_isBlobQuartetOnInduced hN hQsub h4 hT
      obtain ⟨s, hs, hd⟩ := exists_displays_of_isTreeQuartet hN' hX' hTq
      obtain ⟨a', b', c', d', h4', rfl⟩ := TreeMetric.exists_eq_quartetTree s
      have hQ'eq : ({a', b', c', d'} : Finset _) = Q' := (quartetTree_taxa _ _ _ _ _).symm.trans (mem_treesOn.1 hs)
      have hQeq : ({a'.1, b'.1, c'.1, d'.1} : Finset X) = Q := by rw [← image_val_four, hQ'eq, hQ'img]
      subst hQeq
      obtain ⟨a, ha⟩ := a'
      obtain ⟨b, hb⟩ := b'
      obtain ⟨c, hc⟩ := c'
      obtain ⟨d, hd'⟩ := d'
      have hαa : α ≠ a := fun h => ha h.symm
      have hαb : α ≠ b := fun h => hb h.symm
      have hαc : α ≠ c := fun h => hc h.symm
      have hαd : α ≠ d := fun h => hd' h.symm
      obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h4
      -- the cut edge
      have hU : IsUnrootedTree (Trd hN' hX').splits := by
        rw [Bridges.splits_Trd]
        exact isUnrootedTree_treeOfBlobs hN'.isPhylogenetic
      have hcardY : 2 ≤ Fintype.card ↥({α}ᶜ : Set X) := Fintype.one_lt_card_iff_nontrivial.mpr hX'
      obtain ⟨A, hA, haA, hbA, hcA, hdA⟩ := (TreeMetric.displays_quartetTree_iff (hU.isSplitFamily hcardY) h4').mp hd
      rw [Bridges.splits_Trd] at hA
      obtain ⟨-, -, e₀, S, hS, hSA⟩ := (mem_treeOfBlobs_iff A).mp hA
      have hmemS : ∀ x, (induced hN ({α}ᶜ : Set X) hα).leaf x ∈ S ↔ x ∈ A := fun x => by
        have := Set.ext_iff.mp hSA x
        simpa using this
      have hcut : HasCutEdgeSeparating (induced hN ({α}ᶜ : Set X) hα) (Subtype.val ⁻¹' {a, b}) (Subtype.val ⁻¹' {c, d}) := by
        refine ⟨e₀, S, hS, fun x hx => ?_, fun x hx => ?_⟩
        · rcases hx with hx | hx
          · have : x = ⟨a, ha⟩ := Subtype.ext hx
            exact (hmemS x).mpr (this ▸ haA)
          · have : x = ⟨b, hb⟩ := Subtype.ext hx
            exact (hmemS x).mpr (this ▸ hbA)
        · rcases hx with hx | hx
          · have : x = ⟨c, hc⟩ := Subtype.ext hx
            exact fun h => hcA (this ▸ (hmemS x).mp h)
          · have : x = ⟨d, hd'⟩ := Subtype.ext hx
            exact fun h => hdA (this ▸ (hmemS x).mp h)
      have hcut' : HasCutEdgeSeparating (induced hN ({α}ᶜ : Set X) hα) (Subtype.val ⁻¹' {d, c}) (Subtype.val ⁻¹' {b, a}) := by
        refine ⟨e₀, Sᶜ, fun f => ((induced hN ({α}ᶜ : Set X) hα).graph.crosses_compl f S).trans (hS f), fun x hx => ?_, fun x hx => ?_⟩
        · rcases hx with hx | hx
          · have : x = ⟨d, hd'⟩ := Subtype.ext hx
            exact fun h => hdA (this ▸ (hmemS x).mp h)
          · have : x = ⟨c, hc⟩ := Subtype.ext hx
            exact fun h => hcA (this ▸ (hmemS x).mp h)
        · rcases hx with hx | hx
          · have : x = ⟨b, hb⟩ := Subtype.ext hx
            exact not_not.mpr ((hmemS x).mpr (this ▸ hbA))
          · have : x = ⟨a, ha⟩ := Subtype.ext hx
            exact not_not.mpr ((hmemS x).mpr (this ▸ haA))
      have htop : InducedHasQuartetTopology hN a b c d h4 :=
        (inducedHasQuartetTopology_induced hN hα h4' h4).mp (inducedHasQuartetTopology_of_displays hN' hX' h4' hd)
      exact topologyInferred_of_cut hN hstep h4 hαa hαb hαc hαd hQ hα hcut hcut' htop
    · -- "If this network has fewer than `n` taxa"
      refine hstep _ hRnt (fun h => hRu ?_) Q (Finset.coe_subset.mpr hQR) hBR
      exact Finset.coe_injective (by rw [h, Finset.coe_univ])

section Theorem3

variable {V E X : Type*} [DecidableEq X] {N : RootedNetwork V E X}

/-- **"Although the proof of Theorem 3 shows that only part (a) of Theorem 2 is needed to infer all B-quartets from those that are `CF`-detectable"** (`a:claim:part-a`, after Theorem 3), on topologies. -/
theorem theorem3_core_partA (hN : IsBinaryNetwork N) {Q : Finset X} :
    TopologyInferredA hN Q ↔ IsBlobQuartet N Q :=
  ⟨fun h => h.topologyInferred.isBlobQuartet, topologyInferredA_of_isBlobQuartet _ _ _ _ _ hN rfl Q⟩

/-- **The induction of the proof of Theorem 3** (`a:claim:thm3-core`). From the topologies of the reduced unrooted trees of blobs of all induced
4-taxon networks, the Inference Rule identifies all B-quartets, and only those. -/
theorem theorem3_core (hN : IsBinaryNetwork N) {Q : Finset X} :
    TopologyInferred hN Q ↔ IsBlobQuartet N Q :=
  ⟨TopologyInferred.isBlobQuartet, fun h => ((theorem3_core_partA hN).mpr h).topologyInferred⟩

variable [Fintype V] [Fintype E] [Fintype X]

/-- What `readTopology` returning `first` says. -/
theorem isStrictlyCutAtFirst_of_readTopology {t : ℝ × ℝ × ℝ} (h : readTopology t = .first) : IsStrictlyCutAtFirst t := by
  unfold readTopology at h
  split_ifs at h with h₁
  exact h₁

/-- A strictly `(ab|cd)`-cut `CF` reads `first`. -/
theorem readTopology_of_isStrictlyCutAtFirst {t : ℝ × ℝ × ℝ} (h : IsStrictlyCutAtFirst t) : readTopology t = .first := by
  unfold readTopology
  split_ifs with h₁
  · rfl
  all_goals exact absurd h h₁

omit [Fintype V] [Fintype E] in
/-- A resolved topology on a set of four taxa excludes the other two, and the unresolved one. -/
theorem isStrictlyCutAtFirst_of_inducedHasQuartetTopology (hN : IsBinaryNetwork N) {t : ℝ × ℝ × ℝ} {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) (hT : InducedTopologyIs hN a b c d h (readTopology t))
    (hq : InducedHasQuartetTopology hN a b c d h) : IsStrictlyCutAtFirst t := by
  have hP := hN.isPhylogenetic
  have hc := (Bridges.inducedHasQuartetTopology_iff hN h).mp hq
  rcases hr : readTopology t with _ | _ | _ | _
  · exact isStrictlyCutAtFirst_of_readTopology hr
  · exfalso
    rw [hr] at hT
    have hc' := (Bridges.inducedHasQuartetTopology_iff hN (card_acbd h)).mp hT
    refine quartetTree_ne_acbd h (inducedCutSplit_unique hP hc hc' ?_)
    rw [quartetTree_taxa, quartetTree_taxa]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · exfalso
    rw [hr] at hT
    have hc' := (Bridges.inducedHasQuartetTopology_iff hN (card_adbc h)).mp hT
    refine quartetTree_ne_adbc h (inducedCutSplit_unique hP hc hc' ?_)
    rw [quartetTree_taxa, quartetTree_taxa]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · exfalso
    rw [hr] at hT
    refine (Bridges.inducedHasStarTopology_iff hN h).mp hT ⟨_, ?_, hc⟩
    exact mem_treesOn.2 (quartetTree_taxa _ _ _ _ _)

omit [Fintype V] [Fintype E] in
/-- For parameters where Corollary 1 holds, the unresolved topology is what `readTopology` says. -/
theorem readTopology_eq_star_iff (hN : IsBinaryNetwork N) {t : ℝ × ℝ × ℝ} {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hT : InducedTopologyIs hN a b c d h (readTopology t)) : readTopology t = .star ↔ InducedHasStarTopology hN a b c d h := by
  have hno := (Bridges.inducedHasStarTopology_iff hN h)
  constructor
  · intro hr
    rwa [hr] at hT
  · intro hs
    have hnt := hno.mp hs
    rcases hr : readTopology t with _ | _ | _ | _
    · rw [hr] at hT
      exact absurd ((Bridges.isTreelike_quartet_iff h).mpr (Or.inl ((Bridges.inducedHasQuartetTopology_iff hN h).mp hT))) hnt
    · rw [hr] at hT
      exact absurd ((Bridges.isTreelike_quartet_iff h).mpr (Or.inr (Or.inl ((Bridges.inducedHasQuartetTopology_iff hN (card_acbd h)).mp hT)))) hnt
    · rw [hr] at hT
      exact absurd ((Bridges.isTreelike_quartet_iff h).mpr (Or.inr (Or.inr ((Bridges.inducedHasQuartetTopology_iff hN (card_adbc h)).mp hT)))) hnt
    · rfl

/-- For parameters where Corollary 1 holds, the resolved topology is what the `CF` says. -/
theorem isStrictlyCutAt_iff_inducedHasQuartetTopology (hN : IsBinaryNetwork N) {θ : MetricData E}
    (h₁ : ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), InducedTopologyIs hN a b c d h (readTopology (cfTriple N θ a b c d h)))
    {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    IsStrictlyCutAt (nmscCF N θ 0) (quartetTree a b c d h) ↔ InducedHasQuartetTopology hN a b c d h := by
  constructor
  · intro hs
    have hT := h₁ a b c d h
    have hs' : IsStrictlyCutAtFirst (cfTriple N θ a b c d h) := (isStrictlyCutAtFirst_iff _ h).mpr hs
    rwa [readTopology_of_isStrictlyCutAtFirst hs'] at hT
  · exact fun hq => (isStrictlyCutAtFirst_iff _ h).mp (isStrictlyCutAtFirst_of_inducedHasQuartetTopology hN h (h₁ a b c d h) hq)

/-- For parameters where Corollary 1 holds, `readTopology` reads a set as unresolved exactly when the set is a B-quartet on its induced network. -/
theorem readsUnresolved_iff (hN : IsBinaryNetwork N) {θ : MetricData E}
    (h₁ : ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), InducedTopologyIs hN a b c d h (readTopology (cfTriple N θ a b c d h))) {t : Finset X} :
    ReadsUnresolved (nmscCF N θ 0) t ↔ InducedIsBlobQuartet hN t := by
  constructor
  · rintro ⟨a, b, c, d, h, rfl, hr⟩
    have hs := (readTopology_eq_star_iff hN h (h₁ a b c d h)).mp hr
    exact ⟨h, (Bridges.isBlobQuartetOnInduced_self_iff hN h).mpr ((Bridges.inducedHasStarTopology_iff hN h).mp hs)⟩
  · rintro ⟨ht, hB⟩
    obtain ⟨u, v, w, z, rfl⟩ := exists_eq_of_card_four ht
    have hs := (Bridges.inducedHasStarTopology_iff hN ht).mpr ((Bridges.isBlobQuartetOnInduced_self_iff hN ht).mp hB)
    exact ⟨u, v, w, z, ht, rfl, (readTopology_eq_star_iff hN ht (h₁ u v w z ht)).mpr hs⟩

/-- **`CF`-detection and the rule on the `CF`s are those on the topologies**, for parameters where Corollary 1 holds: "Since the B-quartet Inference Rule does not depend on parameters". -/
theorem cfInferred_iff_topologyInferred (hN : IsBinaryNetwork N) {θ : MetricData E}
    (h₁ : ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), InducedTopologyIs hN a b c d h (readTopology (cfTriple N θ a b c d h)))
    (Q : Finset X) : CFInferred (nmscCF N θ 0) Q ↔ TopologyInferred hN Q := by
  constructor
  · intro h
    induction h with
    | detected Q hQ =>
      obtain ⟨a, b, c, d, h, rfl, hr⟩ := hQ
      exact .detected a b c d h ((readTopology_eq_star_iff hN h (h₁ a b c d h)).mp hr)
    | rule a b c d e t q h5 _ _ ht hr hq ih₁ ih₂ =>
      refine .rule a b c d e t q h5 ih₁ ih₂ ht ?_ hq
      rcases hr with ⟨s, hs, hsc, hsep⟩ | hnc
      · obtain ⟨u, v, w, z, h4, rfl⟩ := TreeMetric.exists_eq_quartetTree s
        exact Or.inl ⟨u, v, w, z, h4, (quartetTree_taxa _ _ _ _ _).symm.trans (mem_treesOn.1 hs),
          (isStrictlyCutAt_iff_inducedHasQuartetTopology hN h₁ h4).mp hsc, hsep⟩
      · exact Or.inr ((readsUnresolved_iff hN h₁).mp hnc)
  · intro h
    induction h with
    | detected a b c d h hs => exact .detected _ ⟨a, b, c, d, h, rfl, (readTopology_eq_star_iff hN h (h₁ a b c d h)).mpr hs⟩
    | rule a b c d e t q h5 _ _ ht hr hq ih₁ ih₂ =>
      refine .rule a b c d e t q h5 ih₁ ih₂ ht ?_ hq
      rcases hr with ⟨u, v, w, z, h4, rfl, htop, hsep⟩ | hB
      · exact Or.inl ⟨quartetTree u v w z h4, mem_treesOn.2 (quartetTree_taxa _ _ _ _ _), (isStrictlyCutAt_iff_inducedHasQuartetTopology hN h₁ h4).mpr htop, hsep⟩
      · exact Or.inr ((readsUnresolved_iff hN h₁).mpr hB)

/-- **`CF`-detection and part (a) of the rule on the `CF`s are those on the topologies.** -/
theorem cfInferredA_iff_topologyInferredA (hN : IsBinaryNetwork N) {θ : MetricData E}
    (h₁ : ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), InducedTopologyIs hN a b c d h (readTopology (cfTriple N θ a b c d h)))
    (Q : Finset X) : CFInferredA (nmscCF N θ 0) Q ↔ TopologyInferredA hN Q := by
  constructor
  · intro h
    induction h with
    | detected Q hQ =>
      obtain ⟨a, b, c, d, h, rfl, hr⟩ := hQ
      exact .detected a b c d h ((readTopology_eq_star_iff hN h (h₁ a b c d h)).mp hr)
    | rule a b c d e t q h5 _ _ ht hr hq ih₁ ih₂ =>
      refine .rule a b c d e t q h5 ih₁ ih₂ ht ?_ hq
      obtain ⟨s, hs, hsc, hsep⟩ := hr
      obtain ⟨u, v, w, z, h4, rfl⟩ := TreeMetric.exists_eq_quartetTree s
      exact ⟨u, v, w, z, h4, (quartetTree_taxa _ _ _ _ _).symm.trans (mem_treesOn.1 hs),
        (isStrictlyCutAt_iff_inducedHasQuartetTopology hN h₁ h4).mp hsc, hsep⟩
  · intro h
    induction h with
    | detected a b c d h hs => exact .detected _ ⟨a, b, c, d, h, rfl, (readTopology_eq_star_iff hN h (h₁ a b c d h)).mpr hs⟩
    | rule a b c d e t q h5 _ _ ht hr hq ih₁ ih₂ =>
      refine .rule a b c d e t q h5 ih₁ ih₂ ht ?_ hq
      obtain ⟨u, v, w, z, h4, rfl, htop, hsep⟩ := hr
      exact ⟨quartetTree u v w z h4, mem_treesOn.2 (quartetTree_taxa _ _ _ _ _), (isStrictlyCutAt_iff_inducedHasQuartetTopology hN h₁ h4).mpr htop, hsep⟩

/-- **Theorem 3** (`a:thm:infer`). On an `n`-taxon rooted binary phylogenetic network `𝒩⁺` with generic numerical parameters, all
B-quartets can be identified from the quartet `CF`s using `CF`-detectability (Theorem 1) and applications of the B-quartet Inference Rule
(Theorem 2). -/
theorem theorem3 (hN : IsBinaryNetwork N) :
    ForGenericParams N fun θ => ∀ Q : Finset X, Q.card = 4 →
      (CFInferred (nmscCF N θ 0) Q ↔ IsBlobQuartet N Q) := by
  refine (corollary1 hN).mono ?_
  rintro θ ⟨hθ, hnot⟩
  refine ⟨hθ, fun h₁ => hnot fun Q _ => ?_⟩
  exact (cfInferred_iff_topologyInferred hN h₁ Q).trans (theorem3_core hN)

/-- **"Only part (a) of Theorem 2 is needed to infer all B-quartets from those that are `CF`-detectable"** (`a:claim:part-a`, after Theorem 3). -/
theorem theorem3_partA (hN : IsBinaryNetwork N) :
    ForGenericParams N fun θ => ∀ Q : Finset X, Q.card = 4 →
      (CFInferredA (nmscCF N θ 0) Q ↔ IsBlobQuartet N Q) := by
  refine (corollary1 hN).mono ?_
  rintro θ ⟨hθ, hnot⟩
  refine ⟨hθ, fun h₁ => hnot fun Q _ => ?_⟩
  exact (cfInferredA_iff_topologyInferredA hN h₁ Q).trans (theorem3_core_partA hN)

end Theorem3

end AllmanEtAl2023
