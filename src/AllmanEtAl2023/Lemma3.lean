module

public import AllmanEtAl2023.Theorem2

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Lemma 3
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023.Printed

variable {V E X : Type*} [DecidableEq X] {N : RootedNetwork V E X}

/-- The network has a cut edge separating the taxa `P` from the taxa `Q`. -/
def HasCutEdgeSeparating {V' E' X' : Type*} (M : RootedNetwork V' E' X') (P Q : Set X') : Prop :=
  ∃ (e : E') (T : Set V'), (∀ f, M.graph.Crosses f T ↔ f = e) ∧ (∀ x ∈ P, M.leaf x ∈ T) ∧ ∀ x ∈ Q, M.leaf x ∉ T

/- Inventory. Proved from `AllmanEtAl2023.lemma3` and `exists_determines_erase`, which follow the paper's proof on subgraphs, with its gaps repaired and documented; and `Bridges.induced_hasCutSplit_iff`,
`Bridges.isBlobQuartetOnInduced_iff`. -/
/-- **Lemma 3** (`a:lem:main`). Let `𝒩⁺` be a rooted binary phylogenetic network on taxa `X` for which `{a, b, c, d}` is a B-quartet,
and suppose for some `α ∈ X` the induced network `𝒩′` on `X ∖ {α}` has a cut edge in `𝒩′` separating `a, b` from `c, d`. Then
`{a, b, c, α}` is a B-quartet on the induced network `ℳ⁺` on `X ∖ {d}`.

That `α` is not one of `a, b, c, d` is what the sentence says when it speaks of them on the network on `X ∖ {α}`. -/
theorem lemma3 (hN : IsBinaryNetwork N) {a b c d α : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hαa : α ≠ a) (hαb : α ≠ b) (hαc : α ≠ c) (hαd : α ≠ d) (hB : IsBlobQuartet N {a, b, c, d})
    (hY : ({α}ᶜ : Set X).Nontrivial)
    (hcut : HasCutEdgeSeparating (induced hN ({α}ᶜ : Set X) hY) (Subtype.val ⁻¹' {a, b}) (Subtype.val ⁻¹' {c, d}))
    (hY' : ({d}ᶜ : Set X).Nontrivial) :
    IsBlobQuartetOnInduced hN ({d}ᶜ : Set X) hY' {a, b, c, α} := by
  have hP := hN.isPhylogenetic
  have : Finite X := hP.finite_taxa
  let _ : Fintype X := Fintype.ofFinite X
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  -- the cut edge of `𝒩′`, in the older form
  obtain ⟨e', T, hT, hP₁, hP₂⟩ := hcut
  have hαmem : ∀ x, x ≠ α → x ∈ ({α}ᶜ : Set X) := fun x hx => hx
  let A : Set ({α}ᶜ : Set X) := (induced hN ({α}ᶜ : Set X) hY).leaf ⁻¹' T
  have ha' : (⟨a, hαmem a hαa.symm⟩ : ({α}ᶜ : Set X)) ∈ A := hP₁ _ (by simp)
  have hb' : (⟨b, hαmem b hαb.symm⟩ : ({α}ᶜ : Set X)) ∈ A := hP₁ _ (by simp)
  have hc' : (⟨c, hαmem c hαc.symm⟩ : ({α}ᶜ : Set X)) ∉ A := hP₂ _ (by simp)
  have hd' : (⟨d, hαmem d hαd.symm⟩ : ({α}ᶜ : Set X)) ∉ A := hP₂ _ (by simp)
  have hpre : Subtype.val ⁻¹' (Subtype.val '' A) = A := Set.preimage_image_eq _ Subtype.val_injective
  have hN₁ : (({α}ᶜ : Set X) ∩ Subtype.val '' A).Nonempty := ⟨a, hαmem a hαa.symm, _, ha', rfl⟩
  have hN₂ : (({α}ᶜ : Set X) \ Subtype.val '' A).Nonempty := by
    refine ⟨c, hαmem c hαc.symm, ?_⟩
    rintro ⟨z, hz, hzc⟩
    have : z = ⟨c, hαmem c hαc.symm⟩ := Subtype.ext hzc
    exact hc' (this ▸ hz)
  have hon : N.HasCutSplitOn ({α}ᶜ : Set X) (Subtype.val '' A) :=
    (Bridges.induced_hasCutSplit_iff hN hY hN₁ hN₂).mp (by rw [hpre]; exact ⟨e', T, hT, rfl⟩)
  have hAmem : ∀ x (hx : x ≠ α), x ∈ Subtype.val '' A ↔ (⟨x, hαmem x hx⟩ : ({α}ᶜ : Set X)) ∈ A := fun x hx => by
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · exact fun hz => ⟨_, hz, rfl⟩
  obtain ⟨e₀, hsep⟩ := (hasCutSplitOn_iff_separates hP _ _).mp hon
  have hcutold : ∀ x ∈ (Finset.univ : Finset X), x ≠ α → N.IsBelow e₀ x → N.Dominates e₀ x := by
    intro x _ hx hb
    rcases hsep with ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩
    · by_cases hxA : x ∈ Subtype.val '' A
      · exact h₁ x ⟨hαmem x hx, hxA⟩
      · exact absurd hb (h₂ x ⟨hαmem x hx, hxA⟩)
    · by_cases hxA : x ∈ Subtype.val '' A
      · exact absurd hb (h₂ x ⟨hαmem x hx, hxA⟩)
      · exact h₁ x ⟨hαmem x hx, hxA⟩
  have hor : (N.IsBelow e₀ a ∧ N.IsBelow e₀ b ∧ ¬ N.IsBelow e₀ c ∧ ¬ N.IsBelow e₀ d) ∨
      (¬ N.IsBelow e₀ a ∧ ¬ N.IsBelow e₀ b ∧ N.IsBelow e₀ c ∧ N.IsBelow e₀ d) := by
    have hin : ∀ x (hx : x ≠ α), (⟨x, hαmem x hx⟩ : ({α}ᶜ : Set X)) ∈ A → x ∈ ({α}ᶜ : Set X) ∩ Subtype.val '' A :=
      fun x hx h => ⟨hαmem x hx, (hAmem x hx).mpr h⟩
    have hout : ∀ x (hx : x ≠ α), (⟨x, hαmem x hx⟩ : ({α}ᶜ : Set X)) ∉ A → x ∈ ({α}ᶜ : Set X) \ Subtype.val '' A :=
      fun x hx h => ⟨hαmem x hx, fun h' => h ((hAmem x hx).mp h')⟩
    rcases hsep with ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩
    · exact Or.inl ⟨(h₁ a (hin a hαa.symm ha')).isBelow hP, (h₁ b (hin b hαb.symm hb')).isBelow hP,
        h₂ c (hout c hαc.symm hc'), h₂ d (hout d hαd.symm hd')⟩
    · exact Or.inr ⟨h₂ a (hin a hαa.symm ha'), h₂ b (hin b hαb.symm hb'),
        (h₁ c (hout c hαc.symm hc')).isBelow hP, (h₁ d (hout d hαd.symm hd')).isBelow hP⟩
  have hB' := (Bridges.isBlobQuartet_iff_not_resolves hN h).mp hB
  have hres := AllmanEtAl2023.lemma3 hP (Y := Finset.univ) h (Finset.mem_univ a) (Finset.mem_univ b) (Finset.mem_univ c)
    (Finset.mem_univ d) (Finset.mem_univ α) hαa hαb hαc hαd hcutold hor hB'
  have h4' : ({a, b, c, α} : Finset X).card = 4 :=
    TreeMetric.card_four_of_ne hab hac hαa.symm hbc hαb.symm hαc.symm
  have hsub : (Finset.univ.erase d : Finset X) = ({d}ᶜ : Set X).toFinset := by
    ext x
    simp
  have hcoe : (((Finset.univ.erase d : Finset X)) : Set X) = ({d}ᶜ : Set X) := by
    ext x
    simp
  have hq : ({a, b, c, α} : Finset X) ⊆ Finset.univ.erase d := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Finset.mem_erase.mpr ⟨had, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨hbd, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨hcd, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨hαd, Finset.mem_univ _⟩
  obtain ⟨v, hv, hdet⟩ := (not_resolves_iff_exists_determines hP hq h4').mp hres
  rw [hcoe] at hv hdet
  have hsubset : (({a, b, c, α} : Finset X) : Set X) ⊆ ({d}ᶜ : Set X) := by
    intro x hx
    have := hq (Finset.mem_coe.mp hx)
    simpa using this
  exact (Bridges.isBlobQuartetOnInduced_iff hN _ hY' hsubset h4').mpr ⟨v, hv, hdet⟩

end AllmanEtAl2023.Printed
