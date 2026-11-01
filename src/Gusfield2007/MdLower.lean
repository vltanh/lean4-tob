module

public import Gusfield2007.MdMatrix
public import Gusfield2007.Figure6
public import Gusfield2007.Figure10

/-!
# Gusfield et al. 2007, Theorem 11: `R¹(M_d) = 3d`

The paper proves `R¹(M_d) ≤ 3d` (line 656), which is all that Theorem 11 needs. Here is the lower bound, which it doesn't claim. A single crossover falls in one of two adjacent groups of sites, so that `R¹` adds up over them, and the restriction of a single crossover is a single crossover (`Gen.split_single`). So a history for `M_{d+1}` gives a history for `M_d` and one for Figure 6, and `R¹` of Figure 6 is `3` (`fig6_three_le_of_labels`).
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

section GenSingle

universe u

variable {ι : Type u} [LinearOrder ι] {κ : Type*} [LinearOrder κ]

/-- A single crossover, on a set of sites in their order, is a single crossover. -/
theorem Recombinant.comp_monotone {p p' q : ι → Bool} (h : Recombinant .single p p' q) {f : κ → ι} (hf : Monotone f) : Recombinant .single (p ∘ f) (p' ∘ f) (q ∘ f) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨⟨f ⁻¹' L, fun a b hab ha => L.lower (hf hab) ha⟩, fun a => hL (f a)⟩

omit [LinearOrder ι] in
/-- A restricted flip of a single-crossover history. -/
theorem Gen.comp_flip_single {f : κ → ι} (hf : Function.Injective f) {S : ι → Bool} {A : Finset (ι → Bool)} {U : Set ι} {r : ℕ}
    (h : Gen .single (S ∘ f) (A.image (· ∘ f)) (f ⁻¹' U) r) {p q : ι → Bool} {i : ι} (hp : p ∈ A) (hi : i ∉ U) (hflip : IsFlip i p q) :
    Gen .single (S ∘ f) ((insert q A).image (· ∘ f)) (f ⁻¹' insert i U) r := by
  have hp' : p ∘ f ∈ A.image (· ∘ f) := Finset.mem_image_of_mem _ hp
  rw [Finset.image_insert]
  by_cases hrange : ∃ a, f a = i
  · obtain ⟨a, rfl⟩ := hrange
    have hflip' : IsFlip a (p ∘ f) (q ∘ f) :=
      ⟨hflip.1, fun b hb => hflip.2 (f b) fun hfb => hb (hf hfb)⟩
    have hU : f ⁻¹' insert (f a) U = insert a (f ⁻¹' U) := by
      ext b
      simp [hf.eq_iff]
    rw [hU]
    exact h.flip hp' hi hflip'
  · have hq : q ∘ f = p ∘ f := by
      funext a
      exact hflip.2 (f a) fun hfa => hrange ⟨a, hfa⟩
    have hU : f ⁻¹' insert i U = f ⁻¹' U := by
      ext b
      simp only [Set.mem_preimage, Set.mem_insert_iff, or_iff_right_iff_imp]
      exact fun hb => absurd ⟨b, hb⟩ hrange
    rw [hU, hq, Finset.insert_eq_of_mem hp']
    exact h

/-- **The composite bound, keeping the model.** `Gen.split`, with single crossovers on both sides: `R¹(M) ≥ R¹(M(I)) + R¹(M(J))`, for `I` to the left of `J`. -/
theorem Gen.split_single {κ' : Type*} [LinearOrder κ'] {S : ι → Bool} {A : Finset (ι → Bool)} {U : Set ι} {r : ℕ} (h : Gen .single S A U r)
    {f : κ → ι} {g : κ' → ι} (hf : StrictMono f) (hg : StrictMono g) (hfg : ∀ a b, f a ≤ g b) :
    ∃ r₁ r₂, r₁ + r₂ ≤ r ∧ Gen .single (S ∘ f) (A.image (· ∘ f)) (f ⁻¹' U) r₁ ∧
      Gen .single (S ∘ g) (A.image (· ∘ g)) (g ⁻¹' U) r₂ := by
  induction h with
  | base => exact ⟨0, 0, le_rfl, by simpa using Gen.base, by simpa using Gen.base⟩
  | flip _ hp hi hflip ih =>
    obtain ⟨r₁, r₂, hle, h₁, h₂⟩ := ih
    exact ⟨r₁, r₂, hle, h₁.comp_flip_single hf.injective hp hi hflip, h₂.comp_flip_single hg.injective hp hi hflip⟩
  | @recomb A U r p p' q _ hp hp' hm ih =>
    obtain ⟨r₁, r₂, hle, h₁, h₂⟩ := ih
    have hm₁ := hm.comp_monotone hf.monotone
    have hm₂ := hm.comp_monotone hg.monotone
    obtain ⟨L, hL⟩ := hm
    by_cases hcut : ∃ a, f a ∉ L
    · -- The crossover is to the left of `g`, which copies `p'`.
      obtain ⟨a, ha⟩ := hcut
      have hq : q ∘ g = p' ∘ g := by
        funext b
        have hb : g b ∉ L := fun hb => ha (L.lower (hfg a b) hb)
        change q (g b) = p' (g b)
        simp [hL, hb]
      refine ⟨r₁ + 1, r₂, by omega, ?_, ?_⟩
      · rw [Finset.image_insert]
        exact h₁.recomb (Finset.mem_image_of_mem _ hp) (Finset.mem_image_of_mem _ hp') hm₁
      · have hmem : p' ∘ g ∈ A.image (· ∘ g) := Finset.mem_image_of_mem _ hp'
        rw [Finset.image_insert, hq, Finset.insert_eq_of_mem hmem]
        exact h₂
    · -- All of `f` is on the left of the crossover, and copies `p`.
      push Not at hcut
      have hq : q ∘ f = p ∘ f := by
        funext a
        change q (f a) = p (f a)
        simp [hL, hcut a]
      refine ⟨r₁, r₂ + 1, by omega, ?_, ?_⟩
      · have hmem : p ∘ f ∈ A.image (· ∘ f) := Finset.mem_image_of_mem _ hp
        rw [Finset.image_insert, hq, Finset.insert_eq_of_mem hmem]
        exact h₁
      · rw [Finset.image_insert]
        exact h₂.recomb (Finset.mem_image_of_mem _ hp) (Finset.mem_image_of_mem _ hp') hm₂

end GenSingle

/-- A single-crossover history with the rows of Figure 6 among its labels has at least three recombinations: `fig6_three_le_of_labels`, on histories. -/
theorem Gen.fig6_three_le {S : Fin 6 → Bool} {A : Finset (Fin 6 → Bool)} {U : Set (Fin 6)} {r : ℕ} (hg : Gen .single S A U r) (hsub : fig6 ⊆ A) : 3 ≤ r := by
  obtain ⟨r₁, r₂, hle, h₁, h₂⟩ := hg.split fig6Left_strictMono fig6Right_strictMono fig6Left_le_right
  have hl := h₁.lt_of_check (M := fig6.image fun r => r ∘ fig6Left) (image_subset_image_of_inst _ _ _ hsub) fig6LeftCodes_codesOf fig6Left_check
  have hr := h₂.lt_of_check (M := fig6.image fun r => r ∘ fig6Right) (image_subset_image_of_inst _ _ _ hsub) fig6RightCodes_codesOf fig6Right_check
  omega

/-- The sites of the first `d` copies in `M_{d+1}`. -/
def MdInit (d : ℕ) : Fin (6 * d) → Fin (6 * (d + 1)) := Fin.castLE (by omega)

/-- The sites of the last copy in `M_{d+1}`. -/
def MdLast (d : ℕ) : Fin 6 → Fin (6 * (d + 1)) := fun j => ⟨6 * d + j.val, by omega⟩

theorem MdInit_strictMono (d : ℕ) : StrictMono (MdInit d) := Fin.strictMono_castLE _

theorem MdLast_strictMono (d : ℕ) : StrictMono (MdLast d) := fun a b h => by
  have : a.val < b.val := h
  change 6 * d + a.val < 6 * d + b.val
  omega

theorem MdInit_le_last (d : ℕ) (a : Fin (6 * d)) (b : Fin 6) : MdInit d a ≤ MdLast d b := by
  have := a.2
  change a.val ≤ 6 * d + b.val
  omega

theorem mod6_MdInit (d : ℕ) (a : Fin (6 * d)) : mod6 (MdInit d a) = mod6 a := rfl

theorem mod6_MdLast (d : ℕ) (b : Fin 6) : mod6 (MdLast d b) = b := by
  refine Fin.ext ?_
  change (6 * d + b.val) % 6 = b.val
  have := b.2
  omega

/-- **A single-crossover history whose labels contain `M_d` has at least `3d` recombinations.** -/
theorem Gen.three_mul_le : ∀ (d : ℕ) {S : Fin (6 * d) → Bool} {A : Finset (Fin (6 * d) → Bool)} {U : Set (Fin (6 * d))} {r : ℕ}, Gen .single S A U r → Md d ⊆ A → 3 * d ≤ r := by
  intro d
  induction d with
  | zero => intro _ _ _ _ _ _; simp
  | succ d ih =>
    intro S A U r hg hsub
    obtain ⟨r₁, r₂, hle, h₁, h₂⟩ := hg.split_single (MdInit_strictMono d) (MdLast_strictMono d) (MdInit_le_last d)
    have hrow : ∀ t : Fin 6, (fun j : Fin (6 * (d + 1)) => fig6Entry t (mod6 j)) ∈ A := fun t => hsub (mem_Md.2 ⟨t, rfl⟩)
    have h₃ := ih h₁ (fun r hr => by
      obtain ⟨t, rfl⟩ := mem_Md.1 hr
      exact (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) _ _ _).2 ⟨_, hrow t, rfl⟩)
    have h₄ := h₂.fig6_three_le (fun r hr => by
      unfold fig6 at hr
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hr
      refine (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) _ _ _).2 ⟨_, hrow t, ?_⟩
      funext b
      change fig6Entry t (mod6 (MdLast d b)) = _
      rw [mod6_MdLast]
      rfl)
    omega

/-- A network with the rows of `M_d` among its labels, in the single-crossover model, has at least `3d` recombination nodes. -/
theorem three_mul_le_recombCount {V E : Type*} [Finite V] {d : ℕ} (N : Network (Fin (6 * d)) V E) (hc : N.Obeys .single) (hl : ∀ r ∈ Md d, ∃ v, N.label v = r) :
    3 * d ≤ N.recombCount := by
  obtain ⟨A, U, hg, hlab⟩ := N.exists_gen hc
  exact Gen.three_mul_le d hg fun r hr => by
    obtain ⟨v, rfl⟩ := hl r hr
    exact hlab v

/-- `R¹(M_d) ≥ 3d`. The paper doesn't claim it. -/
theorem three_mul_le_R_Md (d : ℕ) : 3 * d ≤ R .single (Md d) := by
  obtain ⟨a, b, N, h₁, h₂, h₃⟩ := Nat.sInf_mem (recombSet_nonempty .single (Md_nonempty (d := d)))
  rw [R, ← h₃]
  exact three_mul_le_recombCount N h₁ fun r hr => by
    obtain ⟨v, -, hv⟩ := h₂.surjOn hr
    exact ⟨v, hv⟩

/-- **`R¹(M_d) = 3d`** (`g:Md_R_eq`). "`L(P_d) = 3d ≥ R¹(M_d)`" (line 656) is the upper bound, which is what Theorem 11 needs. The paper doesn't claim the lower bound. -/
theorem Md_R_eq (d : ℕ) : R .single (Md d) = 3 * d :=
  le_antisymm (Md_R_le d) (three_mul_le_R_Md d)

/-- A network for `M_2` with root `000000000000` and six single crossovers, at the points where the trees of Figure 10 change. It isn't in the paper. The kernel checks it below. -/
def md2RootSpec : NetSpec (6 * 2) 23 28 :=
  ⟨[0, 0, 1, 2, 3, 4, 3, 4, 8, 7, 10, 9, 7, 9, 11, 12, 11, 13, 12, 13, 14, 15, 15, 16, 14, 20, 17, 20],
   [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 13, 14, 15, 16, 16, 17, 17, 18, 19, 20, 20, 21, 21, 22, 22],
   [15, 14, 2, 3, 10, 8, 7, 9, 0, 1, 6, 11],
   [0, 256, 512, 260, 520, 260, 520, 1284, 584, 616, 1412, 1428, 2664, 1128, 1430, 2665, 1172, 2152, 1430, 2665, 1169, 1170, 2145]⟩

theorem md2RootSpec_valid : md2RootSpec.Valid := by decide +kernel

theorem md2RootSpec_derives : md2RootSpec.DerivesCheck (Md 2) := by
  have h₁ : ∀ v, (∀ e, md2RootSpec.src e ≠ v) → ∃ t : Fin 6, ∀ j : Fin (6 * 2), md2RootSpec.label v j = fig6Entry t (mod6 j) := by decide +kernel
  have h₂ : ∀ u v, (∀ e, md2RootSpec.src e ≠ u) → (∀ e, md2RootSpec.src e ≠ v) → (∀ j : Fin (6 * 2), md2RootSpec.label u j = md2RootSpec.label v j) → u = v := by decide +kernel
  have h₃ : ∀ t : Fin 6, ∃ v, (∀ e, md2RootSpec.src e ≠ v) ∧ ∀ j : Fin (6 * 2), md2RootSpec.label v j = fig6Entry t (mod6 j) := by decide +kernel
  refine ⟨fun v hv => ?_, fun u v hu hv huv => h₂ u v hu hv (congrFun huv), fun r hr => ?_⟩
  · obtain ⟨t, ht⟩ := h₁ v hv
    exact mem_Md.2 ⟨t, funext ht⟩
  · obtain ⟨t, rfl⟩ := mem_Md.1 hr
    obtain ⟨v, hv, hl⟩ := h₃ t
    exact ⟨v, hv, funext hl⟩

theorem md2RootSpec_single : md2RootSpec.SingleCheck := by decide +kernel

theorem md2RootSpec_recombs : md2RootSpec.recombs = 6 := by decide +kernel

theorem md2RootSpec_root : md2RootSpec.label 0 = fun _ => false := by decide +kernel

/-- **`R¹_0(M_2) = 6`** (`g:Md2_RS`). With the ancestral sequence `0`, two copies of Figure 6 need six recombination nodes. `≥` is `Md_R_eq`, and `≤` is `md2RootSpec`, a network that the paper doesn't give. The paper doesn't state this number. -/
theorem Md2_RS_eq : RS .single (fun _ => false) (Md 2) = 6 := by
  have h₁ := NetSpec.RS_le md2RootSpec_valid md2RootSpec_derives (NetSpec.obeys_single_toNetwork _ md2RootSpec_single) md2RootSpec_root
  rw [md2RootSpec_recombs] at h₁
  have h₂ := R_le_RS .single (fun _ => false) (Md_nonempty (d := 2))
  rw [Md_R_eq] at h₂
  omega

end Gusfield2007
