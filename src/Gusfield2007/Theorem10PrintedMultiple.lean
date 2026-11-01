module

public import Gusfield2007.Components
public import Gusfield2007.OpenSearch

/-!
# Gusfield et al. 2007: Theorem 10 with `R(M + S)` read by line 385's definition, for multiple crossovers

The matrix `printedMRows` has 74 rows and 34 sites, and two components, the sites `0` to `4` and the sites `5` to `33`. With `S = printedMRoot`, one of its rows, `H(M + S) = R(M + S) = 39`, the root `printedMTightRoot` being tight, while `R_S(M) ≤ 42`, and the
sum over the components for `S` is at least `4 + 39 = 43`.

The lower bound on the second component is the verified search `LabelSearch.lt_RS_of_check2`. Its computation, `printedMSearch`, is too large for the kernel as written, and it's a hypothesis of the theorem here: everything else is proved.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

open LabelSearch

section Codes

variable {k : ℕ}

theorem mem_toFinset_map_dec {L : List ℕ} {r : Fin k → Bool} : r ∈ (L.map dec).toFinset ↔ ∃ x ∈ L, dec x = r := by
  rw [List.mem_toFinset, List.mem_map]

theorem mem_iff_exists_code {L : List ℕ} (hL : ∀ x ∈ L, x < 2 ^ k) (x : ℕ) : x ∈ L ↔ ∃ r ∈ ((L.map dec).toFinset : Finset (Fin k → Bool)), code r = x := by
  constructor
  · intro hx
    exact ⟨dec x, mem_toFinset_map_dec.2 ⟨x, hx, rfl⟩, code_dec (hL x hx)⟩
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨y, hy, rfl⟩ := mem_toFinset_map_dec.1 hr
    rwa [code_dec (hL y hy)]

theorem card_toFinset_map_dec {L : List ℕ} (hL : ∀ x ∈ L, x < 2 ^ k) (hnd : L.Nodup) : ((L.map dec).toFinset : Finset (Fin k → Bool)).card = L.length := by
  rw [List.toFinset_card_of_nodup, List.length_map]
  refine List.Nodup.map_on (fun x hx y hy hxy => ?_) hnd
  rw [← code_dec (hL x hx), ← code_dec (hL y hy), hxy]

end Codes

section Printed

/-- The codes of the rows: bit `i` is the state of the site `i`. -/
def printedMCodes : List ℕ := [0, 1, 2, 5, 10, 12, 20, 24, 28, 160, 192, 256, 384, 1184, 1600, 4288, 6176, 16384, 24672, 66720, 67232, 98368, 99488, 266432, 268480, 393248, 397504, 1064960, 1572960, 5259264, 5267456, 5783552, 6291552, 7356416, 8390144, 8390208, 16783392, 25173504, 33579104, 58752512, 67207232, 125959680, 134610976, 260570624, 270008416, 530578944, 543162464, 1073741312, 2147483136, 4294966784, 8589934080, 16106127360, 16642998272, 16911433728, 17045651456, 17112760320, 17146314752, 17163091968, 17171480576, 17175674880, 17177772032, 17178820608, 17179344896, 17179607040, 17179738112, 17179803648, 17179836416, 17179852800, 17179860992, 17179865088, 17179867136, 17179868160, 17179868672, 17179868704]

/-- Seventy-four rows on thirty-four sites: a counterexample to Theorem 10 with `R(M + S)` read by line 385's definition, for multiple crossovers. -/
def printedMRows : Finset (Fin 34 → Bool) := (printedMCodes.map dec).toFinset

/-- The ancestral sequence of the counterexample: one of the rows. -/
def printedMRoot : Fin 34 → Bool := dec 12

/-- The tight root. -/
def printedMTightRoot : Fin 34 → Bool := dec 1073741312

/-- A history for `printedMRows` from the tight root, with 39 recombinations. -/
def printedMTightSteps : List Step := [.flip 1073741312 30, .flip 2147483136 31, .flip 4294966784 32, .flip 8589934080 33, .flip 17179868672 9, .flip 17179868160 10, .flip 17179867136 11, .flip 17179865088 12, .flip 17179860992 13, .flip 17179852800 14, .flip 17179836416 15, .flip 17179803648 16, .flip 17179738112 17, .flip 17179607040 18, .flip 17179344896 19, .flip 17178820608 20, .flip 17177772032 21, .flip 17175674880 22, .flip 17171480576 23, .flip 17163091968 24, .flip 17146314752 25, .flip 17112760320 26, .flip 17045651456 27, .flip 16911433728 28, .flip 16642998272 29, .mix 1073741312 16106127360 0, .mix 1073741312 16106127360 16384, .mix 1073741312 16106127360 1064960, .mix 1073741312 16106127360 5259264, .mix 1073741312 16106127360 5267456, .mix 1073741312 16106127360 5783552, .mix 1073741312 16106127360 7356416, .mix 1073741312 16106127360 8390144, .mix 1073741312 16106127360 25173504, .mix 1073741312 16106127360 58752512, .mix 1073741312 16106127360 125959680, .mix 1073741312 16106127360 260570624, .mix 1073741312 16106127360 530578944, .flip 0 0, .flip 0 1, .flip 1 2, .flip 2 3, .mix 5 10 12, .flip 12 4, .mix 1073741312 28 20, .mix 1073741312 28 24, .flip 0 8, .flip 256 7, .flip 8390144 6, .mix 384 8390208 192, .mix 1073741312 192 1600, .mix 1073741312 192 4288, .mix 1073741312 192 98368, .mix 1073741312 192 266432, .mix 1073741312 192 268480, .mix 1073741312 192 397504, .mix 1073741312 192 67207232, .flip 17179868672 5, .mix 384 17179868704 160, .mix 1073741312 160 1184, .mix 1073741312 160 6176, .mix 192 17179868704 24672, .mix 1073741312 160 66720, .mix 1073741312 160 67232, .mix 1073741312 160 99488, .mix 1073741312 160 393248, .mix 17179836416 24672 1572960, .mix 17179836416 24672 6291552, .mix 1073741312 160 16783392, .mix 1073741312 24672 33579104, .mix 1073741312 160 134610976, .mix 1073741312 1572960 270008416, .mix 1073741312 6291552 543162464]

/-- A history for `printedMRows` from `printedMRoot`, with 42 recombinations. Its labels off the rows are `52`, `76` and `100`, the last a mix of the first two. -/
def printedMRootSteps : List Step := [.flip 12 4, .flip 28 3, .flip 28 2, .flip 20 5, .flip 12 6, .mix 52 76 100, .mix 24 100 0, .flip 0 0, .mix 12 1 5, .flip 0 1, .mix 12 2 10, .flip 0 8, .flip 256 7, .mix 52 384 160, .mix 76 384 192, .flip 160 10, .flip 192 12, .flip 0 14, .flip 1184 16, .flip 66720 9, .mix 76 67232 1600, .flip 66720 15, .mix 76 99488 98368, .flip 4288 18, .flip 266432 11, .mix 52 268480 6176, .flip 266432 17, .mix 52 397504 393248, .flip 16384 20, .flip 1064960 22, .flip 5259264 13, .mix 100 5267456 24672, .flip 5259264 19, .mix 100 5783552 1572960, .flip 5259264 21, .mix 100 7356416 6291552, .flip 1600 23, .mix 12 8390208 8390144, .flip 6176 24, .mix 8390208 16783392 25173504, .flip 24672 25, .mix 25173504 33579104 58752512, .flip 98368 26, .mix 58752512 67207232 125959680, .flip 393248 27, .mix 125959680 134610976 260570624, .flip 1572960 28, .mix 260570624 270008416 530578944, .flip 6291552 29, .mix 530578944 543162464 1073741312, .flip 1073741312 30, .flip 2147483136 31, .flip 4294966784 32, .flip 8589934080 33, .mix 12 17179868672 16106127360, .mix 12 17179868672 16642998272, .mix 12 17179868672 16911433728, .mix 12 17179868672 17045651456, .mix 12 17179868672 17112760320, .mix 12 17179868672 17146314752, .mix 12 17179868672 17163091968, .mix 12 17179868672 17171480576, .mix 12 17179868672 17175674880, .mix 12 17179868672 17177772032, .mix 12 17179868672 17178820608, .mix 12 17179868672 17179344896, .mix 12 17179868672 17179607040, .mix 12 17179868672 17179738112, .mix 12 17179868672 17179803648, .mix 12 17179868672 17179836416, .mix 12 17179868672 17179852800, .mix 12 17179868672 17179860992, .mix 12 17179868672 17179865088, .mix 12 17179868672 17179867136, .mix 12 17179868672 17179868160, .mix 52 17179868672 17179868704]

theorem printedMCodes_lt : ∀ x ∈ printedMCodes, x < 2 ^ 34 := by decide +kernel

theorem printedMCodes_nodup : printedMCodes.Nodup := by decide +kernel

theorem printedMRows_card : printedMRows.card = 74 :=
  (card_toFinset_map_dec printedMCodes_lt printedMCodes_nodup).trans (by decide +kernel)

theorem printedMRows_nonempty : printedMRows.Nonempty :=
  ⟨dec 12, mem_toFinset_map_dec.2 ⟨12, by decide +kernel, rfl⟩⟩

theorem printedMRoot_mem : printedMRoot ∈ printedMRows := mem_toFinset_map_dec.2 ⟨12, by decide +kernel, rfl⟩

theorem addRow_printedMRows : addRow printedMRows printedMRoot = printedMRows := addRow_eq_of_mem printedMRoot_mem

theorem printedMRows_noConstantColumn : NoConstantColumn printedMRows := by
  have h : ∀ i : Fin 34, ∃ x ∈ printedMCodes, ∃ y ∈ printedMCodes, (dec x : Fin 34 → Bool) i ≠ dec y i := by decide +kernel
  intro i
  obtain ⟨x, hx, y, hy, hne⟩ := h i
  exact ⟨dec x, mem_toFinset_map_dec.2 ⟨x, hx, rfl⟩, dec y, mem_toFinset_map_dec.2 ⟨y, hy, rfl⟩, hne⟩

theorem haplotypeBound_printedMRows : haplotypeBound printedMRows = 39 := by
  have h : ∀ i j : Fin 34, (∀ x ∈ printedMCodes, (dec x : Fin 34 → Bool) i = dec x j) → i = j := by decide +kernel
  have hinj : Function.Injective fun i : Fin 34 => fun r : printedMRows => (r : Fin 34 → Bool) i := by
    intro i j hij
    refine h i j fun x hx => ?_
    exact congrFun hij ⟨dec x, mem_toFinset_map_dec.2 ⟨x, hx, rfl⟩⟩
  have hcols : distinctColumns printedMRows = 34 := by
    rw [distinctColumns, Set.ncard_range_of_injective hinj]
    simp
  simp [haplotypeBound, printedMRows_card, hcols]

theorem RS_printedMRoot_le : RS .multiple printedMRoot printedMRows ≤ 42 := by
  have h := RS_le_of_run (m := 34) (s := 12) (by decide +kernel) (l := printedMRootSteps) (by decide +kernel) printedMRows_nonempty printedMRows_noConstantColumn (fun r hr => by
    obtain ⟨x, hx, rfl⟩ := mem_toFinset_map_dec.1 hr
    have hc : ∀ x ∈ printedMCodes, x = 12 ∨ ∃ t ∈ printedMRootSteps, x = t.label := by decide +kernel
    rcases hc x hx with rfl | ⟨t, ht, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨t, ht, rfl⟩)
  exact h.trans (by decide +kernel)

theorem R_printedMRows : R .multiple printedMRows = 39 := by
  have h := RS_le_of_run (m := 34) (s := 1073741312) (by decide +kernel) (l := printedMTightSteps) (by decide +kernel) printedMRows_nonempty printedMRows_noConstantColumn (fun r hr => by
    obtain ⟨x, hx, rfl⟩ := mem_toFinset_map_dec.1 hr
    have hc : ∀ x ∈ printedMCodes, x = 1073741312 ∨ ∃ t ∈ printedMTightSteps, x = t.label := by decide +kernel
    rcases hc x hx with rfl | ⟨t, ht, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨t, ht, rfl⟩)
  have hle : R .multiple printedMRows ≤ 39 := (R_le_RS .multiple _ printedMRows_nonempty).trans (h.trans (by decide +kernel))
  have hge := MyersGriffiths2003.haplotypeBound_le_R .multiple printedMRows printedMRows_nonempty
  rw [haplotypeBound_printedMRows] at hge
  omega

/-- The first component: the sites `0` to `4`. -/
def printedMC₁ : Set (Fin 34) := {i | i.val < 5}

/-- The sites of the first component. -/
def printedMSites₁ : Fin 5 → Fin 34 := fun a => ⟨a.val, by omega⟩

/-- The sites of the second component. -/
def printedMSites₂ : Fin 29 → Fin 34 := fun a => ⟨a.val + 5, by omega⟩

theorem printedMSites₁_strictMono : StrictMono printedMSites₁ := fun _ _ h => h

theorem printedMSites₂_strictMono : StrictMono printedMSites₂ := fun a b h => by
  change a.val + 5 < b.val + 5
  have : a.val < b.val := h
  omega

theorem printedMSites₁_range : Set.range printedMSites₁ = printedMC₁ := Set.ext fun i => by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hi
    exact ⟨⟨i.val, hi⟩, rfl⟩

theorem printedMSites₂_range : Set.range printedMSites₂ = printedMC₁ᶜ := Set.ext fun i => by
  constructor
  · rintro ⟨a, rfl⟩
    intro h
    have h' : a.val + 5 < 5 := h
    omega
  · intro hi
    have hi' : ¬ i.val < 5 := hi
    refine ⟨⟨i.val - 5, by omega⟩, Fin.ext ?_⟩
    change i.val - 5 + 5 = i.val
    omega

theorem dec_comp_sites₁ (x : ℕ) : (dec x : Fin 34 → Bool) ∘ printedMSites₁ = dec (x % 32) := by
  funext a
  change x.testBit a.val = (x % 2 ^ 5).testBit a.val
  rw [Nat.testBit_mod_two_pow]
  simp [a.2]

theorem dec_comp_sites₂ (x : ℕ) : (dec x : Fin 34 → Bool) ∘ printedMSites₂ = dec (x / 32) := by
  funext a
  change x.testBit (a.val + 5) = (x / 2 ^ 5).testBit a.val
  rw [Nat.testBit_div_two_pow, Nat.add_comm]

/-- The rows on the first component. -/
def printedMCodes₁ : List ℕ := [0, 1, 2, 5, 10, 12, 20, 24, 28]

/-- The rows on the second component. -/
def printedMCodes₂ : List ℕ := [0, 5, 6, 8, 12, 37, 50, 134, 193, 512, 771, 2085, 2101, 3074, 3109, 8326, 8390, 12289, 12422, 33280, 49155, 164352, 164608, 180736, 196611, 229888, 262192, 262194, 524481, 786672, 1049347, 1836016, 2100226, 3936240, 4206593, 8142832, 8437763, 16580592, 16973827, 33554416, 67108848, 134217712, 268435440, 503316480, 520093696, 528482304, 532676608, 534773760, 535822336, 536346624, 536608768, 536739840, 536805376, 536838144, 536854528, 536862720, 536866816, 536868864, 536869888, 536870400, 536870656, 536870784, 536870848, 536870880, 536870896, 536870897]

theorem image_sites₁ : (printedMRows.image fun r => r ∘ printedMSites₁) = (printedMCodes₁.map dec).toFinset := by
  have h₁ : ∀ x ∈ printedMCodes, x % 32 ∈ printedMCodes₁ := by decide +kernel
  have h₂ : ∀ y ∈ printedMCodes₁, ∃ x ∈ printedMCodes, x % 32 = y := by decide +kernel
  ext r
  rw [Finset.mem_image, mem_toFinset_map_dec]
  constructor
  · rintro ⟨_, hs, rfl⟩
    obtain ⟨x, hx, rfl⟩ := mem_toFinset_map_dec.1 hs
    exact ⟨_, h₁ x hx, (dec_comp_sites₁ x).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := h₂ y hy
    exact ⟨dec x, mem_toFinset_map_dec.2 ⟨x, hx, rfl⟩, dec_comp_sites₁ x⟩

theorem image_sites₂ : (printedMRows.image fun r => r ∘ printedMSites₂) = (printedMCodes₂.map dec).toFinset := by
  have h₁ : ∀ x ∈ printedMCodes, x / 32 ∈ printedMCodes₂ := by decide +kernel
  have h₂ : ∀ y ∈ printedMCodes₂, ∃ x ∈ printedMCodes, x / 32 = y := by decide +kernel
  ext r
  rw [Finset.mem_image, mem_toFinset_map_dec]
  constructor
  · rintro ⟨_, hs, rfl⟩
    obtain ⟨x, hx, rfl⟩ := mem_toFinset_map_dec.1 hs
    exact ⟨_, h₁ x hx, (dec_comp_sites₂ x).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := h₂ y hy
    exact ⟨dec x, mem_toFinset_map_dec.2 ⟨x, hx, rfl⟩, dec_comp_sites₂ x⟩

/-- A parent for each site, in its component. -/
def printedMPar : List ℕ := [0, 3, 0, 2, 2, 5, 5, 5, 7, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]

/-- The depth of each site, in its component. -/
def printedMDepth : List ℕ := [0, 3, 1, 2, 2, 0, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem incompatible_of_codes {i j : Fin 34} (h : ∀ a b : Bool, ∃ x ∈ printedMCodes, (dec x : Fin 34 → Bool) i = a ∧ (dec x : Fin 34 → Bool) j = b) : Incompatible printedMRows i j := fun a b => by
  obtain ⟨x, hx, h₁, h₂⟩ := h a b
  exact ⟨dec x, mem_toFinset_map_dec.2 ⟨x, hx, rfl⟩, h₁, h₂⟩

theorem printedM_reachable (i j : Fin 34) : (incompatGraph printedMRows).Reachable i j ↔ (i ∈ printedMC₁ ↔ j ∈ printedMC₁) := by
  have hstep : ∀ i : Fin 34, printedMDepth.getD i.val 0 = 0 ∨ ∃ k : Fin 34, (i.val < 5 ↔ k.val < 5) ∧ printedMDepth.getD k.val 0 < printedMDepth.getD i.val 0 ∧
      ∀ a b : Bool, ∃ x ∈ printedMCodes, (dec x : Fin 34 → Bool) i = a ∧ (dec x : Fin 34 → Bool) k = b := by decide +kernel
  have hzero : ∀ i : Fin 34, printedMDepth.getD i.val 0 = 0 → i = 0 ∨ i = 5 := by decide +kernel
  have hreach : ∀ (n : ℕ) (i : Fin 34), printedMDepth.getD i.val 0 = n → (incompatGraph printedMRows).Reachable i (if i.val < 5 then 0 else 5) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      rcases hstep i with h | ⟨k, hk, hlt, hinc⟩
      · rcases hzero i h with rfl | rfl <;> exact SimpleGraph.Reachable.refl _
      · have hadj : (incompatGraph printedMRows).Adj i k := incompatible_of_codes hinc
        have := ih _ (hi ▸ hlt) k rfl
        have hif : (if k.val < 5 then (0 : Fin 34) else 5) = if i.val < 5 then 0 else 5 := by
          by_cases hi' : i.val < 5
          · rw [ite_eq_left hi', ite_eq_left (hk.1 hi')]
          · rw [ite_eq_right hi', ite_eq_right fun h' => hi' (hk.2 h')]
        rw [hif] at this
        exact hadj.reachable.trans this
  have hcross : ∀ i k : Fin 34, i.val < 5 → ¬ k.val < 5 → ∀ x ∈ printedMCodes, (dec x : Fin 34 → Bool) i = false ∨ (dec x : Fin 34 → Bool) k = false := by decide +kernel
  refine reachable_iff_of_adj _ (fun i k hik => ?_) (a := 0) (b := 5) (fun i hi => ?_) (fun i hi => ?_) i j
  · have hno : ∀ i k : Fin 34, i.val < 5 → ¬ k.val < 5 → ¬ Incompatible printedMRows i k := by
      intro i k hi hk hinc
      obtain ⟨r, hr, h₁, h₂⟩ := hinc true true
      obtain ⟨x, hx, rfl⟩ := mem_toFinset_map_dec.1 hr
      rcases hcross i k hi hk x hx with h | h
      · rw [h] at h₁
        exact absurd h₁ (by decide)
      · rw [h] at h₂
        exact absurd h₂ (by decide)
    change i.val < 5 ↔ k.val < 5
    by_cases hi : i.val < 5
    · by_cases hk : k.val < 5
      · exact ⟨fun _ => hk, fun _ => hi⟩
      · exact absurd hik (hno i k hi hk)
    · by_cases hk : k.val < 5
      · exact absurd hik.symm (hno k i hk hi)
      · exact ⟨fun h => absurd h hi, fun h => absurd h hk⟩
  · have := hreach _ i rfl
    rwa [ite_eq_left (show i.val < 5 from hi)] at this
  · have := hreach _ i rfl
    rwa [ite_eq_right (show ¬ i.val < 5 from hi)] at this

theorem printedM_conflict_reachable (i j : Fin 34) : (conflictGraph printedMRoot printedMRows).Reachable i j ↔ (i ∈ printedMC₁ ↔ j ∈ printedMC₁) := by
  rw [conflictGraph_eq_incompatGraph_addRow, addRow_printedMRows]
  exact printedM_reachable i j

/-- `R_{S(C₁)}(M(C₁)) ≥ 4`. -/
theorem four_le_RS_printedM₁ : 4 ≤ RS .multiple (printedMC₁.domRestrict printedMRoot) (restrictRows printedMC₁ printedMRows) := by
  rw [RS_restrictRows printedMSites₁ printedMSites₁_strictMono printedMSites₁_range, image_sites₁, printedMRoot, dec_comp_sites₁]
  have hlt : ∀ x ∈ printedMCodes₁, x < 2 ^ 5 := by decide +kernel
  have := lt_RS_of_closed (m := 5) (S := dec (12 % 32)) (M := (printedMCodes₁.map dec).toFinset) (Mc := printedMCodes₁) (X0 := [12, 20, 24, 28]) (rest0 := [0, 1, 2, 5, 10]) (b := 3)
    (mem_toFinset_map_dec.2 ⟨12 % 32, by decide +kernel, rfl⟩) (by rw [card_toFinset_map_dec hlt (by decide +kernel)]; decide +kernel) (mem_iff_exists_code hlt)
    (by rw [code_dec (by decide +kernel)]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  omega

/-- The rows that the root generates on the second component. -/
def printedMX₂ : List ℕ := [0, 8, 12, 512, 33280, 164352, 164608, 180736, 229888]

/-- The rows left on the second component. -/
def printedMRest₂ : List ℕ := [5, 6, 37, 50, 134, 193, 771, 2085, 2101, 3074, 3109, 8326, 8390, 12289, 12422, 49155, 196611, 262192, 262194, 524481, 786672, 1049347, 1836016, 2100226, 3936240, 4206593, 8142832, 8437763, 16580592, 16973827, 33554416, 67108848, 134217712, 268435440, 503316480, 520093696, 528482304, 532676608, 534773760, 535822336, 536346624, 536608768, 536739840, 536805376, 536838144, 536854528, 536862720, 536866816, 536868864, 536869888, 536870400, 536870656, 536870784, 536870848, 536870880, 536870896, 536870897]


/-- The search on the second component: from the rows that the root generates, two extra labels never give all the rows. It is a computation on numbers, too large for the kernel as written, so it is a hypothesis of what follows. -/
def printedMSearch : Prop :=
  ∀ z ∈ dedupN [] (cands 29 printedMX₂), level1 70 29 printedMX₂ printedMRest₂ printedMCodes₂ z = true


/-- `R_{S(C₂)}(M(C₂)) ≥ 39`. -/
theorem le_RS_printedM₂ (hs : printedMSearch) : 39 ≤ RS .multiple (printedMC₁ᶜ.domRestrict printedMRoot) (restrictRows printedMC₁ᶜ printedMRows) := by
  rw [RS_restrictRows printedMSites₂ printedMSites₂_strictMono printedMSites₂_range, image_sites₂, printedMRoot, dec_comp_sites₂]
  have hlt : ∀ x ∈ printedMCodes₂, x < 2 ^ 29 := by decide +kernel
  have := lt_RS_of_check2 (m := 29) (S := dec (12 / 32)) (M := (printedMCodes₂.map dec).toFinset) (Mc := printedMCodes₂) (X0 := printedMX₂) (rest0 := printedMRest₂) (b := 38) (fuel := 70)
    (mem_toFinset_map_dec.2 ⟨12 / 32, by decide +kernel, rfl⟩) (by rw [card_toFinset_map_dec hlt (by decide +kernel)]; decide +kernel) (mem_iff_exists_code hlt)
    (by rw [code_dec (by decide +kernel)]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hs
  omega

/-- The sum over the components of `G_S(M)`, for the counterexample. -/
theorem le_sum_printedM (hs : printedMSearch) : 43 ≤ ∑ᶠ C : (conflictGraph printedMRoot printedMRows).ConnectedComponent,
    RS .multiple (C.supp.domRestrict printedMRoot) (restrictRows C.supp printedMRows) := by
  have e := finsum_connectedComponent_eq_add printedM_conflict_reachable (a := 0) (b := 5) (show (0 : Fin 34).val < 5 by decide) (show ¬ (5 : Fin 34).val < 5 by decide)
    fun C => RS .multiple (C.domRestrict printedMRoot) (restrictRows C printedMRows)
  rw [e]
  have h₁ := four_le_RS_printedM₁
  have h₂ := le_RS_printedM₂ hs
  omega

/-- **Theorem 10 with `R(M + S)` read by line 385's definition, for multiple crossovers: false, given one computation** (`g:thm10_printed_multiple_search`). "If `H(M + S) = R(M + S)` then `M` is S-min decomposable" (line 568), with that reading, fails on `printedMRows`, with `S = printedMRoot`, a row, and with the columns of `M + S` distinct: `H(M + S) = R(M + S) = 39`,
while `R_S(M) ≤ 42` and the two components of `G_S(M)` need at least `4` and `39` recombination nodes for their sequences at `S`. This is a counterexample to that literal reading only. The paper uses the symbol at lines 525 and 560 for a network with ancestral sequence `S`, which suggests a slip for `R_S(M)`, and with the rooted count the statement is `theorem10`, which is what the proof of the paper is about. The hypothesis `printedMSearch` is the one fact here that isn't proved: the kernel hasn't completed this computation. -/
theorem theorem10Printed_multiple_false_of_search (hs : printedMSearch) : printedMRows.Nonempty ∧ NoConstantColumn printedMRows ∧
    haplotypeBound (addRow printedMRows printedMRoot) = R .multiple (addRow printedMRows printedMRoot) ∧
    ¬ SMinDecomposable .multiple printedMRoot printedMRows ∧ ¬ Theorem10Printed .multiple printedMRows printedMRoot := by
  have hH : haplotypeBound (addRow printedMRows printedMRoot) = R .multiple (addRow printedMRows printedMRoot) := by
    rw [addRow_printedMRows, haplotypeBound_printedMRows, R_printedMRows]
    rfl
  have hnot : ¬ SMinDecomposable .multiple printedMRoot printedMRows := by
    intro h
    have heq := (sMinDecomposable_iff .multiple printedMRows printedMRoot printedMRows_nonempty printedMRows_noConstantColumn).1 h
    have h₁ := le_sum_printedM hs
    have h₂ := RS_printedMRoot_le
    omega
  exact ⟨printedMRows_nonempty, printedMRows_noConstantColumn, hH, hnot, fun h => hnot (h hH)⟩

end Printed

end Gusfield2007
