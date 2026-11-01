module

public import Gusfield2007.Decomposition
public import Gusfield2007.NetworkOps

/-!
# The haplotype bound of Myers and Griffiths

See the `README.md` of this directory. The proof is that of Myers and Griffiths 2003, p. 379: each mutation or recombination event creates at most one new type, the ancestor is at
most one more, and the bound can be applied to any subset of the sites, here one per distinct column. The rooted form is the "type known" case of their (4): "we always add an all-zero type".
-/

@[expose] public section

open scoped Classical

namespace MyersGriffiths2003

open Gusfield2007

variable {ι : Type*} [LinearOrder ι] [Finite ι]

omit [LinearOrder ι] [Finite ι] in
/-- The count behind the bound: on the sites `ρ k`, the labels of `N` are at most one for the root, one for each site, and one for each recombination node. -/
theorem ncard_labels_le {V E : Type*} [Finite V] {κ : Type*} [Finite κ] (N : Network ι V E) (ρ : κ → ι) :
    (Set.range fun (v : V) (k : κ) => N.label v (ρ k)).ncard ≤ N.recombCount + Nat.card κ + 1 := by
  set B : Set V := ({x | N.IsRecomb x} ∪ Set.range fun k => N.tgt (N.site (ρ k))) ∪ {N.root} with hB
  have hsub : (Set.range fun (v : V) (k : κ) => N.label v (ρ k)) ⊆ (fun (u : V) (k : κ) => N.label u (ρ k)) '' B := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨u, hu, hul⟩ := N.exists_source (Set.range ρ) v
    refine ⟨u, ?_, funext fun k => (hul _ ⟨k, rfl⟩).symm⟩
    rcases hu with rfl | ⟨_, ⟨k, rfl⟩, rfl⟩ | ⟨hu, -⟩
    · exact Or.inr rfl
    · exact Or.inl (Or.inr ⟨k, rfl⟩)
    · exact Or.inl (Or.inl hu)
  have hB₁ : B.ncard ≤ N.recombCount + Nat.card κ + 1 := by
    have h₁ : (Set.range fun k => N.tgt (N.site (ρ k))).ncard ≤ Nat.card κ := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by rw [Set.ncard_univ])
    have h₂ := Set.ncard_union_le ({x | N.IsRecomb x} ∪ Set.range fun k => N.tgt (N.site (ρ k))) {N.root}
    have h₃ := Set.ncard_union_le {x | N.IsRecomb x} (Set.range fun k => N.tgt (N.site (ρ k)))
    have h₄ : ({N.root} : Set V).ncard = 1 := Set.ncard_singleton _
    have h₅ : {x | N.IsRecomb x}.ncard = N.recombCount := rfl
    rw [hB]
    omega
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ((Set.ncard_image_le (Set.toFinite _)).trans hB₁)

omit [LinearOrder ι] in
/-- The haplotype bound for rows that label nodes of a network: the sites are one for each distinct column. -/
theorem card_le_of_displays {V E : Type*} [Finite V] (N : Network ι V E) {L : Finset (ι → Bool)} (hL : ∀ r ∈ L, ∃ v, N.label v = r) :
    L.card ≤ N.recombCount + distinctColumns L + 1 := by
  set col : ι → L → Bool := fun i r => (r : ι → Bool) i with hcol
  set ρ : Set.range col → ι := Set.rangeSplitting col with hρ
  have hρ' : ∀ (r : L) (i : ι), (r : ι → Bool) (ρ ⟨col i, i, rfl⟩) = (r : ι → Bool) i := fun r i =>
    congrFun (Set.apply_rangeSplitting col ⟨col i, i, rfl⟩) r
  have hcard := ncard_labels_le N ρ
  have hdist : Nat.card (Set.range col) = distinctColumns L := rfl
  rw [hdist] at hcard
  refine le_trans ?_ hcard
  have hinj : Set.InjOn (fun (r : ι → Bool) (k : Set.range col) => r (ρ k)) (L : Set (ι → Bool)) := by
    intro r hr r' hr' h
    funext i
    have := congrFun h ⟨col i, i, rfl⟩
    exact (hρ' ⟨r, hr⟩ i).symm.trans (this.trans (hρ' ⟨r', hr'⟩ i))
  rw [← Set.ncard_coe_finset L, ← hinj.ncard_image]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨r, hr, rfl⟩
  obtain ⟨v, rfl⟩ := hL r hr
  exact ⟨v, rfl⟩

/-- **The haplotype bound** (`ext:haplotype_bound`): `H(M) ≤ R(M)`, and so `H(M) ≤ R¹(M)` (Gusfield et al., line 559). -/
theorem haplotypeBound_le_R (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) :
    haplotypeBound M ≤ R c M := by
  obtain ⟨a, b, N, -, hd, h⟩ := Nat.sInf_mem (recombSet_nonempty c hM)
  have := card_le_of_displays N hd.displays
  rw [h] at this
  unfold haplotypeBound R
  omega

/-- **Line 559** (`g:haplotype_rooted`). "The haplotype bound is computed on `M + S` when an ancestral sequence `S` is specified": `H(M + S) ≤ R_S(M)`, and so `H(M + S) ≤ R¹_S(M)`. It's the second case of (4) in Myers and
Griffiths 2003, p. 379. The proof of Theorem 6 needs it. -/
theorem haplotypeBound_addRow_le_RS (c : Crossover) (S : ι → Bool) (M : Finset (ι → Bool)) (hM : M.Nonempty) :
    haplotypeBound (addRow M S) ≤ RS c S M := by
  obtain ⟨a, b, N, -, hd, hS, h⟩ := Nat.sInf_mem (rootedRecombSet_nonempty c S hM)
  have := card_le_of_displays N (L := addRow M S) fun r hr => by
    rcases mem_addRow.1 hr with rfl | hr
    · exact ⟨N.root, hS⟩
    · exact hd.displays r hr
  rw [h] at this
  unfold haplotypeBound RS
  omega

omit [LinearOrder ι] in
/-- **The equality case of the haplotype bound** (`ext:haplotype_equality`) (Gusfield et al., lines 560 to 564), when the columns of `M + S` are
distinct: a network for `M` with ancestral sequence `S` and `H(M + S)` recombination nodes has every node visible. The
printed sentence has no hypothesis on the columns, and is false without it. -/
theorem allVisible_of_eq {V E : Type*} [Finite V] [Finite E] (N : Network ι V E) {M : Finset (ι → Bool)}
    {S : ι → Bool} (hd : N.Derives M) (hS : N.ancestral = S)
    (hinj : Function.Injective fun i : ι => fun r : addRow M S => (r : ι → Bool) i)
    (h : (N.recombCount : ℤ) = haplotypeBound (addRow M S)) : N.AllVisible M S := by
  have hcard := ncard_labels_le N (id : ι → ι)
  have hrange : (Set.range fun (v : V) (k : ι) => N.label v (id k)) = Set.range N.label := rfl
  rw [hrange] at hcard
  have hdist : distinctColumns (addRow M S) = Nat.card ι := by
    rw [distinctColumns, ← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
  unfold haplotypeBound at h
  rw [hdist] at h
  have hsub : ((addRow M S : Finset (ι → Bool)) : Set (ι → Bool)) ⊆ Set.range N.label := by
    intro r hr
    rcases mem_addRow.1 (Finset.mem_coe.1 hr) with rfl | hr
    · exact ⟨N.root, hS⟩
    · exact hd.displays r hr
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_coe_finset]; omega) (Set.toFinite _)
  intro v
  have : N.label v ∈ ((addRow M S : Finset (ι → Bool)) : Set (ι → Bool)) := heq ▸ ⟨v, rfl⟩
  exact Finset.mem_coe.1 this

end MyersGriffiths2003
