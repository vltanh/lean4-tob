module

public import Gusfield2007.Decomposition
public import Gusfield2007.NetworkOps

/-!
# The Hudson-Kaplan lower bound

See the `README.md` of this directory. The proof is that of Hudson and Kaplan 1985, p. 148 and Appendix 2: at most one mutation occurs at each site, so "the only way for all four gametic types
to be in the sample is for at least one recombination event to have occurred in the history of the sample between the two sites", and "to each interval we must assign at least one recombination event".
-/

@[expose] public section

open scoped Classical

namespace HudsonKaplan1985

open Gusfield2007

variable {ι : Type*} [LinearOrder ι] [Finite ι]

/-- **The Hudson-Kaplan bound** (`ext:hudson_kaplan`): a set of pairs of incompatible sites, whose intervals don't overlap (they can share an
endpoint), has at most `R¹(M)` elements. -/
theorem card_le_R (M : Finset (ι → Bool)) (P : Finset (ι × ι)) (hP : ∀ p ∈ P, p.1 < p.2 ∧ Incompatible M p.1 p.2)
    (hd : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1) : P.card ≤ R .single M := by
  by_cases hM : M.Nonempty
  · obtain ⟨a, b, N, hc, hder, hcount⟩ := Nat.sInf_mem (recombSet_nonempty .single hM)
    change N.recombCount = R .single M at hcount
    have hc' : ∀ x : {x // N.IsRecomb x}, ∃ L : LowerSet ι, ∃ e f, N.tgt e = x.1 ∧ N.tgt f = x.1 ∧
        ∀ i, N.label x.1 i = if i ∈ L then N.label (N.src e) i else N.label (N.src f) i := fun x => by
      obtain ⟨e, f, -, he, hf, L, hL⟩ := hc x.1 x.2
      exact ⟨L, e, f, he, hf, hL⟩
    choose L e f he hf hL using hc'
    have hbreak : ∀ p : P, ∃ x, p.1.1 ∈ L x ∧ p.1.2 ∉ L x := by
      rintro ⟨⟨u, w⟩, hp⟩
      obtain ⟨huw, hinc⟩ := hP _ hp
      simp only at huw hinc ⊢
      obtain ⟨x, hx, hbr⟩ := N.exists_breaksAt_of_incompatible hder.displays hinc
      refine ⟨⟨x, hx⟩, ?_, ?_⟩
      · by_contra hu
        have hw : w ∉ L ⟨x, hx⟩ := fun hw => hu ((L ⟨x, hx⟩).lower huw.le hw)
        refine hbr (f ⟨x, hx⟩) (hf ⟨x, hx⟩) (funext ?_)
        rintro ⟨i, rfl | rfl⟩
        · simpa [hu] using hL ⟨x, hx⟩ i
        · simpa [hw] using hL ⟨x, hx⟩ i
      · intro hw
        have hu : u ∈ L ⟨x, hx⟩ := (L ⟨x, hx⟩).lower huw.le hw
        refine hbr (e ⟨x, hx⟩) (he ⟨x, hx⟩) (funext ?_)
        rintro ⟨i, rfl | rfl⟩
        · simpa [hu] using hL ⟨x, hx⟩ i
        · simpa [hw] using hL ⟨x, hx⟩ i
    choose φ hφ₁ hφ₂ using hbreak
    have hinj : Function.Injective φ := by
      rintro p q hpq
      by_contra hne
      have hne' : p.1 ≠ q.1 := fun h => hne (Subtype.ext h)
      rcases hd p.1 p.2 q.1 q.2 hne' with h | h
      · apply hφ₂ p
        rw [hpq]
        exact (L (φ q)).lower h (hφ₁ q)
      · apply hφ₂ q
        rw [← hpq]
        exact (L (φ p)).lower h (hφ₁ p)
    have := Nat.card_le_card_of_injective φ hinj
    rw [← hcount]
    rw [show Nat.card P = P.card by simp] at this
    exact this
  · have hempty : P = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp => hM ?_
      obtain ⟨r, hr, -⟩ := (hP p hp).2 true true
      exact ⟨r, hr⟩
    simp [hempty]

end HudsonKaplan1985
