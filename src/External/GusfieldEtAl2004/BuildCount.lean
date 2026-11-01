module

public import External.GusfieldEtAl2004.Build

/-!
# The count of the computed reduced galled tree (Gusfield, Eddhu, Langley 2004)

See the `README.md` of this directory. `galledBuildOps` is `galledBuild` with its operations counted, as `galledDecide` counts its own: it returns the same value (`galledBuildOps_fst`), and it counts at most `233 (n + m + 1)⁶` operations (`galledBuildOps_le`).

An operation is a read of an entry, a comparison of two states or two labels, or a write of a label. No machine model is used. The structure of a list isn't counted, and neither is the arithmetic on a key apart from its comparison. Each function below charges all its tests, with no early exit, so that the count doesn't depend on the answers. Comparing two rows counts `m` operations, and a test of a cluster `2 m`, since it also compares a label at each site. A `dedup` of `k` things counts `k²` comparisons.

The labels `f` are those that the decision computes and counts. The bound is in `n` and `m`, and not the source's `O(nm + n³)`: the function compares all the pairs of rows and all the candidate parents of each node, so `m ≤ 2n`, which the source cites from Wang et al. 2001, isn't needed here and isn't proved.
-/

@[expose] public section

namespace GusfieldEtAl2004.Algorithm

variable {m : ℕ}

section Ops

variable (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (ar : Fin m → Arr m)

/-- Whether a row is below a node: at each site, a comparison of labels and one of states. -/
def clOps (u : GNode m) (r : Row m) : Bool × ℕ := (u.cl S f r, 2 * m)

/-- The rank of a node: the labels of all the sites are compared, for `isNT`. -/
def rankOps (u : GNode m) : ℕ × ℕ := (u.rank f, m)

/-- The test `Up`, with its count. -/
def upOps (u v : GNode m) : Bool × ℕ :=
  let below := allOps M fun r => (!(clOps S f v r).1 || (clOps S f u r).1, (clOps S f v r).2 + (clOps S f u r).2)
  let above := allOps M fun r => (!(clOps S f u r).1 || (clOps S f v r).1, (clOps S f u r).2 + (clOps S f v r).2)
  (decide (u ≠ v) && below.1 && (!above.1 || decide ((rankOps f u).1 < (rankOps f v).1) || (decide ((rankOps f u).1 = (rankOps f v).1) && decide (u.idx < v.idx))),
    2 * m + below.2 + above.2 + (rankOps f u).2 + (rankOps f v).2)

/-- The number `key`, with its count. -/
def keyOps (u : GNode m) : ℕ × ℕ :=
  let below := filterOps M (clOps S f u)
  ((M.length - below.1.length) * (6 * (m + 1)) + (rankOps f u).1 * (m + 1) + u.idx, below.2 + (rankOps f u).2)

/-- The sequences of a component: a `dedup` of `n` rows, and a comparison of each with the ancestral sequence. -/
def rowsOfOps (c : Fin m) : List (Row m) × ℕ := (rowsOf S M f c, M.length * (M.length * (2 * m)) + M.length * (2 * m))

/-- The candidate parents, with their count. -/
def candsOps : List (GNode m) × ℕ :=
  let nt := filterOps (reps f) fun c => (isNT f c, m)
  (.root :: (reps f).map .top ++ nt.1.flatMap (fun c => (rowsOfOps S M f c).1.map (.part c)), m * m + nt.2 + (nt.1.map fun c => (rowsOfOps S M f c).2).sum)

/-- The parent by clusters: the tests `Up` on the candidates, and then `argmax`, which evaluates two keys and compares them at each step. -/
def treeParOps (v : GNode m) : Option (GNode m) × ℕ :=
  let above := filterOps (candsOps S M f).1 fun u => upOps S M f u v
  (above.1.argmax (fun u => (keyOps S M f u).1), (candsOps S M f).2 + above.2 + above.1.length * (2 * (M.length * (2 * m) + m) + 1))

/-- The end of a chain: `argmax` of `card1`, which reads a row. -/
def endNodeOps (c : Fin m) (Y : List (Row m)) : GNode m × ℕ := (endNode S c Y, Y.length * (2 * m + 1))

/-- The node before a row on a chain. -/
def predNodeOps (c : Fin m) (Y : List (Row m)) (σ : Row m) : GNode m × ℕ :=
  let low := filterOps Y fun y => (decide (card1 S y < card1 S σ), 2 * m)
  ((endNodeOps S c low.1).1, low.2 + (endNodeOps S c low.1).2)

/-- The parent of a node, with its count. -/
def parOps : GNode m → Option (GNode m) × ℕ
  | .root => (none, 0)
  | .part c σ =>
    if σ = (ar c).1 then (some (endNodeOps S c (ar c).2.1).1, m + (endNodeOps S c (ar c).2.1).2)
    else if σ ∈ (ar c).2.1 then (some (predNodeOps S c (ar c).2.1 σ).1, m + (ar c).2.1.length * m + (predNodeOps S c (ar c).2.1 σ).2)
    else (some (predNodeOps S c (ar c).2.2 σ).1, m + (ar c).2.1.length * m + (predNodeOps S c (ar c).2.2 σ).2)
  | .top c => treeParOps S M f (.top c)
  | .leaf r => treeParOps S M f (.leaf r)

/-- The other parent of a node, with its count. -/
def par₂Ops : GNode m → Option (GNode m) × ℕ
  | .part c σ => if σ = (ar c).1 then (some (endNodeOps S c (ar c).2.2).1, m + (endNodeOps S c (ar c).2.2).2) else (none, m)
  | .root => (none, 0)
  | .top _ => (none, 0)
  | .leaf _ => (none, 0)

/-- The label of a node at a site. All the branches of `label` are charged: `isNT`, the comparisons of labels and the read of the entry, the search through the sequences of the component, and the test of the top. -/
def labelOps (v : GNode m) (i : Fin m) : Bool × ℕ :=
  (label S M f v i, m + 3 + (rowsOfOps S M f (f i)).2 + ((rowsOfOps S M f (f i)).1.map fun τ => (upOps S M f (.part (f i) τ) v).2).sum + (upOps S M f (.top (f i)) v).2)

/-- The arrangement of a component: the tests of all the rows, and then the chains and the recombination point of the accepted row, which are parts of its test, so at most its cost again. -/
def arrOps (c : Fin m) : Arr m × ℕ :=
  let rows := rowsOfOps S M f c
  (arrOf S M f c, m + rows.2 + (rows.1.map fun s => (candidate S (sitesOf f c) rows.1 s).2).sum +
    (match rows.1.find? (fun s => (candidate S (sitesOf f c) rows.1 s).1) with
      | none => 0
      | some s => (candidate S (sitesOf f c) rows.1 s).2))

/-- The node below the arc of a site: `isNT`, a read of the site in each row of the chains, and `argmin` of `card1`. -/
def siteNodeOps (i : Fin m) : GNode m × ℕ :=
  (siteNode S f ar i, m + ((ar (f i)).2.1 ++ (ar (f i)).2.2).length + ((ar (f i)).2.1 ++ (ar (f i)).2.2).length * (2 * m + 1))

/-- The table, with its count. -/
def gTableOps : List (GNode m × Option (GNode m) × Option (GNode m) × List Bool) × ℕ :=
  (((candsOps S M f).1 ++ M.map GNode.leaf).map (fun v => (v, (parOps S M f ar v).1, (par₂Ops S ar v).1, List.ofFn fun i => (labelOps S M f v i).1)),
    (candsOps S M f).2 + (((candsOps S M f).1 ++ M.map GNode.leaf).map fun v => (parOps S M f ar v).2 + (par₂Ops S ar v).2 + ((List.finRange m).map fun i => (labelOps S M f v i).2).sum).sum)

end Ops

/-- `galledBuild`, with its operations counted: the decision, the arrangements, the table, and the nodes of the sites. -/
def galledBuildOps (S : Row m) (M : List (Row m)) : Option (GalledOut m) × ℕ :=
  if (galledDecide S M).1 then
    let f := labOf (edgesOps S M).1
    let t := List.ofFn fun c => (arrOps S M f c).1
    let ar : Fin m → Arr m := fun c => t.getD c.val (S, [], [])
    (some ((gTableOps S M f ar).1, List.ofFn fun i => (siteNodeOps S f ar i).1),
      (galledDecide S M).2 + ((List.finRange m).map fun c => (arrOps S M f c).2).sum + (gTableOps S M f ar).2 + ((List.finRange m).map fun i => (siteNodeOps S f ar i).2).sum)
  else (none, (galledDecide S M).2)

section Same

variable {S : Row m} {M : List (Row m)} {f : Fin m → Fin m} {ar : Fin m → Arr m}

theorem upOps_fst (u v : GNode m) : (upOps S M f u v).1 = Up S M f u v := rfl

theorem keyOps_fst (u : GNode m) : (keyOps S M f u).1 = key S M f u := rfl

theorem candsOps_fst : (candsOps S M f).1 = cands S M f := rfl

theorem treeParOps_fst (v : GNode m) : (treeParOps S M f v).1 = treePar S M f v := rfl

theorem parOps_fst (v : GNode m) : (parOps S M f ar v).1 = par S M f ar v := by
  cases v with
  | root => rfl
  | top c => rfl
  | part c σ =>
    simp only [parOps, par]
    split_ifs <;> rfl
  | leaf r => rfl

theorem par₂Ops_fst (v : GNode m) : (par₂Ops S ar v).1 = par₂ S ar v := by
  cases v with
  | root => rfl
  | top c => rfl
  | part c σ =>
    simp only [par₂Ops, par₂]
    split_ifs <;> rfl
  | leaf r => rfl

theorem gTableOps_fst : (gTableOps S M f ar).1 = gTable S M f ar := by
  simp only [gTableOps, gTable, candsOps_fst, parOps_fst, par₂Ops_fst]
  rfl

/-- The function with its count returns the value of `galledBuild`. -/
theorem galledBuildOps_fst : (galledBuildOps S M).1 = galledBuild S M := by
  unfold galledBuildOps galledBuild
  split_ifs
  · simp only [gTableOps_fst]
    rfl
  · rfl

end Same

section Bounds

variable {S : Row m} {M : List (Row m)} {f : Fin m → Fin m} {ar : Fin m → Arr m} {X : ℕ}

theorem powers_le (h : 1 ≤ X) : X ≤ X ^ 2 ∧ X ^ 2 ≤ X ^ 3 ∧ X ^ 3 ≤ X ^ 4 ∧ X ^ 4 ≤ X ^ 5 ∧ X ^ 5 ≤ X ^ 6 := by
  refine ⟨?_, Nat.pow_le_pow_right h (by omega), Nat.pow_le_pow_right h (by omega), Nat.pow_le_pow_right h (by omega), Nat.pow_le_pow_right h (by omega)⟩
  simpa using Nat.pow_le_pow_right h (show 1 ≤ 2 by omega)

theorem reps_length_le (f : Fin m → Fin m) : (reps f).length ≤ m := by
  have h := List.Sublist.length_le (List.dedup_sublist ((List.finRange m).map f))
  rw [List.length_map, List.length_finRange] at h
  exact h

theorem rowsOf_length_le (c : Fin m) : (rowsOf S M f c).length ≤ M.length := by
  have h₁ : (rowsOf S M f c).length ≤ ((M.map (mkRow S f c)).dedup).length := List.length_filter_le _ _
  have h₂ := List.Sublist.length_le (List.dedup_sublist (M.map (mkRow S f c)))
  simp only [List.length_map] at h₂
  omega

theorem cands_length_le : (cands S M f).length ≤ 1 + m + m * M.length := by
  have hflat : (((reps f).filter (isNT f)).flatMap fun c => (rowsOf S M f c).map (GNode.part c)).length ≤ ((reps f).filter (isNT f)).length * M.length := by
    rw [List.length_flatMap]
    refine sum_map_le ?_
    intro c _
    simpa using rowsOf_length_le c
  have hfl : ((reps f).filter (isNT f)).length ≤ m := (List.length_filter_le _ _).trans (reps_length_le f)
  have hmul : ((reps f).filter (isNT f)).length * M.length ≤ m * M.length := Nat.mul_le_mul_right _ hfl
  have hreps := reps_length_le f
  simp only [cands, List.length_cons, List.length_append, List.length_map]
  omega

theorem arrOf_chains_le (c : Fin m) : (arrOf S M f c).2.1.length ≤ M.length ∧ (arrOf S M f c).2.2.length ≤ M.length := by
  have hr := rowsOf_length_le (S := S) (M := M) (f := f) c
  unfold arrOf
  split
  · simp
  · split
    · simp
    · rename_i seed tl hrest
      have hlen : (seed :: tl).length ≤ M.length := by
        rw [← hrest]
        exact filterOps_length_le.trans hr
      split
      · exact ⟨filterOps_length_le.trans hlen, filterOps_length_le.trans hlen⟩
      · exact ⟨filterOps_length_le.trans hlen, filterOps_length_le.trans hlen⟩

theorem upOps_le (hX : M.length + m + 1 = X) (u v : GNode m) : (upOps S M f u v).2 ≤ 12 * X ^ 2 := by
  obtain ⟨p, -⟩ := powers_le (show 1 ≤ X by omega)
  have hb : ∀ a b : GNode m, (allOps M fun r => (!(clOps S f a r).1 || (clOps S f b r).1, (clOps S f a r).2 + (clOps S f b r).2)).2 ≤ M.length * (4 * m) := fun a b =>
    allOps_le fun _ _ => by
      simp only [clOps]
      omega
  have hnm : M.length * (4 * m) ≤ 4 * X ^ 2 := by
    calc M.length * (4 * m) ≤ X * (4 * X) := Nat.mul_le_mul (by omega) (by omega)
      _ = 4 * X ^ 2 := by ring
  have h₁ := hb v u
  have h₂ := hb u v
  simp only [upOps, rankOps]
  omega

/-- The count in `treeParOps` is that of `key`. -/
theorem keyOps_snd_le (u : GNode m) : (keyOps S M f u).2 ≤ M.length * (2 * m) + m := by
  have h : (filterOps M (clOps S f u)).2 ≤ M.length * (2 * m) := filterOps_le fun _ _ => le_rfl
  simpa only [keyOps, rankOps, add_le_add_iff_right] using h

theorem rowsOfOps_le (hX : M.length + m + 1 = X) (c : Fin m) : (rowsOfOps S M f c).2 ≤ 4 * X ^ 3 := by
  obtain ⟨p, q, -⟩ := powers_le (show 1 ≤ X by omega)
  have h₁ : M.length * (M.length * (2 * m)) ≤ 2 * X ^ 3 := by
    calc M.length * (M.length * (2 * m)) ≤ X * (X * (2 * X)) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
      _ = 2 * X ^ 3 := by ring
  have h₂ : M.length * (2 * m) ≤ 2 * X ^ 2 := by
    calc M.length * (2 * m) ≤ X * (2 * X) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * X ^ 2 := by ring
  simp only [rowsOfOps]
  omega

theorem candsOps_le (hX : M.length + m + 1 = X) : (candsOps S M f).2 ≤ 6 * X ^ 4 := by
  obtain ⟨p, q, r, -⟩ := powers_le (show 1 ≤ X by omega)
  have hm : m ≤ X := by omega
  have hmm : m * m ≤ X ^ 2 := by
    calc m * m ≤ X * X := Nat.mul_le_mul hm hm
      _ = X ^ 2 := by ring
  have hnt : (filterOps (reps f) fun c => (isNT f c, m)).2 ≤ X ^ 2 := by
    have h : (filterOps (reps f) fun c => (isNT f c, m)).2 ≤ (reps f).length * m := filterOps_le fun _ _ => le_rfl
    exact h.trans ((Nat.mul_le_mul_right _ (reps_length_le f)).trans hmm)
  have hsum : (((filterOps (reps f) fun c => (isNT f c, m)).1).map fun c => (rowsOfOps S M f c).2).sum ≤ 4 * X ^ 4 := by
    refine (sum_map_le fun c _ => rowsOfOps_le hX c).trans ?_
    calc _ ≤ X * (4 * X ^ 3) := Nat.mul_le_mul_right _ ((filterOps_length_le.trans (reps_length_le f)).trans hm)
      _ = 4 * X ^ 4 := by ring
  simp only [candsOps]
  omega

theorem cands_length_le_sq (hX : M.length + m + 1 = X) : (cands S M f).length ≤ X ^ 2 := by
  have h := cands_length_le (S := S) (M := M) (f := f)
  subst hX
  nlinarith [Nat.zero_le M.length, Nat.zero_le m]

theorem treeParOps_le (hX : M.length + m + 1 = X) (v : GNode m) : (treeParOps S M f v).2 ≤ 25 * X ^ 4 := by
  obtain ⟨p, q, r, -⟩ := powers_le (show 1 ≤ X by omega)
  have hL : (candsOps S M f).1.length ≤ X ^ 2 := cands_length_le_sq hX
  have hab : (filterOps (candsOps S M f).1 fun u => upOps S M f u v).2 ≤ 12 * X ^ 4 := by
    refine (filterOps_le fun u _ => upOps_le hX u v).trans ?_
    calc _ ≤ X ^ 2 * (12 * X ^ 2) := Nat.mul_le_mul_right _ hL
      _ = 12 * X ^ 4 := by ring
  have hk : 2 * (M.length * (2 * m) + m) + 1 ≤ 7 * X ^ 2 := by
    have : M.length * (2 * m) ≤ 2 * X ^ 2 := by
      calc M.length * (2 * m) ≤ X * (2 * X) := Nat.mul_le_mul (by omega) (by omega)
        _ = 2 * X ^ 2 := by ring
    omega
  have hkey : (filterOps (candsOps S M f).1 fun u => upOps S M f u v).1.length * (2 * (M.length * (2 * m) + m) + 1) ≤ 7 * X ^ 4 := by
    calc _ ≤ X ^ 2 * (7 * X ^ 2) := Nat.mul_le_mul (filterOps_length_le.trans hL) hk
      _ = 7 * X ^ 4 := by ring
  have hc := candsOps_le (S := S) (M := M) (f := f) hX
  simp only [treeParOps]
  omega

theorem endNodeOps_le (hX : M.length + m + 1 = X) (c : Fin m) {Y : List (Row m)} (hY : Y.length ≤ M.length) : (endNodeOps S c Y).2 ≤ 2 * X ^ 2 := by
  simp only [endNodeOps]
  calc _ ≤ X * (2 * X) := Nat.mul_le_mul (by omega) (by omega)
    _ = 2 * X ^ 2 := by ring

theorem predNodeOps_le (hX : M.length + m + 1 = X) (c : Fin m) {Y : List (Row m)} (hY : Y.length ≤ M.length) (σ : Row m) : (predNodeOps S c Y σ).2 ≤ 4 * X ^ 2 := by
  have h₁ : (filterOps Y fun y => (decide (card1 S y < card1 S σ), 2 * m)).2 ≤ 2 * X ^ 2 := by
    refine (filterOps_le (c := 2 * m) fun _ _ => le_rfl).trans ?_
    calc _ ≤ X * (2 * X) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * X ^ 2 := by ring
  have h₂ := endNodeOps_le (S := S) hX c (filterOps_length_le (p := fun y => (decide (card1 S y < card1 S σ), 2 * m)) |>.trans hY)
  simp only [predNodeOps]
  omega

theorem parOps_le (hX : M.length + m + 1 = X) (har : ∀ c, (ar c).2.1.length ≤ M.length ∧ (ar c).2.2.length ≤ M.length) (v : GNode m) : (parOps S M f ar v).2 ≤ 25 * X ^ 4 := by
  obtain ⟨p, q, r, -⟩ := powers_le (show 1 ≤ X by omega)
  cases v with
  | root => simp [parOps]
  | top c => exact treeParOps_le hX _
  | leaf r => exact treeParOps_le hX _
  | part c σ =>
    have h₀ : (ar c).2.1.length * m ≤ X ^ 2 := by
      calc _ ≤ X * X := Nat.mul_le_mul (by have := (har c).1; omega) (by omega)
        _ = X ^ 2 := by ring
    have h₁ := endNodeOps_le (S := S) hX c (har c).1
    have h₂ := predNodeOps_le (S := S) hX c (har c).1 σ
    have h₃ := predNodeOps_le (S := S) hX c (har c).2 σ
    simp only [parOps]
    split_ifs <;> simp only <;> omega

theorem par₂Ops_le (hX : M.length + m + 1 = X) (har : ∀ c, (ar c).2.1.length ≤ M.length ∧ (ar c).2.2.length ≤ M.length) (v : GNode m) : (par₂Ops S ar v).2 ≤ 3 * X ^ 2 := by
  obtain ⟨p, -⟩ := powers_le (show 1 ≤ X by omega)
  cases v with
  | root => simp [par₂Ops]
  | top c => simp [par₂Ops]
  | leaf r => simp [par₂Ops]
  | part c σ =>
    have h₁ := endNodeOps_le (S := S) hX c (har c).2
    simp only [par₂Ops]
    split_ifs <;> simp only <;> omega

theorem labelOps_le (hX : M.length + m + 1 = X) (v : GNode m) (i : Fin m) : (labelOps S M f v i).2 ≤ 32 * X ^ 3 := by
  obtain ⟨p, q, -⟩ := powers_le (show 1 ≤ X by omega)
  have hi : 1 ≤ m := by
    have := i.isLt
    omega
  have h₁ := rowsOfOps_le (S := S) (M := M) (f := f) hX (f i)
  have h₂ : ((rowsOfOps S M f (f i)).1.map fun τ => (upOps S M f (.part (f i) τ) v).2).sum ≤ 12 * X ^ 3 := by
    refine (sum_map_le fun τ _ => upOps_le hX _ v).trans ?_
    calc _ ≤ X * (12 * X ^ 2) := Nat.mul_le_mul_right _ ((rowsOf_length_le (f i)).trans (by omega))
      _ = 12 * X ^ 3 := by ring
  have h₃ := upOps_le (S := S) (M := M) (f := f) hX (.top (f i)) v
  simp only [labelOps]
  omega

theorem gTableOps_le (hX : M.length + m + 1 = X) (har : ∀ c, (ar c).2.1.length ≤ M.length ∧ (ar c).2.2.length ≤ M.length) : (gTableOps S M f ar).2 ≤ 128 * X ^ 6 := by
  obtain ⟨p, q, r, s, t⟩ := powers_le (show 1 ≤ X by omega)
  have hnode : ∀ v : GNode m, (parOps S M f ar v).2 + (par₂Ops S ar v).2 + ((List.finRange m).map fun i => (labelOps S M f v i).2).sum ≤ 61 * X ^ 4 := fun v => by
    have h₁ := parOps_le (S := S) (M := M) (f := f) hX har v
    have h₂ := par₂Ops_le (S := S) (M := M) hX har v
    have h₃ : ((List.finRange m).map fun i => (labelOps S M f v i).2).sum ≤ 32 * X ^ 4 := by
      refine (sum_map_le fun i _ => labelOps_le hX v i).trans ?_
      rw [List.length_finRange]
      calc _ ≤ X * (32 * X ^ 3) := Nat.mul_le_mul_right _ (by omega)
        _ = 32 * X ^ 4 := by ring
    omega
  have hlen : ((candsOps S M f).1 ++ M.map GNode.leaf).length ≤ 2 * X ^ 2 := by
    have hL : (candsOps S M f).1.length ≤ X ^ 2 := cands_length_le_sq hX
    simp only [List.length_append, List.length_map]
    omega
  have hsum : (((candsOps S M f).1 ++ M.map GNode.leaf).map fun v => (parOps S M f ar v).2 + (par₂Ops S ar v).2 + ((List.finRange m).map fun i => (labelOps S M f v i).2).sum).sum ≤ 122 * X ^ 6 := by
    refine (sum_map_le fun v _ => hnode v).trans ?_
    calc _ ≤ (2 * X ^ 2) * (61 * X ^ 4) := Nat.mul_le_mul_right _ hlen
      _ = 122 * X ^ 6 := by ring
  have hc := candsOps_le (S := S) (M := M) (f := f) hX
  simp only [gTableOps]
  omega

theorem candidate_le_cube (hX : M.length + m + 1 = X) (S : Row m) {C : List (Fin m)} (hC : C.length ≤ m) {rows : List (Row m)} (hrows : rows.length ≤ M.length) (s : Row m) : (candidate S C rows s).2 ≤ 21 * X ^ 3 := by
  obtain ⟨p, q, -⟩ := powers_le (show 1 ≤ X by omega)
  have hn : M.length ≤ X := by omega
  have hm : m ≤ X := by omega
  have h := candidate_le S hC rows s hrows
  have a₁ : M.length * M.length * m ≤ X ^ 3 := by
    calc _ ≤ X * X * X := Nat.mul_le_mul (Nat.mul_le_mul hn hn) hm
      _ = X ^ 3 := by ring
  have a₂ : M.length * m ≤ X ^ 2 := by
    calc _ ≤ X * X := Nat.mul_le_mul hn hm
      _ = X ^ 2 := by ring
  have a₃ : (m + 1) * (2 * (m * (2 * M.length + 1))) ≤ 4 * X ^ 3 := by
    calc _ ≤ X * (2 * (X * (2 * X))) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul le_rfl (Nat.mul_le_mul hm (by omega)))
      _ = 4 * X ^ 3 := by ring
  have a₄ : m * (2 * M.length) ≤ 2 * X ^ 2 := by
    calc _ ≤ X * (2 * X) := Nat.mul_le_mul hm (by omega)
      _ = 2 * X ^ 2 := by ring
  omega

theorem arrOps_le (hX : M.length + m + 1 = X) (c : Fin m) : (arrOps S M f c).2 ≤ 47 * X ^ 4 := by
  obtain ⟨p, q, r, -⟩ := powers_le (show 1 ≤ X by omega)
  have hC : (sitesOf f c).length ≤ m := by
    have h := List.length_filter_le (fun k => decide (f k = c)) (List.finRange m)
    rwa [List.length_finRange] at h
  have hr := rowsOf_length_le (S := S) (M := M) (f := f) c
  have hc := fun s => candidate_le_cube hX S hC (rows := (rowsOfOps S M f c).1) hr s
  have h₁ := rowsOfOps_le (S := S) (M := M) (f := f) hX c
  have h₂ : ((rowsOfOps S M f c).1.map fun s => (candidate S (sitesOf f c) (rowsOfOps S M f c).1 s).2).sum ≤ 21 * X ^ 4 := by
    refine (sum_map_le fun s _ => hc s).trans ?_
    calc _ ≤ X * (21 * X ^ 3) := Nat.mul_le_mul_right _ (hr.trans (by omega))
      _ = 21 * X ^ 4 := by ring
  have h₃ : (match (rowsOfOps S M f c).1.find? (fun s => (candidate S (sitesOf f c) (rowsOfOps S M f c).1 s).1) with
      | none => 0
      | some s => (candidate S (sitesOf f c) (rowsOfOps S M f c).1 s).2) ≤ 21 * X ^ 3 := by
    split
    · omega
    · exact hc _
  simp only [arrOps]
  omega

theorem siteNodeOps_le (hX : M.length + m + 1 = X) (har : ∀ c, (ar c).2.1.length ≤ M.length ∧ (ar c).2.2.length ≤ M.length) (i : Fin m) : (siteNodeOps S f ar i).2 ≤ 7 * X ^ 2 := by
  obtain ⟨p, -⟩ := powers_le (show 1 ≤ X by omega)
  have hlen : ((ar (f i)).2.1 ++ (ar (f i)).2.2).length ≤ 2 * X := by
    have := har (f i)
    rw [List.length_append]
    omega
  have h : ((ar (f i)).2.1 ++ (ar (f i)).2.2).length * (2 * m + 1) ≤ 4 * X ^ 2 := by
    calc _ ≤ (2 * X) * (2 * X) := Nat.mul_le_mul hlen (by omega)
      _ = 4 * X ^ 2 := by ring
  simp only [siteNodeOps]
  omega

/-- **Gusfield et al. 2007, line 180, "polynomial time"** (`g:reduced_poly`), and the count of the algorithm of Sections 3 to 7 of the source: on `n` rows and `m` sites, `galledBuildOps`, which returns the value of `galledBuild` (`galledBuildOps_fst`), counts at most `233 (n + m + 1)⁶` operations, for the decision, the arrangements, the table, and the nodes of the sites.

This is a bound in `n` and `m`, and not the source's `O(nm + n³)`, so `m ≤ 2n` isn't needed and isn't proved. -/
theorem galledBuildOps_le (S : Row m) (M : List (Row m)) : (galledBuildOps S M).2 ≤ 233 * (M.length + m + 1) ^ 6 := by
  obtain ⟨X, hX⟩ : ∃ X, M.length + m + 1 = X := ⟨_, rfl⟩
  rw [hX]
  obtain ⟨p, q, r, s, t⟩ := powers_le (show 1 ≤ X by omega)
  have hd := galledDecide_ops_le S M
  rw [hX] at hd
  unfold galledBuildOps
  split_ifs
  · have hm : m ≤ X := by omega
    have har : ∀ c : Fin m, ((fun c : Fin m => (List.ofFn fun c => (arrOps S M (labOf (edgesOps S M).1) c).1).getD c.val (S, [], [])) c).2.1.length ≤ M.length ∧ ((fun c : Fin m => (List.ofFn fun c => (arrOps S M (labOf (edgesOps S M).1) c).1).getD c.val (S, [], [])) c).2.2.length ≤ M.length := fun c => by
      simpa [List.getD_eq_getElem?_getD, arrOps] using arrOf_chains_le (S := S) (M := M) (f := labOf (edgesOps S M).1) c
    have h₁ : ((List.finRange m).map fun c => (arrOps S M (labOf (edgesOps S M).1) c).2).sum ≤ 47 * X ^ 5 := by
      refine (sum_map_le fun c _ => arrOps_le hX c).trans ?_
      rw [List.length_finRange]
      calc _ ≤ X * (47 * X ^ 4) := Nat.mul_le_mul_right _ hm
        _ = 47 * X ^ 5 := by ring
    have h₂ := gTableOps_le (S := S) (M := M) (f := labOf (edgesOps S M).1) hX har
    have h₃ : ((List.finRange m).map fun i => (siteNodeOps S (labOf (edgesOps S M).1) (fun c : Fin m => (List.ofFn fun c => (arrOps S M (labOf (edgesOps S M).1) c).1).getD c.val (S, [], [])) i).2).sum ≤ 7 * X ^ 3 := by
      refine (sum_map_le fun i _ => siteNodeOps_le hX har i).trans ?_
      rw [List.length_finRange]
      calc _ ≤ X * (7 * X ^ 2) := Nat.mul_le_mul_right _ hm
        _ = 7 * X ^ 3 := by ring
    dsimp only
    omega
  · dsimp only
    omega

end Bounds

end GusfieldEtAl2004.Algorithm
