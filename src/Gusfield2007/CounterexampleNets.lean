module

public import Gusfield2007.FiniteNets

/-!
# Gusfield et al. 2007: the explicit networks of the counterexamples of Sections 3.7 and 4.2

Each network comes with the facts that `decide` can check: it derives its rows, obeys all the crossover models, its blobs, and that it's fully decomposed and efficient where it is. The statements are in
`Gusfield2007.Uniqueness`. Sites are numbered from 0 here, and from 1 in the paper.
-/

@[expose] public section

namespace Gusfield2007

open Network

/-! ### The recombination leaf, on `fourGametes` -/

/-- `{00, 01, 10, 11}`, with `11` a recombination leaf of `01` and `10`, and a pendant arc at each of `00`, `01`, `10`. -/
def fourNet : Network (Fin 2) (Fin 7) (Fin 7) :=
  mkNet (tbl [0, 0, 1, 2, 0, 1, 2]) (tbl [1, 2, 3, 3, 4, 5, 6]) 0 (tbl [1, 0])
    (bitsOf [[0, 0], [0, 1], [1, 0], [1, 1], [0, 0], [0, 1], [1, 0]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def fourNetAc : Fin 7 → Option (Fin 1) := colourOf [1, 1, 1, 1]
def fourNetVc : Fin 7 → Option (Fin 1) := colourOf [1, 1, 1, 1]

theorem fourNet_derives : fourNet.Derives fourGametes :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fourNet_obeys (c : Crossover) : fourNet.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem fourNet_cover : GallCover fourNet fourNetAc fourNetVc :=
  GallCover.of_decide (fun _ => 0) (fun _ => 2) (fun _ => 1) (fun _ => 3) (fun e v => decide (v = fourNet.tgt e)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem fourNet_fullyDecomposed : fourNet.IsFullyDecomposedFor (incompatGraph fourGametes) :=
  fourNet_cover.isFullyDecomposedFor (fun _ : Fin 2 => 0)
    (fun _ _ _ => rfl) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem fourNet_efficient : fourNet.IsEfficient :=
  fourNet_cover.isEfficient (by decide +kernel) (by decide +kernel)

theorem fourNet_recomb : fourNet.IsRecomb 3 := ⟨2, 3, by decide, rfl, rfl⟩

theorem fourNet_leaf : fourNet.IsLeaf 3 := by
  unfold IsLeaf
  decide +kernel

/-! ### The network of `topRows` -/

/-- The network of `topRows`: a blob on `00000, 01000, 10000, 11000` with the sites 0, 1; an arc with the site 4 from `11000` to `11001`; a blob on `11001, 11011, 11101, 11111` with the sites 2, 3; and a pendant
arc at each node of the two blobs other than `11000`. -/
def topNet : Network (Fin 5) (Fin 15) (Fin 16) :=
  mkNet (tbl [0, 0, 1, 2, 3, 4, 4, 5, 6, 0, 1, 2, 4, 5, 6, 7]) (tbl [1, 2, 3, 3, 4, 5, 6, 7, 7, 8, 9, 10, 11, 12, 13, 14]) 0 (tbl [1, 0, 6, 5, 4])
    (bitsOf [[0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1],
      [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def topNetAc : Fin 16 → Option (Fin 2) := colourOf [1, 1, 1, 1, 0, 2, 2, 2, 2]
def topNetVc : Fin 15 → Option (Fin 2) := colourOf [1, 1, 1, 1, 2, 2, 2, 2]

theorem topNet_derives : topNet.Derives topRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem topNet_obeys (c : Crossover) : topNet.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem topNet_cover : GallCover topNet topNetAc topNetVc :=
  GallCover.of_decide (tbl [0, 5]) (tbl [2, 7]) (tbl [1, 6]) (tbl [3, 8])
    (fun e v => if e = 4 then decide (4 ≤ v.val ∧ v.val ≤ 7 ∨ 11 ≤ v.val) else decide (v = topNet.tgt e))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem topNet_fullyDecomposed : topNet.IsFullyDecomposedFor (incompatGraph topRows) :=
  topNet_cover.isFullyDecomposedFor (tbl [0, 0, 1, 1, 2] : Fin 5 → Fin 3)
    (by unfold Incompatible; decide +kernel) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem topNet_efficient : topNet.IsEfficient :=
  topNet_cover.isEfficient (by decide +kernel) (by decide +kernel)

/-! ### The smaller instance -/

/-- Six rows on four sites, the smaller instance of the failure at line 342: `{0000, 0001, 0010, 0110, 1010, 1110}`. -/
def smallRows : Finset (Fin 4 → Bool) :=
  {ofBits [0, 0, 0, 0], ofBits [0, 0, 0, 1], ofBits [0, 0, 1, 0], ofBits [0, 1, 1, 0], ofBits [1, 0, 1, 0], ofBits [1, 1, 1, 0]}

/-- One blob, on `0010, 0110, 1010, 1110`, entered by an arc with the site 2 from a root of degree 3; a row at the root; a row below the root with the site 3; and a pendant arc at each node of the blob. -/
def smallNet : Network (Fin 4) (Fin 11) (Fin 11) :=
  mkNet (tbl [0, 1, 1, 2, 3, 0, 0, 1, 2, 3, 4]) (tbl [1, 2, 3, 4, 4, 5, 6, 7, 8, 9, 10]) 0 (tbl [2, 1, 0, 6])
    (bitsOf [[0, 0, 0, 0], [0, 0, 1, 0], [0, 1, 1, 0], [1, 0, 1, 0], [1, 1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 1, 0], [1, 0, 1, 0], [1, 1, 1, 0]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def smallNetAc : Fin 11 → Option (Fin 1) := colourOf [0, 1, 1, 1, 1]
def smallNetVc : Fin 11 → Option (Fin 1) := colourOf [0, 1, 1, 1, 1]

theorem smallNet_derives : smallNet.Derives smallRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem smallNet_obeys (c : Crossover) : smallNet.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem smallNet_cover : GallCover smallNet smallNetAc smallNetVc :=
  GallCover.of_decide (fun _ => 1) (fun _ => 3) (fun _ => 2) (fun _ => 4)
    (fun e v => if e = 0 then decide (1 ≤ v.val ∧ v.val ≤ 4 ∨ 7 ≤ v.val) else decide (v = smallNet.tgt e))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem smallNet_fullyDecomposed : smallNet.IsFullyDecomposedFor (incompatGraph smallRows) :=
  smallNet_cover.isFullyDecomposedFor (tbl [0, 0, 1, 2] : Fin 4 → Fin 3)
    (by unfold Incompatible; decide +kernel) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem smallNet_efficient : smallNet.IsEfficient :=
  smallNet_cover.isEfficient (by decide +kernel) (by decide +kernel)

/-! ### The first example of Section 4.2 -/

/-- The rows `0000 0001 0010 0100 1000 1100`. -/
def treenessRows₁ : Finset (Fin 4 → Bool) :=
  {ofBits [0, 0, 0, 0], ofBits [0, 0, 0, 1], ofBits [0, 0, 1, 0], ofBits [0, 1, 0, 0], ofBits [1, 0, 0, 0], ofBits [1, 1, 0, 0]}

/-- The labels of `treenessNet₁`, `treenessNet₁'`. -/
def treenessLabels₁ : List (List ℕ) :=
  [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [1, 0, 0, 0], [1, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0], [1, 1, 0, 0]]

/-- The network for `treenessRows₁` with `T′ = T̄`: a root with four arcs, one into the blob. -/
def treenessNet₁ : Network (Fin 4) (Fin 11) (Fin 11) :=
  mkNet (tbl [0, 1, 1, 2, 3, 0, 0, 0, 2, 3, 4]) (tbl [1, 2, 3, 4, 4, 5, 6, 7, 8, 9, 10]) 0 (tbl [2, 1, 7, 6]) (bitsOf treenessLabels₁)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The network for `treenessRows₁` with as many edges in `T′`, and `T′ ≠ T̄`: the row `0010` hangs from the top of the blob, through an arc with the site 2. -/
def treenessNet₁' : Network (Fin 4) (Fin 11) (Fin 11) :=
  mkNet (tbl [0, 1, 1, 2, 3, 0, 0, 1, 2, 3, 4]) (tbl [1, 2, 3, 4, 4, 5, 6, 7, 8, 9, 10]) 0 (tbl [2, 1, 7, 6]) (bitsOf treenessLabels₁)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def treenessAc₁ : Fin 11 → Option (Fin 1) := colourOf [0, 1, 1, 1, 1]
def treenessVc₁ : Fin 11 → Option (Fin 1) := colourOf [0, 1, 1, 1, 1]

theorem treenessNet₁_derives : treenessNet₁.Derives treenessRows₁ :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem treenessNet₁_obeys (c : Crossover) : treenessNet₁.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem treenessNet₁_cover : GallCover treenessNet₁ treenessAc₁ treenessVc₁ :=
  GallCover.of_decide (fun _ => 1) (fun _ => 3) (fun _ => 2) (fun _ => 4)
    (fun e v => if e = 0 then decide (1 ≤ v.val ∧ v.val ≤ 4 ∨ 8 ≤ v.val) else decide (v = treenessNet₁.tgt e))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem treenessNet₁_fullyDecomposed : treenessNet₁.IsFullyDecomposedFor (incompatGraph treenessRows₁) :=
  treenessNet₁_cover.isFullyDecomposedFor (tbl [0, 0, 1, 2] : Fin 4 → Fin 3)
    (by unfold Incompatible; decide +kernel) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem treenessNet₁_efficient : treenessNet₁.IsEfficient :=
  treenessNet₁_cover.isEfficient (by decide +kernel) (by decide +kernel)

theorem treenessNet₁'_derives : treenessNet₁'.Derives treenessRows₁ :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem treenessNet₁'_obeys (c : Crossover) : treenessNet₁'.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem treenessNet₁'_cover : GallCover treenessNet₁' treenessAc₁ treenessVc₁ :=
  GallCover.of_decide (fun _ => 1) (fun _ => 3) (fun _ => 2) (fun _ => 4)
    (fun e v => if e = 0 then decide (1 ≤ v.val ∧ v.val ≤ 4 ∨ 7 ≤ v.val) else decide (v = treenessNet₁'.tgt e))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem treenessNet₁'_fullyDecomposed : treenessNet₁'.IsFullyDecomposedFor (incompatGraph treenessRows₁) :=
  treenessNet₁'_cover.isFullyDecomposedFor (tbl [0, 0, 1, 2] : Fin 4 → Fin 3)
    (by unfold Incompatible; decide +kernel) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem treenessNet₁'_efficient : treenessNet₁'.IsEfficient :=
  treenessNet₁'_cover.isEfficient (by decide +kernel) (by decide +kernel)

/-! ### The second example of Section 4.2 -/

/-- The rows `00000 00001 00010 00100 01000 10000 11000`. -/
def treenessRows₂ : Finset (Fin 5 → Bool) :=
  {ofBits [0, 0, 0, 0, 0], ofBits [0, 0, 0, 0, 1], ofBits [0, 0, 0, 1, 0], ofBits [0, 0, 1, 0, 0], ofBits [0, 1, 0, 0, 0], ofBits [1, 0, 0, 0, 0], ofBits [1, 1, 0, 0, 0]}

/-- The network for `treenessRows₂` with `T′ = T̄`: a root with five arcs, one into the blob. -/
def treenessNet₂ : Network (Fin 5) (Fin 12) (Fin 12) :=
  mkNet (tbl [0, 1, 1, 2, 3, 0, 0, 0, 0, 2, 3, 4]) (tbl [1, 2, 3, 4, 4, 5, 6, 7, 8, 9, 10, 11]) 0 (tbl [2, 1, 6, 7, 8])
    (bitsOf [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [1, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [1, 1, 0, 0, 0]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def treenessAc₂ : Fin 12 → Option (Fin 1) := colourOf [0, 1, 1, 1, 1]
def treenessVc₂ : Fin 12 → Option (Fin 1) := colourOf [0, 1, 1, 1, 1]

theorem treenessNet₂_derives : treenessNet₂.Derives treenessRows₂ :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem treenessNet₂_obeys (c : Crossover) : treenessNet₂.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem treenessNet₂_cover : GallCover treenessNet₂ treenessAc₂ treenessVc₂ :=
  GallCover.of_decide (fun _ => 1) (fun _ => 3) (fun _ => 2) (fun _ => 4)
    (fun e v => if e = 0 then decide (1 ≤ v.val ∧ v.val ≤ 4 ∨ 9 ≤ v.val) else decide (v = treenessNet₂.tgt e))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem treenessNet₂_fullyDecomposed : treenessNet₂.IsFullyDecomposedFor (incompatGraph treenessRows₂) :=
  treenessNet₂_cover.isFullyDecomposedFor (tbl [0, 0, 1, 2, 3] : Fin 5 → Fin 4)
    (by unfold Incompatible; decide +kernel) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem treenessNet₂_efficient : treenessNet₂.IsEfficient :=
  treenessNet₂_cover.isEfficient (by decide +kernel) (by decide +kernel)

/-- The network for `treenessRows₂` with one more edge in `T′` than `T̄`: two rows are below a site-free arc out of the top of the blob. -/
def treenessNet₂' : Network (Fin 5) (Fin 13) (Fin 13) :=
  mkNet (tbl [0, 1, 1, 1, 3, 4, 0, 0, 2, 2, 3, 4, 5]) (tbl [1, 2, 3, 4, 5, 5, 6, 7, 8, 9, 10, 11, 12]) 0 (tbl [3, 2, 7, 8, 9])
    (bitsOf [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [1, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [1, 1, 0, 0, 0]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def treenessAc₂' : Fin 13 → Option (Fin 1) := colourOf [0, 0, 1, 1, 1, 1]
def treenessVc₂' : Fin 13 → Option (Fin 1) := colourOf [0, 1, 0, 1, 1, 1]

theorem treenessNet₂'_derives : treenessNet₂'.Derives treenessRows₂ :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem treenessNet₂'_obeys (c : Crossover) : treenessNet₂'.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem treenessNet₂'_cover : GallCover treenessNet₂' treenessAc₂' treenessVc₂' :=
  GallCover.of_decide (fun _ => 2) (fun _ => 4) (fun _ => 3) (fun _ => 5)
    (fun e v => if e = 0 then decide (1 ≤ v.val ∧ v.val ≤ 5 ∨ 8 ≤ v.val) else
      if e = 1 then decide (v.val = 2 ∨ v.val = 8 ∨ v.val = 9) else decide (v = treenessNet₂'.tgt e))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem treenessNet₂'_fullyDecomposed : treenessNet₂'.IsFullyDecomposedFor (incompatGraph treenessRows₂) :=
  treenessNet₂'_cover.isFullyDecomposedFor (tbl [0, 0, 1, 2, 3] : Fin 5 → Fin 4)
    (by unfold Incompatible; decide +kernel) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem treenessNet₂'_efficient : treenessNet₂'.IsEfficient :=
  treenessNet₂'_cover.isEfficient (by decide +kernel) (by decide +kernel)

/-! ### The star, and a root of out-degree one -/

/-- The star for `starRows`: a root with four arcs, each with a site. -/
def starNet : Network (Fin 4) (Fin 5) (Fin 4) :=
  mkNet (tbl [0, 0, 0, 0]) (tbl [1, 2, 3, 4]) 0 (tbl [0, 1, 2, 3])
    (bitsOf [[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The star resolved by two arcs with no site. -/
def starNet' : Network (Fin 4) (Fin 7) (Fin 6) :=
  mkNet (tbl [0, 0, 1, 1, 2, 2]) (tbl [1, 2, 3, 4, 5, 6]) 0 (tbl [2, 3, 4, 5])
    (bitsOf [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem starNet_tgt_injective : Function.Injective starNet.tgt := by
  intro e f h
  revert e f
  decide +kernel

theorem starNet'_tgt_injective : Function.Injective starNet'.tgt := by
  intro e f h
  revert e f
  decide +kernel

theorem starNet_derives : starNet.Derives starRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem starNet'_derives : starNet'.Derives starRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The rows `00`, `01`, `10`. -/
def threeRows : Finset (Fin 2 → Bool) := {ofBits [0, 0], ofBits [0, 1], ofBits [1, 0]}

/-- `T̄` for `threeRows`: a root with three arcs. -/
def threeNet : Network (Fin 2) (Fin 4) (Fin 3) :=
  mkNet (tbl [0, 0, 0]) (tbl [1, 2, 3]) 0 (tbl [2, 1]) (bitsOf [[0, 0], [0, 0], [0, 1], [1, 0]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The same, with a new root above the root, on a site-free arc: a root of out-degree one, whose split has an empty side. -/
def threeNet' : Network (Fin 2) (Fin 5) (Fin 4) :=
  mkNet (tbl [0, 1, 1, 1]) (tbl [1, 2, 3, 4]) 0 (tbl [3, 2]) (bitsOf [[0, 0], [0, 0], [0, 0], [0, 1], [1, 0]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem threeNet_tgt_injective : Function.Injective threeNet.tgt := by
  intro e f h
  revert e f
  decide +kernel

theorem threeNet'_tgt_injective : Function.Injective threeNet'.tgt := by
  intro e f h
  revert e f
  decide +kernel

theorem threeNet_derives : threeNet.Derives threeRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem threeNet'_derives : threeNet'.Derives threeRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The standing assumption holds for each of these sets of rows. So `T̄` exists for them (`exists_isTBar`), and the statements below that quantify over `T̄` aren't vacuous. -/

theorem noConstantColumn_fourGametes : NoConstantColumn fourGametes := by
  unfold NoConstantColumn
  decide +kernel

theorem noConstantColumn_topRows : NoConstantColumn topRows := by
  unfold NoConstantColumn
  decide +kernel

theorem noConstantColumn_smallRows : NoConstantColumn smallRows := by
  unfold NoConstantColumn
  decide +kernel

theorem noConstantColumn_treenessRows₁ : NoConstantColumn treenessRows₁ := by
  unfold NoConstantColumn
  decide +kernel

theorem noConstantColumn_treenessRows₂ : NoConstantColumn treenessRows₂ := by
  unfold NoConstantColumn
  decide +kernel

theorem noConstantColumn_starRows : NoConstantColumn starRows := by
  unfold NoConstantColumn
  decide +kernel

theorem noConstantColumn_threeRows : NoConstantColumn threeRows := by
  unfold NoConstantColumn
  decide +kernel

/-! ### Degrees and exits -/

theorem topNet_degree : ∀ v, (topNet.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, topNet.IsLeaf l ∧ topNet.toBlobNode l = v :=
  topNet_cover.degree_cond (tbl [9, 9, 9, 9, 12, 12, 12, 12]) (tbl [10, 10, 10, 10, 13, 13, 13, 13]) (tbl [11, 11, 11, 11, 14, 14, 14, 14]) (by decide +kernel)

theorem smallNet_degree : ∀ v, (smallNet.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, smallNet.IsLeaf l ∧ smallNet.toBlobNode l = v :=
  smallNet_cover.degree_cond (tbl [5, 7, 7, 7, 7]) (tbl [6, 8, 8, 8, 8]) (tbl [0, 9, 9, 9, 9]) (by decide +kernel)

theorem treenessNet₁_degree : ∀ v, (treenessNet₁.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, treenessNet₁.IsLeaf l ∧ treenessNet₁.toBlobNode l = v :=
  treenessNet₁_cover.degree_cond (tbl [5, 8, 8, 8, 8]) (tbl [6, 9, 9, 9, 9]) (tbl [7, 10, 10, 10, 10]) (by decide +kernel)

theorem treenessNet₂_degree : ∀ v, (treenessNet₂.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, treenessNet₂.IsLeaf l ∧ treenessNet₂.toBlobNode l = v :=
  treenessNet₂_cover.degree_cond (tbl [5, 9, 9, 9, 9]) (tbl [6, 10, 10, 10, 10]) (tbl [7, 11, 11, 11, 11]) (by decide +kernel)

theorem starNet_cover : GallCover (κ := Empty) starNet (fun _ => none) (fun _ => none) := GallCover.of_tgt_injective starNet_tgt_injective

theorem starNet_degree : ∀ v, (starNet.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, starNet.IsLeaf l ∧ starNet.toBlobNode l = v :=
  starNet_cover.degree_cond (fun _ => 0) (fun _ => 1) (fun _ => 2) (by decide +kernel)

theorem threeNet_cover : GallCover (κ := Empty) threeNet (fun _ => none) (fun _ => none) := GallCover.of_tgt_injective threeNet_tgt_injective

theorem threeNet_degree : ∀ v, (threeNet.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, threeNet.IsLeaf l ∧ threeNet.toBlobNode l = v :=
  threeNet_cover.degree_cond (fun _ => 0) (fun _ => 1) (fun _ => 2) (by decide +kernel)

theorem threeNet'_cover : GallCover (κ := Empty) threeNet' (fun _ => none) (fun _ => none) := GallCover.of_tgt_injective threeNet'_tgt_injective

theorem starNet'_cover : GallCover (κ := Empty) starNet' (fun _ => none) (fun _ => none) := GallCover.of_tgt_injective starNet'_tgt_injective

/-- No node of in-degree and out-degree one (line 364). -/
theorem starNet_noOneOne : ∀ e f, starNet.tgt e = starNet.src f → (∀ g, starNet.tgt g = starNet.tgt e → g = e) → (∀ g, starNet.src g = starNet.src f → g = f) → False := by
  decide +kernel

theorem starNet'_noOneOne : ∀ e f, starNet'.tgt e = starNet'.src f → (∀ g, starNet'.tgt g = starNet'.tgt e → g = e) → (∀ g, starNet'.src g = starNet'.src f → g = f) → False := by
  decide +kernel

theorem treenessNet₁'_noOneOne : ∀ e f, treenessNet₁'.tgt e = treenessNet₁'.src f → (∀ g, treenessNet₁'.tgt g = treenessNet₁'.tgt e → g = e) →
    (∀ g, treenessNet₁'.src g = treenessNet₁'.src f → g = f) → False := by
  decide +kernel

theorem treenessNet₂'_noOneOne : ∀ e f, treenessNet₂'.tgt e = treenessNet₂'.src f → (∀ g, treenessNet₂'.tgt g = treenessNet₂'.tgt e → g = e) →
    (∀ g, treenessNet₂'.src g = treenessNet₂'.src f → g = f) → False := by
  decide +kernel

/-- The arc of the row that hangs from the top of a blob, in `topNet`: it's the row `11001`. -/
theorem topNet_exit : topNetVc (topNet.src 12) = some 1 ∧ topNetVc (topNet.tgt 12) ≠ some 1 ∧ (∀ f, topNetAc f = some 1 → topNet.tgt f ≠ topNet.src 12) ∧
    topNet.src 12 ≠ topNet.root := by
  decide +kernel

theorem smallNet_exit : smallNetVc (smallNet.src 7) = some 0 ∧ smallNetVc (smallNet.tgt 7) ≠ some 0 ∧ (∀ f, smallNetAc f = some 0 → smallNet.tgt f ≠ smallNet.src 7) ∧
    smallNet.src 7 ≠ smallNet.root := by
  decide +kernel

theorem treenessNet₁'_exit : treenessVc₁ (treenessNet₁'.src 7) = some 0 ∧ treenessVc₁ (treenessNet₁'.tgt 7) ≠ some 0 ∧
    (∀ f, treenessAc₁ f = some 0 → treenessNet₁'.tgt f ≠ treenessNet₁'.src 7) ∧ treenessNet₁'.src 7 ≠ treenessNet₁'.root := by
  decide +kernel

/-! ### The conditions of `IsTreeNormalStructural` -/

theorem topNet_hr : ∀ e f, e ≠ f → topNet.tgt e = topNet.tgt f → ∃ g, topNet.src g = topNet.tgt e := by decide +kernel

theorem topNet_hl : ∀ e, topNetAc e = none → topNetVc (topNet.src e) = none → topNetVc (topNet.tgt e) = none → (∃ g, topNet.src g = topNet.tgt e) →
    ∃ i, topNet.site i = e := by
  decide +kernel

theorem smallNet_hr : ∀ e f, e ≠ f → smallNet.tgt e = smallNet.tgt f → ∃ g, smallNet.src g = smallNet.tgt e := by decide +kernel

theorem smallNet_hl : ∀ e, smallNetAc e = none → smallNetVc (smallNet.src e) = none → smallNetVc (smallNet.tgt e) = none → (∃ g, smallNet.src g = smallNet.tgt e) →
    ∃ i, smallNet.site i = e := by
  decide +kernel

theorem treenessNet₁_hr : ∀ e f, e ≠ f → treenessNet₁.tgt e = treenessNet₁.tgt f → ∃ g, treenessNet₁.src g = treenessNet₁.tgt e := by decide +kernel

theorem treenessNet₁_hl : ∀ e, treenessAc₁ e = none → treenessVc₁ (treenessNet₁.src e) = none → treenessVc₁ (treenessNet₁.tgt e) = none →
    (∃ g, treenessNet₁.src g = treenessNet₁.tgt e) → ∃ i, treenessNet₁.site i = e := by
  decide +kernel

theorem treenessNet₁_htop : ∀ k e w, treenessVc₁ (treenessNet₁.src e) = some k → treenessVc₁ (treenessNet₁.tgt e) ≠ some k → treenessVc₁ w = some k →
    (∀ f, treenessAc₁ f = some k → treenessNet₁.tgt f ≠ w) → w ≠ treenessNet₁.root → ∃ i, treenessAc₁ (treenessNet₁.site i) = some k ∧
      treenessNet₁.label (treenessNet₁.src e) i ≠ treenessNet₁.label w i := by
  decide +kernel

theorem treenessNet₂_hr : ∀ e f, e ≠ f → treenessNet₂.tgt e = treenessNet₂.tgt f → ∃ g, treenessNet₂.src g = treenessNet₂.tgt e := by decide +kernel

theorem treenessNet₂_hl : ∀ e, treenessAc₂ e = none → treenessVc₂ (treenessNet₂.src e) = none → treenessVc₂ (treenessNet₂.tgt e) = none →
    (∃ g, treenessNet₂.src g = treenessNet₂.tgt e) → ∃ i, treenessNet₂.site i = e := by
  decide +kernel

theorem treenessNet₂_htop : ∀ k e w, treenessVc₂ (treenessNet₂.src e) = some k → treenessVc₂ (treenessNet₂.tgt e) ≠ some k → treenessVc₂ w = some k →
    (∀ f, treenessAc₂ f = some k → treenessNet₂.tgt f ≠ w) → w ≠ treenessNet₂.root → ∃ i, treenessAc₂ (treenessNet₂.site i) = some k ∧
      treenessNet₂.label (treenessNet₂.src e) i ≠ treenessNet₂.label w i := by
  decide +kernel

theorem treenessNet₂'_hl : ∀ e, treenessAc₂' e = none → treenessVc₂' (treenessNet₂'.src e) = none → treenessVc₂' (treenessNet₂'.tgt e) = none →
    (∃ g, treenessNet₂'.src g = treenessNet₂'.tgt e) → ∃ i, treenessNet₂'.site i = e := by
  decide +kernel

theorem treenessNet₁'_hl : ∀ e, treenessAc₁ e = none → treenessVc₁ (treenessNet₁'.src e) = none → treenessVc₁ (treenessNet₁'.tgt e) = none →
    (∃ g, treenessNet₁'.src g = treenessNet₁'.tgt e) → ∃ i, treenessNet₁'.site i = e := by
  decide +kernel

theorem starNet_hr : ∀ e f, e ≠ f → starNet.tgt e = starNet.tgt f → ∃ g, starNet.src g = starNet.tgt e := by decide +kernel

theorem starNet_hl : ∀ e, (∃ g, starNet.src g = starNet.tgt e) → ∃ i, starNet.site i = e := by decide +kernel

theorem threeNet_hr : ∀ e f, e ≠ f → threeNet.tgt e = threeNet.tgt f → ∃ g, threeNet.src g = threeNet.tgt e := by decide +kernel

theorem threeNet_hl : ∀ e, (∃ g, threeNet.src g = threeNet.tgt e) → ∃ i, threeNet.site i = e := by decide +kernel

/-! ### Numbers of tree arcs -/

theorem treenessAc₁_card : Fintype.card {e // treenessAc₁ e = none} = 7 := by decide +kernel

theorem treenessAc₂_card : Fintype.card {e // treenessAc₂ e = none} = 8 := by decide +kernel

theorem treenessAc₂'_card : Fintype.card {e // treenessAc₂' e = none} = 9 := by decide +kernel

/-! ### A row at the root of a blob -/

/-- `{00, 01, 10, 11}`, with a blob at the root and a pendant arc at each of its four nodes, the root included. -/
def fourRootNet : Network (Fin 2) (Fin 8) (Fin 8) :=
  mkNet (tbl [0, 0, 1, 2, 0, 1, 2, 3]) (tbl [1, 2, 3, 3, 4, 5, 6, 7]) 0 (tbl [1, 0])
    (bitsOf [[0, 0], [0, 1], [1, 0], [1, 1], [0, 0], [0, 1], [1, 0], [1, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def fourRootNetAc : Fin 8 → Option (Fin 1) := colourOf [1, 1, 1, 1]
def fourRootNetVc : Fin 8 → Option (Fin 1) := colourOf [1, 1, 1, 1]

theorem fourRootNet_derives : fourRootNet.Derives fourGametes :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fourRootNet_obeys (c : Crossover) : fourRootNet.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem fourRootNet_cover : GallCover fourRootNet fourRootNetAc fourRootNetVc :=
  GallCover.of_decide (fun _ => 0) (fun _ => 2) (fun _ => 1) (fun _ => 3) (fun e v => decide (v = fourRootNet.tgt e)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem fourRootNet_fullyDecomposed : fourRootNet.IsFullyDecomposedFor (incompatGraph fourGametes) :=
  fourRootNet_cover.isFullyDecomposedFor (fun _ : Fin 2 => 0)
    (fun _ _ _ => rfl) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem fourRootNet_efficient : fourRootNet.IsEfficient :=
  fourRootNet_cover.isEfficient (by decide +kernel) (by decide +kernel)

theorem fourRootNet_degree : ∀ v, (fourRootNet.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, fourRootNet.IsLeaf l ∧ fourRootNet.toBlobNode l = v :=
  fourRootNet_cover.degree_cond (fun _ => 4) (fun _ => 5) (fun _ => 6) (by decide +kernel)

theorem fourRootNet_hr : ∀ e f, e ≠ f → fourRootNet.tgt e = fourRootNet.tgt f → ∃ g, fourRootNet.src g = fourRootNet.tgt e := by decide +kernel

theorem fourRootNet_hl : ∀ e, fourRootNetAc e = none → fourRootNetVc (fourRootNet.src e) = none → fourRootNetVc (fourRootNet.tgt e) = none →
    (∃ g, fourRootNet.src g = fourRootNet.tgt e) → ∃ i, fourRootNet.site i = e := by
  decide +kernel

theorem fourRootNet_htop : ∀ k e w, fourRootNetVc (fourRootNet.src e) = some k → fourRootNetVc (fourRootNet.tgt e) ≠ some k → fourRootNetVc w = some k →
    (∀ f, fourRootNetAc f = some k → fourRootNet.tgt f ≠ w) → w ≠ fourRootNet.root → ∃ i, fourRootNetAc (fourRootNet.site i) = some k ∧
      fourRootNet.label (fourRootNet.src e) i ≠ fourRootNet.label w i := by
  decide +kernel

/-- The arc from the root, in the blob, to a row. -/
theorem fourRootNet_exit : fourRootNetVc (fourRootNet.src 4) = some 0 ∧ fourRootNetVc (fourRootNet.tgt 4) ≠ some 0 ∧ (∀ f, fourRootNetAc f = some 0 → fourRootNet.tgt f ≠ fourRootNet.src 4) := by
  decide +kernel

/-- The degrees in `T′` of `threeNet'`, which has no blob: none is two. -/
theorem threeNet'_degree : ∀ z, (Finset.univ.filter fun y => ∃ e, (threeNet'.src e = z ∧ threeNet'.tgt e = y) ∨ (threeNet'.tgt e = z ∧ threeNet'.src e = y)).card ≠ 2 := by
  decide +kernel

theorem threeRows_card : threeRows.card = 3 := by decide +kernel

/-! ### Site-free arcs: a third failure of Theorem 4 -/

/-- The rows `10000, 01000, 00100, 00010, 00001`. -/
def fiveRows : Finset (Fin 5 → Bool) :=
  {ofBits [1, 0, 0, 0, 0], ofBits [0, 1, 0, 0, 0], ofBits [0, 0, 1, 0, 0], ofBits [0, 0, 0, 1, 0], ofBits [0, 0, 0, 0, 1]}

/-- A root with arcs to the rows `10000`, `01000`, and a site-free arc to a node with the rows `00100`, `00010`, `00001`. -/
def fiveNet : Network (Fin 5) (Fin 7) (Fin 6) :=
  mkNet (tbl [0, 0, 0, 1, 1, 1]) (tbl [1, 2, 3, 4, 5, 6]) 0 (tbl [1, 2, 3, 4, 5])
    (bitsOf [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `T̄` for `fiveRows`: a root with five arcs. -/
def fiveStarNet : Network (Fin 5) (Fin 6) (Fin 5) :=
  mkNet (tbl [0, 0, 0, 0, 0]) (tbl [1, 2, 3, 4, 5]) 0 (tbl [0, 1, 2, 3, 4])
    (bitsOf [[0, 0, 0, 0, 0], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fiveNet_tgt_injective : Function.Injective fiveNet.tgt := by
  intro e f h
  revert e f
  decide +kernel

theorem fiveStarNet_tgt_injective : Function.Injective fiveStarNet.tgt := by
  intro e f h
  revert e f
  decide +kernel

theorem fiveNet_derives : fiveNet.Derives fiveRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fiveStarNet_derives : fiveStarNet.Derives fiveRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem noConstantColumn_fiveRows : NoConstantColumn fiveRows := by
  unfold NoConstantColumn
  decide +kernel

theorem fiveNet_cover : GallCover (κ := Empty) fiveNet (fun _ => none) (fun _ => none) := GallCover.of_tgt_injective fiveNet_tgt_injective

theorem fiveStarNet_cover : GallCover (κ := Empty) fiveStarNet (fun _ => none) (fun _ => none) := GallCover.of_tgt_injective fiveStarNet_tgt_injective

theorem fiveNet_degree : ∀ v, (fiveNet.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, fiveNet.IsLeaf l ∧ fiveNet.toBlobNode l = v :=
  fiveNet_cover.degree_cond (tbl [1, 3]) (tbl [2, 4]) (tbl [0, 5]) (by decide +kernel)

theorem fiveStarNet_degree : ∀ v, (fiveStarNet.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, fiveStarNet.IsLeaf l ∧ fiveStarNet.toBlobNode l = v :=
  fiveStarNet_cover.degree_cond (fun _ => 0) (fun _ => 1) (fun _ => 2) (by decide +kernel)

theorem fiveNet_hr : ∀ e f, e ≠ f → fiveNet.tgt e = fiveNet.tgt f → ∃ g, fiveNet.src g = fiveNet.tgt e := by decide +kernel

theorem fiveStarNet_hr : ∀ e f, e ≠ f → fiveStarNet.tgt e = fiveStarNet.tgt f → ∃ g, fiveStarNet.src g = fiveStarNet.tgt e := by decide +kernel

theorem fiveStarNet_hl : ∀ e, (∃ g, fiveStarNet.src g = fiveStarNet.tgt e) → ∃ i, fiveStarNet.site i = e := by decide +kernel

/-- The site-free arc of `fiveNet`, with both ends off the blobs, and not pendant. -/
theorem fiveNet_siteFree : (∀ i, fiveNet.site i ≠ 0) ∧ ∃ g, fiveNet.src g = fiveNet.tgt 0 := by decide +kernel

/-- The rows below the site-free arc of `fiveNet`: `00100, 00010, 00001`. -/
def fiveBelow : Finset (Fin 5 → Bool) := {ofBits [0, 0, 1, 0, 0], ofBits [0, 0, 0, 1, 0], ofBits [0, 0, 0, 0, 1]}

theorem fiveNet_arcSide : fiveNet.arcSide 0 = (fiveBelow : Set (Fin 5 → Bool)) := by
  ext r
  constructor
  · rintro ⟨v, hv, hr, rfl⟩
    have hclosed : ∀ e, ((fiveNet.src e).val = 1 ∨ 4 ≤ (fiveNet.src e).val) → ((fiveNet.tgt e).val = 1 ∨ 4 ≤ (fiveNet.tgt e).val) := by decide +kernel
    have h₀ : (fiveNet.tgt 0).val = 1 ∨ 4 ≤ (fiveNet.tgt 0).val := by decide +kernel
    have hD : ∀ z, fiveNet.Reach (fiveNet.tgt 0) z → z.val = 1 ∨ 4 ≤ z.val := by
      intro z hz
      induction hz with
      | refl => exact h₀
      | tail _ hs ih =>
        obtain ⟨g, hg, rfl⟩ := hs
        exact hclosed g (hg ▸ ih)
    have key : ∀ v : Fin 7, (∀ e, fiveNet.src e ≠ v) → (v.val = 1 ∨ 4 ≤ v.val) → fiveNet.label v ∈ fiveBelow := by decide +kernel
    exact Finset.mem_coe.2 (key v hv (hD v hr))
  · intro hr
    have key : ∀ r ∈ fiveBelow, ∃ g : Fin 6, fiveNet.src g = fiveNet.tgt 0 ∧ (∀ e, fiveNet.src e ≠ fiveNet.tgt g) ∧ fiveNet.label (fiveNet.tgt g) = r := by decide +kernel
    obtain ⟨g, h₁, h₂, h₃⟩ := key r (Finset.mem_coe.1 hr)
    exact ⟨_, h₂, Relation.ReflTransGen.single ⟨g, h₁, rfl⟩, h₃⟩

/-- What's needed of the rows and `fiveBelow`. -/
theorem fiveBelow_facts : (ofBits [0, 0, 1, 0, 0] : Fin 5 → Bool) ∈ fiveBelow ∧ (ofBits [0, 0, 0, 1, 0] : Fin 5 → Bool) ∈ fiveBelow ∧ (ofBits [1, 0, 0, 0, 0] : Fin 5 → Bool) ∉ fiveBelow ∧ (ofBits [0, 1, 0, 0, 0] : Fin 5 → Bool) ∉ fiveBelow ∧
    (ofBits [0, 0, 1, 0, 0] : Fin 5 → Bool) ∈ fiveRows ∧ (ofBits [0, 0, 0, 1, 0] : Fin 5 → Bool) ∈ fiveRows ∧ (ofBits [1, 0, 0, 0, 0] : Fin 5 → Bool) ∈ fiveRows ∧ (ofBits [0, 1, 0, 0, 0] : Fin 5 → Bool) ∈ fiveRows ∧
    (ofBits [0, 0, 1, 0, 0] : Fin 5 → Bool) ≠ ofBits [0, 0, 0, 1, 0] ∧ (ofBits [1, 0, 0, 0, 0] : Fin 5 → Bool) ≠ ofBits [0, 1, 0, 0, 0] := by
  decide +kernel

/-- An arc of the star has at most one row below it. -/
theorem fiveStarNet_arcSide_subsingleton (g : Fin 5) {r r' : Fin 5 → Bool} (h : r ∈ fiveStarNet.arcSide g) (h' : r' ∈ fiveStarNet.arcSide g) : r = r' := by
  have key : ∀ g e, fiveStarNet.src e ≠ fiveStarNet.tgt g := by decide +kernel
  have hs : ∀ {z}, fiveStarNet.Reach (fiveStarNet.tgt g) z → z = fiveStarNet.tgt g := by
    intro z hz
    rcases Relation.ReflTransGen.cases_head hz with h₁ | ⟨b, ⟨f, hf, -⟩, -⟩
    · exact h₁.symm
    · exact absurd hf (key g f)
  obtain ⟨v, -, hv, rfl⟩ := h
  obtain ⟨v', -, hv', rfl⟩ := h'
  rw [hs hv, hs hv']

theorem fiveNet_treeness : fiveNet.treeness = 6 := by
  rw [fiveNet_cover.treeness_eq]
  decide +kernel

theorem fiveStarNet_treeness : fiveStarNet.treeness = 5 := by
  rw [fiveStarNet_cover.treeness_eq]
  decide +kernel

/-! ### A root above a blob with a row at its top -/

/-- `fourRootNet` with a new site-free root above its root. -/
def fourRootNet' : Network (Fin 2) (Fin 9) (Fin 9) :=
  mkNet (tbl [0, 1, 1, 2, 3, 1, 2, 3, 4]) (tbl [1, 2, 3, 4, 4, 5, 6, 7, 8]) 0 (tbl [2, 1])
    (bitsOf [[0, 0], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0], [0, 1], [1, 0], [1, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def fourRootNet'Ac : Fin 9 → Option (Fin 1) := colourOf [0, 1, 1, 1, 1]
def fourRootNet'Vc : Fin 9 → Option (Fin 1) := colourOf [0, 1, 1, 1, 1]

theorem fourRootNet'_derives : fourRootNet'.Derives fourGametes :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fourRootNet'_cover : GallCover fourRootNet' fourRootNet'Ac fourRootNet'Vc :=
  GallCover.of_decide (fun _ => 1) (fun _ => 3) (fun _ => 2) (fun _ => 4)
    (fun e v => if e = 0 then decide (1 ≤ v.val) else decide (v = fourRootNet'.tgt e))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fourRootNet'_fullyDecomposed : fourRootNet'.IsFullyDecomposedFor (incompatGraph fourGametes) :=
  fourRootNet'_cover.isFullyDecomposedFor (fun _ : Fin 2 => 0)
    (fun _ _ _ => rfl) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem fourRootNet'_efficient : fourRootNet'.IsEfficient :=
  fourRootNet'_cover.isEfficient (by decide +kernel) (by decide +kernel)

theorem fourRootNet'_hr : ∀ e f, e ≠ f → fourRootNet'.tgt e = fourRootNet'.tgt f → ∃ g, fourRootNet'.src g = fourRootNet'.tgt e := by decide +kernel

theorem fourRootNet'_hl : ∀ e, fourRootNet'Ac e = none → fourRootNet'Vc (fourRootNet'.src e) = none → fourRootNet'Vc (fourRootNet'.tgt e) = none →
    (∃ g, fourRootNet'.src g = fourRootNet'.tgt e) → ∃ i, fourRootNet'.site i = e := by
  decide +kernel

theorem fourRootNet'_root : fourRootNet'.src 0 = fourRootNet'.root := by decide +kernel

/-- The arc from the top of the blob to a row, and that the root has one arc, to the top. -/
theorem fourRootNet'_exit : fourRootNet'Vc (fourRootNet'.src 5) = some 0 ∧ fourRootNet'Vc (fourRootNet'.tgt 5) ≠ some 0 ∧ (∀ f, fourRootNet'Ac f = some 0 → fourRootNet'.tgt f ≠ fourRootNet'.src 5) ∧
    fourRootNet'.src 5 ≠ fourRootNet'.root ∧ (∀ e, fourRootNet'.src e = fourRootNet'.root → fourRootNet'.tgt e = fourRootNet'.src 5) ∧
    ∀ w, fourRootNet'Vc w = some 0 → (∀ f, fourRootNet'Ac f = some 0 → fourRootNet'.tgt f ≠ w) → w = fourRootNet'.src 5 := by
  decide +kernel

/-! ### The row moved up, on `topRows` -/

/-- `topNet` with the row `11001` moved up to a new node on the arc entering the second blob. -/
def topNet' : Network (Fin 5) (Fin 16) (Fin 17) :=
  mkNet (tbl [0, 0, 1, 2, 3, 4, 4, 5, 5, 6, 7, 0, 1, 2, 6, 7, 8]) (tbl [1, 2, 3, 3, 4, 5, 12, 6, 7, 8, 8, 9, 10, 11, 13, 14, 15]) 0 (tbl [1, 0, 8, 7, 4])
    (bitsOf [[0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1],
      [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def topNet'Ac : Fin 17 → Option (Fin 2) := colourOf [1, 1, 1, 1, 0, 0, 0, 2, 2, 2, 2]
def topNet'Vc : Fin 16 → Option (Fin 2) := colourOf [1, 1, 1, 1, 0, 2, 2, 2, 2]

theorem topNet'_derives : topNet'.Derives topRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem topNet'_obeys (c : Crossover) : topNet'.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem topNet'_cover : GallCover topNet' topNet'Ac topNet'Vc :=
  GallCover.of_decide (tbl [0, 7]) (tbl [2, 9]) (tbl [1, 8]) (tbl [3, 10])
    (fun e v => if e = 4 then decide (4 ≤ v.val ∧ v.val ≤ 8 ∨ 12 ≤ v.val) else if e = 5 then decide (5 ≤ v.val ∧ v.val ≤ 8 ∨ 13 ≤ v.val) else decide (v = topNet'.tgt e))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem topNet'_fullyDecomposed : topNet'.IsFullyDecomposedFor (incompatGraph topRows) :=
  topNet'_cover.isFullyDecomposedFor (tbl [0, 0, 1, 1, 2] : Fin 5 → Fin 3)
    (by unfold Incompatible; decide +kernel) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem topNet'_efficient : topNet'.IsEfficient :=
  topNet'_cover.isEfficient (by decide +kernel) (by decide +kernel)

theorem topNet'_degree : ∀ v, (topNet'.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, topNet'.IsLeaf l ∧ topNet'.toBlobNode l = v :=
  topNet'_cover.degree_cond₂ (tbl [11, 11, 11, 11, 4, 14, 14, 14, 14]) (tbl [12, 12, 12, 12, 5, 15, 15, 15, 15]) (tbl [13, 13, 13, 13, 6, 16, 16, 16, 16])
    (tbl [9, 9, 9, 9, 3, 13, 13, 13, 13]) (tbl [10, 10, 10, 10, 5, 14, 14, 14, 14]) (tbl [11, 11, 11, 11, 12, 15, 15, 15, 15]) (by decide +kernel)

theorem topNet'_hr : ∀ e f, e ≠ f → topNet'.tgt e = topNet'.tgt f → ∃ g, topNet'.src g = topNet'.tgt e := by decide +kernel

theorem topNet'_hl : ∀ e, topNet'Ac e = none → topNet'Vc (topNet'.src e) = none → topNet'Vc (topNet'.tgt e) = none →
    (∃ g, topNet'.src g = topNet'.tgt e) → ∃ i, topNet'.site i = e := by
  decide +kernel

theorem topNet'_htop : ∀ k e w, topNet'Vc (topNet'.src e) = some k → topNet'Vc (topNet'.tgt e) ≠ some k → topNet'Vc w = some k →
    (∀ f, topNet'Ac f = some k → topNet'.tgt f ≠ w) → w ≠ topNet'.root → ∃ i, topNet'Ac (topNet'.site i) = some k ∧
      topNet'.label (topNet'.src e) i ≠ topNet'.label w i := by
  decide +kernel

/-- The entering arc and the row's arc of the second blob of `topNet` are at one node. -/
theorem topNet_entry : topNetVc (topNet.tgt 4) = some 1 ∧ topNetVc (topNet.src 4) ≠ some 1 ∧ topNetVc (topNet.src 12) = some 1 ∧ topNetVc (topNet.tgt 12) ≠ some 1 ∧
    topNet.tgt 4 = topNet.src 12 ∧ (4 : Fin 16) ≠ 12 := by
  decide +kernel

/-! ### Figure 2 made efficient -/

/-- The rows of Figures 1 and 2. -/
def fig2Rows : Finset (Fin 5 → Bool) :=
  {ofBits [0, 0, 0, 1, 0], ofBits [1, 0, 0, 1, 0], ofBits [1, 0, 1, 0, 0], ofBits [0, 0, 1, 0, 0], ofBits [0, 1, 1, 0, 0], ofBits [0, 0, 1, 0, 1], ofBits [0, 1, 1, 0, 1]}

/-- The fully decomposed network of Figure 2, made efficient: the node `00100`, with the row and the arc to the second blob, has the two below a new node. -/
def fig2Net : Network (Fin 5) (Fin 17) (Fin 18) :=
  mkNet (tbl [0, 0, 1, 3, 2, 1, 3, 4, 2, 5, 5, 6, 6, 7, 8, 7, 8, 9]) (tbl [1, 2, 3, 4, 4, 10, 11, 12, 5, 13, 6, 7, 8, 9, 9, 14, 15, 16]) 0 (tbl [2, 11, 1, 0, 12])
    (bitsOf [[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [1, 0, 0, 1, 0], [1, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0], [0, 0, 1, 0, 1], [0, 1, 1, 0, 1],
      [0, 0, 0, 1, 0], [1, 0, 0, 1, 0], [1, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0], [0, 0, 1, 0, 1], [0, 1, 1, 0, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def fig2Ac : Fin 18 → Option (Fin 2) := colourOf [1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2]
def fig2Vc : Fin 17 → Option (Fin 2) := colourOf [1, 1, 1, 1, 1, 0, 2, 2, 2, 2]

theorem fig2Net_derives : fig2Net.Derives fig2Rows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fig2Net_obeys (c : Crossover) : fig2Net.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem fig2Net_cycle (k : Fin 2) : fig2Net.IsCycle {e | fig2Ac e = some k} := by
  fin_cases k
  · refine ⟨0, 4, [0, 2, 3], [1, 4], ⟨⟨3, 4, by decide, rfl, rfl⟩, ⟨by decide, by decide, by decide, by change _ = _; decide⟩, ⟨by decide, by decide, by change _ = _; decide⟩, by decide, ?_⟩, ?_⟩
    · decide +kernel
    · ext e
      revert e
      simp only [Set.mem_ofPred_eq]
      decide +kernel
  · refine ⟨6, 9, [11, 13], [12, 14], ⟨⟨13, 14, by decide, rfl, rfl⟩, ⟨by decide, by decide, by change _ = _; decide⟩, ⟨by decide, by decide, by change _ = _; decide⟩, by decide, ?_⟩, ?_⟩
    · decide +kernel
    · ext e
      revert e
      simp only [Set.mem_ofPred_eq]
      decide +kernel

theorem fig2Net_cover : GallCover fig2Net fig2Ac fig2Vc :=
  GallCover.of_cycle fig2Net_cycle
    (fun e v => if e = 8 then decide (5 ≤ v.val ∧ v.val ≤ 9 ∨ 13 ≤ v.val) else if e = 10 then decide (6 ≤ v.val ∧ v.val ≤ 9 ∨ 14 ≤ v.val) else decide (v = fig2Net.tgt e))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fig2Net_fullyDecomposed : fig2Net.IsFullyDecomposedFor (incompatGraph fig2Rows) :=
  fig2Net_cover.isFullyDecomposedFor₂ (tbl [0, 1, 0, 0, 1] : Fin 5 → Fin 2)
    (by unfold Incompatible; decide +kernel) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem fig2Net_efficient : fig2Net.IsEfficient :=
  fig2Net_cover.isEfficient (by decide +kernel) (by decide +kernel)

theorem fig2Net_degree : ∀ v, (fig2Net.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, fig2Net.IsLeaf l ∧ fig2Net.toBlobNode l = v :=
  fig2Net_cover.degree_cond₂ (tbl [5, 5, 5, 5, 5, 8, 15, 15, 15, 15]) (tbl [6, 6, 6, 6, 6, 9, 16, 16, 16, 16]) (tbl [7, 7, 7, 7, 7, 10, 17, 17, 17, 17])
    (tbl [10, 10, 10, 10, 10, 2, 14, 14, 14, 14]) (tbl [11, 11, 11, 11, 11, 13, 15, 15, 15, 15]) (tbl [12, 12, 12, 12, 12, 6, 16, 16, 16, 16]) (by decide +kernel)

theorem fig2Net_hr : ∀ e f, e ≠ f → fig2Net.tgt e = fig2Net.tgt f → ∃ g, fig2Net.src g = fig2Net.tgt e := by decide +kernel

theorem fig2Net_hl : ∀ e, fig2Ac e = none → fig2Vc (fig2Net.src e) = none → fig2Vc (fig2Net.tgt e) = none →
    (∃ g, fig2Net.src g = fig2Net.tgt e) → ∃ i, fig2Net.site i = e := by
  decide +kernel

theorem fig2Net_htop : ∀ k e w, fig2Vc (fig2Net.src e) = some k → fig2Vc (fig2Net.tgt e) ≠ some k → fig2Vc w = some k →
    (∀ f, fig2Ac f = some k → fig2Net.tgt f ≠ w) → w ≠ fig2Net.root → ∃ i, fig2Ac (fig2Net.site i) = some k ∧
      fig2Net.label (fig2Net.src e) i ≠ fig2Net.label w i := by
  decide +kernel

/-- The super-character `00` of the sites 1, 4 (2, 5 in the paper) is in a row and at no external node of its blob. -/
theorem fig2Net_noPort : (∃ r ∈ fig2Rows, r 1 = false ∧ r 4 = false) ∧ fig2Ac (fig2Net.site 1) = some 1 ∧ fig2Ac (fig2Net.site 4) = some 1 ∧
    ∀ v, fig2Vc v = some 1 → (∃ e, fig2Net.src e = v ∧ fig2Vc (fig2Net.tgt e) ≠ some 1) → ¬ (fig2Net.label v 1 = false ∧ fig2Net.label v 4 = false) := by
  decide +kernel

/-! ### Section 4.2: more examples for the positive form -/

/-- The rows `00, 01, 10`, in a blob that has only the compatible site 0, with a row at its top: not fully decomposed, and not efficient, though `T′` is `T̄`. -/
def threeBlobNet : Network (Fin 2) (Fin 7) (Fin 7) :=
  mkNet (tbl [0, 0, 1, 2, 0, 1, 3]) (tbl [1, 2, 3, 3, 4, 5, 6]) 0 (tbl [0, 4])
    (bitsOf [[0, 0], [1, 0], [0, 0], [0, 0], [0, 1], [1, 0], [0, 0]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def threeBlobAc : Fin 7 → Option (Fin 1) := colourOf [1, 1, 1, 1]
def threeBlobVc : Fin 7 → Option (Fin 1) := colourOf [1, 1, 1, 1]

theorem threeBlobNet_derives : threeBlobNet.Derives threeRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem threeBlobNet_obeys (c : Crossover) : threeBlobNet.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem threeBlobNet_cover : GallCover threeBlobNet threeBlobAc threeBlobVc :=
  GallCover.of_decide (fun _ => 0) (fun _ => 2) (fun _ => 1) (fun _ => 3) (fun e v => decide (v = threeBlobNet.tgt e)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem threeBlobNet_degree : ∀ v, (threeBlobNet.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, threeBlobNet.IsLeaf l ∧ threeBlobNet.toBlobNode l = v :=
  threeBlobNet_cover.degree_cond (fun _ => 4) (fun _ => 5) (fun _ => 6) (by decide +kernel)

theorem threeBlobNet_hr : ∀ e f, e ≠ f → threeBlobNet.tgt e = threeBlobNet.tgt f → ∃ g, threeBlobNet.src g = threeBlobNet.tgt e := by decide +kernel

theorem threeBlobNet_hl : ∀ e, threeBlobAc e = none → threeBlobVc (threeBlobNet.src e) = none → threeBlobVc (threeBlobNet.tgt e) = none →
    (∃ g, threeBlobNet.src g = threeBlobNet.tgt e) → ∃ i, threeBlobNet.site i = e := by
  decide +kernel

/-- The arcs at the blob are pendant exits, and the sites of the blob are the site 0. -/
theorem threeBlobNet_ports : (∀ e, threeBlobVc (threeBlobNet.src e) = some 0 → threeBlobVc (threeBlobNet.tgt e) ≠ some 0 → ∀ g, threeBlobNet.src g ≠ threeBlobNet.tgt e) ∧
    (∀ e, threeBlobVc (threeBlobNet.tgt e) = some 0 → threeBlobVc (threeBlobNet.src e) = some 0) ∧ ∀ i, threeBlobAc (threeBlobNet.site i) = some 0 ↔ i = 0 := by
  decide +kernel

theorem threeRows_compatible : ∀ i j, ¬ Incompatible threeRows i j := by
  unfold Incompatible
  decide +kernel

theorem threeBlobAc_card : Fintype.card {e // threeBlobAc e = none} = 3 := by decide +kernel

theorem threeBlobNet_not_isEfficient : ¬ threeBlobNet.IsEfficient := by
  intro he
  have hB := threeBlobNet_cover.isBlob_color 0
  have hext : ∀ {v : Fin 7} {e : Fin 7}, threeBlobVc v = some 0 → threeBlobNet.src e = v → threeBlobVc (threeBlobNet.tgt e) ≠ some 0 → threeBlobNet.IsExternal {f | threeBlobAc f = some 0} v :=
    fun hv he' ht => ⟨threeBlobNet_cover.mem_blobVerts_iff.2 hv, _, he', fun hm => ht (threeBlobNet_cover.mem_blobVerts_iff.1 hm)⟩
  have h₀ := he.label_inj _ _ 0 3 hB hB (hext (e := 4) (by decide) (by decide) (by decide)) (hext (e := 6) (by decide) (by decide) (by decide)) (by decide +kernel)
  exact absurd h₀ (by decide)

theorem threeBlobNet_not_fullyDecomposed : ¬ threeBlobNet.IsFullyDecomposedFor (incompatGraph threeRows) := by
  intro hf
  refine hf.isolated_treeArc 0 (fun j => threeRows_compatible 0 j) ?_
  exact (threeBlobNet_cover.onCycle_iff _).2 ⟨0, by decide⟩

/-- The rows `000, 010, 100, 110, 111`. -/
def pendantRows : Finset (Fin 3 → Bool) :=
  {ofBits [0, 0, 0], ofBits [0, 1, 0], ofBits [1, 0, 0], ofBits [1, 1, 0], ofBits [1, 1, 1]}

/-- Two pendant arcs at one node of the blob: not efficient, and `T′` is a contraction of `T̄`. -/
def pendantNet : Network (Fin 3) (Fin 9) (Fin 9) :=
  mkNet (tbl [0, 0, 1, 2, 0, 1, 2, 3, 3]) (tbl [1, 2, 3, 3, 4, 5, 6, 7, 8]) 0 (tbl [1, 0, 8])
    (bitsOf [[0, 0, 0], [0, 1, 0], [1, 0, 0], [1, 1, 0], [0, 0, 0], [0, 1, 0], [1, 0, 0], [1, 1, 0], [1, 1, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The same with a hub: `T′` is `T̄`. -/
def pendantHubNet : Network (Fin 3) (Fin 10) (Fin 10) :=
  mkNet (tbl [0, 0, 1, 2, 3, 0, 1, 2, 4, 4]) (tbl [1, 2, 3, 3, 4, 5, 6, 7, 8, 9]) 0 (tbl [1, 0, 9])
    (bitsOf [[0, 0, 0], [0, 1, 0], [1, 0, 0], [1, 1, 0], [1, 1, 0], [0, 0, 0], [0, 1, 0], [1, 0, 0], [1, 1, 0], [1, 1, 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def pendantAc : Fin 9 → Option (Fin 1) := colourOf [1, 1, 1, 1]
def pendantVc : Fin 9 → Option (Fin 1) := colourOf [1, 1, 1, 1]
def pendantHubAc : Fin 10 → Option (Fin 1) := colourOf [1, 1, 1, 1]
def pendantHubVc : Fin 10 → Option (Fin 1) := colourOf [1, 1, 1, 1]

theorem pendantNet_derives : pendantNet.Derives pendantRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pendantHubNet_derives : pendantHubNet.Derives pendantRows :=
  derives_of_decide _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pendantNet_obeys (c : Crossover) : pendantNet.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem pendantHubNet_obeys (c : Crossover) : pendantHubNet.Obeys c := obeys_of_decide _ (by decide +kernel) (by decide +kernel) c

theorem pendantNet_cover : GallCover pendantNet pendantAc pendantVc :=
  GallCover.of_decide (fun _ => 0) (fun _ => 2) (fun _ => 1) (fun _ => 3) (fun e v => decide (v = pendantNet.tgt e)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem pendantHubNet_cover : GallCover pendantHubNet pendantHubAc pendantHubVc :=
  GallCover.of_decide (fun _ => 0) (fun _ => 2) (fun _ => 1) (fun _ => 3)
    (fun e v => if e = 4 then decide (v.val = 4 ∨ 8 ≤ v.val) else decide (v = pendantHubNet.tgt e)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pendantNet_fullyDecomposed : pendantNet.IsFullyDecomposedFor (incompatGraph pendantRows) :=
  pendantNet_cover.isFullyDecomposedFor (tbl [0, 0, 1] : Fin 3 → Fin 2)
    (by unfold Incompatible; decide +kernel) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem pendantHubNet_fullyDecomposed : pendantHubNet.IsFullyDecomposedFor (incompatGraph pendantRows) :=
  pendantHubNet_cover.isFullyDecomposedFor (tbl [0, 0, 1] : Fin 3 → Fin 2)
    (by unfold Incompatible; decide +kernel) (by unfold Incompatible; decide +kernel) (by decide +kernel) (by unfold Incompatible; decide +kernel)

theorem pendantHubNet_efficient : pendantHubNet.IsEfficient :=
  pendantHubNet_cover.isEfficient (by decide +kernel) (by decide +kernel)

theorem pendantNet_degree : ∀ v, (pendantNet.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, pendantNet.IsLeaf l ∧ pendantNet.toBlobNode l = v :=
  pendantNet_cover.degree_cond (fun _ => 4) (fun _ => 5) (fun _ => 6) (by decide +kernel)

theorem pendantHubNet_degree : ∀ v, (pendantHubNet.blobbedTree.neighborSet v).ncard ≤ 2 → ∃ l, pendantHubNet.IsLeaf l ∧ pendantHubNet.toBlobNode l = v :=
  pendantHubNet_cover.degree_cond₂ (tbl [5, 5, 5, 5, 4]) (tbl [6, 6, 6, 6, 8]) (tbl [7, 7, 7, 7, 9]) (tbl [5, 5, 5, 5, 3]) (tbl [6, 6, 6, 6, 8]) (tbl [7, 7, 7, 7, 9]) (by decide +kernel)

theorem pendantNet_hr : ∀ e f, e ≠ f → pendantNet.tgt e = pendantNet.tgt f → ∃ g, pendantNet.src g = pendantNet.tgt e := by decide +kernel

theorem pendantHubNet_hr : ∀ e f, e ≠ f → pendantHubNet.tgt e = pendantHubNet.tgt f → ∃ g, pendantHubNet.src g = pendantHubNet.tgt e := by decide +kernel

theorem pendantNet_hl : ∀ e, pendantAc e = none → pendantVc (pendantNet.src e) = none → pendantVc (pendantNet.tgt e) = none →
    (∃ g, pendantNet.src g = pendantNet.tgt e) → ∃ i, pendantNet.site i = e := by
  decide +kernel

theorem pendantHubNet_hl : ∀ e, pendantHubAc e = none → pendantHubVc (pendantHubNet.src e) = none → pendantHubVc (pendantHubNet.tgt e) = none →
    (∃ g, pendantHubNet.src g = pendantHubNet.tgt e) → ∃ i, pendantHubNet.site i = e := by
  decide +kernel

theorem pendantHubNet_htop : ∀ k e w, pendantHubVc (pendantHubNet.src e) = some k → pendantHubVc (pendantHubNet.tgt e) ≠ some k → pendantHubVc w = some k →
    (∀ f, pendantHubAc f = some k → pendantHubNet.tgt f ≠ w) → w ≠ pendantHubNet.root → ∃ i, pendantHubAc (pendantHubNet.site i) = some k ∧
      pendantHubNet.label (pendantHubNet.src e) i ≠ pendantHubNet.label w i := by
  decide +kernel

theorem pendantNet_ports : (∀ e, pendantVc (pendantNet.src e) = some 0 → pendantVc (pendantNet.tgt e) ≠ some 0 → ∀ g, pendantNet.src g ≠ pendantNet.tgt e) ∧
    ∀ e, pendantVc (pendantNet.tgt e) = some 0 → pendantVc (pendantNet.src e) = some 0 := by
  decide +kernel

theorem pendantAc_card : Fintype.card {e // pendantAc e = none} = 5 := by decide +kernel

theorem pendantNet_not_isEfficient : ¬ pendantNet.IsEfficient := by
  intro he
  have hs : pendantNet.src 7 ∈ pendantNet.blobVerts {f | pendantAc f = some 0} := pendantNet_cover.mem_blobVerts_iff.2 (by decide)
  have ht : ∀ {e : Fin 9}, pendantVc (pendantNet.tgt e) ≠ some 0 → pendantNet.tgt e ∉ pendantNet.blobVerts {f | pendantAc f = some 0} :=
    fun h hm => h (pendantNet_cover.mem_blobVerts_iff.1 hm)
  have h₀ := he.exit_unique _ 7 8 (pendantNet_cover.isBlob_color 0) hs (ht (by decide)) (by decide) (ht (by decide))
  exact absurd h₀ (by decide)

theorem pendantHubAc_card : Fintype.card {e // pendantHubAc e = none} = 6 := by decide +kernel

end Gusfield2007
