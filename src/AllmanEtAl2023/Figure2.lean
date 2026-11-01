module

public import AllmanEtAl2023.Figure1

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Figures 2L and 2C

The caption of Figure 2: "Examples of blobs in networks. Red indicates hybrid nodes, and hybrid edges above them. Cut edges incident to the blobs are represented by dotted line segments: L a planar 5-blob, C a non-planar 4-blob, R a single 2-blob in a non-binary network, formed from two 2-cycles sharing a single node". Figure 2R is `Figures.fig2R_blob`.

The figures draw a blob with dotted cut edges. Here each is a rooted binary phylogenetic network, read from the figure, with a taxon at the end of each dotted edge, and a root above the top one with one more taxon. `fig2L_blob` and `fig2C_blob` are the blobs and their degrees, by the certificates of `FigureCheck.BlobCert`, and `fig2L_edges` and `fig2C_edges` say which edges are in them.

"Planar" and "non-planar" describe the drawn blobs, and nothing depends on them. They have a small definition here. A *rotation system* of a graph is a cyclic order of the edges at each node, and it traces faces; a connected graph is planar exactly when some rotation system has `V - E + F = 2`, genus 0. The nodes of these blobs have degree at most 3, where a cyclic order is one of two orientations: `Rotation.IsPlanar` is that definition, for such graphs, on the edges of the blob.

* `fig2L_planar`: a rotation system of genus 0 for the blob of Figure 2L, as a certificate.
* `fig2C_not_planar`: for the blob of Figure 2C, no rotation system has genus 0. It is a finite check of the 256 orientations of its eight nodes of degree 3. Its largest number of faces is 4, where genus 0 needs 6.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph

namespace AllmanEtAl2023.FigureCheck.Rotation

variable {n k : ℕ}

/-- A dart: an edge with a direction. `false` is from the source of the edge. -/
abbrev Dart (k : ℕ) := Fin k × Bool

/-- The node a dart starts from. -/
def origin (src tgt : Fin k → Fin n) (d : Dart k) : Fin n := if d.2 then tgt d.1 else src d.1

/-- The dart in the other direction. -/
def rev (d : Dart k) : Dart k := (d.1, !d.2)

/-- All darts. -/
def allDarts (k : ℕ) : List (Dart k) := (List.finRange k).flatMap fun e => [(e, false), (e, true)]

/-- The darts at a node, in a fixed order. -/
def dartsAt (src tgt : Fin k → Fin n) (v : Fin n) : List (Dart k) := (allDarts k).filter fun d => origin src tgt d = v

/-- The next dart at its node, with `l₀` the darts at each node. -/
def nextOf (l₀ : Fin n → List (Dart k)) (src tgt : Fin k → Fin n) (b : Bool) (d : Dart k) : Dart k :=
  let l := l₀ (origin src tgt d)
  let l' := if b then l.reverse else l
  l'.nextOr d (l'.headD d)

/-- The next dart at its node, in the fixed cyclic order or in its reverse. At a node of degree at most 3 these are all the cyclic orders. -/
def nextAt (src tgt : Fin k → Fin n) (b : Bool) (d : Dart k) : Dart k := nextOf (dartsAt src tgt) src tgt b d

/-- A rotation system, by an orientation `o` at each node: the next dart. -/
def nextDart (src tgt : Fin k → Fin n) (o : Fin n → Bool) (d : Dart k) : Dart k := nextAt src tgt (o (origin src tgt d)) d

/-- Tracing a face: go along the dart, and turn at its end. -/
def faceStep (src tgt : Fin k → Fin n) (o : Fin n → Bool) (d : Dart k) : Dart k := nextDart src tgt o (rev d)

/-- The number that orders the darts. -/
def key (d : Dart k) : ℕ := 2 * d.1.1 + d.2.toNat

/-- `d` is the least dart of its orbit, starting from `x` on it. -/
def orbitLeast (φ : Dart k → Dart k) : ℕ → Dart k → Dart k → Bool
  | 0, _, _ => true
  | f + 1, x, d =>
    let y := φ x
    if y = d then true else if key y < key d then false else orbitLeast φ f y d

/-- The number of faces of a rotation system: the orbits of `faceStep`, by their least darts. -/
def faces (src tgt : Fin k → Fin n) (o : Fin n → Bool) : ℕ :=
  ((allDarts k).filter fun d => orbitLeast (faceStep src tgt o) (2 * k) d d).length

/-- The number of faces, with `l₀` the darts at each node: a table, for computation. -/
def facesOf (l₀ : Fin n → List (Dart k)) (src tgt : Fin k → Fin n) (o : Fin n → Bool) : ℕ :=
  ((allDarts k).filter fun d => orbitLeast (fun x => nextOf l₀ src tgt (o (origin src tgt (rev x))) (rev x)) (2 * k) d d).length

theorem faces_eq_facesOf {src tgt : Fin k → Fin n} {l₀ : Fin n → List (Dart k)} (h : dartsAt src tgt = l₀) (o : Fin n → Bool) :
    faces src tgt o = facesOf l₀ src tgt o := by
  subst h
  rfl

/-- The number of nodes of the graph, those on an edge. -/
def nodeCount (src tgt : Fin k → Fin n) : ℕ := ((allDarts k).map (origin src tgt)).dedup.length

/-- **Planar, for a connected graph with nodes of degree at most 3**: a rotation system of genus 0, with `V - E + F = 2`. -/
def IsPlanar (src tgt : Fin k → Fin n) : Prop := ∃ o, nodeCount src tgt + faces src tgt o = k + 2

/-- The number of faces depends only on the orientation at the nodes where it matters. -/
theorem faces_eq_of_orientation {src tgt : Fin k → Fin n} {cubic : Finset (Fin n)} (hs : ∀ d : Dart k, origin src tgt d ∉ cubic → nextAt src tgt true d = nextAt src tgt false d)
    {o o' : Fin n → Bool} (ho : ∀ v ∈ cubic, o v = o' v) : faces src tgt o = faces src tgt o' := by
  have hn : ∀ d, nextDart src tgt o d = nextDart src tgt o' d := by
    intro d
    unfold nextDart
    by_cases hd : origin src tgt d ∈ cubic
    · rw [ho _ hd]
    · have h := hs d hd
      cases o (origin src tgt d) <;> cases o' (origin src tgt d)
      · rfl
      · exact h.symm
      · exact h
      · rfl
  have hstep : faceStep src tgt o = faceStep src tgt o' := by
    funext d
    exact hn _
  unfold faces
  rw [hstep]

end AllmanEtAl2023.FigureCheck.Rotation

namespace AllmanEtAl2023.Figures

open InPassing FigureCheck FigureCheck.Rotation

/-! ### Figure 2L -/

section Fig2L

/-- The sources of the edges of the network of Figure 2L. The taxa are `0, …, 4`: at the left, right and lower left dotted edges, the bottom one, and at the root. The nodes are `H₃ = 5`, `W = 6`, `H₂ = 7`, `H₁ = 8`, `R₂ = 9`, `M = 10`, `L = 11`, `R₁ = 12`, the top `T = 13`, the root `14`. -/
def src2L : Fin 17 → Fin 15 := ![14, 14, 13, 13, 12, 12, 11, 11, 10, 10, 9, 9, 8, 6, 6, 7, 5]

/-- The targets of the edges of the network of Figure 2L. -/
def tgt2L : Fin 17 → Fin 15 := ![13, 4, 11, 12, 9, 10, 0, 8, 8, 7, 1, 7, 6, 2, 5, 5, 3]

/-- **The network of Figure 2L.** -/
def fig2L : RootedNetwork (Fin 15) (Fin 17) (Fin 5) := finNetwork src2L tgt2L 14 (Fin.castLE (by norm_num))

theorem isBinaryNetwork_fig2L : IsBinaryNetwork fig2L :=
  isBinaryNetwork_finNetwork (by decide +kernel) (by decide +kernel) (by decide +kernel) (Fin.castLE_injective _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The edges of the blob of Figure 2L. -/
def blob2L : Fin 11 → Fin 17 := ![2, 3, 4, 5, 7, 8, 9, 11, 12, 14, 15]

/-- The blob, as a graph: its sources. -/
def src2Lb : Fin 11 → Fin 15 := ![13, 13, 12, 12, 11, 10, 10, 9, 8, 6, 7]

/-- The blob, as a graph: its targets. -/
def tgt2Lb : Fin 11 → Fin 15 := ![11, 12, 9, 10, 8, 8, 7, 7, 6, 5, 5]

/-- The blobs of Figure 2L: the nodes `5, …, 13` have one colour. -/
def col2L : Fin 15 → Fin 15 := ![0, 1, 2, 3, 4, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14]

/-- The sets that the cut edges of Figure 2L alone cross. -/
def side2L (e : Fin 17) : Finset (Fin 15) :=
  if e = 0 then {14, 4} else if e = 1 then {4} else if e = 6 then {0} else if e = 10 then {1} else if e = 13 then {2} else if e = 16 then {3} else ∅

theorem blobCert2L : BlobCert src2L tgt2L col2L side2L 5 := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **"A ... 5-blob"** (`a:claim:fig2-blobs`, the caption of Figure 2): the blob of the top node isn't a node, and has degree 5. -/
theorem fig2L_blob : ¬ IsTrivialBlob fig2L.graph (blobOf fig2L.graph 13) ∧ blobDegree fig2L (blobOf fig2L.graph 13) = 5 := by
  refine ⟨mt blobCert2L.isTrivialBlob_iff.1 (by decide +kernel), ?_⟩
  rw [show blobDegree fig2L (blobOf fig2L.graph 13) = _ from blobCert2L.blobDegree_blobOf 13]
  decide +kernel

/-- **The edges of the blob of Figure 2L** are those that aren't cut edges. -/
theorem fig2L_edges : (∀ e, ¬ fig2L.graph.underlying.IsBridge e ↔ ∃ i, blob2L i = e) ∧ (∀ i, src2L (blob2L i) = src2Lb i ∧ tgt2L (blob2L i) = tgt2Lb i) := by
  refine ⟨fun e => ?_, by decide +kernel⟩
  have h : ∀ e : Fin 17, col2L (src2L e) = col2L (tgt2L e) ↔ ∃ i, blob2L i = e := by decide +kernel
  exact (not_congr blobCert2L.isBridge_iff).trans (not_not.trans (h e))

/-- **"A planar 5-blob"** (`a:claim:fig2-planar`, the caption of Figure 2): a rotation system of genus 0 for the blob of Figure 2L. -/
theorem fig2L_planar : IsPlanar src2Lb tgt2Lb :=
  ⟨![false, false, false, false, false, false, false, false, false, false, true, false, false, false, false], by decide +kernel⟩

end Fig2L

/-! ### Figure 2C -/

section Fig2C

/-- The sources of the edges of the network of Figure 2C. The taxa are `0, …, 3`: at the left, right and bottom dotted edges, and at the root. The nodes are `H₅ = 4`, `H₄ = 5`, `H₂ = 6`, `H₃ = 7`, `F = 8`, `D = 9`, `G = 10`, `H₁ = 11`, `E = 12`, `C = 13`, `B = 14`, the top `A = 15`, the root `16`. -/
def src2C : Fin 21 → Fin 17 := ![16, 16, 15, 15, 14, 14, 13, 13, 9, 9, 12, 12, 8, 8, 10, 10, 11, 6, 7, 5, 4]

/-- The targets of the edges of the network of Figure 2C. -/
def tgt2C : Fin 21 → Fin 17 := ![15, 3, 14, 13, 9, 12, 8, 11, 0, 6, 11, 7, 1, 5, 6, 7, 10, 4, 5, 4, 2]

/-- **The network of Figure 2C.** -/
def fig2C : RootedNetwork (Fin 17) (Fin 21) (Fin 4) := finNetwork src2C tgt2C 16 (Fin.castLE (by norm_num))

theorem isBinaryNetwork_fig2C : IsBinaryNetwork fig2C :=
  isBinaryNetwork_finNetwork (by decide +kernel) (by decide +kernel) (by decide +kernel) (Fin.castLE_injective _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The edges of the blob of Figure 2C. -/
def blob2C : Fin 16 → Fin 21 := ![2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19]

/-- The blob, as a graph: its sources. -/
def src2Cb : Fin 16 → Fin 17 := ![15, 15, 14, 14, 13, 13, 9, 12, 12, 8, 10, 10, 11, 6, 7, 5]

/-- The blob, as a graph: its targets. -/
def tgt2Cb : Fin 16 → Fin 17 := ![14, 13, 9, 12, 8, 11, 6, 11, 7, 5, 6, 7, 10, 4, 5, 4]

/-- The blobs of Figure 2C: the nodes `4, …, 15` have one colour. -/
def col2C : Fin 17 → Fin 17 := ![0, 1, 2, 3, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16]

/-- The sets that the cut edges of Figure 2C alone cross. -/
def side2C (e : Fin 21) : Finset (Fin 17) :=
  if e = 0 then {16, 3} else if e = 1 then {3} else if e = 8 then {0} else if e = 12 then {1} else if e = 20 then {2} else ∅

theorem blobCert2C : BlobCert src2C tgt2C col2C side2C 5 := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **"A ... 4-blob"** (`a:claim:fig2-blobs`, the caption of Figure 2): the blob of the top node isn't a node, and has degree 4. -/
theorem fig2C_blob : ¬ IsTrivialBlob fig2C.graph (blobOf fig2C.graph 15) ∧ blobDegree fig2C (blobOf fig2C.graph 15) = 4 := by
  refine ⟨mt blobCert2C.isTrivialBlob_iff.1 (by decide +kernel), ?_⟩
  rw [show blobDegree fig2C (blobOf fig2C.graph 15) = _ from blobCert2C.blobDegree_blobOf 15]
  decide +kernel

/-- **The edges of the blob of Figure 2C** are those that aren't cut edges. -/
theorem fig2C_edges : (∀ e, ¬ fig2C.graph.underlying.IsBridge e ↔ ∃ i, blob2C i = e) ∧ (∀ i, src2C (blob2C i) = src2Cb i ∧ tgt2C (blob2C i) = tgt2Cb i) := by
  refine ⟨fun e => ?_, by decide +kernel⟩
  have h : ∀ e : Fin 21, col2C (src2C e) = col2C (tgt2C e) ↔ ∃ i, blob2C i = e := by decide +kernel
  exact (not_congr blobCert2C.isBridge_iff).trans (not_not.trans (h e))

/-- The orientation at the eight nodes of degree 3 of the blob of Figure 2C. -/
def orient2C (b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Bool) : Fin 17 → Bool :=
  ![false, false, false, false, false, b₀, b₁, b₂, false, false, b₃, b₄, b₅, b₆, b₇, false, false]

/-- The darts at the nodes of the blob of Figure 2C. -/
def at2C : Fin 17 → List (Dart 16) := ![[], [], [], [], [(13, true), (15, true)], [(9, true), (14, true), (15, false)], [(6, true), (10, true), (13, false)], [(8, true), (11, true), (14, false)], [(4, true), (9, false)], [(2, true), (6, false)], [(10, false), (11, false), (12, true)], [(5, true), (7, true), (12, false)], [(3, true), (7, false), (8, false)], [(1, true), (4, false), (5, false)], [(0, true), (2, false), (3, false)], [(0, false), (1, false)], []]

theorem dartsAt_2C : dartsAt src2Cb tgt2Cb = at2C := by
  funext v
  revert v
  decide +kernel

/-- The blob of Figure 2C has 12 nodes. -/
theorem nodeCount_2C : nodeCount src2Cb tgt2Cb = 12 := by decide +kernel

/-- The finite check: no orientation at the eight nodes of degree 3 has genus 0, which needs 6 faces. -/
theorem fig2C_orientations : ∀ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Bool, nodeCount src2Cb tgt2Cb + faces src2Cb tgt2Cb (orient2C b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇) ≠ 16 + 2 := by
  have h : ∀ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Bool, facesOf at2C src2Cb tgt2Cb (orient2C b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇) ≠ 6 := by decide +kernel
  intro b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ he
  rw [nodeCount_2C, faces_eq_facesOf dartsAt_2C] at he
  exact h b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ (by omega)

/-- The other nodes have degree at most 2, so their orientation doesn't matter. -/
theorem fig2C_next : ∀ d : Dart 16, origin src2Cb tgt2Cb d ∉ ({5, 6, 7, 10, 11, 12, 13, 14} : Finset (Fin 17)) → nextAt src2Cb tgt2Cb true d = nextAt src2Cb tgt2Cb false d := by
  decide +kernel

/-- **"A non-planar 4-blob"** (`a:claim:fig2-planar`, the caption of Figure 2): no rotation system of the blob of Figure 2C has genus 0, by a check of the orientations at its eight nodes of degree 3. -/
theorem fig2C_not_planar : ¬ IsPlanar src2Cb tgt2Cb := by
  rintro ⟨o, ho⟩
  have hv : ∀ v ∈ ({5, 6, 7, 10, 11, 12, 13, 14} : Finset (Fin 17)), o v = orient2C (o 5) (o 6) (o 7) (o 10) (o 11) (o 12) (o 13) (o 14) v := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hf := faces_eq_of_orientation fig2C_next hv
  exact fig2C_orientations _ _ _ _ _ _ _ _ ((congrArg (nodeCount src2Cb tgt2Cb + ·) hf).symm.trans ho)

end Fig2C

end AllmanEtAl2023.Figures
