module

public import AllmanEtAl2023.Concordance

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the networks `𝒩(k)⁺` of the proof of Proposition 1

"Edges lead from the root to the taxon `d` and to a 3-blob. The other two edges incident to the 3-blob lead to `c`, and to a
cherry of `a, b`. The edge leading to the cherry has length `ε` and joins the blob at a node that can be thought of as the
'root' of an inverted binary subtree of hybrid edges, inverted so that its edges are directed toward this node. This binary
subtree has `2^k` 'leaves', and all internal edges of length `ε`. The 'pendant' edges of this subtree have lengths `ε, ε + M,
ε + 2M, …, ε + (2^k - 1)M`, with the subtree 'leaves' connected by a path of edges all of length `M`. The pendant edges of
the network `𝒩(k)⁺`, and the internal edge leading from the root of `𝒩(k)⁺` to the 3-blob can be given any fixed lengths, but
for concreteness, we make the network ultrametric by choosing the remaining internal edge to have length 1 and the pendant
edges to `a, b, c, d` to be of lengths `1, 1, 1 + (k + 1)ε, 2 + (k + 1)ε + (2^k - 1)M`, respectively. We set all
hybridization parameters equal to `1/2`."

The lengths of the pendant edges are the arXiv version's. The PMC manuscript prints "`1, 1, 1 + (k + 1)ε + (2^k - 1)M`", three
lengths for four edges, a misprint: Figure 6 has the arXiv lengths, which make the network ultrametric, as the sentence says. The journal's text wasn't read.

The nodes of the inverted subtree are numbered as a binary heap: `1` is its 'root', the node `n` has parents `2n` and
`2n + 1`, and the 'leaves' are `2^k, …, 2^(k+1) - 1`, in the order of the path. The node numbered `n` is `Vertex.heap (n - 1)`.
The paper has `k ∈ ℤ⁺`; `k = 0` makes sense here too, and is a tree.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023.NetworkNk

/-- The nodes of `𝒩(k)⁺` on the taxa `X`. -/
inductive Vertex (k : ℕ) (X : Type*)
  /-- The root. -/
  | root
  /-- The parent of `a` and `b`. -/
  | cherry
  /-- A node of the inverted subtree, by its heap number minus one. -/
  | heap (n : Fin (2 ^ (k + 1) - 1))
  /-- A taxon. -/
  | taxon (x : X)

/-- The edges of `𝒩(k)⁺`. -/
inductive Edge (k : ℕ)
  /-- The edge from the root to the taxon `d`. -/
  | rootTaxon
  /-- The internal edge from the root to the 3-blob, at the top 'leaf' of the inverted subtree. -/
  | rootTop
  /-- The edge of the path between 'leaves' from `2^k + t + 1` to `2^k + t`. -/
  | step (t : Fin (2 ^ k - 1))
  /-- The edge from the lowest 'leaf' of the inverted subtree to the taxon `c`. -/
  | bottomTaxon
  /-- The hybrid edge of the inverted subtree from the node `m + 2` to the node `(m + 2) / 2`. -/
  | tree (m : Fin (2 ^ (k + 1) - 2))
  /-- The edge from the 'root' of the inverted subtree to the cherry. -/
  | stem
  /-- The edge from the cherry to `a`. -/
  | cherryLeft
  /-- The edge from the cherry to `b`. -/
  | cherryRight

variable {X : Type*} (k : ℕ)

theorem two_le_two_pow_succ : 2 ≤ 2 ^ (k + 1) := by
  rw [pow_succ]
  have := Nat.one_le_two_pow (n := k)
  omega

theorem one_le_two_pow_k : 1 ≤ 2 ^ k := Nat.one_le_two_pow

theorem two_pow_succ_eq : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [pow_succ]
  omega

variable {k}

/-- The node of the inverted subtree with heap number `n`. -/
def heapNode (n : ℕ) (h₁ : 1 ≤ n) (h₂ : n < 2 ^ (k + 1)) : Vertex k X :=
  .heap ⟨n - 1, by omega⟩

/-- The graph of `𝒩(k)⁺`, on the taxa `X` with names `a, b, c, d` (see `networkNk`). -/
def graphNk (k : ℕ) (a b c d : X) : DirectedMultigraph (Vertex k X) (Edge k) where
  source
    | .rootTaxon => .root
    | .rootTop => .root
    | .step t => heapNode (2 ^ k + t.1 + 1) (by omega) (by
        have := t.2
        have := two_pow_succ_eq k
        have := one_le_two_pow_k k
        omega)
    | .bottomTaxon => heapNode (2 ^ k) (one_le_two_pow_k k) (by
        have := two_pow_succ_eq k
        have := one_le_two_pow_k k
        omega)
    | .tree m => heapNode (m.1 + 2) (by omega) (by
        have := m.2
        have := two_le_two_pow_succ k
        omega)
    | .stem => heapNode 1 le_rfl (by
        have := two_le_two_pow_succ k
        omega)
    | .cherryLeft => .cherry
    | .cherryRight => .cherry
  target
    | .rootTaxon => .taxon d
    | .rootTop => heapNode (2 ^ (k + 1) - 1) (by
        have := two_le_two_pow_succ k
        omega) (by
        have := two_le_two_pow_succ k
        omega)
    | .step t => heapNode (2 ^ k + t.1) (by
        have := one_le_two_pow_k k
        omega) (by
        have := t.2
        have := two_pow_succ_eq k
        have := one_le_two_pow_k k
        omega)
    | .bottomTaxon => .taxon c
    | .tree m => heapNode ((m.1 + 2) / 2) (by omega) (by
        have := m.2
        have := two_le_two_pow_succ k
        omega)
    | .stem => .cherry
    | .cherryLeft => .taxon a
    | .cherryRight => .taxon b

/-- **The network `𝒩(k)⁺`** (`a:def:Nk`) of the proof of Proposition 1, on the taxa `X` with names `a, b, c, d`, topological. -/
def networkNk (k : ℕ) (a b c d : X) : RootedNetwork (Vertex k X) (Edge k) X where
  graph := graphNk k a b c d
  root := .root
  leaf := .taxon

/-- **The numerical parameters of `𝒩(k)⁺`**, with the variable lengths `ε` and `M`. All hybridization parameters are `1/2`. -/
def metricNk (k : ℕ) (ε M : ℝ) : MetricData (Edge k) where
  length
    | .rootTaxon => 2 + (k + 1) * ε + (2 ^ k - 1) * M
    | .rootTop => 1
    | .step _ => M
    | .bottomTaxon => 1 + (k + 1) * ε
    | .tree m => if m.1 + 2 < 2 ^ k then ε else ε + (((m.1 + 2 - 2 ^ k : ℕ) : ℝ) * M)
    | .stem => ε
    | .cherryLeft => 1
    | .cherryRight => 1
  inheritance
    | .tree _ => 1 / 2
    | _ => 1

/-- `𝒩(k)⁺` has finitely many edges. -/
instance : Finite (Edge k) :=
  Finite.of_injective
    (fun e : Edge k => (match e with
      | .rootTaxon => .inl 0
      | .rootTop => .inl 1
      | .step t => .inr (.inl t)
      | .bottomTaxon => .inl 2
      | .tree m => .inr (.inr m)
      | .stem => .inl 3
      | .cherryLeft => .inl 4
      | .cherryRight => .inl 5 : Fin 6 ⊕ (Fin (2 ^ k - 1) ⊕ Fin (2 ^ (k + 1) - 2)))) (by
    intro e e' h
    cases e <;> cases e' <;> simp_all)

instance : Fintype (Edge k) := Fintype.ofFinite _

instance [Finite X] : Finite (Vertex k X) :=
  Finite.of_injective
    (fun v : Vertex k X => (match v with
      | .root => .inl 0
      | .cherry => .inl 1
      | .heap n => .inr (.inl n)
      | .taxon x => .inr (.inr x) : Fin 2 ⊕ (Fin (2 ^ (k + 1) - 1) ⊕ X))) (by
    intro v v' h
    cases v <;> cases v' <;> simp_all)

instance [Finite X] : Fintype (Vertex k X) := Fintype.ofFinite _

end AllmanEtAl2023.NetworkNk
