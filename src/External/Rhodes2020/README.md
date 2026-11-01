# Rhodes 2020: the quartet metrization

Source: J. A. Rhodes, *Topological metrizations of trees, and new quartet methods of tree inference*,
IEEE/ACM Trans. Comput. Biol. Bioinform. 17 (2020), 2107–2118,
<https://doi.org/10.1109/TCBB.2019.2917204> (read in PMC7650847).

TINNiK uses its Theorem 2 and the fact that internal edges have weight at least 2 (proof of Theorem 4).
`theorem2` and `quartetWeight_ge_two` prove them. `exists_isExactBuilder` is Buneman's uniqueness of the
tree of a tree metric, which shows that the class of distance-based methods in `TINNiK.theorem4` is
nonempty; the source has no proof of it.

`theorem2` follows the source's proof. The nodes on the path between `x` and `y` are
`TreeMetric.pathNodes`: a node is a vertex partition (`IsVertexPartition`), and `blockOf` and
`otherBlocks` give its blocks `A_v`, `B_v` and `C_v^i`. Each quartet of `Q_{x,y}` determines one node.
The count by node gives the source's equations (2) and (3) (`equation_two`, `equation_three`), and
grouping their terms by the edges on the path (`sum_sidePairs_eq`, `sum_sidePairs_compl_eq`) gives the
theorem.

The source has one indexing slip. In the display before equation (2), and in equations (2) and (3), the
sums over the blocks `C_v^i` run up to `k` or `k(v)`, and there are `k - 2` such blocks. With `k - 2` the
proof is correct. The plain text of the PMC page (PMC7650847) lacks the displayed equations; they are in the page's XML.
