# Song, Hein 2005: an upper bound on `R¹` from a sequence of trees

Source: Y. S. Song, J. Hein, *Constructing minimal ancestral recombination graphs*, J. Comput. Biol. 12 (2005), 147--169, as stated in Gusfield et al. 2007, line 654 (the line numbers of Gusfield et al. are explained in `src/Gusfield2007/README.md`): "For any n by m matrix M, if P = T_1, T_2, ..., T_m is a sequence of time-ordered leaf-labeled trees in which T_i is compatible with site i in M,
for all i = 1, ..., m, then R¹(M) <= L(P)."

**The source couldn't be read.** It's closed (Unpaywall and Semantic Scholar list no open copy, Europe PMC has only the abstract, and the publisher and the Internet Archive gave no copy). So whether its trees are binary couldn't be checked. It doesn't matter for the
statement: `R_le_sprLength` has no such hypothesis and is proved, so it holds for binary trees too, and Figure 10's trees are binary.

Gusfield et al. 2007 use it at line 656, to prove `R¹(M_d) <= 3d` in Theorem 11.

`Bound.lean` proves `R_le_sprLength` by the standard construction of an ancestral recombination graph from a sequence of marginal trees, with `L(P)` in `ℕ∞`, because `d_oSPR` is infinite between trees that no sequence of ordered-SPR operations connects. Going along the sites:

- The network starts as the first tree, with a root above it (`hasState_init`).
- A site is placed on the edge of the current tree above its cluster (`HasState.addSite`). Its state changes at the nodes below that arc, following the arcs to the right of every crossover so far, since the new site is to the right of them.
- An ordered-SPR operation on the cluster `A` is one new recombination node `x` just above the node of `A` (`HasState.spr`, `Realizes.spr`). Its parents are the old parent of the node, on the left of the crossover, and a node at the time of the new parent of `A`, on the right. Since the times of the nodes are kept, and the new parent is
  earlier than `A` (`TimeOrderedTree.time_lt`), this closes no cycle. This is where time-ordered is used.

The state of the construction is `Realizes`: every arc goes forward in time, and a node at time `t` on the path up from a row has below it exactly the rows of the edge of the current tree above that row at time `t` (`lin`). All the nodes on the path are covered, including those of earlier trees, and a time that isn't taken gets a new node (`exists_node_at`).

If the operation returns `A` to the old parent, the new node is an ordinary node and there's no recombination.

Imports: `Gusfield2007.TimeOrdered` for the definitions, `Gusfield2007.NetworkOps` for `PreNet` and for trimming.
