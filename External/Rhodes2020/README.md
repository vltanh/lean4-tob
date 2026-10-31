# Rhodes 2020: the quartet metrization

Source: J. A. Rhodes, *Topological metrizations of trees, and new quartet methods of tree inference*,
IEEE/ACM Trans. Comput. Biol. Bioinform. 17 (2020), 2107–2118,
<https://doi.org/10.1109/TCBB.2019.2917204> (read in PMC7650847).

TINNiK uses its Theorem 2 and the fact that internal edges have weight at least 2 (proof of Theorem 4).
`theorem2` and `quartetWeight_ge_two` prove them. `exists_isExactBuilder` is Buneman's uniqueness of the
tree of a tree metric, which shows that the class of distance-based methods in `TINNiK.theorem4` is
nonempty.
