# No cyclic equilibrium block with four branch vertices

**Theorem.** At $\alpha>n$, every cyclic biconnected equilibrium block
has at least five vertices of block degree at least three.

The earlier [parallel-path theorem](parallel-block-paths.md) gives a
simple graph of minimum degree at least three after suppressing
degree-two paths. Therefore four branch vertices would give a subdivision
of $K_4$. There are no cyclic blocks with fewer branch vertices.

## Finite reduction independent of player count

Choose a maximum-weight attachment $x$. The
[exponential path bound](thread-length-bound.md) and the triangle paths
of $K_4$ give the following length limits.

- If $x$ is a branch vertex, every path length is at most seven.
- If $x$ lies inside a path, each of the two parts of that path has
  length at most eight and every other path has length at most seven.

An eight-cycle in a subdivision of $K_4$ has at most four
vertices of block degree at least three. The exact octagon theorem
therefore gives a girth lower bound of nine. Each simple cycle of the
subdivision comes from one of the four triangles or three quadrilaterals
of $K_4$.

The enumeration covers all six length choices in the branch-root case.
In the other case relabel the path containing $x$ to edge $01$, choose
the two arm lengths independently, and enumerate the five other lengths.
The structural filters are the long-path distance gap, the exponential
bound using the shortest cycle through the path, and the prohibition
of two forced penultimate purchases toward the same endpoint. These
filters also apply to the split paths ending at $x$. Each graph is
retained up to relabelling of its four branch vertices. There are 636
remaining length vectors, with core order at most 32.

## Exact checks over all ownership and attachments

For each retained graph, test every possible location of $x$ that
satisfies the same geometric constraints. A degree-two chain owns its
edges in a word of forward and backward purchases. The propagation
lemma forbids a forward purchase followed at distance two or more by
a backward purchase. The maximum-weight swap forces the purchase
away from $x$ wherever a two-step distance gap occurs at a degree-two
vertex. The checker branches over every remaining word on every path.

Each node of this search knows a partial assignment of purchases.
A row uses any subset of the assigned purchases of one player and at
most one new chord. Purchases outside those sold are held fixed.
Connected deviations therefore yield valid rows for every completion of
the partial assignment. Additional rows record that $x$ has maximum
weight and that $n<\alpha\le2n$ in a non-tree equilibrium.

The numerical solver proposes nonnegative multipliers. A branch closes
only after exact integer verification of one of two inequalities.
Either the combined purchase coefficient is $-c<0$ and every distance
coefficient is at most $c$, implying $\alpha\le\sum w=n$, or the
purchase coefficient is nonpositive and all distance coefficients are
strictly negative, contradicting the positive total weight. Thus a
certificate at an internal search node rules out every orientation
below it and every attachment vector. No upper bound on $n$ is used.
The run checks 949 rooted cases. It verifies 1,435 price certificates
and 52 infeasibility certificates.

Run `python3 research/min-cycles/k4_subdivision_certificates.py` with
NumPy and SciPy. The geometry and integer checks run in Python. Lean
checks the underlying long-path and purchase-forcing inequalities.
