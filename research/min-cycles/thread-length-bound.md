# Bounding degree-two paths in cyclic equilibrium blocks

Let $H$ be a maximal cyclic biconnected block in a sum network creation
equilibrium with $n$ players and price $\alpha>n$. Give each vertex $z$ of
$H$ weight $w(z)$ equal to its attachment size in the full graph. The
weights are positive and sum to $n$. Let $x$ be any maximum-weight
vertex of $H$.

**Path bound.** Suppose $v_0=A,\ldots,v_L=B$ is a simple path in $H$ with
$L\ge5$, whose interior vertices have block degree two and avoid $x$.
Order the endpoints so that $d(A,x)\le d(B,x)$. Every cycle of $H$
containing $v_{L-1}$ has length $c$ satisfying
\[
  3\cdot 2^{L-4} < 2(c-3).
\]

## Geodesics and purchases

Put $d_A=d(A,x)$ and $d_B=d(B,x)$. The long-path gap theorem gives
$d_B-d_A\ge L-3$. In particular $d(A,B)\ge L-3$. Distances from the path
to $x$ are
\[
  d(v_i,x)=\min(i+d_A,L-i+d_B).
\]
This equals $i+d_A$ for $i\le L-2$. For $1\le i\le L-3$, the
two-step swap away from the maximum attachment forces $v_i$ to purchase
$v_iv_{i+1}$. The penultimate-purchase theorem supplies the same ownership
at $i=L-2$. The three-edge geodesic from $v_{L-3}$ to $B$ then forces
$v_{L-1}$ to buy $v_{L-1}B$. The opposite purchase by $B$ would be the
second inward purchase along a three-edge geodesic with degree-two
interior.

For every $1\le i\le j\le L-1$, the path segment from $v_i$ to $v_j$
is geodesic. For $j\le L-2$, the distance difference to $x$ gives a
lower bound of $j-i$, and the segment gives the matching upper bound.
For $j=L-1$ and $i<L-1$, the two-ended distance formula for destination
$B$ gives
\[
  d(v_i,B)=\min(i+d(A,B),L-i)\ge L-2-i.
\]
The degree-two identity at $v_{L-1}$ now gives
\[
  d(v_i,v_{L-1})
  =1+\min(d(v_i,v_{L-2}),d(v_i,B))=L-1-i.
\]
Distances here can be measured in the block because every simple path
between two block vertices stays in the block.

## Doubling and the deletion inequality

For $2\le k\le L-2$, let $v_{k-1}$ replace its purchase of $v_k$ by a
link to $v_{k+1}$. The two-step Nash inequality applies to the entire
suffix because the preceding geodesic calculation gives
$d(v_{k-1},v_j)=2+d(v_{k+1},v_j)$ for $k+1\le j\le L-1$. Therefore
\[
  w(v_k)\ge \sum_{j=k+1}^{L-1}w(v_j).
\]
Write $W_k=\sum_{j=k}^{L-1}w(v_j)$. This gives
$W_k\ge 2W_{k+1}$ and hence $W_3\ge 2^{L-4}w(v_{L-1})$. The weight of
$x$ is at least $w(v_2)$ and $v_2$ is outside the suffix counted by
$W_3$. Since the path interior avoids $x$, the three contributions
are disjoint and
\[
  n\ge w(x)+w(v_2)+W_3\ge3 W_3\ge3\cdot2^{L-4}w(v_{L-1}).
\]
The local degree-two deletion bound on a cycle of length $c$ gives
$\alpha\le2(c-3)w(v_{L-1})$. Its hypotheses hold because $v_{L-2}$
buys $v_{L-2}v_{L-1}$ and $v_{L-1}$ buys $v_{L-1}B$. The detour
proof of this bound uses positive price and a sufficiently long
cycle. Combining the two inequalities with $n<\alpha$ proves the
strict bound.

## Bounded number of branch vertices

Let $b$ count the vertices of block degree at least three and retain
these vertices together with $x$. This gives at most $b+1$ retained
vertices. Contract each maximal degree-two path between retained
vertices to a multigraph edge, marking it with the path length. The
multigraph is loopless because a returning path would make its retained
vertex a cut vertex. Every path belongs to a simple cycle in the
block. Such a cycle projects to a cycle in the multigraph with at most
$b+1$ edges, allowing a cycle of two parallel edges.

Let $L$ be the longest path length in this representation. A cycle
through its last interior vertex has length at most $(b+1)L$. Thus
either $L\le4$ or
\[
  3\cdot2^{L-4}<2((b+1)L-3).
\]
This gives a finite bound on $L$ for each fixed $b$. Before retaining
$x$, the parallel-path exclusion allows at most one parallel pair and
no class of higher multiplicity. Retaining $x$ adds at most one edge
to that multigraph. Thus the order of the block is at most
\[
  b+1+\bigl(\tbinom b2+2\bigr)(L-1).
\]
The bound is independent of the total player count.

For a subdivision of $K_4$, $b=4$ and the length inequality gives
$L\le8$. When $x$ is a branch vertex, each path lies on a triangle of
the suppressed $K_4$. Taking the longest path gives $c\le3L$ and
improves the maximum to seven. When $x$ lies inside one original
path, the other five original paths have length at most seven. In
fact, each of those five lies on a triangle avoiding the split path,
so a longest one among them again has a cycle of length at most
three times its own length. The two parts of the split path have
length at most eight. The total original block order is therefore at
most $4+5(7-1)+(16-1)=49$.

With bounded block order only finitely many graph shapes and ownership
orientations remain. The exact block-with-leaves reduction turns
each into a finite set of linear inequalities in the price and integer
weights, with a finite case split on leaf support. This reduces every
fixed branch bound to a finite decision problem, even when $n$ is
unbounded.
