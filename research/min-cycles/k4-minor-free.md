# The Tree Conjecture for graphs without a K4 minor

**Theorem.** Let $G$ be a Nash equilibrium of the sum network creation
game on $n\ge 1$ players with edge price $α>n$. Every cyclic biconnected
block of $G$ contains $K_4$ as a minor. In particular, every $K_4$-minor-free
equilibrium graph is a tree at this price, for every player count.

## Parallel paths in a block

Let $H$ be a cyclic biconnected block, and choose a vertex $x$ of
maximum attachment mass. A thread is a path between branch vertices
whose interior vertices have block degree two. We show that any pair
of parallel threads with disjoint interiors must contain $x$ in the
interior of one of them.

Suppose both interiors avoid $x$, and write their lengths as $a\le b$.
Their union is a cycle, so $a+b\ge 8$ by
`nash_cycle_length_ge_eight`. Label their common endpoints $A,B$ so
that $d(A,x)\le d(B,x)$, and put
$Δ=d(B,x)-d(A,x)$. If $b\ge5$, `nash_block_long_thread_gap` gives
$b\leΔ+3$. The triangle inequality gives $Δ\le d(A,B)\le a$.
Thus $a\le2$ would imply $a+b\le7$. If $a\in\{3,4\}$, then
$Δ\ge2$ gives $a\leΔ+2$. Both threads therefore qualify for
the forced penultimate purchase toward $B$, either by length at least
five or by length at least three and at most $Δ+2$. The two
purchases contradict `nash_block_no_two_penultimate_path_purchases`.
This is the long case. In the remaining case $a=b=4$.

## Two paths of length four

Their union is a shortest cycle $C$ of length eight, hence isometric
in $H$. Label its endpoints $0,4$, and the other vertices in cyclic
order. Only vertices $0,4$ have neighbors in $H\setminus C$. Each
cycle edge has one buyer because equilibrium at positive price
excludes double purchases.

Give each vertex $v\in H$ the positive weight $w_H(v)$ equal to its
attachment mass in $G$. These weights sum to $n$.
The weighted block reduction gives every vertex of $C$ the Nash
inequality for any connected deviation made inside $H$, using original
distance sum $∑_v w_H(v)d_H(i,v)$ and the same weights after deviation.

Consider deviations by one buyer $i$ that replace their cycle
purchases by zero or one edge to a vertex of $C$. Other purchases are
retained. The changed cycle edges in each certificate form a
connected graph $C'$, as checked by predecessor labels decreasing by
one to $i$. Thus the changed block is connected. The labels $d'_i$
upper bound its distances to the eight cycle vertices, and they all
lie between zero and seven. The old distances to cycle vertices are
the exact cycle distances $d_i$.

For an exterior vertex $z\in H\setminus C$, let $D_j$ be the
distance from portal $j\in\{0,4\}$ to $z$ in $H$ after removing
the six cycle interiors. Disconnected distances are infinite. At
least one portal distance is finite. Every path from $i$ to $z$
has a last portal, and the path after that portal lies in the
residual graph. Concatenating a cycle route with a residual route
proves the reverse inequality. Therefore the original distance is
$μ(d_i)=\min(d_i(0)+D_0,d_i(4)+D_4)$.
The residual graph is unchanged by the deviations, so $μ(d'_i)$
is an upper bound on the new distance.

Subtract $min(D_0,D_4)$ from both expressions. The two residual
offsets become $\max(0,δ)$ and $\max(0,-δ)$ for
$δ=D_0-D_4$, allowing either infinite extreme. Clamping $δ$
to $[-7,7]$ preserves both minima. Whenever an offset is at least
seven, the other portal has offset zero and distance at most seven.
Aggregate the weights $w_H$ into 23 nonnegative columns $w_z$,
eight for cycle vertices and fifteen for exterior offset classes.
The total remains $n$.

For each orientation of the cycle purchases, the certificates give
deviations indexed by $m$. Their price coefficients $a_m$ are
exact, and distance coefficients $b_{mz}$ use exact original
distances and upper bounds on the new distances. Nash therefore
gives $0\le a_mα+∑_z b_{mz}w_z$.
The nonnegative integer multipliers $λ_m$ satisfy
$∑_mλ_m a_m=-c$ with $c>0$ and
$∑_mλ_m b_{mz}\le c$ for every $z$.
Summing the inequalities yields $0\le-cα+cn$, a contradiction.

Lean checks the 256 orientation certificates, their predecessor
conditions, and all 23 coefficient bounds in
`TwoPortalCertificateCheck.lean`. The preceding graph argument
explains how they apply to this block.

## From parallel paths to a minor

The existing block degree theorem gives a branch vertex in $H$.
Suppress all degree-two interiors of threads. The resulting
multigraph $M$ has minimum degree at least three and has no loops.
A thread returning to its own start would make that start a cut
vertex, since it is a branch and the returning thread has no other way
out. Let $F$ be $M$ with parallel edges identified. The graph $F$
is a minor of $H$. If $F$ has at least three vertices it is
2-connected. A path in $H$ with a branch vertex removed projects
to a walk in $F$ avoiding that vertex.

At most one thread contains $x$ internally. If $M$ has two
vertices then it has at least three parallel edges, so two threads
avoid $x$. If it has three vertices then $F$ is a triangle and
$M$ has at least two distinct parallel bundles. One bundle alone
could only raise the degrees of its two endpoints.

Suppose now that $F$ has at least four vertices and is $K_4$-minor
free. The partial 2-tree characterization allows adding edges on
the same vertices to obtain a 2-tree. A 2-tree on at least four
vertices has two nonadjacent degree-two vertices. This follows by
induction from the diamond, since one of two old nonadjacent
degree-two vertices avoids the edge on which the new vertex is
attached. It stays degree two and is nonadjacent to the new vertex.
Those two vertices have degree two in $F$ as well, by
2-connectivity. Both must be incident to a parallel bundle in $M$
to reach multigraph degree three. The bundles are distinct because
the vertices are nonadjacent. At least one of the bundles avoids
$x$ in all its interiors, again giving a forbidden pair.

All possibilities for a $K_4$-minor-free cyclic block contradict the
parallel-path exclusion. Equilibrium graphs with at least one player
are connected. In a $K_4$-minor-free equilibrium every block is
acyclic, and the full graph is a tree.

This also restricts arbitrary blocks. Their suppressed multigraph
can have at most one parallel bundle, which must consist of exactly
two threads, one containing $x$ in its interior.

For the partial 2-tree characterization and completion theorem see
[Designing and Expanding Electrical Networks, §2.3](https://publikationen.bibliothek.kit.edu/1000156516/150409911).

## Octagons in the remaining blocks

At $\alpha>n$, any eight-cycle in a cyclic block has at least six
vertices of block degree at least three. This follows from exact
integer certificates for every orientation with at least three
specified degree-two cycle vertices.

Label the isometric eight-cycle in cyclic order. For a destination
outside the cycle, take its eight old distances in $H$ and subtract
their minimum. The resulting integer labels $l_i$ satisfy
$|l_i-l_{i+1}|\le1$ and $\min_i l_i=0$. Every block degree-two
cycle vertex also satisfies $l_i=1+\min(l_{i-1},l_{i+1})$.
Cycle destinations keep their eight exact cycle distances.

For a deviation by $i$ that deletes some of its cycle purchases
and adds at most one chord, require the changed cycle edges to
connect all eight vertices. To bound the distance change to a
destination with normalized labels $l$, consider its old shortest
paths. If no deleted edge $ij$ has $l_i=l_j+1$, an old shortest
path survives and the change is at most zero. For any $j$ with
$l_j<l_i+d_C(i,j)$, a shortest path from $j$ to the destination
avoids $i$, by isometry. The changed cycle route from $i$ to $j$
and that old shortest path give an upper bound
$d_{C'}(i,j)+l_j-l_i$. Take the minimum of all available bounds.
If no zero bound was used, a deleted first edge of an old
shortest path supplies a valid choice of $j$.

The checker generates all $1{,}107$ normalized exterior distance
types from successive differences in $\{-1,0,1\}$ on the cycle.
For 20 of the 22 dihedral orientation representatives, the
unrestricted types already give a certificate. For each of the
two other orientations, all $\binom83=56$ choices of degree-two
vertices give an exact certificate after the corresponding
exterior types are filtered. The eight cycle types are included
in every case. Each certificate combines connected deviation
inequalities with nonnegative integer coefficients to yield
$\alpha\le n$ for any attachment weights. The checker verifies
these coefficients using exact integer arithmetic.

Reproduce the degree bound with
`python3 research/min-cycles/octagon-degree-bound.py`. The
octagon degree bound is checked by Python. The opposite-portal
certificate used in the minor theorem has its own Lean check.
