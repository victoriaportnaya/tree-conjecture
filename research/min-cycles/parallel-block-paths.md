# Suppressed equilibrium blocks have no parallel edges

Suppose $\alpha>n$. Let $H$ be a cyclic biconnected equilibrium block and
let $x$ have maximum attachment weight in $H$. Suppress the interiors of
the maximal paths whose interior vertices have degree two. The resulting
multigraph is simple and has minimum degree at least three.

## Reducing a parallel pair to finite geometry

The parallel-path theorem in [the minor proof](k4-minor-free.md) shows
that a parallel pair must have $x$ internally on one path. The two paths
join the same branch vertices $A,B$. Write $s,t$ for the two lengths on
the path from $x$ to $A,B$, ordered by $s\le t$, and $r$ for the length
of the other path. Their union is a cycle $C$ of length $c=s+t+r$. The
block girth bound excludes $c<8$, and the octagon degree theorem excludes
$c=8$ because the six interior vertices have degree two.

Put $d_A=d(x,A)$ and $d_B=d(x,B)$. If $D$ is the shortest $A$–$B$
distance avoiding the interior of the path containing $x$, then
\[
  d_A=s,\qquad d_B=\min(t,s+D)\ge d_A.
\]
The path of length $r$ avoids $x$ internally. If $r\ge5$, the long-path
gap theorem gives $d_B-d_A\ge r-3\ge2$, so $t\ge d_B\ge3$. The $x$–$B$
arm forces a penultimate purchase toward $B$. For arm lengths three
or four, the arm is geodesic by girth at least eight, so the short
path gap condition applies. An arm of length at least five uses the
long-path condition directly. The length-$r$ path also forces a
penultimate purchase toward $B$, contradicting the cross-path swap
inequality. Therefore $r\le4$.

The length-$r$ path is geodesic, again by girth. Any excursion from the
cycle inside the block must leave and return through $A,B$. The
length-$r$ path can replace any such excursion without increasing
length. Thus $C$ is isometric and $d_B=\min(t,s+r)$.

If $r$ is three or four and $d_B-d_A\ge r-2$, the length-$r$ path
forces the same conflicting purchase. Here $t\ge3$ follows from
$c\ge9$ and $s\le t$ because $r\le4$. Hence
$d_B-d_A<r-2$ for $r=3,4$.

When $t\ge5$, the exponential
[path bound](thread-length-bound.md) gives
\[
  3\cdot2^{t-4}<2(c-3)\le4t+2.
\]
The inequality fails for every $t\ge8$, by doubling the left side
at each successive $t$. Hence $1\le s\le t\le7$. The long-path gap
also gives $t\le d_B+3$ when $t\ge5$. This leaves exactly 35 triples
$(s,t,r)$.

## Exact certificate check

For each path, use its direction away from $x$, or from $A$ to $B$
for the length-$r$ path. The two inward purchase inequalities
forbid a forward purchase followed two or more positions later by
a backward purchase. For an arm of length at least five, the
long-path argument forces every edge after the first to be bought
forward. For a four-edge arm, the four-path lemma and the
penultimate purchase force the same. For a three-edge arm, the
middle edge is bought forward. For a two-edge arm, the maximum
attachment swap forces its last edge forward. The short arm cases
use that any simple path of length at most four is geodesic.
For $r=4$, the first and last interior vertices buy toward the
far endpoint. At equal endpoint distances they each buy both
of their cycle edges.

Under these restrictions the 35 triples allow 535 orientations.
For each orientation, keep the eight-cycle proof's two-portal
construction, with $c$ cycle columns and $2c-1$ exterior distance
difference classes. The exterior offsets subtract their common
minimum and clamp their signed difference to $[-(c-1),c-1]$.
Every deviation used leaves the changed cycle connected, so all
cycle distances are at most $c-1$ and the clamp preserves the
relevant minimum. The original distances are exact by isometry.
A surviving route in the changed cycle gives an upper bound for
each new distance in the block.

The checker considers unilateral deviations selling any subset
of the buyer's cycle purchases and adding at most one chord. It
also uses the inequalities $w(x)\ge w(v)$ for cycle vertices.
A certificate forms a nonnegative integer combination of these
Nash and weight inequalities. In 381 cases its price coefficient
is $-a<0$ and all distance coefficients are at most $a$. This
gives $\alpha\le n$. In the other 154 cases its price coefficient
is nonpositive and every distance coefficient is negative. The
positive total weight makes those inequalities inconsistent.
The integer verification is exact.

Run `python3 research/min-cycles/parallel_path_certificates.py`
with NumPy and SciPy. SciPy proposes coefficients. Integer
arithmetic checks their signs and every column.

## Consequences

A returning degree-two path is impossible by two-connectivity.
The earlier block-degree theorem excludes cycle blocks. Since
parallel paths are now excluded, suppression gives a simple graph
of minimum degree at least three, with the actual branch vertices
as its vertices. In particular, a cyclic equilibrium block with
exactly four branch vertices would have to be a subdivision of
$K_4$.

# Uniform subdivisions of K4

If every edge of $K_4$ is replaced by a path of the same length
$\ell$, the resulting block is impossible at $\alpha>n$, for any
attachment weights.

For $\ell\le2$ the branch triangles violate girth eight. For
$\ell\ge5$ choose a cycle of the underlying $K_4$ avoiding the
possible edge whose interior contains $x$. At a farthest vertex
of this cycle from $x$, both incident long paths force their
penultimate purchases inward toward that endpoint, a contradiction.

At $\ell=3$, each of the six paths has six possible ownership
words after excluding a forward first purchase and backward last
purchase by the three-edge swap inequality. There are $6^6=46{,}656$
orientations, or 1,956 under relabelling of the four branch vertices.
The exact checker rules out all 1,956 classes.

At $\ell=4$ the maximum-weight vertex cannot be internal. To see
this, place it on the path $AB$ at distance $j\in\{1,2\}$ along
the path from $A$. Its distances to $A,B$ are $j,4-j$.
Its distance to either other branch vertex $Z$ is $4+j$.
The paths $AZ$ and $BZ$ thus have distance gaps four and $2j$,
so their two penultimate purchases toward $Z$ conflict. Relabel
a maximum-weight branch vertex as zero. Its three outgoing paths
have the last three edges bought forward. On each of the other
three paths the endpoints tie in distance from zero, so the
first and last interior vertices buy both incident path edges.
These conditions leave eight orientations, all excluded by exact
certificates.

Run `python3 research/min-cycles/uniform-k4-certificates.py`
with NumPy and SciPy. This check uses weighted Nash inequalities
of connected deviations confined to the block, so it applies at
arbitrary total player count.
