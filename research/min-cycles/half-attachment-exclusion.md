# Exclusion of attachments containing half the players

**Theorem.** In a non-tree equilibrium of the sum network creation game at
price $\alpha>n$, no attachment to any cyclic biconnected block has weight
at least $n/2$.

Fix a cyclic maximal biconnected block $H$. Let $w(z)$ be the number of
players attached at $z$ in $H$, including $z$. The weights are positive
and sum to $n$. For connected deviations within $H$, weighted block
distances give the exact change in the full distance sum. Write
$R=w(r)$ and assume $2R\ge n$ for some $r\in V(H)$.

## The four distance layers

The published tree theorem above $2n$ gives $\alpha\le2n$ in a non-tree
equilibrium. The girth is at least eight by the project's checked
short-cycle exclusions. Put $\ell(v)=d_H(r,v)$.

If $d_H(r,u)=d\ge2$, add the link $ur$. It saves at least $d-1$ per
player attached at $r$. It also saves at least $d-3$ per player attached
at any specified neighbor $y$ of $r$ within $H$. Indeed
$d_H(u,y)\ge d-1$ and the new route from $u$ to $y$ has length two.
Thus $\alpha\ge(d-1)R+(d-3)w(y)$. For $d\ge5$ this would give
$\alpha>4R\ge2n$. Every vertex therefore has level at most four.

Some vertex has level four. Otherwise a breadth-first tree has depth
three and any off-tree edge gives a cycle of length at most seven.
Applying the preceding addition at level four gives $\alpha>3R$.

Every vertex of levels one through three has exactly one neighbor at
the previous level. Two such neighbors would yield a cycle of length
at most six in a breadth-first tree plus one edge. There are no
same-level edges at level at most three, which would similarly yield
a cycle of length at most seven. Adjacent vertices differ in level by
at most one.

## Purchases toward the root

A vertex $u$ with $\ell(u)=d\ge2$ cannot buy an edge to a neighbor $v$
with $\ell(v)=d-1$. Replacing that edge with $ur$ shortens the distance
to $r$ by $d-1$. Every original simple shortest path from $u$ that
does not begin with the deleted edge survives. For any other path,
the first edge can be replaced with the new edge $ur$ followed by
an old shortest route from $r$ to $v$. That route avoids $u$
because its length is $d-1$. Each such distance increases by at
most $d-1$, and the distance to $u$ stays zero. The weighted change
is at most $(d-1)(n-2R-w(u))<0$. This is a cost-neutral swap in
edge count. Consequently every edge from level two to three and
every edge from level three to four is bought by its lower-level
endpoint.

## A level-three vertex has degree two

Suppose a level-three vertex $u$ buys links to distinct level-four
children $v_1,v_2$. Delete both and buy $ur$. All original shortest
paths from $r$ to vertices other than the two sold targets survive.
They cannot use either sold edge because they would reach level four
at that edge and then need another step. A sold target that has
another parent retains its original distance four from $r$. If it
has only one parent, its block degree is at least two, so it has a
same-level neighbor. This neighbor is neither of the sold targets
because a triangle is forbidden. The neighbor retains its original
distance four from $r$, giving the sold target a route of length
five from $r$. These walks also ensure connectivity.

The change in distance from $u$ to $r$ is $-2$. Other distances
can increase only if their original shortest paths started with a
sold edge. For a destination of level $j\le2$, such a path has
length at least $5-j$, and the new root route has length at most
$1+j$. So this distance cannot increase. For a level-three
destination distinct from $u$, an affected old distance is at least
two and the new root route has length at most four. For a level-four
destination other than $v_1,v_2$, an affected old distance is at least
two and the new route is of length at most five. Each sold target
gets a route of length at most six, giving an increase of at most
five for that target.

Consequently the weighted distance increase is at most
\[
 -2R+3(n-R)+2(w(v_1)+w(v_2))\le5n-7R\le3R<\alpha.
\]
The change saves one purchase, so it is profitable. Thus each
level-three vertex has at most one child, and it has exactly one
because its block degree is at least two. Its block degree is two.

## A level-four vertex has a unique parent

Let $v$ have level four and let $u$ be a parent at level three.
The parent $p$ of $u$ at level two buys $pu$. The two-step swap from
$pu$ to $pv$ yields
\[
 w(u)\ge w(v)+\sum_{z\in N_H(v)\setminus\{u\}}w(z).
 \tag{1}
\]
The graph distances here are attained along $p,u,v$ and
$p,u,v,z$. Those paths are geodesics by girth at least eight.
The swap inequality follows because $u$ has block degree two
and the skipped attachment at $u$ is the only possible loss.

Now let $u$ replace its purchase $uv$ with $ur$. Let $M(v)$
be the total weight of the level-four neighbors of $v$. As in the
two-sale deviation, old root distances survive for every vertex
other than the sold target $v$. Its root distance stays four if
it has another parent and is at most five otherwise. The root
gives a gain of two per player attached there. Every affected
destination other than $v$ has increase at most two, except a
level-four neighbor of $v$ that can increase by three. Indeed, for
one of these exceptional destinations the old distance from $u$
can be two via $v$, and the new root route has length at most five.
The distance to $u$ stays zero and the distance to $v$ increases
by at most $4+\eta$, where $\eta=1$ for a unique parent and
$\eta=0$ otherwise. The resulting bound on weighted change is
\[
 2(n-2R)+(2+\eta)w(v)+M(v)-2w(u).
 \tag{2}
\]
If $v$ has another parent, (1) includes that parent's positive
weight. Equations (1) and (2) then give a strictly negative change.
Hence every level-four vertex has exactly one parent.

## No purchases within the fourth layer

Suppose a level-four vertex $v$ buys a same-level edge $vz$.
Replace it with $vr$. No old shortest path from $r$ uses a
same-level edge, so all old root routes survive. The gain at the
root is three, each affected distance other than the sold target
increases by at most three because its old distance is at least
two, and the distance to the sold target increases by at most
four. The distance to the buyer stays zero. The weighted change
is therefore at most
\[
  3(n-2R)-3w(v)+w(z).
\]
Nonprofitability implies $w(z)\ge3w(v)$ and hence $M(v)>w(v)$.
But $v$ has a unique parent, so (1) and (2) give for that parent's
swap a bound of $w(v)-M(v)<0$. This contradiction eliminates
every same-level edge. Each level-four vertex would then have
degree one, contradicting two-connectivity.

Lean checks the two-attachment addition bound, the eccentricity bound,
and the exclusion of inward purchases in `TreeConjecture/HeavyAttachment.lean`. The rest of the
layer argument above is a mathematical proof.

[Dippel and Vetta, One n Remains to Settle the Tree Conjecture](https://doi.org/10.4230/LIPIcs.STACS.2024.28)
