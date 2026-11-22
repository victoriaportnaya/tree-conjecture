# General bounds from distance layers and core cycles

## Ownership across distance layers

Let $H$ be any cyclic maximal biconnected block of an equilibrium at $\alpha>n$. Distances between its vertices agree with the ambient graph $G$. Each vertex $v$ of $H$ has attachment weight $w(v)$, the size of the set of ambient vertices entering the block at $v$. Choose $r\in V(H)$ minimizing the original distance sum among vertices of $H$. Equivalently it minimizes $\sum_z w(z)d_H(r,z)$.

**Capacity for purchases.** A purchase $uv$ by $u\ne r$ is dispensable for the redirect to $r$ if $v$ is at most as far from $r$ as $u$, or if $v$ is one layer farther and has a second predecessor. A predecessor of $v$ is a neighbor at distance $d_H(r,v)-1$ from $r$. In either case there is an original shortest route from $r$ to $v$ avoiding $uv$. One can choose alternatives for all the sold endpoints at once in a breadth-first parent tree. After replacing the sold set by $ur$, distances from $r$ do not increase. Selling at least two purchases would save at least $\alpha$, while the buyer's distance sum would rise by at most $n$ because $r$ minimizes the old sum. Thus every nonroot vertex buys at most one of these dispensable block edges. The Lean lemma is `nash_at_most_one_purchase_with_alternative_parents`. The updated `RetainedRoutes.lean` including this corollary and its paired version compiled successfully.

This also gives an orientation-free condition at every minimum-distance root. Form the graph of all equal-layer edges and all edges to a deeper endpoint with at least two predecessors. Each is dispensable for either owner, so any subset $X\subseteq V(H)$ spans at most $|X|$ such edges. In particular this graph is a pseudoforest.

**Layer calculation.** For $v\in L_i=\{x:d_H(r,x)=i\}$, $i\ge1$, let $p,q,h$ be the numbers of neighbors in the previous, next and same layers. Let $a$ count purchases by $v$ toward its predecessors if $p\ge2$, and set $a=0$ if $p=1$. Let $b$ count purchases by $v$ toward next-layer vertices having at least two predecessors, and $t$ count purchases on equal-layer edges. Then $a+b+t\le1$. Set $k=p-a$ when $p\ge2$ and $k=0$ otherwise. This counts edges incident to $v$ from its previous layer that are dispensable for either endpoint and bought by the other endpoint. Each equilibrium edge has one buyer.

Define $\Phi_i=\sum_{v\in L_i}(2p-3k)$ and
$
 \sigma(v)=4q-6b-2p+3k+2h-4t.
$
All edges from $L_i$ to $L_{i+1}$ give $\sum_{L_i}q=\sum_{L_{i+1}}p$. The purchases in the same direction counted here give $\sum_{L_i}b=\sum_{L_{i+1}}k$. The same-layer term sums to zero because $\sum_{L_i}h=2\sum_{L_i}t$. Consequently
$
 2\Phi_{i+1}-\Phi_i=\sum_{v\in L_i}\sigma(v).
$
The first layer has one predecessor at every vertex and $\Phi_1=2\deg_H(r)>0$. If $R$ is the eccentricity of $r$ in $H$, then $\Phi_{R+1}=0$. Telescoping yields
$
 \sum_{i=1}^{R}2^{i-1}\sum_{v\in L_i}\sigma(v)=-2\deg_H(r).
$
Some nonroot vertex has negative $\sigma$.

The hand calculation uses $p\ge1,\ p+q+h\ge2,\ a+b+t\le1$, together with $b>0\Rightarrow q>0$ and $t>0\Rightarrow h>0$. The only negative cases are below. The column for the purchase records the dispensable edge included in the count.

| Previous $p$ | Next $q$ | Same $h$ | Purchase | $\sigma$ |
| --- | --- | --- | --- | --- |
| 2 | 0 | 0 | To a predecessor | −1 |
| 1 | 1 | 0 | To a next-layer vertex with at least two predecessors | −4 |
| 1 | 0 | 1 | To a same-layer vertex | −4 |
| 1 | 1 | 1 | To a next-layer vertex with at least two predecessors | −2 |
| 1 | 0 | 2 | To a same-layer vertex | −2 |

For $p\ge2$, the four possibilities $a=1,b=1,t=1$, and none give respectively $4q+p-3+2h,\ 4q+p-6+2h,\ 4q+p+2h-4,\ 4q+p+2h$. For $p=1$, the three possibilities $b=1,t=1$, and neither give $4q+2h-8,\ 4q+2h-6,\ 4q+2h-2$. These formulas also prove completeness of the table.

**Attachment bound.** A negative vertex of degree two belongs to an ownership-directed path $a_0\to v\to b_0$ in the block. Its remaining edge points to a predecessor of $v$ when viewed from $v$, so that edge too would be dispensable if $v$ bought it. The one-purchase capacity forces the other endpoint to buy it. Write $g$ for the girth of $H$. From $b_0$ continue away from $v$ until the whole nonbacktracking path from $a_0$ has length $\lfloor g/2\rfloor$. Minimum block degree two permits each extension. The path has no repeat and every initial segment is geodesic, since a strictly shorter route would give a cycle of length less than $g$. The same holds for its segments from $b_0$.

For every vertex $z$ from $b_0$ onward on this path, $d_H(a_0,z)=2+d_H(b_0,z)$. The swap by $a_0$ from $a_0v$ to $a_0b_0$ gains at least one unit on each such attachment, and can lose at most one unit on $v$'s attachment alone. A shortest path from $a_0$ that used the sold edge and goes outside $v$'s attachment has to continue through $b_0$. The new link shortens that portion of the route. On $v$'s attachment the old edge is replaced by a two-edge route. Nash therefore gives
$
 w(v)\ \ge\ \sum_{z\text{ from } b_0\text{ onward}}w(z)
 \ \ge\ \lfloor g/2\rfloor-1 .
$

**Consequences.** Every cyclic bipartite block at $\alpha>n$ contains a degree-two vertex with at least $\lfloor g/2\rfloor-1\ge3$ players in its attachment, since $h=0$ and the equilibrium girth is at least eight. This excludes all bipartite cyclic blocks of minimum degree at least three, with arbitrary exterior attachments and arbitrary diameter. It also excludes a bipartite equilibrium that is itself biconnected. For general blocks, relative to every minimum-distance root, there is either a degree-two vertex with this attachment bound or one of the two specified degree-three configurations involving an equal-layer edge. The general degree bounds and the bipartite degeneracy consequences are Lean theorems. The stronger attachment-size consequence is given here as a mathematical proof.

## Degeneracy of the graph of edges between layers

The layer calculation applies to arbitrary subgraphs, including subgraphs that do not contain a shortest route to the chosen root. Let $r$ be a minimum-distance vertex of the whole equilibrium graph, or a minimum-distance vertex of a fixed block when working inside that block. Let $K$ be any nonempty subgraph in the relevant domain. Use depths inherited from the original graph or block. Count $p,q,h,a,b,t,k$ using only edges of $K$. A next-layer vertex with at least two predecessors in $K$ still has two valid shortest-path parents in the original graph. Thus exactly the same capacity $a+b+t\le1$ applies to all nonroot vertices. The root, if present, contributes $a=b=t=0$ because all its graph neighbors are at depth one and have just one predecessor in the whole graph.

The new case $p=0$ is allowed at local minima of depth in $K$. It gives $k=a=0$. At a vertex of degree at least three in $K$, $\sigma=4q-6b+2h-4t$ is strictly positive. If $b=1$ then $q\ge1$, $t=0$, and $\sigma=2(q+h)+2q-6\ge2$. If $t=1$ then $b=0$ and $\sigma\ge2(q+h)-4\ge2$. With neither purchase, $\sigma\ge2(q+h)\ge6$. Every vertex in the earliest nonempty layer of $K$ has $p=0$. At that layer $\Phi=0$, and $\Phi=0$ again one step beyond the last layer. The same edge counts and telescoping with positive powers of two show that a subgraph of minimum degree at least three must have a strictly negative vertex elsewhere. Only the final two rows of the preceding table are possible there. Both require a degree-three vertex in $K$ incident to an equal-layer edge of $K$.

It follows that for $\alpha>n$ every Nash equilibrium is **3-degenerate**. Every nonempty subgraph has a vertex of degree at most three. Moreover, after removing all equal-layer edges relative to any minimum-distance root, the remaining graph is **2-degenerate**. Every nonempty subgraph of that graph has a vertex of degree at most two. The result also applies inside any block relative to a block minimum-distance root. In a bipartite block, an edge never joins two equal layers, so the entire block is 2-degenerate. The same conclusion holds for a bipartite equilibrium graph as a whole. In an arbitrary equilibrium there is no isometric bipartite subgraph of minimum degree at least three. For this last application, choose $r$ minimizing the ambient distance sum among the vertices of that subgraph, which is all the redirect argument needs.

**Price threshold for the layer count.** The same degeneracy conclusions in fact hold for a positive price $\alpha>n-2$. If $u\ne r$ wants to remove two or more dispensable purchases, the retained-route credit at destination $u$ is $1+d_G(r,u)\ge2$. At a root of no greater total distance, the checked redirect inequality thus implies $\alpha\le n-1-d_G(r,u)\le n-2$. If the graph has girth at least seven, a buyer within distance two of $r$ has at most one dispensable incident edge. There is a unique predecessor. An equal-layer neighbor would create a cycle of length at most five, and a next-layer neighbor with another predecessor would create a cycle of length at most six. So it suffices in that case to take a positive price $\alpha>n-4$. The attachment corollary at $\alpha>n$ uses the separate known girth bound of eight.

The orientation-free combinatorial statement is also valid without a Nash game. In a finite connected bipartite graph with any root, if some subgraph has minimum degree at least three, then the graph formed by edges leading to a deeper endpoint with at least two predecessors has a connected component with more edges than vertices. Indeed, an orientation with at most one outgoing edge per vertex in that graph would give the capacity used above. Such an orientation exists exactly when it is a pseudoforest. For the forward implication of this equivalence count the outgoing edges in each component. For the reverse implication orient a tree toward a chosen root, and orient a unicyclic component toward its cycle with the cycle oriented consistently.

## Two forests in the one-subdivision of a bipartite core

Suppose a maximal equilibrium block $H$ is obtained from a finite connected simple bipartite graph $K$ by inserting one new vertex $m_e$ in every edge $e$ of $K$. Each attachment weight in $H$ is arbitrary and positive. At $\alpha>n$, the edges of $K$ split into two forests.

Put an edge $e=uv$ in $F$ if at least one endpoint buys its half of the subdivided edge. Represent a purchase $u\to m_e$ by an arc $u\to v$ in $K$. By swapping the purchase from $m_e$ to $v$, the buyer gains one unit on every attachment at $v$ and at every other midpoint incident to $v$. Indeed $d_H(u,v)=2$, and each other midpoint $m_f$ incident to $v$ has distance three from $u$ and one from $v$. Such a midpoint is distinct from $m_e$, so it is not adjacent to $u$ in the simple subdivision. The only possible loss is one unit per player attached at $m_e$, by the same degree-two swap used above. Thus
$
 w(m_e)\ \ge\ w(v)+\sum_{f\ni v,\ f\ne e}w(m_f).
$
In particular there is at most one arc entering $v$, since two would force their midpoints to have strictly greater weight than one another. If $F$ had a cycle, choose one supported direction for each of its edges, including an arbitrary choice when both directions are supported. The incoming bound forces all directions around this cycle to be consistent. The same inequalities force each incoming midpoint weight to be strictly greater than the next midpoint weight. This is impossible, so $F$ is a forest.

Let $B=E(K)\setminus F$. A midpoint of an edge in $B$ buys both halves. For each $e=uv\in B$, partition $V(K)$ by which of $u,v$ is closer in $K$. The distances to adjacent $u,v$ differ by exactly one because $K$ is bipartite. If $f=ab\ne e$ crosses this cut, number its endpoints so that $a$ is closer to $u$. The triangle inequalities along $ab$ then give an integer $j\ge0$ with $d_K(u,a)=d_K(v,b)=j$ and $d_K(u,b)=d_K(v,a)=j+1$. In $H$, this puts both $a,b$ at distance $2j+1$ from $m_e$ and $m_f$ at distance $2j+2$ from $m_e$. Also both $u,v$ are one step closer to $m_f$ than $m_e$ is. If $f$ belonged to $B$, both midpoints could sell two edges and redirect toward one another, preserving the other midpoint's old distances. This contradicts the paired redirect bound. Thus $e$ is the sole edge of $B$ crossing its cut. Every edge of $B$ is a bridge in $B$, and $B$ is a forest.

Consequently $|E(K)|\le 2(|V(K)|-1)$. In particular $H$ cannot be the subdivision of a bipartite core of minimum degree at least four. More generally $K$ must be the union of two forests, a condition also imposed on every subgraph of $K$.

If $K$ embeds isometrically into a $d$-dimensional cube, the cut for an edge is exactly the partition by the unique coordinate flipped by that edge. Each coordinate therefore has at most one edge of $B$. Since $F$ is a forest, an additional necessary condition is
$
 |E(K)|-|V(K)|+1\le d .
$
For example it excludes every one-subdivision of a middle-level graph of the $(2k+1)$-dimensional cube for $k\ge2$. The subgraph on subsets of sizes $k$ and $k+1$ is isometric because elements can be exchanged one at a time by alternating insertions and deletions. It has $2\binom{2k+1}{k}$ vertices and degree $k+1$, so its cycle rank is $(k-1)\binom{2k+1}{k}+1>2k+1$. This argument allows arbitrary attachments to the subdivided block.

### Further consequences for subdivided cores

For $e\in E(K)$ write $\Theta(e)$ for the set of edges across the distance cut of its endpoints. If $e\in B$, the entire graph of $\Theta(e)\setminus\{e\}$ lies in the forest $F$. This excludes the one-subdivision of any bipartite core of minimum degree at least three, diameter $D$, and girth $2D$. To see this, take any $e=uv$. Let $A$ consist of vertices at distance $D-1$ from $u$ and $D$ from $v$, and let $C$ be the analogous set with $u,v$ interchanged. The set $A$ is nonempty by extending the walk $v,u$ to a nonbacktracking walk of length $D$. Girth $2D$ makes it a geodesic. Each $x\in A$ has exactly one neighbor at distance $D-2$ from $u$, since two shortest paths of length $D-1$ would create a shorter cycle. Every other neighbor has distance $D$ from $u$ and therefore $D-1$ from $v$, by bipartiteness and the diameter bound. It belongs to $C$. The same argument applies to each $y\in C$. The edges between $A$ and $C$ consequently form a nonempty graph of minimum degree at least two, so they contain a cycle. They all belong to $\Theta(e)\setminus\{e\}$. Since this holds for every $e$, all core edges would have to belong to the forest $F$, contradicting minimum degree three.

There is also a restriction for any bipartite core $K$ of minimum degree at least three. A minimum-distance vertex in $H$ must be a subdividing midpoint, not an original vertex of $K$. Suppose the root $r$ were original, and $f=ab$ joins consecutive layers of $K$ with $b$ deeper and having at least two predecessors in $K$. In $H$, the midpoint $m_f$ has $a$ toward the root and $b$ one step farther. The vertex $b$ has the midpoints of its multiple parent edges as alternative predecessors. If $f\in B$, $m_f$ could remove both purchases and redirect to $r$, contradicting the rooted capacity. Therefore all edges of $K$ leading into a vertex with two or more predecessors belong to $F$. The orientation-free bipartite layer theorem shows that these edges contain a component with more edges than vertices. They cannot lie in a forest.

For the remaining minimum-root case $r=m_e$, define the original-vertex layers of $K$ by $\ell(x)=\min\{d_K(u,x),d_K(v,x)\}$, where $e=uv$. Every same-layer edge other than $e$ has its midpoint farther from $r$ than both original endpoints, so that midpoint cannot buy both halves. Every edge leading to a vertex with two predecessors also belongs to $F$, by the same multi-parent argument. Thus the combination of the equal-layer edges other than $e$ and the edges with alternative parents must be a forest in these two-root layers. The one-root bipartite layer theorem does not settle this case, because the two-root layers do have equal-layer edges.

## A common weight budget for cycles in the suppressed core

Let $H$ be a cyclic maximal biconnected block in a Nash equilibrium at $\alpha>n$. Write $w(v)$ for the number of players attached to $v$ through $H$, including $v$ itself. Choose a vertex $x$ of maximum attachment weight. Suppress the internal degree-two paths while retaining $x$ as well as every vertex of degree at least three. The length of a core edge $e$ is the length $L_e$ of its path in $H$. A core cycle with $h$ edges lifts to a simple cycle $C$ of length $c=\sum_e L_e$.

For each path of length $L\ge5$ in this cycle, index it as $v_0,\ldots,v_L$ with the endpoint nearer to $x$ first. Its interior avoids $x$. The degree-two swap argument gives
$
 w(v_i)\ge\sum_{j=i+1}^{L-1}w(v_j)\qquad(2\le i\le L-2).
$
In particular the suffix weight $M=\sum_{i=2}^{L-1}w(v_i)$ satisfies $M\ge2^{L-3}w(v_{L-1})$. At the last internal vertex the degree-two cycle inequality gives $\alpha\le2(c-3)w(v_{L-1})$, because this vertex belongs to $C$. It follows that
$
 \alpha\, 2^{L-3}\le 2(c-3)M .
$
Different paths have disjoint interiors, so all their suffix weights together are at most $n$. Therefore every such core cycle satisfies the joint inequality
$
 \alpha\sum_{e:L_e\ge5} 2^{L_e-3}\le 2(c-3)n. \tag{1}
$
The bound for one path uses the same weights as all others. Summing them is stronger than bounding each path length independently.

Put $f(L)=2^{L-3}$ for $L\ge5$ and zero otherwise. The elementary inequality $f(L)\ge8L-40$ holds for all integers $L\ge1$. It is tight at six and seven and follows at greater lengths by doubling. Because $c\ge8$ and $\alpha>n$, (1) gives $8c-40h\le\sum_e f(L_e)<2(c-3)$. Hence
$
 c<\frac{20}{3}h-1. \tag{2}
$
In particular, the core edges of length at least seven form a forest. If $\alpha\ge 3n/2$, the same holds for edges of length at least six, since $f(L)\ge4L/3$ for every $L\ge6$ and (1) then excludes a cycle composed of such edges.

**Girth independent of attachments.** Let $b$ be the number of degree-at-least-three vertices in $H$, and take the ordinary suppressed core on these vertices first, before retaining $x$. Its minimum degree is at least three. With $R=\lceil\log_2 b\rceil$, it has a cycle of at most $2R$ edges. Otherwise distinct nonbacktracking walks from a root of lengths at most $R$ would have distinct endpoints and would give at least $1+3(2^R-1)>b$ vertices. If there are parallel edges their two-edge cycle also suffices. Retaining $x$ can add at most one edge to the chosen cycle. Applying (2) gives
$
 g(H)<\frac{20}{3}\bigl(2\lceil\log_2 b\rceil+1\bigr)-1.
$
This bound depends only on the number of branch vertices and holds for nonbipartite blocks as well.

**Average degree.** The core after retaining $x$ has no bridges. In its binary cycle space, each edge occurs in exactly half of all the even subgraphs, because toggling any cycle through that edge is a bijection. Decompose every nonempty even subgraph into edge-disjoint cycles and sum (2) over those cycles. If $E'$ is the edge count of this core, its total path length $M_H=|E(H)|$ satisfies $M_H<(20/3)E'-1$. Indeed each edge is counted in half of the even subgraphs, and the negative constant contributes at least one after division since every nonempty even subgraph contributes at least one cycle and the cycle space has at least two elements.

Write $k$ for the number of edges before retaining $x$, $q=k-b$, and $E'=k+\delta$, with $0\le\delta\le1$. As $k\ge3b/2$, $k\le3q$ and $b\le2q$. Also $M_H-|V(H)|=q$. Thus
$
 |V(H)|<19q+\frac{20}{3}\delta-1.
$
If $b\ge5$, as required by the earlier exclusion of all subdivisions of $K_4$ and of blocks without a $K_4$ minor, then $q\ge3$, so $|V(H)|<21q$ and the average degree is greater than $2+2/21$. If a maximum attachment is at a branch vertex, $\delta=0$ and the stronger bound $2+2/19$ holds.

## Length-sensitive orientation of isometric cycles

Let an isometric cycle have $\ell$ vertices. Suppose a player $v$ buys both incident cycle edges. Take $m=\lfloor(\ell-1)/2\rfloor$ and an owner $u$ of the opposite edge between positions $m$ and $m+1$ from $v$. Set $d=d_G(u,v)\ge m$. Use the two deviations in Dippel and Vetta's orientation argument. Player $u$ sells the opposite edge and links to $v$. Player $v$ separately sells both of its cycle edges and links to $u$. In each deviation the old distances from the target are upper bounds for the new ones. This is because the cycle provides alternative shortest paths from each target to the sold endpoints. As a result the two distance sums cancel after adding the Nash inequalities.

The route bound through a new link overestimates the buyer's distance to itself by $d+1$ in each deviation. Consequently a double buyer forces
$
  \alpha+2\bigl\lfloor(\ell-1)/2\bigr\rfloor+2\le2n .
$
In particular every isometric cycle of length $\ell$ is consistently oriented when $\alpha>2n-\ell$. For the price range $\alpha>n$, the checked girth bound $\ell\ge8$ makes the uniform sufficient orientation threshold $\alpha>\max(n,2n-8)$.

There is an additional credit for every vertex on the surviving shortest cycle arc from $u$ to $v$. Write $z_j$ for its vertex at distance $j$ from $u$, $0\le j\le d$. Each remains reachable from $u$ in $j$ steps after the swap. The bound via the new link would give $1+d-j$ steps. Their difference gives a total credit of $\sum_{0\le j\le\lfloor d/2\rfloor}(d+1-2j)=\lfloor(d+2)^2/4\rfloor$ for the swap. The credit at $v$ for its own deviation is still $d+1$. Hence the stronger mathematical bound is
$
 \alpha + (m+1)+\left\lfloor\frac{(m+2)^2}{4}\right\rfloor\le2n . \tag{3}
$
This gives $\ell<4\sqrt n$ for any inconsistently oriented isometric cycle at $\alpha>n$. Indeed $m\ge(\ell-2)/2$, and $(m+1)+\lfloor(m+2)^2/4\rfloor>\ell^2/16$. At $\ell=8$, (3) gives $\alpha\le2n-10$. The quadratic correction is a mathematical proof using the surviving arc.
