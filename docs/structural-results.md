# Structural results for cyclic equilibrium blocks

These arguments use the sum network creation game and the block attachment weights from the [main manuscript](../paper/main.tex). The [Lean declaration index](lean-declarations.md) records the available kernel-checked statements. Graph reductions and numerical consequences are stated with their hypotheses.

## Redirect bounds with retained shortest paths

Let u sell a set U of purchases and buy an edge to r. For each sold endpoint v, suppose some shortest-path parent choice rooted at r does not use u as v's parent. The parent choices may come from different trees. Combining these choices gives a single parent tree whose r-to-destination routes survive, or can be shortened at u by the new link.

For a destination z, let C(u,r,U,z) be max(0,d(r,z)+1−d(u,z)) when z=u or when a shortest path from u to z starts with a retained edge. Set the credit to zero otherwise. Nash equilibrium gives D(u)+α|U|+Σ_z C(u,r,U,z) ≤ D(r)+n+α. Pairing a redirect from u to r with one from r to u cancels both original distance sums.

Lean checks the two bounds `nash_redirect_with_retained_routes` and `nash_two_redirect_credit_bound` in `TreeConjecture/RetainedRoutes.lean`. The adjacent-parent formulation has the same metric meaning. If v is no further from r than u, every old shortest path to v avoids u. If v is one step farther, a distinct predecessor of v gives an alternative parent. At α > n, two buyers cannot both have two such purchases toward one another.

## Ownership across distance layers

Let \(H\) be any cyclic maximal biconnected block of an equilibrium at \(\alpha>n\). Distances between its vertices agree with the ambient graph \(G\). Each vertex \(v\) of \(H\) has attachment weight \(w(v)\), the size of the set of ambient vertices entering the block at \(v\). Choose \(r\in V(H)\) minimizing the original distance sum among vertices of \(H\). Equivalently it minimizes \(\sum_z w(z)d_H(r,z)\).

**Capacity for purchases.** A purchase \(uv\) by \(u\ne r\) is dispensable for the redirect to \(r\) if \(v\) is at most as far from \(r\) as \(u\), or if \(v\) is one layer farther and has a second predecessor. A predecessor of \(v\) is a neighbor at distance \(d_H(r,v)-1\) from \(r\). In either case there is an original shortest route from \(r\) to \(v\) avoiding \(uv\). One can choose alternatives for all the sold endpoints at once in a breadth-first parent tree. After replacing the sold set by \(ur\), distances from \(r\) do not increase. Selling at least two purchases would save at least \(\alpha\), while the buyer's distance sum would rise by at most \(n\) because \(r\) minimizes the old sum. Thus every nonroot vertex buys at most one of these dispensable block edges. The Lean lemma is `nash_at_most_one_purchase_with_alternative_parents`. The updated `RetainedRoutes.lean` including this corollary and its paired version compiled successfully.

This also gives an orientation-free condition at every minimum-distance root. Form the graph of all equal-layer edges and all edges to a deeper endpoint with at least two predecessors. Each is dispensable for either owner, so any subset \(X\subseteq V(H)\) spans at most \(|X|\) such edges. In particular this graph is a pseudoforest.

**Layer calculation.** For \(v\in L_i=\{x:d_H(r,x)=i\}\), \(i\ge1\), let \(p,q,h\) be the numbers of neighbors in the previous, next and same layers. Let \(a\) count purchases by \(v\) toward its predecessors if \(p\ge2\), and set \(a=0\) if \(p=1\). Let \(b\) count purchases by \(v\) toward next-layer vertices having at least two predecessors, and \(t\) count purchases on equal-layer edges. Then \(a+b+t\le1\). Set \(k=p-a\) when \(p\ge2\) and \(k=0\) otherwise. This counts edges incident to \(v\) from its previous layer that are dispensable for either endpoint and bought by the other endpoint. Each equilibrium edge has one buyer.

Define \(\Phi_i=\sum_{v\in L_i}(2p-3k)\) and
\[
 \sigma(v)=4q-6b-2p+3k+2h-4t.
\]
All edges from \(L_i\) to \(L_{i+1}\) give \(\sum_{L_i}q=\sum_{L_{i+1}}p\). The purchases in the same direction counted here give \(\sum_{L_i}b=\sum_{L_{i+1}}k\). The same-layer term sums to zero because \(\sum_{L_i}h=2\sum_{L_i}t\). Consequently
\[
 2\Phi_{i+1}-\Phi_i=\sum_{v\in L_i}\sigma(v).
\]
The first layer has one predecessor at every vertex and \(\Phi_1=2\deg_H(r)>0\). If \(R\) is the eccentricity of \(r\) in \(H\), then \(\Phi_{R+1}=0\). Telescoping yields
\[
 \sum_{i=1}^{R}2^{i-1}\sum_{v\in L_i}\sigma(v)=-2\deg_H(r).
\]
Some nonroot vertex has negative \(\sigma\).

The hand calculation uses \(p\ge1,\ p+q+h\ge2,\ a+b+t\le1\), together with \(b>0\Rightarrow q>0\) and \(t>0\Rightarrow h>0\). The only negative cases are below. The column for the purchase records the dispensable edge included in the count.

| Previous \(p\) | Next \(q\) | Same \(h\) | Purchase | \(\sigma\) |
| --- | --- | --- | --- | --- |
| 2 | 0 | 0 | To a predecessor | −1 |
| 1 | 1 | 0 | To a next-layer vertex with at least two predecessors | −4 |
| 1 | 0 | 1 | To a same-layer vertex | −4 |
| 1 | 1 | 1 | To a next-layer vertex with at least two predecessors | −2 |
| 1 | 0 | 2 | To a same-layer vertex | −2 |

For \(p\ge2\), the four possibilities \(a=1,b=1,t=1\), and none give respectively \(4q+p-3+2h,\ 4q+p-6+2h,\ 4q+p+2h-4,\ 4q+p+2h\). For \(p=1\), the three possibilities \(b=1,t=1\), and neither give \(4q+2h-8,\ 4q+2h-6,\ 4q+2h-2\). These formulas also prove completeness of the table.

**Attachment bound.** A negative vertex of degree two belongs to an ownership-directed path \(a_0\to v\to b_0\) in the block. Its remaining edge points to a predecessor of \(v\) when viewed from \(v\), so that edge too would be dispensable if \(v\) bought it. The one-purchase capacity forces the other endpoint to buy it. Write \(g\) for the girth of \(H\). From \(b_0\) continue away from \(v\) until the whole nonbacktracking path from \(a_0\) has length \(\lfloor g/2\rfloor\). Minimum block degree two permits each extension. The path has no repeat and every initial segment is geodesic, since a strictly shorter route would give a cycle of length less than \(g\). The same holds for its segments from \(b_0\).

For every vertex \(z\) from \(b_0\) onward on this path, \(d_H(a_0,z)=2+d_H(b_0,z)\). The swap by \(a_0\) from \(a_0v\) to \(a_0b_0\) gains at least one unit on each such attachment, and can lose at most one unit on \(v\)'s attachment alone. A shortest path from \(a_0\) that used the sold edge and goes outside \(v\)'s attachment has to continue through \(b_0\). The new link shortens that portion of the route. On \(v\)'s attachment the old edge is replaced by a two-edge route. Nash therefore gives
\[
 w(v)\ \ge\ \sum_{z\text{ from } b_0\text{ onward}}w(z)
 \ \ge\ \lfloor g/2\rfloor-1 .
\]

**Consequences.** Every cyclic bipartite block at \(\alpha>n\) contains a degree-two vertex with at least \(\lfloor g/2\rfloor-1\ge3\) players in its attachment, since \(h=0\) and the equilibrium girth is at least eight. This excludes all bipartite cyclic blocks of minimum degree at least three, with arbitrary exterior attachments and arbitrary diameter. It also excludes a bipartite equilibrium that is itself biconnected. For general blocks, relative to every minimum-distance root, there is either a degree-two vertex with this attachment bound or one of the two specified degree-three configurations involving an equal-layer edge. Lean checks the general degree bounds and the bipartite degeneracy corollaries in `NashLayerSparsity.lean`. The attachment-size bound above is a mathematical proof.

## Degeneracy of the graph of edges between layers

The layer calculation applies to arbitrary subgraphs, including subgraphs that do not contain a shortest route to the chosen root. Let \(r\) be a minimum-distance vertex of the whole equilibrium graph, or a minimum-distance vertex of a fixed block when working inside that block. Let \(K\) be any nonempty subgraph in the relevant domain. Use depths inherited from the original graph or block. Count \(p,q,h,a,b,t,k\) using only edges of \(K\). A next-layer vertex with at least two predecessors in \(K\) still has two valid shortest-path parents in the original graph. Thus exactly the same capacity \(a+b+t\le1\) applies to all nonroot vertices. The root, if present, contributes \(a=b=t=0\) because all its graph neighbors are at depth one and have just one predecessor in the whole graph.

The new case \(p=0\) is allowed at local minima of depth in \(K\). It gives \(k=a=0\). At a vertex of degree at least three in \(K\), \(\sigma=4q-6b+2h-4t\) is strictly positive. If \(b=1\) then \(q\ge1\), \(t=0\), and \(\sigma=2(q+h)+2q-6\ge2\). If \(t=1\) then \(b=0\) and \(\sigma\ge2(q+h)-4\ge2\). With neither purchase, \(\sigma\ge2(q+h)\ge6\). Every vertex in the earliest nonempty layer of \(K\) has \(p=0\). At that layer \(\Phi=0\), and \(\Phi=0\) again one step beyond the last layer. The same edge counts and telescoping with positive powers of two show that a subgraph of minimum degree at least three must have a strictly negative vertex elsewhere. Only the final two rows of the preceding table are possible there. Both require a degree-three vertex in \(K\) incident to an equal-layer edge of \(K\).

It follows that for \(\alpha>n\) every Nash equilibrium is **3-degenerate**. Every nonempty subgraph has a vertex of degree at most three. Moreover, after removing all equal-layer edges relative to any minimum-distance root, the remaining graph is **2-degenerate**. Every nonempty subgraph of that graph has a vertex of degree at most two. The result also applies inside any block relative to a block minimum-distance root. In a bipartite block, an edge never joins two equal layers, so the entire block is 2-degenerate. The same conclusion holds for a bipartite equilibrium graph as a whole. In an arbitrary equilibrium there is no isometric bipartite subgraph of minimum degree at least three. For this last application, choose \(r\) minimizing the ambient distance sum among the vertices of that subgraph, which is all the redirect argument needs.

**Price threshold for the layer count.** The same degeneracy conclusions in fact hold for a positive price \(\alpha>n-2\). If \(u\ne r\) wants to remove two or more dispensable purchases, the retained-route credit at destination \(u\) is \(1+d_G(r,u)\ge2\). At a root of no greater total distance, the checked redirect inequality thus implies \(\alpha\le n-1-d_G(r,u)\le n-2\). If the graph has girth at least seven, a buyer within distance two of \(r\) has at most one dispensable incident edge. There is a unique predecessor. An equal-layer neighbor would create a cycle of length at most five, and a next-layer neighbor with another predecessor would create a cycle of length at most six. So it suffices in that case to take a positive price \(\alpha>n-4\). The attachment corollary at \(\alpha>n\) uses the separate known girth bound of eight.

The orientation-free combinatorial statement is also valid without a Nash game. In a finite connected bipartite graph with any root, if some subgraph has minimum degree at least three, then the graph formed by edges leading to a deeper endpoint with at least two predecessors has a connected component with more edges than vertices. Indeed, an orientation with at most one outgoing edge per vertex in that graph would give the capacity used above. Such an orientation exists exactly when it is a pseudoforest. For the forward implication of this equivalence count the outgoing edges in each component. For the reverse implication orient a tree toward a chosen root, and orient a unicyclic component toward its cycle with the cycle oriented consistently.

## Two forests in the one-subdivision of a bipartite core

Suppose a maximal equilibrium block \(H\) is obtained from a finite connected simple bipartite graph \(K\) by inserting one new vertex \(m_e\) in every edge \(e\) of \(K\). Each attachment weight in \(H\) is arbitrary and positive. At \(\alpha>n\), the edges of \(K\) split into two forests.

Put an edge \(e=uv\) in \(F\) if at least one endpoint buys its half of the subdivided edge. Represent a purchase \(u\to m_e\) by an arc \(u\to v\) in \(K\). By swapping the purchase from \(m_e\) to \(v\), the buyer gains one unit on every attachment at \(v\) and at every other midpoint incident to \(v\). Indeed \(d_H(u,v)=2\), and each other midpoint \(m_f\) incident to \(v\) has distance three from \(u\) and one from \(v\). Such a midpoint is distinct from \(m_e\), so it is not adjacent to \(u\) in the simple subdivision. The only possible loss is one unit per player attached at \(m_e\), by the same degree-two swap used above. Thus
\[
 w(m_e)\ \ge\ w(v)+\sum_{f\ni v,\ f\ne e}w(m_f).
\]
In particular there is at most one arc entering \(v\), since two would force their midpoints to have strictly greater weight than one another. If \(F\) had a cycle, choose one supported direction for each of its edges, including an arbitrary choice when both directions are supported. The incoming bound forces all directions around this cycle to be consistent. The same inequalities force each incoming midpoint weight to be strictly greater than the next midpoint weight. This is impossible, so \(F\) is a forest.

Let \(B=E(K)\setminus F\). A midpoint of an edge in \(B\) buys both halves. For each \(e=uv\in B\), partition \(V(K)\) by which of \(u,v\) is closer in \(K\). The distances to adjacent \(u,v\) differ by exactly one because \(K\) is bipartite. If \(f=ab\ne e\) crosses this cut, number its endpoints so that \(a\) is closer to \(u\). The triangle inequalities along \(ab\) then give an integer \(j\ge0\) with \(d_K(u,a)=d_K(v,b)=j\) and \(d_K(u,b)=d_K(v,a)=j+1\). In \(H\), this puts both \(a,b\) at distance \(2j+1\) from \(m_e\) and \(m_f\) at distance \(2j+2\) from \(m_e\). Also both \(u,v\) are one step closer to \(m_f\) than \(m_e\) is. If \(f\) belonged to \(B\), both midpoints could sell two edges and redirect toward one another, preserving the other midpoint's old distances. This contradicts the paired redirect bound. Thus \(e\) is the sole edge of \(B\) crossing its cut. Every edge of \(B\) is a bridge in \(B\), and \(B\) is a forest.

Consequently \(|E(K)|\le 2(|V(K)|-1)\). In particular \(H\) cannot be the subdivision of a bipartite core of minimum degree at least four. More generally \(K\) must be the union of two forests, a condition also imposed on every subgraph of \(K\).

If \(K\) embeds isometrically into a \(d\)-dimensional cube, the cut for an edge is exactly the partition by the unique coordinate flipped by that edge. Each coordinate therefore has at most one edge of \(B\). Since \(F\) is a forest, an additional necessary condition is
\[
 |E(K)|-|V(K)|+1\le d .
\]
For example it excludes every one-subdivision of a middle-level graph of the \((2k+1)\)-dimensional cube for \(k\ge2\). The subgraph on subsets of sizes \(k\) and \(k+1\) is isometric because elements can be exchanged one at a time by alternating insertions and deletions. It has \(2\binom{2k+1}{k}\) vertices and degree \(k+1\), so its cycle rank is \((k-1)\binom{2k+1}{k}+1>2k+1\). This argument allows arbitrary attachments to the subdivided block.

### Further consequences for subdivided cores

For \(e\in E(K)\) write \(\Theta(e)\) for the set of edges across the distance cut of its endpoints. If \(e\in B\), the entire graph of \(\Theta(e)\setminus\{e\}\) lies in the forest \(F\). This excludes the one-subdivision of any bipartite core of minimum degree at least three, diameter \(D\), and girth \(2D\). To see this, take any \(e=uv\). Let \(A\) consist of vertices at distance \(D-1\) from \(u\) and \(D\) from \(v\), and let \(C\) be the analogous set with \(u,v\) interchanged. The set \(A\) is nonempty by extending the walk \(v,u\) to a nonbacktracking walk of length \(D\). Girth \(2D\) makes it a geodesic. Each \(x\in A\) has exactly one neighbor at distance \(D-2\) from \(u\), since two shortest paths of length \(D-1\) would create a shorter cycle. Every other neighbor has distance \(D\) from \(u\) and therefore \(D-1\) from \(v\), by bipartiteness and the diameter bound. It belongs to \(C\). The same argument applies to each \(y\in C\). The edges between \(A\) and \(C\) consequently form a nonempty graph of minimum degree at least two, so they contain a cycle. They all belong to \(\Theta(e)\setminus\{e\}\). Since this holds for every \(e\), all core edges would have to belong to the forest \(F\), contradicting minimum degree three.

There is also a restriction for any bipartite core \(K\) of minimum degree at least three. A minimum-distance vertex in \(H\) must be a subdividing midpoint, not an original vertex of \(K\). Suppose the root \(r\) were original, and \(f=ab\) joins consecutive layers of \(K\) with \(b\) deeper and having at least two predecessors in \(K\). In \(H\), the midpoint \(m_f\) has \(a\) toward the root and \(b\) one step farther. The vertex \(b\) has the midpoints of its multiple parent edges as alternative predecessors. If \(f\in B\), \(m_f\) could remove both purchases and redirect to \(r\), contradicting the rooted capacity. Therefore all edges of \(K\) leading into a vertex with two or more predecessors belong to \(F\). The orientation-free bipartite layer theorem shows that these edges contain a component with more edges than vertices. They cannot lie in a forest.

For the remaining minimum-root case \(r=m_e\), define the original-vertex layers of \(K\) by \(\ell(x)=\min\{d_K(u,x),d_K(v,x)\}\), where \(e=uv\). Every same-layer edge other than \(e\) has its midpoint farther from \(r\) than both original endpoints, so that midpoint cannot buy both halves. Every edge leading to a vertex with two predecessors also belongs to \(F\), by the same multi-parent argument. Thus the combination of the equal-layer edges other than \(e\) and the edges with alternative parents must be a forest in these two-root layers. The one-root bipartite layer theorem does not settle this case, because the two-root layers do have equal-layer edges.

## A forest joining short and long threads

Assume \(\alpha>n\). Let \(H\) be a cyclic maximal biconnected block, let \(K\) be its suppressed core, and let \(w(z)\) be the attachment weight at \(z\) in \(H\). The earlier suppression result gives a simple core of minimum degree at least three. The girth of \(H\) is at least eight. All paths and distances between block vertices can be measured in \(H\).

An edge of \(K\) can be assigned a direction from \(A\) to \(B\) if its thread has both of the following witnesses. First, its last two steps toward \(B\) are \(p,m,B\), where the degree-two vertex \(m\) is adjacent to \(B\) and \(p\) buys \(pm\). Second, the thread has an internal vertex \(z\) within its first two steps from \(A\) with \(w(z)\ge w(m)\). Choose one direction when both can be assigned. Call \(w(m)\) the charge of the directed edge.

Suppose an assigned edge enters \(B\). If another thread incident with \(B\) has an internal vertex \(y\) one or two steps from \(B\), the route from \(p\) through \(m,B\) to \(y\) is simple and has length three or four. Girth at least eight makes it geodesic, since a shorter route would create a cycle of length at most seven. The two-step swap by \(p\) from \(pm\) to \(pB\) therefore implies \(w(m)\ge w(B)+w(y)\). The only possible distance loss is one step for each player attached at \(m\).

Apply this inequality to the charged vertex of another edge entering \(B\). It gives a strict inequality between the two charges in each direction, so at most one assigned edge enters any vertex. If another assigned edge leaves \(B\), apply the inequality to its chosen internal vertex near \(B\). This gives a strict decrease of charge along consecutive directed edges. Thus no directed cycle exists. In a finite undirected cycle, an orientation with indegree at most one forces indegree exactly one at each vertex within the cycle. It would be a directed cycle. The assigned core edges therefore form a forest.

Every length-three thread admits a direction, including when its endpoint distances to a maximum attachment tie. Orient toward the endpoint on the recipient's side of the purchased middle edge. The recipient is both the charged vertex and the vertex within two steps of the source. The same rule applies to every length-two thread where the middle vertex receives a purchase, by orienting from the buying endpoint to the other endpoint.

Fix a maximum-weight block vertex \(x\). Exclude temporarily the one thread, if any, containing \(x\) internally. For each remaining thread of length at least five, orient from the nearer endpoint to the farther endpoint with respect to \(x\). The established long-thread ownership lemma gives all forward internal purchases. In particular it supplies the penultimate purchase toward the far endpoint. Each forward purchase into an internal vertex gives at least as much weight at that vertex as at the next internal vertex, by the two-step swap and the length-two geodesic. Thus the second internal vertex counted from the starting branch has weight at least that of the last internal vertex, giving the second witness.

For a four-edge thread \(A,a,m,b,B\) with \(A\) no farther from \(x\) than \(B\), the checked four-edge ownership lemma gives the purchase \(a\to m\). If \(m\to b\), the swap by \(a\) from \(m\) to \(b\) gives \(w(m)\ge w(b)\), so the thread admits a direction from \(A\) to \(B\). If \(m\) does not buy \(mb\), the unique buyer of \(mb\) is \(b\). The center \(m\) then receives purchases from both neighbors. This exception requires \(d(B,x)-d(A,x)\le1\), by the existing penultimate-purchase lemma. In a bipartite block the gap of an even-length path is even, so the exception then requires equal endpoint distances.

## Exceptional four-edge threads and a short-thread necessity

Two exceptional four-edge threads can meet at a branch vertex \(B\) only if their other ends are adjacent in \(H\). Write the two threads as \(A,a,m,b,B\) and \(B,c,t,d,C\), with both centers \(m,t\) receiving purchases from both sides. Suppose \(A,C\) are distinct and not adjacent. The distances \(d(A,B)\) and \(d(B,C)\) are both four by the girth condition. Every route from \(a\) to \(t\) exits the first thread at \(A\) or \(B\) and enters the second at \(B\) or \(C\). Via \(B\) alone the length is five. Using distinct endpoints between the threads costs at least two steps between them, in addition to at least one exit step and two entry steps. Thus \(d(a,t)=5\). The path of length three from \(b\) to \(t\) is geodesic. Also \(d(a,B)=3\) and \(d(b,B)=1\). The swap \(a\to m\) replaced by \(a\to b\) yields \(w(m)\ge w(B)+w(t)\). The symmetric swap at \(d\) yields \(w(t)\ge w(B)+w(m)\), a contradiction.

It follows that the other ends of outstanding exceptional threads incident with \(B\) are pairwise adjacent by length-one edges. There can be at most two, since these direct edges cannot form a triangle. If two occur, the two threads and the direct edge form a nine-cycle. In particular the exceptional edges form a matching if the core has no length-one edge, or if the block is bipartite.

**The short-thread theorem.** Every cyclic maximal biconnected equilibrium block at \(\alpha>n\) has either an edge joining two branch vertices directly or a two-edge thread whose middle vertex buys both halves. Suppose neither exists. The assigned forest and the exceptional matching cover every edge except possibly the one containing \(x\) internally. If the core has \(b\) vertices and \(k\) edges and there is no such omitted edge, then \(k\le (b-1)+\lfloor b/2\rfloor\), contradicting \(k\ge\lceil3b/2\rceil\).

If the omitted thread joins \(A\) and \(B\), choose its endpoint \(A\) nearest to \(x\). Every other branch vertex \(C\notin\{A,B\}\) is at distance at least \(d(x,A)+2\), since a path away from \(x\) must first leave the thread at \(A\) or \(B\) and then traverse a thread of length at least two to reach a new branch. Simplicity of \(K\) makes every other edge at \(A\) lead to such a \(C\). Hence no remaining length-four edge at \(A\) can be exceptional. The matching on remaining edges has size at most \(\lfloor(b-1)/2\rfloor\), and \(k-1\le(b-1)+\lfloor(b-1)/2\rfloor\). This again contradicts minimum degree three. This proves the short-thread theorem for all exterior attachment weights, all player counts and both parities of the block.

In particular every subdivision with all thread lengths at least three is excluded. When there are no direct branch-to-branch edges, if \(s\) counts two-edge threads whose middle vertex buys both halves, the same counting argument yields the common bound
\[
 s\ge k-b-\left\lfloor\frac{b-1}{2}\right\rfloor \ge 1.
\]
The forest and matching arguments above are mathematical proofs. They use the checked two-step swap, long-thread ownership and four-edge ownership lemmas.

## Incoming degree-two purchases and a linear bound on block order

Let \(H\) be a cyclic maximal biconnected equilibrium block at \(\alpha>n\). Write \(b\) for its number of branch vertices, \(D\) for its diameter, and \(\rho=n/\alpha\). Split the degree-two vertices into receivers, which have at least one incident block edge paid for by a neighbor, and buyers of both incident block edges. Let \(q\) count the receivers and \(s\) the buyers of both.

**Each receiver has a minimum attachment size.** Let \(a,u,b_0\) be consecutive vertices with \(u\) of block degree two and \(a\) buying \(au\). No assumption is needed on who buys \(ub_0\). Let \(A\) be the attachment of \(u\), and \(B=\{z:d_G(a,z)=2+d_G(b_0,z)\}\). These sets are disjoint. Swapping \(au\) for \(ab_0\) reduces distances by at least one on \(B\) and can increase them only on \(A\), by one. Hence \(|B|\le w(u)\). For a block cycle of length \(c\) containing \(u\), deleting \(au\) leaves a detour of length \(c-2\) from \(a\) to \(b_0\). Destinations in \(A\) may gain at most \(c-2\) steps and those in \(B\) at most \(c-4\). Every old shortest route affected outside \(A\) starts \(a,u,b_0\), so its destination lies in \(B\). Therefore
\[
 \alpha\le(c-2)w(u)+(c-4)|B|\le2(c-3)w(u).
\]
The other block edge at \(u\) survives changing \(a\)'s purchases regardless of its owner. This is the only ownership fact about that edge used in the bound.

Let \(c_u\) be the shortest cycle length through a receiver. Since every block edge belongs to a cycle of length at most \(2D+1\), and both edges of a degree-two vertex are on every cycle through it, \(c_u\le2D+1\). The receivers have disjoint attachments. The common budget gives
\[
 \sum_{u\ \mathrm{receiver}}\frac1{c_u-3}\le2\rho,
 \qquad
 q\le4\rho(D-1).
\]

**The vertices that buy both edges produce a forest.** Choose a minimum-distance-sum root \(r\) in \(H\). Such degree-two buyers are pairwise nonadjacent because each edge has a single owner. Suppress all of them to edges on the remaining vertices. The resulting graph of these edges is simple because two vertices with the same two neighbors would form a four-cycle. For a suppressed vertex \(u\ne r\) with neighbors \(a,b_0\), its depth is \(1+\min(d(r,a),d(r,b_0))\). If the endpoint depths differ by at most one, both purchases are dispensable for the redirect to \(r\). This violates the rooted one-purchase capacity. Their difference is therefore two. If the farther endpoint has a second shortest-path predecessor, both purchases are again dispensable. Thus it has \(u\) as its unique predecessor.

Orient each suppressed edge from its nearer to its farther endpoint. The depth strictly increases and each endpoint has at most one such incoming edge. This gives a forest. If \(r\) was itself a suppressed buyer, omit its edge during the argument. Its two neighbors both have depth one and therefore indegree zero, so they are in distinct directed tree components. Reinserting the omitted edge preserves the forest.

Hence \(s\le b+q-1\). In particular the subset of original core edges corresponding to two-edge threads whose middle vertex buys both halves is a forest for arbitrary cores. The earlier semicube argument for bipartite cores gives extra restrictions on which edges can share that forest.

**Linear size bound.** Retain a maximum-attachment vertex \(x\) when forming the suppressed core, and put \(B_0=b+\delta\), where \(\delta=1\) if \(x\) was internal to a thread and zero otherwise. The joint long-thread bound across the entire block gives
\[
 X:=\sum_e(L_e-4)_+\le\rho(D-1).
\]
Two diametral vertices of the biconnected block lie on a simple cycle by vertex biconnectivity. Each arc of that cycle has length at least \(D\), and the cycle uses at most \(B_0\) edges after suppression. Therefore
\[
 2D\le4B_0+X,\qquad
 (2-\rho)D\le4B_0-\rho.
\]
With \(\rho<1\) this gives \(D\le4B_0-2\). Along with the receiver estimate and \(s\le b+q-1\), it gives
\[
 |V(H)|=b+q+s\le34b+32\delta-27\le34b+5.
\]
Here the strict inequality \(q<4(D-1)\) has been rounded down because \(q\) is an integer. If \(\alpha\ge3n/2\), then \(\rho\le2/3\) gives \(D\le3B_0-1\) and \(q\le8B_0-6\), yielding \(|V(H)|\le18b+16\delta-13\le18b+3\). These bounds concern the size of the block itself and are independent of how many players are attached to it from outside.

**Core sparsity in the absence of direct branch edges.** In this case the core edges split into the forest of witnessed threads, the forest of double-buying two-edge threads, the matching of exceptional four-edge threads, and at most the one thread through \(x\). This decomposition restricts to any nonempty subgraph on \(t\) branch vertices. Its edge count is at most \(2(t-1)+\lfloor t/2\rfloor+1<5t/2\). Thus the suppressed core is 4-degenerate, so a core of minimum degree at least five is impossible unless there is a direct edge joining two branch vertices.

These conclusions use the checked swap and shortest-parent inequalities. The receiver extension and the combined forest and size deductions are given here as mathematical proofs.

## A finite bound for all blocks without direct branch edges

Let \(K\) be the ordinary suppressed core of a cyclic maximal biconnected equilibrium block \(H\) at \(\alpha>n\). Let \(K_{\ge2}\) contain only the edges whose threads have length at least two. For any subgraph \(J\) of \(K_{\ge2}\) on \(t\ge2\) vertices, put \(\rho=n/\alpha\) and let \(r\ge1\) be the least integer with \(6(7/5)^r-5>t\). Then
\[
 |E(J)|<\frac65 t+2\rho\,\frac{40r+8}{3}.
\]
In particular, any such \(J\) of average degree at least three has \(t\le1528\). If all threads of \(H\) have length at least two, then \(H\) has at most \(1528\) branch vertices and at most \(14520\) vertices in total. These bounds hold with all exterior attachment weights and for arbitrary cores.

Every cycle of \(J\) lifts to a simple cycle in \(H\) containing a degree-two vertex with an incident block edge bought by a neighbor. A thread of length at least three has an internal edge, whose recipient is such a vertex. A cycle consisting entirely of length-two threads with no such recipient would be a cycle of the forest of double-buyers.

Keep the \(t\) vertices of \(J\) fixed. While the remaining edge count is at least \(6t/5\), find a cycle of length at most \(2r\). Indeed, the average degree is at least \(12/5\), so girth at least \(2r+1\) would require at least
\[
 1+\frac{12}{5}\sum_{i=0}^{r-1}(7/5)^i=6(7/5)^r-5
\]
vertices by the irregular Moore bound. Pick one recipient as above on the lifted cycle and remove its thread's core edge. The chosen recipients have disjoint attachment sets, since their threads can never be used in later iterations. [Alon, Hoory and Linial, The Moore bound for irregular graphs](https://web.math.princeton.edu/~nalon/PDFS/ahl1.pdf).

A chosen cycle lifts to length \(c\) with \(c-3<(20/3)(2r+1)-4=(40r+8)/3\) by the cycle length bound below. The possible extra core edge accounts for splitting the one thread containing the maximum attachment. The recipient on that cycle has weight at least \(\alpha/[2(c-3)]\). If \(u\) edges are removed, summing the distinct charges gives \(u<2\rho(40r+8)/3\), which also holds when \(u=0\). The final edge count is less than \(6t/5\), giving the claimed bound on \(|E(J)|\).

If \(|E(J)|\ge3t/2\), use \(\rho<1\) to get \(t<(800r+160)/9\). For \(r\le17\) this gives \(t\le1528\). For \(r\ge18\), minimality gives \(t\ge6(7/5)^{r-1}-5\). At \(r=18\) this lower bound already exceeds \((800r+160)/9\). With each increment of \(r\), the lower bound is multiplied by \(7/5\) and then increased by two, so it keeps exceeding the linear bound.

If there are no direct branch edges, apply the result to \(J=K\), whose minimum degree is at least three. Now \(r\le17\), and the edge inequality gives \(k=|E(K)|\le2292\). Retaining a maximum-attachment vertex in the core adds \(\delta\in\{0,1\}\) vertices and edges. With \(b=|V(K)|\) and the diameter \(D\) of \(H\), the global excess \(X=\sum_e(L_e-4)_+\) is an integer satisfying \(X<D-1\). Since \(D\le4(b+\delta)-2\), we have \(X\le4(b+\delta)-4\). Thus
\[
 |V(H)|=b+|E(H)|-k
 \le b+4(k+\delta)+X-k
 \le 5b+3k+8\delta-4
 \le14520 .
\]

The density inequality also constrains blocks with direct branch edges. If \(k_1\) counts those edges, then \(k_1>(3/10)b-2\rho(40r+8)/3\), with \(r\) chosen for \(t=b\). In particular, along any family of such blocks with unboundedly many branch vertices, the number of direct edges grows at least as \(3b/10-O(\log b)\). These arguments are mathematical proofs using the receiver bound, the shortcut forest, and the cycle length bound.

### A necessary density of direct branch edges

The cycle-removal argument works at any average-degree threshold \(2+2\eta\) with \(0<\eta\le1/2\). In a subgraph \(J\) of \(K_{\ge2}\) on \(t\ge2\) vertices, remove one charged thread from a short cycle while the edge count is at least \((1+\eta)t\). Take \(r=\lceil\log(t)/\log(1+2\eta)\rceil\). The irregular Moore bound at girth \(2r+1\) exceeds \((1+2\eta)^r\ge t\), so a cycle of length at most \(2r\) is available at each removal. The same disjoint charge bound gives
\[
 |E(J)|<(1+\eta)t+\frac{80r+16}{3}.
\]
Because \(\log(1+2\eta)\ge\eta\) for \(\eta\le1/2\), the right side is at most \(t+\eta t+(80/3)\log(t)/\eta+32\). For \(t\ge1024\) take \(\eta=\sqrt{(80/3)\log(t)/t}\le1/2\). This yields
\[
 |E(J)|<t+\sqrt{(320/3)t\log t}+32.
\]
Consequently, in any cyclic block with \(b\ge1024\) branch vertices the number of direct edges between branch vertices satisfies
\[
 k_1>\frac b2-\sqrt{(320/3)b\log b}-32.
\]
This condition follows from the minimum core degree of three. For every fixed \(\epsilon>0\), blocks with at most \((1/2-\epsilon)b\) direct edges now have bounded order, independent of the total number of players. The argument is valid with arbitrary exterior attachments and for nonplanar and nonbipartite blocks.

### Cycles using only threads without degree-two recipients

The restriction on direct edges can be strengthened. In the suppressed core \(K\), let \(K_0\) have every direct edge and every two-edge thread whose middle vertex buys both sides. Include all \(b\) branch vertices, including isolated ones. These are exactly the threads without a degree-two recipient. Write \(r_0=|E(K_0)|-b+\operatorname{comp}(K_0)\) for its cycle rank. Delete \(r_0\) edges of \(K_0\) to make its remaining edges a spanning forest of \(K_0\). After those deletions from \(K\), every cycle has a degree-two recipient on at least one thread. The short-cycle removal proof therefore works on this graph, with all unchanged thread lengths, and for \(b\ge1024\) gives
\[
 r_0>|E(K)|-b-\sqrt{(320/3)b\log b}-32
 \ \ge\ b/2-\sqrt{(320/3)b\log b}-32 .
\]
Also, if \(K_0\) is a forest, the same \(1528\) bound on \(b\) and \(14520\) bound on \(|V(H)|\) apply as in the case without any direct edges. The Moore and charge arguments use the presence of a recipient on every cycle. Some of the uncharged threads may be direct edges.

There is an upper bound on \(r_0\) in terms of the layers around any vertex \(r\) minimizing the distance sum among block vertices. Let \(e_=\) count direct edges joining branch vertices of equal depth. At each branch vertex \(v\), let \(p_1(v)\) count its direct branch neighbors one layer closer to \(r\). Then
\[
 r_0\le e_=+\sum_v(p_1(v)-1)_+ .
\]
To prove this, omit the shortcut for the one two-edge thread whose double buyer is \(r\), if present, and delete all equal-layer direct edges. At each vertex keep at most one direct edge from an earlier layer. By the rooted purchase capacity, the endpoints of every remaining shortcut differ in depth by two, and its deeper endpoint has its middle vertex as its unique original shortest-path predecessor. This is incompatible with an incoming direct edge at that branch vertex. Orient the retained edges in increasing depth. The indegree is at most one and there are no directed cycles, so the unoriented graph is a forest. If the shortcut through \(r\) was omitted, its endpoints both have depth one and indegree zero. They are in distinct forest components, since a directed tree with indegree at most one has exactly one vertex of indegree zero. Reinserting that edge preserves the forest.

In particular, in a bipartite block there are no equal-layer edges. If the direct edges between branch vertices form a matching, then each \(p_1(v)\le1\), so \(K_0\) is a forest and the finite block bounds apply. The same conclusion holds when there are no equal-layer direct edges and the one-earlier-neighbor condition holds even with intersecting direct edges.

## Finite bounds for planar blocks without direct branch edges

Suppose the suppressed core \(K\) is planar and its threads all have length at least two. Write \(b,k,f\) for its numbers of vertices, edges and faces in a plane embedding, including the outer face. Suppression preserves two-connectivity, so every face boundary is a simple cycle. Since the core has minimum degree three, Euler's identity \(b-k+f=2\) gives \(b\le2(f-2)\) and \(k\le3(f-2)\).

Every face contains a receiving degree-two vertex in its lifted cycle. A thread of length at least three supplies one because the buyer of an edge between two degree-two vertices is one of those vertices. If every thread on the face has length two, at least one midpoint must receive a purchase, since the two-edge threads with double buyers form a forest.

For each face \(j\), select such a receiver and denote the lifted boundary length by \(c_j\). A receiver lies on at most two lifted face boundaries. Its attachment bound for the selected face gives
\[
 \sum_{j=1}^{f}\frac1{c_j-3}\le4\rho,\qquad \rho=n/\alpha<1.
\]
The prior cycle-length bound after retaining the maximum attachment gives \(\sum_j c_j<(40/3)(k+\delta)-f\), with \(\delta\le1\), since every core edge after the possible split appears on two faces. Consequently
\[
 f^2\le\left(\sum_j(c_j-3)\right)
          \left(\sum_j\frac1{c_j-3}\right)
   < 4\left(36f-\frac{200}{3}\right).
\]
This implies \(f\le142\) and \(b\le280\). With \(M_H=\frac12\sum_j c_j\), the identity \(M_H-|V(H)|=f-2\) yields
\[
 |V(H)| < \frac{40}{6}(k+\delta)-\frac32 f+2
 \le\frac{37}{2}f-\frac{94}{3},
\]
so \(|V(H)|\le2595\).

For a uniform two-edge subdivision the lifted face lengths are \(c_j=2h_j\), where \(\sum_j h_j=2k\). In that case \(\sum_j(c_j-3)=4k-3f\le9f-24\), so Cauchy gives \(f^2<36f-96\). This improves the bounds to \(f\le33\), \(b\le62\), and \(|V(H)|=b+k\le155\). The proof also applies when the planar core has odd cycles. These bounds are independent of the number of exterior players.

## A common weight budget for cycles in the suppressed core

Let \(H\) be a cyclic maximal biconnected block in a Nash equilibrium at \(\alpha>n\). Write \(w(v)\) for the number of players attached to \(v\) through \(H\), including \(v\) itself. Choose a vertex \(x\) of maximum attachment weight. Suppress the internal degree-two paths while retaining \(x\) as well as every vertex of degree at least three. The length of a core edge \(e\) is the length \(L_e\) of its path in \(H\). A core cycle with \(h\) edges lifts to a simple cycle \(C\) of length \(c=\sum_e L_e\).

For each path of length \(L\ge5\) in this cycle, index it as \(v_0,\ldots,v_L\) with the endpoint nearer to \(x\) first. Its interior avoids \(x\). The degree-two swap argument gives
\[
 w(v_i)\ge\sum_{j=i+1}^{L-1}w(v_j)\qquad(2\le i\le L-2).
\]
In particular the suffix weight \(M=\sum_{i=2}^{L-1}w(v_i)\) satisfies \(M\ge2^{L-3}w(v_{L-1})\). At the last internal vertex the degree-two cycle inequality gives \(\alpha\le2(c-3)w(v_{L-1})\), because this vertex belongs to \(C\). It follows that
\[
 \alpha\, 2^{L-3}\le 2(c-3)M .
\]
Different paths have disjoint interiors, so all their suffix weights together are at most \(n\). Therefore every such core cycle satisfies the joint inequality
\[
 \alpha\sum_{e:L_e\ge5} 2^{L_e-3}\le 2(c-3)n. \tag{1}
\]
The bound for one path uses the same weights as all others. Summing them is stronger than bounding each path length independently.

Put \(f(L)=2^{L-3}\) for \(L\ge5\) and zero otherwise. The elementary inequality \(f(L)\ge8L-40\) holds for all integers \(L\ge1\). It is tight at six and seven and follows at greater lengths by doubling. Because \(c\ge8\) and \(\alpha>n\), (1) gives \(8c-40h\le\sum_e f(L_e)<2(c-3)\). Hence
\[
 c<\frac{20}{3}h-1. \tag{2}
\]
In particular, the core edges of length at least seven form a forest. If \(\alpha\ge 3n/2\), the same holds for edges of length at least six, since \(f(L)\ge4L/3\) for every \(L\ge6\) and (1) then excludes a cycle composed of such edges.

**Girth independent of attachments.** Let \(b\) be the number of degree-at-least-three vertices in \(H\), and take the ordinary suppressed core on these vertices first, before retaining \(x\). Its minimum degree is at least three. With \(R=\lceil\log_2 b\rceil\), it has a cycle of at most \(2R\) edges. Otherwise distinct nonbacktracking walks from a root of lengths at most \(R\) would have distinct endpoints and would give at least \(1+3(2^R-1)>b\) vertices. If there are parallel edges their two-edge cycle also suffices. Retaining \(x\) can add at most one edge to the chosen cycle. Applying (2) gives
\[
 g(H)<\frac{20}{3}\bigl(2\lceil\log_2 b\rceil+1\bigr)-1.
\]
This bound depends only on the number of branch vertices and holds for nonbipartite blocks as well.

**Average degree.** The core after retaining \(x\) has no bridges. In its binary cycle space, each edge occurs in exactly half of all the even subgraphs, because toggling any cycle through that edge is a bijection. Decompose every nonempty even subgraph into edge-disjoint cycles and sum (2) over those cycles. If \(E'\) is the edge count of this core, its total path length \(M_H=|E(H)|\) satisfies \(M_H<(20/3)E'-1\). Indeed each edge is counted in half of the even subgraphs, and the negative constant contributes at least one after division since every nonempty even subgraph contributes at least one cycle and the cycle space has at least two elements.

Write \(k\) for the number of edges before retaining \(x\), \(q=k-b\), and \(E'=k+\delta\), with \(0\le\delta\le1\). As \(k\ge3b/2\), \(k\le3q\) and \(b\le2q\). Also \(M_H-|V(H)|=q\). Thus
\[
 |V(H)|<19q+\frac{20}{3}\delta-1.
\]
If \(b\ge5\), as required by the earlier exclusion of all subdivisions of \(K_4\) and of blocks without a \(K_4\) minor, then \(q\ge3\), so \(|V(H)|<21q\) and the average degree is greater than \(2+2/21\). If a maximum attachment is at a branch vertex, \(\delta=0\) and the stronger bound \(2+2/19\) holds.

### A bound across the entire block

The disjoint interiors can also be charged when each long thread uses a different cycle. For each core edge \(e\) of length \(L_e\ge5\), let \(\gamma_e\) be the shortest cycle length through its path in \(H\). Every cycle containing an edge of the path contains the whole path, because every internal vertex has block degree two. Applying the local price inequality on the shortest such cycle and summing the disjoint suffix weights yields
\[
 \sum_{e:L_e\ge5}\frac{2^{L_e-3}}{\gamma_e-3}
 \ \le\ \frac{2n}{\alpha}\ < 2.
\]
This single inequality covers the whole block, so its charged paths can lie on different cycles.

If \(D\) is the diameter of \(H\), each edge lies on a cycle of length at most \(2D+1\). Delete an edge \(uv\) and take a shortest remaining \(u\)-to-\(v\) path of length \(a\). For its vertex \(z\) at distance \(\lfloor a/2\rfloor\) from \(u\) along the path, the distance from \(v\) in \(H\) is \(\min(\lceil a/2\rceil,1+\lfloor a/2\rfloor)=\lceil a/2\rceil\). A simple path starting at \(v\) that uses \(uv\) can do so only as its first step, which justifies the two terms in the minimum. Thus \(a\le2D\). In the charge bound, \(\gamma_e-3\le2(D-1)\) for each \(e\), and \(2^{L-3}\ge4(L-4)\) for all integers \(L\ge5\). Consequently
\[
 \sum_e (L_e-4)_+\le \frac{n}{\alpha}(D-1)< D-1 .
\]
The total length in excess of four per core edge is smaller than the diameter minus one, with no dependence on the number of branches. This is a mathematical corollary of the two checked local inequalities.

## Purchase orientations on even and odd isometric cycles

Let \(C\) be an isometric cycle of length \(c\) in an equilibrium graph. Call a cycle vertex a double buyer if it buys both of its incident cycle edges. If \(c=2m\) and \(\alpha>n-m\), then at most \(\lfloor c/4\rfloor\) vertices of \(C\) are double buyers. If \(c=2m+1\) and \(\alpha>n-m-1\), then at most \(\lfloor c/3\rfloor\) are double buyers. In particular both bounds hold at \(\alpha>n\), regardless of the rest of the graph or the orientation of edges outside \(C\).

**Opposite redirects.** Suppose two distinct vertices \(u,v\) of \(C\) both buy their two incident cycle edges. For an even cycle assume \(d_C(u,v)\in\{m-1,m\}\), and for an odd cycle assume \(d_C(u,v)=m\). The two arcs of \(C\) from \(v\) to the two neighbors of \(u\) can be chosen as shortest paths avoiding \(u\). Indeed if the arcs from \(v\) to \(u\) have lengths \(d,c-d\), the paths to the neighbors have lengths \(d-1,c-d-1\), each at most \(\lfloor c/2\rfloor\) for the stated separations. Isometry makes them shortest also in the full graph. The same argument applies from \(u\) to the two neighbors of \(v\).

Consider the unilateral deviation of \(u\) removing its two cycle purchases and linking to \(v\). The original distances from \(v\) can all be preserved or improved. An old shortest route from \(v\) that uses a removed edge can have its prefix replaced through the last such edge. If the endpoint reached on that edge is \(u\), use the new link. If it is a neighbor of \(u\), use the alternative shortest route to that neighbor just described. The suffix after the last removed edge is still present. Thus the deviating distance sum of \(u\) is at most \(F(v)+n-1-d_G(u,v)\), with \(F\) denoting the old distance sum, since \(u\)'s distance to itself is zero. Its number of purchases decreases by at least one. The reverse deviation by \(v\) has the corresponding bound with \(u,v\) exchanged. Adding the two Nash inequalities yields \(\alpha\le n-1-d_G(u,v)\). This contradicts the respective price threshold. Adjacent vertices are also forbidden from both being double buyers, since each edge has one owner at positive price.

**Counting.** On the even cycle any four positions \(i,i+1,i+m,i+m+1\) are pairwise incompatible as double buyers. Each position occurs in four of the cyclic translates of this set. Thus \(4s\le c\), where \(s\) counts double buyers. On the odd cycle use the three positions \(i,i+1,i+m+1\), which again are pairwise incompatible. Each position occurs in three translates, giving \(3s\le c\). As every cycle edge has one buyer, the number of vertices buying no cycle edge equals \(s\). At least \(c-2\lfloor c/4\rfloor\) vertices buy exactly one cycle edge on an even cycle, and at least \(c-2\lfloor c/3\rfloor\) do so on an odd cycle.

**Attachment budgets on min-cycles.** Let \(C\) lie in a maximal biconnected block \(H\) at \(\alpha>n\), and let \(b_C\) count its vertices of block degree at least three. Of the \(c-b_C\) vertices of block degree two, all except the double buyers receive at least one incident purchase. Thus there are at least \((c-b_C-\lfloor c/4\rfloor)_+\) receivers when \(c\) is even, and at least \((c-b_C-\lfloor c/3\rfloor)_+\) when \(c\) is odd. Each weighs at least \(\alpha/[2(c-3)]\) on this cycle by the receiver bound. For any family of isometric cycles with nonnegative coefficients \(\lambda_C\), subject to \(\sum_{C\ni u}\lambda_C\le1\) for each vertex \(u\) of block degree two, the sum of these receiver lower bounds divided by \(2(c-3)\), with coefficients \(\lambda_C\), is at most \(n/\alpha\). This provides a numerical necessary condition on the block alone.

If every thread of \(C\) between consecutive branch vertices has length at least two, then \(b_C\le c/2\). Hence even cycles of this kind require strictly more than \(\alpha/8\) in receiver attachments, and odd ones require strictly more than \(\alpha/12\). For edge-disjoint cycles the degree-two vertices are distinct, so these charges are disjoint. For example, eight edge-disjoint even isometric cycles of this kind are impossible, even if they share branch vertices.

**Uniform two-edge subdivisions.** Suppose \(H\) is obtained by subdividing every edge of a simple core \(K\) once. Write \(k=|E(K)|\) and \(g=g(K)\). Assume every edge of \(K\) belongs to the same positive number of girth cycles, as holds for an edge-transitive core. Every lifted girth cycle is isometric and has \(2g\) edges. At least \(\lceil g/2\rceil\) of its \(g\) midpoints receive a purchase by the even cycle count. Each such midpoint has weight at least \(\alpha/(4g-6)\). Summing over the girth cycles counts each receiver attachment the same number of times, and gives
\[
 \alpha \le \frac{g(4g-6)}{k\lceil g/2\rceil}\,n \le \frac{8g-12}{k}\,n .
\]
In particular a core with \(k\ge8g-12\) satisfying this cycle incidence condition is excluded at \(\alpha>n\), for all attachments. The cycle orientation, packing and incidence bounds here are mathematical deductions from the paired redirect and receiver estimates.

## Length-sensitive orientation of isometric cycles

Let an isometric cycle have \(\ell\) vertices. Suppose a player \(v\) buys both incident cycle edges. Take \(m=\lfloor(\ell-1)/2\rfloor\) and an owner \(u\) of the opposite edge between positions \(m\) and \(m+1\) from \(v\). Set \(d=d_G(u,v)\ge m\). Use the two deviations in Dippel and Vetta's orientation argument. Player \(u\) sells the opposite edge and links to \(v\). Player \(v\) separately sells both of its cycle edges and links to \(u\). In each deviation the old distances from the target are upper bounds for the new ones. This is because the cycle provides alternative shortest paths from each target to the sold endpoints. As a result the two distance sums cancel after adding the Nash inequalities.

The route bound through a new link overestimates the buyer's distance to itself by \(d+1\) in each deviation. Consequently a double buyer forces
\[
  \alpha+2\bigl\lfloor(\ell-1)/2\bigr\rfloor+2\le2n .
\]
In particular every isometric cycle of length \(\ell\) is consistently oriented when \(\alpha>2n-\ell\). For the price range \(\alpha>n\), the checked girth bound \(\ell\ge8\) makes the uniform sufficient orientation threshold \(\alpha>\max(n,2n-8)\).

There is an additional credit for every vertex on the surviving shortest cycle arc from \(u\) to \(v\). Write \(z_j\) for its vertex at distance \(j\) from \(u\), \(0\le j\le d\). Each remains reachable from \(u\) in \(j\) steps after the swap. The bound via the new link would give \(1+d-j\) steps. Their difference gives a total credit of \(\sum_{0\le j\le\lfloor d/2\rfloor}(d+1-2j)=\lfloor(d+2)^2/4\rfloor\) for the swap. The credit at \(v\) for its own deviation is still \(d+1\). Hence the stronger mathematical bound is
\[
 \alpha + (m+1)+\left\lfloor\frac{(m+2)^2}{4}\right\rfloor\le2n . \tag{3}
\]
This gives \(\ell<4\sqrt n\) for any inconsistently oriented isometric cycle at \(\alpha>n\). Indeed \(m\ge(\ell-2)/2\), and \((m+1)+\lfloor(m+2)^2/4\rfloor>\ell^2/16\). At \(\ell=8\), (3) gives \(\alpha\le2n-10\). The quadratic correction is a mathematical proof using the surviving arc. Lean checks the length-linear orientation theorem and the joint threaded-cycle inequality with specified paths.

## Bipartite blocks of diameter four and minimum degree three

Suppose a maximal cyclic block H is bipartite, has diameter at most four, and every vertex has block degree at least three. In the range α > n its girth is at least eight. Fix two block vertices u,r at distance at least three. For every block neighbor v of u an old shortest path from r to v avoids the edge uv. If d(r,u)=4, every v is at level three. If d(r,u)=3, then v is at level two or four. At level four every neighbor of v is at level three, so there is another shortest parent besides u.

Call a vertex a double buyer if it purchases at least two block edges. If two double buyers had distance at least three, each could sell two such edges and buy a link to the other. Old root distances survive. The two Nash inequalities sum to 2α plus nonnegative route credit at most 2n, a contradiction. Double buyers thus have pairwise distance at most two.

Write m for the order, e for the number of edges, Δ for the maximum degree, and B for the set of double buyers. Every purchase is counted once because α>0. Hence e ≤ m + Σ_(v∈B)(deg(v)−1). Also e−m = ½Σ_v(deg(v)−2) ≥ ½(m+Δ−3).

If B meets both sides of the bipartition, every pair of its vertices on opposite sides is adjacent. One side must be a singleton, since a 4-cycle is forbidden. Thus B is contained in a star centered at a vertex q. Write a=deg(q) and S₁=Σ_(v∈N(q))deg(v). Distinct neighbors of q have disjoint next layers outside q, and every vertex at distance two from q has at least two new neighbors at distance three. Those neighbors are distinct because girth is at least eight. Thus m ≥ 1+a+3(S₁−a). The excess bound from purchases is e−m ≤ S₁−1. The lower degree sum gives e−m ≥ ½(m+a−3) ≥ ½(3S₁−a−2) > S₁−1, as S₁≥3a.

If B lies in one side and contains at least two vertices, take two of them with common neighbor q. They have exactly one common neighbor. Any third double buyer must share the same q, because three distinct common neighbors for the three pairs would form a 6-cycle. Thus B⊆N(q), and the preceding degree contradiction still applies. If B has just one vertex q, use the same star estimate with that center. If B is empty then e≤m contradicts minimum degree three. Hence the block cannot exist.

The counting argument is a mathematical proof using the Lean-checked redirect inequalities.

### Diameter four with degree-two vertices

Every connected bipartite graph of girth eight and diameter four is the incidence graph of a generalized quadrangle. The classification implies that if such a graph has a degree-two vertex, then one entire side has degree two. This holds for the regular parameters with one side of degree two and for the nonregular grid and complete bipartite incidence families. [Brouwer, Generalized quadrangles, §3](https://aeb.win.tue.nl/2WF02/genq.pdf).

Suppress the degree-two side to get a graph K. There are no loops or parallel edges, by simplicity and girth eight. A triangle in K would give a six-cycle. For any vertex p of K and an edge xy not incident to p, their distance in the incidence graph is at most three by parity. Thus p is adjacent in K to x or y. This implies K is complete bipartite. To see this, fix an edge ab. Each other vertex belongs to exactly one of N(a),N(b), since triangles are forbidden and the property applies to ab. For p∈N(a) and q∈N(b), apply the property to p and the edge bq. It gives pq, because p and b lie in the independent set N(a).

The suppressed graph has minimum degree at least two by two-connectivity of the original block. Thus K has a rectangle, and its subdivision is an octagon with four degree-two vertices. The exact octagon theorem forbids it at α > n. Combining both degree cases excludes every bipartite cyclic equilibrium block of diameter at most four.

## Counting unique parents and locating double buyers

Fix a minimum-distance-sum vertex r of a cyclic block H. For every v≠r, the neighbors of v one step closer to r are precisely its possible shortest-path parents. Let U be the number of nonroot block vertices with a unique such parent.

An edge can fail to be dispensable for its buyer only if the other endpoint has that buyer as its unique shortest-path parent. All other purchases can be removed together while restoring the buyer's root access with a single new link. The checked redirect inequality and D(r)≤D(u) allow at most one such dispensable purchase per buyer u≠r. The root itself has none because the only possible parent of a vertex at distance one is the root. Consequently e(H)≤m−1+U. Equivalently, the number of equal-depth edges plus the sum of p(v)−1 over vertices with multiple parents is at most U, where p(v) counts shortest parents.

Every farthest vertex v from a minimum-distance-sum root r buys at most one block edge. All its purchases are dispensable for a redirect to r, and if there were two, the term α>n alone would contradict D(v)≥D(r). More generally, for any vertices u,r such that u has two dispensable purchases relative to r, the credit from the buyer's own destination gives D(r)−D(u)≥α−n+d(r,u)+1. Hence among several mutually feasible redirects involving a sale of two edges, their targets must have strictly larger distance sums than their buyers.

## Counting off-tree edges at price above n

Choose a root r whose distance sum is smallest among the block vertices, and choose any shortest-path parent tree from r. For a non-root buyer i, deleting all purchases whose endpoints are not children of i and adding ir preserves every old distance from r. Induct on original depth. Routes to i use the added edge, and routes to each other vertex use its unchanged parent edge. Two or more such purchases would save at least α in buys, while the replacement route through r increases total distance from i by at most n − 1. Lean proves that at most one such purchase exists for each i.

Each off-tree edge consequently has a distinct buyer. Its buyer has depth at least three, since the edge plus a tree path would otherwise make a cycle of length at most six. That buyer cannot also buy its own parent edge, which must thus be bought by its parent. If D counts these downward parent purchases with child depth at least three, Lean proves |E(H)| ≤ |V(H)| − 1 + D ≤ 2(|V(H)| − 1). The handshaking identity and minimum block degree two then give a vertex of degree two or three in every block, for arbitrary n with α > n.

Lean also excludes blocks in which every vertex has a witness root from which it is farthest and whose weighted distance sum is no greater than its own. This includes self-centered blocks of constant weighted distance sum. The source contains a generic certificate checker that combines any finite family of valid deviation rows with nonnegative multipliers. A total price coefficient −c for c > 0 and a distance coefficient at most c in every coordinate prove α ≤ n for all weights.
