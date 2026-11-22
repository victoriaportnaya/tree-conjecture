# Price thresholds from retained routes and girth

## A general bound of 2n minus 6

**Theorem.** For \(n\ge4\), if \(\alpha>2n-6\), every Nash equilibrium graph in the sum network creation game is a tree. This is a mathematical refinement of the published \(\alpha>2n\) bound. [Dippel–Vetta, STACS 2024](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2024.28).

For \(n=4\), the triangle and square bounds suffice. For \(n=5\) they leave only the chordless pentagon, on which dropping any owned edge raises the buyer's distance sum by four. For \(n\ge6\) the assumed price exceeds \(n\), so the proved girth bound of eight applies. In the cyclic case assume \(n\ge8\) and let \(H\) be a maximal cyclic biconnected block. Write \(w(v)=|S_H(v)|\) for attachment weights and \(F(v)\) for the old distance sum in the full graph. Distances between block vertices agree with their distances in the full graph.

### The additional credit in the receiver bound

Let \(a,v,b,z_3,z_4,\ldots\) be the cyclic order on any cycle of length \(c\) through a vertex \(v\) of block degree two, where \(a\) buys \(av\). The degree-two swap replacing \(av\) by \(ab\) gives \(|B|\le w(v)\) for \(B=\{z:d(a,z)=2+d(b,z)\}\). The elementary deletion estimate for \(av\) charges at most \(c-2\) on the attachment at \(v\) and at most \(c-4\) per player in \(B\). Every other distance from \(a\) can be retained.

The first four edges of the displayed cycle form a geodesic because the girth is at least eight. The attachments of \(z_3,z_4\) therefore lie in \(B\). After deleting \(av\), the other cycle arc reaches \(z_i\) in \(c-i\) steps instead of \(i\), for \(i=3,4\). Relative to \(c-4\), this saves \(2\) per player at \(z_3\) and \(4\) per player at \(z_4\). Thus equilibrium implies
\[
 \alpha+2w(z_3)+4w(z_4)\ \le\ 2(c-3)w(v)
 \quad\text{and hence}\quad
 (c-3)w(v)\ge\alpha/2+3. \tag{A}
\]
Both statements hold for either owner of \(vb\). This is the change to the degree-two deletion bound of Lemma 9. The branch inequality in that lemma also holds. If \(a,v,b\) are consecutive downward vertices of a shortest-path tree and \(a\) buys \(av\), then \(T(b)\subseteq B\), so \(w(v)\ge |T(b)|\).

### Directed cycles and the root tree

Every isometric cycle is directed at this price. If \(x\) buys both of its incident cycle edges, take the owner \(y\) of the opposite edge between positions \(\lfloor(c-1)/2\rfloor\) and \(\lfloor(c-1)/2\rfloor+1\) relative to \(x\). Both endpoints have shortest routes from \(x\) avoiding that edge. From \(y\), both cycle neighbors of \(x\) have shortest routes avoiding \(x\). If \(y\) sells the opposite edge and links to \(x\), its cost change is at most \(F(x)-F(y)+n-1-d(x,y)\). If \(x\) sells both and links to \(y\), its change is at most \(F(y)-F(x)+n-1-d(x,y)-\alpha\). These bounds use the retained shortest routes and the fact that the buyer's distance to itself is zero. Adding the two Nash inequalities gives \(\alpha\le2n-2-2d(x,y)\le2n-8\), a contradiction.

Any directed shortest path between specified endpoints is unique. Otherwise take internally disjoint subpaths of two such paths between a divergence \(a\) and a reunion \(z\). Both subpaths have the same length \(\ell\ge4\) by girth. Let \(y\) be the penultimate vertex on one path. That player's purchase \(yz\) can be swapped to \(ya\) while preserving the old distances from \(a\), since the other path reaches \(z\) and the path to \(y\) does not use \(yz\). In the other deviation, \(a\) sells its two first edges and links to \(y\). From \(y\) the first neighbor along its own path is reached by reversing the geodesic. The first neighbor along the other path can be reached in \(\ell\) steps via \(z\), avoiding \(a\). A route strictly shorter than \(\ell\) to that neighbor also avoids \(a\), since \(d(a,y)=\ell-1\). The same two cost bounds give \(\alpha\le2n-2\ell\le2n-8\), a contradiction.

Choose a root \(r\) with minimum \(F\) among block vertices and a shortest-path tree \(T\) containing every directed shortest path from \(r\). It exists by the uniqueness just proved, because prefixes of those paths are directed shortest paths. Its restriction spans \(H\). For a block vertex \(u\ne r\), \(|T(u)|\le n/2\). Indeed \(F(u)-F(r)\le d(r,u)(n-2|T(u)|)\) by the exact distances on descendants and the triangle inequality elsewhere. Also, when a degree-two block vertex \(v\) has one child \(s\) in \(H\), \(T(v)\setminus T(s)=S_H(v)\). When it has no block child, \(T(v)=S_H(v)\). This follows from unique entry into a maximal block.

Use \(X_0\) for the edges of \(H\) outside \(T\), and \(X_i\) for those edges together with each purchased downward tree edge from which a chain of at most \(i\) downward purchases reaches a buyer of an \(X_0\) edge. Write \(X_i^+\) for \(X_i\) together with upward purchases. Give an edge in \(X_2\) its least index \(i\in\{0,1,2\}\). Suppose \(u\) buys it. If the chain ends with off-tree purchase \(xy\), then \(y\notin T(u)\), since otherwise the fundamental cycle of \(xy\) would have length at most \(2i+2\le6\). A sold downward edge with index \(i\) can therefore replace each descendant's route from \(r\) by a walk avoiding \(u\) of length at most the old distance plus \(2i\). The walk uses \(r\) to \(y\) in \(T\), \(yx\), then the old tree routes inside the branch. The bound follows from \(d(r,y)\le d(r,x)+1\) and \(d(r,x)=d(r,u)+i\).

If \(c_u\) is the length of a shortest cycle through \(u\), the same fundamental cycle gives \(d(r,u)\ge\lfloor c_u/2\rfloor-i\). To see this, it contains \(u\) and has length at most \(2(d(r,u)+i)+2\). Failure of the stated inequality would force equality in that length bound and equality with an even \(c_u\). The cycle would then be isometric, because it is shortest through an edge incident to \(u\). In general, if a shortest cycle through an edge had a shortcut, some shortcut segment with interior outside the cycle would give a shorter cycle through that edge by keeping the arc that contains the edge. In the equality case the fundamental cycle consists of two shortest routes from \(r\) to \(y\), with \(d(r,y)=d(r,x)+1\). Since the cycle is directed and \(x\) bought \(xy\), one of the directed shortest routes from \(r\) would contain \(xy\). That contradicts \(xy\notin T\). These arguments are the structural parts of Lemmas 7 and 8 with girth and directedness as hypotheses. In particular the buyers of \(X_0,X_1,X_2\) have depth at least \(4,3,2\), respectively.

### Distance estimates and purchase capacities

Let \(u=u_0,u_1,\ldots,u_d=r\) be the path in \(T\), where \(d=d(r,u)\). For a deviation selling \(j\) purchases, let \(B_e\) be the child subtree for a sold downward edge and the empty set for a sold out-edge or up-edge. Define \(U=\sum_e|B_e|\), \(M=|T(u)|\), and \(A_l=T(u_l)\setminus T(u_{l-1})\) for \(1\le l\le d\). The subtrees of sold child edges are disjoint, and \(M-U\ge1\) because \(u\) is outside them. Also \(|A_l|\ge1\).

When adding a link to \(r\), an upper bound on cost change is
\[
 n-(j-1)\alpha-(d+1)(M-U)+\sum_e2i_e|B_e|
       -\sum_{l=1}^d(d+1-2l)_+|A_l|. \tag{B}
\]
If the up-edge is sold, omit the final sum. The corresponding bound when only deleting, with no up-edge sold, is
\[
 dn-j\alpha-2d(M-U)+\sum_e2i_e|B_e|
       -\sum_{l=1}^d(2d-2l)|A_l|. \tag{C}
\]
Here \(i_e\) is the index of each sold downward edge, and the empty branches contribute zero. For either formula, start with the routes through \(r\), overestimating the distance sum by using \(F(r)\le F(u)\). Sold child subtrees use the detours above. The unsold descendants have their old tree path from \(u\). For a destination \(z\in A_l\), when the up-edge is retained, its old tree route from \(u\) has length \(d(r,z)-d+2l\) and is available. Compare with the route via \(r\) of initial length \(1\) in (B) or \(d\) in (C). These substitutions prove the displayed estimates and give a route to every destination.

**At most one purchase in \(X_1^+\).** Two such sales include at least one \(X_1\) edge, so \(d\ge3\). By (B) the cost change is at most \(n-\alpha+2M-(d+3)(M-U)\le2n-\alpha-6<0\).

**At most two purchases in \(X_2\).** With three sales the change by (B) is at most \(n-2\alpha+4M-(d+5)(M-U)\le3n-2\alpha-d-5<0\), using \(n\ge8\) and \(\alpha>2n-6\).

**Two purchases in \(X_2\) force depth three and \(U>n/4\).** The depth is at least two. If \(d=2\), \(|T(u_1)|=M+|A_1|\le n/2\), so (C) gives cost change at most
\[
 2n-2\alpha+4M-8(M-U)-2|A_1|
 \le4n-2\alpha-14<0.
\]
For \(d\ge3\), (B) gives \(4U\ge\alpha-n+(d+1)(M-U)+(d-1)|A_1|\ge\alpha-n+2d>n\).

To rule out depth above three, choose a sold child \(v\) with \(|T(v)|>n/8\). It buys an edge in \(X_1\). If it buys an out-edge, swapping that edge to \(r\) by (B) saves at least \(2|T(v)|+d|T(u)|\) from the baseline \(n\). This exceeds \(n\), since \(d\ge3\) and \(|T(u)|>n/4\). Otherwise it buys a down-edge to a child \(z\) buying an out-edge. Swapping the out-edge of \(z\) to \(r\) saves at least \(2|T(z)|+2|T(v)|+(d-1)|T(u)|\) from the baseline \(n\), by retaining the first two ancestor credits in (B). This exceeds \(n\) when \(d\ge4\). Thus \(d=3\).

### Degree-two pairs and the final count

For a buyer \(u_0\) of an \(X_0\) edge, let \(u_1,u_2\) be its parent and grandparent in \(T\). The \(X_1^+\) capacity forces \(u_1\) to buy \(u_1u_0\) and \(u_2\) to buy \(u_2u_1\). Put \(T_j=|T(u_j)|\), \(w_j=w(u_j)\), and \(d=d(r,u_0)\ge4\). If \(u_0\) has block degree two, \(T_0=w_0\) because its second block edge is off-tree. If \(u_j\) has degree two for \(j=1,2\), then \(w_j=T_j-T_{j-1}\ge T_{j-1}\) by the branch inequality. For \(j=2\), the purchase into \(u_2\) is forced by a directed shortest cycle through that degree-two vertex.

Suppose at least two of these vertices have block degree two. The following swaps contradict equilibrium. In each case, let \(c_j\) be the length of a shortest cycle through the degree-two vertex indexed by \(j\).

- If \(u_1,u_2\) have degree two, use the swap of \(u_1u_0\) to \(u_1r\). Set \(a=d-1\ge3\). By (B), its change is at most \(n-(a+1)(T_1-T_0)-(a-1)(T_2-T_1)+2T_0\le n-2a w_1\). The depth bound gives \(2a\ge c_1-3\).
- If \(u_0,u_2\) have degree two, swap the out-edge of \(u_0\) to \(r\). Formula (B) gives a change at most \(n-(d+1)T_0-(d-1)(T_1-T_0)-(d-3)(T_2-T_1)\le n-(2d-2)w_0\). The depth bound gives \(2d-2\ge c_0-3\).
- If \(u_0,u_1\) have degree two, the same swap gives change at most \(n-(d+1)T_0-(d-1)(T_1-T_0)\le n-2d w_0\), and \(2d\ge c_0-3\).

Each of these bounds is at most \(n-\alpha/2-3<0\) by (A). Thus every off-tree buyer and its first two ancestors contain at least two branch vertices.

Let \(P\) count buyers of two \(X_2\) edges. They have depth three and subtrees larger than \(n/4\). At most one lies below each child \(p\) of \(r\), since two disjoint such subtrees below \(p\) would give \(|T(p)|>n/2\). Also \(r\) cannot buy \(rp\) for any such child. If it did, it could swap that edge to the buyer \(u\) at depth three, saving at least two steps on \(T(u)\) and adding at most two on \(T(p)\setminus T(u)\) by using the old tree path from \(u\) to \(p\). The cost change would be at most \(2|T(p)|-4|T(u)|<0\). The root does buy some block edge, because it belongs to a directed isometric cycle. Hence \(P<\deg_H(r)\).

Finally associate to each off-tree edge the purchases at its buyer and at the first two ancestors, namely the off-tree edge and the two compulsory downward edges. These associations are distinct as purchases. Each child along such a chain has at most one purchase in \(X_1^+\), so no downward edge in this association can lead to two distinct off-tree purchases. Each off-tree edge gives at least two branch incidences outside the root. A branch vertex can supply at most one incidence, plus one extra if it is counted in \(P\). Thus
\[
 2|X_0|
 \le\sum_{v\in H,\ v\ne r}(\deg_H(v)-2)+P
 =2|X_0|-\deg_H(r)+P
 <2|X_0|.
\]
The degree identity uses \(|E(H)|=|V(H)|-1+|X_0|\). This contradiction finishes the proof.

**Verification status.** Lean 4.33.0 rebuilt `TreeConjecture.TreeTheorem` and reported only standard logical axioms for the existing `dippelVetta` theorem at \(\alpha>2n\). The improvement to \(\alpha>2n-6\) above is a mathematical proof. The source changes generalizing the degree-two bound to either ownership of the remaining edge were made in `DegreeTwo.lean` and `BlockDegreeTwo.lean`. Their targeted rebuild had no final status when the execution environment disconnected.

## A general bound of 2n minus 8

**Theorem.** For every \(n\ge8\), an equilibrium graph is a tree if \(\alpha>2n-8\). Equivalently, for \(n\ge2\) the bound \(\alpha>\max\{n,2n-8\}\) suffices, using the girth result for the smaller player counts. This sharpens the preceding proof by retaining more of the available distance savings.

Assume a cyclic block exists. Since \(\alpha>n\), its girth is at least eight. The arguments for directed isometric cycles and uniqueness of directed shortest paths used only \(\alpha>2n-8\). Thus the same root \(r\), tree \(T\), sets \(X_i\) and depth bounds are available. Retain the strengthened degree-two estimate (A) and the deviation estimates (B) and (C). The steps below replace the numerical arguments that used the larger threshold.

### Purchase capacities at the lower price

For a block vertex at depth \(d\ge1\), the subtree at the first child of \(r\) on its path contains \(T(u)\) and the \(d-1\) intervening ancestors. Thus the half bound strengthens to \(M=|T(u)|\le n/2-(d-1)\). Two sales in \(X_1^+\) have \(d\ge3\), and their bound in (B) is now at most
\[
 n-\alpha+2M-(d+3)(M-U)\le2n-\alpha-3d-1<0.
\]
Three sales in \(X_2\) have \(d\ge2\), and the bound is at most
\[
 n-2\alpha+4M-(d+5)(M-U)\le3n-2\alpha-5d-1<0
\]
for \(n\ge8\) and \(\alpha>2n-8\). Hence the same capacities hold.

Suppose a vertex \(u\) at depth two buys two \(X_2\) edges. Both have index two, since \(X_1\) purchases require depth at least three. Each yields a three-edge path from \(u\) through its sold child and an off-tree buyer \(x_i\) at depth four to an endpoint \(y_i\) outside \(T(u)\). The \(y_i\) are distinct. Otherwise the two paths through different child subtrees form a six-cycle. Let \(p\) be the parent of \(u\). Each \(y_i\) is at distance at most three from \(u\), which saves at least two steps relative to the old tree route to \(y_i\). Indeed, if \(y_i\) is outside \(T(p)\), its depth is at least three by adjacency to \(x_i\), and the tree route goes through \(r\). If \(y_i\in T(p)\setminus T(u)\), the fundamental cycle has length \(d(r,y_i)+3\), so \(d(r,y_i)\ge5\) by girth, and the tree route from \(u\) has that depth as its length.

Bounding the old distance sum via the tree and taking those two extra savings gives
\[
 0\le F(u)-F(r)\le2n-4M-2|A_1|-4,
 \qquad A_1=T(p)\setminus T(u).
\]
In (C) the cost change of deleting the two purchases is therefore at most
\[
 2n-2\alpha+4M-8(M-U)-2|A_1|
 \le4n-2\alpha-12-4|A_1|
 \le4n-2\alpha-16<0 .
\]
Depth two is impossible.

At depth \(d\ge3\), the redirect gives \(4U\ge\alpha-n+2d\). At depth at least four this still yields \(U>n/4\), so the descendant swaps in the preceding proof exclude that depth. At depth three it yields \(4U>n-2\), and \(M\ge U+1\) gives \(|T(u)|>n/4\). This is the mass condition needed for the final count of double incidences.

### Degree-two pairs at the lower price

Use the same \(u_0,u_1,u_2\) above an off-tree purchase and notation \(w_j,T_j,d\). If \(u_0,u_2\) have degree two, then \(T_1\ge T_0+1\). The old bound for the swap by \(u_0\) improves to \(n-(2d-2)w_0-(2d-4)\), hence is at most \(n-\alpha/2-7\) by (A) and \(d\ge4\). If \(u_0,u_1\) have degree two, then \(2d\ge c_0-1\) improves their bound to at most \(n-\alpha/2-5\), since \(w_0\ge1\).

Suppose \(u_1,u_2\) both have degree two. With \(a=d(r,u_1)=d-1\), the swap by \(u_1\) has bound \(n-2a w_1-(a-3)T_0\) before using (A). If \(c_1\) is even, then \(2a\ge c_1-2\), which gains at least one additional unit because \(w_1\ge1\). If \(a\ge4\), the last term gains at least one unit because \(T_0\ge1\). The only remaining case is \(a=3\) and \(c_1=9\), by the depth bound and girth.

In that case write the shortest cycle in order as
\[
 u_2,\ u_1,\ u_0,\ z,\ \ldots,\ u_3,\ u_2,
\]
where \(u_3\) is the parent of \(u_2\). If \(z\notin T(u_0)\), it is outside \(T(u_1)\) because \(u_1\) has block degree two. The four-edge geodesic from \(u_3\) to \(z\) places \(z\) among the destinations benefiting when \(u_3\) replaces \(u_3u_2\) by \(u_3u_1\). All of \(T(u_1)\) also benefits. Thus \(w_2\ge T_1+1\), which adds two units to the bound for the swap by \(u_1\).

If \(z\in T(u_0)\), then its depth is five, since it is adjacent to \(u_0\) of depth four and is a descendant. The bound (B) in the swap by \(u_1\) uses eight steps to \(z\), from one step to the new root link, the old depth five and two detour steps. After the swap the other arc of the nine-cycle takes only seven steps from \(u_1\) to \(z\). Keeping this sharper route saves at least one unit. Thus in all three degree-two cases the relevant cost change is at most \(n-\alpha/2-4<0\).

As before, every off-tree edge supplies at least two branch incidences, and the number of vertices supplying two incidences is strictly below the degree of \(r\). This uses only the capacities and the depth-three subtree condition above. The same final degree count contradicts the existence of the block. The proof at \(\alpha>2n-8\) has been checked on paper and awaits Lean formalization.

## A general bound of 2n minus 10

**Theorem.** For every \(n\ge10\), any Nash equilibrium graph of the sum network creation game at \(\alpha>2n-10\) is a tree. The proof retains the root-tree counting argument above. Three strengthened estimates give the extra margin.

### Cycle orientation and directed geodesics

An equilibrium in this range has girth at least eight since \(\alpha>n\). In the opposite-edge swap used to orient an isometric cycle, let \(x\) be the double buyer and \(y\) the owner of the opposite edge. Write \(d=d(x,y)\ge3\). The single swap by \(y\) keeps its other incident edge of the cycle, to a vertex \(t\ne y\). The after-swap bound via \(x\) gives \(1+d(x,t)\) steps to \(t\), while the retained edge gives one. This additional saving is at least \(d-1\). The two Nash inequalities therefore yield
\[
 \alpha\le 2n-2-2d-(d-1)=2n-1-3d\le2n-10 .
\]
Thus every isometric cycle is directed.

The proof of uniqueness of purchase-directed shortest paths has the same credit. For the two internally disjoint arms of equal length \(\ell\ge4\) from divergence \(a\) to reunion \(z\), the penultimate vertex \(y\) on one arm swaps \(yz\) toward \(a\). Its predecessor on that arm stays at distance one from \(y\) and was at distance \(\ell-2\) from \(a\). The paired inequality sharpens to \(\alpha\le2n-2\ell-(\ell-2)\le2n-10\), so the compatible shortest-path tree \(T\) exists. All the structural depth and route estimates of the preceding proofs apply.

### The shallow buyer of two second-layer purchases

Use \(d=d(r,u)\), \(M=|T(u)|\), the total size \(U\) of sold child subtrees, and \(A_1=T(p)\setminus T(u)\) at the parent \(p\). Two \(X_1^+\) purchases have cost change at most \(2n-\alpha-3d-1\le2n-\alpha-10<0\) by the strengthened half bound. Three \(X_2\) purchases have change at most \(3n-2\alpha-5d-1<9-n<0\), since \(d\ge2\) and \(n\ge10\). Hence the purchase capacities carry over.

Suppose at \(d=2\) there are two \(X_2\) purchases. Both are genuinely index two. As above, through each sold child and the associated off-tree purchase \(x_i y_i\), there is a three-edge path from \(u\) to \(y_i\notin T(u)\), with \(d(r,x_i)=4\). The endpoints \(y_1,y_2\) are distinct by girth. If \(|A_1|\ge2\), inserting \(M\le n/2-|A_1|\) in formula (C) gives the deletion bound \(4n-2\alpha-8-6|A_1|\le4n-2\alpha-20<0\).

Now let \(|A_1|=1\), so both \(y_i\) lie outside \(T(p)\). The root \(r\) cannot buy \(rp\). It could otherwise swap \(rp\) for \(ru\), shortening routes by at least one on \(T(u)\) and increasing them by at most one on \(A_1\). Here \(M>1\) because the two child branches both exist. If some \(y_i\) has depth three, the fundamental cycle is an eight-cycle, hence isometric. Its edge \(x_i y_i\) is bought by \(x_i\), so directedness forces the first tree edge \(rp\) to be bought by \(r\), a contradiction. This leaves depths four and five for the \(y_i\).

In the original graph the three-edge routes to \(y_i\) improve on their tree routes from \(u\) by at least three or four units according to depth four or five. For each endpoint of depth four its parent, of depth three, gains at least one further unit by adding the parent edge to that three-edge route. If both endpoints have depth four and share a parent, the two four-edge routes from \(u\) to that parent form an eight-cycle. It has both incident edges of \(u\) bought by \(u\), contradicting directedness. The additional parent credits are therefore for distinct destinations. Counting these savings gives at least eight units in all depth combinations. Consequently
\[
 0\le F(u)-F(r)\le2n-4M-2|A_1|-8.
\]
With \(|A_1|=1\), formula (C) again bounds the deletion cost change by \(4n-2\alpha-20<0\).

For a two-purchase buyer at \(d\ge3\), formula (B) gives \(4U\ge\alpha-n+2d\). At \(d=3\) this yields \(4U>n-4\), and \(M\ge U+1\) yields \(M>n/4\). For \(d\ge4\) it gives \(U>(n-2)/4\) and \(M>(n+2)/4\). A largest sold branch, at a child \(v\), has \(|T(v)|>(n-2)/8\). If \(v\) buys an off-tree edge, its redirect to \(r\) earns at least \(2|T(v)|+dM>n\) from the baseline \(n\). Otherwise it buys an edge to a child \(z\) who buys an off-tree edge. That child's redirect earns at least \(2|T(z)|+2|T(v)|+(d-1)M>n\), using \(|T(z)|\ge1\) and \(d\ge4\). The two-purchase buyers therefore have depth three and subtree size above \(n/4\), as needed for the count.

### The remaining degree-two configuration

Retain inequality (A), namely \((c-3)w(v)\ge\alpha/2+3\). The cases with \(u_0\) and either \(u_1\) or \(u_2\) both of degree two already had cost bounds \(n-\alpha/2-5\) and \(n-\alpha/2-7\), respectively, in the preceding proof. They are negative here.

If \(u_1,u_2\) both have degree two, write \(a=d(r,u_1)\ge3\). For \(a\ge4\), keep the credit \((a-3)T_0\) and the previously omitted credit \((a-3)|T(u_3)\setminus T(u_2)|\) in the swap by \(u_1\). These together give at least two additional units. If \(c_1\) is even, the inequality \(2a\ge c_1-2\) gives the extra credit \(w_1\ge3\). The latter follows from the original degree-two swap by \(u_2\), since the next three vertices starting at \(u_0\) along the cycle are reached by shortest paths of length two, three and four.

The remaining case has \(a=3\) and \(c_1=9\). Write the cycle in order as \(u_2,u_1,u_0,z_3,z_4,\ldots,u_3,u_2\). If \(z_3\) is outside \(T(u_0)\), the earlier argument gives \(w_2\ge T_1+1\) and two units of extra credit. If \(z_3\in T(u_0)\), it is a child of \(u_0\). The directed cycle forces \(u_0\) to buy \(u_0z_3\) and \(z_3\) to buy \(z_3z_4\). The latter edge has to be a downward tree edge. Its being off-tree would put \(u_0z_3\) in \(X_1\) and give \(u_0\) two \(X_1^+\) purchases together with the original off-tree edge. The only upward tree edge from \(z_3\) leads to \(u_0\). Hence \(z_4\) is a child of \(z_3\), at depth six. In the swap by \(u_1\), the estimate via \(r\) and the sold branch assigns it \(1+6+2=9\) steps. The complementary cycle arc avoids the sold edge and reaches \(z_4\) in six steps. This saves three further units. In every subcase the cost bound is at most \(n-\alpha/2-5<0\).

Thus each off-tree purchase still contributes at least two branch incidences, and fewer than \(\deg_H(r)\) vertices can contribute twice. The same degree identity completes the contradiction. The \(\alpha>2n-10\) threshold is a mathematical result. The degree-two bound (A) has its own Lean verification.

## A girth-dependent bound for cyclic blocks

**Theorem.** Let \(H\) be a cyclic maximal biconnected block of an equilibrium graph. If its girth \(g\) is at least twelve and \(m=\lfloor g/2\rfloor\), then
\[
 \alpha \le 2n-\delta_m,\qquad
 \delta_m=\min\{3m-2,\ \lfloor m^2/4\rfloor+6\}.
\]
In particular a block of girth at least sixteen requires \(\alpha\le 2n-22\).

Suppose \(\alpha>2n-\delta_m\). The isometric cycles in \(H\) are directed by the retained-neighbor argument. In that argument \(d\ge m-1\), so \(2n-1-3d\le2n-3m+2\). The fork proof also gives unique purchase-directed shortest paths between vertices of \(H\), since the two arms of a fork have length at least \(m\). Shortest paths between block vertices stay in the block. The tree from the minimum-distance root can therefore be chosen to contain all directed shortest paths to block vertices, with arbitrary valid parents outside the block. The depth bound \(d(r,u)\ge\lfloor c_u/2\rfloor-i\) for \(X_i\) holds with \(c_u\ge g\).

Two \(X_1^+\) purchases would have \(d\ge m-1\) and redirect cost change at most \(2n-\alpha-3d-1<0\). Suppose instead that \(u\) buys two \(X_2\) edges, with \(d\ge m-2\ge4\). Write \(M=|T(u)|\) and \(U\) for the sum of the sizes of the sold child subtrees. In the redirect estimate (B) retain all positive ancestor credits. Because \(M-U\ge1\) and every successive difference between ancestor subtrees has size at least one, Nash gives
\[
 4U\ \ge\ \alpha-n+\sum_{j=0}^{\lfloor d/2\rfloor}(d+1-2j)
 =\alpha-n+\lfloor(d+2)^2/4\rfloor
 > n-6 .
\]
Thus \(M>(n-2)/4\), and there is a sold child \(v\) with \(|T(v)|>(n-6)/8\). Let \(p\) be the parent of \(u\). If \(v\) buys an off-tree edge, its swap to the root saves at least \(2|T(v)|+dM+(d-2)\) from its distance baseline \(n\). The last term retains the credit on \(T(p)\setminus T(u)\), which has at least one vertex. This sum exceeds \(n\) already at \(d=4\). Otherwise \(v\) buys a downward edge to a child \(z\) with an off-tree purchase. The swap by \(z\) saves at least \(2|T(z)|+2|T(v)|+(d-1)M+(d-3)>n\), again retaining the positive credit on \(T(p)\setminus T(u)\). For \(d=4\) the lower estimates give \(2+(n-6)/4+3(n-2)/4+1=n\), with strictness from the two subtree bounds. For larger depths the bounds increase. Thus there are no buyers of two \(X_2\) edges.

On any cycle of length \(c\) through a degree-two recipient \(v\), the first \(m\) steps from its buying neighbor \(a\) along \(a,v,b,\ldots\) are geodesic. For each position \(i\) from 3 to \(m\), the complementary cycle arc improves the deletion estimate on the attachment at that position by \(2(i-2)\) per player. The attachments are disjoint and nonempty, so
\[
 2(c-3)w(v)\ \ge\ \alpha+(m-2)(m-1).
\]
Since \(m\ge6\), one has \((m-2)(m-1)\ge3m-2\ge\delta_m\). Thus \((c-3)w(v)>n\). All three degree-two pair swaps above have cost bounds of the form \(n-\lambda w(v)\) with \(\lambda\ge c-3\), and remain contradictions. The final degree count applies with zero second-layer double incidences and rules out \(H\).

## Exact certificates for cycles of length eight through fifteen

For an isometric cycle of length \(c\), fix an arbitrary graph destination and normalize its old distances from the cycle vertices by subtracting the minimum. The resulting integer labels \(\ell_i\) have minimum zero, values in \([0,\lfloor c/2\rfloor]\), and differ by at most one across each edge of the cycle. Let a deviation change only the cycle purchases of its buyer \(u\), with the auxiliary graph on the cycle vertices remaining connected. If \(L'(u,y)\) is the auxiliary distance to a cycle vertex \(y\), the distance increase to the destination is at most
\[
 L'(u,y)+\ell_y-\ell_u
 \quad\text{whenever}\quad
 \ell_y<d_C(u,y)+\ell_u.
\]
The strict inequality makes the old shortest tail from \(y\) avoid \(u\), so it survives the deviation. A zero upper bound is also available if no sold endpoint \(v\) satisfies \(\ell_u=\ell_v+1\). These are the two bounds used by the verifier, which takes the better bound at each destination.

For octagons, each purchase orientation represents an eight-bit mask with bit \(i\) equal to one when vertex \(i\) buys edge \(i,i+1\). Rotation and reflection give 22 representatives. The checker verifies the listed deviations with nonnegative integer multiplicities on all 1,107 normalized labels. For each orientation the sum of purchase savings \(S\) is strictly positive. The checker proves the per-destination upper bound \(5B\le7S\) on the weighted sum \(B\) of distance increases. Summing the Nash inequalities then gives \(\alpha\le7n/5\) for an isometric octagon.

For a directed cycle, let \(D\) sum the deletion bounds for all buyers, and let \(S_j\) sum their swap bounds when each tries replacing its forward purchase by a link \(j\) positions ahead. These sums are rotation invariant. The table lists exact checked inequalities \(4D+\sum_j a_j S_j\le M_c\) for every normalized label word. Each weighted collection saves \(4c\) purchases overall, so \(\alpha\le M_c n/(4c)\).

| Cycle length | Swap coefficients | Maximum \(M_c\) | Normalized label orbits |
| ---: | --- | ---: | ---: |
| 9 | \(4S_2+5S_3\) | 41 | 351 |
| 10 | \(5S_2+5S_3\) | 45 | 902 |
| 11 | \(9S_3\) | 56 | 2,333 |
| 12 | \(9S_2+4S_4\) | 59 | 6,166 |
| 13 | \(6S_2+7S_3\) | 71 | 16,381 |
| 14 | \(11S_2+4S_4\) | 73 | 44,046 |
| 15 | \(13S_2+4S_4\) | 87 | 119,183 |

Every resulting price ratio is at most \(29/20\). The certificate checker is given below.

## A general bound of 2n minus 22

**Theorem.** For all \(n\ge40\), any Nash equilibrium graph of the sum network creation game at \(\alpha>2n-22\) is a tree. This is an additive improvement of 22 over the published general threshold for these player counts. The proof combines the short-cycle certificates with the girth-dependent block bound. [Dippel–Vetta, STACS 2024](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2024.28).

For these \(n\), the price exceeds \((29/20)n\), and hence also \(n\). There are no cycles of length at most seven by the girth-eight theorem. Any eight-cycle would therefore be isometric, and the octagon certificate excludes it. The next step shows that a shortest remaining cycle of length nine through fifteen must be directed at this price.

Let \(x\) buy both incident edges of an isometric cycle. As in the previous argument, let \(y\) own the opposite edge used for the paired swaps, and put \(d=d(x,y)\). The single seller \(y\) retains a cycle arc of length \(d\) from \(y\) to \(x\). Its first two vertices give additional credits \(d-1,d-3\) when \(y\) redirects to \(x\), since they remain at distances at most one and two. The base paired estimate, with the self destinations already removed, was \(2n-2-2d\).

If \(y\) has degree two in the maximal block and also bought its retained cycle edge, then \(x,y\) would both make the near-opposite two-purchase deviations. The resulting \(\alpha\le n-1-d\) contradicts \(\alpha>n\). Thus degree two at \(y\) makes it a receiver. Its swap inequality gives \(w(y)\ge3\), using the three next destinations along a four-edge geodesic in the cycle. The other two players attached at \(y\) yield at least \(2(d+1)\) additional units of credit when \(y\) sells its cycle edge. Their old shortest routes from \(y\) stay outside the other block vertices, while the original distances from \(x\) to them factor through \(y\).

If \(y\) has block degree at least three, choose its off-cycle neighbor \(t\) and a neighbor \(t'\ne y\) of \(t\) inside the block. They are distinct from the first two destinations on the retained arc, by girth at least eight. The retained routes have lengths at most one and two. By the triangle inequality their additional credits are at least \(d-1\) and \(d-3\). In particular when \(d\ge5\), either block-degree case gives an upper price bound at most \(2n-2-2d-2(d-1+d-3)\le2n-24\).

For a nine-cycle with ambient girth at least nine, or a ten-cycle with ambient girth at least ten, the remaining case is \(d=4\). The cycle credits are then four. If \(y\) has degree two, the attachment credit above is at least ten. Suppose \(y\) has an off-cycle neighbor \(t\). Necessarily \(d(x,t)\ge4\), because an \(x\)-to-\(y\) geodesic of length four via \(t\) would give a cycle of length at most eight together with the four-edge arc of \(C\). Then \(d(x,t')\ge3\), so these two off-cycle credits total at least six. If \(x\) has block degree at least three, its own two-edge redirect to \(y\) retains an extra neighbor off the cycle. That neighbor gives at least three additional units on the \(x\) side.

Finally let \(x\) have block degree two and \(y\) have the off-cycle neighbor \(t\). In this case \(d(x,t)\ge5\). Otherwise a path from \(x\) to \(t\) of length at most four, followed by \(ty\), gives a path of length at most five from \(x\) to \(y\), distinct from either cycle arc. It starts by one of the two cycle edges at \(x\), because shortest paths between block vertices stay in the block. Removing the common first edge with the corresponding arc leaves two distinct paths and hence a cycle of length at most \(5+(c-4)-2=c-1\). This contradicts the respective girth assumption. It follows that \(d(x,t')\ge4\), and the credits to \(t,t'\) total at least eight. All degree cases therefore give
\[
 \alpha\le 2n-2-8-4-8=2n-22
\]
or a smaller upper bound. This contradicts the assumed price, so such an isometric cycle is directed.

Apply this argument to a possible nine-cycle first. It is isometric as the globally shortest cycle. The directed nine-cycle certificate excludes it, so then the ambient girth is at least ten. Apply the same reasoning to a possible ten-cycle, and then to a shortest cycle of length from eleven to fifteen, for which \(d\ge5\). All are ruled out by their integer certificates. Any remaining cyclic block has girth at least sixteen, contrary to the girth-dependent bound. Thus the graph is a tree.

The general threshold uses a mathematical argument and a finite integer certificate check for the short cycles. It has no full Lean formalization. Lean has checked the existing base theorem, the generalized degree-two receiver estimate, and the new inequality for adding savings from shorter individual routes.


The finite checks run with `node research/min-cycles/short-cycle-threshold-check.mjs`.
