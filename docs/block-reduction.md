# Exact reduction to leaf attachments

The proof below applies to every positive integer player count for which a cyclic block exists and to edge prices at least one. `WeightedBlocks.lean` verifies the cost identity and both systems of necessary inequalities. The construction yielding sufficiency is given in full below.

## Exact reduction to a block with leaves

Let H be a maximal two-connected block of a connected equilibrium graph at price α ≥ 1. Every component of the graph outside H has exactly one neighbour in H. Connectivity gives existence. Two distinct neighbours would give an ear with both endpoints in H and all internal vertices outside H. The union of a two-connected graph and such an ear is two-connected, contradicting maximality.

Write Aᵥ for v and all components attached at v, wᵥ = |Aᵥ|, and W = Σᵥ wᵥ = n. Retain H and the original buyer of every core edge. Replace Aᵥ − {v} by wᵥ − 1 leaves adjacent to v, with every new leaf edge bought by v. **The resulting graph is a Nash equilibrium at the same price α.** It has the same number of players and still contains H.

### The exact inequalities

For a connected core H′ obtained by replacing all core purchases of one vertex u, put a = |new purchases| − |old purchases|. The required inequality is

$$a\alpha+\sum_{z\in V(H)}w_z\bigl(d_{H'}(u,z)-d_H(u,z)\bigr)\ge0.$$

For each v with wᵥ > 1 and each possible shortcut endpoint r in H, there is one more inequality

$$\sum_{z\in V(H)}w_z\,[d_H(v,z)-d_H(r,z)]_+\le\alpha,$$

where [x]₊ = max(0,x). Each inequality is necessary in the original graph, and together they are sufficient for the core with hub-owned leaves.

### Necessity in the original graph

If a player changes core purchases and leaves H′ connected, distances from the player to y in A_z are d_{H′}(u,z) plus the original distance from z to y. A path between core vertices cannot use an exterior component as a shortcut because the component has a single core neighbour. All attachment offsets cancel in the difference of costs. The remaining contributions give the weighted core inequality.

For the second inequality, choose any x in Aᵥ − {v} and add xr. When r differs from v this is a new edge. For any y in A_z with z ≠ v, every old path from x to y passes through v and z, so the old distance is d(x,v) + d_H(v,z) + d(z,y). The added link provides a route of length at most 1 + d_H(r,z) + d(z,y). Since d(x,v) ≥ 1 and old routes remain available, the saving at y is at least [d_H(v,z) − d_H(r,z)]₊. The term for z = v vanishes. The Nash inequality for x's addition gives the stated bound.

### Sufficiency after replacing the attachments by leaves

Consider a connected deviation by x in the expanded graph. If x is a hub, it must retain every edge to its own leaves, since no other player can replace such an edge. An extra purchase xℓ to another hub's leaf ℓ can be eliminated without increasing cost. If x is already adjacent to ℓ's hub b, removing xℓ increases the distance only to ℓ, by at most one, and saves α ≥ 1. Otherwise replace xℓ by xb. Distances to destinations other than ℓ do not increase, the distance to b decreases from two to one, and the distance to ℓ increases by at most one. The number of purchases is unchanged. Repeating this step leaves only core destinations for discretionary purchases.

For a hub, the normalized deviation is exactly a connected core deviation with the weighted cost change above. For a leaf at v, the incoming edge to v remains, and the player can only add new core neighbours. Its distance saving at a core vertex z is the maximum of the nonnegative savings from each individual addition. The same saving applies to every leaf hanging at z. Summing the single-addition bounds therefore pays for any subset of new links. This proves the exact equivalence.

A concrete example shows the role of the leaf inequalities. On a directed triangle, core weights (2,2,1) admit weighted core equilibrium at α = 1. A leaf at either of the two weight-two vertices improves by buying a link to the other weight-two vertex. The two vertices in that attachment each become one step closer, for a gain of two at price one.

## A restriction on purchases toward a vertex with an attachment

Let F(u) = Σ_z w_z d_H(u,z). Suppose i ≠ r, and i buys k edges to vertices z satisfying d_H(r,z) ≤ d_H(r,i). Delete those purchases and buy a link to r. A shortest path from r to any sold endpoint avoids i, since a path via i would be longer than d_H(r,i). The new edge repairs the distance from r to i. Any shortest route from r using a deleted edge can be repaired by replacing its prefix up to the last deleted edge with a route to that endpoint. Thus every distance from r in the changed core is at most its old value.

The new distance from i to any z ≠ i is then at most 1 + d_H(r,z). The weighted core inequality implies

$$(k-1)\alpha\le F(r)-F(i)+W-w_i(1+d_H(r,i)).$$

If wᵣ > 1, use the leaf inequality for r adding a link to i. Its left side is F(r) − F(i) plus the weighted sum of the differences of the opposite sign. The term at r contributes wᵣd_H(r,i) to that opposite sum. Combining the two bounds gives

$$(k-2)\alpha\le W-w_i(1+d_H(r,i))-w_r d_H(r,i).$$

Consequently at α > W, no vertex buys three such edges toward any r with wᵣ > 1. This holds for arbitrary block size, girth, and ownership. For k = 2, it also bounds the total of the two weighted endpoint terms.

There is a consequence without any leaf hypothesis. If i and r are at the diameter of H and i buys at least two core edges, every sold endpoint satisfies the distance hypothesis and the first bound gives F(r) > F(i) at α > W. Thus the vertices buying at least two core edges form an independent set in the graph of diameter pairs. In a self-centered block with constant F and |E(H)| > |V(H)|, this is impossible. Every vertex has a partner at the diameter, while counting the purchases forces some vertex to buy at least two. This excludes vertex-transitive blocks of degree at least three with equal attachment weights at any total player count.

## Exact feasibility for a fixed core at every player count

Fix H and its orientation of purchases. For each choice of the vertices carrying leaves, use integer variables wᵥ ≥ 2 at those vertices and wᵥ = 1 everywhere else. Include the core deviation rows and leaf addition rows above, leaving α continuous. All coefficients are integers.

The strict threshold α > W can be encoded by the closed inequality (m − 1)(α − W) ≥ 1, where m is the number of core vertices. For fixed integer weights, the greatest feasible price is the minimum of the upper bounds supplied by deviations buying fewer edges. At least one upper bound exists because deleting a single edge of a two-connected core leaves it connected. Each upper bound is an integer divided by an integer from 1 through m − 1. If the greatest feasible price exceeds the integer W, its distance above W is at least 1/(m − 1). Moving the price up to that endpoint preserves all lower bounds. Thus the finitely many mixed-integer models for this oriented core cover every number of players.

To settle the full conjecture, one still needs to rule out feasible weights for every remaining two-connected core of girth at least eight. Lean now checks the weighted cost identity, the necessity of both systems of inequalities, and the purchase restriction toward a vertex with an attachment. The converse that replaces the exterior by hub-owned leaves remains a mathematical proof above. The model generator is also available in the project source as `research/min-cycles/block-weight-milp.mjs`.

The inequalities were cross-checked against full unilateral-deviation intervals at α ≥ 1 for all 59,805 uniquely owned labelled profiles on three through five vertices. There were 36,928 distinct pairs of core ownership and attachment weights. For each pair, the predicted interval matched the leaf-expanded graph's interval, and every original equilibrium price remained feasible after the replacement.
