# Tree Conjecture for the sum network creation game

A player pays `α` per purchased edge plus the sum of its distances to the
other players. Edges are undirected, ownership belongs to the profile, and
unreachable vertices have infinite distance. The conjecture asks whether
every Nash equilibrium is a tree when `α > n`.

## Equilibria without a K4 minor

For `α > n`, every cyclic biconnected block of a Nash equilibrium
contains a `K₄` minor. The tree conclusion follows for graphs without
that minor at every player count. The
[proof](../research/min-cycles/k4-minor-free.md) combines the degree-two
path inequalities with exact certificates for the cycle formed by two
four-edge paths. Lean checks the deviation witnesses and integer
coefficient bounds for all 256 ownership orientations. The graph
reduction to these certificates and the minor argument are written out
in the proof. The general case with a `K₄` minor remains open.

## The shape of a cyclic block

At `α > n`, suppressing the degree-two paths gives a simple graph of
minimum degree at least three. The
[parallel-path proof](../research/min-cycles/parallel-block-paths.md)
uses 535 exact certificates for the case in which a path contains a
maximum attachment. It also excludes every uniform subdivision of
`K₄`.

Lean proves the
[exponential length bound](../research/min-cycles/thread-length-bound.md)
in `TreeConjecture.nash_block_long_path_cycle_bound`. This bounds block
order for any fixed number of branch vertices independently of the
total player count.

[Every subdivision of K4](../research/min-cycles/k4-subdivision-proof.md)
is excluded by the exact check of 636 geometries and 1,487 integer
certificates. Therefore a cyclic block has at least five branch
vertices. The [half-attachment argument](../research/min-cycles/half-attachment-exclusion.md)
also shows that every attachment to such a block has weight strictly
less than half the total player count. Lean checks the shortcut,
eccentricity and inward-purchase lemmas used in that argument.

With NumPy and SciPy installed, run the exact checks from the project root.

```sh
python3 research/min-cycles/octagon-degree-bound.py
python3 research/min-cycles/parallel_path_certificates.py
python3 research/min-cycles/uniform-k4-certificates.py
python3 research/min-cycles/k4_subdivision_certificates.py
```

## General bounds from distance layers and thread weights

At a positive price above `n - 2`, every nonempty subgraph of an
equilibrium has a vertex of degree at most three. Deleting same-distance
edges around a minimum-distance root lowers this degree bound to two.
The degree-two bound also holds on every bipartite maximal block, even
if the rest of the equilibrium is nonbipartite.

For `α > n`, let `c` be the length of a cycle lifted from `h` edges of
the suppressed core, retaining a vertex of largest attachment weight.
The joint attachment budget gives `6 * (c + 1) < 40 * h`. It implies
an upper bound on block girth logarithmic in the number of branch
vertices. The [proof and consequences](../research/min-cycles/layer-and-cycle-bounds.md)
also give a quadratic length correction for inconsistently oriented
isometric cycles.

Lean checks the subgraph statements in `NashLayerSparsity.lean`, the
joint cycle inequality in `CoreCycleBudget.lean`, and the
length-sensitive orientation theorem in `DirectedMinCycles.lean`.

## Lean 4

`TreeConjecture.nash_tree_of_two_n_lt_alpha` proves the full published
`α > 2n` theorem for any positive number of players. Import
`TreeConjecture` to use it. The general `α > n` statement is
`TreeConjecture.conjecture`.
[Dippel–Vetta, STACS 2024](https://doi.org/10.4230/LIPIcs.STACS.2024.28)

`TreeConjecture.nash_tree_of_le_ten_at_n` proves the `α > n` statement
for `1 ≤ n ≤ 10` in Lean.

The project uses Lean 4.33.0 and the Mathlib revision pinned in
`lake-manifest.json`. The three game modules under `Lax899194/` are vendored
from the [Lax Archive submission](https://laxarchive.org/lax-899194/index.html)
at commit `ab7c839f02a08a417dcf6ccbf6f447790ddd5db3`. Their license is in
`LICENSE-Lax899194`.

With [Elan](https://lean-lang.org/install/) available, run these commands in
this directory.

```sh
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Acyclic \
  Mathlib.Combinatorics.SimpleGraph.DegreeSum Mathlib.Data.Fin.VecNotation \
  Mathlib.Data.ENNReal.BigOperators Mathlib.Data.Real.ENatENNReal \
  Mathlib.Logic.Equiv.Fin.Rotate Mathlib.Tactic.Linarith
lake build
```

If the cycle-certificate checks exceed the available memory when run
concurrently, build the certificate modules one at a time before the
final `lake build`.

```sh
lake build +TreeConjecture.HeptagonChecks0:olean
lake build +TreeConjecture.HeptagonChecks1:olean
lake build +TreeConjecture.HeptagonChecks2:olean
lake build +TreeConjecture.HexagonChecks0:olean
lake build +TreeConjecture.Pentagon:olean
lake build
```

The pentagon checker separates the 32 orientations into eight
groups of four closed computations.

| Module | Main checked results |
| --- | --- |
| `TreeConjecture/Foundations.lean` | Equilibrium connectivity, unique ownership for positive prices, and the one-edge deletion inequality |
| `TreeConjecture/ShortCycles.lean` | No 3- or 4-cycles above `n − 2`, and the tree conclusion through four players |
| `TreeConjecture/Girth.lean` | Every cycle of length `k` at equilibrium satisfies `2α ≤ n(k − 2)`. Above `2n`, every cycle has length at least seven. |
| `TreeConjecture/MinCycles.lean` | Globally shortest cycles are isometric |
| `TreeConjecture/EdgeMinCycles.lean` | A shortest cycle through a given edge (Dippel–Vetta, Lemma 2) or vertex is isometric |
| `TreeConjecture/Redirect.lean` | A Nash inequality for selling a set of links and buying one link, obtained by repairing distances to the affected endpoints |
| `TreeConjecture/DirectedMinCycles.lean` | At `α > 2(n − 1)`, every isometric cycle in equilibrium is coherently directed by its edge purchases (Dippel–Vetta, Lemma 3) |
| `TreeConjecture/CycleInequalities.lean` | The square penalty sum and the weighted pentagon deletion bound given its swap inequalities |
| `TreeConjecture/DeviationCertificates.lean` | A generic shortest-distance certificate and a kernel-checked eight-player deviation |
| `TreeConjecture/Baseline.lean` | The half-size bound for a shortest-path branch through a vertex whose distance sum is at least the root's |
| `TreeConjecture/RootedShortestPaths.lean` | Construction of a rooted shortest-path spanning tree and the half-size bound for its branches |
| `TreeConjecture/RootedCycles.lean` | Fundamental cycle lengths, and depth at least three for endpoints of edges outside the rooted tree at `α > 2n` |
| `TreeConjecture/DirectedGeodesics.lean` | Uniqueness of purchase-directed shortest paths and existence of a shortest-path tree containing all such paths from its root at `α > 2(n − 1)` |
| `TreeConjecture/BranchDetours.lean` | Paths to the root that bypass a branch ancestor, with excess length at most twice the depth gap (Lemma 7) |
| `TreeConjecture/CycleDepth.lean` | The depth bound from the length of a shortest cycle through the ancestor of an off-tree buyer (Lemma 8) |
| `TreeConjecture/EdgeLayers.lean` | The accumulated edge classes `X_i` and Lemmas 7 and 8 stated for those classes, within a specified subgraph |
| `TreeConjecture/DegreeTwo.lean` | The swap and deletion estimates of Lemma 9 under the local degree-two condition, including the downward-branch bound |
| `TreeConjecture/Biconnected.lean` | Finite maximal blocks, uniqueness of the block of a cycle edge, and containment of every cycle through a block edge |
| `TreeConjecture/BlockPaths.lean` | Paths within a block, unique entry vertices, minimum internal degree two, and existence of shortest cycles through block vertices |
| `TreeConjecture/BlockDegreeTwo.lean` | Identification of the attachment sets `S_H(v)`, Lemma 9 for maximal blocks, and selection of a largest block with a minimum-distance-sum root |
| `TreeConjecture/TreeDistanceBudget.lean` | Exact sum of tree distances in terms of the root distance sum and ancestor branch sizes |
| `TreeConjecture/LayerDeviations.lean` | Deletion of several purchases in the first three out-edge layers preserves connectivity and satisfies the cost inequality of Lemma 10 |
| `TreeConjecture/RootLinkBudget.lean` | Pointwise and summed savings from tree routes up to the midpoint of the path to the root |
| `TreeConjecture/LayerRootLink.lean` | The midpoint-sensitive cost estimate for replacing several purchases with a link to the root (Corollary 11) |
| `TreeConjecture/LayerRedirects.lean` | The cost estimate for a root-link deviation in the augmented layers, allowing sale of the parent edge (Corollary 12) |
| `TreeConjecture/LayerRestrictions.lean` | At most one purchase in `X₁⁺`, at most two in `X₂⁺`, and the quarter-size bound for two purchases in `X₂⁺` (Observations 13–14) |
| `TreeConjecture/LayerDepth.lean` | Depth at least three for two purchases in `X₂`, with equality when the affected branches contain more than a quarter of the players (Observation 15) |
| `TreeConjecture/BlockParentPurchases.lean` | The first two parent edges above an off-tree buyer in its block are bought by their higher endpoints (the orientation step of Lemma 16) |
| `TreeConjecture/BlockCycleDepth.lean` | The length bound of Lemma 8 for the shortest cycle through a vertex inside its block |
| `TreeConjecture/BlockBranchAttachments.lean` | Block attachments described by subtracting the child branches rooted inside the block |
| `TreeConjecture/BlockDegreePattern.lean` | Among an off-tree buyer and its first two ancestors, at most one has block degree two (Lemma 16) |
| `TreeConjecture/RootBranchSwap.lean` and `TreeConjecture/BlockLayerCount.lean` | A root-to-descendant swap and the injection from double buyers in `X₂` to incoming root neighbors (Lemma 17) |
| `TreeConjecture/BlockPurchaseCount.lean` | The number of off-tree triples visiting a vertex is at most one plus its double-buyer indicator |
| `TreeConjecture/TreeTheorem.lean` | Double counting excludes every nontrivial block and proves the tree theorem for `α > 2n` |
| `TreeConjecture/CycleCertificate.lean` and `TreeConjecture/CycleCertificateCheck.lean` | Soundness and finite checking of weighted cycle deviations |
| `TreeConjecture/Pentagon.lean` | Every isometric pentagon implies `7α ≤ 6n`. Hence at `α > n` equilibrium girth is at least six and the tree conclusion holds through five players. |
| `TreeConjecture/Hexagon.lean` and `TreeConjecture/Heptagon.lean` | An isometric cycle of length six or seven in equilibrium implies `α ≤ n`. |
| `TreeConjecture/ShortCycleBounds.lean` | At `α > n`, all cycles in equilibrium have length at least eight. The tree conclusion follows through seven players. |
| `TreeConjecture/Addition.lean` | A new link's distance savings, bounded from below using old routes from its two endpoints, cannot exceed its price. |
| `TreeConjecture/GeodesicPurchases.lean` | Paired redirects bound the number of purchased first steps of geodesics. Two opposite double buyers on an isometric octagon imply `α + 5 ≤ n`. |
| `TreeConjecture/GirthDistances.lean` | A simple path of length `L` in girth at least `g` bounds its endpoints' distance below by `min(L, g − L)`. At a degree-two vertex, the distance to another vertex is one plus the minimum of the two neighbours' distances. |
| `TreeConjecture/BlockSwaps.lean` | A maximum-weight attachment forbids certain purchases toward it. The two ends of a three-step geodesic cannot both buy inward when its middle vertices have block degree two. |
| `TreeConjecture/ThreadDistances.lean` | The two-step restrictions exclude long degree-two threads under the two-ended metric formula and short-geodesic conditions. |
| `TreeConjecture/ThetaMetric.lean` | A forced purchase propagates two steps in the borderline distance case. Two degree-two threads with the stated metrics cannot coexist off a maximum-weight vertex or at a maximum-weight endpoint. |
| `TreeConjecture/ThreadForest.lean` | Long degree-two paths directed away from a maximum attachment have distance increase at least their length minus three. Two such paths with a common end and possibly different starts give conflicting swap bounds. |
| `TreeConjecture/ThreadGeometry.lean` | Derives the two-ended distance formula, cross geodesics and the forest theorem from simple block paths with disjoint interiors and girth at least eight. |
| `TreeConjecture/ShortThreads.lean` | Extends the forest to short paths with the requisite endpoint distance gap, identifies the two double buyers on a four-edge path at equal levels, and verifies the bipartite parity argument. |
| `TreeConjecture/ChainWeights.lean` | Bounds the total weight gained by a two-step swap, gives an attachment-degree inequality, and forces forward purchases to propagate along any degree-two chain. |
| `TreeConjecture/EarPruning.lean` | Bounds how far new vertices can be from an original vertex and gives a girth obstruction for any later ear at that vertex. |
| `TreeConjecture/TwoLayerWeights.lean` | Counts the first two layers beyond a swapped edge and bounds the outside vertices required by a three-edge chain. |
| `TreeConjecture/CycleBlocks.lean` | Excludes cycle blocks at `α > n`, bounds the order of other blocks by their girth, and proves the tree conclusion for up to ten players. |
| `TreeConjecture/WeightedBlocks.lean` | Exact cost changes for block-local deviations, necessary leaf inequalities, and restrictions on purchases toward a root. |
| `TreeConjecture/BlockRootBounds.lean` | Counts off-tree edges at price `α > n` and proves that every block contains a vertex of degree two or three. |
| `TreeConjecture/WeightedCertificates.lean` | A certificate that combines Nash inequalities to bound the price for all attachment weights of a block. |

The girth proof constructs the surviving walks from the cycle and uses the
two detour inequalities in `ShortCycles.lean` to bound the price.
Combining the two isometric-cycle lemmas gives a directed isometric cycle
through every edge belonging to some cycle when `α > 2(n − 1)`.
The formalization includes the shortest-path tree arguments of Lemmas 7
and 8 and applies the degree-two estimates of Lemma 9 to maximal blocks.
A block contains every cycle through its edges, and deleting a block
vertex separates its attachment set from each other block vertex.
The deviation inequalities of Lemma 10 and Corollaries 11–12 give the
purchase and depth restrictions in Observations 13–15. For the final
degree count, each off-tree purchase supplies two incidences with vertices
of degree at least three. Lemma 17 bounds the repeated incidences by
strictly less than the root degree. The resulting lower bound
contradicts the handshaking identity for the block.

The build reports the axiom dependencies of the research theorems. The
eight-player theorem verifies graph distances via labels, an edge
inequality, and a predecessor at each non-root vertex. It establishes the
cost change `4 − α` for that profile. The coverage of the exhaustive
Python search is a separate computational result.

## Short isometric cycles

For each destination, the certificate records the distances from the cycle
vertices after subtracting their minimum. The short-arc distances bound the
range of the labels. A deviation can route through a cycle vertex whenever
the triangle inequality is strict enough to guarantee that a shortest tail
avoids the buyer. The resulting signed distance changes can be summed
against nonnegative integer weights on the Nash inequalities.

For pentagons the generator uses 51 normalized label types and all 32
ownership patterns. Lean verifies the routes and integer inequalities,
then proves the bound for arbitrary finite networks using
`nash_isometric_pentagon_price_bound`.

For lengths six and seven, rotations and reflections reduce the ownership
patterns to nine and ten representatives. Lean checks coverage and the
distance inequalities for 141 and 393 normalized label types respectively.
The proofs check batches by initial label. A route-length bound guarantees
that each distance estimate uses an available route.

The optional generator uses NumPy and SciPy to propose weights and checks
them with integer arithmetic. The checked Lean files need neither package.

```sh
python3 research/min-cycles/certificates.py 5
python3 research/min-cycles/certificates.py 6
python3 research/min-cycles/certificates.py 7
python3 research/min-cycles/certificates.py 8
python3 research/min-cycles/octagon_example.py
python3 research/min-cycles/octagon_example.py 00001101
node research/min-cycles/octagon-order.mjs
node research/min-cycles/theta-search.mjs 7
node research/min-cycles/theta-search.mjs 8
node research/min-cycles/theta-search.mjs 9
node research/min-cycles/block-search.mjs 24
node research/min-cycles/block-search-exact.mjs 26
node research/min-cycles/block-search-exact.mjs 25 --prune-extensions
node research/min-cycles/block-search-exact.mjs 27 --prune-extensions
node research/min-cycles/block-search-exact.mjs 25 --prune-extensions --two-layer-bounds
node research/min-cycles/block-search-exact.mjs 25 --prune-extensions --two-layer-bounds --repair-ears
node research/min-cycles/block-search-exact.mjs 28 --prune-extensions --two-layer-bounds --repair-ears
node research/min-cycles/forced-block-purchases.mjs 30
```

For octagons, weighted inequalities give `α ≤ n` in 20 of the 22
ownership classes. In both exceptions, the two vertices buying two
cycle edges are at positions 0 and 6 in the canonical labelling. For
an outside destination, a vertex with no off-cycle neighbour satisfies
the degree-two distance identity. An off-cycle neighbour of a cycle
vertex has more restricted labels because appending the shorter cycle
arc to the first step gives a simple path. Both facts constrain the
weighted inequalities along with the exact distances to the eight
cycle vertices. The integer checker gives minimum orders 201 and 157
for the two ownership classes at `α > n`. The checked Lean girth-eight
theorem therefore strengthens to girth nine through 156 players using
the external octagon certificates.

The two graph families verify the limitation of deviations confined
to cycle purchases. For both families the script checks the intercept
and slope of every connected change among 1,024 strategies. A player
can save cost by buying a link to an outside hub in each family.

Every connected cyclic graph of girth at least seven is a cactus or
contains a theta subgraph of three internally disjoint paths between two
vertices. The cactus swap argument is in the research notes. The
JavaScript check extends each possible theta and finds an edge whose
buyer can profitably swap it in either purchase direction. It excludes
all connected theta extensions through 15 players at minimum cycle
length seven, through 16 players at minimum cycle length eight, and
through 18 players at minimum cycle length nine.

The block search starts with a theta and adds ears to cover every
non-cycle biconnected block of the test sizes. Each outside vertex
contributes one unit of weight at its attachment vertex of the block.
The algorithm compares the weighted distance gains of single swaps.
For every allowed positive weight vector it finds an edge whose buyer
can swap profitably in either ownership direction. It uses worst-case
gains to check families of weights at once. The original search covers
all player counts through 24. The fixed-total search canonically labels
the multigraph obtained by suppressing degree-two vertices and checks
every attachment-weight vector of a fixed total. The runs through 25 and
for 26 players covered 197,593 and 731,205 isomorphism classes respectively.
There are 533,612 classes of order exactly 26. The unpruned run for
27 players covered 2,827,665 classes, with 2,096,460 of order exactly 27.
With ear pruning the run reached 396,906 canonical classes. Both modes
used 5,837 weight-search branches. The run for 28 players with the
two-layer bounds and restricted ear extensions reached 1,562,065 canonical
classes, including 226,967 of order exactly 28, and completed 4,042
weight-search branches. These counts cover the classes reached after
pruning. The combined searches and cycle-block exclusion give the tree
conclusion for `α > n` through 28 players. Lean proves the cycle-block
exclusion. The finite enumeration runs outside Lean.

For a theta block with three internally disjoint paths of lengths
`a ≤ b ≤ c`, assume `a+b ≥ 7` and `b ≥ a+4`. Choose a block vertex
with a largest attachment and one of the two long paths whose interior
avoids that vertex. Distances to the chosen vertex along this path are
the minimum of the two lengths obtained by routing through its ends.
The distance between the ends is `a`. Paths of three consecutive
edges are geodesic in the block by its girth, and shortest paths
between block vertices stay in the block. Thus the metric thread
theorem excludes this theta block for every positive attachment weight
vector and all positive edge prices. The Lean theorem checks the local
metric argument. The theta application uses the path description above.

For every block of girth at least nine formed by at least three
internally disjoint paths with common endpoints, the remaining cases
are covered by `ThetaMetric.lean` once the path geometry is supplied. If the endpoint distance is one or two, two paths are at least four
longer, so one such path avoids the maximum-weight vertex in its
interior and the long-thread argument applies. In the remaining cases,
for a maximum-weight vertex inside one path, use the off-target theorem
on any two paths avoiding that vertex, indexed from the closer endpoint. For a
maximum-weight endpoint, a path at least four longer than the endpoint
distance is already forbidden. Otherwise two paths of length at least five satisfy
the endpoint theorem. Distances to the target are the minimum of the
routes through the ends, and the three-edge routes across the common
endpoint are geodesic. This proves the exclusion analytically at every
positive edge price. Lean checks the metric implications, with the
translation from the theta block to those metric hypotheses given by
the geometric argument. In particular, an equilibrium block of girth at least nine and cycle rank at least
two has at least three vertices of internal degree greater than two.

For any biconnected equilibrium block of girth at least eight and
cycle rank `r ≥ 2`, suppress its degree-two vertices. Choose a vertex
`x` of maximum attachment weight. The compressed edges of length at
least five whose interiors avoid `x` form a forest, including exclusion
of parallel pairs. Each retained path is directed from its endpoint
nearer `x` to its endpoint farther away. Two incoming paths at any
vertex would yield incompatible swap bounds. In particular the block
has at least `r − 1` compressed edges of length at most four, and at
least `r` if `x` is a branch vertex or lies in a short path.
`ThreadGeometry.lean` verifies the forest and parallel-pair exclusion
for the supplied block paths. Suppressing the chains and counting
edges give the stated combinatorial corollary. At `α > n`, the checked
girth bound of eight makes this reasoning applicable at any player
count.

The forest also contains every three-edge chain whose endpoint
distances to `x` differ, and every four-edge chain whose endpoint
distances differ by at least two. As before, the retained chains have
interiors avoiding `x`. A four-edge chain with distance gap one joins
the forest if its middle vertex buys the edge toward the farther end.
Otherwise the last interior vertex toward that end buys both its path
edges. A four-edge chain at equal levels has two such buyers, one next
to each endpoint. Consequently, outside the at-most-one chain
containing `x` internally, at least `r − 1` chains are among the
following: length at most two, length three at equal levels, length
four at equal levels, or length four with gap one and the specified
double buyer.

In a bipartite block a three-edge chain always has unequal endpoint
distances to `x`, and a four-edge chain always has an even distance
gap. If all chains have length at least three, a block of cycle rank
`r ≥ 2` therefore has at least `2(r − 1)` degree-two vertices that
buy both incident block edges. This excludes bipartite blocks with
all chain lengths equal to three or at least five. The forest, parity,
and ownership lemmas are checked in Lean. The count uses the same
compression and forest edge bound as above.

For a purchased edge across an internal degree-two vertex, swapping
to the next vertex gains a step for every attachment reached
geodesically through that next vertex. The weight of the skipped
attachment bounds the total of these gains. At girth eight, every
simple path of length at most four is geodesic. Thus a chain's
successor weights and, near either endpoint, its other neighbours
give necessary lower bounds on the internal weights.

Two opposite inward purchases at separation two or three cannot
coexist. Forward purchases therefore propagate at every separation
of at least two. The resulting words consist of a block of backward
purchases followed by a block of forward purchases, with one
possible adjacent inversion at the boundary. The checker evaluates
these `2L` words for a chain of length `L`, propagates lower bounds
from both ends, and takes the minimum required excess. Distinct
chain interiors use disjoint attachment sets, so their lower bounds
add. At endpoints of degree three, the lower bounds for lengths
three through six are two, three, six, and eight outside vertices.
`ChainWeights.lean` checks the swap inequalities, propagation, and
the classification of ownership words.
By default, the budget check prunes weight tests while extending the
corresponding blocks. Add `--prune-extensions` to skip entire branches
when their attachment deficit persists in every continuation. At a
partially constructed block with `R` vertex slots remaining, a vertex
whose eccentricity `E` satisfies `E + R + 1 < g` cannot be an endpoint
of any later ear in a graph of girth at least `g`. A new vertex reached
after consuming `s` slots is at distance at most `E + s`. The next
ear has length at most `R - s + 1`, so the cycle it would close is
too short. Lean checks this bound in `EarPruning.lean`.

A chain with every interior vertex below the threshold keeps its
internal degrees in any continuation. Its attachment budget can
only increase as endpoint degrees increase. If the sum of these
budgets exceeds `R`, the checker skips the branch before canonical
labelling. The optional mode reports canonical classes reached by
the remaining search and the number of successful pruning tests.
Equivalent labelled visits can trigger the pruning test more than
once.

For fixed totals of 24 and 25, the optional mode and the full
enumeration reach the same numbers of weight-search branches (79 and
328). At 25 players the optional mode reaches 28,567 canonical block
classes, down from 197,593 in the full enumeration.

With `--two-layer-bounds`, when a skip lands directly at a chain endpoint
of block degree `d`, each branch other than the skipped one supplies a
neighbour and a second distinct improved vertex. These vertices are
all distinct in girth at least eight. Lean gives the inequality
`w(skip) ≥ w(endpoint) + 2(d − 1)` in `TwoLayerWeights.lean`. A three-edge
chain whose ends have degree at least three therefore needs four outside
vertices, even when the middle edge can be purchased in either direction.
At degree three on both ends, the strengthened check gives lower bounds
of four, three, ten, and fourteen outside vertices for lengths three
through six. At totals 25 and 27 the stronger check leaves 24 and 308
weight-search branches, compared with 328 and 5,837 respectively.

The `--repair-ears` option selects chains whose combined required
attachment weight exceeds the remaining budget. Any feasible extension
has to add an edge at an internal vertex of at least one selected chain.
In the final two-connected block, a path from that edge's other end back
to the partial block can avoid the first endpoint. Truncating it at
first entry gives an ear that can be added immediately. The generator
therefore needs to try only ears with an endpoint on a selected chain.
`TwoConnectedOn.exists_ear_with_first_edge` checks this construction in
Lean. At total 25 this option preserves all 24 weight-search branches
and reduces successful frozen-branch pruning tests from 1,071,943 to
750,201 as fewer extensions are generated.

`CycleBlocks.lean` excludes a block in which every vertex has degree two.
A minimum-weight vertex must purchase both incident block edges by the
swap inequality. Propagation around the cycle then forces the last edge
to be purchased toward that vertex.

A cycle through a vertex of block degree at least three and an ear starting
there force `3g ≤ 2(|S| + 1)`, where `g` is a lower bound on girth and `S`
is the block. The two arcs of the cycle and the ear bound the sum of the
three cycle lengths. With `g = 8` a block needs at least eleven vertices,
so an equilibrium is a tree at `α > n` through ten players. With `g = 9`
the same inequality requires at least thirteen block vertices.

The search first tries the Lean-checked ownership restrictions for
each possible maximum-weight vertex. If those implications do not
force incompatible owners, it checks the remaining block with the
weighted swap enumeration. With girth at least nine and at most 30
vertices in the block, the ownership check alone excludes 283 of 511
theta length triples for every positive attachment weight vector.

The use of distance-label LPs for short cycles was developed in §4 of
the earlier work.
[Mamageishvili–Mihalák–Müller, Internet Mathematics (2015)](https://www.internetmathematicsjournal.com/article/1588.pdf)

## Weighted blocks at arbitrary order

For a maximal two-connected block, give each vertex the size of its
attachment as weight. When a unilateral deviation changes only purchases
within the block, the distance sum equals the weighted core distance sum
plus an unchanged exterior term. The total weight equals `n`. If some
player is attached outside the core at `v`, adding a shortcut from that
player gives the weighted leaf inequality for `v`. Lean checks both
necessary systems. The converse via replacement of the exterior by
hub-owned leaves is recorded as a mathematical proof in the research
notes.

Choose a block root of minimum distance sum and any shortest-path parent
tree from it. At `α > n`, each non-root player buys at most one edge
that is not to a child in that tree. Replacing all such purchases with a
link to the root preserves the root's distances. A buyer of an off-tree
edge therefore does not buy its own parent edge. Its depth is at least
three by the girth bound. If `D` counts parent edges bought by the
parent toward a block child at depth at least three, the checked edge
bound is `|E(H)| ≤ |V(H)| − 1 + D ≤ 2(|V(H)| − 1)`. Every block
then has a vertex of degree two or three.

For a fixed core ownership and a prescribed set of vertices carrying
leaves, the following generator prints its mixed-integer model in LP
syntax. The integer weights range over all total player counts.

```sh
node research/min-cycles/block-weight-milp.mjs < core.json > core.lp
```

The JSON fields are `profile`, the list of purchased-neighbour arrays,
and `active`, the indices with an exterior attachment. A candidate
nonnegative combination of deviation rows can be checked by
`price_le_total_weight_of_deviation_certificate`. Its price coefficient
must be `−c` for a positive `c`, with each distance coefficient at
most `c`.

## Reproduce the experiments

The Python programs use the standard library. Profile JSON files are
arrays of purchased-neighbor lists, indexed from zero. A price threshold
may be an integer, decimal, or fraction. The inequalities are exact.

```sh
python3 research.py scan 8 --above 6
python3 research.py verify examples/eight-player-certificate.json
python3 research.py analyze examples/eight-player-profile.json --above 6 --smt /tmp/tree-example.smt2
python3 research/lemma-9/check_degree_two.py .
```

The scan takes one graph representative per isomorphism class and tests
every single-owner assignment on it. It prunes triangles when the strict
price threshold is at least `n − 2`, and at eight vertices it also prunes
squares at that threshold. At eight players and threshold six, the search
checks 24 graphs and 8,448 ownership assignments. Of those, 7,888 are
refuted by a single deletion, 558 more by single additions or swaps, and
two by a larger unilateral deviation. The JavaScript cross-check runs as
`node scan.mjs 8 6`.

The degree-two script checks the distance changes for both deviations
in Lemma 9 on all connected labeled graphs through six vertices and on
a fixed sample of larger graphs through ten vertices.

Use `--keep-triangles` to turn off short-cycle pruning. At eight players,
`--keep-squares` disables square pruning alone. The optional SMT-LIB
output can be checked by Z3. `research.py prompt` turns analysis JSON into
research context for a model.

The [research notes](cactus-and-search.md)
give a mathematical proof for cactus graphs at `α > n − 1`. The weighted
pentagon inequality is compiled in Lean. The cactus decomposition and
its distance formulas are still outside the formalization.
