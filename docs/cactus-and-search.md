# Cactus equilibria and small-network computations

The cactus proof below is mathematical. The small-network tables summarize finite computations. The source release supplies the exhaustive search programs and the Lean proof through ten players.

# Exhaustive results for α > n

| Players | Connected cyclic graph representatives | Ownership assignments | Refuted by a single deletion | First refuted when additions and swaps were allowed | Survivors |
|---:|---:|---:|---:|---:|---:|
| 3 | 0 | 0 | 0 | 0 | 0 |
| 4 | 1 | 16 | 16 | 0 | 0 |
| 5 | 3 | 128 | 128 | 0 | 0 |
| 6 | 13 | 1,920 | 1,920 | 0 | 0 |
| 7 | 48 | 22,400 | 22,272 | 128 | 0 |
| 8 | 24 | 8,448 | 7,936 | 512 | 0 |

The search takes one representative of each isomorphism class of eligible connected cyclic graphs and tests every assignment of one buyer to each edge. Disconnected profiles and double purchases are excluded by one-step deviations. Triangles are excluded in every row, and 4-cycles are also excluded in the row for eight players. The count for two players is vacuous. The Python and JavaScript runs agree at six, seven, and eight players. The Python scan supports both eight-player price thresholds. The scans are computational evidence, with no Lean certificate for exhaustive coverage.

The seven-player example below survives single deletions throughout 7 < α ≤ 9. Player 0 can replace the purchase to player 5 with a purchase to player 3 and keep the purchase to player 6. This saves one unit of distance at the same edge cost for every α.

```json
{
  "purchases": [
    [
      5,
      6
    ],
    [
      4,
      6
    ],
    [
      3,
      5
    ],
    [
      4
    ],
    [],
    [],
    []
  ],
  "above": "7",
  "witnesses": [
    {
      "player": 0,
      "targets": [
        3,
        6
      ],
      "a": 0,
      "b": -1
    }
  ]
}
```

For eight players the same search also refuted all 8,448 tested assignments at α > 6. Single deletions refuted 7,888, single edits and swaps refuted another 558, and the last two required replacing more than one purchased edge. In the certificate below, player 2 drops its purchases to players 6 and 7 and buys a link to player 5. The cost change is 4 − α.

```json
{
  "purchases": [
    [],
    [],
    [
      6,
      7
    ],
    [],
    [
      5,
      7
    ],
    [
      3,
      6
    ],
    [
      1
    ],
    [
      0
    ]
  ],
  "above": "6",
  "witnesses": [
    {
      "player": 2,
      "targets": [
        5
      ],
      "a": -1,
      "b": 4
    }
  ]
}
```

# Cactus equilibria

The same argument applies whenever removing the edges of a cycle leaves components each containing exactly one cycle vertex. Write wᵢ for the positive number of vertices in the component attached to cycle vertex i, indexed modulo the cycle length k. In a cactus graph every cycle has this property. A distance from a cycle vertex to any vertex in component i is the distance to i along the cycle plus the distance within component i. Replacing a cycle edge while keeping the cycle vertices connected preserves the latter term.

Suppose i buys the edge to i+1. For k ≥ 5, it can swap this purchase for the chord to i+2. The distance to i+1 increases by one. The distances to i+2 through i+⌊k/2⌋ decrease by one, and all others stay fixed. Therefore every such purchased edge requires the following at equilibrium. Reverse the indices for an edge owned in the other direction.

```math
w_{i+1}\ \ge\ \sum_{j=2}^{\lfloor k/2\rfloor} w_{i+j}.
```

For k ≥ 6, set m = ⌊k/2⌋ and place a maximum component weight at vertex 0. Each edge j to j+1 for 1 ≤ j ≤ m−1 must be purchased by j, since the reverse purchase would put w₀ and another positive term on the right. Reversing the indexing forces the corresponding edges on the other side of 0. For k = 2m, select the forced edges from m−2 to m−1 and from m+2 to m+1. For k = 2m+1, select the forced edges from m−1 to m and from m+2 to m+1. In both cases each target’s weight must exceed the other target’s weight, a contradiction.

For k = 5, deleting an edge with target weight t raises distances in its target component by three and in the following component by one. If that following weight is u, Nash requires α ≤ 3t + u. The swap inequality is t ≥ u. Every orientation falls into one of the following cases.

- **Directed cycle.** Summing the five deletion bounds gives 5α ≤ 4n. As n ≥ 5, this implies α ≤ n − 1.

- **One source with arms of lengths 1 and 4.** Let s and t be the source and sink weights. By the swaps, the three internal weights on the long arm are a ≥ b ≥ c = t. The last edge of that arm gives α ≤ 3t + s, and n − (3t + s) = a + b − t ≥ 1.

- **One source with arms of lengths 2 and 3.** The two internal weights immediately before the sink both equal its weight t by the swap inequalities on the arms and at the sink. The other internal weight b is at least t. Deleting either edge into the sink gives α ≤ 4t, and n − 4t = s + b − t ≥ 1.

- **Two sources.** Up to cycle rotation and reversal, the purchases are 0→1→2, 3→2, 3→4, and 0→4. The swaps imply w₁ = w₂ = t. If t < w₀ + w₄, deleting 1→2 gives α ≤ 3t + w₃ ≤ n − 1. If t ≥ w₀ + w₄, deleting 0→4 gives α ≤ 3w₄ + w₃ ≤ n − 1.

Consequently a Nash equilibrium on a cactus graph can contain a cycle only for α ≤ n − 1. The directed bare pentagon reaches the bound at α = 4. The weighted swap formula was independently compared against exact graph distances for cycle lengths 5–60. Among pentagon attachment weights in {1,…,6}, all 6,242 weight and orientation pairs that passed the swaps satisfied the deletion bound.

# Weighted biconnected block search

Take any cyclic biconnected block of an equilibrium. Every component outside the block attaches to one of its vertices because a path between two distinct vertices through the outside would extend the block. Give each block vertex weight one plus the number of outside vertices attached there. The weights are positive integers summing to n.

If the block is a simple cycle, the weighted cycle swap argument above excludes it at minimum cycle length nine. A block with more edges contains a theta. Starting with that theta, add a path whose endpoints are distinct vertices already present and whose interior is new. A connected component of the remaining vertices has at least two distinct neighbours in the existing subgraph, or one vertex would separate the block. This supplies an ear until all vertices are covered. The remaining edges are ears of length one.

Adding an ear of length r between u and v preserves minimum cycle length g exactly when the current u-to-v distance plus r is at least g. The verifier enumerates all permitted ears. It identifies blocks using the lengths of their paths through degree-two vertices. Equal keys represent isomorphic blocks, and tied vertex orderings can leave more than one key for the same isomorphism class.

In a swap with the block still connected, the gain in distances to each attached region equals the gain in distance to its attachment vertex times the region's weight. The verifier finds an edge for which both endpoints have a profitable swap if they own it. Each swap keeps the buyer's purchase count. Lower bounds on gains cover whole ranges of weight vectors at once.

| Vertices in block | Block keys checked |
| ---: | ---: |
| 13 | 1 |
| 14 | 3 |
| 15 | 5 |
| 16 | 18 |
| 17 | 32 |
| 18 | 85 |
| 19 | 208 |
| 20 | 580 |
| 21 | 1,827 |
| 22 | 6,420 |
| 23 | 25,112 |
| 24 | 102,526 |

The run checks 136,817 block keys and covers all positive integer weights with total at most 24. Thus, together with the girth bound through 156 and the cycle-block argument, the tree conclusion follows for α > n through 24 players. Run `node research/min-cycles/block-search.mjs 24` from the [project archive](https://github.com/victoriaportnaya/tree-conjecture).

## Exact search for 25 players

For 25 players, the search excluded all 197,593 isomorphism classes of non-cycle biconnected blocks of girth at least nine and order at most 25. Of these, 142,162 have order 25 and 38,997 have order 24. The exclusion covers every positive integer attachment-weight vector with total exactly 25. The preceding search handles smaller player counts. Together with the minimum-girth and cycle-block arguments, this gives the tree conclusion for α > n and n ≤ 25.

The new key records the full matrix of sorted path-length multisets after suppressing degree-two vertices. Color refinement and branching over tied vertices produce the same matrix code under relabeling. Conversely a common code reconstructs the same weighted multigraph and hence isomorphic unweighted blocks. A separate permutation check on all 226 labelled non-cycle biconnected graphs on five vertices agreed with the nine classes found by the new key.

The first swap bound excludes 197,385 blocks before full swap evaluation. For an edge between degree-two vertices, swapping past the other endpoint saves at least one unit for every block vertex reached geodesically in those two steps. The only possible loss is at the skipped vertex and its attachments, of weight at most one plus the number of players outside the block. If both directions pass the bound, every ownership of the edge fails. Breadth-first distance recomputation confirmed all 2,040 early rejections in a separate check over theta blocks with up to three extra players.

The `Exact block search source` section contains the verifier. The exhaustive computation runs outside Lean.
