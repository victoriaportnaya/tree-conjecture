# Formal Tree Bounds for the Sum Network Creation Game

Each player pays a price `α` per edge it purchases and the sum of its
undirected distances to every other player. Its strategy may replace its
entire purchased edge set. The Tree Conjecture asks whether every pure Nash
equilibrium is a tree when `α > n`.

## Lean development

[Lax Lean Archive entry lax-869952](https://laxarchive.org/lax-869952/index.html)
presents the five results independently checked by the archive. The
[submitted package](https://github.com/victoriaportnaya/tree-conjecture/tree/74e2373388cdfe34d2ec9afe2e64d58c7936ae78/formalization)
contains the exact Lean sources used for verification.

| Result | Scope |
| --- | --- |
| [Dippel and Vetta's tree theorem](formalization/concepts/Lax869952/TreeAtDoublePrice.lean) | At `α > 2n`, every equilibrium graph is a tree. |
| [Girth bound](formalization/concepts/Lax869952/GirthAtPopulationPrice.lean) | At `α > n`, every equilibrium cycle has length at least eight. |
| [Small games](formalization/concepts/Lax869952/SmallGames.lean) | At `α > n`, the tree conclusion holds on one through ten players. |
| [Receiver deletion inequality](formalization/concepts/Lax869952/ReceiverDeletionBound.lean) | For a degree-two receiver in a maximal cyclic block, `α + 6 ≤ 2(c − 3)w(v)` under the girth-eight hypothesis. |
| [Leaf addition inequality](formalization/concepts/Lax869952/LeafAdditionInequality.lean) | A nontrivial attachment supplies the weighted Nash inequalities for single additions by a leaf. |

The [annotated proofs](formalization/proofs/Lax869952Proofs/ArchiveProofs.lean)
discharge the five statement declarations. They invoke the checked mathematics
in the proof package and do not use those statement declarations as
hypotheses. The standalone project keeps the original Lean namespaces. See
the [module index and build instructions](docs/lean-development.md).

## Companion research

The [English manuscript source](paper/main.tex) proves the tree conclusion
at `α > 2n − 24` for `n ≥ 48`, `α > 2n − 27` for `n ≥ 54`, and
`α > 2n − 30` for `n ≥ 79`. Its argument combines a girth-dependent block
bound with integer certificates for shorter cycles. These additive refinements
use the mathematical argument and the external integer checker.

```sh
node research/min-cycles/short-cycle-certificates.mjs
```

The companion notes include the [exact block reduction](docs/block-reduction.md),
[cactus proof and finite searches](docs/cactus-and-search.md),
[structural block bounds](docs/structural-results.md), and the proof for
[graphs without a K4 minor](research/min-cycles/k4-minor-free.md).
The general conjecture at `α > n` remains open in this development.

## Provenance and licensing

The model and parts of the basic cost proofs adapt
[Lax entry lax-899194](https://laxarchive.org/lax-899194/index.html).
The upstream license is in [LICENSE-Lax899194](LICENSE-Lax899194).
The development formalizes [Dippel and Vetta's published result](https://doi.org/10.4230/LIPIcs.STACS.2024.28)
and includes further inequalities. OpenAI Codex assisted with Lean proofs,
mathematical exploration, certificates and exposition.

The archive submission and the Lean source are available under the
[Apache License 2.0](formalization/LICENSE).
