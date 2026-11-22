import Lax869952.NashEquilibrium
import Lax869952.BlockGeometry

/-!
---
title: Deletion bound for a purchase into a degree-two block vertex
type: theorem
---
Let $v$ have degree two in a maximal cyclic block of a Nash equilibrium of girth at least eight. If a neighbor buys an edge into $v$, then for any cycle of length $c$ through $v$ in that block, the attachment weight $w(v)$ satisfies

$$\alpha+6\le 2(c-3)w(v).$$

The result allows either owner of the other edge incident to $v$.
-/

namespace Lax869952.ReceiverDeletionBound

open Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal BigOperators

axiom statement {n : ℕ} {S : Finset (Fin n)} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : BlockGeometry.IsBiconnectedBlock (graph s) S)
    [DecidableRel (BlockGeometry.blockGraph (graph s) S).Adj]
    (girth : ∀ {x}, (p : (graph s).Walk x x) → p.IsCycle → 8 ≤ p.length)
    {u v w : Fin n} (huv : (BlockGeometry.blockGraph (graph s) S).Adj u v)
    (hvw : (BlockGeometry.blockGraph (graph s) S).Adj v w) (huw : u ≠ w)
    (hdegree : (BlockGeometry.blockGraph (graph s) S).degree v = 2)
    (hBuy : v ∈ (s u).val)
    (c : (BlockGeometry.blockGraph (graph s) S).Walk v v) (hc : c.IsCycle) :
    (α : ℝ) + 6 ≤ 2 * ((c.length : ℝ) - 3) *
      ((BlockGeometry.blockAttachment (graph s) S v).card : ℝ)

end Lax869952.ReceiverDeletionBound
