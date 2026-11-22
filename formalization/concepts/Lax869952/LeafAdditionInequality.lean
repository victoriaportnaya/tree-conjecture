import Lax869952.NashEquilibrium
import Lax869952.BlockGeometry

/-!
---
title: Weighted leaf addition inequality for a maximal block
type: theorem
---
If a block vertex $v$ has another player in its attachment, its attachment and the block distances satisfy every single-addition inequality of a leaf at $v$. The weights are actual attachment cardinalities.
-/

namespace Lax869952.LeafAdditionInequality

open Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal BigOperators

axiom statement {n : ℕ} {S : Finset (Fin n)} (α : ℝ≥0) (s : Profile n)
    (hne : IsNashEquilibrium α s) (hS : BlockGeometry.IsBiconnectedBlock (graph s) S)
    {v r : Fin n} (hv : v ∈ S) (hr : r ∈ S) (hvr : v ≠ r)
    (hWeight : 1 < (BlockGeometry.blockAttachment (graph s) S v).card) :
    (∑ z ∈ S, ((BlockGeometry.blockAttachment (graph s) S z).card : ℝ) *
      max 0 (((BlockGeometry.blockGraph (graph s) S).dist v z : ℝ) -
        ((BlockGeometry.blockGraph (graph s) S).dist r z : ℝ))) ≤ (α : ℝ)

end Lax869952.LeafAdditionInequality
