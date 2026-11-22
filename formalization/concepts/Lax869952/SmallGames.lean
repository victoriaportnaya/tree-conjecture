import Lax869952.NashEquilibrium
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
---
title: The Tree Conjecture for up to ten players
type: theorem
---
For $1\le n\le10$ and $\alpha>n$, every pure Nash equilibrium graph is a tree.
-/

namespace Lax869952.SmallGames

open Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal BigOperators

axiom statement {n : ℕ} (hn : 0 < n) (hsmall : n ≤ 10)
    (s : Profile n) (α : ℝ≥0) (hα : (n : ℝ≥0) < α)
    (hne : IsNashEquilibrium α s) : (graph s).IsTree

end Lax869952.SmallGames
