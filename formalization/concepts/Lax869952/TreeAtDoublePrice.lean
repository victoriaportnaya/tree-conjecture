import Lax869952.NashEquilibrium
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
---
title: Tree equilibria above twice the player count
type: theorem
---
On a positive number of players, an edge price $\alpha>2n$ forces every pure Nash equilibrium graph to be a tree. This is the theorem of Dippel and Vetta (STACS 2024, Theorem 1).
-/

namespace Lax869952.TreeAtDoublePrice

open Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal BigOperators

axiom statement {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 2 * (n : ℝ≥0) < α)
    (s : Profile n) (hne : IsNashEquilibrium α s) : (graph s).IsTree

end Lax869952.TreeAtDoublePrice
