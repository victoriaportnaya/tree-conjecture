import Lax869952.NashEquilibrium
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
---
title: Girth at least eight at price above the player count
type: theorem
---
At $\alpha>n$, every cycle in a pure Nash equilibrium has at least eight edges.
-/

namespace Lax869952.GirthAtPopulationPrice

open Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal BigOperators

axiom statement {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    {u : Fin n} (p : (graph s).Walk u u) (hp : p.IsCycle) : 8 ≤ p.length

end Lax869952.GirthAtPopulationPrice
