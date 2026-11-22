import TreeConjecture.Hexagon
import TreeConjecture.Heptagon

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped NNReal

/-- For α > n, any cycle in a Nash equilibrium has length at least eight. -/
theorem nash_cycle_length_ge_eight {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    {u : Fin n} (p : (graph s).Walk u u) (hp : p.IsCycle) : 8 ≤ p.length := by
  have hPrice : (n : ℝ) < α := by exact_mod_cast hα
  have hSix {v : Fin n} (q : (graph s).Walk v v) (hq : q.IsCycle) : 6 ≤ q.length :=
    nash_cycle_length_ge_six s α hα hne q hq
  have hSeven {v : Fin n} (q : (graph s).Walk v v) (hq : q.IsCycle) : 7 ≤ q.length := by
    by_contra hlt
    have hLen : q.length = 6 := by have := hSix q hq; omega
    have hIso := globally_shortest_cycle_isometric q hq fun z hz => hLen.symm ▸ hSix z hz
    exact (not_le_of_gt hPrice) (nash_isometric_hexagon_price_bound s α hne q hIso hLen)
  by_contra hlt
  have hLen : p.length = 7 := by have := hSeven p hp; omega
  have hIso := globally_shortest_cycle_isometric p hp fun q hq => hLen.symm ▸ hSeven q hq
  exact (not_le_of_gt hPrice) (nash_isometric_heptagon_price_bound s α hne p hIso hLen)

theorem nash_tree_of_le_seven_at_n {n : ℕ} (hn : 0 < n) (hsmall : n ≤ 7)
    (s : Profile n) (α : ℝ≥0) (hα : (n : ℝ≥0) < α)
    (hne : IsNashEquilibrium α s) : (graph s).IsTree := by
  refine ⟨nash_connected hn α s hne, ?_⟩
  intro u p hp
  have hMin := nash_cycle_length_ge_eight s α hα hne p hp
  have hMax := hp.nodup_dropLast_support.length_le_card
  simp [Walk.length_support] at hMax
  omega

#print axioms nash_cycle_length_ge_eight
#print axioms nash_tree_of_le_seven_at_n

end TreeConjecture
