import TreeConjecture.HexagonChecks0
import TreeConjecture.HexagonChecks1
import TreeConjecture.Pentagon

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped NNReal
open CycleCertificate CycleCertificate.Cycle6

private theorem symmetries6 : Symmetries 6 := by decide

private theorem checksEveryRepresentative : ∀ c ∈ certificates, Checks c.1 c.2 1 1 := by
  intro c hc
  simp only [certificates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CycleCertificate.Cycle6.checked0
  · exact CycleCertificate.Cycle6.checked1
  · exact CycleCertificate.Cycle6.checked2
  · exact CycleCertificate.Cycle6.checked3
  · exact CycleCertificate.Cycle6.checked4
  · exact CycleCertificate.Cycle6.checked5
  · exact CycleCertificate.Cycle6.checked6
  · exact CycleCertificate.Cycle6.checked7
  · exact CycleCertificate.Cycle6.checked8

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem coverage6 : (vectors [false, true] 6).all
    (covered certificates) = true := by decide

/-- An equilibrium with an isometric hexagon satisfies `α ≤ n`. -/
theorem nash_isometric_hexagon_price_bound {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {u : Fin n} (p : (graph s).Walk u u)
    (hp : IsometricCycle p) (hlen : p.length = 6) : (α : ℝ) ≤ n := by
  simpa using price_bound_from_representatives s α hne (by decide : 0 < 6)
    (Embedding.of_isometric_cycle p hp hlen)
    1 1 symmetries6 certificates checksEveryRepresentative coverage6

#print axioms nash_isometric_hexagon_price_bound

end TreeConjecture
