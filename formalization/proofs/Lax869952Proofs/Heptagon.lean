import Lax869952Proofs.HeptagonChecks0
import Lax869952Proofs.HeptagonChecks1
import Lax869952Proofs.HeptagonChecks2
import Lax869952Proofs.Pentagon

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal
open CycleCertificate CycleCertificate.Cycle7

private theorem symmetries7 : Symmetries 7 := by decide

private theorem checksEveryRepresentative : ∀ c ∈ certificates, Checks c.1 c.2 1 1 := by
  intro c hc
  simp only [certificates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CycleCertificate.Cycle7.checked0
  · exact CycleCertificate.Cycle7.checked1
  · exact CycleCertificate.Cycle7.checked2
  · exact CycleCertificate.Cycle7.checked3
  · exact CycleCertificate.Cycle7.checked4
  · exact CycleCertificate.Cycle7.checked5
  · exact CycleCertificate.Cycle7.checked6
  · exact CycleCertificate.Cycle7.checked7
  · exact CycleCertificate.Cycle7.checked8
  · exact CycleCertificate.Cycle7.checked9

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem coverage7 : (vectors [false, true] 7).all
    (covered certificates) = true := by decide

/-- An equilibrium with an isometric heptagon satisfies `α ≤ n`. -/
theorem nash_isometric_heptagon_price_bound {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {u : Fin n} (p : (graph s).Walk u u)
    (hp : IsometricCycle p) (hlen : p.length = 7) : (α : ℝ) ≤ n := by
  simpa using price_bound_from_representatives s α hne (by decide : 0 < 7)
    (Embedding.of_isometric_cycle p hp hlen)
    1 1 symmetries7 certificates checksEveryRepresentative coverage7

#print axioms nash_isometric_heptagon_price_bound

end Lax869952Proofs
