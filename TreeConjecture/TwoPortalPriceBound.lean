import TreeConjecture.TwoPortalCertificateCheck
import TreeConjecture.WeightedCertificates
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

set_option warningAsError true

namespace TreeConjecture.TwoPortalCertificate

open scoped BigOperators

private theorem sum_getElem_eq_sum_map (moves : List Move) (f : Move → ℤ) :
    (∑ i : Fin moves.length, f moves[i.val]) = (moves.map f).sum := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map moves f)

/-- The exact certificate bounds the price for every nonnegative vector
of weights on the cycle and exterior distance classes. The rows are
the inequalities supplied by unilateral deviations in the two-portal model. -/
theorem price_le_total_weight (o : Fin 256) (α : ℝ) (w : Fin 23 → ℝ)
    (hWeight : ∀ z, 0 ≤ w z)
    (hRows : ∀ m ∈ certificate o,
      0 ≤ (priceChange o.val m : ℝ) * α +
        ∑ z, (distanceChange m z : ℝ) * w z) :
    α ≤ ∑ z, w z := by
  let ms := certificate o
  let move (i : Fin ms.length) := ms[i.val]
  let c : ℤ := -combinedPrice o.val ms
  have checked := checked_conditions (certificate_checked o)
  have hC : (0 : ℝ) < (c : ℝ) := by
    exact_mod_cast (show 0 < c from neg_pos.mpr checked.2.1)
  apply price_le_total_weight_of_deviation_certificate α (c : ℝ) w
    (fun i => ((move i).multiplicity : ℝ))
    (fun i => (priceChange o.val (move i) : ℝ))
    (fun i z => (distanceChange (move i) z : ℝ)) hC hWeight
  · intro i
    exact Nat.cast_nonneg _
  · intro i
    exact hRows (move i) (List.getElem_mem _)
  · have hP : (∑ i : Fin ms.length, ((move i).multiplicity : ℤ) *
          priceChange o.val (move i)) = -c := by
      change (∑ i : Fin ms.length, (ms[i.val].multiplicity : ℤ) *
        priceChange o.val ms[i.val]) = -c
      rw [sum_getElem_eq_sum_map ms (fun m => (m.multiplicity : ℤ) * priceChange o.val m)]
      simp [c, ms, combinedPrice]
    exact_mod_cast hP
  · intro z
    have hD : (∑ i : Fin ms.length, ((move i).multiplicity : ℤ) *
          distanceChange (move i) z) ≤ c := by
      change (∑ i : Fin ms.length, (ms[i.val].multiplicity : ℤ) *
        distanceChange ms[i.val] z) ≤ c
      rw [sum_getElem_eq_sum_map ms (fun m => (m.multiplicity : ℤ) * distanceChange m z)]
      exact checked.2.2 z
    exact_mod_cast hD

#print axioms price_le_total_weight

end TreeConjecture.TwoPortalCertificate
