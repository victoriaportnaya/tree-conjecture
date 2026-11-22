import Lax869952Proofs.WeightedBlocks

set_option warningAsError true

namespace Lax869952Proofs

open scoped BigOperators

/-- A nonnegative combination of deviation rows can rule out all weights
at once. If the combined price coefficient is `-c` and each combined
distance coefficient is at most `c`, then the price is at most total weight. -/
theorem price_le_total_weight_of_deviation_certificate {m k : ℕ}
    (price c : ℝ) (weight : Fin m → ℝ) (multiplier priceChange : Fin k → ℝ)
    (distanceChange : Fin k → Fin m → ℝ)
    (hC : 0 < c) (hWeight : ∀ v, 0 ≤ weight v)
    (hMultiplier : ∀ r, 0 ≤ multiplier r)
    (hRows : ∀ r, 0 ≤ priceChange r * price + ∑ v, distanceChange r v * weight v)
    (hPrice : (∑ r, multiplier r * priceChange r) = -c)
    (hDistance : ∀ v, (∑ r, multiplier r * distanceChange r v) ≤ c) :
    price ≤ ∑ v, weight v := by
  have hCollect :
      (∑ r, multiplier r * (priceChange r * price + ∑ v, distanceChange r v * weight v)) =
        (∑ r, multiplier r * priceChange r) * price +
          ∑ v, (∑ r, multiplier r * distanceChange r v) * weight v := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_mul]
      simp only [mul_assoc]
    · simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_mul]
  have hNonneg : 0 ≤
      ∑ r, multiplier r * (priceChange r * price + ∑ v, distanceChange r v * weight v) :=
    Finset.sum_nonneg fun r _ => mul_nonneg (hMultiplier r) (hRows r)
  rw [hCollect, hPrice] at hNonneg
  have hUpper :
      (∑ v, (∑ r, multiplier r * distanceChange r v) * weight v) ≤
        c * ∑ v, weight v := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_right (hDistance v) (hWeight v)
  by_contra! hPriceLarge
  have hStrict := mul_lt_mul_of_pos_left hPriceLarge hC
  linarith

#print axioms price_le_total_weight_of_deviation_certificate

end Lax869952Proofs
