import Lax869952Proofs.BlockSwaps

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

/-- Distance along a thread to an outside target reachable through either end. -/
def threadDistance (length fromStart fromEnd i : ℕ) : ℕ :=
  min (i + fromStart) (length - i + fromEnd)

/-- Near the maximum of the two-ended distance function, there are four
consecutive internal vertices whose middle vertices each have a two-step
shortest route outward. Both destinations in the middle are at distance
at least three if the endpoint distance data meet the stated bounds. -/
theorem exists_internal_thread_ridge (length fromStart fromEnd : ℕ)
    (hlen : 5 ≤ length)
    (hLeft : fromStart + 4 ≤ length + fromEnd)
    (hRight : fromEnd + 4 ≤ length + fromStart)
    (hZeroLeft : fromStart = 0 → 7 ≤ length + fromEnd)
    (hZeroRight : fromEnd = 0 → 7 ≤ length + fromStart) :
    ∃ i, 1 ≤ i ∧ i + 3 < length ∧
      threadDistance length fromStart fromEnd (i + 1) =
        2 + threadDistance length fromStart fromEnd (i - 1) ∧
      threadDistance length fromStart fromEnd (i + 2) =
        2 + threadDistance length fromStart fromEnd (i + 4) ∧
      3 ≤ threadDistance length fromStart fromEnd (i + 1) ∧
      3 ≤ threadDistance length fromStart fromEnd (i + 2) := by
  let k := (length + fromEnd - fromStart) / 2
  let i := if k + 3 ≤ length then k - 1 else k - 2
  have hk : 2 * k ≤ length + fromEnd - fromStart ∧
      length + fromEnd - fromStart ≤ 2 * k + 1 := by
    dsimp [k]
    omega
  have hIndices : 1 ≤ i ∧ i + 3 < length ∧
      2 * (i + 1) + fromStart ≤ length + fromEnd ∧
      length + fromEnd ≤ 2 * (i + 2) + fromStart := by
    dsimp only [i]
    split <;> omega
  obtain ⟨hi, hj, hb, hc⟩ := hIndices
  have hB : i + 1 + fromStart ≤ length - (i + 1) + fromEnd := by omega
  have hC : length - (i + 2) + fromEnd ≤ i + 2 + fromStart := by omega
  have hP : i - 1 + fromStart ≤ length - (i - 1) + fromEnd := by omega
  have hQ : length - (i + 4) + fromEnd ≤ i + 4 + fromStart := by omega
  refine ⟨i, hi, hj, ?_, ?_, ?_, ?_⟩
  · simp only [threadDistance, min_eq_left hB, min_eq_left hP]
    omega
  · simp only [threadDistance, min_eq_right hC, min_eq_right hQ]
    omega
  · simp only [threadDistance, min_eq_left hB]
    by_cases h : fromStart = 0
    · have hh := hZeroLeft h
      dsimp only [i]
      split <;> omega
    · omega
  · simp only [threadDistance, min_eq_right hC]
    by_cases h : fromEnd = 0
    · have hh := hZeroRight h
      dsimp only [i]
      split <;> omega
    · omega

/-- A maximum-weight attachment cannot see the two ends of a degree-two
thread within the specified distance difference. -/
theorem nash_block_no_balanced_metric_thread {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {L : ℕ} (v : ℕ → Fin n) (hLen : 5 ≤ L)
    (hAdjacent : ∀ i < L, (blockGraph (graph s) S).Adj (v i) (v (i + 1)))
    (hDegree : ∀ i, 0 < i → i < L → (blockGraph (graph s) S).degree (v i) = 2)
    (hThree : ∀ i, i + 3 ≤ L → (graph s).dist (v i) (v (i + 3)) = 3)
    {x : Fin n} (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (hLeft : (graph s).dist (v 0) x + 4 ≤ L + (graph s).dist (v L) x)
    (hRight : (graph s).dist (v L) x + 4 ≤ L + (graph s).dist (v 0) x)
    (hZeroLeft : (graph s).dist (v 0) x = 0 → 7 ≤ L + (graph s).dist (v L) x)
    (hZeroRight : (graph s).dist (v L) x = 0 → 7 ≤ L + (graph s).dist (v 0) x)
    (hMetric : ∀ i ≤ L, (graph s).dist (v i) x =
      threadDistance L ((graph s).dist (v 0) x) ((graph s).dist (v L) x) i) : False := by
  let G := graph s
  obtain ⟨i, hi, hj, hb, hc, hb3, hc3⟩ :=
    exists_internal_thread_ridge L _ _ hLen hLeft hRight hZeroLeft hZeroRight
  have hBack : G.dist (v (i + 1)) x = 2 + G.dist (v (i - 1)) x := by
    rw [hMetric (i + 1) (by omega), hMetric (i - 1) (by omega)]
    exact hb
  have hForward : G.dist (v (i + 2)) x = 2 + G.dist (v (i + 4)) x := by
    rw [hMetric (i + 2) (by omega), hMetric (i + 4) (by omega)]
    exact hc
  have hp : v (i - 1) ≠ x := by
    intro he
    have hh : 3 ≤ G.dist (v (i + 1)) x := (hMetric (i + 1) (by omega)).symm ▸ hb3
    rw [he, dist_self] at hBack
    omega
  have hq : v (i + 4) ≠ x := by
    intro he
    have hh : 3 ≤ G.dist (v (i + 2)) x := (hMetric (i + 2) (by omega)).symm ▸ hc3
    rw [he, dist_self] at hForward
    omega
  have hpa : (blockGraph G S).Adj (v (i - 1)) (v i) := by
    have he : i - 1 + 1 = i := by omega
    simpa only [he] using hAdjacent (i - 1) (by omega)
  exact nash_block_no_geodesic_ridge s α hne hS hpa
    (hAdjacent i (by omega)) (hAdjacent (i + 1) (by omega))
    (hAdjacent (i + 2) (by omega)) (hAdjacent (i + 3) (by omega))
    (hThree i (by omega)) (hDegree i (by omega) (by omega))
    (hDegree (i + 1) (by omega) (by omega)) (hDegree (i + 2) (by omega) (by omega))
    (hDegree (i + 3) (by omega) (by omega)) hx hp hq hBack hForward hMax

/-- A two-ended degree-two thread cannot be at least four steps longer than
the distance between its ends when a maximum-weight attachment sees the
thread through those ends. The metric hypotheses express those two-ended
distances and that three consecutive steps are geodesic. -/
theorem nash_block_no_long_metric_thread {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {L : ℕ} (v : ℕ → Fin n) (hEnds : v 0 ≠ v L)
    (hGap : (graph s).dist (v 0) (v L) + 4 ≤ L)
    (hCycleLength : 7 ≤ L + (graph s).dist (v 0) (v L))
    (hAdjacent : ∀ i < L, (blockGraph (graph s) S).Adj (v i) (v (i + 1)))
    (hDegree : ∀ i, 0 < i → i < L → (blockGraph (graph s) S).degree (v i) = 2)
    (hThree : ∀ i, i + 3 ≤ L → (graph s).dist (v i) (v (i + 3)) = 3)
    {x : Fin n} (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (hMetric : ∀ i ≤ L, (graph s).dist (v i) x =
      threadDistance L ((graph s).dist (v 0) x) ((graph s).dist (v L) x) i) : False := by
  let G := graph s
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt (v 0).isLt) α s hne
  change G.dist (v 0) (v L) + 4 ≤ L at hGap
  change 7 ≤ L + G.dist (v 0) (v L) at hCycleLength
  have hDistPos : 0 < G.dist (v 0) (v L) := hG.pos_dist_of_ne hEnds
  have hLen : 5 ≤ L := by omega
  have hLeft : G.dist (v 0) x + 4 ≤ L + G.dist (v L) x := by
    have h : G.dist (v 0) x ≤ G.dist (v 0) (v L) + G.dist (v L) x := hG.dist_triangle
    omega
  have hRight : G.dist (v L) x + 4 ≤ L + G.dist (v 0) x := by
    have h : G.dist (v L) x ≤ G.dist (v L) (v 0) + G.dist (v 0) x := hG.dist_triangle
    rw [dist_comm (u := v L) (v := v 0)] at h
    omega
  have hZeroLeft (h : G.dist (v 0) x = 0) : 7 ≤ L + G.dist (v L) x := by
    have he := hG.dist_eq_zero_iff.mp h
    rw [← he, dist_comm]
    exact hCycleLength
  have hZeroRight (h : G.dist (v L) x = 0) : 7 ≤ L + G.dist (v 0) x := by
    rw [← hG.dist_eq_zero_iff.mp h]
    exact hCycleLength
  exact nash_block_no_balanced_metric_thread s α hne hS v hLen hAdjacent hDegree
    hThree hx hMax hLeft hRight hZeroLeft hZeroRight hMetric

#print axioms exists_internal_thread_ridge
#print axioms nash_block_no_balanced_metric_thread
#print axioms nash_block_no_long_metric_thread

end Lax869952Proofs
