import TreeConjecture.ThreadDistances

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped NNReal

/-- A thread in a block with its internal degrees and three-step distances. -/
structure DegreeTwoBlockThread {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    [DecidableRel (blockGraph G S).Adj] (A B : Fin n) (length : ℕ) where
  vertex : ℕ → Fin n
  start_eq : vertex 0 = A
  end_eq : vertex length = B
  adjacent : ∀ i < length, (blockGraph G S).Adj (vertex i) (vertex (i + 1))
  degree : ∀ i, 0 < i → i < length → (blockGraph G S).degree (vertex i) = 2
  three : ∀ i, i + 3 ≤ length → G.dist (vertex i) (vertex (i + 3)) = 3

namespace DegreeTwoBlockThread

variable {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}
variable [DecidableRel (blockGraph G S).Adj] {A B : Fin n} {L : ℕ}

theorem penultimate_adj (P : DegreeTwoBlockThread G S A B L) (hL : 3 ≤ L) :
    (blockGraph G S).Adj (P.vertex (L - 2)) (P.vertex (L - 1)) := by
  simpa only [show L - 2 + 1 = L - 1 by omega] using P.adjacent (L - 2) (by omega)

theorem last_adj (P : DegreeTwoBlockThread G S A B L) (hL : 3 ≤ L) :
    (blockGraph G S).Adj (P.vertex (L - 1)) B := by
  simpa only [show L - 1 + 1 = L by omega, P.end_eq] using P.adjacent (L - 1) (by omega)

theorem dist_penultimate_to_end (P : DegreeTwoBlockThread G S A B L) (hL : 3 ≤ L)
    (hG : G.Connected) : G.dist (P.vertex (L - 2)) B = 2 := by
  have hStart := blockGraph_le G S (P.adjacent (L - 3) (by omega))
  rw [show L - 3 + 1 = L - 2 by omega] at hStart
  have hUpper := dist_le (.cons (blockGraph_le G S (P.penultimate_adj hL))
    (.cons (blockGraph_le G S (P.last_adj hL)) .nil))
  have hThree := P.three (L - 3) (by omega)
  rw [show L - 3 + 3 = L by omega, P.end_eq] at hThree
  have hLower : G.dist (P.vertex (L - 3)) B ≤
      G.dist (P.vertex (L - 3)) (P.vertex (L - 2)) + G.dist (P.vertex (L - 2)) B :=
    hG.dist_triangle
  rw [dist_eq_one_iff_adj.mpr hStart] at hLower
  change G.dist (P.vertex (L - 2)) B ≤ 2 at hUpper
  omega

end DegreeTwoBlockThread

/-- The maximum attachment forces a forward purchase when the next vertex
can reach it geodesically by stepping back twice. -/
theorem nash_block_thread_forces_forward_purchase {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {A B x : Fin n} {L : ℕ} (P : DegreeTwoBlockThread (graph s) S A B L)
    (i : ℕ) (hi : 0 < i) (hj : i + 1 < L) (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (hNear : 2 * (i + 1) + (graph s).dist A x ≤ L + (graph s).dist B x)
    (hPositive : 0 < i - 1 + (graph s).dist A x)
    (hMetric : ∀ j ≤ L, (graph s).dist (P.vertex j) x =
      threadDistance L ((graph s).dist A x) ((graph s).dist B x) j) :
    P.vertex (i + 1) ∈ (s (P.vertex i)).val := by
  have hOnStart (j : ℕ) (hj' : j ≤ i + 1) :
      (graph s).dist (P.vertex j) x = j + (graph s).dist A x := by
    rw [hMetric j (by omega), threadDistance, min_eq_left (by omega)]
  have hDist : (graph s).dist (P.vertex (i + 1)) x =
      2 + (graph s).dist (P.vertex (i - 1)) x := by
    rw [hOnStart (i + 1) (by omega), hOnStart (i - 1) (by omega)]
    omega
  have hDistinct : P.vertex (i + 1) ≠ P.vertex (i - 1) := by
    intro h
    rw [h] at hDist
    omega
  have hTarget : P.vertex (i - 1) ≠ x := by
    intro h
    have hh := hOnStart (i - 1) (by omega)
    rw [h, dist_self] at hh
    omega
  have hStep : (blockGraph (graph s) S).Adj (P.vertex (i - 1)) (P.vertex i) := by
    simpa only [show i - 1 + 1 = i by omega] using P.adjacent (i - 1) (by omega)
  have hRev := (P.adjacent i (by omega)).symm
  exact nash_block_forces_purchase_away_from_maximum s α hne hS hRev hStep.symm
    hDistinct (P.degree _ hi (by omega)) hx hTarget hDist (hMax _ hRev.2.1)

/-- At the borderline distance difference, the purchase two edges earlier
forces the penultimate purchase via the three-edge geodesic constraint. -/
theorem nash_block_thread_penultimate_purchase {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {A B x : Fin n} {L : ℕ} (P : DegreeTwoBlockThread (graph s) S A B L)
    (hL : 3 ≤ L) (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (hGap : L + (graph s).dist A x ≤ (graph s).dist B x + 3)
    (hShort : L = 3 → 0 < (graph s).dist A x)
    (hCritical : (graph s).dist B x + 2 < L + (graph s).dist A x →
      5 ≤ L ∧ (6 ≤ L ∨ 0 < (graph s).dist A x))
    (hMetric : ∀ i ≤ L, (graph s).dist (P.vertex i) x =
      threadDistance L ((graph s).dist A x) ((graph s).dist B x) i) :
    P.vertex (L - 1) ∈ (s (P.vertex (L - 2))).val := by
  by_cases hFar : L + (graph s).dist A x ≤ (graph s).dist B x + 2
  · have h := nash_block_thread_forces_forward_purchase s α hne hS P (L - 2)
      (by omega) (by omega) hx hMax (by omega) (by omega) hMetric
    simpa only [show L - 2 + 1 = L - 1 by omega] using h
  · obtain ⟨hFive, hTarget⟩ := hCritical (by omega)
    have h₁ : (blockGraph (graph s) S).Adj (P.vertex (L - 4)) (P.vertex (L - 3)) := by
      simpa only [show L - 4 + 1 = L - 3 by omega] using P.adjacent (L - 4) (by omega)
    have h₂ : (blockGraph (graph s) S).Adj (P.vertex (L - 3)) (P.vertex (L - 2)) := by
      simpa only [show L - 3 + 1 = L - 2 by omega] using P.adjacent (L - 3) (by omega)
    have h₃ := P.penultimate_adj hL
    have hLength : (graph s).dist (P.vertex (L - 4)) (P.vertex (L - 1)) = 3 := by
      simpa only [show L - 4 + 3 = L - 1 by omega] using P.three (L - 4) (by omega)
    have h₁Buy : P.vertex (L - 3) ∈ (s (P.vertex (L - 4))).val := by
      have h := nash_block_thread_forces_forward_purchase s α hne hS P (L - 4)
        (by omega) (by omega) hx hMax (by omega) (by omega) hMetric
      simpa only [show L - 4 + 1 = L - 3 by omega] using h
    rcases blockGraph_le (graph s) S h₃ with hBuy | hInward
    · exact hBuy
    · exact (nash_block_no_inward_purchases_on_three_step_path s α hne hS
        h₁ h₂ h₃ hLength (P.degree _ (by omega) (by omega))
        (P.degree _ (by omega) (by omega)) h₁Buy hInward).elim

/-- The two penultimate purchases toward a common endpoint give incompatible
weighted bounds when both cross-thread routes are three-step geodesics. -/
theorem nash_block_no_two_penultimate_purchases {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {A B C : Fin n} {L M : ℕ} (P : DegreeTwoBlockThread (graph s) S A B L)
    (Q : DegreeTwoBlockThread (graph s) S C B M)
    (hL : 3 ≤ L) (hM : 3 ≤ M)
    (hBuyP : P.vertex (L - 1) ∈ (s (P.vertex (L - 2))).val)
    (hBuyQ : Q.vertex (M - 1) ∈ (s (Q.vertex (M - 2))).val)
    (hCrossP : (graph s).dist (P.vertex (L - 2)) (Q.vertex (M - 1)) = 3)
    (hCrossQ : (graph s).dist (Q.vertex (M - 2)) (P.vertex (L - 1)) = 3) : False := by
  let G := graph s
  have hG := nash_connected (Nat.zero_lt_of_lt A.isLt) α s hne
  have hPLast := P.last_adj hL
  have hQLast := Q.last_adj hM
  have hP1 : G.dist B (P.vertex (L - 1)) = 1 :=
    dist_eq_one_iff_adj.mpr (blockGraph_le G S hPLast.symm)
  have hQ1 : G.dist B (Q.vertex (M - 1)) = 1 :=
    dist_eq_one_iff_adj.mpr (blockGraph_le G S hQLast.symm)
  have hP2 := P.dist_penultimate_to_end hL hG
  have hQ2 := Q.dist_penultimate_to_end hM hG
  have hPNe : P.vertex (L - 2) ≠ B := by
    intro h
    rw [h, dist_self] at hP2
    omega
  have hQNe : Q.vertex (M - 2) ≠ B := by
    intro h
    rw [h, dist_self] at hQ2
    omega
  have hWP := nash_block_two_step_pair_bound s α hne hS
    (P.penultimate_adj hL) hPLast hPNe (P.degree _ (by omega) (by omega)) hBuyP
    hPLast.2.1 hQLast.1 (blockGraph_le G S hQLast.symm).ne
    (by simpa using hP2) (by rw [hCrossP, hQ1])
  have hWQ := nash_block_two_step_pair_bound s α hne hS
    (Q.penultimate_adj hM) hQLast hQNe (Q.degree _ (by omega) (by omega)) hBuyQ
    hQLast.2.1 hPLast.1 (blockGraph_le G S hPLast.symm).ne
    (by simpa using hQ2) (by rw [hCrossQ, hP1])
  have hPositive : 0 < (blockAttachment (graph s) S B).card := blockAttachment_card_pos B
  omega

/-- An interior maximum-weight target outside two threads of lengths at
least three contradicts equilibrium when either thread has length at least five. -/
theorem nash_block_no_two_off_target_metric_threads {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {A B x : Fin n} {L M : ℕ} (P : DegreeTwoBlockThread (graph s) S A B L)
    (Q : DegreeTwoBlockThread (graph s) S A B M)
    (hL : 3 ≤ L) (hM : 3 ≤ M) (hLong : 5 ≤ L ∨ 5 ≤ M) (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (hPositive : 0 < (graph s).dist A x)
    (hCloser : (graph s).dist A x ≤ (graph s).dist B x)
    (hMetricP : ∀ i ≤ L, (graph s).dist (P.vertex i) x =
      threadDistance L ((graph s).dist A x) ((graph s).dist B x) i)
    (hMetricQ : ∀ i ≤ M, (graph s).dist (Q.vertex i) x =
      threadDistance M ((graph s).dist A x) ((graph s).dist B x) i)
    (hCrossP : (graph s).dist (P.vertex (L - 2)) (Q.vertex (M - 1)) = 3)
    (hCrossQ : (graph s).dist (Q.vertex (M - 2)) (P.vertex (L - 1)) = 3) : False := by
  let G := graph s
  have farOfLong {K : ℕ} (T : DegreeTwoBlockThread G S A B K) (hK : 5 ≤ K)
      (hMetric : ∀ i ≤ K, G.dist (T.vertex i) x =
        threadDistance K (G.dist A x) (G.dist B x) i) :
      K + G.dist A x ≤ G.dist B x + 3 := by
    by_contra! h
    change 0 < G.dist A x at hPositive
    change G.dist A x ≤ G.dist B x at hCloser
    have hLeft : G.dist A x + 4 ≤ K + G.dist B x := by omega
    have hRight : G.dist B x + 4 ≤ K + G.dist A x := by omega
    apply nash_block_no_balanced_metric_thread s α hne hS T.vertex hK
      T.adjacent T.degree T.three hx hMax
    · simpa only [T.start_eq, T.end_eq] using hLeft
    · simpa only [T.start_eq, T.end_eq] using hRight
    · simpa only [T.start_eq, T.end_eq] using (show G.dist A x = 0 → _ by omega)
    · simpa only [T.start_eq, T.end_eq] using (show G.dist B x = 0 → _ by omega)
    · simpa only [T.start_eq, T.end_eq] using hMetric
  have hGapP : L + G.dist A x ≤ G.dist B x + 3 := by
    by_cases hl : 5 ≤ L
    · exact farOfLong P hl hMetricP
    · have h := farOfLong Q (hLong.resolve_left hl) hMetricQ
      omega
  have hGapQ : M + G.dist A x ≤ G.dist B x + 3 := by
    by_cases hm : 5 ≤ M
    · exact farOfLong Q hm hMetricQ
    · have h := farOfLong P (hLong.resolve_right hm) hMetricP
      omega
  have hCritP : G.dist B x + 2 < L + G.dist A x → 5 ≤ L := by
    intro h
    by_contra! hl
    have hh := farOfLong Q (hLong.resolve_left (by omega)) hMetricQ
    omega
  have hCritQ : G.dist B x + 2 < M + G.dist A x → 5 ≤ M := by
    intro h
    by_contra! hm
    have hh := farOfLong P (hLong.resolve_right (by omega)) hMetricP
    omega
  have hBuyP := nash_block_thread_penultimate_purchase s α hne hS P hL hx hMax hGapP
    (fun _ => hPositive) (fun h => ⟨hCritP h, Or.inr hPositive⟩) hMetricP
  have hBuyQ := nash_block_thread_penultimate_purchase s α hne hS Q hM hx hMax hGapQ
    (fun _ => hPositive) (fun h => ⟨hCritQ h, Or.inr hPositive⟩) hMetricQ
  exact nash_block_no_two_penultimate_purchases s α hne hS P Q hL hM hBuyP hBuyQ
    hCrossP hCrossQ

/-- At a maximum-weight endpoint, two threads of length at least five
and at most three greater than the endpoint distance are impossible. -/
theorem nash_block_no_two_endpoint_metric_threads {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {A B : Fin n} {L M : ℕ} (P : DegreeTwoBlockThread (graph s) S A B L)
    (Q : DegreeTwoBlockThread (graph s) S A B M)
    (hL : 5 ≤ L) (hM : 5 ≤ M) (hA : A ∈ S)
    (hDist : 3 ≤ (graph s).dist B A)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S A).card)
    (hGapP : L ≤ (graph s).dist B A + 3)
    (hGapQ : M ≤ (graph s).dist B A + 3)
    (hMetricP : ∀ i ≤ L, (graph s).dist (P.vertex i) A =
      threadDistance L ((graph s).dist A A) ((graph s).dist B A) i)
    (hMetricQ : ∀ i ≤ M, (graph s).dist (Q.vertex i) A =
      threadDistance M ((graph s).dist A A) ((graph s).dist B A) i)
    (hCrossP : (graph s).dist (P.vertex (L - 2)) (Q.vertex (M - 1)) = 3)
    (hCrossQ : (graph s).dist (Q.vertex (M - 2)) (P.vertex (L - 1)) = 3) : False := by
  have hBuyP := nash_block_thread_penultimate_purchase s α hne hS P (by omega) hA hMax
    (by simpa using hGapP) (by omega) (by simp only [dist_self]; omega) hMetricP
  have hBuyQ := nash_block_thread_penultimate_purchase s α hne hS Q (by omega) hA hMax
    (by simpa using hGapQ) (by omega) (by simp only [dist_self]; omega) hMetricQ
  exact nash_block_no_two_penultimate_purchases s α hne hS P Q (by omega) (by omega)
    hBuyP hBuyQ hCrossP hCrossQ

#print axioms nash_block_thread_penultimate_purchase
#print axioms nash_block_no_two_penultimate_purchases
#print axioms nash_block_no_two_off_target_metric_threads
#print axioms nash_block_no_two_endpoint_metric_threads

end TreeConjecture
