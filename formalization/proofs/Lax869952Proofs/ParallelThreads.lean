import Lax869952Proofs.ShortThreads

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

/-- Two parallel degree-two paths cannot avoid a maximum-weight attachment
if at least one path is long and their combined length is at least eight.
The nearer endpoint is written first. -/
theorem nash_block_no_parallel_paths_of_long {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B : Fin n} (hx : x ∈ S) (hAB : A ≠ B)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {v}, (q : (graph s).Walk v v) → q.IsCycle → 8 ≤ q.length)
    (p q : DegreeTwoBlockPath (graph s) S x A B)
    (hLong : 5 ≤ q.walk.length)
    (hSum : 8 ≤ p.walk.length + q.walk.length)
    (hNear : (graph s).dist A x ≤ (graph s).dist B x)
    (disjoint : ∀ i j, 0 < i → i < p.walk.length → 0 < j → j < q.walk.length →
      p.walk.getVert i ≠ q.walk.getVert j) : False := by
  have hG := nash_connected (Nat.zero_lt_of_lt x.isLt) α s hne
  let Q := LongBlockThreadTo.ofWalk hS hG hx girth q.walk q.isPath hLong q.degree q.avoid
  have gap := nash_block_long_thread_gap s α hne hS Q hAB hx hMax hNear
  change q.walk.length + (graph s).dist A x ≤ (graph s).dist B x + 3 at gap
  have distAB : (graph s).dist A B ≤ p.walk.length := by
    simpa only [Walk.length_mapLe] using
      dist_le (p.walk.mapLe (blockGraph_le (graph s) S))
  have triangle : (graph s).dist B x ≤ (graph s).dist B A + (graph s).dist A x :=
    hG.dist_triangle
  rw [dist_comm (u := B) (v := A)] at triangle
  have hPLength : 3 ≤ p.walk.length := by omega
  have hPGap : 5 ≤ p.walk.length ∨
      p.walk.length + (graph s).dist A x ≤ (graph s).dist B x + 2 := by omega
  have pBuys := nash_block_path_penultimate_purchase_of_length_or_gap s α hne hS hx hMax
    girth p hAB hPLength hNear hPGap
  have qBuys := nash_block_long_thread_penultimate_purchase s α hne hS Q hAB hx hMax hNear
  exact nash_block_no_two_penultimate_path_purchases s α hne hS girth p q hPLength
    (by omega) pBuys qBuys disjoint

#print axioms nash_block_no_parallel_paths_of_long

end Lax869952Proofs
