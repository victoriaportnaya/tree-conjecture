import Lax869952Proofs.ThetaMetric

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

/-- A long degree-two thread whose distances to a fixed target are measured
through its endpoints. The endpoint condition covers a target at the start. -/
structure LongBlockThreadTo {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    [DecidableRel (blockGraph G S).Adj] (x A B : Fin n) where
  length : ℕ
  long : 5 ≤ length
  thread : DegreeTwoBlockThread G S A B length
  metric : ∀ i ≤ length, G.dist (thread.vertex i) x =
    threadDistance length (G.dist A x) (G.dist B x) i
  boundary : G.dist A x = 0 → 8 ≤ length + G.dist B x

/-- Along a long thread the distance from the maximum attachment increases by
at least the length minus three, when read from the nearer endpoint. -/
theorem nash_block_long_thread_gap {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B : Fin n} (P : LongBlockThreadTo (graph s) S x A B)
    (hAB : A ≠ B) (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (hNear : (graph s).dist A x ≤ (graph s).dist B x) :
    P.length + (graph s).dist A x ≤ (graph s).dist B x + 3 := by
  have hG := nash_connected (Nat.zero_lt_of_lt A.isLt) α s hne
  have hEnd : 0 < (graph s).dist B x := by
    by_contra! h
    have hb : (graph s).dist B x = 0 := by omega
    have ha : (graph s).dist A x = 0 := by omega
    exact hAB ((hG.dist_eq_zero_iff.mp ha).trans (hG.dist_eq_zero_iff.mp hb).symm)
  by_contra! h
  have hLong := P.long
  have hLeft : (graph s).dist A x + 4 ≤ P.length + (graph s).dist B x := by omega
  have hRight : (graph s).dist B x + 4 ≤ P.length + (graph s).dist A x := by omega
  apply nash_block_no_balanced_metric_thread s α hne hS P.thread.vertex P.long
    P.thread.adjacent P.thread.degree P.thread.three hx hMax
  · simpa only [P.thread.start_eq, P.thread.end_eq] using hLeft
  · simpa only [P.thread.start_eq, P.thread.end_eq] using hRight
  · simpa only [P.thread.start_eq, P.thread.end_eq] using
      (show (graph s).dist A x = 0 → 7 ≤ P.length + (graph s).dist B x from
        fun hz => (show 7 ≤ 8 by decide).trans (P.boundary hz))
  · simpa only [P.thread.start_eq, P.thread.end_eq] using
      (show (graph s).dist B x = 0 → 7 ≤ P.length + (graph s).dist A x by omega)
  · simpa only [P.thread.start_eq, P.thread.end_eq] using P.metric

theorem nash_block_long_thread_penultimate_purchase {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B : Fin n} (P : LongBlockThreadTo (graph s) S x A B)
    (hAB : A ≠ B) (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (hNear : (graph s).dist A x ≤ (graph s).dist B x) :
    P.thread.vertex (P.length - 1) ∈ (s (P.thread.vertex (P.length - 2))).val := by
  have hGap := nash_block_long_thread_gap s α hne hS P hAB hx hMax hNear
  have hLong := P.long
  refine nash_block_thread_penultimate_purchase s α hne hS P.thread (by omega)
    hx hMax hGap (by omega) (fun h => ⟨P.long, ?_⟩) P.metric
  by_contra! hSmall
  have hBoundary := P.boundary (by omega)
  omega

/-- Two long threads from possibly different starts cannot approach the
same endpoint from the side nearer the maximum attachment. -/
theorem nash_block_no_two_incoming_long_threads {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B C : Fin n} (P : LongBlockThreadTo (graph s) S x A B)
    (Q : LongBlockThreadTo (graph s) S x C B)
    (hAB : A ≠ B) (hCB : C ≠ B) (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (hNearP : (graph s).dist A x ≤ (graph s).dist B x)
    (hNearQ : (graph s).dist C x ≤ (graph s).dist B x)
    (hCrossP : (graph s).dist (P.thread.vertex (P.length - 2))
      (Q.thread.vertex (Q.length - 1)) = 3)
    (hCrossQ : (graph s).dist (Q.thread.vertex (Q.length - 2))
      (P.thread.vertex (P.length - 1)) = 3) : False := by
  have hBuyP := nash_block_long_thread_penultimate_purchase s α hne hS P hAB hx hMax hNearP
  have hBuyQ := nash_block_long_thread_penultimate_purchase s α hne hS Q hCB hx hMax hNearQ
  exact nash_block_no_two_penultimate_purchases s α hne hS P.thread Q.thread
    (by have := P.long; omega) (by have := Q.long; omega)
    hBuyP hBuyQ hCrossP hCrossQ

/-- A cycle would have two lower-or-equal neighbours at one of its
maximum-potential vertices. -/
theorem isAcyclic_of_unique_lower_neighbor {V : Type*} (H : SimpleGraph V) (level : V → ℕ)
    (hUnique : ∀ {u v w}, H.Adj u v → H.Adj u w →
      level v ≤ level u → level w ≤ level u → v = w) : H.IsAcyclic := by
  classical
  intro v c hc
  obtain ⟨u, hu, hMax⟩ := Finset.exists_max_image c.support.toFinset level
    ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  have hu' := List.mem_toFinset.mp hu
  let d := c.rotate u hu'
  have hd : d.IsCycle := hc.rotate hu'
  have hDMax (w : V) (hw : w ∈ d.support) : level w ≤ level u :=
    hMax w (List.mem_toFinset.mpr ((c.mem_support_rotate_iff u hu').mp hw))
  exact hd.snd_ne_penultimate (hUnique (d.adj_snd hd.not_nil)
    (d.adj_penultimate hd.not_nil).symm
    (hDMax _ (d.getVert_mem_support _)) (hDMax _ (d.getVert_mem_support _)))

#print axioms nash_block_long_thread_gap
#print axioms nash_block_no_two_incoming_long_threads
#print axioms isAcyclic_of_unique_lower_neighbor

end Lax869952Proofs
