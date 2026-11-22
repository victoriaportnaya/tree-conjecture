import TreeConjecture.ShortThreads
import TreeConjecture.ChainWeights
import TreeConjecture.WeightedBlocks
import Mathlib.Order.Interval.Finset.Nat

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped NNReal BigOperators

private theorem tail_mass_le {L : ℕ} (w : ℕ → ℕ) (hL : 5 ≤ L)
    (hStep : ∀ k, 2 ≤ k → k < L - 1 →
      (∑ j ∈ Finset.Ico (k + 1) L, w j) ≤ w k)
    (k : ℕ) (hk : 2 ≤ k) (hLast : k < L) :
    2 ^ (L - 1 - k) * w (L - 1) ≤ ∑ j ∈ Finset.Ico k L, w j := by
  have bound (d : ℕ) (hd : d ≤ L - 3) :
      2 ^ d * w (L - 1) ≤ ∑ j ∈ Finset.Ico (L - 1 - d) L, w j := by
    induction d with
    | zero =>
      have interval : Finset.Ico (L - 1) L = {L - 1} := by
        ext j
        simp only [Finset.mem_Ico, Finset.mem_singleton]
        omega
      simp [interval]
    | succ d ih =>
      let b := L - 1 - (d + 1)
      have hB : 2 ≤ b := by dsimp [b]; omega
      have hBL : b < L - 1 := by dsimp [b]; omega
      have next : b + 1 = L - 1 - d := by dsimp [b]; omega
      have hRec := ih (by omega)
      have hWeight := hStep b hB hBL
      rw [← next] at hRec
      have interval : Finset.Ico b L = insert b (Finset.Ico (b + 1) L) := by
        ext j
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      change 2 ^ (d + 1) * w (L - 1) ≤ ∑ j ∈ Finset.Ico b L, w j
      rw [interval, Finset.sum_insert (by simp), pow_succ, mul_right_comm]
      omega
  have h := bound (L - 1 - k) (by omega)
  rwa [show L - 1 - (L - 1 - k) = k by omega] at h

private theorem nash_block_long_path_masses {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B : Fin n} (hx : x ∈ S) (hAB : A ≠ B)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {u}, (c : (graph s).Walk u u) → c.IsCycle → 8 ≤ c.length)
    (p : DegreeTwoBlockPath (graph s) S x A B)
    (long : 5 ≤ p.walk.length) (near : (graph s).dist A x ≤ (graph s).dist B x) :
    (2 ^ (p.walk.length - 3) *
      (blockAttachment (graph s) S (p.walk.getVert (p.walk.length - 1))).card ≤
      ∑ i ∈ Finset.Ico 2 p.walk.length, (blockAttachment (graph s) S (p.walk.getVert i)).card) ∧
    3 * 2 ^ (p.walk.length - 4) *
      (blockAttachment (graph s) S (p.walk.getVert (p.walk.length - 1))).card ≤ n := by
  classical
  let G := graph s
  let L := p.walk.length
  let v := p.walk.getVert
  let mass (z : Fin n) := (blockAttachment G S z).card
  let w (i : ℕ) := mass (v i)
  have hL : 5 ≤ L := long
  have hG := nash_connected (Nat.zero_lt_of_lt x.isLt) α s hne
  let P := LongBlockThreadTo.ofWalk hS hG hx girth p.walk p.isPath long p.degree p.avoid
  have gap := nash_block_long_thread_gap s α hne hS P hAB hx hMax near
  change L + G.dist A x ≤ G.dist B x + 3 at gap
  have between : L - 3 ≤ G.dist A B := by
    have h : G.dist B x ≤ G.dist B A + G.dist A x := hG.dist_triangle
    rw [dist_comm (u := B) (v := A)] at h
    omega
  have adj (i : ℕ) (hi : i < L) :=
    p.walk.adj_getVert_succ (i := i) hi
  have atEnd : v L = B := p.walk.getVert_length
  have distinct {i j : ℕ} (hi : i ≤ L) (hj : j ≤ L) (hij : i ≠ j) : v i ≠ v j :=
    fun h => hij (p.isPath.getVert_injOn hi hj h)
  have along (i : ℕ) (hi : i ≤ L - 2) : G.dist (v i) x = i + G.dist A x := by
    have h := P.metric i (by change i ≤ L; omega)
    change G.dist (v i) x =
      threadDistance L (G.dist A x) (G.dist B x) i at h
    rw [threadDistance, min_eq_left (by omega)] at h
    exact h
  have forward (i : ℕ) (hi : 1 ≤ i) (hBefore : i ≤ L - 2) :
      v (i + 1) ∈ (s (v i)).val := by
    by_cases atPenultimate : i = L - 2
    · subst i
      have buy := nash_block_long_thread_penultimate_purchase s α hne hS P hAB hx hMax near
      change v (L - 1) ∈ (s (v (L - 2))).val at buy
      simpa only [show L - 2 + 1 = L - 1 by omega] using buy
    · have left := adj (i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at left
      apply nash_block_forces_purchase_away_from_maximum_girth s α hne hS girth
        (adj i (by omega)).symm left.symm
        (distinct (by omega) (by omega) (by omega)) (p.degree i (by omega) (by omega)) hx
      · rw [along (i + 1) (by omega), along (i - 1) (by omega)]
        omega
      · exact hMax _ left.2.1
  have geodesic {i j : ℕ} (hi : i ≤ j) (hj : j ≤ L - 2) :
      G.dist (v i) (v j) = j - i := by
    have triangle : G.dist (v j) x ≤ G.dist (v j) (v i) + G.dist (v i) x :=
      hG.dist_triangle
    rw [dist_comm (u := v j) (v := v i), along j hj, along i (by omega)] at triangle
    let segment := (p.walk.drop i).take (j - i)
    have finish : (p.walk.drop i).getVert (j - i) = v j := by
      rw [Walk.drop_getVert, show i + (j - i) = j by omega]
    have upper := dist_le ((segment.copy rfl finish).mapLe (blockGraph_le G S))
    rw [Walk.length_mapLe, Walk.length_copy] at upper
    have length : segment.length = j - i := by
      simp only [segment, Walk.take_length, Walk.drop_length]
      exact min_eq_left (by change j - i ≤ L - i; omega)
    rw [length] at upper
    change G.dist (v i) (v j) ≤ j - i at upper
    omega
  have vMember (i : ℕ) (hi : i < L) : v i ∈ S := (adj i hi).1
  have bMember : B ∈ S := by
    have h := (adj (L - 1) (by omega)).2.1
    rw [show L - 1 + 1 = L by omega] at h
    change v L ∈ S at h
    rwa [atEnd] at h
  have toEnd (i : ℕ) (hi : 1 ≤ i) (hBelow : i ≤ L - 2) :
      L - 2 - i ≤ G.dist (v i) B := by
    have avoidEnd (j : ℕ) (hj : 0 < j) (hjL : j < L) : v j ≠ B := by
      rw [← atEnd]
      exact distinct hjL.le le_rfl hjL.ne
    have h := block_path_dist_to_external_target hS hG bMember p.walk p.isPath p.degree
      avoidEnd (j := i) (by change i ≤ L; omega)
    change G.dist (v i) B = threadDistance L (G.dist A B) (G.dist B B) i at h
    rw [threadDistance, dist_self, add_zero] at h
    omega
  have geoLast (i : ℕ) (hi : 1 ≤ i) (hBelow : i ≤ L - 2) :
      G.dist (v i) (v (L - 1)) = L - 1 - i := by
    have left := adj (L - 2) (by omega)
    rw [show L - 2 + 1 = L - 1 by omega] at left
    have right := adj (L - 1) (by omega)
    rw [show L - 1 + 1 = L by omega] at right
    change (blockGraph G S).Adj (v (L - 1)) (v L) at right
    rw [atEnd] at right
    have low : G.dist (v (L - 2)) (v i) = L - 2 - i := by
      rw [dist_comm]
      exact geodesic hBelow le_rfl
    have high : L - 2 - i ≤ G.dist B (v i) := by
      rw [dist_comm]
      exact toEnd i hi hBelow
    have distinctLast : v (L - 1) ≠ v i := distinct (by omega) (by omega) (by omega)
    have distinctNbr : v (L - 2) ≠ B := by
      rw [← atEnd]
      exact distinct (by omega) le_rfl (by omega)
    obtain ⟨q, qPath, qLen⟩ := hG.exists_path_of_dist (v (L - 1)) (v i)
    have hSupport := hS.path_support_subset right.1 (vMember i (by omega)) q qPath
    obtain ⟨y, edge, tail, rfl⟩ := Walk.exists_eq_cons_of_ne distinctLast q
    have hy : y ∈ S := hSupport _ (by simp [Walk.support_cons])
    have hNeighbor := neighbors_of_degree_two left.symm right distinctNbr
      (p.degree (L - 1) (by omega) (by omega)) ⟨right.1, hy, edge⟩
    have lenLow := dist_le tail
    rw [Walk.length_cons] at qLen
    have upper : G.dist (v (L - 1)) (v i) ≤ L - 1 - i := by
      have tri : G.dist (v (L - 1)) (v i) ≤
          G.dist (v (L - 1)) (v (L - 2)) + G.dist (v (L - 2)) (v i) :=
        hG.dist_triangle
      rw [dist_eq_one_iff_adj.mpr (blockGraph_le G S left.symm), low] at tri
      omega
    rw [dist_comm]
    change tail.length + 1 = G.dist (v (L - 1)) (v i) at qLen
    rcases hNeighbor with rfl | rfl
    · change G.dist (v (L - 2)) (v i) ≤ tail.length at lenLow
      rw [low] at lenLow
      omega
    · change G.dist _ (v i) ≤ tail.length at lenLow
      omega
  have suffix {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j < L) :
      G.dist (v i) (v j) = j - i := by
    by_cases atLast : j = L - 1
    · subst j
      by_cases same : i = L - 1
      · simp [same]
      · exact geoLast i hi (by omega)
    · exact geodesic hij (by omega)
  have sum_image_eq (k : ℕ) :
      (∑ z ∈ (Finset.Ico k L).image v, mass z) = ∑ j ∈ Finset.Ico k L, w j := by
    apply Finset.sum_image
    intro i hi j hj equality
    have hI := (Finset.mem_Ico.mp hi).2
    have hJ := (Finset.mem_Ico.mp hj).2
    exact p.isPath.getVert_injOn (by change i ≤ L; omega) (by change j ≤ L; omega) equality
  have step (k : ℕ) (hk : 2 ≤ k) (hLast : k < L - 1) :
      (∑ j ∈ Finset.Ico (k + 1) L, w j) ≤ w k := by
    let T := (Finset.Ico (k + 1) L).image v
    rw [← sum_image_eq]
    have left := adj (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at left
    apply nash_block_two_step_sum_bound s α hne hS left (adj k (by omega))
      (distinct (by omega) (by omega) (by omega)) (p.degree k (by omega) (by omega))
    · simpa only [show k - 1 + 1 = k by omega] using forward (k - 1) (by omega) (by omega)
    · intro z hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      exact vMember j (Finset.mem_Ico.mp hj).2
    · intro z hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨first, last⟩ := Finset.mem_Ico.mp hj
      rw [suffix (by omega) (by omega) last, suffix (by omega) first last]
      omega
  constructor
  · have massBound := tail_mass_le w hL step 2 le_rfl (by omega)
    simpa only [show L - 1 - 2 = L - 3 by omega] using massBound
  · have tail := tail_mass_le w hL step 3 (by decide) (by omega)
    have tailBound := step 2 (by decide) (by omega)
    change (∑ j ∈ Finset.Ico 3 L, w j) ≤ w 2 at tailBound
    have hMax' : w 2 ≤ mass x := hMax _ (vMember 2 (by omega))
    have budget : mass x + (∑ j ∈ Finset.Ico 2 L, w j) ≤ n := by
      let T := (Finset.Ico 2 L).image v
      have xNotMem : x ∉ T := by
        intro h
        obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
        exact p.avoid j (by have := (Finset.mem_Ico.mp hj).1; omega) (Finset.mem_Ico.mp hj).2 he
      rw [← sum_image_eq, ← Finset.sum_insert xNotMem]
      calc
        _ ≤ ∑ z ∈ S, mass z := by
          apply Finset.sum_le_sum_of_subset
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hx
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
            exact vMember j (Finset.mem_Ico.mp hj).2
        _ = n := hS.sum_blockAttachment_card hG
    have interval : Finset.Ico 2 L = insert 2 (Finset.Ico 3 L) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [interval, Finset.sum_insert (by simp)] at budget
    change 3 * 2 ^ (L - 4) * w (L - 1) ≤ n
    rw [show L - 1 - 3 = L - 4 by omega] at tail
    rw [mul_assoc]
    omega


/-- The interior suffix consumes exponentially more weight than its last vertex. -/
theorem nash_block_long_path_suffix_mass {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B : Fin n} (hx : x ∈ S) (hAB : A ≠ B)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {u}, (c : (graph s).Walk u u) → c.IsCycle → 8 ≤ c.length)
    (p : DegreeTwoBlockPath (graph s) S x A B)
    (long : 5 ≤ p.walk.length) (near : (graph s).dist A x ≤ (graph s).dist B x) :
    2 ^ (p.walk.length - 3) *
      (blockAttachment (graph s) S (p.walk.getVert (p.walk.length - 1))).card ≤
      ∑ i ∈ Finset.Ico 2 p.walk.length, (blockAttachment (graph s) S (p.walk.getVert i)).card :=
  (nash_block_long_path_masses s α hne hS hx hAB hMax girth p long near).1

/-- Long paths pointing away from a maximum attachment consume an exponential
amount of total weight relative to their last interior vertex. -/
theorem nash_block_long_path_tail_mass {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B : Fin n} (hx : x ∈ S) (hAB : A ≠ B)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {u}, (c : (graph s).Walk u u) → c.IsCycle → 8 ≤ c.length)
    (p : DegreeTwoBlockPath (graph s) S x A B)
    (long : 5 ≤ p.walk.length) (near : (graph s).dist A x ≤ (graph s).dist B x) :
    3 * 2 ^ (p.walk.length - 4) *
      (blockAttachment (graph s) S (p.walk.getVert (p.walk.length - 1))).card ≤ n :=
  (nash_block_long_path_masses s α hne hS hx hAB hMax girth p long near).2

/-- The last internal vertex of a long thread supplies a local upper
bound on the edge price in terms of any cycle containing it. -/
theorem nash_block_long_path_cycle_price_bound {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B : Fin n} (hx : x ∈ S) (hAB : A ≠ B)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {u}, (c : (graph s).Walk u u) → c.IsCycle → 8 ≤ c.length)
    (p : DegreeTwoBlockPath (graph s) S x A B)
    (long : 5 ≤ p.walk.length) (near : (graph s).dist A x ≤ (graph s).dist B x)
    (c : (blockGraph (graph s) S).Walk (p.walk.getVert (p.walk.length - 1))
      (p.walk.getVert (p.walk.length - 1))) (hc : c.IsCycle) :
    (α : ℝ) ≤ 2 * ((c.length : ℝ) - 3) *
      ((blockAttachment (graph s) S (p.walk.getVert (p.walk.length - 1))).card : ℝ) := by
  let G := graph s
  let H := blockGraph G S
  let L := p.walk.length
  let v := p.walk.getVert
  let w := (blockAttachment G S (v (L - 1))).card
  have hL : 5 ≤ L := long
  have hG := nash_connected (Nat.zero_lt_of_lt x.isLt) α s hne
  let P := LongBlockThreadTo.ofWalk hS hG hx girth p.walk p.isPath long p.degree p.avoid
  have buyPenultimate := nash_block_long_thread_penultimate_purchase s α hne hS P hAB hx hMax near
  have shortBuy := nash_block_long_thread_gap s α hne hS P hAB hx hMax near
  change L + G.dist A x ≤ G.dist B x + 3 at shortBuy
  have hFirstBuy : v 2 ∈ (s (v 1)).val := by
    have left := p.walk.adj_getVert_succ (i := 0) (by omega)
    have right := p.walk.adj_getVert_succ (i := 1) (by omega)
    refine nash_block_forces_purchase_away_from_maximum_girth s α hne hS girth
      right.symm left.symm ?_ (p.degree 1 (by decide) (by omega)) hx ?_ ?_
    · intro same
      have different := p.isPath.getVert_injOn
        (show 2 ≤ L by omega) (show 0 ≤ L by omega) same
      omega
    · change G.dist (v 2) x = 2 + G.dist (v 0) x
      have h := P.metric 2 (show 2 ≤ L by omega)
      change G.dist (v 2) x = threadDistance L (G.dist A x) (G.dist B x) 2 at h
      rw [threadDistance, min_eq_left (by omega)] at h
      simpa only [v, Walk.getVert_zero] using h
    · exact hMax _ left.2.1
  have buyLast := nash_block_chain_purchase_propagates s α hne hS girth p.walk p.isPath
    p.degree (i := 1) (j := L - 1) (by omega) (by omega) hFirstBuy
  rw [show L - 1 + 1 = L by omega, Walk.getVert_length] at buyLast
  have left := P.thread.penultimate_adj (by have := P.long; omega)
  have right := P.thread.last_adj (by have := P.long; omega)
  have cycleLength : 8 ≤ c.length := by
    simpa only [Walk.length_mapLe] using girth (c.mapLe (blockGraph_le G S)) (hc.mapLe _)
  have pos : 0 < α := lt_of_le_of_lt (by positivity) hα
  have price := (nash_degree_two_cycle_bound_of_length s α hne pos H
    (blockGraph_le G S) left.symm right (p.degree (L - 1) (by omega) (by omega))
    buyPenultimate buyLast
    (fun q hq he => hS.cycle_edges_subset q hq left he) c hc (le_trans (by decide : 4 ≤ 8) cycleLength)).2
  rw [hS.separatedVertices_eq_blockAttachment hG left.1 left.2.1
    (blockGraph_le G S left).ne] at price
  exact price

/-- At price above the number of players, a cycle containing the end of a
long degree-two path must have length exponential in the path length. -/
theorem nash_block_long_path_cycle_bound {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B : Fin n} (hx : x ∈ S) (hAB : A ≠ B)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {u}, (c : (graph s).Walk u u) → c.IsCycle → 8 ≤ c.length)
    (p : DegreeTwoBlockPath (graph s) S x A B)
    (long : 5 ≤ p.walk.length) (near : (graph s).dist A x ≤ (graph s).dist B x)
    (c : (blockGraph (graph s) S).Walk (p.walk.getVert (p.walk.length - 1))
      (p.walk.getVert (p.walk.length - 1))) (hc : c.IsCycle) :
    3 * 2 ^ (p.walk.length - 4) < 2 * (c.length - 3) := by
  let w := (blockAttachment (graph s) S (p.walk.getVert (p.walk.length - 1))).card
  let L := p.walk.length
  have price := nash_block_long_path_cycle_price_bound s α hα hne hS hx hAB hMax girth
    p long near c hc
  change (α : ℝ) ≤ 2 * ((c.length : ℝ) - 3) * (w : ℝ) at price
  have cycleLength : 8 ≤ c.length := by
    simpa only [Walk.length_mapLe] using
      girth (c.mapLe (blockGraph_le (graph s) S)) (hc.mapLe _)
  have hMass := nash_block_long_path_tail_mass s α hne hS hx hAB hMax girth p long near
  change 3 * 2 ^ (L - 4) * w ≤ n at hMass
  change 3 * 2 ^ (L - 4) < 2 * (c.length - 3)
  by_contra! no
  have upper := (Nat.mul_le_mul_right w no).trans hMass
  have hUpper : (2 : ℝ) * ((c.length : ℝ) - 3) * (w : ℝ) ≤ (n : ℝ) := by
    have upperReal : ((2 * (c.length - 3) * w : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast upper
    simpa only [Nat.cast_mul, Nat.cast_sub (le_trans (by decide : 3 ≤ 8) cycleLength),
      Nat.cast_ofNat] using upperReal
  have hα' : (n : ℝ) < α := by exact_mod_cast hα
  linarith only [price, hUpper, hα']

#print axioms nash_block_long_path_suffix_mass
#print axioms nash_block_long_path_cycle_price_bound
#print axioms nash_block_long_path_tail_mass
#print axioms nash_block_long_path_cycle_bound

end TreeConjecture
