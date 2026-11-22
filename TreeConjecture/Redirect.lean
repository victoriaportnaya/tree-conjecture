import TreeConjecture.Foundations

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped NNReal BigOperators

variable {n : ℕ}

/-- Replace a player's purchases in a finite set with a single link to the target. -/
noncomputable def redirect (s : Profile n) (i r : Fin n) (hir : i ≠ r)
    (sold : Finset (Fin n)) : Profile n :=
  fun j => ⟨if j = i then insert r ((s j).val \ ↑sold) else (s j).val, by
    split_ifs with hj
    · subst j
      simp [hir, (s i).property]
    · exact (s j).property⟩

lemma redirect_other (s : Profile n) {i r : Fin n} (hir : i ≠ r)
    (sold : Finset (Fin n)) {j : Fin n} (hj : j ≠ i) :
    redirect s i r hir sold j = s j := by
  apply Subtype.ext
  simp [redirect, hj]

lemma redirect_adj_target (s : Profile n) {i r : Fin n} (hir : i ≠ r)
    (sold : Finset (Fin n)) : (graph (redirect s i r hir sold)).Adj i r :=
  Or.inl (by simp [redirect])

private lemma mem_redirect {s : Profile n} {i r a b : Fin n} {hir : i ≠ r}
    {sold : Finset (Fin n)} (h : b ∈ (s a).val) (hkeep : a ≠ i ∨ b ∉ sold) :
    b ∈ (redirect s i r hir sold a).val := by
  rcases hkeep with ha | hb
  · simpa [redirect, ha] using h
  · by_cases ha : a = i
    · simp [redirect, ha, h, hb]
    · simpa [redirect, ha] using h

lemma redirect_preserves_adj {s : Profile n} {i r a b : Fin n} {hir : i ≠ r}
    {sold : Finset (Fin n)} (h : (graph s).Adj a b)
    (hab : a ≠ i ∨ b ∉ sold) (hba : b ≠ i ∨ a ∉ sold) :
    (graph (redirect s i r hir sold)).Adj a b :=
  h.imp (fun h => mem_redirect h hab) (fun h => mem_redirect h hba)

lemma redirect_preserves_other_edge {s : Profile n} {i r a b : Fin n} {hir : i ≠ r}
    {sold : Finset (Fin n)} (h : (graph s).Adj a b)
    (hkeep : ∀ x ∈ sold, s(a, b) ≠ s(i, x)) :
    (graph (redirect s i r hir sold)).Adj a b := by
  apply redirect_preserves_adj h
  · by_cases ha : a = i
    · exact Or.inr (fun hb => hkeep b hb (Sym2.eq_iff.mpr (Or.inl ⟨ha, rfl⟩)))
    · exact Or.inl ha
  · by_cases hb : b = i
    · exact Or.inr (fun ha => hkeep a ha (Sym2.eq_iff.mpr (Or.inr ⟨rfl, hb⟩)))
    · exact Or.inl hb

lemma redirect_card_le (s : Profile n) {i r : Fin n} (hir : i ≠ r)
    (sold : Finset (Fin n)) (hsold : ∀ j ∈ sold, j ∈ (s i).val) :
    (redirect s i r hir sold i).val.ncard + sold.card ≤ (s i).val.ncard + 1 := by
  have hsub : (↑sold : Set (Fin n)) ⊆ (s i).val := fun j hj => hsold j hj
  have hdiff := Set.ncard_sdiff_add_ncard_of_subset hsub
  rw [Set.ncard_coe_finset] at hdiff
  have hinsert := Set.ncard_insert_le r ((s i).val \ (↑sold : Set (Fin n)))
  simp only [redirect, ↓reduceIte]
  omega

/-- A connected swap of a single purchased link cannot reduce the buyer's
distance sum at equilibrium. The purchase count can only decrease. -/
theorem nash_swap_distanceSum_le (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {i old target : Fin n} (hneTarget : i ≠ target)
    (hown : old ∈ (s i).val)
    (hconn : (graph (redirect s i target hneTarget {old})).Connected) :
    distanceSum (graph s) i ≤ distanceSum (graph (redirect s i target hneTarget {old})) i := by
  let t := redirect s i target hneTarget {old}
  have hG := nash_connected (Nat.zero_lt_of_lt i.isLt) α s hne
  have hc := nash_finite_cost_le α s t hG hconn hne i
    (fun j hj => redirect_other s hneTarget {old} hj)
  have hcard := redirect_card_le s hneTarget ({old} : Finset (Fin n))
    (fun j hj => (Finset.mem_singleton.mp hj).symm ▸ hown)
  have hcount : (t i).val.ncard ≤ (s i).val.ncard := by
    simpa [t] using hcard
  have hcountReal : ((t i).val.ncard : ℝ) ≤ ((s i).val.ncard : ℝ) := by
    exact_mod_cast hcount
  have hnonneg : 0 ≤ (α : ℝ) := NNReal.zero_le_coe
  have hpurchase := mul_le_mul_of_nonneg_left hcountReal hnonneg
  unfold finiteCost at hc
  linarith

/-- It suffices to repair the target's shortest distances to the endpoints
of the sold edges. All other target distances then stay within their old bounds. -/
theorem redirect_preserves_target_distances (s : Profile n) (hG : (graph s).Connected)
    {i r : Fin n} (hir : i ≠ r) (sold : Finset (Fin n))
    (hrepair : ∀ j, j = i ∨ j ∈ sold →
      ∃ p : (graph (redirect s i r hir sold)).Walk r j, p.length ≤ (graph s).dist r j) :
    (graph (redirect s i r hir sold)).Connected ∧
      ∀ j, (graph (redirect s i r hir sold)).dist r j ≤ (graph s).dist r j := by
  let G := graph s
  let H := graph (redirect s i r hir sold)
  have routesAt : ∀ depth (x : Fin n), G.dist r x = depth →
      ∃ q : H.Walk r x, q.length ≤ depth := by
    intro depth
    induction depth using Nat.strong_induction_on with
    | h depth ih =>
      intro x hdepth
      by_cases endpoint : x = i ∨ x ∈ sold
      · rw [← hdepth]
        exact hrepair x endpoint
      · obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x r
        cases p with
        | nil => exact ⟨.nil, Nat.zero_le _⟩
        | @cons _ y _ hxy p =>
          have hys : G.dist r y ≤ p.length := by
            rw [SimpleGraph.dist_comm]
            exact SimpleGraph.dist_le p
          rw [Walk.length_cons, SimpleGraph.dist_comm] at hp
          change p.length + 1 = G.dist r x at hp
          have hxpos : G.dist r y < depth := by omega
          obtain ⟨q, hq⟩ := ih (G.dist r y) hxpos y rfl
          have hxyH : H.Adj x y := redirect_preserves_adj hxy
            (Or.inl fun h => endpoint (Or.inl h)) (Or.inr fun h => endpoint (Or.inr h))
          refine ⟨q.concat hxyH.symm, ?_⟩
          rw [Walk.length_concat]
          omega
  have routes (x : Fin n) := routesAt (G.dist r x) x rfl
  exact ⟨(connected_iff_exists_forall_reachable H).mpr ⟨r, fun x => ⟨(routes x).choose⟩⟩,
    fun x => (SimpleGraph.dist_le (routes x).choose).trans (routes x).choose_spec⟩

/-- A redirect may improve on routing through the target at individual destinations. -/
theorem nash_redirect_with_distance_credits (s : Profile n) (α : ℝ≥0) (hne : IsNashEquilibrium α s)
    {i r : Fin n} (hir : i ≠ r) (sold : Finset (Fin n))
    (hsold : ∀ j ∈ sold, j ∈ (s i).val)
    (hrepair : ∀ j, j = i ∨ j ∈ sold →
      ∃ p : (graph (redirect s i r hir sold)).Walk r j, p.length ≤ (graph s).dist r j)
    (credit : Fin n → ℝ)
    (hcredit : ∀ j, j ≠ i → 0 < credit j →
      ((graph (redirect s i r hir sold)).dist i j : ℝ) + credit j ≤ (graph s).dist r j + 1) :
    distanceSum (graph s) i + (α : ℝ) * (sold.card : ℝ) + ((graph s).dist r i : ℝ) +
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, credit j) ≤
      distanceSum (graph s) r + ((n - 1 : ℕ) : ℝ) + (α : ℝ) := by
  classical
  let G := graph s
  let t := redirect s i r hir sold
  let H := graph t
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt i.isLt) α s hne
  obtain ⟨hH, hdist⟩ := redirect_preserves_target_distances s hG hir sold hrepair
  have hlink : H.Adj i r := redirect_adj_target s hir sold
  have hterm (j : Fin n) (hj : j ≠ i) :
      (H.dist i j : ℝ) + credit j ≤ (G.dist r j : ℝ) + 1 := by
    by_cases hpos : 0 < credit j
    · exact hcredit j hj hpos
    have htri : H.dist i j ≤ H.dist i r + H.dist r j := hH.dist_triangle
    rw [dist_eq_one_iff_adj.mpr hlink] at htri
    have hnat : H.dist i j ≤ G.dist r j + 1 := by
      have hd : H.dist r j ≤ G.dist r j := hdist j
      omega
    have hreal : (H.dist i j : ℝ) ≤ (G.dist r j : ℝ) + 1 := by exact_mod_cast hnat
    linarith
  let others := (Finset.univ : Finset (Fin n)).erase i
  have hcard : others.card = n - 1 := by simp [others]
  have hsum : distanceSum H i + (G.dist r i : ℝ) + (∑ j ∈ others, credit j) ≤
      distanceSum G r + ((n - 1 : ℕ) : ℝ) := by
    have hSelf : (∑ j ∈ others, (G.dist r j : ℝ)) + (G.dist r i : ℝ) = distanceSum G r :=
      Finset.sum_erase_add _ (fun j => (G.dist r j : ℝ)) (Finset.mem_univ i)
    have hDistSum : distanceSum H i = ∑ j ∈ others, (H.dist i j : ℝ) := by
      unfold distanceSum
      symm
      apply Finset.sum_subset (Finset.subset_univ others)
      intro x _ hx
      have hxi : x = i := by simpa [others] using hx
      simp [hxi]
    have hNew : distanceSum H i + (∑ j ∈ others, credit j) ≤
        ∑ j ∈ others, ((G.dist r j : ℝ) + 1) := by
      rw [hDistSum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j hj => hterm j (Finset.mem_erase.mp hj).1
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hcard] at hNew
    linarith [hSelf]
  have hcost := nash_finite_cost_le α s t hG hH hne i (fun j hj => redirect_other s hir sold hj)
  have hp := redirect_card_le s hir sold hsold
  have hpR : ((t i).val.ncard : ℝ) + (sold.card : ℝ) ≤ ((s i).val.ncard : ℝ) + 1 := by
    exact_mod_cast (show (t i).val.ncard + sold.card ≤ (s i).val.ncard + 1 from hp)
  have hmul := mul_le_mul_of_nonneg_left hpR (NNReal.zero_le_coe : 0 ≤ (α : ℝ))
  unfold finiteCost at hcost
  nlinarith

/-- The distance to the buyer is excluded because a player pays zero for itself. -/
theorem nash_redirect_with_buyer_distance (s : Profile n) (α : ℝ≥0) (hne : IsNashEquilibrium α s)
    {i r : Fin n} (hir : i ≠ r) (sold : Finset (Fin n))
    (hsold : ∀ j ∈ sold, j ∈ (s i).val)
    (hrepair : ∀ j, j = i ∨ j ∈ sold →
      ∃ p : (graph (redirect s i r hir sold)).Walk r j, p.length ≤ (graph s).dist r j) :
    distanceSum (graph s) i + (α : ℝ) * (sold.card : ℝ) + ((graph s).dist r i : ℝ) ≤
      distanceSum (graph s) r + ((n - 1 : ℕ) : ℝ) + (α : ℝ) := by
  simpa using nash_redirect_with_distance_credits s α hne hir sold hsold hrepair
    (fun _ => 0) (fun _ _ h => (lt_irrefl (0 : ℝ) h).elim)

/-- A retained edge saves the target's distance to its other endpoint. -/
theorem nash_redirect_with_retained_neighbor (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {i r z : Fin n} (hir : i ≠ r) (sold : Finset (Fin n))
    (hsold : ∀ j ∈ sold, j ∈ (s i).val)
    (hrepair : ∀ j, j = i ∨ j ∈ sold →
      ∃ p : (graph (redirect s i r hir sold)).Walk r j, p.length ≤ (graph s).dist r j)
    (hkeep : (graph (redirect s i r hir sold)).Adj i z) :
    distanceSum (graph s) i + (α : ℝ) * (sold.card : ℝ) + ((graph s).dist r i : ℝ) +
      ((graph s).dist r z : ℝ) ≤ distanceSum (graph s) r + ((n - 1 : ℕ) : ℝ) + (α : ℝ) := by
  classical
  let credit (j : Fin n) : ℝ := if j = z then (graph s).dist r z else 0
  have hcredit (j : Fin n) (_ : j ≠ i) (h : 0 < credit j) :
      ((graph (redirect s i r hir sold)).dist i j : ℝ) + credit j ≤ (graph s).dist r j + 1 := by
    by_cases he : j = z
    · subst j
      simp [credit, dist_eq_one_iff_adj.mpr hkeep, add_comm]
    · simp [credit, he] at h
  have bound := nash_redirect_with_distance_credits s α hne hir sold hsold hrepair credit hcredit
  simpa [credit, hkeep.ne.symm] using bound

/-- The redirect inequality with the buyer's distance term omitted. -/
theorem nash_redirect_bound (s : Profile n) (α : ℝ≥0) (hne : IsNashEquilibrium α s)
    {i r : Fin n} (hir : i ≠ r) (sold : Finset (Fin n))
    (hsold : ∀ j ∈ sold, j ∈ (s i).val)
    (hrepair : ∀ j, j = i ∨ j ∈ sold →
      ∃ p : (graph (redirect s i r hir sold)).Walk r j, p.length ≤ (graph s).dist r j) :
    distanceSum (graph s) i + (α : ℝ) * (sold.card : ℝ) ≤
      distanceSum (graph s) r + ((n - 1 : ℕ) : ℝ) + (α : ℝ) := by
  linarith [nash_redirect_with_buyer_distance s α hne hir sold hsold hrepair,
    (Nat.cast_nonneg ((graph s).dist r i) : (0 : ℝ) ≤ ((graph s).dist r i : ℝ))]

#print axioms nash_redirect_with_buyer_distance
#print axioms nash_redirect_with_retained_neighbor
#print axioms nash_redirect_bound

end TreeConjecture
