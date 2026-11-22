import Lax869952Proofs.WeightedBlocks

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ}

namespace ShortestParents

/-- A chosen downward edge is dispensable when its far endpoint has
another parent at the same depth. -/
theorem exists_of_alternative_edge {G : SimpleGraph (Fin n)} {r u v a : Fin n}
    (T : ShortestParents G r) (hv : v ≠ r)
    (hAdj : G.Adj v a) (hDepth : G.dist r a + 1 = G.dist r v) (ha : a ≠ u) :
    ∃ P : ShortestParents G r, P.parent v ≠ u := by
  let parent (z : Fin n) := if z = v then a else T.parent z
  let P : ShortestParents G r := {
    parent := parent
    parent_root := by simp [parent, hv.symm, T.parent_root]
    parent_adj := by
      intro z hz
      by_cases eq : z = v
      · subst z
        simpa [parent] using hAdj
      · simpa [parent, eq] using T.parent_adj hz
    parent_depth := by
      intro z hz
      by_cases eq : z = v
      · subst z
        simpa [parent] using hDepth
      · simpa [parent, eq] using T.parent_depth hz }
  exact ⟨P, by simpa [P, parent] using ha⟩

/-- If there is a breadth-first tree in which a sold purchase is not a
child edge, it does not need to belong to the tree used for other sales.
The plans can be combined one endpoint at a time. -/
theorem redirect_preserves_distances_of_alternative_parents
    {s : Profile n} {u r : Fin n} (hG : (graph s).Connected)
    (hur : u ≠ r) (sold : Finset (Fin n))
    (alternative : ∀ v ∈ sold, ∃ T : ShortestParents (graph s) r, T.parent v ≠ u) :
    (graph (redirect s u r hur sold)).Connected ∧
      ∀ z, (graph (redirect s u r hur sold)).dist r z ≤ (graph s).dist r z := by
  classical
  let G := graph s
  let chosen := chooseShortestParents hG r
  let parent (v : Fin n) := if hv : v ∈ sold then (alternative v hv).choose.parent v
    else chosen.parent v
  let T : ShortestParents G r := {
    parent := parent
    parent_root := by
      unfold parent
      split
      · exact (alternative _ ‹r ∈ sold›).choose.parent_root
      · exact chosen.parent_root
    parent_adj := by
      intro v hv
      unfold parent
      split
      · exact (alternative _ ‹v ∈ sold›).choose.parent_adj hv
      · exact chosen.parent_adj hv
    parent_depth := by
      intro v hv
      unfold parent
      split
      · exact (alternative _ ‹v ∈ sold›).choose.parent_depth hv
      · exact chosen.parent_depth hv }
  have avoid {z : Fin n} (hz : z ∈ sold) : T.parent z ≠ u := by
    change parent z ≠ u
    rw [show parent z = (alternative z hz).choose.parent z by simp [parent, hz]]
    exact (alternative z hz).choose_spec
  let D := graph (redirect s u r hur sold)
  have walk (depth : ℕ) (z : Fin n) (hd : G.dist r z = depth) :
      ∃ p : D.Walk r z, p.length ≤ depth := by
    induction depth using Nat.strong_induction_on generalizing z with
    | h depth ih =>
      by_cases root : z = r
      · subst z
        exact ⟨.nil, Nat.zero_le _⟩
      by_cases buyer : z = u
      · subst z
        have hPos : 0 < G.dist r u := hG.pos_dist_of_ne hur.symm
        exact ⟨(redirect_adj_target s hur sold).symm.toWalk, by
          change 1 ≤ depth
          omega⟩
      have lower := T.parent_depth root
      change G.dist r (T.parent z) + 1 = G.dist r z at lower
      obtain ⟨p, hp⟩ := ih (G.dist r (T.parent z)) (by omega) (T.parent z) rfl
      have keep : T.parent z ≠ u ∨ z ∉ sold := by
        by_cases hz : z ∈ sold
        · exact Or.inl (avoid hz)
        · exact Or.inr hz
      have edge : D.Adj (T.parent z) z :=
        redirect_preserves_adj (T.parent_adj root).symm keep (Or.inl buyer)
      exact ⟨p.concat edge, by rw [Walk.length_concat]; omega⟩
  exact ⟨(connected_iff_exists_forall_reachable D).mpr
    ⟨r, fun z => ⟨(walk (G.dist r z) z rfl).choose⟩⟩,
    fun z => (dist_le (walk (G.dist r z) z rfl).choose).trans
      (walk (G.dist r z) z rfl).choose_spec⟩

end ShortestParents

/-- The amount saved, compared with using only the new root link, by an
old shortest path that starts with a retained edge. The buyer itself
always contributes its full root-detour cost. -/
noncomputable def retainedRouteCredit (G : SimpleGraph (Fin n)) (u r : Fin n)
    (sold : Finset (Fin n)) (z : Fin n) : ℕ := by
  classical
  exact if z = u ∨ ∃ a, G.Adj u a ∧ a ∉ sold ∧ G.dist a z + 1 = G.dist u z
    then G.dist r z + 1 - G.dist u z else 0

/-- The exact credit for all retained shortest first steps strengthens
the redirect bound, with no restriction on the compared vertices. -/
theorem nash_redirect_with_retained_routes (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {u r : Fin n} (hur : u ≠ r)
    (sold : Finset (Fin n)) (bought : ∀ v ∈ sold, v ∈ (s u).val)
    (alternative : ∀ v ∈ sold, ∃ T : ShortestParents (graph s) r, T.parent v ≠ u) :
    distanceSum (graph s) u + (α : ℝ) * sold.card +
        (∑ z : Fin n, (retainedRouteCredit (graph s) u r sold z : ℝ)) ≤
      distanceSum (graph s) r + n + (α : ℝ) := by
  classical
  let G := graph s
  let t := redirect s u r hur sold
  let D := graph t
  have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  obtain ⟨hD, rootDist⟩ := ShortestParents.redirect_preserves_distances_of_alternative_parents
    hG hur sold alternative
  have link : D.Adj u r := redirect_adj_target s hur sold
  have oldRoute {z a : Fin n} (edge : G.Adj u a) (keep : a ∉ sold)
      (shortest : G.dist a z + 1 = G.dist u z) : D.dist u z ≤ G.dist u z := by
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist a z
    have avoid : u ∉ p.support := by
      intro hit
      have bound : G.dist a u + G.dist u z ≤ p.length := walk_length_ge_via p hit
      rw [hp] at bound
      change G.dist a z + 1 = G.dist u z at shortest
      change G.dist a u + G.dist u z ≤ G.dist a z at bound
      omega
    obtain ⟨q, hq⟩ := transport_avoiding
      (fun ha hb e => redirect_preserves_adj e (Or.inl ha) (Or.inl hb)) p avoid
    have new : D.Adj u a := redirect_preserves_adj edge (Or.inr keep) (Or.inl edge.ne.symm)
    have len := dist_le (Walk.cons new q)
    rw [Walk.length_cons, hq, hp, shortest] at len
    exact len
  have bound (z : Fin n) : D.dist u z ≤ G.dist r z + 1 := by
    have tri : D.dist u z ≤ D.dist u r + D.dist r z := hD.dist_triangle
    rw [dist_eq_one_iff_adj.mpr link] at tri
    have h : D.dist r z ≤ G.dist r z := rootDist z
    omega
  have point (z : Fin n) :
      D.dist u z + retainedRouteCredit G u r sold z ≤ G.dist r z + 1 := by
    unfold retainedRouteCredit
    split
    · rename_i safe
      have hOld : D.dist u z ≤ G.dist u z := by
        rcases safe with rfl | ⟨a, ha, hk, hs⟩
        · simp
        · exact oldRoute ha hk hs
      have hNew := bound z
      omega
    · simpa using bound z
  have sum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (Fin n))) =>
    (show (D.dist u z : ℝ) + (retainedRouteCredit G u r sold z : ℝ) ≤
        (G.dist r z : ℝ) + 1 by exact_mod_cast point z))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at sum
  change distanceSum D u + (∑ z : Fin n, (retainedRouteCredit G u r sold z : ℝ)) ≤
    distanceSum G r + n at sum
  have cost := nash_finite_cost_le α s t hG hD hne u (fun j hj => redirect_other s hur sold hj)
  have count := redirect_card_le s hur sold bought
  have countR : ((t u).val.ncard : ℝ) + sold.card ≤ ((s u).val.ncard : ℝ) + 1 := by
    exact_mod_cast count
  have price := mul_le_mul_of_nonneg_left countR (NNReal.zero_le_coe : 0 ≤ (α : ℝ))
  unfold finiteCost at cost
  change (α : ℝ) * (s u).val.ncard + distanceSum G u ≤
    (α : ℝ) * (t u).val.ncard + distanceSum D u at cost
  linarith

/-- On summing two redirects, both original distance sums cancel. -/
theorem nash_two_redirect_credit_bound (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {u v : Fin n} (huv : u ≠ v)
    (U V : Finset (Fin n))
    (hU : ∀ z ∈ U, z ∈ (s u).val)
    (hV : ∀ z ∈ V, z ∈ (s v).val)
    (altU : ∀ z ∈ U, ∃ T : ShortestParents (graph s) v, T.parent z ≠ u)
    (altV : ∀ z ∈ V, ∃ T : ShortestParents (graph s) u, T.parent z ≠ v) :
    (α : ℝ) * ((U.card : ℝ) + V.card - 2) +
      (∑ z : Fin n, ((retainedRouteCredit (graph s) u v U z : ℝ) +
        (retainedRouteCredit (graph s) v u V z : ℝ))) ≤ 2 * (n : ℝ) := by
  have first := nash_redirect_with_retained_routes s α hne huv U hU altU
  have second := nash_redirect_with_retained_routes s α hne huv.symm V hV altV
  rw [Finset.sum_add_distrib]
  linarith

/-- Two sales cost at least one edge price, and the buyer's own vertex
contributes its entire detour to the retained-route credit. -/
theorem nash_two_sales_price_le {s : Profile n} {α : ℝ≥0}
    (hne : IsNashEquilibrium α s) {u r : Fin n} (hur : u ≠ r)
    (sold : Finset (Fin n)) (bought : ∀ v ∈ sold, v ∈ (s u).val)
    (alternative : ∀ v ∈ sold, ∃ T : ShortestParents (graph s) r, T.parent v ≠ u)
    (hCard : 2 ≤ sold.card) :
    (α : ℝ) + (graph s).dist r u + 1 ≤
      n + distanceSum (graph s) r - distanceSum (graph s) u := by
  classical
  have h := nash_redirect_with_retained_routes s α hne hur sold bought alternative
  have atSelf : retainedRouteCredit (graph s) u r sold u = (graph s).dist r u + 1 := by
    simp [retainedRouteCredit]
  have credit : ((graph s).dist r u : ℝ) + 1 ≤
      ∑ z : Fin n, (retainedRouteCredit (graph s) u r sold z : ℝ) := by
    have one := Finset.single_le_sum
      (f := fun z : Fin n => (retainedRouteCredit (graph s) u r sold z : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ u)
    simpa only [atSelf, Nat.cast_add, Nat.cast_one] using one
  have cardReal : (2 : ℝ) ≤ sold.card := by exact_mod_cast hCard
  have price := mul_le_mul_of_nonneg_left cardReal (NNReal.zero_le_coe : 0 ≤ (α : ℝ))
  linarith

/-- The buyer's own credit lowers the threshold for the one-purchase
capacity by two, even when the buyer and the target are adjacent. -/
theorem nash_at_most_one_alternative_purchase_above_order_sub_two {s : Profile n} {α : ℝ≥0}
    (hne : IsNashEquilibrium α s) (hα : (n : ℝ) - 2 < α)
    {u r : Fin n} (hur : u ≠ r) (hRoot : distanceSum (graph s) r ≤ distanceSum (graph s) u)
    (sold : Finset (Fin n)) (bought : ∀ v ∈ sold, v ∈ (s u).val)
    (alternative : ∀ v ∈ sold, ∃ T : ShortestParents (graph s) r, T.parent v ≠ u) :
    sold.card ≤ 1 := by
  by_contra! large
  have bound := nash_two_sales_price_le hne hur sold bought alternative (by omega)
  have hG := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  have d : (1 : ℝ) ≤ (graph s).dist r u := by
    exact_mod_cast (hG.pos_dist_of_ne hur.symm)
  linarith

/-- At a root of minimum total distance, at most one purchase can be
removed while retaining some shortest path from the root to each endpoint. -/
theorem nash_at_most_one_purchase_with_alternative_parents {s : Profile n} {α : ℝ≥0}
    (hne : IsNashEquilibrium α s) (hα : (n : ℝ≥0) < α)
    {u r : Fin n} (hur : u ≠ r) (hRoot : distanceSum (graph s) r ≤ distanceSum (graph s) u)
    (sold : Finset (Fin n)) (bought : ∀ v ∈ sold, v ∈ (s u).val)
    (alternative : ∀ v ∈ sold, ∃ T : ShortestParents (graph s) r, T.parent v ≠ u) :
    sold.card ≤ 1 := by
  have h := nash_redirect_with_retained_routes s α hne hur sold bought alternative
  have credit : (0 : ℝ) ≤ ∑ z : Fin n, (retainedRouteCredit (graph s) u r sold z : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  by_contra! hCard
  have cardReal : (2 : ℝ) ≤ sold.card := by exact_mod_cast (show 2 ≤ sold.card by omega)
  have price := mul_le_mul_of_nonneg_left cardReal (NNReal.zero_le_coe : (0 : ℝ) ≤ α)
  have hPrice : (n : ℝ) < α := by exact_mod_cast hα
  linarith

/-- If both players have two dispensable purchases, opposing redirects
form a strict contradiction at price above the number of players. -/
theorem nash_no_mutual_two_alternative_purchases {s : Profile n} {α : ℝ≥0}
    (hne : IsNashEquilibrium α s) (hα : (n : ℝ≥0) < α)
    {u v : Fin n} (huv : u ≠ v) (U V : Finset (Fin n))
    (hU : ∀ z ∈ U, z ∈ (s u).val) (hV : ∀ z ∈ V, z ∈ (s v).val)
    (altU : ∀ z ∈ U, ∃ T : ShortestParents (graph s) v, T.parent z ≠ u)
    (altV : ∀ z ∈ V, ∃ T : ShortestParents (graph s) u, T.parent z ≠ v)
    (count : 4 ≤ U.card + V.card) : False := by
  have h := nash_two_redirect_credit_bound s α hne huv U V hU hV altU altV
  have credit : (0 : ℝ) ≤
      ∑ z : Fin n, ((retainedRouteCredit (graph s) u v U z : ℝ) +
        (retainedRouteCredit (graph s) v u V z : ℝ)) :=
    Finset.sum_nonneg fun _ _ => add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have countR : (4 : ℝ) ≤ (U.card : ℝ) + V.card := by exact_mod_cast count
  have price := mul_le_mul_of_nonneg_left
    (show (2 : ℝ) ≤ (U.card : ℝ) + V.card - 2 by linarith)
    (NNReal.zero_le_coe : (0 : ℝ) ≤ α)
  have high : (n : ℝ) < α := by exact_mod_cast hα
  linarith

#print axioms nash_no_mutual_two_alternative_purchases
#print axioms nash_redirect_with_retained_routes
#print axioms nash_two_redirect_credit_bound

end Lax869952Proofs
