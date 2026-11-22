import TreeConjecture.LayerRestrictions
import TreeConjecture.RootLinkBudget

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Function Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ}

private theorem sell_graph_le_redirect (s : Profile n) {u r : Fin n} (hur : u ≠ r)
    (sold : Finset (Fin n)) :
    graph (sellPurchases s u sold) ≤ graph (redirect s u r hur sold) := by
  have keep {a b : Fin n} (h : b ∈ (sellPurchases s u sold a).val) :
      b ∈ (redirect s u r hur sold a).val := by
    by_cases ha : a = u
    · simp only [sellPurchases, ha, if_pos, Set.mem_sdiff, Finset.mem_coe] at h
      simp only [redirect, ha, if_pos, Set.mem_insert_iff, Set.mem_sdiff, Finset.mem_coe]
      exact Or.inr h
    · simpa only [sellPurchases, redirect, if_neg ha] using h
  intro a b h
  exact h.elim (fun hab => Or.inl (keep hab)) (fun hba => Or.inr (keep hba))

/-- Corollary 11. A root link allows the new routes to retain the savings
from the branches up to the midpoint of the old route to the root. -/
theorem nash_layer_root_link_cost_upper (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r u : Fin n} (hur : u ≠ r) (T : ShortestParents (graph s) r) (H : SimpleGraph (Fin n))
    (hRoot : distanceSum (graph s) r ≤ distanceSum (graph s) u)
    (sold : Finset (Fin n)) (i : Fin n → ℕ) (hi : ∀ v ∈ sold, i v ≤ 2)
    (hLayer : ∀ v ∈ sold, InOutEdgeLayer s T H (i v) u v) :
    let d := (graph s).dist r u
    (graph (redirect s u r hur sold)).Connected ∧
      finiteCost α (redirect s u r hur sold) u - finiteCost α s u ≤
        (n : ℝ) - ((sold.card : ℝ) - 1) * α -
          2 * (∑ k ∈ Finset.range ((d + 1) / 2), ((T.branch (T.parent^[k] u)).card : ℝ)) -
          (if d % 2 = 0 then ((T.branch (T.parent^[d / 2] u)).card : ℝ) else 0) +
          ∑ v ∈ sold, ((T.edgeBranch u v).card : ℝ) * (2 * (i v : ℝ) + (d : ℝ) + 1) := by
  classical
  intro d
  let G := graph s
  let R := graph (redirect s u r hur sold)
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have hWalk (x : Fin n) : ∃ p : R.Walk u x,
      p.length + (if x ∈ T.branch u then d + 1 else 0) ≤
        G.dist r x + 1 + layerPenalty T u sold i (d + 1) x :=
    redirect_layer_walk hur T α hne hα sold i hi (fun v hv => Or.inl (hLayer v hv))
  have hR : R.Connected :=
    (connected_iff_exists_forall_reachable R).mpr ⟨u, fun x => ⟨(hWalk x).choose⟩⟩
  have hPoint (x : Fin n) : (R.dist u x : ℝ) + (T.rootLinkCredit u x : ℝ) ≤
      (G.dist r x : ℝ) + 1 + (layerPenalty T u sold i (d + 1) x : ℝ) := by
    obtain ⟨p, hp⟩ := hWalk x
    have hpDist := (Nat.add_le_add_right (SimpleGraph.dist_le p) _).trans hp
    have hNat : R.dist u x + T.rootLinkCredit u x ≤ G.dist r x + 1 + layerPenalty T u sold i (d + 1) x := by
      by_cases hClean : ∀ v ∈ sold, x ∉ T.edgeBranch u v
      · have hPenalty : layerPenalty T u sold i (d + 1) x = 0 := by
          apply Finset.sum_eq_zero
          intro v hv
          exact if_neg (hClean v hv)
        obtain ⟨q, hq⟩ := layer_deletion_clean_walk sold i hLayer hG hClean
        have hTree : R.dist u x ≤ T.tree.dist u x := by
          simpa only [Walk.length_mapLe, hq] using
            SimpleGraph.dist_le (q.mapLe (sell_graph_le_redirect s hur sold))
        have hLink : R.dist u x ≤ G.dist r x + 1 := by rw [hPenalty] at hpDist; omega
        rw [hPenalty, Nat.add_zero]
        exact (Nat.add_le_add_right (le_min hTree hLink) _).trans (T.min_tree_root_link_le hG u x)
      · push Not at hClean
        obtain ⟨v, _, hv⟩ := hClean
        rw [if_pos (T.edgeBranch_subset_branch u v hv)] at hpDist
        exact (Nat.add_le_add_left (T.rootLinkCredit_le u x) _).trans hpDist
    exact_mod_cast hNat
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin n))) => hPoint x)
  rw [Finset.sum_add_distrib, T.sum_rootLinkCredit, Finset.sum_add_distrib, Finset.sum_add_distrib,
    cast_layerPenalty_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Nat.cast_add, Nat.cast_one, add_assoc] at hsum
  have hDist : distanceSum R u +
      (2 * (∑ k ∈ Finset.range ((d + 1) / 2), ((T.branch (T.parent^[k] u)).card : ℝ)) +
        (if d % 2 = 0 then ((T.branch (T.parent^[d / 2] u)).card : ℝ) else 0)) ≤
      distanceSum G r + ((n : ℝ) +
        ∑ v ∈ sold, ((T.edgeBranch u v).card : ℝ) * (2 * (i v : ℝ) + (d : ℝ) + 1)) := by
    simpa only [distanceSum, add_assoc] using hsum
  have hOwn (v : Fin n) (hv : v ∈ sold) : v ∈ (s u).val := by
    obtain ⟨j, _, hj⟩ := hLayer v hv
    cases hj with
    | out _ h _ => exact h
    | down _ h _ _ _ => exact h
  have hCount : ((redirect s u r hur sold u).val.ncard : ℝ) + (sold.card : ℝ) ≤
      ((s u).val.ncard : ℝ) + 1 := by
    exact_mod_cast redirect_card_le s hur sold hOwn
  have hPurchase := mul_le_mul_of_nonneg_left hCount (NNReal.zero_le_coe : (0 : ℝ) ≤ α)
  change distanceSum G r ≤ distanceSum G u at hRoot
  refine ⟨hR, ?_⟩
  unfold finiteCost
  change (α : ℝ) * ((redirect s u r hur sold u).val.ncard : ℝ) + distanceSum R u -
    ((α : ℝ) * ((s u).val.ncard : ℝ) + distanceSum G u) ≤ _
  linarith

/-- The equilibrium form of Corollary 11 for a single exchanged link. -/
theorem nash_layer_single_root_link_budget (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r u v : Fin n} (hur : u ≠ r) (T : ShortestParents (graph s) r) {H : SimpleGraph (Fin n)}
    (hRoot : distanceSum (graph s) r ≤ distanceSum (graph s) u)
    {i : ℕ} (hi : i ≤ 2) (hLayer : InOutEdgeLayer s T H i u v) :
    (∑ x : Fin n, (T.rootLinkCredit u x : ℝ)) ≤ (n : ℝ) +
      ((T.edgeBranch u v).card : ℝ) * (2 * (i : ℝ) + ((graph s).dist r u : ℝ) + 1) := by
  classical
  obtain ⟨hConn, hCostUpper⟩ :=
    nash_layer_root_link_cost_upper s α hne hα hur T H hRoot {v}
      (fun _ => i) (fun _ _ => hi) (by
        intro w hw
        obtain rfl := Finset.mem_singleton.mp hw
        exact hLayer)
  have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have hCost := nash_finite_cost_le α s (redirect s u r hur {v}) hG hConn hne u
    (fun w hw => redirect_other s hur {v} hw)
  simp at hCostUpper
  rw [T.sum_rootLinkCredit]
  linarith only [hCost, hCostUpper]

#print axioms nash_layer_root_link_cost_upper

end TreeConjecture
