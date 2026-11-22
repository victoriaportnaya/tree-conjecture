import TreeConjecture.LayerRootLink

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Function Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ}

/-- The depth bound in Observation 15. Two purchases in the second
out-edge layer force the buyer to be at least three edges from the root. -/
theorem nash_two_second_layer_purchases_depth_ge_three (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r u v w : Fin n} (T : ShortestParents (graph s) r) (H : SimpleGraph (Fin n))
    (hRoot : distanceSum (graph s) r ≤ distanceSum (graph s) u)
    (hvw : v ≠ w) (hv : InOutEdgeLayer s T H 2 u v) (hw : InOutEdgeLayer s T H 2 u w) :
    3 ≤ (graph s).dist r u := by
  classical
  let G := graph s
  let d := G.dist r u
  let sold : Finset (Fin n) := {v, w}
  have hSold (x : Fin n) (hx : x ∈ sold) : InOutEdgeLayer s T H 2 u x := by
    rcases (show x = v ∨ x = w by simpa [sold] using hx) with h | h
    · exact h.symm ▸ hv
    · exact h.symm ▸ hw
  have hur : u ≠ r := by
    intro he
    subst u
    exact no_root_purchase_in_layer_plus s α hne hα T (le_refl 2) (Or.inl hv)
  have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  obtain ⟨hConn, hCostUpper⟩ := nash_layer_deletion_cost_upper s α hne hα T H hRoot sold
    (fun _ => 2) (fun _ _ => le_refl 2) hSold
  have hCost := nash_finite_cost_le α s (sellPurchases s u sold) hG hConn hne u
    (fun x hx => sellPurchases_other s u x sold hx)
  have hHalf : 2 * ((T.branch u).card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast T.branch_card_le_half hG hur hRoot
  have hCard : (∑ x ∈ sold, ((T.edgeBranch u x).card : ℝ)) ≤ ((T.branch u).card : ℝ) := by
    exact_mod_cast T.sum_edgeBranch_cards_le u sold
  have hAncestors : (d : ℝ) * ((T.branch u).card : ℝ) ≤
      ∑ k ∈ Finset.range d, ((T.branch (T.parent^[k] u)).card : ℝ) := by
    calc
      _ = ∑ _k ∈ Finset.range d, ((T.branch u).card : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        exact_mod_cast Finset.card_le_card
          (fun x hx => T.mem_branch_iterate hx k (Finset.mem_range.mp hk).le)
  have hSoldCard : sold.card = 2 := by simp [sold, hvw]
  have hWeighted := mul_le_mul_of_nonneg_right hCard
    (show 0 ≤ (4 : ℝ) + 2 * (d : ℝ) by positivity)
  rw [← Finset.sum_mul, hSoldCard] at hCostUpper
  norm_num at hCostUpper
  have hPrice : 2 * (n : ℝ) < α := by exact_mod_cast hα
  by_contra! hDepth
  change d < 3 at hDepth
  have hDepthReal : (d : ℝ) ≤ 2 := by exact_mod_cast (show d ≤ 2 by omega)
  have hDepthBudget := mul_le_mul_of_nonneg_right hDepthReal (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith only [hCost, hCostUpper, hHalf, hWeighted, hAncestors, hPrice, hDepthBudget]

private theorem off_tree_root_link_budget (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r u v : Fin n} (T : ShortestParents (graph s) r) {H : SimpleGraph (Fin n)}
    (hRoot : distanceSum (graph s) r ≤ distanceSum (graph s) u)
    (hadj : H.Adj u v) (hbuy : v ∈ (s u).val) (hoff : ¬ T.tree.Adj u v) :
    (∑ x : Fin n, (T.rootLinkCredit u x : ℝ)) ≤ n := by
  classical
  have hLayer : InOutEdgeLayer s T H 0 u v := ⟨0, le_rfl, .out hadj hbuy hoff⟩
  have hur : u ≠ r := by
    intro he
    subst u
    exact no_root_purchase_in_layer_plus s α hne hα T (Nat.zero_le 2) (Or.inl hLayer)
  have hEmpty : T.edgeBranch u v = ∅ := by
    rw [ShortestParents.edgeBranch, if_neg]
    intro hDown
    exact hoff ⟨hadj.ne, Or.inr hDown.2⟩
  simpa [hEmpty] using nash_layer_single_root_link_budget s α hne hα hur T hRoot (Nat.zero_le 2) hLayer

private theorem no_deep_large_second_layer_branch (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r u v : Fin n} (T : ShortestParents (graph s) r) (H : SimpleGraph (Fin n))
    (hRoot : ∀ {a b}, H.Adj a b → distanceSum (graph s) r ≤ distanceSum (graph s) a)
    (hDepth : 4 ≤ (graph s).dist r u)
    (hBranch : n < 4 * (T.branch u).card)
    (hLarge : n < 8 * (T.edgeBranch u v).card)
    (hLayer : InOutEdgeLayer s T H 2 u v) : False := by
  classical
  let G := graph s
  have hParent : v ≠ r ∧ T.parent v = u := by
    by_contra h
    simp [ShortestParents.edgeBranch, h] at hLarge
  have hV := T.parent_depth hParent.1
  rw [hParent.2] at hV
  have hSizeU : (n : ℝ) < 4 * ((T.branch u).card : ℝ) := by exact_mod_cast hBranch
  have hSizeV : (n : ℝ) < 8 * ((T.branch v).card : ℝ) := by
    simp only [ShortestParents.edgeBranch, if_pos hParent] at hLarge
    exact_mod_cast hLarge
  have bigCredit {x : Fin n} {k : ℕ} (hk : 2 * k + 4 ≤ G.dist r x)
      (hv : T.parent^[k] x = v) (hu : T.parent^[k + 1] x = u) :
      (n : ℝ) < ∑ y : Fin n, (T.rootLinkCredit x y : ℝ) := by
    have h := T.sum_rootLinkCredit_two_ancestors x k hk
    rw [hv, hu] at h
    linarith only [h, hSizeU, hSizeV]
  obtain ⟨j, hj, hChain⟩ := hLayer
  cases hChain with
  | out hadj _ hoff => exact hoff ⟨hadj.ne, Or.inr hParent.2⟩
  | @down j _ _ z _ _ _ _ inner =>
    have hj' : j ≤ 1 := by omega
    cases inner with
    | out hadj hbuy hoff =>
      have hBudget := off_tree_root_link_budget s α hne hα T (hRoot hadj) hadj hbuy hoff
      have hDeep : 4 ≤ G.dist r v := by
        change 4 ≤ (graph s).dist r v
        omega
      have hCredit := bigCredit (x := v) (k := 0) hDeep rfl (by simpa using hParent.2)
      exact (not_lt_of_ge hBudget) hCredit
    | @down j _ _ y _ _ hz hp tail =>
      have hj'' : j = 0 := by omega
      subst j
      cases tail with
      | out hadj hbuy hoff =>
        have hBudget := off_tree_root_link_budget s α hne hα T (hRoot hadj) hadj hbuy hoff
        have hZ := T.parent_depth hz
        rw [hp] at hZ
        have hDeep : 6 ≤ G.dist r z := by
          change 6 ≤ (graph s).dist r z
          omega
        have hCredit := bigCredit (x := z) (k := 1) hDeep (by simpa using hp)
          (by simp [Function.iterate_succ_apply, hp, hParent.2])
        exact (not_lt_of_ge hBudget) hCredit

/-- Observation 15. The buyer of two edges in the second layer has depth
exactly three when the affected branches contain more than a quarter of the players. -/
theorem nash_two_second_layer_purchases_depth_eq_three (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r u v w : Fin n} (T : ShortestParents (graph s) r) (H : SimpleGraph (Fin n))
    (hRoot : ∀ {a b}, H.Adj a b → distanceSum (graph s) r ≤ distanceSum (graph s) a)
    (hvw : v ≠ w) (hv : InOutEdgeLayer s T H 2 u v) (hw : InOutEdgeLayer s T H 2 u w)
    (hUnion : n < 4 * ((T.edgeBranch u v) ∪ (T.edgeBranch u w)).card) :
    (graph s).dist r u = 3 := by
  classical
  have hRootU : distanceSum (graph s) r ≤ distanceSum (graph s) u := by
    obtain ⟨j, _, h⟩ := hv
    cases h with
    | out hadj _ _ => exact hRoot hadj
    | down hadj _ _ _ _ => exact hRoot hadj
  have hLower := nash_two_second_layer_purchases_depth_ge_three s α hne hα T H hRootU hvw hv hw
  by_contra hNe
  have hDeep : 4 ≤ (graph s).dist r u := by omega
  have hSubset : (T.edgeBranch u v) ∪ (T.edgeBranch u w) ⊆ T.branch u :=
    Finset.union_subset (T.edgeBranch_subset_branch u v) (T.edgeBranch_subset_branch u w)
  have hParentCard := Finset.card_le_card hSubset
  have hBranch : n < 4 * (T.branch u).card := by omega
  rw [Finset.card_union_of_disjoint (T.disjoint_edgeBranches u hvw)] at hUnion
  by_cases hBig : n < 8 * (T.edgeBranch u v).card
  · exact no_deep_large_second_layer_branch s α hne hα T H hRoot hDeep hBranch hBig hv
  · have hBigW : n < 8 * (T.edgeBranch u w).card := by omega
    exact no_deep_large_second_layer_branch s α hne hα T H hRoot hDeep hBranch hBigW hw

#print axioms nash_two_second_layer_purchases_depth_ge_three
#print axioms nash_two_second_layer_purchases_depth_eq_three

end TreeConjecture
