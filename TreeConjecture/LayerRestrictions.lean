import TreeConjecture.LayerRedirects

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Function Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ}

namespace ShortestParents

variable {G : SimpleGraph (Fin n)} {r : Fin n} (T : ShortestParents G r)

theorem edgeBranch_subset_branch (u v : Fin n) : T.edgeBranch u v ⊆ T.branch u := by
  intro x hx
  unfold edgeBranch at hx
  split at hx
  · rename_i h
    exact h.2 ▸ T.mem_branch_of_mem_child_branch h.1 hx
  · simp at hx

theorem disjoint_edgeBranches (u : Fin n) {v w : Fin n} (hvw : v ≠ w) :
    Disjoint (T.edgeBranch u v) (T.edgeBranch u w) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hv hw
  unfold edgeBranch at hv hw
  split at hv
  · rename_i hvParent
    split at hw
    · rename_i hwParent
      have hdV := T.parent_depth hvParent.1
      have hdW := T.parent_depth hwParent.1
      rw [hvParent.2] at hdV
      rw [hwParent.2] at hdW
      obtain ⟨i, hi, hvi⟩ : ∃ i ≤ G.dist r x, T.parent^[i] x = v := by
        simpa [branch] using hv
      obtain ⟨j, hj, hwj⟩ : ∃ j ≤ G.dist r x, T.parent^[j] x = w := by
        simpa [branch] using hw
      have hDi := T.depth_iterate i x
      have hDj := T.depth_iterate j x
      rw [hvi] at hDi
      rw [hwj] at hDj
      have hij : i = j := by omega
      rw [hij] at hvi
      exact hvw (hvi.symm.trans hwj)
    · simp at hw
  · simp at hv

theorem sum_edgeBranch_cards_le (u : Fin n) (sold : Finset (Fin n)) :
    (∑ v ∈ sold, (T.edgeBranch u v).card) ≤ (T.branch u).card := by
  classical
  have hdis : (sold : Set (Fin n)).PairwiseDisjoint (T.edgeBranch u) := by
    intro v _ w _ hvw
    exact T.disjoint_edgeBranches u hvw
  rw [← Finset.card_biUnion hdis]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hx
  exact T.edgeBranch_subset_branch u v hv

end ShortestParents

/-- The root cannot buy an edge in any of the first three augmented layers. -/
theorem no_root_purchase_in_layer_plus (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r v : Fin n} (T : ShortestParents (graph s) r) {H : SimpleGraph (Fin n)}
    {k : ℕ} (hk : k ≤ 2) : ¬ InOutEdgeLayerPlus s T H k r v := by
  intro h
  rcases h with h | h
  · obtain ⟨j, hj, hchain⟩ := h
    obtain ⟨x, y, _, hdepth, _, hBuy, hOff⟩ := hchain.off_tree_witness
    have hDeep := nash_out_edge_depth_ge_three s α hne hα T (Or.inl hBuy) hOff
    rw [SimpleGraph.dist_self, Nat.zero_add] at hdepth
    omega
  · have he : r = v := T.parent_root.symm.trans h.2.1
    subst v
    exact (s r).property h.2.2

/-- Equilibrium bounds the price of a set of augmented-layer purchases
by the total size of its affected branches. -/
theorem nash_layer_purchase_bound (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r u : Fin n} (T : ShortestParents (graph s) r) (H : SimpleGraph (Fin n))
    (hRoot : distanceSum (graph s) r ≤ distanceSum (graph s) u)
    (sold : Finset (Fin n)) (hSold : sold.Nonempty)
    {k : ℕ} (hk : k ≤ 2) (hLayer : ∀ v ∈ sold, InOutEdgeLayerPlus s T H k u v) :
    ((sold.card : ℝ) - 1) * α ≤ (n : ℝ) +
      2 * (k : ℝ) * ∑ v ∈ sold, ((T.edgeBranch u v).card : ℝ) := by
  have hur : u ≠ r := by
    intro he
    subst u
    obtain ⟨v, hv⟩ := hSold
    exact no_root_purchase_in_layer_plus s α hne hα T hk (hLayer v hv)
  have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  obtain ⟨hConn, hCostUpper⟩ := nash_layer_redirect_cost_upper s α hne hα hur T H hRoot sold
    (fun _ => k) (fun _ _ => hk) hLayer
  have hCost := nash_finite_cost_le α s (redirect s u r hur sold) hG hConn hne u
    (fun v hv => redirect_other s hur sold hv)
  have hCard : (∑ v ∈ sold, ((T.edgeBranch u v).card : ℝ)) ≤ ((T.branch u).card : ℝ) := by
    exact_mod_cast T.sum_edgeBranch_cards_le u sold
  have hDepth : 0 ≤ ((graph s).dist r u : ℝ) + 1 := by positivity
  have hWeighted := mul_le_mul_of_nonneg_right hCard hDepth
  rw [← Finset.sum_mul] at hCostUpper
  nlinarith only [hCostUpper, hCost, hWeighted]

/-- Observations 13 and 14. At most one purchase lies in the first
augmented layer and at most two lie in the second. -/
theorem nash_layer_purchase_card_le (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r u : Fin n} (T : ShortestParents (graph s) r) (H : SimpleGraph (Fin n))
    (hRoot : distanceSum (graph s) r ≤ distanceSum (graph s) u)
    (sold : Finset (Fin n)) {k : ℕ} (hk : k ≤ 2)
    (hLayer : ∀ v ∈ sold, InOutEdgeLayerPlus s T H k u v) : sold.card ≤ max 1 k := by
  by_contra! hMany
  have hSold : sold.Nonempty := Finset.card_pos.mp (by omega)
  have hur : u ≠ r := by
    intro he
    subst u
    obtain ⟨v, hv⟩ := hSold
    exact no_root_purchase_in_layer_plus s α hne hα T hk (hLayer v hv)
  have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have hHalfNat := T.branch_card_le_half hG hur hRoot
  have hHalf : 2 * ((T.branch u).card : ℝ) ≤ n := by exact_mod_cast hHalfNat
  have hCard : (∑ v ∈ sold, ((T.edgeBranch u v).card : ℝ)) ≤ ((T.branch u).card : ℝ) := by
    exact_mod_cast T.sum_edgeBranch_cards_le u sold
  have hBound := nash_layer_purchase_bound s α hne hα T H hRoot sold hSold hk hLayer
  have hPrice : 2 * (n : ℝ) < α := by exact_mod_cast hα
  have hNonneg : (0 : ℝ) ≤ α := NNReal.zero_le_coe
  by_cases hkSmall : k ≤ 1
  · have hTwo : (2 : ℝ) ≤ (sold.card : ℝ) := by exact_mod_cast (show 2 ≤ sold.card by omega)
    have hPay := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (sold.card : ℝ) - 1 by linarith) hNonneg
    have hkReal : (k : ℝ) ≤ 1 := by exact_mod_cast hkSmall
    have hsum : (0 : ℝ) ≤ ∑ v ∈ sold, ((T.edgeBranch u v).card : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hWeighted := mul_le_mul_of_nonneg_right (show 2 * (k : ℝ) ≤ 2 by linarith) hsum
    norm_num at hPay
    linarith
  · have hkTwo : k = 2 := by omega
    subst k
    have hThree : (3 : ℝ) ≤ (sold.card : ℝ) := by exact_mod_cast (show 3 ≤ sold.card by omega)
    have hPay := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ (sold.card : ℝ) - 1 by linarith) hNonneg
    norm_num at hBound hPay
    linarith

/-- The union of the branches affected by selling two purchases in the
second augmented layer contains more than a quarter of the players. -/
theorem nash_two_layer_purchases_large_branch (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r u v w : Fin n} (T : ShortestParents (graph s) r) (H : SimpleGraph (Fin n))
    (hRoot : distanceSum (graph s) r ≤ distanceSum (graph s) u)
    (hvw : v ≠ w) (hv : InOutEdgeLayerPlus s T H 2 u v) (hw : InOutEdgeLayerPlus s T H 2 u w) :
    n < 4 * ((T.edgeBranch u v) ∪ (T.edgeBranch u w)).card := by
  have hSold (x : Fin n) (hx : x ∈ ({v, w} : Finset (Fin n))) :
      InOutEdgeLayerPlus s T H 2 u x := by
    rcases (show x = v ∨ x = w by simpa using hx) with h | h
    · exact h.symm ▸ hv
    · exact h.symm ▸ hw
  have hBound := nash_layer_purchase_bound s α hne hα T H hRoot {v, w} (by simp) le_rfl hSold
  simp [hvw, Finset.sum_insert, Finset.sum_singleton] at hBound
  have hPrice : 2 * (n : ℝ) < α := by exact_mod_cast hα
  have hNat : n < 4 * ((T.edgeBranch u v).card + (T.edgeBranch u w).card) := by
    exact_mod_cast (show (n : ℝ) < 4 * (((T.edgeBranch u v).card : ℝ) +
      ((T.edgeBranch u w).card : ℝ)) by linarith)
  rwa [Finset.card_union_of_disjoint (T.disjoint_edgeBranches u hvw)]

#print axioms nash_layer_purchase_bound
#print axioms nash_layer_purchase_card_le
#print axioms nash_two_layer_purchases_large_branch

end TreeConjecture
