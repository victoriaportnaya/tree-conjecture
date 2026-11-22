import Lax869952Proofs.BlockCyclePurchases
import Lax869952Proofs.BlockParentPurchases
import Lax869952Proofs.LayerDepth
import Lax869952Proofs.RootBranchSwap

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Function Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

variable {n : ℕ}

theorem ShortestParents.disjoint_branch_of_same_depth {G : SimpleGraph (Fin n)} {r u v : Fin n}
    (T : ShortestParents G r) (hDepth : G.dist r u = G.dist r v) (hne : u ≠ v) :
    Disjoint (T.branch u) (T.branch v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, hi, hu⟩ : ∃ i ≤ G.dist r x, T.parent^[i] x = u := by
    simpa [branch] using hx
  obtain ⟨j, hj, hv⟩ : ∃ j ≤ G.dist r x, T.parent^[j] x = v := by
    simpa [branch] using hy
  have hDi := T.depth_iterate i x
  have hDj := T.depth_iterate j x
  rw [hu] at hDi
  rw [hv] at hDj
  have hij : i = j := by omega
  exact hne (hu.symm.trans (hij ▸ hv))

/-- Vertices of a block buying at least two edges in the second layer. -/
noncomputable def twoSecondLayerBuyers (s : Profile n) {r : Fin n}
    (T : ShortestParents (graph s) r) (S : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact S.filter fun u => ∃ v w, v ≠ w ∧
    InOutEdgeLayer s T (blockGraph (graph s) S) 2 u v ∧
    InOutEdgeLayer s T (blockGraph (graph s) S) 2 u w

/-- Lemma 17. Double buyers in the second layer inject into the
incoming neighbors of the block root via their depth-one ancestor. -/
theorem nash_block_two_second_layer_buyers_lt_root_degree (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {S : Finset (Fin n)} (hS : IsBiconnectedBlock (graph s) S) {r : Fin n}
    (hr : r ∈ S) (hRoot : ∀ x ∈ S, distanceSum (graph s) r ≤ distanceSum (graph s) x)
    (T : ShortestParents (graph s) r) [DecidableRel (blockGraph (graph s) S).Adj] :
    (twoSecondLayerBuyers s T S).card < (blockGraph (graph s) S).degree r := by
  classical
  let G := graph s
  let H := blockGraph G S
  let B := twoSecondLayerBuyers s T S
  let ancestor (u : Fin n) := T.parent (T.parent u)
  let incoming := (H.neighborFinset r).filter fun a => r ∈ (s a).val
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  have hLarge (u : Fin n) (hu : u ∈ B) : u ∈ S ∧ G.dist r u = 3 ∧ n < 4 * (T.branch u).card := by
    change u ∈ twoSecondLayerBuyers s T S at hu
    obtain ⟨huS, v, w, hNe, hv, hw⟩ := Finset.mem_filter.mp hu
    have hUnion := nash_two_layer_purchases_large_branch s α hne hα T H (hRoot u huS)
      hNe (Or.inl hv) (Or.inl hw)
    have hDepth := nash_two_second_layer_purchases_depth_eq_three s α hne hα T H
      (fun hadj => hRoot _ hadj.1) hNe hv hw hUnion
    have hCard := Finset.card_le_card
      (Finset.union_subset (T.edgeBranch_subset_branch u v) (T.edgeBranch_subset_branch u w))
    exact ⟨huS, hDepth, by omega⟩
  have depth_ancestor {u : Fin n} (hu : G.dist r u = 3) : G.dist r (ancestor u) = 1 := by
    change G.dist r (T.parent (T.parent u)) = 1
    rw [T.depth_parent, T.depth_parent, hu]
  have branch_ancestor {u : Fin n} (hu : G.dist r u = 3) : T.branch u ⊆ T.branch (ancestor u) := by
    intro x hx
    have h := T.mem_branch_iterate hx 2 (by change 2 ≤ G.dist r u; omega)
    simpa [ancestor, Function.iterate_succ_apply] using h
  have hneRoot {x : Fin n} (hx : 0 < G.dist r x) : x ≠ r := by
    intro he
    simp [he] at hx
  have ancestor_mem {u : Fin n} (hu : u ∈ S) (hDepth : G.dist r u = 3) : ancestor u ∈ S := by
    have hParentDepth : G.dist r (T.parent u) = 2 := by rw [T.depth_parent, hDepth]
    exact hS.parent_mem hG hr (hS.parent_mem hG hr hu (hneRoot (by omega)) T)
      (hneRoot (by omega)) T
  have hMaps : Set.MapsTo ancestor (↑B : Set (Fin n)) (↑incoming : Set (Fin n)) := by
    intro u hu
    obtain ⟨huS, huDepth, huSize⟩ := hLarge u hu
    have haDepth := depth_ancestor huDepth
    have haS := ancestor_mem huS huDepth
    have hAdj : H.Adj r (ancestor u) :=
      ⟨hr, haS, dist_eq_one_iff_adj.mp haDepth⟩
    have hNoBuy : ancestor u ∉ (s r).val := by
      intro hBuy
      have hSwap := nash_root_branch_swap_bound s α hne T haDepth huDepth
        (branch_ancestor huDepth (T.mem_own_branch u)) hBuy
      have hHalf := T.branch_card_le_half hG (hneRoot (by omega : 0 < G.dist r (ancestor u)))
        (hRoot (ancestor u) haS)
      omega
    have hBuy : r ∈ (s (ancestor u)).val := (blockGraph_le G S hAdj).resolve_left hNoBuy
    exact Finset.mem_filter.mpr ⟨(H.mem_neighborFinset r _).mpr hAdj, hBuy⟩
  have hInj : (↑B : Set (Fin n)).InjOn ancestor := by
    intro u hu v hv huv
    by_contra hNe
    obtain ⟨huS, huDepth, huSize⟩ := hLarge u hu
    obtain ⟨_, hvDepth, hvSize⟩ := hLarge v hv
    have haDepth := depth_ancestor huDepth
    have hDisjoint := T.disjoint_branch_of_same_depth (huDepth.trans hvDepth.symm) hNe
    have hInside : T.branch u ∪ T.branch v ⊆ T.branch (ancestor u) :=
      Finset.union_subset (branch_ancestor huDepth) (huv.symm ▸ branch_ancestor hvDepth)
    have hBoth := Finset.card_le_card hInside
    rw [Finset.card_union_of_disjoint hDisjoint] at hBoth
    have haS := ancestor_mem huS huDepth
    have hHalf := T.branch_card_le_half hG (hneRoot (by omega : 0 < G.dist r (ancestor u)))
      (hRoot (ancestor u) haS)
    omega
  have hCard := Finset.card_le_card_of_injOn ancestor hMaps hInj
  obtain ⟨w, hAdj, hBuy⟩ := (nash_block_vertex_incident_purchases s α hne hα hS hr).1
  have hPos : 0 < α := (show 0 ≤ 2 * (n : ℝ≥0) by positivity).trans_lt hα
  have hProper : incoming ⊂ H.neighborFinset r := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hMem : w ∈ incoming := he.symm ▸ (H.mem_neighborFinset r w).mpr hAdj
    exact nash_no_double_purchase α hPos s hne hBuy (Finset.mem_filter.mp hMem).2
  exact hCard.trans_lt (Finset.card_lt_card hProper)

#print axioms nash_block_two_second_layer_buyers_lt_root_degree

end Lax869952Proofs
