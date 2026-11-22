import TreeConjecture.BlockDegreeTwo
import TreeConjecture.LayerRestrictions

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped NNReal

variable {n : ℕ}

/-- A nonroot block vertex has its parent in the block whenever the root
belongs to that block. -/
theorem IsBiconnectedBlock.parent_mem {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    {r u : Fin n} (hS : IsBiconnectedBlock G S) (hG : G.Connected)
    (hr : r ∈ S) (hu : u ∈ S) (hur : u ≠ r) (T : ShortestParents G r) :
    T.parent u ∈ S := by
  let v := T.parent u
  have hDepth := T.parent_depth hur
  have hZero : G.dist r (T.parent^[G.dist r v] v) = 0 := by
    simp [T.depth_iterate]
  have hRoot : T.parent^[G.dist r v] v = r := (hG.dist_eq_zero_iff.mp hZero).symm
  obtain ⟨p, hp⟩ := T.route_to_iterate (G.dist r v) v le_rfl
  let q := (p.mapLe T.tree_le).copy rfl hRoot
  let w : G.Walk u r := .cons (T.parent_adj hur) q
  have hLen : w.length = G.dist u r := by
    rw [dist_comm]
    simp only [w, Walk.length_cons, q, Walk.length_copy, Walk.length_mapLe, hp]
    exact hDepth
  exact hS.shortest_path_support_subset hu hr w hLen v (by
    rw [Walk.support_cons, List.mem_cons]
    exact Or.inr q.start_mem_support)

/-- A buyer with a purchase in X₀ or X₁ cannot also buy its parent edge in
the same subgraph. Therefore the parent pays for that edge. -/
theorem nash_parent_buys_of_layer_purchase (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r u v : Fin n} (T : ShortestParents (graph s) r) {H : SimpleGraph (Fin n)}
    (hParentAdj : H.Adj u (T.parent u)) (hGParent : (graph s).Adj u (T.parent u))
    (hRoot : distanceSum (graph s) r ≤ distanceSum (graph s) u)
    {k : ℕ} (hk : k ≤ 1) (hLayer : InOutEdgeLayer s T H k u v) :
    u ∈ (s (T.parent u)).val := by
  classical
  have hvParent : v ≠ T.parent u := by
    intro he
    subst v
    have hur : u ≠ r := fun he => hParentAdj.ne (by subst u; rw [T.parent_root])
    obtain ⟨j, _, h⟩ := hLayer
    cases h with
    | out _ _ hoff => exact hoff ⟨hParentAdj.ne, Or.inl rfl⟩
    | down _ _ hp hp' _ =>
      have h1 := T.parent_depth hur
      have h2 := T.parent_depth hp
      rw [hp'] at h2
      omega
  rcases hGParent with hBuy | hBuy
  · have hSold (w : Fin n) (hw : w ∈ ({v, T.parent u} : Finset (Fin n))) :
        InOutEdgeLayerPlus s T H k u w := by
      rcases (show w = v ∨ w = T.parent u by simpa using hw) with hwv | hwp
      · exact hwv.symm ▸ Or.inl hLayer
      · exact hwp.symm ▸ Or.inr ⟨hParentAdj, rfl, hBuy⟩
    have hCard := nash_layer_purchase_card_le s α hne hα T H hRoot {v, T.parent u}
      (hk.trans (by decide)) hSold
    simp [hvParent, max_eq_left hk] at hCard
  · exact hBuy

/-- The orientation step of Lemma 16. The first two parent edges above
an off-tree buyer in a block are both bought by the higher endpoint. -/
theorem nash_block_off_tree_first_two_parent_purchases (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {S : Finset (Fin n)} (hS : IsBiconnectedBlock (graph s) S) {r u v : Fin n}
    (hr : r ∈ S) (hRoot : ∀ x ∈ S, distanceSum (graph s) r ≤ distanceSum (graph s) x)
    (T : ShortestParents (graph s) r) (hadj : (blockGraph (graph s) S).Adj u v)
    (hbuy : v ∈ (s u).val) (hoff : ¬ T.tree.Adj u v) :
    u ∈ (s (T.parent u)).val ∧ T.parent u ∈ (s (T.parent (T.parent u))).val := by
  have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have hDepth := nash_out_edge_depth_ge_three s α hne hα T (Or.inl hbuy) hoff
  have hur : u ≠ r := by
    intro he
    simp [he] at hDepth
  have hpr : T.parent u ≠ r := by
    have hp := T.parent_depth hur
    intro he
    rw [he, dist_self] at hp
    omega
  have hParMem := hS.parent_mem hG hr hadj.1 hur T
  have hGrandMem := hS.parent_mem hG hr hParMem hpr T
  have hParAdj : (blockGraph (graph s) S).Adj u (T.parent u) :=
    ⟨hadj.1, hParMem, T.parent_adj hur⟩
  have hGrandAdj : (blockGraph (graph s) S).Adj (T.parent u) (T.parent (T.parent u)) :=
    ⟨hParMem, hGrandMem, T.parent_adj hpr⟩
  have hLayer : InOutEdgeLayer s T (blockGraph (graph s) S) 0 u v :=
    ⟨0, le_rfl, .out hadj hbuy hoff⟩
  have hParBuy := nash_parent_buys_of_layer_purchase s α hne hα T hParAdj (T.parent_adj hur)
    (hRoot u hadj.1) (Nat.zero_le 1) hLayer
  have hParLayer : InOutEdgeLayer s T (blockGraph (graph s) S) 1 (T.parent u) u :=
    ⟨1, le_rfl, .down hParAdj.symm hParBuy hur rfl (.out hadj hbuy hoff)⟩
  exact ⟨hParBuy, nash_parent_buys_of_layer_purchase s α hne hα T hGrandAdj (T.parent_adj hpr)
    (hRoot _ hParMem) le_rfl hParLayer⟩

#print axioms IsBiconnectedBlock.parent_mem
#print axioms nash_block_off_tree_first_two_parent_purchases

end TreeConjecture
