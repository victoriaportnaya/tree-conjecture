import TreeConjecture.WeightedBlocks
import TreeConjecture.CycleBlocks
import TreeConjecture.BlockPurchaseCount
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ} {S : Finset (Fin n)}

private noncomputable def internalPurchases (s : Profile n) (S : Finset (Fin n))
    (u : Fin n) : Finset (Fin n) := by
  classical
  exact S.filter fun z => z ∈ (s u).val

private theorem mem_internalPurchases {s : Profile n} {u z : Fin n} :
    z ∈ internalPurchases s S u ↔ z ∈ S ∧ z ∈ (s u).val := by
  classical
  simp [internalPurchases]

private theorem sum_block_degrees (s : Profile n) [DecidableRel (blockGraph (graph s) S).Adj] :
    let H := blockGraph (graph s) S
    (∑ v ∈ S, H.degree v) = 2 * H.edgeFinset.card := by
  intro H
  rw [← H.sum_degrees_eq_twice_card_edges]
  apply Finset.sum_subset (Finset.subset_univ S)
  intro v _ hv
  have hEmpty : H.neighborFinset v = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hv ((H.mem_neighborFinset v z).mp hz).1
  rw [← card_neighborFinset_eq_degree, hEmpty, Finset.card_empty]

private theorem block_card_edges_le_of_purchase_bound (s : Profile n)
    [DecidableRel (blockGraph (graph s) S).Adj] (bound : ℕ)
    (h : ∀ u ∈ S, (internalPurchases s S u).card ≤ bound) :
    (blockGraph (graph s) S).edgeFinset.card ≤ S.card * bound := by
  classical
  let buys (u : Fin n) := (internalPurchases s S u).image fun v => s(u, v)
  have cover : (blockGraph (graph s) S).edgeFinset ⊆ S.biUnion buys := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      have huv : (blockGraph (graph s) S).Adj u v := mem_edgeFinset.mp he
      rcases huv.2.2 with huvBuy | hvuBuy
      · exact Finset.mem_biUnion.mpr ⟨u, huv.1, Finset.mem_image.mpr
          ⟨v, mem_internalPurchases.mpr ⟨huv.2.1, huvBuy⟩, rfl⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨v, huv.2.1, Finset.mem_image.mpr
          ⟨u, mem_internalPurchases.mpr ⟨huv.1, hvuBuy⟩, Sym2.eq_swap⟩⟩
  calc
    _ ≤ (S.biUnion buys).card := Finset.card_le_card cover
    _ ≤ ∑ u ∈ S, (buys u).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ S, bound :=
      Finset.sum_le_sum fun u hu => Finset.card_image_le.trans (h u hu)
    _ = S.card * bound := by simp

/-- Each block has a root for which every other vertex buys at most one
edge of non-increasing depth, including edges within the same layer. -/
theorem nash_block_exists_root_with_at_most_one_purchase_toward_root (α : ℝ≥0)
    (s : Profile n) (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    (hS : IsBiconnectedBlock (graph s) S) :
    ∃ r ∈ S, ∀ i ∈ S, i ≠ r → ∀ sold : Finset (Fin n),
      (∀ z ∈ sold, z ∈ S ∧ z ∈ (s i).val) →
      (∀ z ∈ sold, (blockGraph (graph s) S).dist r z ≤ (blockGraph (graph s) S).dist r i) →
      sold.card ≤ 1 := by
  obtain ⟨r, hr, hSum⟩ := hS.exists_min_distanceSum
  refine ⟨r, hr, fun i hi hir sold buy depth => ?_⟩
  have hG := nash_connected (Nat.zero_lt_of_lt i.isLt) α s hne
  have agree : AgreeOutsideBlock (graph s) (graph s) S := fun _ _ _ => Iff.rfl
  apply nash_at_most_one_purchase_toward_root_of_le_distanceSum α s hα hne hir (hSum i hi) sold
    (fun z hz => (buy z hz).2)
  intro z hz
  rw [← hS.block_dist_after_block_change agree hG hG hr (buy z hz).1,
    ← hS.block_dist_after_block_change agree hG hG hr hi]
  exact depth z hz

/-- If each vertex is farthest from some other vertex with an exterior
attachment, an equilibrium block has at most twice as many edges as vertices. -/
theorem nash_block_card_edges_le_twice_card_of_eccentric_attached_roots (α : ℝ≥0)
    (s : Profile n) (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    (hRoots : ∀ i ∈ S, ∃ r ∈ S, i ≠ r ∧
      1 < (blockAttachment (graph s) S r).card ∧
      ∀ z ∈ S, (blockGraph (graph s) S).dist r z ≤ (blockGraph (graph s) S).dist r i) :
    (blockGraph (graph s) S).edgeFinset.card ≤ 2 * S.card := by
  rw [Nat.mul_comm 2]
  apply block_card_edges_le_of_purchase_bound s 2
  intro i hi
  obtain ⟨r, hr, hIr, hWeight, hDepth⟩ := hRoots i hi
  exact nash_block_at_most_two_purchases_toward_attachment α s hα hne hS hi hr hIr hWeight
    (internalPurchases s S i) (fun z hz => mem_internalPurchases.mp hz)
    (fun z hz => hDepth z (mem_internalPurchases.mp hz).1)

/-- At price above the order, a block cannot have a farthest-vertex witness
of no larger weighted distance sum for each vertex. In particular, a
self-centered block with constant weighted distance sum is impossible. -/
theorem nash_no_block_of_eccentric_roots_with_le_weighted_distance (α : ℝ≥0)
    (s : Profile n) (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    (hRoots : ∀ i ∈ S, ∃ r ∈ S, i ≠ r ∧
      weightedBlockDistance (graph s) (graph s) S r ≤ weightedBlockDistance (graph s) (graph s) S i ∧
      ∀ z ∈ S, (blockGraph (graph s) S).dist r z ≤ (blockGraph (graph s) S).dist r i) :
    False := by
  let G := graph s
  let H := blockGraph G S
  have hEdge : H.edgeFinset.card ≤ S.card := by
    rw [← Nat.mul_one S.card]
    apply block_card_edges_le_of_purchase_bound s 1
    intro i hi
    obtain ⟨r, hr, hir, hCost, hDepth⟩ := hRoots i hi
    have hG := nash_connected (Nat.zero_lt_of_lt i.isLt) α s hne
    have agree : AgreeOutsideBlock G G S := fun _ _ _ => Iff.rfl
    have hDist :
        ∀ z ∈ S, G.dist r z = H.dist r z :=
      fun z hz => (hS.block_dist_after_block_change agree hG hG hr hz).symm
    have hCost' : distanceSum G r ≤ distanceSum G i := by
      rw [hS.distanceSum_eq_weightedBlockDistance_add agree hG hG hr,
        hS.distanceSum_eq_weightedBlockDistance_add agree hG hG hi]
      linarith
    let sold := internalPurchases s S i
    have hBuy (z : Fin n) (hz : z ∈ sold) : z ∈ S ∧ z ∈ (s i).val :=
      mem_internalPurchases.mp hz
    change sold.card ≤ 1
    apply nash_at_most_one_purchase_toward_root_of_le_distanceSum α s hα hne hir hCost' sold
      (fun z hz => (hBuy z hz).2)
    intro z hz
    change G.dist r z ≤ G.dist r i
    rw [hDist z (hBuy z hz).1, hDist i hi]
    exact hDepth z (hBuy z hz).1
  obtain ⟨x, hx, hBranch⟩ := nash_block_exists_degree_ge_three s α hα hne hS
  have hHandshaking : (∑ v ∈ S, H.degree v) = 2 * H.edgeFinset.card := sum_block_degrees s
  have hRest : 2 * (S.card - 1) ≤ ∑ z ∈ S.erase x, H.degree z := by
    calc
      _ = ∑ _ ∈ S.erase x, (2 : ℕ) := by simp [Finset.card_erase_of_mem hx, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun z hz => hS.two_le_degree (Finset.mem_of_mem_erase hz)
  have hSum : (∑ z ∈ S, H.degree z) = H.degree x + ∑ z ∈ S.erase x, H.degree z := by
    calc
      _ = ∑ z ∈ insert x (S.erase x), H.degree z := by rw [Finset.insert_erase hx]
      _ = _ := Finset.sum_insert (Finset.notMem_erase x S)
  have hCard : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
  change 3 ≤ H.degree x at hBranch
  omega

#print axioms nash_block_card_edges_le_twice_card_of_eccentric_attached_roots
#print axioms nash_no_block_of_eccentric_roots_with_le_weighted_distance
#print axioms nash_block_exists_root_with_at_most_one_purchase_toward_root

/-- At a minimum-distance root, there are at most as many off-tree edges
as parent edges bought toward children at depth at least three. An off-tree
buyer cannot also buy its own parent edge, and shallower vertices have no
off-tree edges by the girth bound. -/
theorem nash_block_edge_card_le_tree_add_downward_purchases (α : ℝ≥0)
    (s : Profile n) (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    [DecidableRel (blockGraph (graph s) S).Adj] {r : Fin n}
    (hRoot : ∀ u ∈ S, distanceSum (graph s) r ≤ distanceSum (graph s) u)
    (T : ShortestParents (graph s) r)
    [DecidablePred (fun u => 3 ≤ (graph s).dist r u ∧ u ∈ (s (T.parent u)).val)] :
    (blockGraph (graph s) S).edgeFinset.card ≤
      (S.erase r).card + ((S.erase r).filter
        fun u => 3 ≤ (graph s).dist r u ∧ u ∈ (s (T.parent u)).val).card := by
  classical
  let G := graph s
  let H := blockGraph G S
  have hG := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  have root_parent {v : Fin n} (adj : G.Adj r v) : T.parent v = r := by
    have depth := T.parent_depth adj.ne.symm
    change G.dist r (T.parent v) + 1 = G.dist r v at depth
    rw [dist_eq_one_iff_adj.mpr adj] at depth
    exact (hG.dist_eq_zero_iff.mp (show G.dist r (T.parent v) = 0
      from Nat.add_right_cancel depth)).symm
  have notRoot {u v : Fin n} (adj : H.Adj u v) (off : ¬ T.tree.Adj u v) : u ≠ r := by
    intro h
    subst u
    have adjacent := blockGraph_le G S adj
    exact off ⟨adjacent.ne, Or.inr (root_parent adjacent)⟩
  have nonchild {u v : Fin n} (adj : H.Adj u v) (off : ¬ T.tree.Adj u v) :
      T.parent v ≠ u :=
    fun h => off ⟨(blockGraph_le G S adj).ne, Or.inr h⟩
  have unique {u v w : Fin n} (adjV : H.Adj u v) (buyV : v ∈ (s u).val)
      (offV : ¬ T.tree.Adj u v) (adjW : H.Adj u w) (buyW : w ∈ (s u).val)
      (offW : ¬ T.tree.Adj u w) : v = w := by
    by_contra hNe
    have bound := nash_at_most_one_purchase_not_to_child α s hα hne (notRoot adjV offV)
      (hRoot u adjV.1) T {v, w}
      (fun z hz => by
        have he : z = v ∨ z = w := by simpa using hz
        rcases he with rfl | rfl <;> assumption)
      (fun z hz => by
        have he : z = v ∨ z = w := by simpa using hz
        rcases he with rfl | rfl
        · exact nonchild adjV offV
        · exact nonchild adjW offW)
    simp [hNe] at bound
  have subset : offTreeBuyers s T S ⊆
      ((S.erase r).filter fun u => 3 ≤ G.dist r u ∧ u ∈ (s (T.parent u)).val) := by
    intro u hu
    obtain ⟨huS, v, adj, buy, off⟩ := mem_offTreeBuyers.mp hu
    have hur := notRoot adj off
    have hDeep : 3 ≤ G.dist r u := by
      obtain ⟨p, hp, _, hUpper⟩ := T.fundamental_cycle_length_le hG
        (blockGraph_le G S adj) off
      have hLower := nash_cycle_length_ge_eight s α hα hne p hp
      change p.length ≤ 2 * G.dist r u + 2 at hUpper
      omega
    have hParentAdj : G.Adj u (T.parent u) := T.parent_adj hur
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨hur, huS⟩, hDeep, ?_⟩
    rcases hParentAdj with hBuyParent | hParentBuys
    · have hNe : v ≠ T.parent u := by
        intro he
        exact off ⟨(blockGraph_le G S adj).ne, Or.inl he.symm⟩
      have hParentNotChild : T.parent (T.parent u) ≠ u := by
        intro he
        have hDepth := T.parent_depth hur
        have hDepth' := T.depth_parent (T.parent u)
        rw [he] at hDepth'
        omega
      have bound := nash_at_most_one_purchase_not_to_child α s hα hne hur
        (hRoot u huS) T {v, T.parent u}
        (fun z hz => by
          have he : z = v ∨ z = T.parent u := by simpa using hz
          rcases he with rfl | rfl <;> assumption)
        (fun z hz => by
          have he : z = v ∨ z = T.parent u := by simpa using hz
          rcases he with rfl | rfl
          · exact nonchild adj off
          · exact hParentNotChild)
      simp [hNe] at bound
    · exact hParentBuys
  exact (block_edge_card_le_of_unique_offTree_purchases s T unique).trans
    (Nat.add_le_add_left (Finset.card_le_card subset) _)

#print axioms nash_block_edge_card_le_tree_add_downward_purchases

/-- Every equilibrium block at price above n has fewer than twice as many
edges as vertices. In particular it has a vertex of block degree two or three. -/
theorem nash_block_exists_vertex_degree_le_three (α : ℝ≥0) (s : Profile n)
    (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj] :
    ∃ u ∈ S, 2 ≤ (blockGraph (graph s) S).degree u ∧
      (blockGraph (graph s) S).degree u ≤ 3 := by
  classical
  let H := blockGraph (graph s) S
  obtain ⟨r, hr, hRoot⟩ := hS.exists_min_distanceSum
  have hG := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  let T := chooseShortestParents hG r
  have hBound := nash_block_edge_card_le_tree_add_downward_purchases α s hα hne hRoot T
  have hEdges : H.edgeFinset.card ≤ 2 * (S.card - 1) := by
    have hFilter := Finset.card_filter_le (s := S.erase r)
      (p := fun u => 3 ≤ (graph s).dist r u ∧ u ∈ (s (T.parent u)).val)
    have hUpper := hBound.trans (Nat.add_le_add_left hFilter (S.erase r).card)
    rw [Finset.card_erase_of_mem hr] at hUpper
    exact hUpper.trans_eq (by omega)
  have hSome : ∃ u ∈ S, H.degree u ≤ 3 := by
    by_contra! hAll
    have hDegrees : 4 * S.card ≤ ∑ u ∈ S, H.degree u := by
      calc
        _ = ∑ _ ∈ S, (4 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun u hu => hAll u hu
    rw [show (∑ u ∈ S, H.degree u) = 2 * H.edgeFinset.card from sum_block_degrees s] at hDegrees
    have hN : 0 < S.card := Finset.card_pos.mpr ⟨r, hr⟩
    omega
  obtain ⟨u, hu, hUpper⟩ := hSome
  exact ⟨u, hu, hS.two_le_degree hu, hUpper⟩

#print axioms nash_block_exists_vertex_degree_le_three

end TreeConjecture
