import Lax869952Proofs.AncestorCredit
import Lax869952Proofs.BlockBranchAttachments
import Lax869952Proofs.BlockCycleDepth
import Lax869952Proofs.BlockCyclePurchases
import Lax869952Proofs.LayerRootLink

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Function Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ}

/-- Lemma 16. Among the buyer of an off-tree edge and its first two
ancestors, at most one vertex has degree two inside the block. -/
theorem nash_block_off_tree_at_most_one_degree_two (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {S : Finset (Fin n)} (hS : IsBiconnectedBlock (graph s) S) {r u v : Fin n}
    (hr : r ∈ S) (hRoot : ∀ x ∈ S, distanceSum (graph s) r ≤ distanceSum (graph s) x)
    (T : ShortestParents (graph s) r)
    (hCompat : ∀ {x} (p : (graph s).Walk r x), p.length = (graph s).dist r x →
      PurchaseDirected s p → ∀ e ∈ p.edges, e ∈ T.tree.edgeSet)
    [DecidableRel (blockGraph (graph s) S).Adj]
    (hAdj : (blockGraph (graph s) S).Adj u v) (hBuy : v ∈ (s u).val) (hOff : ¬ T.tree.Adj u v) :
    let H := blockGraph (graph s) S
    let a := T.parent u
    let b := T.parent a
    ¬ (H.degree u = 2 ∧ H.degree a = 2) ∧
    ¬ (H.degree u = 2 ∧ H.degree b = 2) ∧
    ¬ (H.degree a = 2 ∧ H.degree b = 2) := by
  classical
  intro H a b
  let G := graph s
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  have hDepthU : 3 ≤ G.dist r u :=
    nash_out_edge_depth_ge_three s α hne hα T (Or.inl hBuy) hOff
  have hDepthA : G.dist r a + 1 = G.dist r u := by
    change G.dist r (T.parent u) + 1 = G.dist r u
    rw [T.depth_parent]
    change G.dist r u - 1 + 1 = G.dist r u
    omega
  have hDepthB : G.dist r b + 1 = G.dist r a := by
    change G.dist r (T.parent a) + 1 = G.dist r a
    rw [T.depth_parent]
    change G.dist r a - 1 + 1 = G.dist r a
    omega
  have notRoot {x : Fin n} (hx : 0 < G.dist r x) : x ≠ r := by
    intro he
    simp [he] at hx
  have hu := notRoot (by omega : 0 < G.dist r u)
  have ha := notRoot (by omega : 0 < G.dist r a)
  have hb := notRoot (by omega : 0 < G.dist r b)
  have hA : a ∈ S := hS.parent_mem hG hr hAdj.1 hu T
  have hB : b ∈ S := hS.parent_mem hG hr hA ha T
  have hC : T.parent b ∈ S := hS.parent_mem hG hr hB hb T
  have hUA : H.Adj u a := ⟨hAdj.1, hA, T.parent_adj hu⟩
  have hAB : H.Adj a b := ⟨hA, hB, T.parent_adj ha⟩
  have hBC : H.Adj b (T.parent b) := ⟨hB, hC, T.parent_adj hb⟩
  have hBU : b ≠ u := by
    intro he
    rw [he] at hDepthB
    omega
  have hCA : T.parent b ≠ a := by
    have hD : G.dist r (T.parent b) + 1 = G.dist r b := T.parent_depth hb
    intro he
    rw [he] at hD
    omega
  have hAV : a ≠ v := fun he => hOff ⟨hAdj.ne, Or.inl he⟩
  obtain ⟨hBuyA, hBuyB⟩ := nash_block_off_tree_first_two_parent_purchases s α hne hα hS hr hRoot
    T hAdj hBuy hOff
  have hPricePos : 0 < α := (show 0 ≤ 2 * (n : ℝ≥0) by positivity).trans_lt hα
  have hPrice : 2 * (n : ℝ) < α := by exact_mod_cast hα
  have hUAbranch : T.branch u ⊆ T.branch a := fun _ hx => T.mem_branch_of_mem_child_branch hu hx
  have hABbranch : T.branch a ⊆ T.branch b := fun _ hx => T.mem_branch_of_mem_child_branch ha hx
  let U := ((T.branch u).card : ℝ)
  let A := ((T.branch a).card : ℝ)
  let B := ((T.branch b).card : ℝ)
  let Au := ((blockAttachment G S u).card : ℝ)
  let Aa := ((blockAttachment G S a).card : ℝ)
  let Ab := ((blockAttachment G S b).card : ℝ)
  have hU0 : 0 ≤ U := Nat.cast_nonneg _
  have hAa0 : 0 ≤ Aa := Nat.cast_nonneg _
  have hUAle : U ≤ A := by
    dsimp only [U, A]
    exact_mod_cast Finset.card_le_card hUAbranch
  have hBhalf : 2 * B ≤ (n : ℝ) := by
    dsimp only [B]
    exact_mod_cast T.branch_card_le_half hG hb (hRoot b hB)
  have hNoChildV : T.parent v ≠ u := fun h => hOff ⟨hAdj.ne, Or.inr h⟩
  have hOffChain : OutEdgeChain s T H 0 u v := .out hAdj hBuy hOff
  have hBudgetU : (∑ x : Fin n, (T.rootLinkCredit u x : ℝ)) ≤ (n : ℝ) := by
    have h := nash_layer_single_root_link_budget s α hne hα hu T (hRoot u hAdj.1)
      (Nat.zero_le 2) (show InOutEdgeLayer s T H 0 u v from ⟨0, le_rfl, hOffChain⟩)
    simpa [ShortestParents.edgeBranch, hNoChildV] using h
  have hBudgetA : (∑ x : Fin n, (T.rootLinkCredit a x : ℝ)) ≤
      (n : ℝ) + U * ((G.dist r a : ℝ) + 3) := by
    have hLayer : InOutEdgeLayer s T H 1 a u := ⟨1, le_rfl, .down hUA.symm hBuyA hu rfl hOffChain⟩
    have h := nash_layer_single_root_link_budget s α hne hα ha T (hRoot a hA) (by decide) hLayer
    have hEdge : T.edgeBranch a u = T.branch u := by simp [ShortestParents.edgeBranch, hu, a]
    rw [hEdge] at h
    change _ ≤ (n : ℝ) + U * (2 * ((1 : ℕ) : ℝ) + (G.dist r a : ℝ) + 1) at h
    have hCoeff : 2 * ((1 : ℕ) : ℝ) + (G.dist r a : ℝ) + 1 =
        (G.dist r a : ℝ) + 3 := by push_cast; ring
    rwa [hCoeff] at h
  have hAtU (hDeg : H.degree u = 2) : ∃ k : ℕ, k / 2 ≤ G.dist r u ∧
      (α : ℝ) ≤ 2 * ((k : ℝ) - 3) * U := by
    have hAttach := hS.blockAttachment_eq_sdiff_of_degree_two hG hr T hUA hAdj hAV hDeg
    have hEq : Au = U := by
      change ((blockAttachment G S u).card : ℝ) = U
      rw [hAttach]
      simp [hNoChildV, U]
    obtain ⟨c, hc, hcMin⟩ := hS.exists_shortest_cycle_at hAdj.1
    have hLoc := (nash_degree_two_maximal_block s α hne hα hS hUA hAdj hDeg hBuyA hBuy c hc).2
    change (α : ℝ) ≤ 2 * ((c.length : ℝ) - 3) * Au at hLoc
    rw [hEq] at hLoc
    have hD := nash_block_branch_cycle_depth s α hne hα hS T hCompat (T.mem_own_branch u)
      0 (by decide) (by simp) hAdj hBuy hOff c hcMin
    exact ⟨c.length, by simpa [G] using hD, hLoc⟩
  have hAtA (hDeg : H.degree a = 2) : ∃ k : ℕ, k / 2 ≤ G.dist r a + 1 ∧
      (α : ℝ) ≤ 2 * ((k : ℝ) - 3) * Aa ∧ A = U + Aa ∧ U ≤ Aa := by
    have hAttach := hS.blockAttachment_eq_sdiff_of_degree_two hG hr T hAB hUA.symm hBU hDeg
    have hAttach' : blockAttachment G S a = T.branch a \ T.branch u := by
      simpa only [if_pos (show T.parent u = a from rfl)] using hAttach
    have hEqNat : (blockAttachment G S a).card + (T.branch u).card = (T.branch a).card := by
      rw [hAttach', Finset.card_sdiff_add_card_eq_card hUAbranch]
    have hEq : Aa + U = A := by
      dsimp only [Aa, U, A]
      exact_mod_cast hEqNat
    obtain ⟨c, hc, hcMin⟩ := hS.exists_shortest_cycle_at hA
    have hLoc := (nash_degree_two_maximal_block s α hne hα hS hAB hUA.symm hDeg hBuyB hBuyA c hc).2
    have hDown : U ≤ Aa := by
      dsimp only [U, Aa]
      exact_mod_cast nash_degree_two_block_down_branch s α hne hα hS T ha hu rfl rfl
        hAB hUA.symm hDeg hBuyB hBuyA c hc
    have hD := nash_block_branch_cycle_depth s α hne hα hS T hCompat (hUAbranch (T.mem_own_branch u))
      1 (by decide) hDepthA.symm hAdj hBuy hOff c hcMin
    exact ⟨c.length, hD, hLoc, by linarith, hDown⟩
  have hAtB (hDeg : H.degree b = 2) : 2 * A ≤ B := by
    have hNeighbors := eq_neighbors_of_degree_two hBC hAB.symm hCA hDeg
    obtain ⟨z, hz, hIn⟩ := (nash_block_vertex_incident_purchases s α hne hα hS hB).2
    have hzMem := (H.mem_neighborFinset b z).mpr hz
    rw [← hNeighbors] at hzMem
    have hzNe : z ≠ a := by
      intro he
      rw [he] at hIn
      exact nash_no_double_purchase α hPricePos s hne (i := b) (r := a) hBuyB hIn
    have hzEq : z = T.parent b := (show z = T.parent b ∨ z = a by simpa using hzMem).resolve_right hzNe
    have hBuyC : b ∈ (s (T.parent b)).val :=
      Eq.mp (congrArg (fun a => b ∈ (s a).val) hzEq) hIn
    have hAttach := hS.blockAttachment_eq_sdiff_of_degree_two hG hr T hBC hAB.symm hCA hDeg
    have hAttach' : blockAttachment G S b = T.branch b \ T.branch a := by
      simpa only [if_pos (show T.parent a = b from rfl)] using hAttach
    have hEqNat : (blockAttachment G S b).card + (T.branch a).card = (T.branch b).card := by
      rw [hAttach', Finset.card_sdiff_add_card_eq_card hABbranch]
    have hEq : Ab + A = B := by
      dsimp only [Ab, A, B]
      exact_mod_cast hEqNat
    obtain ⟨c, hc⟩ := hS.twoConnected.exists_cycle_at hB
    have hDown : A ≤ Ab := by
      dsimp only [A, Ab]
      exact_mod_cast nash_degree_two_block_down_branch s α hne hα hS T hb ha rfl rfl
        hBC hAB.symm hDeg hBuyC hBuyB c hc
    linarith

  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hu2, ha2⟩
    obtain ⟨k, hk, hkPrice⟩ := hAtU hu2
    obtain ⟨_, _, _, hSplit, hDown⟩ := hAtA ha2
    have hA2 : 2 * U ≤ A := by linarith
    have hCredit := (T.sum_rootLinkCredit_parent_lower u (by change 2 ≤ G.dist r u; omega)).trans hBudgetU
    change 2 * U + ((G.dist r u : ℝ) - 1) * A ≤ (n : ℝ) at hCredit
    have hD : (3 : ℝ) ≤ (G.dist r u : ℝ) := by exact_mod_cast hDepthU
    have hK : (k : ℝ) ≤ 2 * (G.dist r u : ℝ) + 1 := by
      exact_mod_cast (show k ≤ 2 * G.dist r u + 1 by omega)
    have hPriceBound := mul_le_mul_of_nonneg_right (show 2 * ((k : ℝ) - 3) ≤
      4 * (G.dist r u : ℝ) by linarith) hU0
    have hWeighted := mul_le_mul_of_nonneg_left hA2 (show 0 ≤ (G.dist r u : ℝ) - 1 by linarith)
    nlinarith only [hCredit, hPrice, hkPrice, hPriceBound, hWeighted]
  · rintro ⟨hu2, hb2⟩
    obtain ⟨k, hk, hkPrice⟩ := hAtU hu2
    have hB2 := hAtB hb2
    have hB2U : 2 * U ≤ B := by linarith
    have hCredit := (T.sum_rootLinkCredit_grandparent_lower u hDepthU).trans hBudgetU
    change 2 * U + 2 * A + ((G.dist r u : ℝ) - 3) * B ≤ (n : ℝ) at hCredit
    have hD : (3 : ℝ) ≤ (G.dist r u : ℝ) := by exact_mod_cast hDepthU
    have hK : (k : ℝ) ≤ 2 * (G.dist r u : ℝ) + 1 := by
      exact_mod_cast (show k ≤ 2 * G.dist r u + 1 by omega)
    have hPriceBound := mul_le_mul_of_nonneg_right (show 2 * ((k : ℝ) - 3) ≤
      2 * (2 * (G.dist r u : ℝ) - 2) by linarith) hU0
    have hWeighted := mul_le_mul_of_nonneg_left hB2U (show 0 ≤ (G.dist r u : ℝ) - 3 by linarith)
    nlinarith only [hCredit, hPrice, hkPrice, hPriceBound, hWeighted, hUAle]
  · rintro ⟨ha2, hb2⟩
    obtain ⟨k, hk, hkPrice, hSplit, _⟩ := hAtA ha2
    have hB2 := hAtB hb2
    have hK8 : 8 ≤ k := by
      by_contra h
      have hK7 : (k : ℝ) ≤ 7 := by exact_mod_cast (show k ≤ 7 by omega)
      have hPriceBound := mul_le_mul_of_nonneg_right (show 2 * ((k : ℝ) - 3) ≤ 8 by linarith) hAa0
      nlinarith only [hPrice, hkPrice, hPriceBound, hB2, hBhalf, hSplit, hU0]
    have hDepthA3 : 3 ≤ G.dist r a := by omega
    have hD : (3 : ℝ) ≤ (G.dist r a : ℝ) := by exact_mod_cast hDepthA3
    have hK : (k : ℝ) ≤ 2 * (G.dist r a : ℝ) + 3 := by
      exact_mod_cast (show k ≤ 2 * G.dist r a + 3 by omega)
    have hPriceBound := mul_le_mul_of_nonneg_right (show 2 * ((k : ℝ) - 3) ≤
      4 * (G.dist r a : ℝ) by linarith) hAa0
    have hCredit := (T.sum_rootLinkCredit_parent_lower a (by change 2 ≤ G.dist r a; omega)).trans hBudgetA
    change 2 * A + ((G.dist r a : ℝ) - 1) * B ≤ (n : ℝ) + U * ((G.dist r a : ℝ) + 3) at hCredit
    have hWeighted := mul_le_mul_of_nonneg_left hB2 (show 0 ≤ (G.dist r a : ℝ) - 1 by linarith)
    have hRemaining := mul_nonneg hU0 (show 0 ≤ (G.dist r a : ℝ) - 3 by linarith)
    rw [hSplit] at hCredit hWeighted
    nlinarith only [hCredit, hPrice, hkPrice, hPriceBound, hWeighted, hRemaining]

#print axioms nash_block_off_tree_at_most_one_degree_two

end Lax869952Proofs
