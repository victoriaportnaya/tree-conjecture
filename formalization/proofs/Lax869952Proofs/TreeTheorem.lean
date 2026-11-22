import Lax869952Proofs.BlockPurchaseCount
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ}

private theorem block_edge_card_le (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {S : Finset (Fin n)} {r : Fin n} (hRoot : ∀ x ∈ S, distanceSum (graph s) r ≤ distanceSum (graph s) x)
    (T : ShortestParents (graph s) r) [DecidableRel (blockGraph (graph s) S).Adj] :
    (blockGraph (graph s) S).edgeFinset.card ≤ (S.erase r).card + (offTreeBuyers s T S).card := by
  apply block_edge_card_le_of_unique_offTree_purchases s T
  intro u v w hv hvBuy hvOff hw hwBuy hwOff
  exact nash_layer_one_purchase_unique s α hne hα T (hRoot u hv.1)
    ⟨0, by decide, .out hv hvBuy hvOff⟩ ⟨0, by decide, .out hw hwBuy hwOff⟩

private theorem nash_two_high_degree_in_off_tree_triple (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {S : Finset (Fin n)} (hS : IsBiconnectedBlock (graph s) S) {r u : Fin n}
    (hr : r ∈ S) (hRoot : ∀ x ∈ S, distanceSum (graph s) r ≤ distanceSum (graph s) x)
    (T : ShortestParents (graph s) r)
    (hCompat : ∀ {v} (p : (graph s).Walk r v), p.length = (graph s).dist r v →
      PurchaseDirected s p → ∀ e ∈ p.edges, e ∈ T.tree.edgeSet)
    [DecidableRel (blockGraph (graph s) S).Adj] (hu : u ∈ offTreeBuyers s T S) :
    let H := blockGraph (graph s) S
    let high := (S.erase r).filter fun v => 3 ≤ H.degree v
    2 ≤ (high.filter fun v => v ∈ offTreeBuyerTriple T u).card := by
  classical
  intro H high
  let G := graph s
  obtain ⟨huS, v, hAdj, hBuy, hOff⟩ := mem_offTreeBuyers.mp hu
  let a := T.parent u
  let b := T.parent a
  obtain ⟨hUA, hUB, hAB⟩ := nash_block_off_tree_at_most_one_degree_two s α hne hα hS hr hRoot
    T hCompat hAdj hBuy hOff
  change ¬ (H.degree u = 2 ∧ H.degree a = 2) at hUA
  change ¬ (H.degree u = 2 ∧ H.degree b = 2) at hUB
  change ¬ (H.degree a = 2 ∧ H.degree b = 2) at hAB
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  have du : 3 ≤ G.dist r u := nash_out_edge_depth_ge_three s α hne hα T (Or.inl hBuy) hOff
  have da : G.dist r a = G.dist r u - 1 := T.depth_parent u
  have db : G.dist r b = G.dist r a - 1 := T.depth_parent a
  have neRoot {x : Fin n} (hx : 0 < G.dist r x) : x ≠ r := by
    intro he
    simp [he] at hx
  have huNe := neRoot (by omega : 0 < G.dist r u)
  have haNe := neRoot (by omega : 0 < G.dist r a)
  have hbNe := neRoot (by omega : 0 < G.dist r b)
  have haS := hS.parent_mem hG hr huS huNe T
  have hbS := hS.parent_mem hG hr haS haNe T
  have huDeg : 2 ≤ H.degree u := hS.two_le_degree huS
  have haDeg : 2 ≤ H.degree a := hS.two_le_degree haS
  have hbDeg : 2 ≤ H.degree b := hS.two_le_degree hbS
  have highMem {x : Fin n} (hx : x ∈ S) (hxNe : x ≠ r) (hxDeg : 3 ≤ H.degree x)
      (hxTriple : x ∈ offTreeBuyerTriple T u) :
      x ∈ high.filter fun w => w ∈ offTreeBuyerTriple T u :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxNe, hx⟩, hxDeg⟩, hxTriple⟩
  have uTriple : u ∈ offTreeBuyerTriple T u := by simp [offTreeBuyerTriple]
  have aTriple : a ∈ offTreeBuyerTriple T u := by simp [offTreeBuyerTriple, a]
  have bTriple : b ∈ offTreeBuyerTriple T u := by simp [offTreeBuyerTriple, b, a]
  have hua : u ≠ a := by intro he; have := congrArg (G.dist r) he; omega
  have hub : u ≠ b := by intro he; have := congrArg (G.dist r) he; omega
  have hab : a ≠ b := by intro he; have := congrArg (G.dist r) he; omega
  apply Finset.one_lt_card.mpr
  by_cases hU : 3 ≤ H.degree u
  · by_cases hA : 3 ≤ H.degree a
    · exact ⟨u, highMem huS huNe hU uTriple, a, highMem haS haNe hA aTriple, hua⟩
    · have hB : 3 ≤ H.degree b := by
        by_contra h
        exact hAB ⟨by omega, by omega⟩
      exact ⟨u, highMem huS huNe hU uTriple, b, highMem hbS hbNe hB bTriple, hub⟩
  · have hA : 3 ≤ H.degree a := by
      by_contra h
      exact hUA ⟨by omega, by omega⟩
    have hB : 3 ≤ H.degree b := by
      by_contra h
      exact hUB ⟨by omega, by omega⟩
    exact ⟨a, highMem haS haNe hA aTriple, b, highMem hbS hbNe hB bTriple, hab⟩

private theorem nash_no_biconnected_block_at_two_n (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {S : Finset (Fin n)} (hS : IsBiconnectedBlock (graph s) S) : False := by
  classical
  let G := graph s
  let H := blockGraph G S
  obtain ⟨r, hr, hRoot⟩ := hS.exists_min_distanceSum
  have hPrice : 2 * ((n - 1 : ℕ) : ℝ≥0) < α := by
    have hLE : ((n - 1 : ℕ) : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast Nat.sub_le n 1
    exact (mul_le_mul_of_nonneg_left hLE (by norm_num)).trans_lt hα
  obtain ⟨T, hCompat⟩ := exists_purchase_directed_shortest_parents s α hne hPrice r
  let O := offTreeBuyers s T S
  let R := S.erase r
  let high := R.filter fun v => 3 ≤ H.degree v
  let twice := twoSecondLayerBuyers s T S
  let load (v : Fin n) := (O.filter fun u => v ∈ offTreeBuyerTriple T u).card
  let excess := ∑ v ∈ R, (H.degree v - 2)
  have hTwice : twice.card < H.degree r :=
    nash_block_two_second_layer_buyers_lt_root_degree s α hne hα hS hr hRoot T
  have hEdgeCount := block_edge_card_le s α hne hα hRoot T
  change H.edgeFinset.card ≤ R.card + O.card at hEdgeCount
  have hAtLeastTwo (v : Fin n) (hv : v ∈ R) : 2 ≤ H.degree v :=
    hS.two_le_degree (Finset.mem_erase.mp hv).2
  have hHighCard : high.card ≤ excess := by
    calc
      high.card = ∑ _v ∈ high, (1 : ℕ) := by simp
      _ ≤ ∑ v ∈ high, (H.degree v - 2) := by
        apply Finset.sum_le_sum
        intro v hv
        have hv' : 3 ≤ H.degree v := (Finset.mem_filter.mp hv).2
        omega
      _ ≤ excess := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)
  have count (F : Finset (Fin n)) (P : Fin n → Prop) [DecidablePred P] :
      (∑ v ∈ F, if P v then (1 : ℕ) else 0) = (F.filter P).card := by
    rw [← Finset.sum_filter]
    simp
  have hLower : 2 * O.card ≤ ∑ v ∈ high, load v := by
    calc
      2 * O.card = ∑ _u ∈ O, (2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ u ∈ O, (high.filter fun v => v ∈ offTreeBuyerTriple T u).card := by
        apply Finset.sum_le_sum
        intro u hu
        exact nash_two_high_degree_in_off_tree_triple s α hne hα hS hr hRoot T hCompat hu
      _ = ∑ u ∈ O, ∑ v ∈ high, if v ∈ offTreeBuyerTriple T u then (1 : ℕ) else 0 := by
        simp only [count]
      _ = ∑ v ∈ high, load v := by
        rw [Finset.sum_comm]
        simp only [count, load]
  have hUpper : (∑ v ∈ high, load v) ≤ high.card + twice.card := by
    calc
      _ ≤ ∑ v ∈ high, (1 + if v ∈ twice then 1 else 0) := by
        apply Finset.sum_le_sum
        intro v hv
        have hvS : v ∈ S := (Finset.mem_erase.mp (Finset.mem_filter.mp hv).1).2
        exact nash_off_tree_triple_load_le s α hne hα hS hr hRoot T hvS
      _ = high.card + (high.filter fun v => v ∈ twice).card := by
        simp [Finset.sum_add_distrib, count]
      _ ≤ high.card + twice.card := Nat.add_le_add_left
        (Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2)) _
  have hRsum : (∑ v ∈ R, H.degree v) = 2 * R.card + excess := by
    calc
      _ = ∑ v ∈ R, (2 + (H.degree v - 2)) := by
        apply Finset.sum_congr rfl
        intro v hv
        have hv' := hAtLeastTwo v hv
        omega
      _ = _ := by simp [Finset.sum_add_distrib, excess, Nat.mul_comm]
  have hSsum : (∑ v ∈ S, H.degree v) = H.degree r + (∑ v ∈ R, H.degree v) := by
    have hInsert : insert r R = S := Finset.insert_erase hr
    rw [← hInsert, Finset.sum_insert (by simp [R])]
  have hHandshaking : (∑ v ∈ S, H.degree v) = 2 * H.edgeFinset.card := by
    rw [← H.sum_degrees_eq_twice_card_edges]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro v _ hv
    have hNoEdges : H.neighborFinset v = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hv ((H.mem_neighborFinset v w).mp hw).1
    rw [← card_neighborFinset_eq_degree, hNoEdges, Finset.card_empty]
  omega

/-- Dippel–Vetta (STACS 2024), Theorem 1. Every Nash equilibrium of the
sum network creation game is a tree at edge price strictly above twice
the number of players. -/
theorem nash_tree_of_two_n_lt_alpha {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (hα : 2 * (n : ℝ≥0) < α) (s : Profile n) (hne : IsNashEquilibrium α s) :
    (graph s).IsTree := by
  by_contra hNotTree
  obtain ⟨S, hS, _, _⟩ := nash_largest_block_of_not_tree s α hn hne hNotTree
  exact nash_no_biconnected_block_at_two_n s α hne hα hS

theorem dippelVetta : dippelVettaStatement := by
  intro n hn α hα s hne
  exact nash_tree_of_two_n_lt_alpha (by omega) α hα s hne

#print axioms nash_tree_of_two_n_lt_alpha
#print axioms dippelVetta

end Lax869952Proofs
