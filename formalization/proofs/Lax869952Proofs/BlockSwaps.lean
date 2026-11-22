import Lax869952Proofs.BlockDegreeTwo

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}

/-- Distances from a block vertex to an attachment factor through its entry. -/
theorem IsBiconnectedBlock.dist_add_of_mem_blockAttachment (hS : IsBiconnectedBlock G S)
    (hG : G.Connected) {x v y : Fin n} (hv : v ∈ S) (hy : y ∈ S)
    (hx : x ∈ blockAttachment G S v) : G.dist y x = G.dist y v + G.dist v x := by
  obtain ⟨p, hp⟩ := mem_blockAttachment.mp hx
  obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist x y
  obtain ⟨a, ha, t, hsub, hentry⟩ := exists_first_entry_walk q hy
  have he := hS.first_entry_unique hv ha p t hp hentry
  have hVisit : v ∈ q.support := he.symm ▸ hsub t.end_mem_support
  have hLower := walk_length_ge_via q hVisit
  rw [hq] at hLower
  have hUpper : G.dist x y ≤ G.dist x v + G.dist v y := hG.dist_triangle
  rw [dist_comm (u := y) (v := x), dist_comm (u := y) (v := v),
    dist_comm (u := v) (v := x), Nat.add_comm]
  exact le_antisymm hUpper hLower

theorem blockAttachment_card_pos (v : Fin n) :
    0 < (blockAttachment G S v).card := by
  apply Finset.card_pos.mpr
  refine ⟨v, mem_blockAttachment.mpr ⟨.nil, ?_⟩⟩
  simp [FirstEntryInto]

/-- A two-step swap gains at least one step throughout each selected attachment. -/
theorem nash_block_two_step_sum_bound (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj]
    {u v w : Fin n} {T : Finset (Fin n)}
    (huv : (blockGraph (graph s) S).Adj u v)
    (hvw : (blockGraph (graph s) S).Adj v w)
    (huw : u ≠ w) (hdegree : (blockGraph (graph s) S).degree v = 2)
    (hBuy : v ∈ (s u).val)
    (hT : T ⊆ S)
    (hDist : ∀ z ∈ T, (graph s).dist u z = 2 + (graph s).dist w z) :
    (∑ z ∈ T, (blockAttachment (graph s) S z).card) ≤
      (blockAttachment (graph s) S v).card := by
  classical
  have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have hdegree' := degree_two_neighbor_condition huv.symm hvw huw
    (blockGraph_le (graph s) S) hdegree
    (fun p hp he => hS.cycle_edges_subset p hp huv he)
  have hSwap := nash_degree_two_swap_bound s α hne hBuy
    (blockGraph_le (graph s) S hvw) huw hdegree'
  rw [hS.separatedVertices_eq_blockAttachment hG huv.1 huv.2.1
    (blockGraph_le (graph s) S huv).ne] at hSwap
  have hContain (z : Fin n) (hz : z ∈ S)
      (h : (graph s).dist u z = 2 + (graph s).dist w z) :
      blockAttachment (graph s) S z ⊆ verticesViaTwoSteps (graph s) u w := by
    intro t ht
    apply mem_verticesViaTwoSteps.mpr
    rw [hS.dist_add_of_mem_blockAttachment hG hz huv.1 ht,
      hS.dist_add_of_mem_blockAttachment hG hz hvw.2.1 ht, h, Nat.add_assoc]
  have hSub : T.biUnion (blockAttachment (graph s) S) ⊆ verticesViaTwoSteps (graph s) u w := by
    intro z hz
    obtain ⟨t, ht, hMem⟩ := Finset.mem_biUnion.mp hz
    exact hContain t (hT ht) (hDist t ht) hMem
  have hDisjoint : (↑T : Set (Fin n)).PairwiseDisjoint (blockAttachment (graph s) S) := by
    intro a ha b hb hab
    exact hS.disjoint_blockAttachments (hT (Finset.mem_coe.mp ha))
      (hT (Finset.mem_coe.mp hb)) hab
  have hCard := (Finset.card_le_card hSub).trans hSwap
  rwa [Finset.card_biUnion hDisjoint] at hCard

/-- The two-step swap inequality for two distinct attachment sets. -/
theorem nash_block_two_step_pair_bound (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj]
    {u v w x y : Fin n}
    (huv : (blockGraph (graph s) S).Adj u v)
    (hvw : (blockGraph (graph s) S).Adj v w)
    (huw : u ≠ w) (hdegree : (blockGraph (graph s) S).degree v = 2)
    (hBuy : v ∈ (s u).val)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hX : (graph s).dist u x = 2 + (graph s).dist w x)
    (hY : (graph s).dist u y = 2 + (graph s).dist w y) :
    (blockAttachment (graph s) S x).card + (blockAttachment (graph s) S y).card ≤
      (blockAttachment (graph s) S v).card := by
  have hSum := nash_block_two_step_sum_bound s α hne hS huv hvw huw hdegree hBuy
    (T := {x, y}) (by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · obtain rfl := Finset.mem_singleton.mp hz
        exact hy)
    (by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hX
      · obtain rfl := Finset.mem_singleton.mp hz
        exact hY)
  simpa [hxy] using hSum

/-- A maximal attachment forces ownership away from it along a two-step
geodesic through an internal degree-two vertex. -/
theorem nash_block_forces_purchase_away_from_maximum (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj]
    {u v w x : Fin n}
    (huv : (blockGraph (graph s) S).Adj u v)
    (hvw : (blockGraph (graph s) S).Adj v w)
    (huw : u ≠ w) (hdegree : (blockGraph (graph s) S).degree v = 2)
    (hx : x ∈ S) (hwx : w ≠ x)
    (hDist : (graph s).dist u x = 2 + (graph s).dist w x)
    (hMax : (blockAttachment (graph s) S v).card ≤ (blockAttachment (graph s) S x).card) :
    u ∈ (s v).val := by
  have hAdj : (graph s).Adj u v := blockGraph_le (graph s) S huv
  rcases hAdj with hBuy | hBuy
  · exfalso
    have hStep : (graph s).dist u w = 2 := by
      have hUpper : (graph s).dist u w ≤ 2 :=
        dist_le (.cons (Or.inl hBuy) (.cons (blockGraph_le (graph s) S hvw) .nil))
      have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
      have hTri : (graph s).dist u x ≤ (graph s).dist u w + (graph s).dist w x :=
        hG.dist_triangle
      omega
    have h := nash_block_two_step_pair_bound s α hne hS huv hvw huw hdegree hBuy
      hvw.2.1 hx hwx (by simpa using hStep) hDist
    have hPos : 0 < (blockAttachment (graph s) S w).card := blockAttachment_card_pos w
    omega
  · exact hBuy

/-- Two inward purchases on a shortest path of length three cannot both
survive when the two middle vertices have degree two in the block. -/
theorem nash_block_no_inward_purchases_on_three_step_path (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj]
    {a b c d : Fin n}
    (hab : (blockGraph (graph s) S).Adj a b)
    (hbc : (blockGraph (graph s) S).Adj b c)
    (hcd : (blockGraph (graph s) S).Adj c d)
    (hLength : (graph s).dist a d = 3)
    (hDegB : (blockGraph (graph s) S).degree b = 2)
    (hDegC : (blockGraph (graph s) S).degree c = 2)
    (hLeft : b ∈ (s a).val) (hRight : c ∈ (s d).val) : False := by
  let G := graph s
  have hG := nash_connected (Nat.zero_lt_of_lt a.isLt) α s hne
  have habG := blockGraph_le G S hab
  have hbcG := blockGraph_le G S hbc
  have hcdG := blockGraph_le G S hcd
  have hab1 : G.dist a b = 1 := dist_eq_one_iff_adj.mpr habG
  have hcd1 : G.dist c d = 1 := dist_eq_one_iff_adj.mpr hcdG
  change G.dist a d = 3 at hLength
  have hAC : G.dist a c = 2 := by
    have hup := dist_le (.cons habG (.cons hbcG .nil))
    have htri : G.dist a d ≤ G.dist a c + G.dist c d := hG.dist_triangle
    change G.dist a c ≤ 2 at hup
    omega
  have hBD : G.dist b d = 2 := by
    have hup := dist_le (.cons hbcG (.cons hcdG .nil))
    have htri : G.dist a d ≤ G.dist a b + G.dist b d := hG.dist_triangle
    change G.dist b d ≤ 2 at hup
    omega
  have hac : a ≠ c := by
    intro he
    rw [he, dist_self] at hAC
    omega
  have hdb : d ≠ b := by
    intro he
    rw [he, dist_self] at hBD
    omega
  have hL := nash_block_two_step_pair_bound s α hne hS hab hbc hac hDegB hLeft
    hcd.1 hcd.2.1 hcdG.ne (by simpa using hAC) (by
      change G.dist a d = 2 + G.dist c d
      rw [hLength, hcd1])
  have hR := nash_block_two_step_pair_bound s α hne hS hcd.symm hbc.symm hdb hDegC hRight
    hab.2.1 hab.1 habG.ne.symm (by rw [dist_comm (u := d), dist_self]; simpa using hBD) (by
      change G.dist d a = 2 + G.dist b a
      rw [dist_comm (u := d) (v := a), dist_comm (u := b) (v := a), hLength, hab1])
  have hA : 0 < (blockAttachment (graph s) S a).card := blockAttachment_card_pos a
  have hD : 0 < (blockAttachment (graph s) S d).card := blockAttachment_card_pos d
  omega

/-- The one-sided restrictions from a maximal attachment contradict on a
three-step geodesic when both ends are forced to buy toward the middle. -/
theorem nash_block_no_geodesic_ridge (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj]
    {p a b c d q x : Fin n}
    (hpa : (blockGraph (graph s) S).Adj p a)
    (hab : (blockGraph (graph s) S).Adj a b)
    (hbc : (blockGraph (graph s) S).Adj b c)
    (hcd : (blockGraph (graph s) S).Adj c d)
    (hdq : (blockGraph (graph s) S).Adj d q)
    (hLength : (graph s).dist a d = 3)
    (hA : (blockGraph (graph s) S).degree a = 2)
    (hB : (blockGraph (graph s) S).degree b = 2)
    (hC : (blockGraph (graph s) S).degree c = 2)
    (hD : (blockGraph (graph s) S).degree d = 2)
    (hx : x ∈ S) (hpx : p ≠ x) (hqx : q ≠ x)
    (hL : (graph s).dist b x = 2 + (graph s).dist p x)
    (hR : (graph s).dist c x = 2 + (graph s).dist q x)
    (hMax : ∀ v ∈ S, (blockAttachment (graph s) S v).card ≤
      (blockAttachment (graph s) S x).card) : False := by
  have hbp : b ≠ p := by
    intro he
    rw [he] at hL
    omega
  have hcq : c ≠ q := by
    intro he
    rw [he] at hR
    omega
  have hLeft := nash_block_forces_purchase_away_from_maximum s α hne hS hab.symm
    hpa.symm hbp hA hx hpx hL (hMax a hab.1)
  have hRight := nash_block_forces_purchase_away_from_maximum s α hne hS hcd
    hdq hcq hD hx hqx hR (hMax d hdq.1)
  exact nash_block_no_inward_purchases_on_three_step_path s α hne hS hab hbc hcd
    hLength hB hC hLeft hRight

#print axioms nash_block_forces_purchase_away_from_maximum
#print axioms nash_block_no_inward_purchases_on_three_step_path
#print axioms nash_block_no_geodesic_ridge

end Lax869952Proofs
