import TreeConjecture.BlockParentPurchases
import TreeConjecture.TreeDistanceBudget

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Function

variable {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)} {r v x : Fin n}

private theorem ShortestParents.branch_route_with_ancestors (T : ShortestParents G r)
    (hx : x ∈ T.branch v) :
    ∃ p : T.tree.Walk x v, p.length = G.dist r x - G.dist r v ∧
      ∀ y ∈ p.support, x ∈ T.branch y ∧ G.dist r v ≤ G.dist r y := by
  classical
  obtain ⟨k, hk, he⟩ : ∃ k ≤ G.dist r x, T.parent^[k] x = v := by
    simpa [ShortestParents.branch] using hx
  obtain ⟨p, hp, hSupport⟩ := T.route_to_iterate_support k x hk
  have hv := T.depth_iterate k x
  rw [he] at hv
  refine ⟨p.copy rfl he, by rw [Walk.length_copy, hp]; omega, ?_⟩
  intro y hy
  rw [Walk.support_copy] at hy
  obtain ⟨j, hj, hEq⟩ := hSupport y hy
  have hDepth := T.depth_iterate j x
  rw [hEq] at hDepth
  have hBranch : x ∈ T.branch y := by
    simpa only [ShortestParents.branch, Finset.mem_filter, Finset.mem_univ, true_and] using
      (show ∃ l ≤ G.dist r x, T.parent^[l] x = y from ⟨j, hj.trans hk, hEq⟩)
  exact ⟨hBranch, by omega⟩

/-- Attached vertices lie in the corresponding branch of any shortest-path
tree rooted inside the block. -/
theorem IsBiconnectedBlock.blockAttachment_subset_branch (hS : IsBiconnectedBlock G S)
    (hG : G.Connected) (hr : r ∈ S) (hv : v ∈ S) (T : ShortestParents G r) :
    blockAttachment G S v ⊆ T.branch v := by
  classical
  intro x hx
  obtain ⟨q, hq⟩ := mem_blockAttachment.mp hx
  obtain ⟨p, _, hSupport⟩ := T.route_to_iterate_support (G.dist r x) x le_rfl
  have hz : G.dist r (T.parent^[G.dist r x] x) = 0 := by simp [T.depth_iterate]
  have he := (hG.dist_eq_zero_iff.mp hz).symm
  let w := (p.copy rfl he).mapLe T.tree_le
  obtain ⟨y, hy, t, ht, hFirst⟩ := exists_first_entry_walk w hr
  have hEq := hS.first_entry_unique hv hy q t hq hFirst
  have hMem : y ∈ w.support := ht t.end_mem_support
  simp only [w, Walk.support_mapLe_eq_support, Walk.support_copy] at hMem
  simpa [ShortestParents.branch, hEq] using hSupport y hMem

/-- A block attachment contains exactly the vertices in the branch that
do not belong to any of its child branches rooted inside the block. -/
theorem IsBiconnectedBlock.mem_blockAttachment_iff_branch (hS : IsBiconnectedBlock G S)
    (hG : G.Connected) (hr : r ∈ S) (hv : v ∈ S) (T : ShortestParents G r) :
    x ∈ blockAttachment G S v ↔ x ∈ T.branch v ∧
      ∀ {w}, (blockGraph G S).Adj v w → T.parent w = v → x ∉ T.branch w := by
  constructor
  · intro hx
    have hxv := hS.blockAttachment_subset_branch hG hr hv T hx
    refine ⟨hxv, ?_⟩
    intro w hw hParent hxw
    have hwRoot : w ≠ r := by
      intro he
      subst w
      exact hw.ne (hParent.symm.trans T.parent_root)
    have hDepth := T.parent_depth hwRoot
    rw [hParent] at hDepth
    have hV := T.branch_geodesic hxv hG
    have hW := T.branch_geodesic hxw hG
    have hMin := (hS.mem_blockAttachment_iff_nearest hG hv).mp hx w hw.2.1
    rw [dist_comm (u := x) (v := v), dist_comm (u := x) (v := w)] at hMin
    omega
  · rintro ⟨hx, hNoChild⟩
    obtain ⟨p, hp, hSupport⟩ := T.branch_route_with_ancestors hx
    let P := p.mapLe T.tree_le
    obtain ⟨y, hy, q, hq, hFirst⟩ := exists_first_entry_walk P hv
    by_cases he : y = v
    · subst y
      exact mem_blockAttachment.mpr ⟨q, hFirst⟩
    · have hyP : y ∈ p.support := by simpa only [P, Walk.support_mapLe_eq_support] using hq q.end_mem_support
      let tail := p.dropUntil y hyP
      have hNonempty := tail.not_nil_of_ne he
      let w := tail.penultimate
      have hwTail : w ∈ tail.support := tail.getVert_mem_support _
      have hwP : w ∈ p.support := p.support_dropUntil_subset_support hyP hwTail
      obtain ⟨hwBranch, hwDepth⟩ := hSupport w hwP
      have hwAdj : T.tree.Adj w v := tail.adj_penultimate hNonempty
      have hLen : p.length = T.tree.dist x v := by
        rw [dist_comm (u := x), T.tree_dist_of_mem_branch hG hx]
        exact hp
      have hTail := p.isPath_of_length_eq_dist hLen
      have hTail' : (tail.mapLe T.tree_le).IsPath := (hTail.dropUntil hyP).mapLe _
      have hwS := hS.path_support_subset hy hv (tail.mapLe T.tree_le) hTail' w
        (by simpa only [Walk.support_mapLe_eq_support] using hwTail)
      have hwParent : T.parent w = v := by
        rcases hwAdj.2 with h | h
        · exact h
        · have hvNe : v ≠ r := by
            intro e
            subst v
            exact hwAdj.ne (h.symm.trans T.parent_root)
          have hd := T.parent_depth hvNe
          rw [h] at hd
          omega
      exact (hNoChild ⟨hv, hwS, (T.tree_le hwAdj).symm⟩ hwParent hwBranch).elim

theorem eq_neighbors_of_degree_two {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {a b c : Fin n} (hb : H.Adj a b) (hc : H.Adj a c) (hNe : b ≠ c)
    (hDegree : H.degree a = 2) :
    ({b, c} : Finset (Fin n)) = H.neighborFinset a := by
  have hSub : {b, c} ⊆ H.neighborFinset a := by
    intro v hv
    rcases (show v = b ∨ v = c by simpa using hv) with rfl | rfl
    · exact (H.mem_neighborFinset _ _).mpr hb
    · exact (H.mem_neighborFinset _ _).mpr hc
  apply Finset.eq_of_subset_of_card_le hSub
  rw [card_neighborFinset_eq_degree, hDegree]
  simp [hNe]

/-- With degree two and a parent inside the block, the other neighbor is
the only possible child inside the block. -/
theorem IsBiconnectedBlock.blockAttachment_eq_sdiff_of_degree_two
    (hS : IsBiconnectedBlock G S) (hG : G.Connected) (hr : r ∈ S)
    (T : ShortestParents G r) [DecidableRel (blockGraph G S).Adj]
    {w : Fin n} (hParent : (blockGraph G S).Adj v (T.parent v))
    (hOther : (blockGraph G S).Adj v w) (hNe : T.parent v ≠ w)
    (hDegree : (blockGraph G S).degree v = 2) :
    blockAttachment G S v =
      T.branch v \ (if T.parent w = v then T.branch w else ∅) := by
  classical
  let H := blockGraph G S
  have hNeighbors := eq_neighbors_of_degree_two hParent hOther hNe hDegree
  have hNotChild : T.parent (T.parent v) ≠ v := by
    have hvRoot : v ≠ r := by
      intro he
      subst v
      exact hParent.ne T.parent_root.symm
    have hd := T.parent_depth hvRoot
    have hdd := T.depth_parent (T.parent v)
    intro he
    rw [he] at hdd
    omega
  ext a
  rw [hS.mem_blockAttachment_iff_branch hG hr hParent.1 T, Finset.mem_sdiff]
  apply and_congr_right
  intro _
  constructor
  · intro h
    by_cases hw : T.parent w = v
    · rw [if_pos hw]
      exact h hOther hw
    · simp [hw]
  · intro h b hb hChild
    have hMem := (H.mem_neighborFinset _ _).mpr hb
    rw [← hNeighbors] at hMem
    rcases (show b = T.parent v ∨ b = w by simpa using hMem) with rfl | rfl
    · exact (hNotChild hChild).elim
    · simpa only [if_pos hChild] using h

#print axioms IsBiconnectedBlock.mem_blockAttachment_iff_branch
#print axioms IsBiconnectedBlock.blockAttachment_eq_sdiff_of_degree_two

end TreeConjecture
