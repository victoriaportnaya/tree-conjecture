import Lax869952Proofs.ChainWeights
import Lax869952Proofs.ShortCycleBounds

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}

private theorem dist_eq_length_of_twice_le_girth
    (girth : ∀ {a}, (q : G.Walk a a) → q.IsCycle → 8 ≤ q.length)
    {u v : Fin n} (p : G.Walk u v) (hp : p.IsPath) (hl : p.length ≤ 4) :
    G.dist u v = p.length := by
  have lo := min_path_length_girth_sub_le_dist girth p hp
  rw [min_eq_left (by omega)] at lo
  exact (dist_le p).antisymm lo

private theorem two_step_dist
    (girth : ∀ {a}, (q : G.Walk a a) → q.IsCycle → 8 ≤ q.length)
    {a b c : Fin n} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c) :
    G.dist a c = 2 := by
  let p := Walk.cons hab (Walk.cons hbc Walk.nil)
  have hp : p.IsPath := by simp [p, Walk.isPath_def, hab.ne, hbc.ne, hac]
  exact dist_eq_length_of_twice_le_girth girth p hp (by change 2 ≤ 4; decide)

private theorem two_step_middle_unique
    (girth : ∀ {a}, (q : G.Walk a a) → q.IsCycle → 8 ≤ q.length)
    {a b c d : Fin n} (hac : a ≠ c)
    (hab : G.Adj a b) (hbc : G.Adj b c) (had : G.Adj a d) (hdc : G.Adj d c) : b = d := by
  let p := Walk.cons hab (Walk.cons hbc Walk.nil)
  let q := Walk.cons had (Walk.cons hdc Walk.nil)
  have hp : p.IsPath := by simp [p, Walk.isPath_def, hab.ne, hbc.ne, hac]
  have hq : q.IsPath := by simp [q, Walk.isPath_def, had.ne, hdc.ne, hac]
  have same : p = q := by
    by_contra different
    have bad := girth_le_path_length_add_length_of_ne girth p q hp hq different
    change 8 ≤ 2 + 2 at bad
    omega
  exact congrArg (fun r : G.Walk a c => r.getVert 1) same

/-- Every other branch at the new endpoint supplies at least two distinct
improved block attachments when the original edge skips a degree-two vertex. -/
theorem nash_block_two_step_two_layer_bound (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj]
    (girth : ∀ {a}, (q : (graph s).Walk a a) → q.IsCycle → 8 ≤ q.length)
    {u v w : Fin n} (huv : (blockGraph (graph s) S).Adj u v)
    (hvw : (blockGraph (graph s) S).Adj v w) (huw : u ≠ w)
    (hDegree : (blockGraph (graph s) S).degree v = 2) (hBuy : v ∈ (s u).val) :
    (blockAttachment (graph s) S w).card +
      2 * ((blockGraph (graph s) S).degree w - 1) ≤
      (blockAttachment (graph s) S v).card := by
  let G := graph s
  let H := blockGraph G S
  let A := (H.neighborFinset w).erase v
  have UV : G.Adj u v := blockGraph_le G S huv
  have VW : G.Adj v w := blockGraph_le G S hvw
  have dUW := two_step_dist girth UV VW huw
  have branch (y : A) : H.Adj w y.val := by
    exact (H.mem_neighborFinset w _).mp (Finset.mem_of_mem_erase y.property)
  have branch_ne (y : A) : y.val ≠ v := Finset.ne_of_mem_erase y.property
  have branchG (y : A) : G.Adj w y.val := blockGraph_le G S (branch y)
  have branch_ne_u (y : A) : y.val ≠ u := by
    intro h
    have d := dist_eq_one_iff_adj.mpr (branchG y).symm
    rw [h, dUW] at d
    omega
  have existsNext (y : A) : ∃ z, H.Adj y.val z ∧ w ≠ z := by
    obtain ⟨a, b, ha, hb, hab⟩ := hS.twoConnected.exists_two_neighbors (branch y).2.1
    by_cases h : w = a
    · exact ⟨b, hb, h.trans_ne hab⟩
    · exact ⟨a, ha, h⟩
  choose next adjacent distinct using existsNext
  have dNext (y : A) : G.dist w (next y) = 2 :=
    two_step_dist girth (branchG y) (blockGraph_le G S (adjacent y)) (distinct y)
  have next_ne_v (y : A) : v ≠ next y := by
    intro h
    have d := dist_eq_one_iff_adj.mpr VW.symm
    rw [h, dNext y] at d
    omega
  have next_ne_u (y : A) : u ≠ next y := by
    intro h
    exact branch_ne y (two_step_middle_unique girth (distinct y) (branchG y)
      (blockGraph_le G S (adjacent y)) VW.symm (h ▸ UV.symm))
  have nextInj : Function.Injective next := by
    intro y y' h
    apply Subtype.ext
    exact two_step_middle_unique girth (distinct y) (branchG y)
      (blockGraph_le G S (adjacent y)) (branchG y')
      (blockGraph_le G S (h.symm ▸ adjacent y'))
  let B := A.attach.image next
  have disjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hzB
    have d := dist_eq_one_iff_adj.mpr (branchG ⟨next y, hzA⟩)
    change G.dist w (next y) = 1 at d
    rw [dNext y] at d
    omega
  have wOutside : w ∉ A ∪ B := by
    intro h
    rcases Finset.mem_union.mp h with hw | hw
    · exact (branchG ⟨w, hw⟩).ne rfl
    · obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hw
      exact distinct y hy.symm
  have cardA : A.card = H.degree w - 1 := by
    have hv := (H.mem_neighborFinset w v).mpr hvw.symm
    change ((H.neighborFinset w).erase v).card = _
    rw [Finset.card_erase_of_mem hv, card_neighborFinset_eq_degree]
  have cardB : B.card = A.card := by
    rw [Finset.card_image_of_injective A.attach nextInj, Finset.card_attach]
  have three (y : A) : G.dist u y.val = 3 := by
    let p := Walk.cons UV (Walk.cons VW (Walk.cons (branchG y) Walk.nil))
    have hp : p.IsPath := by
      simp [p, Walk.isPath_def, UV.ne, VW.ne, (branchG y).ne, huw,
        (branch_ne_u y).symm, (branch_ne y).symm]
    exact dist_eq_length_of_twice_le_girth girth p hp (by change 3 ≤ 4; decide)
  have four (y : A) : G.dist u (next y) = 4 := by
    have YZ := blockGraph_le G S (adjacent y)
    let p := Walk.cons UV (Walk.cons VW (Walk.cons (branchG y) (Walk.cons YZ Walk.nil)))
    have hp : p.IsPath := by
      simp [p, Walk.isPath_def, UV.ne, VW.ne, (branchG y).ne, YZ.ne, huw,
        (branch_ne_u y).symm, (branch_ne y).symm, next_ne_u y, next_ne_v y, distinct y]
    exact dist_eq_length_of_twice_le_girth girth p hp (by change 4 ≤ 4; decide)
  let T := insert w (A ∪ B)
  have sub : T ⊆ S := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hvw.2.1
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (branch ⟨z, hz⟩).2.1
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    exact (adjacent y).2.1
  have distances (z : Fin n) (hz : z ∈ T) : G.dist u z = 2 + G.dist w z := by
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simpa using dUW
    rcases Finset.mem_union.mp hz with hz | hz
    · let y : A := ⟨z, hz⟩
      rw [show z = y.val from rfl, three y, dist_eq_one_iff_adj.mpr (branchG y)]
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    rw [four y, dNext y]
  have hSwap := nash_block_two_step_sum_bound s α hne hS huv hvw huw hDegree hBuy sub distances
  have lower : (A ∪ B).card ≤ ∑ z ∈ A ∪ B, (blockAttachment G S z).card := by
    calc
      (A ∪ B).card = ∑ _ ∈ A ∪ B, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun z _ => blockAttachment_card_pos z
  rw [show T = insert w (A ∪ B) from rfl, Finset.sum_insert wOutside] at hSwap
  rw [Finset.card_union_of_disjoint disjoint, cardB, cardA] at lower
  simp only [G, H] at lower
  omega

#print axioms nash_block_two_step_two_layer_bound

/-- At most one vertex of an attachment belongs to the block itself. -/
theorem blockAttachment_card_le_complement_add_one (v : Fin n) :
    (blockAttachment G S v).card ≤ n - S.card + 1 := by
  have sub : blockAttachment G S v ⊆ insert v (Finset.univ \ S) := by
    intro z hz
    by_cases hzS : z ∈ S
    · obtain ⟨p, hp⟩ := mem_blockAttachment.mp hz
      exact Finset.mem_insert.mpr (Or.inl (hp z p.start_mem_support hzS))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzS⟩))
  refine (Finset.card_le_card sub).trans (Finset.card_insert_le _ _ |>.trans ?_)
  simp [Finset.card_sdiff_of_subset (Finset.subset_univ S)]

/-- A three-edge chain with two internal degree-two vertices needs outside
vertices in proportion to the smaller degree of its ends. -/
theorem nash_block_three_edge_chain_extra_budget (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj]
    (girth : ∀ {u}, (q : (graph s).Walk u u) → q.IsCycle → 8 ≤ q.length)
    {a b c d : Fin n} (hab : (blockGraph (graph s) S).Adj a b)
    (hbc : (blockGraph (graph s) S).Adj b c) (hcd : (blockGraph (graph s) S).Adj c d)
    (hac : a ≠ c) (hbd : b ≠ d)
    (hDegB : (blockGraph (graph s) S).degree b = 2)
    (hDegC : (blockGraph (graph s) S).degree c = 2) :
    2 * (min ((blockGraph (graph s) S).degree a) ((blockGraph (graph s) S).degree d) - 1)
      ≤ n - S.card := by
  have weight (v : Fin n) : 0 < (blockAttachment (graph s) S v).card :=
    blockAttachment_card_pos v
  rcases blockGraph_le (graph s) S hbc with hBuy | hBuy
  · have lower := nash_block_two_step_two_layer_bound s α hne hS girth hbc hcd hbd hDegC hBuy
    have upper := blockAttachment_card_le_complement_add_one (G := graph s) (S := S) c
    have h := weight d
    omega
  · have lower := nash_block_two_step_two_layer_bound s α hne hS girth hbc.symm hab.symm
      hac.symm hDegB hBuy
    have upper := blockAttachment_card_le_complement_add_one (G := graph s) (S := S) b
    have h := weight a
    omega

/-- A block missing at most three vertices cannot have a three-edge chain
with degree-two interior and both ends of degree at least three. -/
theorem nash_block_no_three_edge_branch_chain_of_small_gap (s : Profile n) (α : ℝ≥0)
    (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    (hGap : n - S.card ≤ 3)
    {a b c d : Fin n} (hab : (blockGraph (graph s) S).Adj a b)
    (hbc : (blockGraph (graph s) S).Adj b c) (hcd : (blockGraph (graph s) S).Adj c d)
    (hac : a ≠ c) (hbd : b ≠ d)
    (hDegA : 3 ≤ (blockGraph (graph s) S).degree a)
    (hDegB : (blockGraph (graph s) S).degree b = 2)
    (hDegC : (blockGraph (graph s) S).degree c = 2)
    (hDegD : 3 ≤ (blockGraph (graph s) S).degree d) : False := by
  have lower := nash_block_three_edge_chain_extra_budget s α hne hS
    (nash_cycle_length_ge_eight s α hα hne) hab hbc hcd hac hbd hDegB hDegC
  omega

#print axioms nash_block_no_three_edge_branch_chain_of_small_gap

end Lax869952Proofs
