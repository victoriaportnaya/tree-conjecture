import TreeConjecture.TwoLayerWeights
import TreeConjecture.EarPruning

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped NNReal

/-- At α > n, every biconnected block has a vertex of block degree at least
three. In particular, a block cannot consist of a single cycle. -/
theorem nash_block_exists_degree_ge_three {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    {S : Finset (Fin n)} (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj] :
    ∃ x ∈ S, 3 ≤ (blockGraph (graph s) S).degree x := by
  by_contra noBranch
  let G := graph s
  let H := blockGraph G S
  let weight (v : Fin n) := (blockAttachment G S v).card
  have degreeTwo {v : Fin n} (hv : v ∈ S) : H.degree v = 2 := by
    have low := hS.two_le_degree hv
    have high : ¬ 3 ≤ H.degree v := fun h => noBranch ⟨v, hv, h⟩
    change 2 ≤ H.degree v at low
    omega
  have girth {v : Fin n} (p : G.Walk v v) (hp : p.IsCycle) : 8 ≤ p.length :=
    nash_cycle_length_ge_eight s α hα hne p hp
  have nonempty : S.Nonempty := Finset.card_pos.mp (by have := hS.twoConnected.card_ge_three; omega)
  obtain ⟨x, hx, minimum⟩ := Finset.exists_min_image S weight nonempty
  have noIncoming {y : Fin n} (hyx : H.Adj y x) (hBuy : x ∈ (s y).val) : False := by
    obtain ⟨a, b, hxa, hxb, hab⟩ := hS.twoConnected.exists_two_neighbors hx
    have other : ∃ z, H.Adj x z ∧ y ≠ z := by
      by_cases h : y = a
      · exact ⟨b, hxb, h.trans_ne hab⟩
      · exact ⟨a, hxa, h⟩
    obtain ⟨z, hxz, hyz⟩ := other
    have bound := nash_block_two_step_two_layer_bound s α hne hS girth hyx hxz hyz
      (degreeTwo hx) hBuy
    change weight z + 2 * (H.degree z - 1) ≤ weight x at bound
    have hmin := minimum z hxz.2.1
    have hz := hS.two_le_degree hxz.2.1
    change 2 ≤ H.degree z at hz
    omega
  obtain ⟨p, hp⟩ := hS.twoConnected.exists_cycle_at hx
  have hLength : 8 ≤ p.length := by
    simpa only [Walk.length_mapLe] using girth (p.mapLe (blockGraph_le G S)) (hp.mapLe _)
  have first : H.Adj x (p.getVert 1) := by
    simpa only [Walk.getVert_zero] using p.adj_getVert_succ (i := 0) (by omega)
  have hFirstBuy : p.getVert 1 ∈ (s x).val := by
    rcases blockGraph_le G S first with bought | reverse
    · exact bought
    · exact (noIncoming first.symm reverse).elim
  let q := p.dropLast
  have hQLength : q.length = p.length - 1 := by simp [q]
  have hQPath : q.IsPath := hp.isPath_dropLast
  have hQD (j : ℕ) (_ : 0 < j) (hj : j < q.length) : H.degree (q.getVert j) = 2 :=
    degreeTwo (q.adj_getVert_succ hj).1
  have hQBuy : q.getVert 1 ∈ (s (q.getVert 0)).val := by
    rw [Walk.getVert_zero, Walk.getVert_dropLast (by omega)]
    exact hFirstBuy
  let i := p.length - 3
  have hi : i + 3 = p.length := by dsimp [i]; omega
  have hForward := nash_block_chain_purchase_propagates s α hne hS girth q hQPath hQD
    (i := 0) (j := i) (by omega) (by omega) hQBuy
  rw [Walk.getVert_dropLast (by omega), Walk.getVert_dropLast (by omega)] at hForward
  have hab := p.adj_getVert_succ (i := i) (by omega)
  have hbc := p.adj_getVert_succ (i := i + 1) (by omega)
  have last : H.Adj (p.getVert (i + 2)) x := by
    simpa only [Nat.add_assoc, hi, Walk.getVert_length] using
      p.adj_getVert_succ (i := i + 2) (by omega)
  have d : G.dist (p.getVert i) x = 3 := by
    let r := (p.drop i).mapLe (blockGraph_le G S)
    have hr : r.IsPath := (hp.isPath_drop (by omega)).mapLe _
    have hRLength : r.length = 3 := by simp [r, Walk.drop_length]; omega
    exact dist_eq_three_of_girth_eight girth r hr hRLength
  rcases blockGraph_le G S last with towards | away
  · exact noIncoming last towards
  · exact nash_block_no_inward_purchases_on_three_step_path s α hne hS hab hbc last d
      (degreeTwo hbc.1) (degreeTwo last.1) hForward away

#print axioms nash_block_exists_degree_ge_three

private theorem block_walk_support {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    {x y : Fin n} (p : (blockGraph G S).Walk x y) (hx : x ∈ S) :
    ∀ v ∈ p.support, v ∈ S := by
  induction p with
  | nil => simpa using hx
  | cons h p ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h.1
    · exact ih h.2.1 v hv

/-- The cycle through a branch vertex and an incident ear give three
distinct cycles on the same three pairwise internally disjoint paths.
The sum of their lengths bounds the size of the block from below. -/
theorem block_card_girth_bound_of_degree_ge_three {n g : ℕ} {G : SimpleGraph (Fin n)}
    {S : Finset (Fin n)} (hS : IsBiconnectedBlock G S)
    [DecidableRel (blockGraph G S).Adj]
    (girth : ∀ {u}, (p : G.Walk u u) → p.IsCycle → g ≤ p.length)
    {x : Fin n} (hx : x ∈ S) (hDegree : 3 ≤ (blockGraph G S).degree x) :
    3 * g ≤ 2 * (S.card + 1) := by
  let H := blockGraph G S
  obtain ⟨p₀, hp₀⟩ := hS.twoConnected.exists_cycle_at hx
  let p := p₀.mapLe (blockGraph_le G S)
  have hp : p.IsCycle := hp₀.mapLe _
  let C := p.tail.support.toFinset
  have support : p.support = x :: p.tail.support := by
    have eq := congrArg Walk.support (p.cons_tail_eq hp.not_nil)
    simpa only [Walk.support_cons] using eq.symm
  have cycleMem (v : Fin n) : v ∈ C ↔ v ∈ p.support := by
    change v ∈ p.tail.support.toFinset ↔ v ∈ p.support
    rw [List.mem_toFinset, support, List.mem_cons]
    exact ⟨Or.inr, fun h => h.elim (fun h => h.symm ▸ p.tail.end_mem_support) id⟩
  have cycleCard : C.card = p.length := by
    change p.tail.support.toFinset.card = p.length
    rw [List.toFinset_card_of_nodup hp.isPath_tail.support_nodup, Walk.length_support]
    exact Walk.length_tail_add_one hp.not_nil
  have cycleSub : C ⊆ S := by
    intro v hv
    have h := (cycleMem v).mp hv
    rw [show p = p₀.mapLe (blockGraph_le G S) from rfl, Walk.support_mapLe_eq_support] at h
    exact block_walk_support p₀ hx v h
  let N := H.neighborFinset x
  have many : 3 ≤ N.card := by simpa [N, H, card_neighborFinset_eq_degree] using hDegree
  have findOther : ∃ y ∈ N, y ≠ p.snd ∧ y ≠ p.tail.penultimate := by
    by_contra! h
    have sub : N ⊆ {p.snd, p.tail.penultimate} := by
      intro y hy
      by_cases equal : y = p.snd
      · simp [equal]
      · simp [h y hy equal]
    have c := Finset.card_le_card sub
    have upper := Finset.card_insert_le p.snd {p.tail.penultimate}
    rw [Finset.card_singleton] at upper
    omega
  obtain ⟨y, hy, hy₁, hy₂⟩ := findOther
  have hXY := (H.mem_neighborFinset x y).mp hy
  have unused : s(x, y) ∉ p.edges := by
    intro he
    rw [← p.cons_tail_eq hp.not_nil, Walk.edges_cons, List.mem_cons] at he
    exact he.elim (fun h => hy₁ (Sym2.congr_right.mp h))
      (fun h => hy₂ (hp.isPath_tail.eq_penultimate_of_mem_edges h))
  have hLen := girth p hp
  have minCycle := hp.three_le_length
  obtain ⟨z, hz, hzX, t, ht, hTside, hEntry⟩ :=
    hS.twoConnected.exists_ear_with_first_edge cycleSub (by omega : 2 ≤ C.card)
      hXY.2.1 (blockGraph_le G S hXY)
  let ear := Walk.cons (blockGraph_le G S hXY) t
  let left := p.takeUntil z ((cycleMem z).mp hz)
  let right := p.dropUntil z ((cycleMem z).mp hz)
  have split : left.append right = p := p.take_spec ((cycleMem z).mp hz)
  have leftPath : left.IsPath := hp.isPath_takeUntil _
  have rightPath : right.IsPath := (split.symm ▸ hp).isPath_of_append_right (Walk.not_nil_of_ne hzX.symm)
  have firstEdge : s(x, y) ∈ ear.edges := by simp [ear]
  have leftNe : ear ≠ left := by
    intro e
    have here : s(x, y) ∈ left.edges := e ▸ firstEdge
    exact unused (p.edges_takeUntil_subset_edges ((cycleMem z).mp hz) here)
  have rightNe : ear ≠ right.reverse := by
    intro e
    have here := e ▸ firstEdge
    rw [Walk.edges_reverse, List.mem_reverse] at here
    exact unused (p.edges_dropUntil_subset_edges ((cycleMem z).mp hz) here)
  have firstCycle := girth_le_path_length_add_length_of_ne girth ear left ht leftPath leftNe
  have secondCycle := girth_le_path_length_add_length_of_ne girth ear right.reverse ht rightPath.reverse rightNe
  rw [Walk.length_reverse] at secondCycle
  have lenSplit := congrArg Walk.length split
  rw [Walk.length_append] at lenSplit
  have earLength : ear.length = t.length + 1 := rfl
  let outside := t.support.toFinset.erase z
  have outsideCard : outside.card = t.length := by
    have tPath : t.IsPath := (Walk.cons_isPath_iff _ _).mp ht |>.1
    change (t.support.toFinset.erase z).card = _
    rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr t.end_mem_support),
      List.toFinset_card_of_nodup tPath.support_nodup, Walk.length_support]
    omega
  have apart : Disjoint C outside := by
    apply Finset.disjoint_left.mpr
    intro v hv hOutside
    obtain ⟨hNe, hmem⟩ := Finset.mem_erase.mp hOutside
    exact hNe (hEntry v (List.mem_toFinset.mp hmem) hv)
  have sub : C ∪ outside ⊆ S := by
    intro v hv
    exact (Finset.mem_union.mp hv).elim (fun hc => cycleSub hc)
      (fun ho => hTside v (List.mem_toFinset.mp (Finset.mem_of_mem_erase ho)))
  have total := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint apart, cycleCard, outsideCard] at total
  omega

/-- The Tree Conjecture for at most ten players, using the structural
block bounds and no finite external computation. -/
theorem nash_tree_of_le_ten_at_n {n : ℕ} (hn : 0 < n) (hsmall : n ≤ 10)
    (s : Profile n) (α : ℝ≥0) (hα : (n : ℝ≥0) < α)
    (hne : IsNashEquilibrium α s) : (graph s).IsTree := by
  classical
  by_contra hNotTree
  obtain ⟨S, hS, _, _⟩ := nash_largest_block_of_not_tree s α hn hne hNotTree
  obtain ⟨x, hx, hDegree⟩ := nash_block_exists_degree_ge_three s α hα hne hS
  have large := block_card_girth_bound_of_degree_ge_three hS
    (nash_cycle_length_ge_eight s α hα hne) hx hDegree
  have upper : S.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ S)
  omega

#print axioms nash_tree_of_le_ten_at_n

end TreeConjecture
