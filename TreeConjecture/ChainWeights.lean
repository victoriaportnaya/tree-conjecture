import TreeConjecture.ThreadGeometry

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ} {S : Finset (Fin n)}

/-- The forward neighbourhood of the new endpoint contributes to the gain
when a buyer replaces the old edge across a degree-two vertex. -/
theorem nash_block_two_step_neighbor_sum_bound (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj]
    (girth : ∀ {a}, (q : (graph s).Walk a a) → q.IsCycle → 8 ≤ q.length)
    {u v w : Fin n} (huv : (blockGraph (graph s) S).Adj u v)
    (hvw : (blockGraph (graph s) S).Adj v w) (huw : u ≠ w)
    (hDegree : (blockGraph (graph s) S).degree v = 2) (hBuy : v ∈ (s u).val)
    (hTwo : (graph s).dist u w = 2) :
    (∑ y ∈ insert w (((blockGraph (graph s) S).neighborFinset w).erase v),
      (blockAttachment (graph s) S y).card) ≤ (blockAttachment (graph s) S v).card := by
  let H := blockGraph (graph s) S
  let T := insert w ((H.neighborFinset w).erase v)
  have hNeighbor {y : Fin n} (h : y ∈ (H.neighborFinset w).erase v) : H.Adj w y :=
    (H.mem_neighborFinset w y).mp (Finset.mem_of_mem_erase h)
  apply nash_block_two_step_sum_bound s α hne hS huv hvw huw hDegree hBuy (T := T)
  · intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hvw.2.1
    · exact (hNeighbor hy).2.1
  · intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simpa using hTwo
    have hwy := hNeighbor hy
    have hyv := Finset.ne_of_mem_erase hy
    have h₁ := blockGraph_le (graph s) S huv
    have h₂ := blockGraph_le (graph s) S hvw
    have h₃ := blockGraph_le (graph s) S hwy
    have hOne := dist_eq_one_iff_adj.mpr h₃
    have huy : u ≠ y := by
      intro he
      have hyw := dist_eq_one_iff_adj.mpr h₃.symm
      rw [he] at hTwo
      omega
    let p := Walk.cons h₁ (Walk.cons h₂ (Walk.cons h₃ Walk.nil))
    have hPath : p.IsPath := by
      simp [p, Walk.isPath_def, h₁.ne, h₂.ne, h₃.ne, huw, huy, hyv.symm]
    rw [dist_eq_three_of_girth_eight girth p hPath rfl, hOne]

/-- The skipped attachment must contain at least as many vertices as the
block degree of the new endpoint. -/
theorem nash_block_two_step_attachment_ge_degree (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj]
    (girth : ∀ {a}, (q : (graph s).Walk a a) → q.IsCycle → 8 ≤ q.length)
    {u v w : Fin n} (huv : (blockGraph (graph s) S).Adj u v)
    (hvw : (blockGraph (graph s) S).Adj v w) (huw : u ≠ w)
    (hDegree : (blockGraph (graph s) S).degree v = 2) (hBuy : v ∈ (s u).val)
    (hTwo : (graph s).dist u w = 2) :
    (blockGraph (graph s) S).degree w ≤ (blockAttachment (graph s) S v).card := by
  let H := blockGraph (graph s) S
  let T := insert w ((H.neighborFinset w).erase v)
  have hv : v ∈ H.neighborFinset w := (H.mem_neighborFinset w v).mpr hvw.symm
  have hw : w ∉ (H.neighborFinset w).erase v := by simp
  have hCard : T.card = H.degree w := by
    have hPositive := Finset.card_pos.mpr (show (H.neighborFinset w).Nonempty from ⟨v, hv⟩)
    change (insert w ((H.neighborFinset w).erase v)).card = H.degree w
    rw [Finset.card_insert_of_notMem hw, Finset.card_erase_of_mem hv]
    rw [← card_neighborFinset_eq_degree]
    omega
  have hSum : T.card ≤ ∑ y ∈ T, (blockAttachment (graph s) S y).card := by
    calc
      T.card = ∑ _ ∈ T, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun y _ => blockAttachment_card_pos y
  exact hCard ▸ hSum.trans
    (nash_block_two_step_neighbor_sum_bound s α hne hS girth huv hvw huw hDegree hBuy hTwo)

/-- The two inward purchases at the ends of a four-edge geodesic are
incompatible when each skips a degree-two vertex. -/
theorem nash_block_no_inward_purchases_on_four_step_path (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj]
    {a b c d e : Fin n}
    (hab : (blockGraph (graph s) S).Adj a b) (hbc : (blockGraph (graph s) S).Adj b c)
    (hcd : (blockGraph (graph s) S).Adj c d) (hde : (blockGraph (graph s) S).Adj d e)
    (hLength : (graph s).dist a e = 4)
    (hDegB : (blockGraph (graph s) S).degree b = 2)
    (hDegD : (blockGraph (graph s) S).degree d = 2)
    (hLeft : b ∈ (s a).val) (hRight : d ∈ (s e).val) : False := by
  have hG := nash_connected (Nat.zero_lt_of_lt a.isLt) α s hne
  have ab := blockGraph_le (graph s) S hab
  have bc := blockGraph_le (graph s) S hbc
  have cd := blockGraph_le (graph s) S hcd
  have de := blockGraph_le (graph s) S hde
  have ab1 := dist_eq_one_iff_adj.mpr ab
  have bc1 := dist_eq_one_iff_adj.mpr bc.symm
  have cd1 := dist_eq_one_iff_adj.mpr cd
  have de1 := dist_eq_one_iff_adj.mpr de
  have hAD : (graph s).dist a d = 3 := by
    have hUpper : (graph s).dist a d ≤ 3 :=
      dist_le (.cons ab (.cons bc (.cons cd .nil)))
    have hTri : (graph s).dist a e ≤ (graph s).dist a d + (graph s).dist d e :=
      hG.dist_triangle
    omega
  have hEB : (graph s).dist e b = 3 := by
    have hUpper : (graph s).dist e b ≤ 3 :=
      dist_le (.cons de.symm (.cons cd.symm (.cons bc.symm .nil)))
    have hTri : (graph s).dist a e ≤ (graph s).dist a b + (graph s).dist b e :=
      hG.dist_triangle
    rw [dist_comm (u := b) (v := e)] at hTri
    omega
  have hAC : (graph s).dist a c = 2 := by
    have hUpper : (graph s).dist a c ≤ 2 := dist_le (.cons ab (.cons bc .nil))
    have hTri : (graph s).dist a d ≤ (graph s).dist a c + (graph s).dist c d :=
      hG.dist_triangle
    omega
  have hEC : (graph s).dist e c = 2 := by
    have hUpper : (graph s).dist e c ≤ 2 := dist_le (.cons de.symm (.cons cd.symm .nil))
    have hTri : (graph s).dist e b ≤ (graph s).dist e c + (graph s).dist c b :=
      hG.dist_triangle
    omega
  have hac : a ≠ c := by
    intro he
    rw [he, dist_self] at hAC
    omega
  have hec : e ≠ c := by
    intro he
    rw [he, dist_self] at hEC
    omega
  have left := nash_block_two_step_pair_bound s α hne hS hab hbc hac hDegB hLeft
    hcd.1 hcd.2.1 cd.ne (by simpa using hAC) (by rw [hAD, cd1])
  have right := nash_block_two_step_pair_bound s α hne hS hde.symm hcd.symm hec hDegD hRight
    hbc.2.1 hbc.1 bc.symm.ne (by simpa using hEC) (by rw [hEB, bc1])
  have positive : 0 < (blockAttachment (graph s) S c).card := blockAttachment_card_pos c
  omega

#print axioms nash_block_two_step_sum_bound
#print axioms nash_block_two_step_neighbor_sum_bound
#print axioms nash_block_two_step_attachment_ge_degree
#print axioms nash_block_no_inward_purchases_on_four_step_path

/-- Farther along a degree-two path, every purchase at separation two or
more from a forward purchase must also be forward. -/
theorem nash_block_chain_purchase_propagates (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj]
    (girth : ∀ {a}, (q : (graph s).Walk a a) → q.IsCycle → 8 ≤ q.length)
    {A B : Fin n} (p : (blockGraph (graph s) S).Walk A B) (hPath : p.IsPath)
    (hDegree : ∀ i, 0 < i → i < p.length → (blockGraph (graph s) S).degree (p.getVert i) = 2)
    {i j : ℕ} (hGap : i + 2 ≤ j) (hEnd : j < p.length)
    (hBuy : p.getVert (i + 1) ∈ (s (p.getVert i)).val) :
    p.getVert (j + 1) ∈ (s (p.getVert j)).val := by
  let forward (k : ℕ) := p.getVert (k + 1) ∈ (s (p.getVert k)).val
  let P := DegreeTwoBlockThread.ofWalk p hPath hDegree girth
  have stepTwo (k : ℕ) (hk : k + 2 < p.length) (h : forward k) : forward (k + 2) := by
    have h₁ := p.adj_getVert_succ (i := k) (by omega)
    have h₂ := p.adj_getVert_succ (i := k + 1) (by omega)
    have h₃ := p.adj_getVert_succ (i := k + 2) hk
    rcases blockGraph_le (graph s) S h₃ with good | bad
    · exact good
    · exact (nash_block_no_inward_purchases_on_three_step_path s α hne hS h₁ h₂ h₃
        (P.three k (by omega)) (hDegree _ (by omega) (by omega))
        (hDegree _ (by omega) (by omega)) h bad).elim
  have stepThree (k : ℕ) (hk : k + 3 < p.length) (h : forward k) : forward (k + 3) := by
    have h₁ := p.adj_getVert_succ (i := k) (by omega)
    have h₂ := p.adj_getVert_succ (i := k + 1) (by omega)
    have h₃ := p.adj_getVert_succ (i := k + 2) (by omega)
    have h₄ := p.adj_getVert_succ (i := k + 3) hk
    let t := (p.drop k).take 4
    have ht : t.IsPath := (hPath.drop k).take 4
    have htLength : t.length = 4 := by
      simp only [t, Walk.take_length, Walk.drop_length]
      exact min_eq_left (by omega)
    let q := t.mapLe (blockGraph_le (graph s) S)
    have hq : q.IsPath := ht.mapLe _
    have hqLength : q.length = 4 := by simpa only [q, Walk.length_mapLe] using htLength
    have hGeo : (graph s).dist (p.getVert k) (p.getVert (k + 4)) = 4 := by
      have hLower := min_path_length_girth_sub_le_dist girth q hq
      have hUpper := dist_le q
      have hh : (graph s).dist (p.getVert k) ((p.drop k).getVert 4) = 4 := by
        rw [hqLength] at hLower hUpper
        omega
      simpa only [Walk.drop_getVert] using hh
    rcases blockGraph_le (graph s) S h₄ with good | bad
    · exact good
    · exact (nash_block_no_inward_purchases_on_four_step_path s α hne hS h₁ h₂ h₃ h₄
        hGeo (hDegree _ (by omega) (by omega)) (hDegree _ (by omega) (by omega))
        h bad).elim
  have propagate : ∀ k, 2 ≤ k → i + k < p.length → forward (i + k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk hInside
      by_cases hTwo : k = 2
      · subst k; exact stepTwo i hInside hBuy
      by_cases hThree : k = 3
      · subst k; exact stepThree i hInside hBuy
      have smaller := ih (k - 2) (by omega) (by omega) (by omega)
      have hIndex : i + (k - 2) + 2 = i + k := by omega
      have result := stepTwo (i + (k - 2)) (by omega) smaller
      rw [hIndex] at result
      exact result
  have result := propagate (j - i) (by omega) (by omega)
  rwa [show i + (j - i) = j by omega] at result

#print axioms nash_block_chain_purchase_propagates

/-- Forward purchases form a final interval, with at most one adjacent
inversion at its boundary. This gives the ownership cases used by the search. -/
theorem chain_purchase_word_cases {length : ℕ} (forward : ℕ → Prop)
    (propagate : ∀ i j, i + 2 ≤ j → j < length → forward i → forward j) :
    (∃ b ≤ length, ∀ j < length, forward j ↔ b ≤ j) ∨
    (∃ b, 0 < b ∧ b < length ∧ ∀ j < length, forward j ↔ j + 1 = b ∨ b < j) := by
  classical
  by_cases someForward : ∃ j, j < length ∧ forward j
  · let i := Nat.find someForward
    have hi : i < length ∧ forward i := Nat.find_spec someForward
    have first {j : ℕ} (hj : j < length) (hBuy : forward j) : i ≤ j :=
      Nat.find_min' someForward ⟨hj, hBuy⟩
    by_cases inversion : i + 1 < length ∧ ¬ forward (i + 1)
    · refine Or.inr ⟨i + 1, by omega, inversion.1, fun j hj => ⟨?_, ?_⟩⟩
      · intro owned
        have hFirst := first hj owned
        have hNe : j ≠ i + 1 := fun h => inversion.2 (h ▸ owned)
        omega
      · rintro (atBoundary | after)
        · exact (show j = i by omega).symm ▸ hi.2
        · exact propagate i j (by omega) hj hi.2
    · refine Or.inl ⟨i, hi.1.le, fun j hj => ⟨first hj, ?_⟩⟩
      intro hBefore
      by_cases same : j = i
      · exact same.symm ▸ hi.2
      by_cases next : j = i + 1
      · by_contra denied
        exact inversion ⟨next ▸ hj, next ▸ denied⟩
      · exact propagate i j (by omega) hj hi.2
  · exact Or.inl ⟨length, le_rfl, fun j hj =>
      ⟨fun h => (someForward ⟨j, hj, h⟩).elim, fun h => (Nat.not_le_of_lt hj h).elim⟩⟩

#print axioms chain_purchase_word_cases

end TreeConjecture
