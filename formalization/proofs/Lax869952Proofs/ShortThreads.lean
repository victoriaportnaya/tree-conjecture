import Lax869952Proofs.ThreadGeometry

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

/-- At girth eight the two-step target may itself be the maximum attachment.
A second block neighbour of that target gives a further strict saving. -/
theorem nash_block_forces_purchase_away_from_maximum_girth (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    (girth : ∀ {a}, (q : (graph s).Walk a a) → q.IsCycle → 8 ≤ q.length)
    {u v w x : Fin n}
    (huv : (blockGraph (graph s) S).Adj u v)
    (hvw : (blockGraph (graph s) S).Adj v w)
    (huw : u ≠ w) (hDegree : (blockGraph (graph s) S).degree v = 2)
    (hx : x ∈ S) (hDist : (graph s).dist u x = 2 + (graph s).dist w x)
    (hMax : (blockAttachment (graph s) S v).card ≤ (blockAttachment (graph s) S x).card) :
    u ∈ (s v).val := by
  by_cases hwx : w = x
  · subst x
    have hw : w ∈ S := hvw.2.1
    have hTwo : (graph s).dist u w = 2 := by simpa using hDist
    obtain ⟨a, b, ha, hb, hab⟩ := hS.twoConnected.exists_two_neighbors hw
    have hOther : ∃ y, (blockGraph (graph s) S).Adj w y ∧ y ≠ v := by
      by_cases h : a = v
      · exact ⟨b, hb, fun h' => hab (h.trans h'.symm)⟩
      · exact ⟨a, ha, h⟩
    obtain ⟨y, hwy, hyv⟩ := hOther
    have h₁ := blockGraph_le (graph s) S huv
    have h₂ := blockGraph_le (graph s) S hvw
    have h₃ := blockGraph_le (graph s) S hwy
    have huy : u ≠ y := by
      intro he
      have hOne := dist_eq_one_iff_adj.mpr h₃.symm
      rw [he] at hTwo
      omega
    let p := Walk.cons h₁ (Walk.cons h₂ (Walk.cons h₃ Walk.nil))
    have hPath : p.IsPath := by
      simp [p, Walk.isPath_def, h₁.ne, h₂.ne, h₃.ne, huw, huy, hyv.symm]
    have hThree := dist_eq_three_of_girth_eight girth p hPath rfl
    rcases h₁ with hBuy | hBuy
    · exfalso
      have hBound := nash_block_two_step_pair_bound s α hne hS huv hvw huw hDegree
        hBuy hw hwy.2.1 h₃.ne (by simpa using hTwo)
        (by rw [hThree, dist_eq_one_iff_adj.mpr h₃])
      have hPositive : 0 < (blockAttachment (graph s) S y).card := blockAttachment_card_pos y
      omega
    · exact hBuy
  · exact nash_block_forces_purchase_away_from_maximum s α hne hS huv hvw huw hDegree
      hx hwx hDist hMax

/-- A sufficient distance gap forces the penultimate purchase even when
the path starts at the maximum attachment. -/
theorem nash_block_path_penultimate_purchase_of_gap {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B : Fin n} (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {v}, (q : (graph s).Walk v v) → q.IsCycle → 8 ≤ q.length)
    (p : DegreeTwoBlockPath (graph s) S x A B)
    (hLength : 3 ≤ p.walk.length)
    (hGap : p.walk.length + (graph s).dist A x ≤ (graph s).dist B x + 2) :
    p.walk.getVert (p.walk.length - 1) ∈ (s (p.walk.getVert (p.walk.length - 2))).val := by
  have hG := nash_connected (Nat.zero_lt_of_lt x.isLt) α s hne
  let L := p.walk.length
  change 3 ≤ L at hLength
  change L + (graph s).dist A x ≤ (graph s).dist B x + 2 at hGap
  have hNear (i : ℕ) (hi : i ≤ L - 1) :
      (graph s).dist (p.walk.getVert i) x = i + (graph s).dist A x := by
    have hIndex : i ≤ p.walk.length := by change i ≤ L; omega
    have h := block_path_dist_to_external_target hS hG hx p.walk p.isPath p.degree p.avoid hIndex
    change (graph s).dist (p.walk.getVert i) x =
      threadDistance L ((graph s).dist A x) ((graph s).dist B x) i at h
    rw [h, threadDistance, min_eq_left (by omega)]
  have hDist : (graph s).dist (p.walk.getVert (L - 1)) x =
      2 + (graph s).dist (p.walk.getVert (L - 3)) x := by
    rw [hNear _ (by omega), hNear _ (by omega)]
    omega
  have hNe : p.walk.getVert (L - 1) ≠ p.walk.getVert (L - 3) := by
    intro he
    rw [he] at hDist
    omega
  have h₁ : (blockGraph (graph s) S).Adj
      (p.walk.getVert (L - 2)) (p.walk.getVert (L - 1)) := by
    have hAdj := p.walk.adj_getVert_succ (i := L - 2) (by change L - 2 < L; omega)
    simpa only [show L - 2 + 1 = L - 1 by omega] using hAdj
  have h₂ : (blockGraph (graph s) S).Adj
      (p.walk.getVert (L - 3)) (p.walk.getVert (L - 2)) := by
    have hAdj := p.walk.adj_getVert_succ (i := L - 3) (by change L - 3 < L; omega)
    simpa only [show L - 3 + 1 = L - 2 by omega] using hAdj
  exact nash_block_forces_purchase_away_from_maximum_girth s α hne hS girth
    h₁.symm h₂.symm hNe (p.degree _ (by omega) (by change L - 2 < L; omega))
    hx hDist (hMax _ h₁.1)

/-- Paths of length at least five and shorter paths with the specified
distance gap have a penultimate purchase directed away from the target. -/
theorem nash_block_path_penultimate_purchase_of_length_or_gap {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B : Fin n} (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {v}, (q : (graph s).Walk v v) → q.IsCycle → 8 ≤ q.length)
    (p : DegreeTwoBlockPath (graph s) S x A B) (hAB : A ≠ B)
    (hLength : 3 ≤ p.walk.length)
    (hNear : (graph s).dist A x ≤ (graph s).dist B x)
    (hEnough : 5 ≤ p.walk.length ∨ p.walk.length + (graph s).dist A x ≤
      (graph s).dist B x + 2) :
    p.walk.getVert (p.walk.length - 1) ∈ (s (p.walk.getVert (p.walk.length - 2))).val := by
  rcases hEnough with hLong | hGap
  · have hG := nash_connected (Nat.zero_lt_of_lt x.isLt) α s hne
    let P := LongBlockThreadTo.ofWalk hS hG hx girth p.walk p.isPath hLong p.degree p.avoid
    exact nash_block_long_thread_penultimate_purchase s α hne hS P hAB hx hMax hNear
  · exact nash_block_path_penultimate_purchase_of_gap s α hne hS hx hMax girth p hLength hGap

/-- The forest includes all long paths and short paths with sufficient gap.
A short path with strictly increasing endpoint distances can also enter
the forest when the profile supplies its penultimate purchase. -/
theorem nash_block_path_graph_isAcyclic_of_gap_or_purchase {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x : Fin n} (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {v}, (q : (graph s).Walk v v) → q.IsCycle → 8 ≤ q.length)
    (H : SimpleGraph (Fin n))
    (paths : ∀ {u v}, H.Adj v u → DegreeTwoBlockPath (graph s) S x u v)
    (length : ∀ {u v} (h : H.Adj v u), 3 ≤ (paths h).walk.length)
    (eligible : ∀ {u v} (h : H.Adj v u),
      (graph s).dist u x ≤ (graph s).dist v x →
      5 ≤ (paths h).walk.length ∨
        (paths h).walk.length + (graph s).dist u x ≤ (graph s).dist v x + 2 ∨
        ((graph s).dist u x < (graph s).dist v x ∧
          (paths h).walk.getVert ((paths h).walk.length - 1) ∈
            (s ((paths h).walk.getVert ((paths h).walk.length - 2))).val))
    (disjoint : ∀ {u v w} (hu : H.Adj v u) (hw : H.Adj v w), u ≠ w →
      ∀ i j, 0 < i → i < (paths hu).walk.length → 0 < j → j < (paths hw).walk.length →
        (paths hu).walk.getVert i ≠ (paths hw).walk.getVert j) :
    H.IsAcyclic := by
  have buy {u v : Fin n} (h : H.Adj v u)
      (hNear : (graph s).dist u x ≤ (graph s).dist v x) :
      (paths h).walk.getVert ((paths h).walk.length - 1) ∈
        (s ((paths h).walk.getVert ((paths h).walk.length - 2))).val := by
    rcases eligible h hNear with hLong | hGap | hBuy
    · exact nash_block_path_penultimate_purchase_of_length_or_gap s α hne hS hx hMax girth
        (paths h) h.ne.symm (length h) hNear (Or.inl hLong)
    · exact nash_block_path_penultimate_purchase_of_gap s α hne hS hx hMax girth
        (paths h) (length h) hGap
    · exact hBuy.2
  apply isAcyclic_of_unique_lower_neighbor H (fun u => (graph s).dist u x)
  intro v u w hu hw hNearP hNearQ
  by_contra hNe
  exact nash_block_no_two_penultimate_path_purchases s α hne hS girth
    (paths hu) (paths hw) (length hu) (length hw) (buy hu hNearP) (buy hw hNearQ)
    (disjoint hu hw hNe)

#print axioms nash_block_forces_purchase_away_from_maximum_girth
#print axioms nash_block_path_penultimate_purchase_of_gap
#print axioms nash_block_path_graph_isAcyclic_of_gap_or_purchase

/-- For a four-edge path oriented from the nearer end, the first interior
vertex buys toward the middle and the last buys toward the far end.
At equal levels these two vertices each buy both of their path edges. -/
theorem nash_block_four_path_purchases {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B : Fin n} (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {v}, (q : (graph s).Walk v v) → q.IsCycle → 8 ≤ q.length)
    (p : DegreeTwoBlockPath (graph s) S x A B) (hFour : p.walk.length = 4)
    (hNear : (graph s).dist A x ≤ (graph s).dist B x) :
    (p.walk.getVert 2 ∈ (s (p.walk.getVert 1)).val ∧
      B ∈ (s (p.walk.getVert 3)).val) ∧
    ((graph s).dist A x = (graph s).dist B x →
      A ∈ (s (p.walk.getVert 1)).val ∧
        p.walk.getVert 2 ∈ (s (p.walk.getVert 3)).val) := by
  have hG := nash_connected (Nat.zero_lt_of_lt x.isLt) α s hne
  let P := DegreeTwoBlockThread.ofWalk p.walk p.isPath p.degree girth
  have h0 : p.walk.getVert 0 = A := p.walk.getVert_zero
  have h4 : p.walk.getVert 4 = B := by rw [← hFour, Walk.getVert_length]
  have adj (i : ℕ) (hi : i < 4) := p.walk.adj_getVert_succ (i := i) (by omega)
  have distinct {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 4) (hne : i ≠ j) :
      p.walk.getVert i ≠ p.walk.getVert j := by
    intro h
    apply hne
    exact p.isPath.getVert_injOn
      (show i ∈ {k | k ≤ p.walk.length} by simp; omega)
      (show j ∈ {k | k ≤ p.walk.length} by simp; omega) h
  have hMid := block_path_dist_to_external_target hS hG hx p.walk p.isPath
    p.degree p.avoid (j := 2) (by omega)
  rw [hFour, threadDistance] at hMid
  change (graph s).dist (p.walk.getVert 2) x =
    min (2 + (graph s).dist A x) (2 + (graph s).dist B x) at hMid
  have hBuyMiddleLeft : p.walk.getVert 2 ∈ (s (p.walk.getVert 1)).val := by
    apply nash_block_forces_purchase_away_from_maximum_girth s α hne hS girth
      (adj 1 (by decide)).symm (adj 0 (by decide)).symm
      (distinct (by decide) (by decide) (by decide)) (p.degree 1 (by decide) (by omega)) hx
    · rw [h0, hMid, min_eq_left (by omega)]
    · exact hMax _ (adj 1 (by decide)).1
  have hBuyEndRight : p.walk.getVert 4 ∈ (s (p.walk.getVert 3)).val := by
    rcases blockGraph_le (graph s) S (adj 3 (by decide)) with hBuy | hInward
    · exact hBuy
    · exact (nash_block_no_inward_purchases_on_three_step_path s α hne hS
        (adj 1 (by decide)) (adj 2 (by decide)) (adj 3 (by decide)) (P.three 1 (by omega))
        (p.degree 2 (by decide) (by omega)) (p.degree 3 (by decide) (by omega))
        hBuyMiddleLeft hInward).elim
  have hBuyB := Eq.mp (congrArg (fun z : Fin n => z ∈ (s (p.walk.getVert 3)).val) h4)
    hBuyEndRight
  refine ⟨⟨hBuyMiddleLeft, hBuyB⟩, ?_⟩
  intro hEqual
  have hBuyMiddleRight : p.walk.getVert 2 ∈ (s (p.walk.getVert 3)).val := by
    apply nash_block_forces_purchase_away_from_maximum_girth s α hne hS girth
      (adj 2 (by decide)) (adj 3 (by decide))
      (distinct (by decide) (by decide) (by decide)) (p.degree 3 (by decide) (by omega)) hx
    · rw [h4, hMid, hEqual, min_self]
    · exact hMax _ (adj 3 (by decide)).1
  refine ⟨?_, hBuyMiddleRight⟩
  have hBuyEndLeft : p.walk.getVert 0 ∈ (s (p.walk.getVert 1)).val := by
    rcases blockGraph_le (graph s) S (adj 0 (by decide)) with hInward | hBuy
    · exact (nash_block_no_inward_purchases_on_three_step_path s α hne hS
        (adj 0 (by decide)) (adj 1 (by decide)) (adj 2 (by decide)) (P.three 0 (by omega))
        (p.degree 1 (by decide) (by omega)) (p.degree 2 (by decide) (by omega))
        hInward hBuyMiddleRight).elim
    · exact hBuy
  exact Eq.mp (congrArg (fun z : Fin n => z ∈ (s (p.walk.getVert 1)).val) h0) hBuyEndLeft

#print axioms nash_block_four_path_purchases

theorem walk_length_color_parity {V : Type*} {H : SimpleGraph V}
    (c : H.Coloring (Fin 2)) {a b : V} (p : H.Walk a b) :
    (p.length + (c a).val) % 2 = (c b).val := by
  induction p with
  | nil =>
    rw [Walk.length_nil, zero_add, Nat.mod_eq_of_lt (c _).isLt]
  | @cons u v w huv tail ih =>
    have hNe : (c u).val ≠ (c v).val := fun he => c.valid huv (Fin.ext he)
    have hu := (c u).isLt
    have hv := (c v).isLt
    rw [Walk.length_cons]
    omega

/-- In a bipartite block the length parity of a block path agrees with
the parity of the difference of its endpoints' distances to the target. -/
theorem block_path_dist_parity {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock G S) (hG : G.Connected) (bipartite : (blockGraph G S).IsBipartite)
    {A B x : Fin n} (hA : A ∈ S) (hB : B ∈ S) (hx : x ∈ S)
    (p : (blockGraph G S).Walk A B) :
    (G.dist A x + G.dist B x) % 2 = p.length % 2 := by
  obtain ⟨c⟩ := bipartite
  have colorDist (v : Fin n) (hv : v ∈ S) : (G.dist v x + (c v).val) % 2 = (c x).val := by
    obtain ⟨q, hPath, hLen⟩ := hG.exists_path_of_dist v x
    have hSupport := hS.path_support_subset hv hx q hPath
    have hEdges : ∀ e ∈ q.edges, e ∈ (blockGraph G S).edgeSet := by
      intro e he
      induction e using Sym2.ind
      rw [mem_edgeSet, blockGraph_adj]
      exact ⟨hSupport _ (q.fst_mem_support_of_mem_edges he),
        hSupport _ (q.snd_mem_support_of_mem_edges he),
        by simpa only [mem_edgeSet] using q.edges_subset_edgeSet he⟩
    have h := walk_length_color_parity c (q.transfer (blockGraph G S) hEdges)
    simpa only [Walk.length_transfer, hLen] using h
  have hPA := colorDist A hA
  have hPB := colorDist B hB
  have hP := walk_length_color_parity c p
  have hColor := (c x).isLt
  omega

/-- In a bipartite block, length-three paths never tie in endpoint
distance. The forest theorem thus includes every length-three path. -/
theorem nash_bipartite_block_path_graph_isAcyclic_of_ne_four {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    (bipartite : (blockGraph (graph s) S).IsBipartite)
    {x : Fin n} (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {v}, (q : (graph s).Walk v v) → q.IsCycle → 8 ≤ q.length)
    (H : SimpleGraph (Fin n))
    (paths : ∀ {u v}, H.Adj v u → DegreeTwoBlockPath (graph s) S x u v)
    (length : ∀ {u v} (h : H.Adj v u), 3 ≤ (paths h).walk.length)
    (notFour : ∀ {u v} (h : H.Adj v u), (paths h).walk.length ≠ 4)
    (disjoint : ∀ {u v w} (hu : H.Adj v u) (hw : H.Adj v w), u ≠ w →
      ∀ i j, 0 < i → i < (paths hu).walk.length → 0 < j → j < (paths hw).walk.length →
        (paths hu).walk.getVert i ≠ (paths hw).walk.getVert j) :
    H.IsAcyclic := by
  apply nash_block_path_graph_isAcyclic_of_gap_or_purchase s α hne hS hx hMax girth
    H paths length ?_ disjoint
  intro u v h hNear
  by_cases hLong : 5 ≤ (paths h).walk.length
  · exact Or.inl hLong
  · have hLength := length h
    have hNotFour := notFour h
    have hThree : (paths h).walk.length = 3 := by omega
    have hG := nash_connected (Nat.zero_lt_of_lt x.isLt) α s hne
    let p := (paths h).walk
    have hStart := p.adj_snd (by rw [Walk.not_nil_iff_lt_length]; change 0 < (paths h).walk.length; omega)
    have hEnd := p.adj_penultimate (by rw [Walk.not_nil_iff_lt_length]; change 0 < (paths h).walk.length; omega)
    have hParity := block_path_dist_parity hS hG bipartite hStart.1 hEnd.2.1 hx p
    change ((graph s).dist u x + (graph s).dist v x) % 2 = (paths h).walk.length % 2 at hParity
    exact Or.inr (Or.inl (by omega))

#print axioms block_path_dist_parity
#print axioms nash_bipartite_block_path_graph_isAcyclic_of_ne_four

end Lax869952Proofs
