import Lax869952Proofs.RootedOwnership
import Lax869952Proofs.ShortThreads

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph RootedOwnership Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ} {V : Type*} [Fintype V]

private theorem smaller_depth_avoids_parent {G : SimpleGraph (Fin n)} {r u v : Fin n}
    (T : ShortestParents G r) (hur : u ≠ r) (hdepth : G.dist r v ≤ G.dist r u) :
    T.parent v ≠ u := by
  intro eq
  by_cases hv : v = r
  · subst v
    exact hur (eq.symm.trans T.parent_root)
  · have before := T.parent_depth hv
    rw [eq] at before
    omega

/-- The Nash purchase capacity applies to every subgraph embedded in the
game graph. Predecessors are counted inside the chosen subgraph. -/
theorem nash_rooted_subgraph_capacity (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (price : (n : ℝ) - 2 < α)
    (K : SimpleGraph V) (player : V ↪ Fin n)
    (hEdge : ∀ {v w}, K.Adj v w → (graph s).Adj (player v) (player w))
    (r : Fin n) (hRoot : ∀ v, distanceSum (graph s) r ≤ distanceSum (graph s) (player v))
    (v : V) :
    let depth (w : V) := (graph s).dist r (player w)
    let buy (w z : V) := player z ∈ (s (player w)).val
    (boughtEarlier K depth buy v).card +
      (boughtLater K depth buy v).card + (boughtSame K depth buy v).card ≤ 1 := by
  classical
  let G := graph s
  let depth (w : V) := G.dist r (player w)
  let buy (w z : V) := player z ∈ (s (player w)).val
  let E := boughtEarlier K depth buy v
  let L := boughtLater K depth buy v
  let H := boughtSame K depth buy v
  let S := E ∪ L ∪ H
  have mE {w : V} (hw : w ∈ E) : w ∈ earlier K depth v ∧ buy v w := by
    have h : w ∈ earlier K depth v ∧ (buy v w ∧ 2 ≤ (earlier K depth v).card) := by
      simpa [E, boughtEarlier] using hw
    exact ⟨h.1, h.2.1⟩
  have mL {w : V} (hw : w ∈ L) :
      w ∈ later K depth v ∧ buy v w ∧ 2 ≤ (earlier K depth w).card := by
    simpa [L, boughtLater] using hw
  have mH {w : V} (hw : w ∈ H) : w ∈ same K depth v ∧ buy v w := by
    simpa [H, boughtSame] using hw
  have eDepth {w : V} (hw : w ∈ E) : depth w + 1 = depth v :=
    ((mem_earlier K depth).mp (mE hw).1).2
  have lDepth {w : V} (hw : w ∈ L) : depth v + 1 = depth w :=
    ((mem_later K depth).mp (mL hw).1).2
  have hDepth {w : V} (hw : w ∈ H) : depth w = depth v :=
    ((mem_same K depth).mp (mH hw).1).2
  have disjEL : Disjoint E L := Finset.disjoint_left.mpr (by
    intro w he hl
    have he' := eDepth he
    have hl' := lDepth hl
    omega)
  have disjH : Disjoint (E ∪ L) H := Finset.disjoint_left.mpr (by
    intro w heh hh
    have eq := hDepth hh
    rcases Finset.mem_union.mp heh with he | hl
    · have h := eDepth he
      omega
    · have h := lDepth hl
      omega)
  have card : S.card = E.card + L.card + H.card := by
    simp only [S, Finset.card_union_of_disjoint disjH, Finset.card_union_of_disjoint disjEL]
  have hG := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  have alternate {w : V} (hw : w ∈ L) :
      ∃ a, a ∈ earlier K depth w ∧ a ≠ v := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (mL hw).2.2
    by_cases eq : a = v
    · exact ⟨b, hb, fun h => hab (eq.trans h.symm)⟩
    · exact ⟨a, ha, eq⟩
  change E.card + L.card + H.card ≤ 1
  rw [← card]
  by_cases hr : player v = r
  · have dv : depth v = 0 := by simp [depth, hr]
    have empty : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      rcases Finset.mem_union.mp hw with hel | hh
      · rcases Finset.mem_union.mp hel with he | hl
        · have h := eDepth he
          omega
        · obtain ⟨a, ha, hav⟩ := alternate hl
          have h := ((mem_earlier K depth).mp ha).2
          have h' := lDepth hl
          have da : G.dist r (player a) = 0 := by change depth a = 0; omega
          exact hav (player.injective ((hG.dist_eq_zero_iff.mp da).symm.trans hr.symm))
      · have h := hDepth hh
        have dw : G.dist r (player w) = 0 := by change depth w = 0; omega
        have eq := (hG.dist_eq_zero_iff.mp dw).symm.trans hr.symm
        exact ((mem_same K depth).mp (mH hh).1).1.ne (player.injective eq.symm)
    simp [empty]
  · have bound := nash_at_most_one_alternative_purchase_above_order_sub_two hne price hr
      (hRoot v) (S.map player)
    have hBuy (x : Fin n) (hx : x ∈ S.map player) : x ∈ (s (player v)).val := by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hx
      rcases Finset.mem_union.mp hw with hel | hh
      · rcases Finset.mem_union.mp hel with he | hl
        · exact (mE he).2
        · exact (mL hl).2.1
      · exact (mH hh).2
    let T := chooseShortestParents hG r
    have hAlt (x : Fin n) (hx : x ∈ S.map player) :
        ∃ P : ShortestParents G r, P.parent x ≠ player v := by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hx
      rcases Finset.mem_union.mp hw with hel | hh
      · rcases Finset.mem_union.mp hel with he | hl
        · refine ⟨T, smaller_depth_avoids_parent T hr ?_⟩
          change depth w ≤ depth v
          have h := eDepth he
          omega
        · obtain ⟨a, ha, hav⟩ := alternate hl
          have hwa := (mem_earlier K depth).mp ha
          have hw : player w ≠ r := by
            intro eq
            have hZero : depth w = 0 := by simp [depth, eq]
            have h := lDepth hl
            omega
          exact T.exists_of_alternative_edge hw (hEdge hwa.1) hwa.2 (player.injective.ne hav)
      · exact ⟨T, smaller_depth_avoids_parent T hr (hDepth hh).le⟩
    simpa using bound hBuy hAlt

/-- In any embedded subgraph of minimum degree three, there is a cubic
vertex on an edge within a distance layer of the minimum-distance root. -/
theorem nash_subgraph_cubic_equal_layer (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hPositive : 0 < α) (price : (n : ℝ) - 2 < α)
    [Nonempty V] (K : SimpleGraph V) [DecidableRel K.Adj] (player : V ↪ Fin n)
    (hEdge : ∀ {v w}, K.Adj v w → (graph s).Adj (player v) (player w))
    (r : Fin n) (hRoot : ∀ v, distanceSum (graph s) r ≤ distanceSum (graph s) (player v))
    (hMin : ∀ v, 3 ≤ K.degree v) :
    ∃ v w, K.degree v = 3 ∧ K.Adj v w ∧
      (graph s).dist r (player v) = (graph s).dist r (player w) := by
  classical
  let G := graph s
  let depth (w : V) := G.dist r (player w)
  let buy (w z : V) := player z ∈ (s (player w)).val
  have owner {u v : V} (adj : K.Adj u v) :
      (buy u v ∧ ¬ buy v u) ∨ (buy v u ∧ ¬ buy u v) := by
    rcases hEdge adj with h | h
    · exact Or.inl ⟨h, nash_no_double_purchase α hPositive s hne h⟩
    · exact Or.inr ⟨h, nash_no_double_purchase α hPositive s hne h⟩
  have hG := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  have step {u v : V} (h : K.Adj u v) :
      depth u ≤ depth v + 1 ∧ depth v ≤ depth u + 1 := by
    have left := hG.dist_triangle (u := r) (v := player v) (w := player u)
    have right := hG.dist_triangle (u := r) (v := player u) (w := player v)
    simpa only [dist_eq_one_iff_adj.mpr (hEdge h).symm, dist_eq_one_iff_adj.mpr (hEdge h)]
      using And.intro left right
  have capacity v := nash_rooted_subgraph_capacity s α hne price K player hEdge r hRoot v
  obtain ⟨v, hep, hpattern⟩ := exists_cubic_pattern K depth buy owner step hMin capacity
  have vDegree : K.degree v = 3 := by
    have eq := counts_degree K depth buy step v
    unfold LayerCounts.degree at eq
    rcases hpattern with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> omega
  have samePos : 0 < (same K depth v).card := by
    have hSaw : (0 : ℤ) < (counts K depth buy v).same := by rcases hpattern with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> omega
    change (0 : ℤ) < ((same K depth v).card : ℤ) at hSaw
    exact_mod_cast hSaw
  obtain ⟨w, hw⟩ := Finset.card_pos.mp samePos
  exact ⟨v, w, vDegree, ((mem_same K depth).mp hw).1, ((mem_same K depth).mp hw).2.symm⟩

/-- Every nonempty subgraph of an equilibrium graph has a vertex of
degree at most three. The finite vertex embedding may omit ambient edges. -/
theorem nash_subgraph_has_degree_le_three (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hPositive : 0 < α) (price : (n : ℝ) - 2 < α)
    [Nonempty V] (K : SimpleGraph V) [DecidableRel K.Adj] (player : V ↪ Fin n)
    (hEdge : ∀ {v w}, K.Adj v w → (graph s).Adj (player v) (player w)) :
    ∃ v, K.degree v ≤ 3 := by
  classical
  by_contra! all
  obtain ⟨v, _, least⟩ := Finset.exists_min_image Finset.univ
    (fun u : V => distanceSum (graph s) (player u)) Finset.univ_nonempty
  obtain ⟨w, _, hw, _, _⟩ := nash_subgraph_cubic_equal_layer s α hne hPositive price
    K player hEdge (player v) (fun w => least w (Finset.mem_univ w)) (fun w => by have h := all w; omega)
  have bound := all w
  omega

/-- After removing equal-layer edges at a minimum-distance root, every
nonempty subgraph has a vertex of degree at most two. -/
theorem nash_cross_layer_subgraph_has_degree_le_two (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hPositive : 0 < α) (price : (n : ℝ) - 2 < α)
    [Nonempty V] (K : SimpleGraph V) [DecidableRel K.Adj] (player : V ↪ Fin n)
    (hEdge : ∀ {v w}, K.Adj v w → (graph s).Adj (player v) (player w))
    (r : Fin n) (hRoot : ∀ v, distanceSum (graph s) r ≤ distanceSum (graph s) (player v))
    (cross : ∀ {v w}, K.Adj v w → (graph s).dist r (player v) ≠ (graph s).dist r (player w)) :
    ∃ v, K.degree v ≤ 2 := by
  by_contra! all
  obtain ⟨_, _, _, h, eq⟩ := nash_subgraph_cubic_equal_layer s α hne hPositive price
    K player hEdge r hRoot all
  exact cross h eq


/-- Every nonempty subgraph of a bipartite equilibrium has a vertex
of degree at most two, regardless of the number of players. -/
theorem nash_bipartite_subgraph_has_degree_le_two (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hPositive : 0 < α) (price : (n : ℝ) - 2 < α)
    (bipartite : (graph s).IsBipartite)
    [Nonempty V] (K : SimpleGraph V) [DecidableRel K.Adj] (player : V ↪ Fin n)
    (hEdge : ∀ {v w}, K.Adj v w → (graph s).Adj (player v) (player w)) :
    ∃ v, K.degree v ≤ 2 := by
  classical
  obtain ⟨v, _, least⟩ := Finset.exists_min_image Finset.univ
    (fun u : V => distanceSum (graph s) (player u)) Finset.univ_nonempty
  have hG := nash_connected (Nat.zero_lt_of_lt (player v).isLt) α s hne
  obtain ⟨c⟩ := bipartite
  apply nash_cross_layer_subgraph_has_degree_le_two s α hne hPositive price K player hEdge
    (player v) (fun w => least w (Finset.mem_univ w))
  intro u w h hEq
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist (player v) (player u)
  obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist (player v) (player w)
  have parityP := walk_length_color_parity c p
  have parityQ := walk_length_color_parity c q
  rw [hp, hEq] at parityP
  rw [hq] at parityQ
  exact c.valid (hEdge h) (Fin.ext (parityP.symm.trans parityQ))

/-- The bipartite conclusion is local to a maximal block. External
attachments and other blocks may contain odd cycles. -/
theorem nash_bipartite_block_subgraph_has_degree_le_two (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hPositive : 0 < α) (price : (n : ℝ) - 2 < α)
    {S : Finset (Fin n)} (hS : IsBiconnectedBlock (graph s) S)
    (bipartite : (blockGraph (graph s) S).IsBipartite)
    [Nonempty V] (K : SimpleGraph V) [DecidableRel K.Adj] (player : V ↪ Fin n)
    (hVertex : ∀ v, player v ∈ S)
    (hEdge : ∀ {v w}, K.Adj v w → (blockGraph (graph s) S).Adj (player v) (player w)) :
    ∃ v, K.degree v ≤ 2 := by
  obtain ⟨r, hr, least⟩ := hS.exists_min_distanceSum
  have hG := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  apply nash_cross_layer_subgraph_has_degree_le_two s α hne hPositive price K player
    (fun h => blockGraph_le (graph s) S (hEdge h)) r (fun v => least _ (hVertex v))
  intro u w h hEq
  have p := block_path_dist_parity hS hG bipartite (hVertex u) (hVertex w) hr (hEdge h).toWalk
  rw [dist_comm (u := player u), dist_comm (u := player w)] at p
  rw [Adj.length_toWalk] at p
  omega

#print axioms nash_subgraph_has_degree_le_three
#print axioms nash_cross_layer_subgraph_has_degree_le_two
#print axioms nash_bipartite_block_subgraph_has_degree_le_two

end Lax869952Proofs
