import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph

/-- Two distinct simple paths between the same vertices contain a cycle
of length at most the sum of their lengths. -/
theorem girth_le_path_length_add_length_of_ne {V : Type*} [Fintype V]
    {G : SimpleGraph V} {u v : V} {g : ℕ}
    (hg : ∀ {x : V} (c : G.Walk x x), c.IsCycle → g ≤ c.length)
    (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath) (hne : p ≠ q) :
    g ≤ p.length + q.length := by
  classical
  let edges := (p.edges ++ q.edges).toFinset
  let H := fromEdgeSet (↑edges : Set (Sym2 V))
  have hSub : (↑edges : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    have hm : e ∈ p.edges ++ q.edges := List.mem_toFinset.mp he
    exact (List.mem_append.mp hm).elim (fun h => p.edges_subset_edgeSet h)
      (fun h => q.edges_subset_edgeSet h)
  have hHG : H ≤ G := (fromEdgeSet_le G).2 fun _ he => hSub he.1
  have hMem (e : Sym2 V) (he : e ∈ edges) : e ∈ H.edgeSet := by
    change e ∈ (fromEdgeSet (↑edges : Set (Sym2 V))).edgeSet
    rw [edgeSet_fromEdgeSet]
    exact ⟨he, G.not_isDiag_of_mem_edgeSet (hSub he)⟩
  let pH := p.transfer H (fun e he => hMem e (List.mem_toFinset.mpr (List.mem_append_left _ he)))
  let qH := q.transfer H (fun e he => hMem e (List.mem_toFinset.mpr (List.mem_append_right _ he)))
  have hpH : pH.IsPath := by
    simpa only [Walk.isPath_def, pH, Walk.support_transfer] using hp
  have hqH : qH.IsPath := by
    simpa only [Walk.isPath_def, qH, Walk.support_transfer] using hq
  have hNotTree : ¬ H.IsAcyclic := by
    intro hc
    have he : (⟨pH, hpH⟩ : H.Path u v) = ⟨qH, hqH⟩ := (hc.subsingleton_path u v).allEq _ _
    apply hne
    apply Walk.ext_support
    simpa only [pH, qH, Walk.support_transfer] using
      congrArg (fun t : H.Path u v => t.val.support) he
  obtain ⟨x, c, hc⟩ : ∃ (x : V) (c : H.Walk x x), c.IsCycle := by
    simpa only [SimpleGraph.IsAcyclic, not_forall, Decidable.not_not] using hNotTree
  have hcG := hg (c.mapLe hHG) (hc.mapLe hHG)
  have hcCard := hc.isTrail.length_le_card_edgeFinset
  have hCard : H.edgeFinset.card ≤ edges.card := by
    apply Finset.card_le_card
    intro e he
    have hm := mem_edgeFinset.mp he
    change e ∈ (fromEdgeSet (↑edges : Set (Sym2 V))).edgeSet at hm
    rw [edgeSet_fromEdgeSet] at hm
    exact hm.1
  have hBound : edges.card ≤ p.length + q.length := by
    simp only [edges, ← Walk.length_edges, ← List.length_append]
    exact List.toFinset_card_le _
  simp only [Walk.length_mapLe] at hcG
  omega

/-- In a graph with no cycles shorter than g, a path of length L is either
shortest or its length plus the distance between its endpoints is at least g. -/
theorem girth_le_path_length_add_dist_of_not_shortest {V : Type*} [Fintype V]
    {G : SimpleGraph V} {u v : V} {g : ℕ}
    (hg : ∀ {x : V} (c : G.Walk x x), c.IsCycle → g ≤ c.length)
    (p : G.Walk u v) (hp : p.IsPath) (hshorter : G.dist u v < p.length) :
    g ≤ p.length + G.dist u v := by
  obtain ⟨q, hq, hql⟩ := p.reachable.exists_path_of_dist
  rw [← hql]
  exact girth_le_path_length_add_length_of_ne hg p q hp hq (by
    rintro rfl
    omega)

/-- A girth lower bound yields a distance bound along any given simple path. -/
theorem min_path_length_girth_sub_le_dist {V : Type*} [Fintype V]
    {G : SimpleGraph V} {u v : V} {g : ℕ}
    (hg : ∀ {x : V} (c : G.Walk x x), c.IsCycle → g ≤ c.length)
    (p : G.Walk u v) (hp : p.IsPath) :
    min p.length (g - p.length) ≤ G.dist u v := by
  by_cases h : G.dist u v < p.length
  · have hsum := girth_le_path_length_add_dist_of_not_shortest hg p hp h
    exact (min_le_right _ _).trans (by omega)
  · exact (min_le_left _ _).trans (Nat.le_of_not_gt h)

/-- For a vertex with exactly the two named neighbours, every shortest path to
another vertex takes one of those two first steps. -/
theorem dist_eq_min_neighbors_add_one {V : Type*} {G : SimpleGraph V}
    {u a b x : V} (hG : G.Connected) (ha : G.Adj u a) (hb : G.Adj u b)
    (hOnly : ∀ y, G.Adj u y → y = a ∨ y = b) (hx : u ≠ x) :
    G.dist u x = min (G.dist a x) (G.dist b x) + 1 := by
  have hA : G.dist u x ≤ G.dist u a + G.dist a x := hG.dist_triangle
  have hB : G.dist u x ≤ G.dist u b + G.dist b x := hG.dist_triangle
  rw [dist_eq_one_iff_adj.mpr ha] at hA
  rw [dist_eq_one_iff_adj.mpr hb] at hB
  have hUpper : G.dist u x ≤ min (G.dist a x) (G.dist b x) + 1 := by
    omega
  refine le_antisymm hUpper ?_
  obtain ⟨p, _, hLen⟩ := hG.exists_path_of_dist u x
  obtain ⟨y, hab, tail, rfl⟩ := Walk.exists_eq_cons_of_ne hx p
  have hTail := dist_le tail
  rw [Walk.length_cons] at hLen
  rcases hOnly y hab with rfl | rfl <;> omega

#print axioms min_path_length_girth_sub_le_dist
#print axioms dist_eq_min_neighbors_add_one

end Lax869952Proofs
