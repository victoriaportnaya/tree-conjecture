import Lax869952Proofs.RootedShortestPaths
import Lax869952Proofs.Girth

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Function Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

namespace ShortestParents

variable {n : ℕ} {G : SimpleGraph (Fin n)} {root : Fin n} (T : ShortestParents G root)

/-- An edge to a strict ancestor is a tree edge. Adjacent levels differ by at
most one, so the ancestor must be the immediate parent. -/
theorem adjacent_ancestor_is_tree_edge (hG : G.Connected) {x y : Fin n}
    (hxy : G.Adj x y) (hbranch : x ∈ T.branch y) : T.tree.Adj x y := by
  classical
  obtain ⟨k, hk, he⟩ : ∃ k ≤ G.dist root x, T.parent^[k] x = y := by
    simpa [branch] using hbranch
  have hdepth := T.depth_iterate k x
  rw [he] at hdepth
  have hupper : G.dist root x ≤ G.dist root y + G.dist y x := hG.dist_triangle
  rw [dist_eq_one_iff_adj.mpr hxy.symm] at hupper
  have hkne : k ≠ 0 := by
    intro hz
    exact hxy.ne (by simpa [hz] using he)
  have h₁ : k = 1 := by omega
  rw [h₁, Function.iterate_one] at he
  exact ⟨hxy.ne, Or.inl he⟩

/-- Closing a tree path with an off-tree edge forms a cycle in the graph. -/
theorem cycle_of_off_tree_edge {x y : Fin n}
    (hxy : G.Adj x y) (hoff : ¬ T.tree.Adj x y) (p : T.tree.Walk x y) (hp : p.IsPath) :
    (Walk.cons hxy.symm (p.mapLe T.tree_le)).IsCycle := by
  have hnot : s(y, x) ∉ (p.mapLe T.tree_le).edges := by
    intro hm
    have hmem : s(y, x) ∈ p.edges := by simpa only [Walk.edges_mapLe_eq_edges] using hm
    exact hoff (p.adj_of_mem_edges hmem).symm
  exact (Walk.cons_isCycle_iff _ _).mpr ⟨hp.mapLe T.tree_le, hnot⟩

/-- An off-tree edge closes a cycle along the tree's unique path. -/
theorem fundamental_cycle (hG : G.Connected) {x y : Fin n}
    (hxy : G.Adj x y) (hoff : ¬ T.tree.Adj x y) :
    ∃ p : G.Walk y y, p.IsCycle ∧ s(x, y) ∈ p.edges ∧
      p.length = T.tree.dist x y + 1 := by
  have ht := (T.isTree hG).connected
  obtain ⟨q, hq, hlen⟩ := ht.exists_path_of_dist x y
  refine ⟨.cons hxy.symm (q.mapLe T.tree_le), T.cycle_of_off_tree_edge hxy hoff q hq, ?_, ?_⟩
  · rw [Walk.edges_cons, List.mem_cons]
    exact Or.inl Sym2.eq_swap
  · simp only [Walk.length_cons, Walk.length_mapLe, hlen]

/-- An off-tree edge closes a fundamental cycle whose length is at most
twice the depth of its first endpoint, plus two. -/
theorem fundamental_cycle_length_le (hG : G.Connected) {x y : Fin n}
    (hxy : G.Adj x y) (hoff : ¬ T.tree.Adj x y) :
    ∃ p : G.Walk y y, p.IsCycle ∧ s(x, y) ∈ p.edges ∧
      p.length ≤ 2 * G.dist root x + 2 := by
  have ht := (T.isTree hG).connected
  obtain ⟨p, hp, he, hlen⟩ := T.fundamental_cycle hG hxy hoff
  have htBound : T.tree.dist x y ≤ T.tree.dist x root + T.tree.dist root y := ht.dist_triangle
  rw [SimpleGraph.dist_comm (u := x) (v := root), T.root_distance hG x,
    T.root_distance hG y] at htBound
  have hlevels : G.dist root y ≤ G.dist root x + G.dist x y := hG.dist_triangle
  rw [dist_eq_one_iff_adj.mpr hxy] at hlevels
  exact ⟨p, hp, he, by omega⟩

end ShortestParents

/-- In the setting of the 2n proof, an endpoint of an out-edge is at
depth at least three. This is the out-edge case of the depth argument. -/
theorem nash_out_edge_depth_ge_three {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {root x y : Fin n} (T : ShortestParents (graph s) root)
    (hxy : (graph s).Adj x y) (hoff : ¬ T.tree.Adj x y) :
    3 ≤ (graph s).dist root x := by
  have hG := nash_connected (Nat.zero_lt_of_lt root.isLt) α s hne
  obtain ⟨p, hp, _, hupper⟩ := T.fundamental_cycle_length_le hG hxy hoff
  have hlower := nash_cycle_length_ge_seven s α hα hne p hp
  omega

#print axioms ShortestParents.fundamental_cycle_length_le
#print axioms nash_out_edge_depth_ge_three

end Lax869952Proofs
