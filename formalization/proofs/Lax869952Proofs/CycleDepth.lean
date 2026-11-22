import Lax869952Proofs.DirectedMinCycles
import Lax869952Proofs.DirectedGeodesics
import Lax869952Proofs.BranchDetours

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

private lemma directed_cycle_walk_or_reverse {n : ℕ} {s : Profile n} {r : Fin n}
    {p : (graph s).Walk r r} (hp : CycleDirected s p) :
    PurchaseDirected s p ∨ PurchaseDirected s p.reverse := by
  rcases hp with hf | hb
  · left
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    let j : Fin p.length := ⟨i, by simpa using hi⟩
    have hh := hf j
    rw [cycle_getVert_finRotate] at hh
    change p.darts[i].snd ∈ (s p.darts[i].fst).val
    rw [Walk.fst_darts_getElem hi, Walk.snd_darts_getElem hi]
    rw [List.getElem_tail, List.getElem_dropLast,
      Walk.support_getElem_eq_getVert, Walk.support_getElem_eq_getVert]
    exact hh
  · right
    intro d hd
    have hds := Walk.mem_darts_reverse.mp hd
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hds
    let j : Fin p.length := ⟨i, by simpa using hi⟩
    have hh := hb j
    rw [cycle_getVert_finRotate] at hh
    rw [← Dart.symm_symm d, ← he]
    change p.darts[i].fst ∈ (s p.darts[i].snd).val
    rw [Walk.fst_darts_getElem hi, Walk.snd_darts_getElem hi]
    rw [List.getElem_tail, List.getElem_dropLast,
      Walk.support_getElem_eq_getVert, Walk.support_getElem_eq_getVert]
    exact hh

private lemma purchaseDirected_append_right {n : ℕ} {s : Profile n} {x y z : Fin n}
    {p : (graph s).Walk x y} {q : (graph s).Walk y z}
    (h : PurchaseDirected s (p.append q)) : PurchaseDirected s q := by
  intro d hd
  exact h d (by simp [hd])

theorem nash_branch_cycle_depth_of_cycle_bound {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {root u x y : Fin n} (T : ShortestParents (graph s) root)
    (hcompatible : ∀ {v} (p : (graph s).Walk root v), p.length = (graph s).dist root v →
      PurchaseDirected s p → ∀ e ∈ p.edges, e ∈ T.tree.edgeSet)
    (hx : x ∈ T.branch u) (i : ℕ) (hi : i ≤ 2)
    (hxi : (graph s).dist root x = (graph s).dist root u + i)
    (hbuy : y ∈ (s x).val) (hoff : ¬ T.tree.Adj x y)
    (lengthBound : ℕ)
    (hBound : ∀ {v} (q : (graph s).Walk v v), q.IsCycle → u ∈ q.support →
      s(x, y) ∈ q.edges → lengthBound ≤ q.length)
    (hIsoBound : ∀ {v} (q : (graph s).Walk v v), q.IsCycle → u ∈ q.support →
      s(x, y) ∈ q.edges → q.length = lengthBound → IsometricCycle q) :
    lengthBound / 2 ≤ (graph s).dist root u + i := by
  classical
  let G := graph s
  change G.dist root x = G.dist root u + i at hxi
  change lengthBound / 2 ≤ G.dist root u + i
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt root.isLt) α s hne
  have hT := (T.isTree hG).connected
  have hxy : G.Adj x y := Or.inl hbuy
  have hgap : G.dist root x ≤ G.dist root u + 2 := by omega
  have hy := nash_off_tree_edge_leaves_branch s α hne hα T hx hgap hxy hoff
  obtain ⟨p, hp, hplen⟩ := hT.exists_path_of_dist x y
  let close (w : T.tree.Walk x y) : G.Walk y y := .cons hxy.symm (w.mapLe T.tree_le)
  have hclose (w : T.tree.Walk x y) : (close w).length = w.length + 1 := by
    simp [close]
  have hu (w : T.tree.Walk x y) : u ∈ (close w).support := by
    exact List.mem_cons_of_mem _
      (by simpa only [Walk.support_mapLe_eq_support] using T.branch_root_mem_support w hx hy)
  have hEdge (w : T.tree.Walk x y) : s(x, y) ∈ (close w).edges := by
    rw [Sym2.eq_swap]
    simp [close, Walk.edges_cons]
  have hmin := hBound (close p) (T.cycle_of_off_tree_edge hxy hoff p hp) (hu p) (hEdge p)
  rw [hclose, hplen] at hmin

  have hlevels : G.dist root y ≤ G.dist root x + 1 := by
    rw [← dist_eq_one_iff_adj.mpr hxy]
    exact hG.dist_triangle
  have htriangle : T.tree.dist x y ≤ G.dist root x + G.dist root y := by
    have h : T.tree.dist x y ≤ T.tree.dist x root + T.tree.dist root y := hT.dist_triangle
    rwa [SimpleGraph.dist_comm (u := x) (v := root), T.root_distance hG x, T.root_distance hG y] at h

  by_contra hn
  have heq : T.tree.dist x y = G.dist root x + G.dist root y := by omega
  have hdy : G.dist root y = G.dist root x + 1 := by omega
  have hlength : lengthBound = T.tree.dist x y + 1 := by omega
  obtain ⟨branchX, hxLength⟩ := hT.exists_walk_length_eq_dist root x
  obtain ⟨branchY, hyLength⟩ := hT.exists_walk_length_eq_dist root y
  rw [T.root_distance hG x] at hxLength
  rw [T.root_distance hG y] at hyLength
  change branchX.length = G.dist root x at hxLength
  change branchY.length = G.dist root y at hyLength
  let w := branchX.reverse.append branchY
  have hwlen : w.length = T.tree.dist x y := by
    simp only [w, Walk.length_append, Walk.length_reverse, hxLength, hyLength, heq]
  let C := close w
  have hC : C.IsCycle := T.cycle_of_off_tree_edge hxy hoff w (w.isPath_of_length_eq_dist hwlen)
  have hCLen : C.length = lengthBound := by
    change (close w).length = lengthBound
    rw [hclose, hwlen, hlength]
  have hIso := hIsoBound C hC (hu w) (hEdge w) hCLen

  have nR : (0 : ℝ≥0) < α := lt_of_le_of_lt (by positivity) hα
  have hpm : ((n - 1 : ℕ) : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast Nat.sub_le n 1
  have hprice := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpm (by positivity : 0 ≤ (2 : ℝ≥0))) hα
  have hdir := directed_cycle_walk_or_reverse (nash_isometric_cycle_directed s α hne hprice C hIso)
  let A := branchX.mapLe T.tree_le
  let B := branchY.mapLe T.tree_le
  have hCdef : C = Walk.cons hxy.symm (A.reverse.append B) := by simp [C, close, w, A, B]
  rcases hdir with hd | hd
  · rw [hCdef] at hd
    exact (nash_no_double_purchase α nR s hne hbuy ((purchaseDirected_cons _ _).mp hd).1).elim
  · rw [hCdef, Walk.reverse_cons, Walk.reverse_append, Walk.reverse_reverse,
      ← Walk.append_assoc, ← Walk.concat_eq_append] at hd
    have hD := purchaseDirected_append_right hd
    have hDLen : (A.concat hxy).length = G.dist root y := by
      simp [A, hxLength, hdy]
    have hmem : s(x, y) ∈ (A.concat hxy).edges := by
      simp [Walk.edges_concat]
    exact (hoff (hcompatible (A.concat hxy) hDLen hD s(x, y) hmem)).elim

/-- The depth bound of Dippel–Vetta, Lemma 8. If a descendant within
`i ≤ 2` levels buys an off-tree edge, the depth of its ancestor plus `i`
is at least half the length of the shortest cycle through the ancestor,
rounded down. This includes `i = 0`. -/
theorem nash_branch_cycle_depth {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {root u x y : Fin n} (T : ShortestParents (graph s) root)
    (hcompatible : ∀ {v} (p : (graph s).Walk root v), p.length = (graph s).dist root v →
      PurchaseDirected s p → ∀ e ∈ p.edges, e ∈ T.tree.edgeSet)
    (hx : x ∈ T.branch u) (i : ℕ) (hi : i ≤ 2)
    (hxi : (graph s).dist root x = (graph s).dist root u + i)
    (hbuy : y ∈ (s x).val) (hoff : ¬ T.tree.Adj x y)
    {z : Fin n} (c : (graph s).Walk z z)
    (hc : ∀ {v} (q : (graph s).Walk v v), q.IsCycle → u ∈ q.support → c.length ≤ q.length) :
    c.length / 2 ≤ (graph s).dist root u + i :=
  nash_branch_cycle_depth_of_cycle_bound s α hne hα T hcompatible hx i hi hxi hbuy hoff c.length
    (fun q hq hqu _ => hc q hq hqu)
    (fun q hq hqu _ hLen => shortest_cycle_through_vertex_isometric q hq hqu
      (fun p hp hpu => hLen.trans_le (hc p hp hpu)))

#print axioms nash_branch_cycle_depth

end Lax869952Proofs
