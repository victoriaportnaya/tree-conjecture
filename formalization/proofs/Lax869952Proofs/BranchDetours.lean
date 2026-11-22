import Lax869952Proofs.RootedCycles

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Function Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

namespace ShortestParents

variable {n : ℕ} {G : SimpleGraph (Fin n)} {root : Fin n}
variable (T : ShortestParents G root)

lemma branch_route {x v : Fin n} (hx : x ∈ T.branch v) :
    ∃ p : T.tree.Walk x v, p.length = G.dist root x - G.dist root v ∧
      ∀ y ∈ p.support, G.dist root v ≤ G.dist root y := by
  classical
  obtain ⟨k, hk, he⟩ : ∃ k ≤ G.dist root x, T.parent^[k] x = v := by
    simpa [branch] using hx
  obtain ⟨p, hp, hs⟩ := T.route_to_iterate_support k x hk
  have hv := T.depth_iterate k x
  rw [he] at hv
  refine ⟨p.copy rfl he, by rw [Walk.length_copy, hp]; omega, ?_⟩
  intro y hy
  rw [Walk.support_copy] at hy
  obtain ⟨j, hj, hye⟩ := hs y hy
  have hyDepth := T.depth_iterate j x
  rw [hye] at hyDepth
  omega

lemma mem_branch_of_mem_child_branch {x v : Fin n}
    (hv : v ≠ root) (hx : x ∈ T.branch v) :
    x ∈ T.branch (T.parent v) := by
  classical
  obtain ⟨k, hk, he⟩ : ∃ k ≤ G.dist root x, T.parent^[k] x = v := by
    simpa [branch] using hx
  have hdepth := T.depth_iterate k x
  rw [he] at hdepth
  have hvDepth := T.parent_depth hv
  have he' : T.parent^[k + 1] x = T.parent v := by
    rw [Function.iterate_succ_apply', he]
  simpa only [branch, Finset.mem_filter, Finset.mem_univ, true_and] using
    (show ∃ j ≤ G.dist root x, T.parent^[j] x = T.parent v from ⟨k + 1, by omega, he'⟩)

lemma outside_branch_route (hG : G.Connected) {u y : Fin n}
    (hy : y ∉ T.branch u) :
    ∃ p : T.tree.Walk y root, p.length = G.dist root y ∧ u ∉ p.support := by
  classical
  obtain ⟨p, hp, hs⟩ := T.route_to_iterate_support (G.dist root y) y le_rfl
  have hzero : G.dist root (T.parent^[G.dist root y] y) = 0 := by
    rw [T.depth_iterate, Nat.sub_self]
  have he := hG.dist_eq_zero_iff.mp hzero
  refine ⟨p.copy rfl he.symm, by simpa using hp, ?_⟩
  intro hu
  rw [Walk.support_copy] at hu
  exact hy (by simpa [branch] using hs u hu)

lemma parent_mem_branch_of_ne {x u : Fin n}
    (hx : x ∈ T.branch u) (hne : x ≠ u) : T.parent x ∈ T.branch u := by
  classical
  obtain ⟨k, hk, he⟩ : ∃ k ≤ G.dist root x, T.parent^[k] x = u := by
    simpa [branch] using hx
  cases k with
  | zero => exact (hne (by simpa using he)).elim
  | succ k =>
    rw [Function.iterate_succ_apply] at he
    have hdepth := T.depth_parent x
    simpa only [branch, Finset.mem_filter, Finset.mem_univ, true_and] using
      (show ∃ j ≤ G.dist root (T.parent x), T.parent^[j] (T.parent x) = u from
        ⟨k, by omega, he⟩)

lemma mem_branch_of_parent_mem {x u : Fin n} (hx : x ≠ root)
    (hp : T.parent x ∈ T.branch u) : x ∈ T.branch u := by
  classical
  obtain ⟨k, hk, he⟩ : ∃ k ≤ G.dist root (T.parent x), T.parent^[k] (T.parent x) = u := by
    simpa [branch] using hp
  have hd := T.parent_depth hx
  simpa only [branch, Finset.mem_filter, Finset.mem_univ, true_and] using
    (show ∃ j ≤ G.dist root x, T.parent^[j] x = u from
      ⟨k + 1, by omega, (Function.iterate_succ_apply _ _ _).trans he⟩)

/-- A walk leaving a branch of a parent tree visits the root of that branch. -/
theorem branch_root_mem_support {x y u : Fin n} (p : T.tree.Walk x y)
    (hx : x ∈ T.branch u) (hy : y ∉ T.branch u) : u ∈ p.support := by
  induction p with
  | nil => exact (hy hx).elim
  | @cons x z y h p ih =>
    by_cases hxu : x = u
    · simp [hxu]
    have hz : z ∈ T.branch u := by
      rcases h.2 with he | he
      · exact he ▸ T.parent_mem_branch_of_ne hx hxu
      · have hz : z ≠ root := by
          intro hz
          subst z
          exact h.1 (he.symm.trans T.parent_root)
        exact T.mem_branch_of_parent_mem hz (he.symm ▸ hx)
    exact List.mem_cons_of_mem _ (ih hz hy)

end ShortestParents

/-- From within two levels of the root of a branch, an off-tree edge
must go outside the branch when every equilibrium cycle has length at least seven. -/
theorem nash_off_tree_edge_leaves_branch {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {root u x y : Fin n} (T : ShortestParents (graph s) root)
    (hx : x ∈ T.branch u)
    (hdepth : (graph s).dist root x ≤ (graph s).dist root u + 2)
    (hxy : (graph s).Adj x y) (hoff : ¬ T.tree.Adj x y) : y ∉ T.branch u := by
  intro hy
  let G := graph s
  change G.dist root x ≤ G.dist root u + 2 at hdepth
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt root.isLt) α s hne
  have hlevels : G.dist root y ≤ G.dist root x + 1 := by
    have hadj : G.Adj x y := hxy
    rw [← dist_eq_one_iff_adj.mpr hadj]
    exact hG.dist_triangle
  obtain ⟨p, hp, _⟩ := T.branch_route hx
  obtain ⟨q, hq, _⟩ := T.branch_route hy
  change p.length = G.dist root x - G.dist root u at hp
  change q.length = G.dist root y - G.dist root u at hq
  have hlen := SimpleGraph.dist_le (p.append q.reverse)
  rw [Walk.length_append, Walk.length_reverse] at hlen
  obtain ⟨c, hc, _, hcl⟩ := T.fundamental_cycle hG hxy hoff
  have hgirth := nash_cycle_length_ge_seven s α hα hne c hc
  omega

/-- The detour in Dippel–Vetta, Lemma 7. When a descendant `x` is within
two steps of `u` and has an off-tree edge, every vertex in the same child
branch can bypass `u` with excess length at most twice the depth gap. -/
theorem nash_short_branch_detour {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {root u v w x y : Fin n} (T : ShortestParents (graph s) root)
    (hv : v ≠ root) (hparent : T.parent v = u)
    (hw : w ∈ T.branch v) (hx : x ∈ T.branch v)
    (i : ℕ) (hi : i ≤ 2) (hxi : (graph s).dist root x = (graph s).dist root u + i)
    (hxy : (graph s).Adj x y) (hoff : ¬ T.tree.Adj x y) :
    ∃ p : (graph s).Walk w root, p.length ≤ (graph s).dist root w + 2 * i ∧ u ∉ p.support := by
  classical
  let G := graph s
  change G.dist root x = G.dist root u + i at hxi
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt root.isLt) α s hne
  have hlevels : G.dist root y ≤ G.dist root x + 1 := by
    have hadj : G.Adj x y := hxy
    rw [← dist_eq_one_iff_adj.mpr hadj]
    exact hG.dist_triangle
  have hvDepth := T.parent_depth hv
  rw [hparent] at hvDepth
  change G.dist root u + 1 = G.dist root v at hvDepth
  have hxDepth := T.branch_geodesic hx hG
  have hwDepth := T.branch_geodesic hw hG
  change G.dist root x = G.dist root v + G.dist v x at hxDepth
  change G.dist root w = G.dist root v + G.dist v w at hwDepth
  have hxu : x ∈ T.branch u := by
    simpa only [hparent] using T.mem_branch_of_mem_child_branch hv hx
  have hgap : G.dist root x ≤ G.dist root u + 2 := by omega
  have hyout := nash_off_tree_edge_leaves_branch s α hne hα T hxu hgap hxy hoff
  obtain ⟨p, hp, hps⟩ := T.branch_route hw
  obtain ⟨q, hq, hqs⟩ := T.branch_route hx
  obtain ⟨t, ht, hts⟩ := T.outside_branch_route hG hyout
  change p.length = G.dist root w - G.dist root v at hp
  change q.length = G.dist root x - G.dist root v at hq
  change t.length = G.dist root y at ht
  have hpu : u ∉ p.support := fun hu => by
    have huDepth : G.dist root v ≤ G.dist root u := hps u hu
    omega
  have hqu : u ∉ q.support := fun hu => by
    have huDepth : G.dist root v ≤ G.dist root u := hqs u hu
    omega
  have hxu' : x ≠ u := fun h => hqu (h ▸ q.start_mem_support)
  let detour := ((p.mapLe T.tree_le).append (q.reverse.mapLe T.tree_le)).append
    (Walk.cons hxy (t.mapLe T.tree_le))
  refine ⟨detour, ?_, ?_⟩
  · change detour.length ≤ G.dist root w + 2 * i
    simp only [detour, Walk.length_append, Walk.length_mapLe, Walk.length_reverse,
      Walk.length_cons, hp, hq, ht]
    omega
  · simp [detour, Walk.mem_support_append_iff, Walk.support_reverse, hpu, hqu, hts, hxu'.symm]

#print axioms nash_short_branch_detour

end Lax869952Proofs
