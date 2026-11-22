import Lax869952Proofs.BranchDetours

set_option warningAsError true

namespace Lax869952Proofs.ShortestParents

open SimpleGraph Function
open scoped BigOperators

variable {n : ℕ} {G : SimpleGraph (Fin n)} {root : Fin n} (T : ShortestParents G root)

theorem mem_own_branch (v : Fin n) : v ∈ T.branch v := by
  classical
  simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨0, Nat.zero_le _, rfl⟩

/-- The only tree edge leaving a branch joins its root to its parent. -/
theorem branch_boundary {a b v : Fin n} (h : T.tree.Adj a b)
    (ha : a ∈ T.branch v) (hb : b ∉ T.branch v) : a = v ∧ T.parent a = b := by
  rcases h.2 with hab | hba
  · refine ⟨?_, hab⟩
    by_contra hne
    exact hb (hab ▸ T.parent_mem_branch_of_ne ha hne)
  · have hbr : b ≠ root := by
      intro he
      subst b
      exact h.1 (hba.symm.trans T.parent_root)
    exact (hb (T.mem_branch_of_parent_mem hbr (hba.symm ▸ ha))).elim

/-- Every walk leaving a branch visits the parent of the branch root. -/
theorem branch_parent_mem_support {a b v : Fin n} (p : T.tree.Walk a b)
    (ha : a ∈ T.branch v) (hb : b ∉ T.branch v) : T.parent v ∈ p.support := by
  induction p with
  | nil => exact (hb ha).elim
  | @cons a c b h p ih =>
    by_cases hc : c ∈ T.branch v
    · exact List.mem_cons_of_mem _ (ih hc hb)
    · obtain ⟨hav, he⟩ := T.branch_boundary h ha hc
      have hc' : T.parent v = c := hav ▸ he
      exact List.mem_cons_of_mem _ (hc'.symm ▸ p.start_mem_support)

/-- Tree distances to descendants are differences of ambient root depths. -/
theorem tree_dist_of_mem_branch (hG : G.Connected) {v x : Fin n}
    (hx : x ∈ T.branch v) :
    T.tree.dist v x = G.dist root x - G.dist root v := by
  obtain ⟨p, hp, _⟩ := T.branch_route hx
  have hupper := SimpleGraph.dist_le p.reverse
  rw [Walk.length_reverse, hp] at hupper
  have htri : T.tree.dist root x ≤ T.tree.dist root v + T.tree.dist v x :=
    (T.isTree hG).connected.dist_triangle
  rw [T.root_distance hG x, T.root_distance hG v] at htri
  omega

/-- Moving from the parent to the child changes distances by one, with
the sign determined by whether the destination is in the child branch. -/
theorem tree_dist_parent_step (hG : G.Connected) {v : Fin n} (hv : v ≠ root) (x : Fin n) :
    (T.tree.dist v x : ℝ) = (T.tree.dist (T.parent v) x : ℝ) + 1 -
      (if x ∈ T.branch v then 2 else 0) := by
  classical
  by_cases hx : x ∈ T.branch v
  · have hx' := T.mem_branch_of_mem_child_branch hv hx
    have hd := T.parent_depth hv
    have hxDepth := T.branch_geodesic hx hG
    have he : T.tree.dist v x + 1 = T.tree.dist (T.parent v) x := by
      rw [T.tree_dist_of_mem_branch hG hx, T.tree_dist_of_mem_branch hG hx']
      omega
    have hReal : (T.tree.dist v x : ℝ) + 1 = (T.tree.dist (T.parent v) x : ℝ) := by exact_mod_cast he
    rw [if_pos hx]
    linarith
  · have ht := (T.isTree hG).connected
    have hpAdj : T.tree.Adj v (T.parent v) := ⟨(T.parent_adj hv).ne, Or.inl rfl⟩
    have hu : T.tree.dist v x ≤ 1 + T.tree.dist (T.parent v) x := by
      simpa only [dist_eq_one_iff_adj.mpr hpAdj] using
        (ht.dist_triangle : T.tree.dist v x ≤ T.tree.dist v (T.parent v) + T.tree.dist (T.parent v) x)
    obtain ⟨p, hp, hl⟩ := ht.exists_path_of_dist v x
    have hlower : T.tree.dist (T.parent v) x + 1 ≤ T.tree.dist v x := by
      cases p with
      | nil => exact (hx (T.mem_own_branch v)).elim
      | @cons _ y _ hvy q =>
        have havoid := (Walk.cons_isPath_iff hvy q).mp hp |>.2
        have hy : y ∉ T.branch v := fun h => havoid (T.branch_root_mem_support q h hx)
        have he := (T.branch_boundary hvy (T.mem_own_branch v) hy).2
        have hq : T.tree.dist (T.parent v) x ≤ q.length := by
          rw [he]
          exact SimpleGraph.dist_le q
        rw [Walk.length_cons] at hl
        omega
    have he : T.tree.dist v x = T.tree.dist (T.parent v) x + 1 := by omega
    have hReal : (T.tree.dist v x : ℝ) = (T.tree.dist (T.parent v) x : ℝ) + 1 := by exact_mod_cast he
    simpa [hx] using hReal

/-- The total distance in the parent tree is the root's distance sum plus
one unit per player and step, with a two-unit saving for each descendant. -/
theorem tree_distanceSum (hG : G.Connected) (u : Fin n) :
    distanceSum T.tree u = distanceSum G root + (n : ℝ) * (G.dist root u : ℝ) -
      2 * ∑ k ∈ Finset.range (G.dist root u), ((T.branch (T.parent^[k] u)).card : ℝ) := by
  classical
  have hRoot : distanceSum T.tree root = distanceSum G root := by
    simp only [distanceSum, T.root_distance hG]
  have hStep (v : Fin n) (hv : v ≠ root) :
      distanceSum T.tree v = distanceSum T.tree (T.parent v) + n -
        2 * ((T.branch v).card : ℝ) := by
    have hsum (S : Finset (Fin n)) : (∑ x : Fin n, if x ∈ S then (2 : ℝ) else 0) = S.card * 2 := by
      rw [← Finset.sum_filter]
      simp
    unfold distanceSum
    rw [Finset.sum_congr rfl (fun x _ => T.tree_dist_parent_step hG hv x),
      Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum]
    simp
    linarith
  suffices h : ∀ d v, G.dist root v = d → distanceSum T.tree v =
      distanceSum G root + (n : ℝ) * d -
        2 * ∑ k ∈ Finset.range d, ((T.branch (T.parent^[k] v)).card : ℝ) from
    h _ u rfl
  intro d
  induction d with
  | zero =>
    intro v hv
    obtain rfl := hG.dist_eq_zero_iff.mp hv
    simpa using hRoot
  | succ d ih =>
    intro v hd
    have hv : v ≠ root := fun he => by simp [he] at hd
    have hp : G.dist root (T.parent v) = d := by rw [T.depth_parent, hd]; omega
    rw [hStep v hv, ih _ hp, Finset.sum_range_succ']
    simp only [Function.iterate_zero_apply, Function.iterate_succ_apply, Nat.cast_succ]
    ring

#print axioms tree_distanceSum

end Lax869952Proofs.ShortestParents
