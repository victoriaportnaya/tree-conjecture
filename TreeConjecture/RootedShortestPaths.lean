import TreeConjecture.Baseline

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Function

private lemma exists_shortest_parent {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {root x : Fin n} (hx : x ≠ root) :
    ∃ y, G.Adj x y ∧ G.dist root y + 1 = G.dist root x := by
  obtain ⟨walk, hlen⟩ := hG.exists_walk_length_eq_dist x root
  cases walk with
  | nil => exact (hx rfl).elim
  | @cons _ y _ hxy tail =>
    have hlow : G.dist root y ≤ tail.length := by
      rw [SimpleGraph.dist_comm]
      exact SimpleGraph.dist_le tail
    have hhigh : G.dist root x ≤ G.dist root y + G.dist y x := hG.dist_triangle
    rw [dist_eq_one_iff_adj.mpr hxy.symm] at hhigh
    rw [Walk.length_cons, SimpleGraph.dist_comm] at hlen
    exact ⟨y, hxy, by omega⟩

/-- A parent at distance one less from the root, for each non-root vertex. -/
structure ShortestParents {n : ℕ} (G : SimpleGraph (Fin n)) (root : Fin n) where
  parent : Fin n → Fin n
  parent_root : parent root = root
  parent_adj : ∀ {x}, x ≠ root → G.Adj x (parent x)
  parent_depth : ∀ {x}, x ≠ root → G.dist root (parent x) + 1 = G.dist root x

/-- Choose any descending neighbor from a shortest path to the root. -/
noncomputable def chooseShortestParents {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.Connected) (root : Fin n) : ShortestParents G root := by
  let parent (x : Fin n) := if hx : x = root then root else (exists_shortest_parent hG hx).choose
  refine ⟨parent, by simp [parent], ?_, ?_⟩
  · intro x hx
    simpa only [parent, dif_neg hx] using (exists_shortest_parent hG hx).choose_spec.1
  · intro x hx
    simpa only [parent, dif_neg hx] using (exists_shortest_parent hG hx).choose_spec.2

namespace ShortestParents

variable {n : ℕ} {G : SimpleGraph (Fin n)} {root : Fin n}

/-- The spanning graph of the selected parent edges. -/
def tree (T : ShortestParents G root) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ (T.parent x = y ∨ T.parent y = x)
  symm := ⟨fun _ _ ⟨h, h'⟩ => ⟨h.symm, h'.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma tree_le (T : ShortestParents G root) : T.tree ≤ G := by
  rintro x y ⟨hxy, hp | hp⟩
  · have hx : x ≠ root := by
      intro hr
      subst x
      exact hxy (T.parent_root.symm.trans hp)
    exact hp ▸ T.parent_adj hx
  · have hy : y ≠ root := by
      intro hr
      subst y
      exact hxy.symm (T.parent_root.symm.trans hp)
    exact hp ▸ (T.parent_adj hy).symm

lemma depth_parent (T : ShortestParents G root) (x : Fin n) :
    G.dist root (T.parent x) = G.dist root x - 1 := by
  by_cases hx : x = root
  · subst x
    simp [T.parent_root]
  · have h := T.parent_depth hx
    omega

lemma depth_iterate (T : ShortestParents G root) (k : ℕ) (x : Fin n) :
    G.dist root (T.parent^[k] x) = G.dist root x - k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, T.depth_parent]
    omega

/-- Iterating the parent function follows actual edges up to the root, and
the walk visits only the first `k + 1` vertices of the parent chain. -/
lemma route_to_iterate_support (T : ShortestParents G root) (k : ℕ) (x : Fin n)
    (hk : k ≤ G.dist root x) :
    ∃ p : T.tree.Walk x (T.parent^[k] x), p.length = k ∧
      ∀ v ∈ p.support, ∃ j ≤ k, T.parent^[j] x = v := by
  induction k generalizing x with
  | zero => exact ⟨.nil, by simp⟩
  | succ k ih =>
    have hpos : 0 < G.dist root x := by omega
    have hx : x ≠ root := by
      intro hr
      subst x
      simp at hpos
    have hparent : T.tree.Adj x (T.parent x) := ⟨(T.parent_adj hx).ne, Or.inl rfl⟩
    have hdepth := T.parent_depth hx
    obtain ⟨p, hp, hsupport⟩ := ih (T.parent x) (by omega)
    rw [Function.iterate_succ_apply]
    refine ⟨.cons hparent p, by simp [hp], ?_⟩
    intro v hv
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with hv | hv
    · exact ⟨0, Nat.zero_le _, by simpa using hv.symm⟩
    · obtain ⟨j, hj, he⟩ := hsupport v hv
      exact ⟨j + 1, Nat.succ_le_succ hj, (Function.iterate_succ_apply _ _ _).trans he⟩

/-- Iterating the parent function follows actual edges up to the root. -/
lemma route_to_iterate (T : ShortestParents G root) (k : ℕ) (x : Fin n) (hk : k ≤ G.dist root x) :
    ∃ p : T.tree.Walk x (T.parent^[k] x), p.length = k := by
  obtain ⟨p, hp, _⟩ := T.route_to_iterate_support k x hk
  exact ⟨p, hp⟩

private lemma parent_of_shallower_neighbor (T : ShortestParents G root) {x y : Fin n}
    (h : T.tree.Adj x y) (hdepth : G.dist root y ≤ G.dist root x) :
    T.parent x = y := by
  rcases h.2 with hxy | hyx
  · exact hxy
  · have hy : y ≠ root := by
      intro hr
      subst y
      exact h.1.symm (T.parent_root.symm.trans hyx)
    have he := T.parent_depth hy
    rw [hyx] at he
    omega

/-- The graph of the parent edges is a spanning tree. -/
theorem isTree (T : ShortestParents G root) (hG : G.Connected) : T.tree.IsTree := by
  classical
  constructor
  · apply (connected_iff_exists_forall_reachable _).mpr
    refine ⟨root, fun x => ?_⟩
    obtain ⟨p, _⟩ := T.route_to_iterate (G.dist root x) x le_rfl
    have h0 : G.dist root ((T.parent^[G.dist root x]) x) = 0 := by
      simp [T.depth_iterate]
    have he := (hG.dist_eq_zero_iff).mp h0
    exact ⟨(p.copy rfl he.symm).reverse⟩
  · intro v p hp
    let verts := p.support.toFinset
    have hv : v ∈ verts := List.mem_toFinset.mpr p.start_mem_support
    obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image verts (G.dist root) ⟨v, hv⟩
    let hm := List.mem_toFinset.mp hw
    let q := p.rotate w hm
    have hq : q.IsCycle := hp.rotate hm
    have hlen := hq.three_le_length
    have hleft : T.tree.Adj w q.snd := q.adj_snd hq.not_nil
    have hright : T.tree.Adj w q.penultimate := (q.adj_penultimate hq.not_nil).symm
    have hleftMem : q.snd ∈ verts := by
      apply List.mem_toFinset.mpr
      apply (p.mem_support_rotate_iff w hm).mp
      exact q.getVert_mem_support _
    have hrightMem : q.penultimate ∈ verts := by
      apply List.mem_toFinset.mpr
      apply (p.mem_support_rotate_iff w hm).mp
      exact q.getVert_mem_support _
    have he₁ := T.parent_of_shallower_neighbor hleft (hmax _ hleftMem)
    have he₂ := T.parent_of_shallower_neighbor hright (hmax _ hrightMem)
    exact hq.snd_ne_penultimate (he₁.symm.trans he₂)

/-- The selected spanning tree preserves all distances from its root. -/
theorem root_distance (T : ShortestParents G root) (hG : G.Connected) (x : Fin n) :
    T.tree.dist root x = G.dist root x := by
  obtain ⟨p, hp⟩ := T.route_to_iterate (G.dist root x) x le_rfl
  have h0 : G.dist root ((T.parent^[G.dist root x]) x) = 0 := by
    simp [T.depth_iterate]
  have he := (hG.dist_eq_zero_iff).mp h0
  let q := (p.copy rfl he.symm).reverse
  have hq : q.length = G.dist root x := by simp [q, hp]
  exact le_antisymm (hq ▸ SimpleGraph.dist_le q) (q.reachable.dist_anti T.tree_le)

/-- The descendants of v are the vertices whose parent chain passes through v. -/
noncomputable def branch (T : ShortestParents G root) (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun x => ∃ k ≤ G.dist root x, T.parent^[k] x = v)

theorem branch_geodesic (T : ShortestParents G root) {v x : Fin n}
    (hx : x ∈ T.branch v) (hG : G.Connected) :
    G.dist root x = G.dist root v + G.dist v x := by
  classical
  have hx' : ∃ k ≤ G.dist root x, T.parent^[k] x = v := by
    simpa [branch] using hx
  obtain ⟨k, hk, he⟩ := hx'
  obtain ⟨p, hp⟩ := T.route_to_iterate k x hk
  let q := (p.copy rfl he).mapLe T.tree_le
  have hlen : q.length = k := by simp [q, hp]
  have hxv : G.dist v x ≤ k := by simpa [hlen] using SimpleGraph.dist_le q.reverse
  have htri : G.dist root x ≤ G.dist root v + G.dist v x := hG.dist_triangle
  have hdepth := T.depth_iterate k x
  rw [he] at hdepth
  omega

/-- The branch-size bound applied to the constructed shortest-path spanning tree. -/
theorem branch_card_le_half (T : ShortestParents G root) (hG : G.Connected) {v : Fin n}
    (hv : v ≠ root) (hcost : distanceSum G root ≤ distanceSum G v) :
    2 * (T.branch v).card ≤ n :=
  rooted_shortest_path_branch_size G hG hv.symm hcost _ (fun _ hx => T.branch_geodesic hx hG)

end ShortestParents

#print axioms ShortestParents.isTree
#print axioms ShortestParents.root_distance
#print axioms ShortestParents.branch_card_le_half

end TreeConjecture
