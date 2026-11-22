import TreeConjecture.MinCycles

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph

private lemma length_toDeleteEdge {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (e : Sym2 V) (he : e ∉ p.edges) :
    (p.toDeleteEdge e he).length = p.length :=
  p.length_transfer _

private lemma split_walk_edge {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ (a b : V) (before : G.Walk u a) (edge : G.Adj a b) (after : G.Walk b v),
      e = s(a, b) ∧ p = before.append (.cons edge after) := by
  induction p with
  | nil => simp at he
  | @cons a b c hab tail ih =>
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · exact ⟨a, b, .nil, hab, tail, he, rfl⟩
    · obtain ⟨x, y, before, edge, after, hx, htail⟩ := ih he
      exact ⟨x, y, .cons hab before, edge, after, hx, by rw [Walk.cons_append, ← htail]⟩

private lemma split_trail_parts_avoid {V : Type*} {G : SimpleGraph V} {u v a b : V}
    (before : G.Walk u a) (edge : G.Adj a b) (after : G.Walk b v)
    (ht : (before.append (.cons edge after)).IsTrail) :
    s(a, b) ∉ before.edges ∧ s(a, b) ∉ after.edges := by
  have hn := ht.edges_nodup
  simp only [Walk.edges_append, Walk.edges_cons, List.nodup_append', List.nodup_cons] at hn
  exact ⟨fun he => (List.disjoint_left.mp hn.2.2) he (List.Mem.head _), hn.2.1.1⟩

private lemma cycle_from_edge_deleted_walk {V : Type*} {G : SimpleGraph V} {a b : V}
    (edge : G.Adj a b) (w : (G.deleteEdges {s(a, b)}).Walk a b) :
    ∃ q : G.Walk b b, q.IsCycle ∧ s(a, b) ∈ q.edges ∧ q.length ≤ w.length + 1 := by
  classical
  let H := G.deleteEdges {s(a, b)}
  obtain ⟨shortest, hp, hlen⟩ := w.reachable.exists_path_of_dist
  let path := shortest.mapLe (G.deleteEdges_le {s(a, b)})
  have hs : path.IsPath := hp.mapLe (G.deleteEdges_le _)
  have havoid : s(b, a) ∉ path.edges := by
    intro he
    have hm : s(b, a) ∈ H.edgeSet :=
      shortest.edges_subset_edgeSet (by simpa only [path, Walk.edges_mapLe_eq_edges] using he)
    rw [Sym2.eq_swap] at hm
    have hnot : s(a, b) ∉ H.edgeSet := by simp [H, SimpleGraph.edgeSet_deleteEdges]
    exact hnot hm
  refine ⟨.cons edge.symm path, (Walk.cons_isCycle_iff _ _).mpr ⟨hs, havoid⟩, ?_, ?_⟩
  · rw [Walk.edges_cons, List.mem_cons]
    exact Or.inl Sym2.eq_swap
  · have hw := SimpleGraph.dist_le w
    simp only [Walk.length_cons, path, Walk.length_mapLe, hlen]
    omega

private lemma shortest_edge_cycle_other_arc_distance {V : Type*} {G : SimpleGraph V}
    {u v : V} {p q : G.Walk u v} {e : Sym2 V}
    (hc : (p.append q.reverse).IsCycle) (he : e ∈ q.edges)
    (hmin : ∀ {x} (c : G.Walk x x), c.IsCycle → e ∈ c.edges →
      (p.append q.reverse).length ≤ c.length) :
    G.dist u v = min p.length q.length := by
  classical
  refine le_antisymm (le_min (SimpleGraph.dist_le p) (SimpleGraph.dist_le q)) ?_
  obtain ⟨a, b, before, edge, after, heq, hq⟩ := split_walk_edge q he
  subst e
  have hpAvoid : s(a, b) ∉ p.edges := by
    intro hf
    have hnd := hc.isTrail.edges_nodup
    rw [Walk.edges_append, List.nodup_append'] at hnd
    exact (List.disjoint_left.mp hnd.2.2) hf (by simpa only [Walk.edges_reverse, List.mem_reverse] using he)
  have hqTrail : (before.append (.cons edge after)).IsTrail := by
    rw [← hq]
    have hnd := hc.isTrail.edges_nodup
    rw [Walk.edges_append, List.nodup_append'] at hnd
    rw [Walk.isTrail_def]
    simpa only [Walk.edges_reverse, List.nodup_reverse] using hnd.2.1
  obtain ⟨hBefore, hAfter⟩ := split_trail_parts_avoid before edge after hqTrail
  let H := G.deleteEdges {s(a, b)}
  let A := before.toDeleteEdge s(a, b) hBefore
  let B := p.toDeleteEdge s(a, b) hpAvoid
  let C := after.toDeleteEdge s(a, b) hAfter
  have hqLen : q.length = before.length + after.length + 1 := by
    rw [hq, Walk.length_append, Walk.length_cons]
    omega
  have path_min (w : H.Walk a b) : p.length + before.length + after.length ≤ w.length := by
    obtain ⟨d, hd, hde, hdl⟩ := cycle_from_edge_deleted_walk edge w
    have hmin' := hmin d hd hde
    rw [Walk.length_append, Walk.length_reverse] at hmin'
    omega
  obtain ⟨route, hrPath, hrLen⟩ := p.reachable.exists_path_of_dist
  by_cases hmem : s(a, b) ∈ route.edges
  · obtain ⟨a', b', pre, edge', post, hab, hroute⟩ := split_walk_edge route hmem
    have heParts : s(a', b') ∉ pre.edges ∧ s(a', b') ∉ post.edges :=
      split_trail_parts_avoid pre edge' post (hroute ▸ hrPath.isTrail)
    have hrLength : route.length = pre.length + post.length + 1 := by
      rw [hroute, Walk.length_append, Walk.length_cons]
      omega
    rcases Sym2.eq_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · subst a'
      subst b'
      let X := pre.toDeleteEdge s(a, b) heParts.1
      let Y := post.toDeleteEdge s(a, b) heParts.2
      have hw := path_min ((X.reverse.append B).append Y.reverse)
      simp only [Walk.length_append, Walk.length_reverse, X, B, Y, length_toDeleteEdge] at hw
      exact (min_le_right _ _).trans (by omega)
    · subst a'
      subst b'
      have hpre : s(a, b) ∉ pre.edges := by
        rw [Sym2.eq_swap]
        exact heParts.1
      have hpost : s(a, b) ∉ post.edges := by
        rw [Sym2.eq_swap]
        exact heParts.2
      let X := pre.toDeleteEdge s(a, b) hpre
      let Y := post.toDeleteEdge s(a, b) hpost
      have hw := path_min ((Y.append B.reverse).append X)
      simp only [Walk.length_append, Walk.length_reverse, X, B, Y, length_toDeleteEdge] at hw
      exact (min_le_right _ _).trans (by omega)
  · let R := route.toDeleteEdge s(a, b) hmem
    have hw := path_min ((A.reverse.append R).append C.reverse)
    simp only [Walk.length_append, Walk.length_reverse, A, R, C, length_toDeleteEdge] at hw
    exact (min_le_left _ _).trans (by omega)

/-- Dippel–Vetta (2024), Lemma 2. A shortest cycle through a prescribed
undirected edge is isometric. -/
theorem shortest_cycle_through_edge_isometric {V : Type*} {G : SimpleGraph V} {r : V}
    (p : G.Walk r r) (hp : p.IsCycle) (e : Sym2 V) (he : e ∈ p.edges)
    (hmin : ∀ {x} (q : G.Walk x x), q.IsCycle → e ∈ q.edges → p.length ≤ q.length) :
    IsometricCycle p := by
  refine ⟨hp, fun q hq hperm a b hab hb => ?_⟩
  obtain ⟨left, right, hl, hr, hloop, hloopPerm⟩ := cycle_index_arcs q hq hab hb
  have hsame := hloopPerm.trans hperm
  have hlen : (left.append right.reverse).length = p.length := by
    simpa only [Walk.length_edges] using hsame.length_eq
  have heLoop := hsame.mem_iff.mpr he
  rw [Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse] at heLoop
  rcases heLoop with hleft | hright
  · have hrev : (right.append left.reverse).IsCycle := by
      simpa only [Walk.reverse_append, Walk.reverse_reverse] using hloop.reverse
    have hran : (right.append left.reverse).length = p.length := by
      simp only [Walk.length_append, Walk.length_reverse] at hlen ⊢
      omega
    have hd := shortest_edge_cycle_other_arc_distance hrev hleft
      (fun c hc hce => hran.symm ▸ hmin c hc hce)
    simpa only [hl, hr, min_comm] using hd
  · have hd := shortest_edge_cycle_other_arc_distance hloop hright
      (fun c hc hce => hlen.symm ▸ hmin c hc hce)
    simpa only [hl, hr] using hd

#print axioms shortest_cycle_through_edge_isometric

/-- A shortest cycle through a given vertex is also a shortest cycle
through any of its edges incident to that vertex. -/
theorem shortest_cycle_through_vertex_isometric {V : Type*} {G : SimpleGraph V} {u r : V}
    (p : G.Walk r r) (hp : p.IsCycle) (hu : u ∈ p.support)
    (hmin : ∀ {x} (q : G.Walk x x), q.IsCycle → u ∈ q.support → p.length ≤ q.length) :
    IsometricCycle p := by
  obtain ⟨e, he, hue⟩ := (p.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil).mp hu
  apply shortest_cycle_through_edge_isometric p hp e he
  intro x q hq heq
  exact hmin q hq ((q.mem_support_iff_exists_mem_edges_of_not_nil hq.not_nil).mpr ⟨e, heq, hue⟩)

#print axioms shortest_cycle_through_vertex_isometric

/-- Any edge that belongs to a cycle has a shortest such cycle. -/
theorem exists_shortest_cycle_through_edge {V : Type*} {G : SimpleGraph V} (e : Sym2 V)
    (hex : ∃ (x : V) (p : G.Walk x x), p.IsCycle ∧ e ∈ p.edges) :
    ∃ (x : V) (p : G.Walk x x), p.IsCycle ∧ e ∈ p.edges ∧
      ∀ {y} (q : G.Walk y y), q.IsCycle → e ∈ q.edges → p.length ≤ q.length := by
  classical
  let P (k : ℕ) := ∃ (x : V) (p : G.Walk x x), p.IsCycle ∧ e ∈ p.edges ∧ p.length = k
  have hP : ∃ k, P k := by
    obtain ⟨x, p, hp, he⟩ := hex
    exact ⟨p.length, x, p, hp, he, rfl⟩
  obtain ⟨x, p, hp, he, hlen⟩ := Nat.find_spec hP
  refine ⟨x, p, hp, he, fun q hq hqe => ?_⟩
  rw [hlen]
  exact Nat.find_min' hP ⟨_, q, hq, hqe, rfl⟩

end TreeConjecture
