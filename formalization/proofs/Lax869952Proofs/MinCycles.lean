import Mathlib.Combinatorics.SimpleGraph.Metric

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph

/-- Along a cycle, ambient distances are the lengths of the shorter arcs. -/
def CycleDistances {V : Type*} {G : SimpleGraph V} {r : V} (p : G.Walk r r) : Prop :=
  ∀ a b, a ≤ b → b ≤ p.length →
    G.dist (p.getVert a) (p.getVert b) = min (b - a) (p.length - (b - a))

/-- An isometric cycle, expressed in a form independent of its start and direction.
The walks in the quantifier are traversals of the same undirected cycle. -/
def IsometricCycle {V : Type*} {G : SimpleGraph V} {r : V} (p : G.Walk r r) : Prop :=
  p.IsCycle ∧ ∀ {v} (q : G.Walk v v), q.IsCycle → q.edges.Perm p.edges → CycleDistances q


/-- The shorter of two arcs forming a globally shortest cycle is a shortest path
between its endpoints. -/
theorem shortest_cycle_short_arc {V : Type*} {G : SimpleGraph V} {u v : V}
    {left right : G.Walk u v} (hcycle : (left.append right.reverse).IsCycle)
    (hmin : ∀ {x} (p : G.Walk x x), p.IsCycle → (left.append right.reverse).length ≤ p.length)
    (hshort : left.length ≤ right.length) : G.dist u v = left.length := by
  have hbound := SimpleGraph.dist_le left
  by_contra hne
  have hstrict := lt_of_le_of_ne hbound hne
  by_cases hnil : right.reverse.Nil
  · have hzero := Walk.length_eq_zero_iff.mpr hnil
    rw [Walk.length_reverse] at hzero
    omega
  · have hpath := hcycle.isPath_of_append_left hnil
    obtain ⟨shortcut, hsPath, hsLen⟩ := left.reachable.exists_path_of_dist
    have hsNe : left ≠ shortcut := by
      intro h
      rw [← h] at hsLen
      omega
    obtain ⟨x, _, _, cycle, hc, hlen⟩ := hpath.exists_isCycle_length_le_add_of_ne hsPath hsNe
    have hleast := hmin cycle hc
    rw [Walk.length_append, Walk.length_reverse] at hleast
    omega

/-- The ambient distance between two vertices on a globally shortest cycle
is the length of the shorter arc. The hypotheses exhibit the two arcs. -/
theorem shortest_cycle_distance_of_arcs {V : Type*} {G : SimpleGraph V} {u v : V}
    {left right : G.Walk u v} (hcycle : (left.append right.reverse).IsCycle)
    (hmin : ∀ {x} (p : G.Walk x x), p.IsCycle → (left.append right.reverse).length ≤ p.length) :
    G.dist u v = min left.length right.length := by
  by_cases h : left.length ≤ right.length
  · rw [min_eq_left h]
    exact shortest_cycle_short_arc hcycle hmin h
  · have hright := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right hright]
    have hrev : (right.append left.reverse).IsCycle := by
      simpa only [Walk.reverse_append, Walk.reverse_reverse] using hcycle.reverse
    apply shortest_cycle_short_arc hrev _ hright
    intro x p hp
    simpa only [Walk.length_append, Walk.length_reverse, Nat.add_comm] using hmin p hp

#print axioms shortest_cycle_distance_of_arcs

private lemma cycle_append_swap {V : Type*} {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} {q : G.Walk b a} (h : (p.append q).IsCycle) :
    (q.append p).IsCycle := by
  simp only [Walk.isCycle_def, Walk.isTrail_def, Walk.edges_append, Walk.tail_support_append] at h ⊢
  refine ⟨List.perm_append_comm.nodup_iff.mp h.1, ?_, List.perm_append_comm.nodup_iff.mp h.2.2⟩
  intro hn
  have hparts := Walk.nil_append_iff.mp (Walk.eq_nil_iff_nil.mp hn)
  exact h.2.1 ((Walk.nil_append_iff.mpr hparts.symm).eq_nil)

/-- Cutting a cyclic traversal at two indices gives the two complementary arcs. -/
lemma cycle_index_arcs {V : Type*} {G : SimpleGraph V} {r : V} (p : G.Walk r r)
    (hp : p.IsCycle) {a b : ℕ} (hab : a ≤ b) (hbk : b ≤ p.length) :
    ∃ left right : G.Walk (p.getVert a) (p.getVert b),
      left.length = b - a ∧ right.length = p.length - (b - a) ∧
      (left.append right.reverse).IsCycle ∧ (left.append right.reverse).edges.Perm p.edges := by
  let initial := p.take a
  let rest := p.drop a
  let left := rest.take (b - a)
  let other := (rest.drop (b - a)).append initial
  have hend : rest.getVert (b - a) = p.getVert b := by
    simp only [rest, Walk.drop_getVert, Nat.add_sub_of_le hab]
  have hcat : left.append other = rest.append initial := by
    change (rest.take (b - a)).append ((rest.drop (b - a)).append initial) = _
    rw [Walk.append_assoc, Walk.append_take_drop_eq]
  rw [← hend]
  refine ⟨left, other.reverse, ?_, ?_, ?_, ?_⟩
  · have hle : b - a ≤ rest.length := by
      rw [show rest.length = p.length - a by simp [rest]]
      omega
    change (rest.take (b - a)).length = _
    simp only [Walk.take_length, inf_eq_left.mpr hle]
  · have ha : a ≤ p.length := hab.trans hbk
    simp only [other, rest, initial, Walk.length_reverse, Walk.length_append, Walk.drop_length,
      Walk.take_length, inf_eq_left.mpr ha]
    omega
  · have hp' : (initial.append rest).IsCycle := by
      simpa only [initial, rest, Walk.append_take_drop_eq] using hp
    rw [Walk.reverse_reverse, hcat]
    exact cycle_append_swap hp'
  · have hperm : (rest.append initial).edges.Perm (initial.append rest).edges := by
      simp only [Walk.edges_append]
      exact List.perm_append_comm
    rw [show initial.append rest = p by simp only [initial, rest, Walk.append_take_drop_eq]] at hperm
    rw [Walk.reverse_reverse, hcat]
    exact hperm

/-- A globally shortest cycle is isometric in every cyclic traversal. -/
theorem globally_shortest_cycle_isometric {V : Type*} {G : SimpleGraph V} {r : V}
    (p : G.Walk r r) (hp : p.IsCycle)
    (hmin : ∀ {x} (q : G.Walk x x), q.IsCycle → p.length ≤ q.length) : IsometricCycle p := by
  refine ⟨hp, fun q hq hperm a b hab hb => ?_⟩
  obtain ⟨left, right, hl, hr, hloop, hloopPerm⟩ := cycle_index_arcs q hq hab hb
  have length_eq : (left.append right.reverse).length = p.length := by
    simpa only [Walk.length_edges] using (hloopPerm.trans hperm).length_eq
  have hd := shortest_cycle_distance_of_arcs hloop (fun w hw => length_eq.symm ▸ hmin w hw)
  simpa only [hl, hr] using hd

#print axioms globally_shortest_cycle_isometric

end Lax869952Proofs
