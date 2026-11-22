import Lax869952Proofs.BlockPaths

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A reachable point of a nonempty set can be reached in at most as many
steps as there are vertices outside the set. -/
theorem exists_near_vertex_in_finset {G : SimpleGraph V} {S : Finset V} {x y : V}
    (hy : y ∈ S) (hReach : G.Reachable x y) :
    ∃ z ∈ S, G.dist x z ≤ (Finset.univ \ S).card := by
  obtain ⟨p⟩ := hReach
  obtain ⟨z, hz, q, _, hEntry⟩ := exists_first_entry_walk p hy
  let r := q.bypass
  have hPath : r.IsPath := q.bypass_isPath
  have hSub : r.support.toFinset ⊆ insert z (Finset.univ \ S) := by
    intro t ht
    have hMem := q.support_bypass_subset_support (List.mem_toFinset.mp ht)
    by_cases htS : t ∈ S
    · exact Finset.mem_insert.mpr (Or.inl (hEntry t hMem htS))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, htS⟩))
  have hCard := Finset.card_le_card hSub
  rw [List.toFinset_card_of_nodup hPath.support_nodup, Walk.length_support,
    Finset.card_insert_of_notMem (by simp [hz])] at hCard
  exact ⟨z, hz, (dist_le r).trans (by omega)⟩

/-- Adding vertices and edges can increase the distance from an original
vertex by at most the number of vertices added, relative to its original
maximum distance. -/
theorem dist_le_original_bound_add_card {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : H.Connected) {S : Finset V} {x : V} (hx : x ∈ S)
    {E : ℕ} (hOriginal : ∀ z ∈ S, G.Reachable x z ∧ G.dist x z ≤ E) (y : V) :
    H.dist x y ≤ E + (Finset.univ \ S).card := by
  obtain ⟨z, hz, hNear⟩ := exists_near_vertex_in_finset hx (hH y x)
  have hXZ := ((hOriginal z hz).1.dist_anti hGH).trans (hOriginal z hz).2
  have hTriangle : H.dist x y ≤ H.dist x z + H.dist z y := hH.dist_triangle
  rw [dist_comm (u := z) (v := y)] at hTriangle
  omega

/-- If an ear can reach an original vertex, its original distance bound
plus the remaining vertex budget plus one must reach the girth. -/
theorem girth_le_original_bound_add_ear_budget {G H K : SimpleGraph V}
    (hGH : G ≤ H) (hHK : H ≤ K) (hH : H.Connected)
    {S : Finset V} {x y : V} (hx : x ∈ S) {E R g : ℕ}
    (hOriginal : ∀ z ∈ S, G.Reachable x z ∧ G.dist x z ≤ E)
    (girth : ∀ {u}, (p : K.Walk u u) → p.IsCycle → g ≤ p.length)
    (p : H.Walk x y) (hShortest : p.length = H.dist x y)
    (q : K.Walk y x) (hEar : q.IsPath)
    (hDisjoint : (p.mapLe hHK).support.tail.Disjoint q.support.tail)
    (hDistinct : 1 < p.length ∨ 1 < q.length)
    (hBudget : (Finset.univ \ S).card + q.length ≤ R + 1) :
    g ≤ E + R + 1 := by
  have hPath := (p.isPath_of_length_eq_dist hShortest).mapLe hHK
  have hLong : 1 < (p.mapLe hHK).length ∨ 1 < q.length := by
    simpa only [Walk.length_mapLe] using hDistinct
  have hCycle := girth ((p.mapLe hHK).append q) (hPath.isCycle_append hEar hDisjoint hLong)
  rw [Walk.length_append, Walk.length_mapLe, hShortest] at hCycle
  have hDist := dist_le_original_bound_add_card hGH hH hx hOriginal y
  omega

#print axioms girth_le_original_bound_add_ear_budget

omit [Fintype V] in
/-- An edge out of an old vertex in a two-connected extension can start
an ear to another old vertex. If its neighbour is already old, the ear
can consist of that edge alone. -/
theorem TwoConnectedOn.exists_ear_with_first_edge {K : SimpleGraph V} {S T : Finset V}
    (hT : TwoConnectedOn K T) (hST : S ⊆ T) (hCard : 2 ≤ S.card)
    {x y : V} (hy : y ∈ T) (hxy : K.Adj x y) :
    ∃ z ∈ S, z ≠ x ∧ ∃ q : K.Walk y z, (Walk.cons hxy q).IsPath ∧
      (∀ a ∈ q.support, a ∈ T) ∧ FirstEntryInto S q := by
  obtain ⟨w, hw, hwx⟩ := S.exists_mem_ne (by omega) x
  obtain ⟨p, hp, hAvoid⟩ := hT.walk x hy (hST hw) hxy.ne.symm hwx
  obtain ⟨z, hz, t, hSub, hEntry⟩ := exists_first_entry_walk p hw
  let q := t.bypass
  have hSupport : q.support ⊆ p.support :=
    fun _ ha => hSub (t.support_bypass_subset_support ha)
  refine ⟨z, hz, fun he => hAvoid (he ▸ hSupport q.end_mem_support), q,
    t.bypass_isPath.cons (fun h => hAvoid (hSupport h)), fun a ha => hp a (hSupport ha), ?_⟩
  exact fun a ha has => hEntry a (t.support_bypass_subset_support ha) has

#print axioms TwoConnectedOn.exists_ear_with_first_edge

end Lax869952Proofs
