import TreeConjecture.Biconnected
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

private lemma path_to_surviving_endpoint {x a b z : V} (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∈ p.support) (hxz : x ≠ z) :
    (∃ q : G.Walk x a, q.support ⊆ p.support ∧ z ∉ q.support) ∨
      (∃ q : G.Walk x b, q.support ⊆ p.support ∧ z ∉ q.support) := by
  obtain ⟨l, r, hpEq⟩ := p.mem_support_iff_exists_append.mp hx
  have hpath := hpEq ▸ hp
  have hl : l.support ⊆ p.support := by
    intro y hy
    rw [hpEq, Walk.mem_support_append_iff]
    exact Or.inl hy
  have hr : r.support ⊆ p.support := by
    intro y hy
    rw [hpEq, Walk.mem_support_append_iff]
    exact Or.inr hy
  by_cases hz : z ∈ l.support
  · exact Or.inr ⟨r, hr, fun h => hpath.ne_of_mem_support_of_append hxz.symm hz h rfl⟩
  · refine Or.inl ⟨l.reverse, ?_, by simpa using hz⟩
    intro y hy
    exact hl (by simpa using hy)

/-- Adding a path with both endpoints inside a two-connected set
preserves two-connectivity on the union. -/
theorem TwoConnectedOn.adjoin_path {S : Finset V} (hS : TwoConnectedOn G S)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (p : G.Walk a b) (hp : p.IsPath) :
    TwoConnectedOn G (S ∪ p.support.toFinset) := by
  constructor
  · exact hS.card_ge_three.trans (Finset.card_le_card Finset.subset_union_left)
  · intro z x y hx hy hxz hyz
    let U := S ∪ p.support.toFinset
    have fromPath {w c : V} (hc : c ∈ S) (q : G.Walk w c)
        (hq : q.support ⊆ p.support) (hz : z ∉ q.support) :
        ∃ d ∈ S, d ≠ z ∧ ∃ t : G.Walk w d, (∀ k ∈ t.support, k ∈ U) ∧ z ∉ t.support := by
      refine ⟨c, hc, fun h => hz (h ▸ q.end_mem_support), q, ?_, hz⟩
      exact fun _ hk => Finset.mem_union_right S (List.mem_toFinset.mpr (hq hk))
    have route {w : V} (hw : w ∈ U) (hwz : w ≠ z) :
        ∃ c ∈ S, c ≠ z ∧ ∃ q : G.Walk w c, (∀ k ∈ q.support, k ∈ U) ∧ z ∉ q.support := by
      rcases Finset.mem_union.mp hw with hwS | hwp
      · exact ⟨w, hwS, hwz, .nil, by simp [U, hwS], by simp [hwz.symm]⟩
      · rcases path_to_surviving_endpoint p hp (List.mem_toFinset.mp hwp) hwz with
          ⟨q, hq, hqz⟩ | ⟨q, hq, hqz⟩
        · exact fromPath ha q hq hqz
        · exact fromPath hb q hq hqz
    obtain ⟨c, hc, hcz, q₁, hq₁, hq₁z⟩ := route hx hxz
    obtain ⟨d, hd, hdz, q₂, hq₂, hq₂z⟩ := route hy hyz
    obtain ⟨t, ht, htz⟩ := hS.walk z hc hd hcz hdz
    refine ⟨q₁.append (t.append q₂.reverse), ?_, ?_⟩
    · intro k hk
      simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hk
      exact hk.elim (hq₁ k) (fun h => h.elim (fun h => Finset.mem_union_left _ (ht k h)) (hq₂ k))
    · simp [Walk.mem_support_append_iff, hq₁z, hq₂z, htz]

/-- All simple paths with both endpoints in the block remain in the block. -/
theorem IsBiconnectedBlock.path_support_subset {S : Finset V} (hS : IsBiconnectedBlock G S)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (p : G.Walk a b) (hp : p.IsPath) :
    ∀ k ∈ p.support, k ∈ S := by
  have hu := hS.twoConnected.adjoin_path ha hb p hp
  intro x hx
  exact hS.maximal _ Finset.subset_union_left hu (Finset.mem_union_right _ (List.mem_toFinset.mpr hx))

/-- Every shortest path between two block vertices stays in the block. -/
theorem IsBiconnectedBlock.shortest_path_support_subset {S : Finset V}
    (hS : IsBiconnectedBlock G S) {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (p : G.Walk a b) (hp : p.length = G.dist a b) : ∀ k ∈ p.support, k ∈ S :=
  hS.path_support_subset ha hb p (p.isPath_of_length_eq_dist hp)

/-- A walk meets the given vertex set only at its terminal vertex. -/
def FirstEntryInto (S : Finset V) {x y : V} (p : G.Walk x y) : Prop :=
  ∀ a ∈ p.support, a ∈ S → a = y

/-- Truncate a walk at the first vertex of a specified set. -/
theorem exists_first_entry_walk {S : Finset V} {x y : V} (p : G.Walk x y) (hy : y ∈ S) :
    ∃ a ∈ S, ∃ q : G.Walk x a, q.support ⊆ p.support ∧ FirstEntryInto S q := by
  induction p with
  | nil => exact ⟨_, hy, .nil, fun _ h => h, by simp [FirstEntryInto]⟩
  | @cons a b c hab p ih =>
    by_cases ha : a ∈ S
    · refine ⟨a, ha, .nil, ?_, by simp [FirstEntryInto]⟩
      intro k hk
      have he : k = a := by simpa using hk
      subst k
      exact (Walk.cons hab p).start_mem_support
    · obtain ⟨d, hd, q, hq, hentry⟩ := ih hy
      refine ⟨d, hd, .cons hab q, ?_, ?_⟩
      · intro k hk
        simp only [Walk.support_cons, List.mem_cons] at hk ⊢
        exact hk.imp id (fun h => hq h)
      · intro k hk hkS
        rw [Walk.support_cons, List.mem_cons] at hk
        rcases hk with rfl | hk
        · exact (ha hkS).elim
        · exact hentry k hk hkS

/-- Two walks from the same vertex cannot first enter a maximal block
at different vertices. -/
theorem IsBiconnectedBlock.first_entry_unique {S : Finset V} (hS : IsBiconnectedBlock G S)
    {x a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (p : G.Walk x a) (q : G.Walk x b) (hp : FirstEntryInto S p) (hq : FirstEntryInto S q) :
    a = b := by
  by_contra hab
  let pq := p.reverse.append q
  let r := pq.bypass
  have hrn : ¬ r.Nil := Walk.not_nil_of_ne hab
  have hs := hS.path_support_subset ha hb r pq.bypass_isPath
  have hes := r.mk_start_snd_mem_edges hrn
  have hzInS := hs r.snd (r.snd_mem_support_of_mem_edges hes)
  have hzInPQ := pq.support_bypass_subset_support (r.snd_mem_support_of_mem_edges hes)
  change r.snd ∈ (p.reverse.append q).support at hzInPQ
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hzInPQ
  have hz : r.snd = b := by
    rcases hzInPQ with hz | hz
    · exact ((r.adj_snd hrn).ne (hp r.snd hz hzInS).symm).elim
    · exact hq r.snd hz hzInS
  have hes' : s(a, b) ∈ r.edges := by simpa only [hz] using hes
  have he := pq.edges_bypass_subset_edges hes'
  change s(a, b) ∈ (p.reverse.append q).edges at he
  rw [Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse] at he
  rcases he with he | he
  · exact hab (hp b (p.snd_mem_support_of_mem_edges he) hb).symm
  · exact hab (hq a (q.fst_mem_support_of_mem_edges he) ha)

/-- A connected ambient graph has a unique entry vertex for each block
and each starting vertex. -/
theorem IsBiconnectedBlock.exists_unique_entry {S : Finset V} (hS : IsBiconnectedBlock G S)
    (hG : G.Connected) (x : V) :
    ∃! y, y ∈ S ∧ ∃ p : G.Walk x y, FirstEntryInto S p := by
  have hcard := hS.twoConnected.card_ge_three
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨q⟩ := hG x a
  obtain ⟨y, hy, p, _, hp⟩ := exists_first_entry_walk q ha
  refine ⟨y, ⟨hy, p, hp⟩, ?_⟩
  rintro z ⟨hz, q, hq⟩
  exact hS.first_entry_unique hz hy q p hq hp

private lemma TwoConnectedOn.exists_adj_avoiding {S : Finset V} (hS : TwoConnectedOn G S)
    {v z : V} (hv : v ∈ S) (hvz : v ≠ z) :
    ∃ w, (blockGraph G S).Adj v w ∧ w ≠ z := by
  have hcard := hS.card_ge_three
  have hrest := Finset.pred_card_le_card_erase (s := S) (a := z)
  obtain ⟨y, hy, hyv⟩ := (S.erase z).exists_mem_ne (by omega) v
  obtain ⟨hyz, hyS⟩ := Finset.mem_erase.mp hy
  obtain ⟨p, hp, hz⟩ := hS.walk z hv hyS hvz hyz
  have hn := Walk.not_nil_of_ne (p := p) hyv.symm
  have hw := p.snd_mem_support_of_mem_edges (p.mk_start_snd_mem_edges hn)
  exact ⟨p.snd, ⟨hv, hp _ hw, p.adj_snd hn⟩, fun h => hz (h ▸ hw)⟩

/-- Every vertex in a two-connected set has two distinct neighbors there. -/
theorem TwoConnectedOn.exists_two_neighbors {S : Finset V} (hS : TwoConnectedOn G S)
    {v : V} (hv : v ∈ S) :
    ∃ u w, (blockGraph G S).Adj v u ∧ (blockGraph G S).Adj v w ∧ u ≠ w := by
  have hcard := hS.card_ge_three
  obtain ⟨z, _, hzv⟩ := S.exists_mem_ne (by omega) v
  obtain ⟨u, hu, _⟩ := hS.exists_adj_avoiding hv hzv.symm
  obtain ⟨w, hw, hwu⟩ := hS.exists_adj_avoiding hv hu.ne
  exact ⟨u, w, hu, hw, hwu.symm⟩

/-- Every block vertex has degree at least two in the induced block. -/
theorem IsBiconnectedBlock.two_le_degree {S : Finset V}
    (hS : IsBiconnectedBlock G S) {v : V} (hv : v ∈ S)
    [Fintype ((blockGraph G S).neighborSet v)] : 2 ≤ (blockGraph G S).degree v := by
  obtain ⟨u, w, hu, hw, huw⟩ := hS.twoConnected.exists_two_neighbors hv
  have hsub : ({u, w} : Finset V) ⊆ (blockGraph G S).neighborFinset v := by
    intro a ha
    rcases (show a = u ∨ a = w by simpa using ha) with hau | haw
    · exact ((blockGraph G S).mem_neighborFinset v a).mpr (hau.symm ▸ hu)
    · exact ((blockGraph G S).mem_neighborFinset v a).mpr (haw.symm ▸ hw)
  simpa [huw] using Finset.card_le_card hsub

/-- A vertex of a two-connected set belongs to a cycle in the induced graph. -/
theorem TwoConnectedOn.exists_cycle_at {S : Finset V} (hS : TwoConnectedOn G S)
    {v : V} (hv : v ∈ S) : ∃ c : (blockGraph G S).Walk v v, c.IsCycle := by
  obtain ⟨u, w, hu, hw, huw⟩ := hS.exists_two_neighbors hv
  obtain ⟨p, hp, havoid⟩ := hS.walk v hu.2.1 hw.2.1 hu.ne.symm hw.ne.symm
  have keep (e : Sym2 V) (he : e ∈ p.bypass.edges) : e ∈ (blockGraph G S).edgeSet := by
    induction e using Sym2.ind with
    | h a b =>
      exact ⟨hp _ (p.support_bypass_subset_support (p.bypass.fst_mem_support_of_mem_edges he)),
        hp _ (p.support_bypass_subset_support (p.bypass.snd_mem_support_of_mem_edges he)),
        p.bypass.adj_of_mem_edges he⟩
  let q := p.bypass.transfer _ keep
  have hq : q.IsPath := p.bypass_isPath.transfer keep
  have hqv : v ∉ q.support := by
    intro h
    exact havoid (p.support_bypass_subset_support (by simpa only [q, Walk.support_transfer] using h))
  let tail := q.concat hw.symm
  have ht : tail.IsPath := (Walk.concat_isPath_iff hw.symm).mpr ⟨hq, hqv⟩
  have he : s(v, u) ∉ tail.edges := by
    intro h
    change s(v, u) ∈ (q.concat hw.symm).edges at h
    rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · exact hqv (q.fst_mem_support_of_mem_edges h)
    · rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨_, h⟩
      · exact hw.ne h
      · exact huw h
  exact ⟨.cons hu tail, (Walk.cons_isCycle_iff tail hu).mpr ⟨ht, he⟩⟩

/-- Within the block, there is a shortest cycle through each vertex. -/
theorem IsBiconnectedBlock.exists_shortest_cycle_at {S : Finset V} (hS : IsBiconnectedBlock G S)
    {v : V} (hv : v ∈ S) :
    ∃ c : (blockGraph G S).Walk v v, c.IsCycle ∧
      ∀ p : (blockGraph G S).Walk v v, p.IsCycle → c.length ≤ p.length := by
  classical
  let P (k : ℕ) := ∃ p : (blockGraph G S).Walk v v, p.IsCycle ∧ p.length = k
  obtain ⟨p, hp⟩ := hS.twoConnected.exists_cycle_at hv
  have hex : ∃ k, P k := ⟨p.length, p, hp, rfl⟩
  obtain ⟨c, hc, hlen⟩ := Nat.find_spec hex
  refine ⟨c, hc, fun q hq => ?_⟩
  rw [hlen]
  exact Nat.find_min' hex ⟨q, hq, rfl⟩

#print axioms IsBiconnectedBlock.path_support_subset
#print axioms IsBiconnectedBlock.exists_unique_entry
#print axioms IsBiconnectedBlock.two_le_degree
#print axioms IsBiconnectedBlock.exists_shortest_cycle_at

end TreeConjecture
