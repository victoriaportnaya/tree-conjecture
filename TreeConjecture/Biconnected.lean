import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A vertex set of size at least three whose induced graph stays
connected after removing any one vertex. Walks use the ambient vertex type. -/
structure TwoConnectedOn (G : SimpleGraph V) (S : Finset V) : Prop where
  card_ge_three : 3 ≤ S.card
  walk (z : V) {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ p : G.Walk x y, (∀ a ∈ p.support, a ∈ S) ∧ z ∉ p.support

/-- A maximal induced two-connected vertex set. Bridge blocks are excluded. -/
structure IsBiconnectedBlock (G : SimpleGraph V) (S : Finset V) : Prop where
  twoConnected : TwoConnectedOn G S
  maximal (T : Finset V) : S ⊆ T → TwoConnectedOn G T → T ⊆ S

/-- The induced subgraph on the specified vertices, retaining the ambient
type so the original players and edge purchases can be used. -/
def blockGraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph V :=
  ((⊤ : G.Subgraph).induce (↑S : Set V)).spanningCoe

@[simp]
lemma blockGraph_adj {S : Finset V} {a b : V} :
    (blockGraph G S).Adj a b ↔ a ∈ S ∧ b ∈ S ∧ G.Adj a b := Iff.rfl

lemma blockGraph_le (G : SimpleGraph V) (S : Finset V) : blockGraph G S ≤ G :=
  ((⊤ : G.Subgraph).induce (↑S : Set V)).spanningCoe_le

variable [DecidableEq V]

private lemma walk_between_support {a b x y : V} (p : G.Walk a b)
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    ∃ q : G.Walk x y, q.support ⊆ p.support := by
  refine ⟨(p.takeUntil x hx).reverse.append (p.takeUntil y hy), ?_⟩
  intro z hz
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hz
  exact hz.elim (fun h => p.support_takeUntil_subset_support hx h)
    (fun h => p.support_takeUntil_subset_support hy h)

/-- The vertices of any simple cycle form a two-connected induced subgraph. -/
theorem twoConnectedOn_cycle {r : V} (p : G.Walk r r) (hp : p.IsCycle) :
    TwoConnectedOn G p.support.toFinset := by
  constructor
  · have hs : p.support.dropLast.toFinset ⊆ p.support.toFinset := by
      intro x hx
      exact List.mem_toFinset.mpr (List.dropLast_subset _ (List.mem_toFinset.mp hx))
    have hcard := Finset.card_le_card hs
    rw [List.toFinset_card_of_nodup hp.nodup_dropLast_support, List.length_dropLast,
      Walk.length_support] at hcard
    have hlen := hp.three_le_length
    omega
  · intro z x y hx hy hxz hyz
    have hxp := List.mem_toFinset.mp hx
    have hyp := List.mem_toFinset.mp hy
    by_cases hm : z ∈ p.support
    · let q := p.rotate z hm
      have hq : q.IsCycle := hp.rotate hm
      have hqn : ¬ q.tail.Nil := by
        apply Walk.not_nil_iff_lt_length.mpr
        rw [Walk.length_tail]
        have hlen := hq.three_le_length
        omega
      let w := q.tail.dropLast
      have hcut : w.support ++ [z] = q.support.tail := by
        exact (Walk.support_dropLast_concat hqn).trans (q.support_tail_of_not_nil hq.not_nil)
      have havoid : z ∉ w.support := by
        have hnodup := hq.support_nodup
        rw [← hcut] at hnodup
        exact fun h => (List.disjoint_of_nodup_append hnodup) h (List.mem_singleton.mpr rfl)
      have hmem {a : V} (ha : a ∈ p.support) (haz : a ≠ z) : a ∈ w.support := by
        have hqa := (p.mem_support_rotate_iff z hm).mpr ha
        have hTail := (q.mem_support_iff.mp hqa).resolve_left haz
        rw [← hcut, List.mem_append, List.mem_singleton] at hTail
        exact hTail.resolve_right haz
      obtain ⟨walk, hwalk⟩ := walk_between_support w (hmem hxp hxz) (hmem hyp hyz)
      refine ⟨walk, ?_, fun h => havoid (hwalk h)⟩
      intro a ha
      have htail : a ∈ q.support.tail := hcut ▸ List.mem_append_left [z] (hwalk ha)
      exact List.mem_toFinset.mpr ((p.mem_support_rotate_iff z hm).mp (List.mem_of_mem_tail htail))
    · obtain ⟨walk, hw⟩ := walk_between_support p hxp hyp
      exact ⟨walk, fun _ ha => List.mem_toFinset.mpr (hw ha), fun h => hm (hw h)⟩

/-- Two two-connected sets with two common vertices have two-connected union. -/
theorem TwoConnectedOn.union {S T : Finset V} (hS : TwoConnectedOn G S)
    (hT : TwoConnectedOn G T) {a b : V} (haS : a ∈ S) (haT : a ∈ T)
    (hbS : b ∈ S) (hbT : b ∈ T) (hab : a ≠ b) : TwoConnectedOn G (S ∪ T) := by
  constructor
  · exact hS.card_ge_three.trans (Finset.card_le_card Finset.subset_union_left)
  · intro z x y hx hy hxz hyz
    obtain ⟨c, hcS, hcT, hcz⟩ : ∃ c, c ∈ S ∧ c ∈ T ∧ c ≠ z := by
      by_cases haz : a = z
      · exact ⟨b, hbS, hbT, fun h => hab (haz.trans h.symm)⟩
      · exact ⟨a, haS, haT, haz⟩
    have route {v : V} (hv : v ∈ S ∪ T) (hvz : v ≠ z) :
        ∃ p : G.Walk v c, (∀ k ∈ p.support, k ∈ S ∪ T) ∧ z ∉ p.support := by
      rcases Finset.mem_union.mp hv with hs | ht
      · obtain ⟨p, hp, hz⟩ := hS.walk z hs hcS hvz hcz
        exact ⟨p, fun _ hk => Finset.mem_union_left T (hp _ hk), hz⟩
      · obtain ⟨p, hp, hz⟩ := hT.walk z ht hcT hvz hcz
        exact ⟨p, fun _ hk => Finset.mem_union_right S (hp _ hk), hz⟩
    obtain ⟨p, hp, hzp⟩ := route hx hxz
    obtain ⟨q, hq, hzq⟩ := route hy hyz
    refine ⟨p.append q.reverse, ?_, by simp [Walk.mem_support_append_iff, hzp, hzq]⟩
    intro k hk
    rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hk
    exact hk.elim (hp k) (hq k)

/-- Any finite two-connected vertex set extends to a maximal block. -/
theorem exists_biconnectedBlock_superset [Fintype V] {S : Finset V} (hS : TwoConnectedOn G S) :
    ∃ T, S ⊆ T ∧ IsBiconnectedBlock G T := by
  classical
  let candidates := (Finset.univ : Finset V).powerset.filter
    (fun T => S ⊆ T ∧ TwoConnectedOn G T)
  have hcandidates : candidates.Nonempty := ⟨S, by simp [candidates, hS]⟩
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image candidates Finset.card hcandidates
  have ⟨hst, ht⟩ : S ⊆ T ∧ TwoConnectedOn G T := by simpa [candidates] using hT
  refine ⟨T, hst, ht, ?_⟩
  intro U htu hu
  have hU : U ∈ candidates := by simp [candidates, hst.trans htu, hu]
  exact (Finset.eq_of_subset_of_card_le htu (hmax U hU)).symm.subset

/-- A graph containing a cycle has a block of maximum cardinality. -/
theorem exists_largest_biconnectedBlock [Fintype V] {r : V} (p : G.Walk r r) (hp : p.IsCycle) :
    ∃ S, IsBiconnectedBlock G S ∧ ∀ T, TwoConnectedOn G T → T.card ≤ S.card := by
  classical
  let candidates := (Finset.univ : Finset V).powerset.filter (TwoConnectedOn G)
  have hcandidates : candidates.Nonempty :=
    ⟨p.support.toFinset, by simp [candidates, twoConnectedOn_cycle p hp]⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image candidates Finset.card hcandidates
  have hS' : TwoConnectedOn G S := by simpa [candidates] using hS
  have hlarge (T : Finset V) (hT : TwoConnectedOn G T) : T.card ≤ S.card :=
    hmax T (by simp [candidates, hT])
  exact ⟨S, ⟨hS', fun T hst ht => (Finset.eq_of_subset_of_card_le hst (hlarge T ht)).symm.subset⟩,
    hlarge⟩

/-- A cycle sharing two vertices with a maximal block is contained in it. -/
theorem IsBiconnectedBlock.cycle_support_subset {S : Finset V} (hS : IsBiconnectedBlock G S)
    {r a b : V} (p : G.Walk r r) (hp : p.IsCycle) (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) (hap : a ∈ p.support) (hbp : b ∈ p.support) :
    ∀ x ∈ p.support, x ∈ S := by
  have hu := hS.twoConnected.union (twoConnectedOn_cycle p hp)
    ha (List.mem_toFinset.mpr hap) hb (List.mem_toFinset.mpr hbp) hab
  intro x hx
  exact hS.maximal _ Finset.subset_union_left hu (Finset.mem_union_right S (List.mem_toFinset.mpr hx))

/-- In particular, a maximal block contains every cycle through any of its edges. -/
theorem IsBiconnectedBlock.cycle_edges_subset {S : Finset V} (hS : IsBiconnectedBlock G S)
    {r a b : V} (p : G.Walk r r) (hp : p.IsCycle)
    (hab : (blockGraph G S).Adj a b) (he : s(a, b) ∈ p.edges) :
    ∀ e ∈ p.edges, e ∈ (blockGraph G S).edgeSet := by
  have hs := hS.cycle_support_subset p hp hab.1 hab.2.1 (blockGraph_le G S hab).ne
    (p.fst_mem_support_of_mem_edges he) (p.snd_mem_support_of_mem_edges he)
  rintro e
  induction e using Sym2.ind with
  | h x y =>
    intro he'
    exact ⟨hs x (p.fst_mem_support_of_mem_edges he'), hs y (p.snd_mem_support_of_mem_edges he'),
      p.adj_of_mem_edges he'⟩

/-- Distinct maximal blocks share at most one vertex. -/
theorem IsBiconnectedBlock.eq_of_two_vertices {S T : Finset V}
    (hS : IsBiconnectedBlock G S) (hT : IsBiconnectedBlock G T)
    {a b : V} (haS : a ∈ S) (haT : a ∈ T) (hbS : b ∈ S) (hbT : b ∈ T) (hab : a ≠ b) :
    S = T := by
  have hu := hS.twoConnected.union hT.twoConnected haS haT hbS hbT hab
  have hs := hS.maximal _ Finset.subset_union_left hu
  have ht := hT.maximal _ Finset.subset_union_right hu
  exact Finset.Subset.antisymm (Finset.subset_union_left.trans ht)
    (Finset.subset_union_right.trans hs)

/-- A cycle edge belongs to a unique maximal block. -/
theorem exists_unique_block_of_cycle_edge [Fintype V]
    {r a b : V} (p : G.Walk r r) (hp : p.IsCycle) (he : s(a, b) ∈ p.edges) :
    ∃! S, IsBiconnectedBlock G S ∧ (blockGraph G S).Adj a b := by
  obtain ⟨S, hs, hS⟩ := exists_biconnectedBlock_superset (twoConnectedOn_cycle p hp)
  have ha := hs (List.mem_toFinset.mpr (p.fst_mem_support_of_mem_edges he))
  have hb := hs (List.mem_toFinset.mpr (p.snd_mem_support_of_mem_edges he))
  have hab := p.adj_of_mem_edges he
  refine ⟨S, ⟨hS, ha, hb, hab⟩, ?_⟩
  rintro T ⟨hT, hAdj⟩
  exact hT.eq_of_two_vertices hS hAdj.1 ha hAdj.2.1 hb hab.ne

#print axioms twoConnectedOn_cycle
#print axioms exists_largest_biconnectedBlock
#print axioms IsBiconnectedBlock.cycle_edges_subset
#print axioms exists_unique_block_of_cycle_edge

end TreeConjecture
