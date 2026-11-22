import Lax869952Proofs.BlockPaths
import Lax869952Proofs.DegreeTwo

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

variable {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}

/-- The vertices whose first entry into the block is at the given vertex.
This is the set `S_H(v)` in Dippel–Vetta when the vertex belongs to the block. -/
noncomputable def blockAttachment (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun x => ∃ p : G.Walk x v, FirstEntryInto S p)

@[simp]
theorem mem_blockAttachment {x v : Fin n} :
    x ∈ blockAttachment G S v ↔ ∃ p : G.Walk x v, FirstEntryInto S p := by
  classical
  simp [blockAttachment]

private theorem nearest_is_first_entry {x v : Fin n} (p : G.Walk x v)
    (hp : p.length = G.dist x v) (hmin : ∀ y ∈ S, G.dist x v ≤ G.dist x y) :
    FirstEntryInto S p := by
  intro y hyp hyS
  by_contra hyv
  obtain ⟨l, r, he⟩ := p.mem_support_iff_exists_append.mp hyp
  have hrl : 0 < r.length := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hyv)
  have hmin' := (hmin y hyS).trans (dist_le l)
  rw [he, Walk.length_append] at hp
  omega

/-- First entry into a maximal block is equivalent to being a nearest
block vertex. In particular all shortest paths to the block enter there. -/
theorem IsBiconnectedBlock.mem_blockAttachment_iff_nearest (hS : IsBiconnectedBlock G S)
    (hG : G.Connected) {x v : Fin n} (hv : v ∈ S) :
    x ∈ blockAttachment G S v ↔ ∀ y ∈ S, G.dist x v ≤ G.dist x y := by
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := mem_blockAttachment.mp hx
    obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image S (G.dist x) ⟨v, hv⟩
    obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist x y
    have hEq := hS.first_entry_unique hv hy p q hp (nearest_is_first_entry q hq hmin)
    simpa only [hEq] using hmin
  · intro hmin
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x v
    exact mem_blockAttachment.mpr ⟨p, nearest_is_first_entry p hp hmin⟩

/-- Deleting a block vertex separates exactly its attached vertices from
every other vertex of the same block. -/
theorem IsBiconnectedBlock.separatedVertices_eq_blockAttachment (hS : IsBiconnectedBlock G S)
    (hG : G.Connected) {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    separatedVertices G u v = blockAttachment G S v := by
  ext x
  rw [mem_separatedVertices, mem_blockAttachment]
  constructor
  · intro hsep
    obtain ⟨y, ⟨hy, p, hp⟩, _⟩ := hS.exists_unique_entry hG x
    by_cases hyv : y = v
    · subst y
      exact ⟨p, hp⟩
    · have hpv : v ∉ p.support := fun h => hyv (hp v h hv).symm
      obtain ⟨q, _, hqv⟩ := hS.twoConnected.walk v hu hy huv hyv
      exact (hsep ⟨q.append p.reverse, by simp [Walk.mem_support_append_iff, hqv, hpv]⟩).elim
  · rintro ⟨p, hp⟩ ⟨q, hq⟩
    obtain ⟨y, hy, t, ht, htEntry⟩ := exists_first_entry_walk q.reverse hu
    have he := hS.first_entry_unique hv hy p t hp htEntry
    have hx := ht t.end_mem_support
    rw [Walk.support_reverse, List.mem_reverse, ← he] at hx
    exact hq hx

/-- Distinct vertices of the same block have disjoint attachment sets. -/
theorem IsBiconnectedBlock.disjoint_blockAttachments (hS : IsBiconnectedBlock G S)
    {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    Disjoint (blockAttachment G S u) (blockAttachment G S v) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨p, hp⟩ := mem_blockAttachment.mp hx
  obtain ⟨q, hq⟩ := mem_blockAttachment.mp hy
  exact huv (hS.first_entry_unique hu hv p q hp hq)

/-- The degree-two bound applied to a maximal block. The cycle containment
required by the deviation argument follows from maximality. -/
theorem nash_degree_two_maximal_block (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    [DecidableRel (blockGraph (graph s) S).Adj] (hS : IsBiconnectedBlock (graph s) S)
    {u v w : Fin n} (huv : (blockGraph (graph s) S).Adj v u)
    (hvw : (blockGraph (graph s) S).Adj v w) (hdegree : (blockGraph (graph s) S).degree v = 2)
    (huvBuy : v ∈ (s u).val) (hvwBuy : w ∈ (s v).val)
    (c : (blockGraph (graph s) S).Walk v v) (hc : c.IsCycle) :
    (verticesViaTwoSteps (graph s) u w).card ≤ (blockAttachment (graph s) S v).card ∧
      (α : ℝ) ≤ 2 * ((c.length : ℝ) - 3) * ((blockAttachment (graph s) S v).card : ℝ) := by
  have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have hA := hS.separatedVertices_eq_blockAttachment hG huv.2.1 huv.1
    (blockGraph_le (graph s) S huv).ne.symm
  rw [← hA]
  exact nash_degree_two_cycle_bound s α hne hα (blockGraph (graph s) S)
    (blockGraph_le (graph s) S) huv hvw hdegree huvBuy hvwBuy
    (fun p hp he => hS.cycle_edges_subset p hp huv.symm he) c hc

/-- A degree-two vertex receiving a purchase from either neighbor
has a price-dependent lower bound on its attachment size. -/
theorem nash_receiver_cycle_bound (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s)
    [DecidableRel (blockGraph (graph s) S).Adj] (hS : IsBiconnectedBlock (graph s) S)
    {u v w : Fin n} (huv : (blockGraph (graph s) S).Adj v u)
    (hvw : (blockGraph (graph s) S).Adj v w) (huw : u ≠ w)
    (hdegree : (blockGraph (graph s) S).degree v = 2) (huvBuy : v ∈ (s u).val)
    (c : (blockGraph (graph s) S).Walk v v) (hc : c.IsCycle) (hcLen : 4 ≤ c.length) :
    (α : ℝ) ≤ 2 * ((c.length : ℝ) - 3) * ((blockAttachment (graph s) S v).card : ℝ) := by
  have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  rw [← hS.separatedVertices_eq_blockAttachment hG huv.2.1 huv.1
    (blockGraph_le (graph s) S huv).ne.symm]
  exact (nash_degree_two_cycle_bound_of_adj s α hne _ (blockGraph_le (graph s) S)
    huv hvw hdegree huvBuy huw (fun p hp he => hS.cycle_edges_subset p hp huv.symm he)
    c hc hcLen).2

/-- The downward-branch estimate of Lemma 9, with the attachment set of
the maximal block. -/
theorem nash_degree_two_block_down_branch (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    [DecidableRel (blockGraph (graph s) S).Adj] (hS : IsBiconnectedBlock (graph s) S)
    {root u v w : Fin n} (T : ShortestParents (graph s) root)
    (hv : v ≠ root) (hw : w ≠ root) (hvu : T.parent v = u) (hwv : T.parent w = v)
    (huv : (blockGraph (graph s) S).Adj v u)
    (hvw : (blockGraph (graph s) S).Adj v w) (hdegree : (blockGraph (graph s) S).degree v = 2)
    (huvBuy : v ∈ (s u).val) (hvwBuy : w ∈ (s v).val)
    (c : (blockGraph (graph s) S).Walk v v) (hc : c.IsCycle) :
    (T.branch w).card ≤ (blockAttachment (graph s) S v).card := by
  have hG := nash_connected (Nat.zero_lt_of_lt root.isLt) α s hne
  have hbranch := Finset.card_le_card (branch_subset_verticesViaTwoSteps hG T hv hw hvu hwv)
  have hcard := (nash_degree_two_maximal_block s α hne hα hS huv hvw hdegree huvBuy hvwBuy c hc).1
  exact hbranch.trans hcard

/-- A block admits a root of minimum total distance in the ambient graph. -/
theorem IsBiconnectedBlock.exists_min_distanceSum (hS : IsBiconnectedBlock G S) :
    ∃ r ∈ S, ∀ v ∈ S, distanceSum G r ≤ distanceSum G v :=
  Finset.exists_min_image S (distanceSum G)
    (Finset.card_pos.mp (by have h := hS.twoConnected.card_ge_three; omega))

/-- A non-tree equilibrium has a largest block with a root minimizing the
ambient distance sum on that block. -/
theorem nash_largest_block_of_not_tree (s : Profile n) (α : ℝ≥0)
    (hn : 0 < n) (hne : IsNashEquilibrium α s) (hnt : ¬ (graph s).IsTree) :
    ∃ S, IsBiconnectedBlock (graph s) S ∧
      (∀ T, TwoConnectedOn (graph s) T → T.card ≤ S.card) ∧
      ∃ r ∈ S, ∀ v ∈ S, distanceSum (graph s) r ≤ distanceSum (graph s) v := by
  have hG := nash_connected hn α s hne
  have hcycle : ¬ (graph s).IsAcyclic := fun h => hnt ⟨hG, h⟩
  unfold SimpleGraph.IsAcyclic at hcycle
  push Not at hcycle
  obtain ⟨v, p, hp⟩ := hcycle
  obtain ⟨H, hH, hlarge⟩ := exists_largest_biconnectedBlock p hp
  exact ⟨H, hH, hlarge, hH.exists_min_distanceSum⟩

#print axioms IsBiconnectedBlock.mem_blockAttachment_iff_nearest
#print axioms IsBiconnectedBlock.separatedVertices_eq_blockAttachment
#print axioms nash_degree_two_maximal_block
#print axioms nash_receiver_cycle_bound
#print axioms nash_degree_two_block_down_branch
#print axioms nash_largest_block_of_not_tree

end Lax869952Proofs
