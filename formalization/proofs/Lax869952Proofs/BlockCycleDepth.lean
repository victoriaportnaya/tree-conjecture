import Lax869952Proofs.BlockPaths
import Lax869952Proofs.CycleDepth

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

private theorem cycle_length_ge_block_minimum {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} (hS : IsBiconnectedBlock G S)
    {u z : V} (c : (blockGraph G S).Walk u u)
    (hMin : ∀ p : (blockGraph G S).Walk u u, p.IsCycle → c.length ≤ p.length)
    (q : G.Walk z z) (hq : q.IsCycle) (hu : u ∈ q.support)
    (e : Sym2 V) (he : e ∈ q.edges) (heBlock : e ∈ (blockGraph G S).edgeSet) :
    c.length ≤ q.length := by
  have keep : ∀ f ∈ q.edges, f ∈ (blockGraph G S).edgeSet := by
    induction e using Sym2.ind with
    | h a b => exact hS.cycle_edges_subset q hq heBlock he
  let p := q.transfer _ keep
  have hp : p.IsCycle := hq.transfer keep
  have hup : u ∈ p.support := by simpa only [p, Walk.support_transfer] using hu
  simpa only [Walk.length_rotate, p, Walk.length_transfer] using hMin (p.rotate u hup) (hp.rotate hup)

/-- Lemma 8 for the shortest cycle through the ancestor within its block.
All cycles used to compare lengths are confined to the same block. -/
theorem nash_block_branch_cycle_depth {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {S : Finset (Fin n)} (hS : IsBiconnectedBlock (graph s) S)
    {r u x y : Fin n} (T : ShortestParents (graph s) r)
    (hCompatible : ∀ {v} (p : (graph s).Walk r v), p.length = (graph s).dist r v →
      PurchaseDirected s p → ∀ e ∈ p.edges, e ∈ T.tree.edgeSet)
    (hx : x ∈ T.branch u) (i : ℕ) (hi : i ≤ 2)
    (hxi : (graph s).dist r x = (graph s).dist r u + i)
    (hadj : (blockGraph (graph s) S).Adj x y) (hbuy : y ∈ (s x).val) (hoff : ¬ T.tree.Adj x y)
    (c : (blockGraph (graph s) S).Walk u u)
    (hMin : ∀ p : (blockGraph (graph s) S).Walk u u, p.IsCycle → c.length ≤ p.length) :
    c.length / 2 ≤ (graph s).dist r u + i := by
  apply nash_branch_cycle_depth_of_cycle_bound s α hne hα T hCompatible hx i hi hxi hbuy hoff
  · intro z q hq hu he
    exact cycle_length_ge_block_minimum hS c hMin q hq hu _ he hadj
  · intro z q hq hu he hLen
    obtain ⟨e, heq, hMem⟩ := (q.mem_support_iff_exists_mem_edges_of_not_nil hq.not_nil).mp hu
    have heBlock := hS.cycle_edges_subset q hq hadj he e heq
    apply shortest_cycle_through_edge_isometric q hq e heq
    intro w p hp hep
    have hup : u ∈ p.support :=
      (p.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil).mpr ⟨e, hep, hMem⟩
    exact hLen.trans_le (cycle_length_ge_block_minimum hS c hMin p hp hup e hep heBlock)

#print axioms nash_block_branch_cycle_depth

end Lax869952Proofs
