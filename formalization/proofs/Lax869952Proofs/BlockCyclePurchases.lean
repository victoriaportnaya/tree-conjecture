import Lax869952Proofs.BlockPaths
import Lax869952Proofs.DirectedMinCycles

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

variable {n : ℕ}

theorem CycleDirected.exists_incident_purchases {s : Profile n} {z u : Fin n}
    {p : (graph s).Walk z z} (hp : p.IsCycle) (hd : CycleDirected s p) (hu : u ∈ p.support) :
    (∃ v, v ∈ (s u).val ∧ s(u, v) ∈ p.edges) ∧
      (∃ w, u ∈ (s w).val ∧ s(u, w) ∈ p.edges) := by
  obtain ⟨k, he, hk⟩ := Walk.mem_support_iff_exists_getVert.mp hu
  have hLen := hp.three_le_length
  have hIdx : ∃ i : Fin p.length, p.getVert i.val = u := by
    by_cases hl : k < p.length
    · exact ⟨⟨k, hl⟩, he⟩
    · have hEnd : k = p.length := by omega
      rw [hEnd, Walk.getVert_length] at he
      exact ⟨⟨0, by omega⟩, by simpa using he⟩
  obtain ⟨i, hi⟩ := hIdx
  have edge (j : Fin p.length) : s(p.getVert j.val, p.getVert (finRotate p.length j).val) ∈ p.edges := by
    rw [cycle_getVert_finRotate]
    exact p.mk_mem_edges_iff_exists.mpr ⟨j.val, j.isLt, rfl⟩
  let j := (finRotate p.length).symm i
  have hRotate : finRotate p.length j = i := Equiv.apply_symm_apply _ _
  have hE : s(u, p.getVert j.val) ∈ p.edges := by
    have h := edge j
    rw [hRotate, hi] at h
    rw [Sym2.eq_swap]
    exact h
  rcases hd with hf | hb
  · refine ⟨⟨_, hi ▸ hf i, hi ▸ edge i⟩, ⟨_, ?_, hE⟩⟩
    have h := hf j
    rwa [hRotate, hi] at h
  · refine ⟨⟨_, ?_, hE⟩, ⟨_, hi ▸ hb i, hi ▸ edge i⟩⟩
    have h := hb j
    rwa [hRotate, hi] at h

/-- Every block vertex has an incoming and an outgoing purchase along a
directed cycle of the block. -/
theorem nash_block_vertex_incident_purchases (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {S : Finset (Fin n)} (hS : IsBiconnectedBlock (graph s) S) {u : Fin n} (hu : u ∈ S) :
    (∃ v, (blockGraph (graph s) S).Adj u v ∧ v ∈ (s u).val) ∧
      (∃ w, (blockGraph (graph s) S).Adj u w ∧ u ∈ (s w).val) := by
  obtain ⟨c, hc⟩ := hS.twoConnected.exists_cycle_at hu
  let b := c.snd
  have hab : (blockGraph (graph s) S).Adj u b := c.adj_snd hc.not_nil
  let q := c.mapLe (blockGraph_le (graph s) S)
  have hPrice : 2 * ((n - 1 : ℕ) : ℝ≥0) < α := by
    have hLE : ((n - 1 : ℕ) : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast Nat.sub_le n 1
    exact (mul_le_mul_of_nonneg_left hLE (by norm_num)).trans_lt hα
  have hQEdge : s(u, b) ∈ q.edges := by
    change s(u, b) ∈ (c.mapLe (blockGraph_le (graph s) S)).edges
    rw [Walk.edges_mapLe_eq_edges]
    exact c.mk_start_snd_mem_edges hc.not_nil
  obtain ⟨z, p, hp, he, hd, _⟩ := nash_edge_on_cycle_has_directed_cycle s α hne hPrice s(u, b)
    ⟨u, q, hc.mapLe _, hQEdge⟩
  obtain ⟨⟨v, hBuy, hEdge⟩, ⟨w, hIncoming, hWEdge⟩⟩ :=
    hd.exists_incident_purchases hp (p.fst_mem_support_of_mem_edges he)
  have hBlock := hS.cycle_edges_subset p hp hab he
  exact ⟨⟨v, hBlock _ hEdge, hBuy⟩, ⟨w, hBlock _ hWEdge, hIncoming⟩⟩

#print axioms nash_block_vertex_incident_purchases

end Lax869952Proofs
