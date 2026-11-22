import TreeConjecture.CycleDepth

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Function Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped NNReal

variable {n : ℕ} {s : Profile n} {root : Fin n}
variable {T : ShortestParents (graph s) root} {H : SimpleGraph (Fin n)}

/-- A purchased edge of `H` leading to a non-tree purchase after exactly
`i` downward tree edges, all purchased in the downward direction. -/
inductive OutEdgeChain (s : Profile n) {root : Fin n}
    (T : ShortestParents (graph s) root) (H : SimpleGraph (Fin n)) :
    ℕ → Fin n → Fin n → Prop
  | out {u v} : H.Adj u v → v ∈ (s u).val → ¬ T.tree.Adj u v → OutEdgeChain s T H 0 u v
  | down {i u v w} : H.Adj u v → v ∈ (s u).val → v ≠ root → T.parent v = u →
      OutEdgeChain s T H i v w → OutEdgeChain s T H (i + 1) u v

/-- Membership in Dippel–Vetta's accumulated `X_i` edge class,
with the buyer as the first endpoint. -/
def InOutEdgeLayer (s : Profile n) {root : Fin n}
    (T : ShortestParents (graph s) root) (H : SimpleGraph (Fin n))
    (i : ℕ) (u v : Fin n) : Prop :=
  ∃ j ≤ i, OutEdgeChain s T H j u v

theorem OutEdgeChain.off_tree_witness {i : ℕ} {u v : Fin n}
    (h : OutEdgeChain s T H i u v) :
    ∃ x y, x ∈ T.branch u ∧ (graph s).dist root x = (graph s).dist root u + i ∧
      H.Adj x y ∧ y ∈ (s x).val ∧ ¬ T.tree.Adj x y := by
  classical
  induction h with
  | @out u v hadj hbuy hoff =>
    refine ⟨u, v, ?_, by simp, hadj, hbuy, hoff⟩
    simpa only [ShortestParents.branch, Finset.mem_filter, Finset.mem_univ, true_and] using
      (show ∃ k ≤ (graph s).dist root u, T.parent^[k] u = u from ⟨0, Nat.zero_le _, rfl⟩)
  | @down i u v w _ _ hv hparent _ ih =>
    obtain ⟨x, y, hx, hd, hxy, hbuy, hoff⟩ := ih
    have hxu := T.mem_branch_of_mem_child_branch hv hx
    rw [hparent] at hxu
    have hstep := T.parent_depth hv
    rw [hparent] at hstep
    exact ⟨x, y, hxu, by omega, hxy, hbuy, hoff⟩

/-- Lemma 7 in terms of the `X_i` edge class. An off-tree edge has no
child branch, so the hypotheses identify the nonempty branch case. -/
theorem nash_out_edge_layer_detour (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {u v w : Fin n} {i : ℕ} (hi : i ≤ 2)
    (hedge : InOutEdgeLayer s T H i u v)
    (hv : v ≠ root) (hparent : T.parent v = u) (hw : w ∈ T.branch v) :
    ∃ p : (graph s).Walk w root,
      p.IsPath ∧ p.length ≤ (graph s).dist root w + 2 * i ∧ u ∉ p.support := by
  obtain ⟨j, hj, hedge⟩ := hedge
  cases hedge with
  | out hadj _ hoff =>
    exact (hoff ⟨hadj.ne, Or.inr hparent⟩).elim
  | @down k _ _ t _ _ _ _ hchain =>
    obtain ⟨x, y, hx, hd, _, hbuy, hoff⟩ := hchain.off_tree_witness
    have hstep := T.parent_depth hv
    rw [hparent] at hstep
    have hxi : (graph s).dist root x = (graph s).dist root u + (k + 1) := by omega
    obtain ⟨p, hp, havoid⟩ :=
      nash_short_branch_detour s α hne hα T hv hparent hw hx (k + 1) (by omega) hxi
        (Or.inl hbuy) hoff
    exact ⟨p.bypass, p.bypass_isPath, p.length_bypass_le_length.trans (by omega),
      fun hu => havoid (p.support_bypass_subset_support hu)⟩

/-- Lemma 8 in terms of the `X_i` edge class. -/
theorem nash_out_edge_layer_depth (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    (hcompatible : ∀ {v} (p : (graph s).Walk root v), p.length = (graph s).dist root v →
      PurchaseDirected s p → ∀ e ∈ p.edges, e ∈ T.tree.edgeSet)
    {u v : Fin n} {i : ℕ} (hi : i ≤ 2)
    (hedge : InOutEdgeLayer s T H i u v)
    {z : Fin n} (c : (graph s).Walk z z)
    (hc : ∀ {v} (q : (graph s).Walk v v), q.IsCycle → u ∈ q.support → c.length ≤ q.length) :
    c.length / 2 ≤ (graph s).dist root u + i := by
  obtain ⟨j, hj, hedge⟩ := hedge
  obtain ⟨x, y, hx, hd, _, hbuy, hoff⟩ := hedge.off_tree_witness
  have h := nash_branch_cycle_depth s α hne hα T hcompatible hx j (by omega) hd hbuy hoff c hc
  omega

#print axioms OutEdgeChain.off_tree_witness
#print axioms nash_out_edge_layer_detour
#print axioms nash_out_edge_layer_depth

end TreeConjecture
