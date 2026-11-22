import TreeConjecture.EdgeLayers
import TreeConjecture.TreeDistanceBudget

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Function Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ}

/-- Remove the specified purchases from one player's strategy. -/
noncomputable def sellPurchases (s : Profile n) (u : Fin n) (sold : Finset (Fin n)) : Profile n :=
  fun j => ⟨if j = u then (s j).val \ (↑sold : Set (Fin n)) else (s j).val, by
    split_ifs
    · exact fun h => (s j).property h.1
    · exact (s j).property⟩

theorem sellPurchases_other (s : Profile n) (u j : Fin n) (sold : Finset (Fin n)) (hj : j ≠ u) :
    sellPurchases s u sold j = s j := by
  apply Subtype.ext
  simp [sellPurchases, hj]

theorem sellPurchases_count (s : Profile n) (u : Fin n) (sold : Finset (Fin n))
    (hOwn : ∀ v ∈ sold, v ∈ (s u).val) :
    (sellPurchases s u sold u).val.ncard + sold.card = (s u).val.ncard := by
  have hsub : (↑sold : Set (Fin n)) ⊆ (s u).val := fun v hv => hOwn v hv
  have h := Set.ncard_sdiff_add_ncard_of_subset hsub
  simpa [sellPurchases] using h

theorem sellPurchases_adj {s : Profile n} {u a b : Fin n} {sold : Finset (Fin n)}
    (h : (graph s).Adj a b) (ha : a ≠ u ∨ b ∉ sold) (hb : b ≠ u ∨ a ∉ sold) :
    (graph (sellPurchases s u sold)).Adj a b := by
  have keep {v w : Fin n} (hvw : w ∈ (s v).val) (hv : v ≠ u ∨ w ∉ sold) :
      w ∈ (sellPurchases s u sold v).val := by
    by_cases he : v = u
    · have hw := hv.resolve_left (not_not_intro he)
      simpa [sellPurchases, he] using And.intro hvw hw
    · simpa [sellPurchases, he] using hvw
  exact h.elim (fun h => Or.inl (keep h ha)) (fun h => Or.inr (keep h hb))

namespace ShortestParents

variable {G : SimpleGraph (Fin n)} {r : Fin n} (T : ShortestParents G r)

/-- The child branch associated with a downward parent edge. -/
noncomputable def edgeBranch (u v : Fin n) : Finset (Fin n) :=
  if v ≠ r ∧ T.parent v = u then T.branch v else ∅

theorem root_not_mem_edgeBranch (hG : G.Connected) (u v : Fin n) :
    r ∉ T.edgeBranch u v := by
  intro hr
  unfold edgeBranch at hr
  split at hr
  · rename_i h
    have he := T.branch_geodesic hr hG
    rw [SimpleGraph.dist_self] at he
    have hz : G.dist r v = 0 := by omega
    exact h.1 ((hG.dist_eq_zero_iff.mp hz).symm)
  · simp at hr

end ShortestParents

theorem layer_tree_edge_is_down {s : Profile n} {r u v : Fin n}
    {T : ShortestParents (graph s) r} {H : SimpleGraph (Fin n)} {i : ℕ}
    (hLayer : InOutEdgeLayer s T H i u v) (hTree : T.tree.Adj u v) :
    v ≠ r ∧ T.parent v = u := by
  obtain ⟨j, _, h⟩ := hLayer
  cases h with
  | out _ _ hoff => exact (hoff hTree).elim
  | down _ _ hv hp _ => exact ⟨hv, hp⟩

/-- A simple tree path survives the sale if every sold edge it could start
with is downward and the destination lies outside all of the sold branches. -/
theorem clean_tree_walk {G D : SimpleGraph (Fin n)} {r u x : Fin n}
    {T : ShortestParents G r} (sold : Finset (Fin n)) (p : T.tree.Walk u x) (hp : p.IsPath)
    (hKeep : ∀ {a b}, G.Adj a b → (a ≠ u ∨ b ∉ sold) → (b ≠ u ∨ a ∉ sold) → D.Adj a b)
    (hOnlyDown : ∀ a ∈ sold, a ∈ p.support → T.tree.Adj u a → a ≠ r ∧ T.parent a = u)
    (hClean : ∀ v ∈ sold, x ∉ T.edgeBranch u v) :
    ∃ q : D.Walk u x, q.length = p.length := by
  cases p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons _ a _ hua q =>
    have hqu := (Walk.cons_isPath_iff hua q).mp hp |>.2
    have ha : a ∉ sold := by
      intro hSold
      have haMem := List.mem_cons_of_mem u q.start_mem_support
      have hDown := hOnlyDown a hSold haMem hua
      have hx : x ∉ T.branch a := by
        simpa only [ShortestParents.edgeBranch, if_pos hDown] using hClean a hSold
      have hu := T.branch_parent_mem_support q (T.mem_own_branch a) hx
      exact hqu (hDown.2 ▸ hu)
    have hEdge : D.Adj u a := hKeep (T.tree_le hua) (Or.inr ha) (Or.inl hua.ne.symm)
    obtain ⟨p, hlen⟩ := transport_avoiding (H := D)
      (fun hb hc hbc => hKeep (T.tree_le hbc) (Or.inl hb) (Or.inl hc)) q hqu
    exact ⟨.cons hEdge p, by simp only [Walk.length_cons, hlen]⟩

theorem layer_deletion_clean_walk {s : Profile n} {r u x : Fin n}
    {T : ShortestParents (graph s) r} {H : SimpleGraph (Fin n)}
    (sold : Finset (Fin n)) (i : Fin n → ℕ)
    (hLayer : ∀ v ∈ sold, InOutEdgeLayer s T H (i v) u v) (hG : (graph s).Connected)
    (hClean : ∀ v ∈ sold, x ∉ T.edgeBranch u v) :
    ∃ p : (graph (sellPurchases s u sold)).Walk u x, p.length = T.tree.dist u x := by
  obtain ⟨p, hp, hlen⟩ := (T.isTree hG).connected.exists_path_of_dist u x
  obtain ⟨q, hq⟩ := clean_tree_walk sold p hp sellPurchases_adj
    (fun a ha _ hAdj => layer_tree_edge_is_down (hLayer a ha) hAdj) hClean
  exact ⟨q, hq.trans hlen⟩

noncomputable def layerPenalty {G : SimpleGraph (Fin n)} {r : Fin n}
    (T : ShortestParents G r) (u : Fin n) (sold : Finset (Fin n)) (i : Fin n → ℕ) (overhead : ℕ) (x : Fin n) : ℕ := by
  classical
  exact ∑ v ∈ sold, if x ∈ T.edgeBranch u v then 2 * i v + overhead else 0

private theorem layer_deletion_walk {s : Profile n} {r u x : Fin n}
    {T : ShortestParents (graph s) r} {H : SimpleGraph (Fin n)}
    (α : ℝ≥0) (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    (sold : Finset (Fin n)) (i : Fin n → ℕ) (hi : ∀ v ∈ sold, i v ≤ 2)
    (hLayer : ∀ v ∈ sold, InOutEdgeLayer s T H (i v) u v) :
    ∃ p : (graph (sellPurchases s u sold)).Walk u x,
      p.length ≤ T.tree.dist u x + layerPenalty T u sold i (2 * (graph s).dist r u) x := by
  classical
  let G := graph s
  let D := graph (sellPurchases s u sold)
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  by_cases hAffected : ∃ v ∈ sold, x ∈ T.edgeBranch u v
  · obtain ⟨v, hvSold, hxAffected⟩ := hAffected
    have hDown : v ≠ r ∧ T.parent v = u := by
      unfold ShortestParents.edgeBranch at hxAffected
      split at hxAffected
      · assumption
      · exact (Finset.notMem_empty x hxAffected).elim
    have hxBranch : x ∈ T.branch v := by
      simpa only [ShortestParents.edgeBranch, if_pos hDown] using hxAffected
    have hxu : x ∈ T.branch u :=
      hDown.2 ▸ T.mem_branch_of_mem_child_branch hDown.1 hxBranch
    obtain ⟨q, hq⟩ := layer_deletion_clean_walk sold i hLayer hG
      (fun w _ => T.root_not_mem_edgeBranch hG u w)
    have hRootLength : q.length = G.dist r u := by
      rw [hq, SimpleGraph.dist_comm, T.root_distance hG u]
    obtain ⟨walk, _, hlen, hAvoid⟩ :=
      nash_out_edge_layer_detour α hne hα (hi v hvSold) (hLayer v hvSold) hDown.1 hDown.2 hxBranch
    obtain ⟨p, hp⟩ := transport_avoiding (H := D)
      (fun ha hb hab => sellPurchases_adj hab (Or.inl ha) (Or.inl hb)) walk hAvoid
    have hPay : 2 * i v + 2 * G.dist r u ≤ layerPenalty T u sold i (2 * (graph s).dist r u) x := by
      unfold layerPenalty
      have h := Finset.single_le_sum
        (f := fun w => if x ∈ T.edgeBranch u w then 2 * i w + 2 * G.dist r u else 0)
        (fun w _ => Nat.zero_le _) hvSold
      simpa only [if_pos hxAffected] using h
    have hTree := T.tree_dist_of_mem_branch hG hxu
    have hDepth := T.branch_geodesic hxu hG
    change walk.length ≤ G.dist r x + 2 * i v at hlen
    refine ⟨q.append p.reverse, ?_⟩
    rw [Walk.length_append, Walk.length_reverse, hp, hRootLength]
    change T.tree.dist u x = G.dist r x - G.dist r u at hTree
    change G.dist r x = G.dist r u + G.dist u x at hDepth
    omega
  · obtain ⟨p, hp⟩ := layer_deletion_clean_walk sold i hLayer hG
      (fun v hv h => hAffected ⟨v, hv, h⟩)
    exact ⟨p, hp.le.trans (Nat.le_add_right _ _)⟩

theorem cast_layerPenalty_sum {G : SimpleGraph (Fin n)} {r : Fin n}
    (T : ShortestParents G r) (u : Fin n) (sold : Finset (Fin n)) (i : Fin n → ℕ) (overhead : ℕ) :
    (∑ x : Fin n, (layerPenalty T u sold i overhead x : ℝ)) =
      ∑ v ∈ sold, ((T.edgeBranch u v).card : ℝ) * (2 * (i v : ℝ) + (overhead : ℝ)) := by
  classical
  unfold layerPenalty
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_filter]
  simp [mul_add]

/-- Lemma 10. The cost change from deleting purchases in the first three
out-edge layers is bounded by the tree distances and the affected branch sizes. -/
theorem nash_layer_deletion_cost_upper (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r u : Fin n} (T : ShortestParents (graph s) r) (H : SimpleGraph (Fin n))
    (hRoot : distanceSum (graph s) r ≤ distanceSum (graph s) u)
    (sold : Finset (Fin n)) (i : Fin n → ℕ) (hi : ∀ v ∈ sold, i v ≤ 2)
    (hLayer : ∀ v ∈ sold, InOutEdgeLayer s T H (i v) u v) :
    (graph (sellPurchases s u sold)).Connected ∧
      finiteCost α (sellPurchases s u sold) u - finiteCost α s u ≤
        ((graph s).dist r u : ℝ) * (n : ℝ) -
          2 * (∑ k ∈ Finset.range ((graph s).dist r u), ((T.branch (T.parent^[k] u)).card : ℝ)) -
          (sold.card : ℝ) * α +
          ∑ v ∈ sold, ((T.edgeBranch u v).card : ℝ) * (2 * (i v : ℝ) + 2 * ((graph s).dist r u : ℝ)) := by
  classical
  let G := graph s
  let D := graph (sellPurchases s u sold)
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have hWalk (x : Fin n) : ∃ p : D.Walk u x, p.length ≤ T.tree.dist u x + layerPenalty T u sold i (2 * (graph s).dist r u) x :=
    layer_deletion_walk α hne hα sold i hi hLayer
  have hD : D.Connected := (connected_iff_exists_forall_reachable D).mpr ⟨u, fun x => ⟨(hWalk x).choose⟩⟩
  have hDist : distanceSum D u ≤ distanceSum T.tree u + ∑ x : Fin n, (layerPenalty T u sold i (2 * (graph s).dist r u) x : ℝ) := by
    unfold distanceSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    obtain ⟨p, hp⟩ := hWalk x
    exact_mod_cast ((SimpleGraph.dist_le p).trans hp)
  have hOwn (v : Fin n) (hv : v ∈ sold) : v ∈ (s u).val := by
    obtain ⟨j, _, he⟩ := hLayer v hv
    cases he with
    | out _ h _ => exact h
    | down _ h _ _ _ => exact h
  have hcard : ((sellPurchases s u sold u).val.ncard : ℝ) + (sold.card : ℝ) = ((s u).val.ncard : ℝ) := by
    exact_mod_cast sellPurchases_count s u sold hOwn
  rw [T.tree_distanceSum hG u, cast_layerPenalty_sum] at hDist
  push_cast at hDist
  refine ⟨hD, ?_⟩
  unfold finiteCost
  change distanceSum G r ≤ distanceSum G u at hRoot
  rw [← hcard]
  change (α : ℝ) * ((sellPurchases s u sold u).val.ncard : ℝ) + distanceSum D u -
    ((α : ℝ) * (((sellPurchases s u sold u).val.ncard : ℝ) + (sold.card : ℝ)) + distanceSum G u) ≤ _
  linarith

#print axioms nash_layer_deletion_cost_upper

end TreeConjecture
