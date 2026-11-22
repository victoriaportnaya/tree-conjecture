import TreeConjecture.LayerDeviations

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ}

/-- The accumulated out-edge layer, augmented by purchased parent edges. -/
def InOutEdgeLayerPlus (s : Profile n) {r : Fin n} (T : ShortestParents (graph s) r)
    (H : SimpleGraph (Fin n)) (k : ℕ) (u v : Fin n) : Prop :=
  InOutEdgeLayer s T H k u v ∨ (H.Adj u v ∧ T.parent u = v ∧ v ∈ (s u).val)

private theorem parent_edge_not_down {G : SimpleGraph (Fin n)} {r u v : Fin n}
    (T : ShortestParents G r) (hu : u ≠ r) (hv : v ≠ r)
    (hup : T.parent u = v) (hdown : T.parent v = u) : False := by
  have hU := T.parent_depth hu
  have hV := T.parent_depth hv
  rw [hup] at hU
  rw [hdown] at hV
  omega

theorem redirect_layer_walk {s : Profile n} {r u x : Fin n}
    (hur : u ≠ r) (T : ShortestParents (graph s) r) {H : SimpleGraph (Fin n)}
    (α : ℝ≥0) (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    (sold : Finset (Fin n)) (i : Fin n → ℕ) (hi : ∀ v ∈ sold, i v ≤ 2)
    (hLayer : ∀ v ∈ sold, InOutEdgeLayerPlus s T H (i v) u v) :
    ∃ p : (graph (redirect s u r hur sold)).Walk u x,
      p.length + (if x ∈ T.branch u then (graph s).dist r u + 1 else 0) ≤
        (graph s).dist r x + 1 + layerPenalty T u sold i ((graph s).dist r u + 1) x := by
  classical
  let G := graph s
  let R := graph (redirect s u r hur sold)
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have hRootEdge : R.Adj u r := redirect_adj_target s hur sold
  have keep {a b : Fin n} (hab : G.Adj a b) (ha : a ≠ u ∨ b ∉ sold) (hb : b ≠ u ∨ a ∉ sold) :
      R.Adj a b := redirect_preserves_adj hab ha hb
  by_cases hx : x ∈ T.branch u
  · by_cases hAffected : ∃ v ∈ sold, x ∈ T.edgeBranch u v
    · obtain ⟨v, hvSold, hAffected⟩ := hAffected
      have hDown : v ≠ r ∧ T.parent v = u := by
        unfold ShortestParents.edgeBranch at hAffected
        split at hAffected
        · assumption
        · exact (Finset.notMem_empty x hAffected).elim
      have hxv : x ∈ T.branch v := by
        simpa only [ShortestParents.edgeBranch, if_pos hDown] using hAffected
      have hNormal : InOutEdgeLayer s T H (i v) u v := (hLayer v hvSold).resolve_right
        (fun hUp => parent_edge_not_down T hur hDown.1 hUp.2.1 hDown.2)
      obtain ⟨p, _, hp, havoid⟩ :=
        nash_out_edge_layer_detour α hne hα (hi v hvSold) hNormal hDown.1 hDown.2 hxv
      obtain ⟨q, hq⟩ := transport_avoiding (H := R)
        (fun ha hb hab => keep hab (Or.inl ha) (Or.inl hb)) p havoid
      have hPay : 2 * i v + (G.dist r u + 1) ≤ layerPenalty T u sold i (G.dist r u + 1) x := by
        unfold layerPenalty
        have h := Finset.single_le_sum
          (f := fun w => if x ∈ T.edgeBranch u w then 2 * i w + (G.dist r u + 1) else 0)
          (fun w _ => Nat.zero_le _) hvSold
        simpa only [if_pos hAffected] using h
      change p.length ≤ G.dist r x + 2 * i v at hp
      refine ⟨.cons hRootEdge q.reverse, ?_⟩
      change (Walk.cons hRootEdge q.reverse).length + (if x ∈ T.branch u then G.dist r u + 1 else 0)
        ≤ G.dist r x + 1 + layerPenalty T u sold i (G.dist r u + 1) x
      rw [Walk.length_cons, Walk.length_reverse, if_pos hx, hq]
      omega
    · obtain ⟨p, hp, hpSupports⟩ := T.branch_route hx
      have hLen := T.tree_dist_of_mem_branch hG hx
      have hp' : p.reverse.IsPath :=
        p.reverse.isPath_of_length_eq_dist (by rw [Walk.length_reverse, hp, hLen])
      have hDown (v : Fin n) (hv : v ∈ sold) (hvp : v ∈ p.reverse.support) (hadj : T.tree.Adj u v) :
          v ≠ r ∧ T.parent v = u := by
        rcases hLayer v hv with h | hUp
        · exact layer_tree_edge_is_down h hadj
        · have hDeep := hpSupports v (by simpa using hvp)
          have hParent := T.parent_depth hur
          rw [hUp.2.1] at hParent
          omega
      obtain ⟨q, hq⟩ := clean_tree_walk sold p.reverse hp' keep hDown
        (fun v hv h => hAffected ⟨v, hv, h⟩)
      change p.length = G.dist r x - G.dist r u at hp
      have hDepth := T.branch_geodesic hx hG
      refine ⟨q, ?_⟩
      change q.length + (if x ∈ T.branch u then G.dist r u + 1 else 0)
        ≤ G.dist r x + 1 + layerPenalty T u sold i (G.dist r u + 1) x
      rw [if_pos hx, hq, Walk.length_reverse, hp]
      change G.dist r x = G.dist r u + G.dist u x at hDepth
      omega
  · obtain ⟨p, hp, havoid⟩ := T.outside_branch_route hG hx
    obtain ⟨q, hq⟩ := transport_avoiding (H := R)
      (fun ha hb hab => keep (T.tree_le hab) (Or.inl ha) (Or.inl hb)) p havoid
    refine ⟨.cons hRootEdge q.reverse, ?_⟩
    rw [Walk.length_cons, Walk.length_reverse, if_neg hx, hq, hp]
    omega

/-- Corollary 12. The cost bound for selling edges in the augmented layer
and purchasing the link to the root. -/
theorem nash_layer_redirect_cost_upper (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r u : Fin n} (hur : u ≠ r) (T : ShortestParents (graph s) r) (H : SimpleGraph (Fin n))
    (hRoot : distanceSum (graph s) r ≤ distanceSum (graph s) u)
    (sold : Finset (Fin n)) (i : Fin n → ℕ) (hi : ∀ v ∈ sold, i v ≤ 2)
    (hLayer : ∀ v ∈ sold, InOutEdgeLayerPlus s T H (i v) u v) :
    (graph (redirect s u r hur sold)).Connected ∧
      finiteCost α (redirect s u r hur sold) u - finiteCost α s u ≤
        (n : ℝ) - ((sold.card : ℝ) - 1) * α -
          (((graph s).dist r u : ℝ) + 1) * ((T.branch u).card : ℝ) +
          ∑ v ∈ sold, ((T.edgeBranch u v).card : ℝ) * (2 * (i v : ℝ) + ((graph s).dist r u : ℝ) + 1) := by
  classical
  let G := graph s
  let R := graph (redirect s u r hur sold)
  let overhead := G.dist r u + 1
  have hWalk (x : Fin n) : ∃ p : R.Walk u x,
      p.length + (if x ∈ T.branch u then overhead else 0) ≤
        G.dist r x + 1 + layerPenalty T u sold i overhead x :=
    redirect_layer_walk hur T α hne hα sold i hi hLayer
  have hR : R.Connected := (connected_iff_exists_forall_reachable R).mpr ⟨u, fun x => ⟨(hWalk x).choose⟩⟩
  have hpoint (x : Fin n) : (R.dist u x : ℝ) + (if x ∈ T.branch u then (overhead : ℝ) else 0) ≤
      (G.dist r x : ℝ) + 1 + (layerPenalty T u sold i overhead x : ℝ) := by
    obtain ⟨p, hp⟩ := hWalk x
    have hNat := (Nat.add_le_add_right (SimpleGraph.dist_le p) _).trans hp
    by_cases hx : x ∈ T.branch u
    · simp only [if_pos hx] at hNat ⊢
      exact_mod_cast hNat
    · simp only [if_neg hx] at hNat ⊢
      exact_mod_cast hNat
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin n))) => hpoint x)
  have hcredit : (∑ x : Fin n, if x ∈ T.branch u then (overhead : ℝ) else 0) =
      ((T.branch u).card : ℝ) * (overhead : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  simp only [Finset.sum_add_distrib, hcredit, cast_layerPenalty_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  have hDist : distanceSum R u + ((T.branch u).card : ℝ) * (overhead : ℝ) ≤
      distanceSum G r + n +
      ∑ v ∈ sold, ((T.edgeBranch u v).card : ℝ) * (2 * (i v : ℝ) + (overhead : ℝ)) := hsum
  have hOwn (v : Fin n) (hv : v ∈ sold) : v ∈ (s u).val := by
    rcases hLayer v hv with h | h
    · obtain ⟨k, _, hk⟩ := h
      cases hk with
      | out _ h _ => exact h
      | down _ h _ _ _ => exact h
    · exact h.2.2
  have hcount : ((redirect s u r hur sold u).val.ncard : ℝ) + (sold.card : ℝ) ≤
      ((s u).val.ncard : ℝ) + 1 := by exact_mod_cast redirect_card_le s hur sold hOwn
  have hPurchase := mul_le_mul_of_nonneg_left hcount (NNReal.zero_le_coe : (0 : ℝ) ≤ α)
  change distanceSum G r ≤ distanceSum G u at hRoot
  have hBound : (∑ v ∈ sold, ((T.edgeBranch u v).card : ℝ) * (2 * (i v : ℝ) + (overhead : ℝ))) =
      ∑ v ∈ sold, ((T.edgeBranch u v).card : ℝ) * (2 * (i v : ℝ) + (G.dist r u : ℝ) + 1) := by
    apply Finset.sum_congr rfl
    intro v _
    simp only [overhead, Nat.cast_add, Nat.cast_one, add_assoc]
  rw [hBound] at hDist
  simp only [overhead, Nat.cast_add, Nat.cast_one] at hDist
  refine ⟨hR, ?_⟩
  unfold finiteCost
  change (α : ℝ) * ((redirect s u r hur sold u).val.ncard : ℝ) + distanceSum R u -
    ((α : ℝ) * ((s u).val.ncard : ℝ) + distanceSum G u) ≤
    (n : ℝ) - ((sold.card : ℝ) - 1) * α -
      ((G.dist r u : ℝ) + 1) * ((T.branch u).card : ℝ) +
      ∑ v ∈ sold, ((T.edgeBranch u v).card : ℝ) * (2 * (i v : ℝ) + (G.dist r u : ℝ) + 1)
  linarith

#print axioms nash_layer_redirect_cost_upper

end TreeConjecture
