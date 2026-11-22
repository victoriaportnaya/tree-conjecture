import TreeConjecture.RootLinkBudget
import TreeConjecture.Redirect

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Function Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ}

/-- In the swap of Lemma 17, replacing a root's link to its child with a
link to a descendant of depth three rules out a descendant branch with
more than half the vertices of the child's branch. -/
theorem nash_root_branch_swap_bound (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s)
    {r a v : Fin n} (T : ShortestParents (graph s) r)
    (ha : (graph s).dist r a = 1) (hv : (graph s).dist r v = 3)
    (hAncestor : v ∈ T.branch a) (hBuy : a ∈ (s r).val) :
    2 * (T.branch v).card ≤ (T.branch a).card := by
  classical
  let G := graph s
  change G.dist r a = 1 at ha
  change G.dist r v = 3 at hv
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  have hr : r ≠ v := by
    intro he
    simp [← he] at hv
  let R := graph (redirect s r v hr {a})
  have hEdge : R.Adj r v := redirect_adj_target s hr {a}
  have hSub : T.branch v ⊆ T.branch a := by
    obtain ⟨k, hk, hEq⟩ : ∃ k ≤ G.dist r v, T.parent^[k] v = a := by
      simpa [ShortestParents.branch] using hAncestor
    intro x hx
    exact hEq ▸ T.mem_branch_iterate hx k hk
  have inside {b x : Fin n} (hb : 0 < G.dist r b) (h : x ∈ T.branch b) :
      ∃ p : R.Walk x b, p.length = G.dist r x - G.dist r b := by
    obtain ⟨p, hp, hSupport⟩ := T.branch_route h
    have hAvoid : r ∉ p.support := by
      intro hMem
      have hDepth := hSupport r hMem
      change G.dist r b ≤ G.dist r r at hDepth
      rw [dist_self] at hDepth
      omega
    obtain ⟨q, hq⟩ := transport_avoiding (H := R)
      (fun hi hj hij => redirect_preserves_adj (T.tree_le hij) (Or.inl hi) (Or.inl hj)) p hAvoid
    exact ⟨q, hq.trans hp⟩
  have hRoute (x : Fin n) : ∃ p : R.Walk r x,
      p.length + (if x ∈ T.branch v then 2 else 0) ≤
      G.dist r x + (if x ∈ T.branch a \ T.branch v then 2 else 0) := by
    by_cases hV : x ∈ T.branch v
    · obtain ⟨p, hp⟩ := inside (by omega : 0 < G.dist r v) hV
      have hDepth := T.branch_geodesic hV hG
      refine ⟨.cons hEdge p.reverse, ?_⟩
      have hMem : x ∉ T.branch a \ T.branch v := fun h => (Finset.mem_sdiff.mp h).2 hV
      simp only [Walk.length_cons, Walk.length_reverse, if_pos hV, if_neg hMem, add_zero]
      change G.dist r x = G.dist r v + G.dist v x at hDepth
      omega
    · by_cases hA : x ∈ T.branch a
      · have hPos : 0 < G.dist r a := by omega
        obtain ⟨p, hp⟩ := inside hPos hAncestor
        obtain ⟨q, hq⟩ := inside hPos hA
        have hDepth := T.branch_geodesic hA hG
        change G.dist r x = G.dist r a + G.dist a x at hDepth
        have hMem : x ∈ T.branch a \ T.branch v := Finset.mem_sdiff.mpr ⟨hA, hV⟩
        refine ⟨.cons hEdge (p.append q.reverse), ?_⟩
        simp only [Walk.length_cons, Walk.length_append, Walk.length_reverse, if_neg hV, if_pos hMem]
        omega
      · obtain ⟨p, hp, hAvoid⟩ := T.outside_branch_route hG hA
        obtain ⟨q, hq⟩ := transport_avoiding (H := R)
          (fun hi hj hij => redirect_preserves_adj (T.tree_le hij)
            (Or.inr (by simpa using hj)) (Or.inr (by simpa using hi))) p hAvoid
        have hMem : x ∉ T.branch a \ T.branch v := fun h => hA (Finset.mem_sdiff.mp h).1
        change p.length = G.dist r x at hp
        exact ⟨q.reverse, by simp [hV, hMem, hq, hp]⟩
  have hR : R.Connected :=
    (connected_iff_exists_forall_reachable R).mpr ⟨r, fun x => ⟨(hRoute x).choose⟩⟩
  have hNash : distanceSum G r ≤ distanceSum R r :=
    nash_swap_distanceSum_le s α hne hr hBuy hR
  have hPoint (x : Fin n) : (R.dist r x : ℝ) + (if x ∈ T.branch v then 2 else 0) ≤
      (G.dist r x : ℝ) + (if x ∈ T.branch a \ T.branch v then 2 else 0) := by
    obtain ⟨p, hp⟩ := hRoute x
    have hd := (Nat.add_le_add_right (SimpleGraph.dist_le p) _).trans hp
    by_cases hx : x ∈ T.branch v <;> by_cases hy : x ∈ T.branch a \ T.branch v <;>
      simp only [hx, hy, if_true, if_false] at hd ⊢ <;> exact_mod_cast hd
  have indicator (S : Finset (Fin n)) :
      (∑ x : Fin n, if x ∈ S then (2 : ℝ) else 0) = 2 * (S.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have hSum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin n))) => hPoint x)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, indicator, indicator] at hSum
  change distanceSum R r + 2 * ((T.branch v).card : ℝ) ≤
    distanceSum G r + 2 * (((T.branch a) \ (T.branch v)).card : ℝ) at hSum
  have hCard : (T.branch v).card ≤ (T.branch a \ T.branch v).card := by
    exact_mod_cast (show ((T.branch v).card : ℝ) ≤ ((T.branch a \ T.branch v).card : ℝ) by linarith)
  rw [Finset.card_sdiff_of_subset hSub] at hCard
  omega

#print axioms nash_root_branch_swap_bound

end TreeConjecture
