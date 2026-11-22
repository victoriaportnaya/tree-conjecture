import TreeConjecture.Foundations

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ}

private noncomputable def addPurchase (s : Profile n) (u v : Fin n) (huv : u ≠ v) :
    Profile n :=
  fun i => ⟨if i = u then insert v (s i).val else (s i).val, by
    split_ifs with hi
    · subst i
      exact fun h => (Set.mem_insert_iff.mp h).elim huv (s u).property
    · exact (s i).property⟩

/-- The possible saving in distance from adding a link is bounded by its price at Nash
equilibrium. Each destination can use either its old path or the new link. -/
theorem nash_addition_distance_bound (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {u v : Fin n} (huv : u ≠ v)
    (hNotAdj : ¬ (graph s).Adj u v) :
    (∑ x : Fin n, max 0 (((graph s).dist u x : ℝ) - ((graph s).dist v x : ℝ) - 1)) ≤
      (α : ℝ) := by
  classical
  let t := addPurchase s u v huv
  have hKeep (i j : Fin n) (h : j ∈ (s i).val) : j ∈ (t i).val := by
    by_cases hi : i = u
    · exact (by simpa [t, addPurchase, hi] using Or.inr (a := j = v) h)
    · simpa [t, addPurchase, hi] using h
  have hSub : graph s ≤ graph t :=
    fun _ _ h => h.elim (fun h => Or.inl (hKeep _ _ h)) (fun h => Or.inr (hKeep _ _ h))
  have hAdj : (graph t).Adj u v := Or.inl (by simp [t, addPurchase])
  have hs := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have ht := hs.mono hSub
  have hCost := nash_finite_cost_le α s t hs ht hne u (fun i hi => by
    apply Subtype.ext
    simp [t, addPurchase, hi])
  have hNew : v ∉ (s u).val := fun h => hNotAdj (Or.inl h)
  have hCount : (t u).val.ncard = (s u).val.ncard + 1 := by
    simpa [t, addPurchase] using Set.ncard_insert_of_notMem hNew
  have hSum : distanceSum (graph s) u - distanceSum (graph t) u ≤ (α : ℝ) := by
    unfold finiteCost at hCost
    rw [hCount, Nat.cast_add, Nat.cast_one, mul_add, mul_one] at hCost
    linarith
  refine le_trans ?_ hSum
  unfold distanceSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hOld : (graph t).dist u x ≤ (graph s).dist u x := (hs u x).dist_anti hSub
  obtain ⟨p, hp⟩ := hs.exists_walk_length_eq_dist v x
  have hVia : (graph t).dist u x ≤ (graph s).dist v x + 1 := by
    simpa [hp] using (dist_le (Walk.cons hAdj (p.mapLe hSub)))
  have hOldR : ((graph t).dist u x : ℝ) ≤ ((graph s).dist u x : ℝ) := by exact_mod_cast hOld
  have hViaR : ((graph t).dist u x : ℝ) ≤ ((graph s).dist v x : ℝ) + 1 := by
    exact_mod_cast hVia
  exact max_le (by linarith) (by linarith)

#print axioms nash_addition_distance_bound

end TreeConjecture
