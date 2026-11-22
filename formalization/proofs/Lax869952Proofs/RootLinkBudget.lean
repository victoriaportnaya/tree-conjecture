import Lax869952Proofs.TreeDistanceBudget

set_option warningAsError true

namespace Lax869952Proofs.ShortestParents

open SimpleGraph Function
open scoped BigOperators

variable {n : ℕ} {G : SimpleGraph (Fin n)} {r : Fin n} (T : ShortestParents G r)

theorem mem_branch_iterate {u x : Fin n} (hx : x ∈ T.branch u) (k : ℕ) (hk : k ≤ G.dist r u) :
    x ∈ T.branch ((T.parent^[k]) u) := by
  classical
  obtain ⟨j, hj, he⟩ : ∃ j ≤ G.dist r x, T.parent^[j] x = u := by
    simpa [branch] using hx
  have hd := T.depth_iterate j x
  rw [he] at hd
  simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨k + j, by omega, by rw [Function.iterate_add_apply, he]⟩

theorem mem_ancestor_branch_mono {u x : Fin n} {i j : ℕ} (hij : i ≤ j) (hj : j ≤ G.dist r u)
    (hx : x ∈ T.branch ((T.parent^[i]) u)) : x ∈ T.branch ((T.parent^[j]) u) := by
  have hd := T.depth_iterate i u
  have hk : j - i ≤ G.dist r ((T.parent^[i]) u) := by omega
  have h := T.mem_branch_iterate hx (j - i) hk
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij] at h
  exact h

private noncomputable def ancestorIndicator (u x : Fin n) (k : ℕ) : ℕ := by
  classical
  exact if x ∈ T.branch ((T.parent^[k]) u) then 1 else 0

private theorem tree_dist_with_ancestor_visits (hG : G.Connected) (u x : Fin n) :
    T.tree.dist u x + 2 * (∑ k ∈ Finset.range (G.dist r u), T.ancestorIndicator u x k) =
      G.dist r x + G.dist r u := by
  classical
  suffices h : ∀ d v, G.dist r v = d →
      T.tree.dist v x + 2 * (∑ k ∈ Finset.range d, T.ancestorIndicator v x k) = G.dist r x + d from
    h _ u rfl
  intro d
  induction d with
  | zero =>
    intro v hv
    obtain rfl := hG.dist_eq_zero_iff.mp hv
    simp [T.root_distance hG]
  | succ d ih =>
    intro v hd
    have hv : v ≠ r := fun he => by simp [he] at hd
    have hp : G.dist r (T.parent v) = d := by rw [T.depth_parent, hd]; omega
    have hParent := ih _ hp
    have hStep := T.tree_dist_parent_step hG hv x
    have hStepNat : T.tree.dist v x + 2 * T.ancestorIndicator v x 0 =
        T.tree.dist (T.parent v) x + 1 := by
      have hReal : (T.tree.dist v x : ℝ) + 2 * (T.ancestorIndicator v x 0 : ℝ) =
          (T.tree.dist (T.parent v) x : ℝ) + 1 := by
        by_cases hx : x ∈ T.branch v
        · simp [hx] at hStep
          simp [ancestorIndicator, hx]
          linarith
        · simp [hx] at hStep
          simpa [ancestorIndicator, hx] using hStep
      exact_mod_cast hReal
    rw [Finset.sum_range_succ']
    have hshift (k : ℕ) : T.ancestorIndicator v x (k + 1) =
        T.ancestorIndicator (T.parent v) x k := by
      rw [ancestorIndicator, ancestorIndicator, Function.iterate_succ_apply]
    simp only [hshift]
    omega

/-- Savings from using the better of the tree route and the new root link.
The ancestors strictly before the midpoint contribute two units each.
An integral midpoint contributes one more unit. -/
noncomputable def rootLinkCredit (u x : Fin n) : ℕ := by
  classical
  let d := G.dist r u
  exact 2 * (∑ k ∈ Finset.range ((d + 1) / 2), T.ancestorIndicator u x k) +
    if d % 2 = 0 ∧ x ∈ T.branch ((T.parent^[d / 2]) u) then 1 else 0

theorem rootLinkCredit_le (u x : Fin n) : T.rootLinkCredit u x ≤ G.dist r u + 1 := by
  classical
  let d := G.dist r u
  let early := ∑ k ∈ Finset.range ((d + 1) / 2), T.ancestorIndicator u x k
  have hEarly : early ≤ (d + 1) / 2 := by
    calc
      early ≤ ∑ _k ∈ Finset.range ((d + 1) / 2), 1 := by
        apply Finset.sum_le_sum
        intro k _
        unfold ancestorIndicator
        split <;> omega
      _ = _ := by simp
  change 2 * early + (if d % 2 = 0 ∧ x ∈ T.branch ((T.parent^[d / 2]) u) then 1 else 0) ≤ d + 1
  split
  · rename_i h
    have := h.1
    omega
  · omega

private theorem fill_ancestor_suffix (u x : Fin n) (m : ℕ)
    (hm : m ≤ G.dist r u) (h : x ∈ T.branch ((T.parent^[m]) u)) :
    (∑ k ∈ Finset.range (G.dist r u), T.ancestorIndicator u x k) =
      (∑ k ∈ Finset.range m, T.ancestorIndicator u x k) + (G.dist r u - m) := by
  classical
  let d := G.dist r u
  change (∑ k ∈ Finset.range d, T.ancestorIndicator u x k) =
    (∑ k ∈ Finset.range m, T.ancestorIndicator u x k) + (d - m)
  have he : d = m + (d - m) := by omega
  calc
    (∑ k ∈ Finset.range d, T.ancestorIndicator u x k) =
        (∑ k ∈ Finset.range m, T.ancestorIndicator u x k) +
          ∑ j ∈ Finset.range (d - m), T.ancestorIndicator u x (m + j) := by
      conv_lhs => rw [he, Finset.sum_range_add]
    _ = _ := by
      congr 1
      calc
        (∑ j ∈ Finset.range (d - m), T.ancestorIndicator u x (m + j)) =
          ∑ _j ∈ Finset.range (d - m), (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' := Finset.mem_range.mp hj
            have hvisit := T.mem_ancestor_branch_mono (i := m) (j := m + j) (by omega)
              (show m + j ≤ G.dist r u by change m + j ≤ d; omega) h
            simp [ancestorIndicator, hvisit]
        _ = _ := by simp

/-- The shorter of the tree route and the root route realizes at least
the midpoint credit used in Corollary 11. -/
theorem min_tree_root_link_le (hG : G.Connected) (u x : Fin n) :
    min (T.tree.dist u x) (G.dist r x + 1) + T.rootLinkCredit u x ≤ G.dist r x + 1 := by
  classical
  let d := G.dist r u
  let m := (d + 1) / 2
  let early := ∑ k ∈ Finset.range m, T.ancestorIndicator u x k
  have hm : m ≤ d := by omega
  have ht := T.tree_dist_with_ancestor_visits hG u x
  change T.tree.dist u x + 2 * (∑ k ∈ Finset.range d, T.ancestorIndicator u x k) =
    G.dist r x + d at ht
  change min (T.tree.dist u x) (G.dist r x + 1) +
    (2 * early + (if d % 2 = 0 ∧ x ∈ T.branch ((T.parent^[d / 2]) u) then 1 else 0)) ≤
    G.dist r x + 1
  have hMin := min_le_left (T.tree.dist u x) (G.dist r x + 1)
  by_cases hEarly : ∃ k < m, x ∈ T.branch ((T.parent^[k]) u)
  · obtain ⟨k, hk, hx⟩ := hEarly
    have hM := T.mem_ancestor_branch_mono hk.le hm hx
    have hsum := T.fill_ancestor_suffix u x m hm hM
    change (∑ k ∈ Finset.range d, T.ancestorIndicator u x k) = early + (d - m) at hsum
    rw [hsum] at ht
    by_cases hEven : d % 2 = 0
    · have he : d / 2 = m := by omega
      rw [if_pos ⟨hEven, he.symm ▸ hM⟩]
      omega
    · rw [if_neg (fun h => hEven h.1)]
      omega
  · have hzero : early = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have h : x ∉ T.branch ((T.parent^[k]) u) := fun hx => hEarly ⟨k, Finset.mem_range.mp hk, hx⟩
      simp [ancestorIndicator, h]
    rw [hzero]
    by_cases hMid : d % 2 = 0 ∧ x ∈ T.branch ((T.parent^[d / 2]) u)
    · have hEven := hMid.1
      have he : d / 2 = m := by omega
      have hM : x ∈ T.branch ((T.parent^[m]) u) := he ▸ hMid.2
      have hsum := T.fill_ancestor_suffix u x m hm hM
      change (∑ k ∈ Finset.range d, T.ancestorIndicator u x k) = early + (d - m) at hsum
      rw [hsum, hzero] at ht
      rw [if_pos hMid]
      omega
    · simp [hMid]

private theorem sum_branch_indicator (S : Finset (Fin n)) :
    (∑ x : Fin n, if x ∈ S then (1 : ℝ) else 0) = S.card := by
  classical
  rw [← Finset.sum_filter]
  simp

/-- Membership in an ancestor branch forces all midpoint credit from
that ancestor towards the root. -/
theorem rootLinkCredit_ge_of_mem (u x : Fin n) (k : ℕ) (hk : 2 * k ≤ G.dist r u)
    (hx : x ∈ T.branch (T.parent^[k] u)) :
    G.dist r u + 1 - 2 * k ≤ T.rootLinkCredit u x := by
  classical
  let d := G.dist r u
  let m := (d + 1) / 2
  have hkm : k ≤ m := by omega
  have hSum : m - k ≤ ∑ i ∈ Finset.range m, T.ancestorIndicator u x i := by
    conv_rhs => rw [show m = k + (m - k) by omega, Finset.sum_range_add]
    have hSuffix : (∑ j ∈ Finset.range (m - k), T.ancestorIndicator u x (k + j)) = m - k := by
      calc
        _ = ∑ _j ∈ Finset.range (m - k), (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjLt := Finset.mem_range.mp hj
          have hVisit := T.mem_ancestor_branch_mono (i := k) (j := k + j) (by omega)
            (show k + j ≤ d by omega) hx
          simp [ancestorIndicator, hVisit]
        _ = _ := by simp
    rw [hSuffix]
    omega
  change d + 1 - 2 * k ≤
    2 * (∑ i ∈ Finset.range m, T.ancestorIndicator u x i) +
      (if d % 2 = 0 ∧ x ∈ T.branch (T.parent^[d / 2] u) then 1 else 0)
  by_cases hEven : d % 2 = 0
  · have hVisit := T.mem_ancestor_branch_mono (i := k) (j := d / 2) (by omega)
      (show d / 2 ≤ d by omega) hx
    rw [if_pos ⟨hEven, hVisit⟩]
    omega
  · rw [if_neg (fun h => hEven h.1)]
    omega

/-- The midpoint credit covers two units for the nearer ancestor's branch
and three units for its parent's branch, once both are within range. -/
theorem sum_rootLinkCredit_two_ancestors (u : Fin n) (k : ℕ) (hk : 2 * k + 4 ≤ G.dist r u) :
    2 * ((T.branch (T.parent^[k] u)).card : ℝ) +
      3 * ((T.branch (T.parent^[k + 1] u)).card : ℝ) ≤
      ∑ x : Fin n, (T.rootLinkCredit u x : ℝ) := by
  classical
  let S := T.branch (T.parent^[k] u)
  let P := T.branch (T.parent^[k + 1] u)
  rw [← sum_branch_indicator S, ← sum_branch_indicator P, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hPoint : (if x ∈ S then 2 else 0) + (if x ∈ P then 3 else 0) ≤ T.rootLinkCredit u x := by
    by_cases hx : x ∈ S
    · have hParent : x ∈ P := T.mem_ancestor_branch_mono (i := k) (j := k + 1)
        (by omega) (by omega) hx
      rw [if_pos hx, if_pos hParent]
      have h := T.rootLinkCredit_ge_of_mem u x k (by omega) hx
      omega
    · by_cases hParent : x ∈ P
      · rw [if_neg hx, if_pos hParent]
        have h := T.rootLinkCredit_ge_of_mem u x (k + 1) (by omega) hParent
        omega
      · simp [hx, hParent]
  by_cases hx : x ∈ S <;> by_cases hp : x ∈ P <;> simp [hx, hp] at hPoint ⊢ <;> exact_mod_cast hPoint

/-- Total midpoint credit, expressed in terms of branch sizes. -/
theorem sum_rootLinkCredit (u : Fin n) :
    (∑ x : Fin n, (T.rootLinkCredit u x : ℝ)) =
      2 * (∑ k ∈ Finset.range ((G.dist r u + 1) / 2), ((T.branch ((T.parent^[k]) u)).card : ℝ)) +
      (if G.dist r u % 2 = 0 then ((T.branch ((T.parent^[G.dist r u / 2]) u)).card : ℝ) else 0) := by
  classical
  let d := G.dist r u
  unfold rootLinkCredit
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    simp only [ancestorIndicator, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact sum_branch_indicator _
  · by_cases he : d % 2 = 0 <;> simp [d, he]

#print axioms min_tree_root_link_le
#print axioms sum_rootLinkCredit
#print axioms sum_rootLinkCredit_two_ancestors

end Lax869952Proofs.ShortestParents
