import Lax869952Proofs.RootLinkBudget

set_option warningAsError true

namespace Lax869952Proofs.ShortestParents

open SimpleGraph Function
open scoped BigOperators

variable {n : ℕ} {G : SimpleGraph (Fin n)} {r : Fin n} (T : ShortestParents G r)

private theorem cast_rootLinkCredit_ge_of_mem (u x : Fin n) (k : ℕ) (hk : 2 * k ≤ G.dist r u)
    (hx : x ∈ T.branch (T.parent^[k] u)) :
    (G.dist r u : ℝ) + 1 - 2 * (k : ℝ) ≤ (T.rootLinkCredit u x : ℝ) := by
  have h : ((G.dist r u + 1 - 2 * k : ℕ) : ℝ) ≤ (T.rootLinkCredit u x : ℝ) := by
    exact_mod_cast T.rootLinkCredit_ge_of_mem u x k hk hx
  simpa only [Nat.cast_sub (hk.trans (Nat.le_succ _)), Nat.cast_add, Nat.cast_one,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ] using h

private theorem sum_const_on_branch (S : Finset (Fin n)) (c : ℝ) [DecidablePred (· ∈ S)] :
    (∑ x : Fin n, if x ∈ S then c else 0) = c * (S.card : ℝ) := by
  rw [← Finset.sum_filter]
  simp [mul_comm]

/-- Retaining the two nearest ancestor branches gives a lower bound on
the total distance savings in the root-link deviation. -/
theorem sum_rootLinkCredit_parent_lower (u : Fin n) (hd : 2 ≤ G.dist r u) :
    2 * ((T.branch u).card : ℝ) +
      ((G.dist r u : ℝ) - 1) * ((T.branch (T.parent u)).card : ℝ) ≤
      ∑ x : Fin n, (T.rootLinkCredit u x : ℝ) := by
  classical
  rw [← sum_const_on_branch, ← sum_const_on_branch, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x ∈ T.branch u
  · have hxp := T.mem_branch_iterate hx 1 (by omega)
    simp only [Function.iterate_one] at hxp
    have h := T.cast_rootLinkCredit_ge_of_mem u x 0 (by omega)
      (by simpa only [Function.iterate_zero_apply] using hx)
    simp only [if_pos hx, if_pos hxp]
    simp only [Nat.cast_zero, mul_zero, sub_zero] at h
    linarith
  · by_cases hxp : x ∈ T.branch (T.parent u)
    · have h := T.cast_rootLinkCredit_ge_of_mem u x 1 (by omega)
        (by simpa only [Function.iterate_one] using hxp)
      simp only [if_neg hx, if_pos hxp, zero_add]
      norm_num at h
      linarith
    · simp [hx, hxp]

/-- Keeping the first three ancestor branches improves the two-branch
bound when the buyer is at depth four or greater. -/
theorem sum_rootLinkCredit_grandparent_lower (u : Fin n) (hd : 3 ≤ G.dist r u) :
    2 * ((T.branch u).card : ℝ) + 2 * ((T.branch (T.parent u)).card : ℝ) +
      ((G.dist r u : ℝ) - 3) * ((T.branch (T.parent (T.parent u))).card : ℝ) ≤
      ∑ x : Fin n, (T.rootLinkCredit u x : ℝ) := by
  classical
  by_cases hThree : G.dist r u = 3
  · have h := T.sum_rootLinkCredit_parent_lower u (by omega)
    norm_num [hThree] at h ⊢
    exact h
  have hFour : 4 ≤ G.dist r u := by omega
  rw [← sum_const_on_branch, ← sum_const_on_branch, ← sum_const_on_branch,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x ∈ T.branch u
  · have hxp : x ∈ T.branch (T.parent u) := by
      simpa only [Function.iterate_one] using T.mem_branch_iterate hx 1 (by omega)
    have hxg : x ∈ T.branch (T.parent (T.parent u)) := by
      simpa only [Function.iterate_succ_apply, Function.iterate_one, Function.iterate_zero_apply] using
        T.mem_branch_iterate hx 2 (by omega)
    have h := T.cast_rootLinkCredit_ge_of_mem u x 0 (by omega)
      (by simpa only [Function.iterate_zero_apply] using hx)
    simp only [if_pos hx, if_pos hxp, if_pos hxg]
    simp only [Nat.cast_zero, mul_zero, sub_zero] at h
    linarith
  · by_cases hxp : x ∈ T.branch (T.parent u)
    · have hxg : x ∈ T.branch (T.parent (T.parent u)) := by
        have h := T.mem_ancestor_branch_mono (u := u) (i := 1) (j := 2) (by decide) (by omega)
          (by simpa only [Function.iterate_one] using hxp)
        simpa only [Function.iterate_succ_apply, Function.iterate_one, Function.iterate_zero_apply] using h
      have h := T.cast_rootLinkCredit_ge_of_mem u x 1 (by omega)
        (by simpa only [Function.iterate_one] using hxp)
      simp only [if_neg hx, if_pos hxp, if_pos hxg, zero_add]
      norm_num at h
      linarith
    · by_cases hxg : x ∈ T.branch (T.parent (T.parent u))
      · have h := T.cast_rootLinkCredit_ge_of_mem u x 2 (by omega)
          (by simpa only [Function.iterate_succ_apply, Function.iterate_one, Function.iterate_zero_apply] using hxg)
        simp only [if_neg hx, if_neg hxp, if_pos hxg, zero_add]
        norm_num at h
        linarith
      · simp [hx, hxp, hxg]

#print axioms sum_rootLinkCredit_grandparent_lower

end Lax869952Proofs.ShortestParents
