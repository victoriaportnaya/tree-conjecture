import TreeConjecture.Foundations

set_option warningAsError true

namespace TreeConjecture

open scoped BigOperators

/-- Dippel–Vetta (2024), Lemma 6. If the root has no greater connection
cost than v, at most half the vertices can lie in a shortest-path branch through v.

The branch is represented by its defining geodesic equality. This includes
the descendants of v in any shortest-path tree rooted at root. -/
theorem rooted_shortest_path_branch_size {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.Connected) {root v : Fin n} (hne : root ≠ v)
    (hcost : distanceSum G root ≤ distanceSum G v) (branch : Finset (Fin n))
    (hbranch : ∀ x ∈ branch, G.dist root x = G.dist root v + G.dist v x) :
    2 * branch.card ≤ n := by
  classical
  let radius := (G.dist root v : ℝ)
  have hradius : 0 < radius := by
    dsimp [radius]
    exact_mod_cast hG.pos_dist_of_ne hne
  let credit (x : Fin n) : ℝ := if x ∈ branch then 2 * radius else 0
  have hcredit : ∑ x, credit x = (branch.card : ℝ) * (2 * radius) := by
    calc
      _ = ∑ x ∈ branch, credit x := by
        symm
        exact Finset.sum_subset (Finset.subset_univ branch) (fun x _ hx => by simp [credit, hx])
      _ = _ := by simp [credit]
  have hbound : distanceSum G v ≤ ∑ x, ((G.dist root x : ℝ) + radius - credit x) := by
    unfold distanceSum
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : x ∈ branch
    · have hdist : (G.dist root x : ℝ) = radius + (G.dist v x : ℝ) := by
        dsimp [radius]
        exact_mod_cast hbranch x hx
      simp only [credit, if_pos hx]
      linarith
    · have htriangle : G.dist v x ≤ G.dist v root + G.dist root x := hG.dist_triangle
      rw [SimpleGraph.dist_comm (u := v) (v := root)] at htriangle
      have hdist : (G.dist v x : ℝ) ≤ radius + (G.dist root x : ℝ) := by
        dsimp [radius]
        exact_mod_cast htriangle
      simp only [credit, if_neg hx, sub_zero]
      linarith
  have ht : distanceSum G v ≤
      distanceSum G root + (n : ℝ) * radius - (branch.card : ℝ) * (2 * radius) := by
    simpa only [distanceSum, Finset.sum_sub_distrib, Finset.sum_add_distrib, hcredit,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hbound
  have hsize : 2 * (branch.card : ℝ) ≤ (n : ℝ) := by
    by_contra! htoo
    have hprod := mul_pos hradius (sub_pos.mpr htoo)
    nlinarith
  exact_mod_cast hsize

#print axioms rooted_shortest_path_branch_size

end TreeConjecture
