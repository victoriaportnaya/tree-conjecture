import TreeConjecture.CycleCertificate

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ}

noncomputable def geodesicPurchases (s : Profile n) (u v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun w =>
    w ∈ (s u).val ∧ (graph s).dist w v + 1 = (graph s).dist u v

private theorem geodesicPurchases_mem (s : Profile n) (u v w : Fin n) :
    w ∈ geodesicPurchases s u v ↔
      w ∈ (s u).val ∧ (graph s).dist w v + 1 = (graph s).dist u v := by
  simp [geodesicPurchases]

theorem nash_geodesic_purchases_redirect_bound (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {u v : Fin n} (huv : u ≠ v) :
    distanceSum (graph s) u + (α : ℝ) * (geodesicPurchases s u v).card +
        ((graph s).dist u v : ℝ) + 1 ≤
      distanceSum (graph s) v + (n : ℝ) + (α : ℝ) := by
  classical
  let G := graph s
  let sold := geodesicPurchases s u v
  let t := redirect s u v huv sold
  let H := graph t
  have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have hNew : H.Adj u v := redirect_adj_target s huv sold
  have hRepair (w : Fin n) (hw : w = u ∨ w ∈ sold) :
      ∃ p : H.Walk v w, p.length ≤ G.dist v w := by
    rcases hw with hu | hw
    · subst w
      have hPos : 0 < G.dist v u := hG.pos_dist_of_ne huv.symm
      exact ⟨.cons hNew.symm .nil, by change 1 ≤ G.dist v u; omega⟩
    · have hCloser := ((geodesicPurchases_mem s u v w).mp hw).2
      obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v w
      have hAvoid : u ∉ p.support := by
        intro hu
        obtain ⟨a, b, he⟩ := p.mem_support_iff_exists_append.mp hu
        have ha := dist_le a
        rw [he, Walk.length_append, dist_comm] at hp
        change a.length + b.length = G.dist w v at hp
        rw [dist_comm] at ha
        change G.dist u v ≤ a.length at ha
        change G.dist w v + 1 = G.dist u v at hCloser
        omega
      obtain ⟨q, hq⟩ := transport_avoiding (H := H)
        (fun ha hb hab => redirect_preserves_adj hab (Or.inl ha) (Or.inl hb)) p hAvoid
      exact ⟨q, (hq.trans hp).le⟩
  obtain ⟨hH, hDist⟩ := redirect_preserves_target_distances s hG huv sold hRepair
  have hPoint (w : Fin n) :
      (H.dist u w : ℝ) + (if w = u then ((G.dist u v : ℝ) + 1) else 0) ≤
        (G.dist v w : ℝ) + 1 := by
    by_cases hw : w = u
    · subst w
      simp [dist_comm]
    · have hTri : H.dist u w ≤ H.dist u v + H.dist v w := hH.dist_triangle
      rw [dist_eq_one_iff_adj.mpr hNew] at hTri
      have hRoute : H.dist u w ≤ G.dist v w + 1 := by
        have hh := hDist w
        change H.dist v w ≤ G.dist v w at hh
        omega
      simp only [if_neg hw, add_zero]
      exact_mod_cast hRoute
  have hSum := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin n))) => hPoint w)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hSum
  change distanceSum H u + ((G.dist u v : ℝ) + 1) ≤ distanceSum G v + (n : ℝ) at hSum
  have hCost := nash_finite_cost_le α s t hG hH hne u (fun j hj => redirect_other s huv sold hj)
  have hCard : ((t u).val.ncard : ℝ) + (sold.card : ℝ) ≤ ((s u).val.ncard : ℝ) + 1 := by
    exact_mod_cast redirect_card_le s huv sold
      (fun j hj => ((geodesicPurchases_mem s u v j).mp hj).1)
  have hMul := mul_le_mul_of_nonneg_left hCard (NNReal.zero_le_coe : (0 : ℝ) ≤ α)
  unfold finiteCost at hCost
  change (α : ℝ) * (s u).val.ncard + distanceSum G u ≤
    (α : ℝ) * (t u).val.ncard + distanceSum H u at hCost
  change distanceSum G u + (α : ℝ) * sold.card + (G.dist u v : ℝ) + 1 ≤ _
  linarith

theorem nash_geodesic_purchases_pair_count (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {u v : Fin n} (huv : u ≠ v) :
    (α : ℝ) * (((geodesicPurchases s u v).card : ℝ) +
        ((geodesicPurchases s v u).card : ℝ) - 2) +
      2 * (((graph s).dist u v : ℝ) + 1) ≤ 2 * (n : ℝ) := by
  have hFor := nash_geodesic_purchases_redirect_bound s α hne huv
  have hBack := nash_geodesic_purchases_redirect_bound s α hne huv.symm
  rw [dist_comm (u := v) (v := u)] at hBack
  linarith

theorem nash_geodesic_purchases_pair_bound (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {u v : Fin n} (huv : u ≠ v)
    (hFour : 4 ≤ (geodesicPurchases s u v).card + (geodesicPurchases s v u).card) :
    (α : ℝ) + ((graph s).dist u v : ℝ) + 1 ≤ n := by
  have hPair := nash_geodesic_purchases_pair_count s α hne huv
  have hCard : (4 : ℝ) ≤ ((geodesicPurchases s u v).card : ℝ) +
      ((geodesicPurchases s v u).card : ℝ) := by exact_mod_cast hFour
  have hMul := mul_le_mul_of_nonneg_left hCard (NNReal.zero_le_coe : (0 : ℝ) ≤ α)
  linarith

theorem nash_octagon_opposite_buyers_bound {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (e : CycleCertificate.Embedding (graph s) 8)
    (h01 : e.vertex 1 ∈ (s (e.vertex 0)).val)
    (h07 : e.vertex 7 ∈ (s (e.vertex 0)).val)
    (h43 : e.vertex 3 ∈ (s (e.vertex 4)).val)
    (h45 : e.vertex 5 ∈ (s (e.vertex 4)).val) :
    (α : ℝ) + 5 ≤ n := by
  have hCard {u v a b : Fin 8} (hab : a ≠ b)
      (ha : e.vertex a ∈ (s (e.vertex u)).val)
      (hb : e.vertex b ∈ (s (e.vertex u)).val)
      (hA : CycleCertificate.cycleDistance a v + 1 = CycleCertificate.cycleDistance u v)
      (hB : CycleCertificate.cycleDistance b v + 1 = CycleCertificate.cycleDistance u v) :
      2 ≤ (geodesicPurchases s (e.vertex u) (e.vertex v)).card := by
    classical
    have hDistA := (geodesicPurchases_mem s (e.vertex u) (e.vertex v) (e.vertex a)).mpr
      ⟨ha, by rw [e.isometric, e.isometric]; exact hA⟩
    have hDistB := (geodesicPurchases_mem s (e.vertex u) (e.vertex v) (e.vertex b)).mpr
      ⟨hb, by rw [e.isometric, e.isometric]; exact hB⟩
    have hSub : {e.vertex a, e.vertex b} ⊆ geodesicPurchases s (e.vertex u) (e.vertex v) :=
      Finset.insert_subset_iff.mpr ⟨hDistA, Finset.singleton_subset_iff.mpr hDistB⟩
    simpa [e.vertex.injective.ne hab] using Finset.card_le_card hSub
  have hLeft := hCard (u := 0) (v := 4) (by decide : (1 : Fin 8) ≠ 7)
    h01 h07 (by decide) (by decide)
  have hRight := hCard (u := 4) (v := 0) (by decide : (3 : Fin 8) ≠ 5)
    h43 h45 (by decide) (by decide)
  have h := nash_geodesic_purchases_pair_bound s α hne
    (e.vertex.injective.ne (by decide : (0 : Fin 8) ≠ (4 : Fin 8))) (by omega)
  rw [e.isometric] at h
  have hD : CycleCertificate.cycleDistance (0 : Fin 8) 4 = 4 := by decide
  rw [hD] at h
  norm_num at h ⊢
  linarith

#print axioms nash_geodesic_purchases_pair_count
#print axioms nash_octagon_opposite_buyers_bound

end TreeConjecture
