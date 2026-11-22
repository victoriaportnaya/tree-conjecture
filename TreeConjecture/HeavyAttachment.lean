import TreeConjecture.Addition
import TreeConjecture.WeightedBlocks
import TreeConjecture.Redirect

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped NNReal BigOperators

/-- A link to a distant block vertex saves on its entire attachment and
on the attachment of each specified neighboring block vertex. -/
theorem nash_block_shortcut_two_attachment_bound {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S)
    {u x y : Fin n} (hu : u ∈ S) (hxy : (blockGraph (graph s) S).Adj x y)
    (hFar : 2 ≤ (graph s).dist u x) :
    (((graph s).dist u x : ℝ) - 1) * (blockAttachment (graph s) S x).card +
      (((graph s).dist u x : ℝ) - 3) * (blockAttachment (graph s) S y).card ≤ α := by
  classical
  let G := graph s
  let A := blockAttachment G S x
  let B := blockAttachment G S y
  let gain (z : Fin n) : ℝ := max 0 ((G.dist u z : ℝ) - (G.dist x z : ℝ) - 1)
  have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have hne' : u ≠ x := by
    rintro rfl
    simp at hFar
  have hNotAdj : ¬ G.Adj u x := by
    intro h
    have hOne := dist_eq_one_iff_adj.mpr h
    change 2 ≤ G.dist u x at hFar
    omega
  have saving := nash_addition_distance_bound s α hne hne' hNotAdj
  change (∑ z : Fin n, gain z) ≤ (α : ℝ) at saving
  have xBound (z : Fin n) (hz : z ∈ A) : (G.dist u x : ℝ) - 1 ≤ gain z := by
    have hDist := hS.dist_add_of_mem_blockAttachment hG hxy.1 hu hz
    change G.dist u z = G.dist u x + G.dist x z at hDist
    dsimp only [gain]
    rw [hDist, Nat.cast_add]
    linarith only [le_max_right (0 : ℝ)
      ((G.dist u x : ℝ) + (G.dist x z : ℝ) - (G.dist x z : ℝ) - 1)]
  have hOne : G.dist x y = 1 := dist_eq_one_iff_adj.mpr (blockGraph_le G S hxy)
  have hTriangle : (G.dist u x : ℝ) ≤ (G.dist u y : ℝ) + 1 := by
    have triangle : G.dist u x ≤ G.dist u y + G.dist y x := hG.dist_triangle
    rw [dist_comm (u := y), hOne] at triangle
    exact_mod_cast triangle
  have yBound (z : Fin n) (hz : z ∈ B) : (G.dist u x : ℝ) - 3 ≤ gain z := by
    have huDist := hS.dist_add_of_mem_blockAttachment hG hxy.2.1 hu hz
    have hxDist := hS.dist_add_of_mem_blockAttachment hG hxy.2.1 hxy.1 hz
    change G.dist u z = G.dist u y + G.dist y z at huDist
    change G.dist x z = G.dist x y + G.dist y z at hxDist
    dsimp only [gain]
    rw [huDist, hxDist, hOne, Nat.cast_add, Nat.cast_add, Nat.cast_one]
    linarith only [hTriangle, le_max_right (0 : ℝ)
      ((G.dist u y : ℝ) + (G.dist y z : ℝ) - (1 + (G.dist y z : ℝ)) - 1)]
  have hDisjoint : Disjoint A B := hS.disjoint_blockAttachments hxy.1 hxy.2.1
    (blockGraph_le G S hxy).ne
  calc
    _ = (∑ _z ∈ A, ((G.dist u x : ℝ) - 1)) +
        ∑ _z ∈ B, ((G.dist u x : ℝ) - 3) := by
      simp [A, B, G, nsmul_eq_mul, sub_mul, mul_comm]
    _ ≤ (∑ z ∈ A, gain z) + ∑ z ∈ B, gain z :=
      add_le_add (Finset.sum_le_sum xBound) (Finset.sum_le_sum yBound)
    _ = ∑ z ∈ A ∪ B, gain z := (Finset.sum_union hDisjoint).symm
    _ ≤ ∑ z : Fin n, gain z := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun z _ _ => le_max_left _ _)
    _ ≤ α := saving

/-- In the possible price range for a non-tree equilibrium, a vertex
carrying half the attachments has block eccentricity at most four. -/
theorem nash_block_half_attachment_eccentricity_le_four {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hPrice : α ≤ 2 * (n : ℝ≥0)) (hne : IsNashEquilibrium α s)
    {S : Finset (Fin n)} (hS : IsBiconnectedBlock (graph s) S)
    {x : Fin n} (hx : x ∈ S) (hMass : n ≤ 2 * (blockAttachment (graph s) S x).card)
    {u : Fin n} (hu : u ∈ S) : (graph s).dist u x ≤ 4 := by
  by_contra! h
  obtain ⟨y, _, hy, _, _⟩ := hS.twoConnected.exists_two_neighbors hx
  have hBound := nash_block_shortcut_two_attachment_bound s α hne hS hu hy (by omega)
  have hX : (0 : ℝ) ≤ (blockAttachment (graph s) S x).card := Nat.cast_nonneg _
  have hY : (0 : ℝ) < (blockAttachment (graph s) S y).card := by
    exact_mod_cast (blockAttachment_card_pos (G := graph s) (S := S) y)
  have hD : (5 : ℝ) ≤ (graph s).dist u x := by exact_mod_cast (show 5 ≤ (graph s).dist u x by omega)
  have hAlpha : (α : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hPrice
  have hW : (n : ℝ) ≤ 2 * (blockAttachment (graph s) S x).card := by exact_mod_cast hMass
  have hxCost := mul_le_mul_of_nonneg_right (show (4 : ℝ) ≤ ((graph s).dist u x : ℝ) - 1 by linarith) hX
  have hyCost := mul_pos (show (0 : ℝ) < ((graph s).dist u x : ℝ) - 3 by linarith) hY
  linarith only [hxCost, hyCost, hBound, hAlpha, hW]

/-- A buyer at distance at least two cannot buy a link one step closer to
a block vertex carrying at least half the players. -/
theorem nash_no_inward_purchase_toward_half_attachment {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S)
    {u x v : Fin n} (hu : u ∈ S) (hx : x ∈ S)
    (hMass : n ≤ 2 * (blockAttachment (graph s) S x).card)
    (hFar : 2 ≤ (graph s).dist u x)
    (hDepth : (graph s).dist v x + 1 = (graph s).dist u x) :
    v ∉ (s u).val := by
  classical
  intro bought
  let G := graph s
  let A := blockAttachment G S x
  let c : ℝ := (G.dist v x : ℝ)
  have huv : u ≠ v := (show G.Adj u v from Or.inl bought).ne
  have hux : u ≠ x := by
    rintro rfl
    simp at hFar
  have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  let t := redirect s u x hux {v}
  let D := graph t
  have newLink : D.Adj u x := redirect_adj_target s hux {v}
  have keepAway {a b : Fin n} (ha : a ≠ u) (hb : b ≠ u) (hab : G.Adj a b) :
      D.Adj a b := redirect_preserves_adj hab (Or.inl ha) (Or.inl hb)
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x v
  have avoid : u ∉ p.support := by
    intro hm
    obtain ⟨p₁, p₂, he⟩ := p.mem_support_iff_exists_append.mp hm
    have ha : G.dist x u ≤ p₁.length := dist_le p₁
    rw [he, Walk.length_append, dist_comm (u := x) (v := v)] at hp
    rw [dist_comm (u := x) (v := u)] at ha
    change G.dist v x + 1 = G.dist u x at hDepth
    change p₁.length + p₂.length = G.dist v x at hp
    omega
  obtain ⟨q, hq⟩ := transport_avoiding keepAway p avoid
  have qLen : q.length = G.dist v x := by
    rw [hq, hp, dist_comm]
  obtain ⟨hD, rootBound⟩ := redirect_preserves_target_distances s hG hux {v}
    (fun z hz => by
      rcases hz with eq | hz
      · subst z
        exact ⟨.cons newLink.symm .nil, by
          rw [dist_comm]
          change 1 ≤ (graph s).dist u x
          omega⟩
      · have eq := Finset.mem_singleton.mp hz
        subst z
        exact ⟨q, by rw [qLen, dist_comm]⟩)
  have allDest (z : Fin n) : D.dist u z ≤ G.dist u z + G.dist v x := by
    obtain ⟨old, oldPath, oldLen⟩ := hG.exists_path_of_dist u z
    cases old with
    | nil => simp
    | @cons _ a _ edge tail =>
      have hAvoid := (Walk.cons_isPath_iff edge tail).mp oldPath |>.2
      obtain ⟨bypass, bypassLen⟩ := transport_avoiding keepAway tail hAvoid
      rw [Walk.length_cons] at oldLen
      change tail.length + 1 = G.dist u z at oldLen
      by_cases ha : a = v
      · subst a
        have bound := dist_le (Walk.cons newLink (q.append bypass))
        rw [Walk.length_cons, Walk.length_append, qLen, bypassLen] at bound
        omega
      · have edge' : D.Adj u a := redirect_preserves_adj edge
          (Or.inr (by simp [ha])) (Or.inl edge.ne.symm)
        have bound := dist_le (Walk.cons edge' bypass)
        rw [Walk.length_cons, bypassLen, oldLen] at bound
        exact bound.trans (Nat.le_add_right _ _)
  have uNotA : u ∉ A := by
    have disjoint := hS.disjoint_blockAttachments hx hu hux.symm
    intro hm
    apply Finset.disjoint_left.mp disjoint hm
    exact mem_blockAttachment.mpr ⟨.nil, by simp [FirstEntryInto]⟩
  have point (z : Fin n) :
      (D.dist u z : ℝ) - (G.dist u z : ℝ) ≤
        c - (if z ∈ A then 2 * c else 0) - (if z = u then c else 0) := by
    by_cases hzA : z ∈ A
    · have hzu : z ≠ u := by rintro rfl; exact uNotA hzA
      have old := hS.dist_add_of_mem_blockAttachment hG hx hu hzA
      have newDist : D.dist u z ≤ D.dist u x + D.dist x z := hD.dist_triangle
      rw [dist_eq_one_iff_adj.mpr newLink] at newDist
      have upper : D.dist u z ≤ 1 + G.dist x z := newDist.trans (Nat.add_le_add_left (rootBound z) 1)
      have boundReal : (D.dist u z : ℝ) ≤ 1 + (G.dist x z : ℝ) := by exact_mod_cast upper
      have oldReal : (G.dist u z : ℝ) = (G.dist u x : ℝ) + (G.dist x z : ℝ) := by
        exact_mod_cast old
      have levels : (G.dist u x : ℝ) = c + 1 := by
        dsimp [c]
        exact_mod_cast hDepth.symm
      simp [hzA, hzu]
      linarith only [boundReal, oldReal, levels]
    · by_cases hzu : z = u
      · subst z
        simp [uNotA]
      · simp [hzA, hzu]
        have h : (D.dist u z : ℝ) ≤ (G.dist u z : ℝ) + c := by
          dsimp [c]
          exact_mod_cast allDest z
        linarith only [h]
  have summed := Finset.sum_le_sum
    (fun z (_ : z ∈ (Finset.univ : Finset (Fin n))) => point z)
  have indicator : (∑ z : Fin n, if z ∈ A then 2 * c else 0) = (A.card : ℝ) * (2 * c) := by
    rw [← Finset.sum_filter]
    simp [nsmul_eq_mul]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, indicator] at summed
  change distanceSum D u - distanceSum G u ≤ (n : ℝ) * c - A.card * (2 * c) - c at summed
  have hn : (n : ℝ) ≤ 2 * A.card := by exact_mod_cast hMass
  have hcNat : 0 < G.dist v x := by
    change 2 ≤ G.dist u x at hFar
    change G.dist v x + 1 = G.dist u x at hDepth
    omega
  have hc : 0 < c := by
    change (0 : ℝ) < (G.dist v x : ℝ)
    exact_mod_cast hcNat
  have hMul := mul_le_mul_of_nonneg_right hn hc.le
  have neSwap := nash_swap_distanceSum_le s α hne hux bought hD
  change distanceSum G u ≤ distanceSum D u at neSwap
  linarith only [summed, hMul, hc, neSwap]

#print axioms nash_no_inward_purchase_toward_half_attachment
#print axioms nash_block_shortcut_two_attachment_bound
#print axioms nash_block_half_attachment_eccentricity_le_four

end TreeConjecture
