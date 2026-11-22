import TreeConjecture.Redirect
import TreeConjecture.Girth
import TreeConjecture.EdgeMinCycles

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped NNReal

private lemma segment_walk {V : Type*} {G H : SimpleGraph V} {r : V}
    (p : G.Walk r r) {a b : ℕ} (hab : a ≤ b)
    (hkeep : ∀ j, a ≤ j → j < b → H.Adj (p.getVert j) (p.getVert (j + 1))) :
    ∃ q : H.Walk (p.getVert a) (p.getVert b), q.length = b - a := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨.nil, by simp⟩
  | succ b hab ih =>
    obtain ⟨q, hq⟩ := ih (fun j hj hjb => hkeep j hj (by omega))
    exact ⟨q.concat (hkeep b hab (by omega)), by rw [Walk.length_concat, hq]; omega⟩

private lemma cycle_vertex_ne {V : Type*} {G : SimpleGraph V} {r : V}
    {p : G.Walk r r} (hp : p.IsCycle) {i j : ℕ}
    (hi : i < p.length) (hj : j < p.length) (hne : i ≠ j) :
    p.getVert i ≠ p.getVert j := fun he =>
  hne (hp.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) he)

private lemma cycle_getVert_ne_root {V : Type*} {G : SimpleGraph V} {r : V}
    {p : G.Walk r r} (hp : p.IsCycle) {j : ℕ} (hj : 0 < j) (hk : j < p.length) :
    p.getVert j ≠ r := by
  simpa only [Walk.getVert_zero] using cycle_vertex_ne hp hk (show 0 < p.length by omega)
    (show j ≠ 0 by omega)

private lemma cycle_edges_ne {V : Type*} {G : SimpleGraph V} {r : V}
    {p : G.Walk r r} (hp : p.IsCycle) {i j : ℕ}
    (hi : i < p.length) (hj : j < p.length) (hne : i ≠ j) :
    s(p.getVert i, p.getVert (i + 1)) ≠ s(p.getVert j, p.getVert (j + 1)) := by
  have hi' : i < p.edges.length := by simp [hi]
  have hj' : j < p.edges.length := by simp [hj]
  rw [← Walk.getElem_edges hi', ← Walk.getElem_edges hj']
  exact fun he => hne (hp.isTrail.edges_nodup.getElem_inj_iff.mp he)

/-- The two deviations at a source of an isometric cycle bound the
price by twice the number of players minus the size of the cycle. -/
theorem nash_cycle_root_two_purchases_price_bound {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s)
    {r : Fin n} (p : (graph s).Walk r r) (hp : p.IsCycle) (hgeo : CycleDistances p)
    (hfirst : p.getVert 1 ∈ (s r).val)
    (hlast : p.getVert (p.length - 1) ∈ (s r).val) :
    (α : ℝ) + (2 * ((p.length - 1) / 2) + 2 : ℕ) ≤ 2 * (n : ℝ) := by
  classical
  let m := (p.length - 1) / 2
  have hk := hp.three_le_length
  have hmid : 1 ≤ m ∧ m + 1 < p.length ∧ 2 * m ≤ p.length ∧ p.length ≤ 2 * m + 2 := by
    dsimp [m]
    omega
  have hfar := p.adj_getVert_succ (i := m) (by omega)
  obtain ⟨j, l, hloc, howner⟩ : ∃ j l : ℕ,
      (j = m ∧ l = m + 1 ∨ j = m + 1 ∧ l = m) ∧ p.getVert l ∈ (s (p.getVert j)).val := by
    exact hfar.elim (fun h => ⟨m, m + 1, Or.inl ⟨rfl, rfl⟩, h⟩)
      (fun h => ⟨m + 1, m, Or.inr ⟨rfl, rfl⟩, h⟩)
  have hj : m ≤ j ∧ j ≤ m + 1 := by omega
  let u := p.getVert j
  let w := p.getVert l
  have hur : u ≠ r := cycle_getVert_ne_root hp (by omega) (by omega)
  have hw : w ∈ (s u).val := howner
  have hEdge : s(u, w) = s(p.getVert m, p.getVert (m + 1)) := by
    rcases hloc with ⟨hj', hl'⟩ | ⟨hj', hl'⟩
    · simp [u, w, hj', hl']
    · simp [u, w, hj', hl', Sym2.eq_swap]
  have hG := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  have hswap : distanceSum (graph s) u + ((graph s).dist r u : ℝ) ≤
      distanceSum (graph s) r + ((n - 1 : ℕ) : ℝ) := by
    let H := graph (redirect s u r hur {w})
    have hkeep (i : ℕ) (hi : i < p.length) (him : i ≠ m) :
        H.Adj (p.getVert i) (p.getVert (i + 1)) := by
      apply redirect_preserves_other_edge (p.adj_getVert_succ hi)
      intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx, hEdge]
      exact cycle_edges_ne hp hi (by omega) him
    obtain ⟨q₀, hq₀⟩ := segment_walk (H := H) p (show 0 ≤ m by omega)
      (fun i _ hi => hkeep i (by omega) (by omega))
    obtain ⟨q₁, hq₁⟩ := segment_walk (H := H) p (show m + 1 ≤ p.length by omega)
      (fun i hi hik => hkeep i hik (by omega))
    have hleft : (graph s).dist r (p.getVert m) = m := by
      have hd := hgeo 0 m (Nat.zero_le _) (by omega)
      simpa [Walk.getVert_zero, Nat.min_eq_left (show m ≤ p.length - m by omega)] using hd
    have hright : (graph s).dist r (p.getVert (m + 1)) = p.length - (m + 1) := by
      have hd := hgeo 0 (m + 1) (Nat.zero_le _) (by omega)
      simpa [Walk.getVert_zero,
        Nat.min_eq_right (show p.length - (m + 1) ≤ m + 1 by omega)] using hd
    have hrepair : ∀ x, x = u ∨ x ∈ ({w} : Finset (Fin n)) →
        ∃ p' : H.Walk r x, p'.length ≤ (graph s).dist r x := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      have hxmid : x = p.getVert m ∨ x = p.getVert (m + 1) := by
        rcases hloc with ⟨hj', hl'⟩ | ⟨hj', hl'⟩
        · simpa [u, w, hj', hl'] using hx
        · simpa [u, w, hj', hl', or_comm] using hx
      rcases hxmid with rfl | rfl
      · exact ⟨q₀.copy p.getVert_zero rfl, by simp [hq₀, hleft]⟩
      · exact ⟨q₁.reverse.copy p.getVert_length rfl, by simp [hq₁, hright]⟩
    have bound := nash_redirect_with_buyer_distance s α hne hur ({w} : Finset (Fin n))
      (fun x hx => (Finset.mem_singleton.mp hx).symm ▸ hw) hrepair
    simp at bound
    linarith
  have hdouble : distanceSum (graph s) r + (α : ℝ) + ((graph s).dist u r : ℝ) ≤
      distanceSum (graph s) u + ((n - 1 : ℕ) : ℝ) := by
    let sold : Finset (Fin n) := {p.getVert 1, p.getVert (p.length - 1)}
    let H := graph (redirect s r u hur.symm sold)
    have hkeep (i : ℕ) (hi : 1 ≤ i) (hik : i + 1 < p.length) :
        H.Adj (p.getVert i) (p.getVert (i + 1)) :=
      redirect_preserves_adj (p.adj_getVert_succ (by omega))
        (Or.inl (cycle_getVert_ne_root hp (by omega) (by omega)))
        (Or.inl (cycle_getVert_ne_root hp (by omega) hik))
    obtain ⟨q₀, hq₀⟩ := segment_walk (H := H) p (show 1 ≤ j by omega)
      (fun i hi hij => hkeep i hi (by omega))
    obtain ⟨q₁, hq₁⟩ := segment_walk (H := H) p (show j ≤ p.length - 1 by omega)
      (fun i hi hik => hkeep i (by omega) (by omega))
    have hd₀ : (graph s).dist u (p.getVert 1) = j - 1 := by
      change (graph s).dist (p.getVert j) (p.getVert 1) = _
      rw [SimpleGraph.dist_comm, hgeo 1 j (by omega) (by omega)]
      exact Nat.min_eq_left (by omega)
    have hd₁ : (graph s).dist u (p.getVert (p.length - 1)) = p.length - 1 - j := by
      change (graph s).dist (p.getVert j) (p.getVert (p.length - 1)) = _
      rw [hgeo j (p.length - 1) (by omega) (by omega)]
      exact Nat.min_eq_left (by omega)
    have hrepair : ∀ x, x = r ∨ x ∈ sold →
        ∃ p' : H.Walk u x, p'.length ≤ (graph s).dist u x := by
      intro x hx
      rcases hx with hx | hx
      · subst x
        have hlink : H.Adj r u := redirect_adj_target s hur.symm sold
        exact ⟨hlink.symm.toWalk, by simpa using Nat.succ_le_of_lt (hG.pos_dist_of_ne hur)⟩
      · have hx' : x = p.getVert 1 ∨ x = p.getVert (p.length - 1) := by simpa [sold] using hx
        rcases hx' with rfl | rfl
        · exact ⟨q₀.reverse, by simp [hq₀, hd₀]⟩
        · exact ⟨q₁, by simp [hq₁, hd₁]⟩
    have hbuy : ∀ x ∈ sold, x ∈ (s r).val := by
      intro x hx
      have hx' : x = p.getVert 1 ∨ x = p.getVert (p.length - 1) := by simpa [sold] using hx
      rcases hx' with rfl | rfl
      · exact hfirst
      · exact hlast
    have hcard : sold.card = 2 := by
      have hneigh : p.getVert 1 ≠ p.getVert (p.length - 1) :=
        cycle_vertex_ne hp (by omega) (by omega) (by omega)
      simp [sold, hneigh]
    have bound := nash_redirect_with_buyer_distance s α hne hur.symm sold hbuy hrepair
    rw [hcard] at bound
    norm_num at bound
    linarith
  have hDistance : m ≤ (graph s).dist r u := by
    have hD := hgeo 0 j (Nat.zero_le _) (by omega)
    rw [Walk.getVert_zero] at hD
    change (graph s).dist r u = min j (p.length - j) at hD
    have hLen : 2 * m + 1 ≤ p.length := by dsimp [m]; omega
    rw [hD]
    exact le_min (by omega) (by omega)
  have hN : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n by have h := r.isLt; omega), Nat.cast_one]
  have hLower : (m : ℝ) ≤ ((graph s).dist r u : ℝ) := by exact_mod_cast hDistance
  rw [dist_comm (u := u) (v := r)] at hdouble
  rw [hN] at hswap hdouble
  push_cast
  change (α : ℝ) + (2 * (m : ℝ) + 2) ≤ 2 * (n : ℝ)
  linarith

/-- Dippel–Vetta's orientation bound at twice the number of other players. -/
theorem nash_cycle_root_no_two_purchases {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * ((n - 1 : ℕ) : ℝ≥0) < α)
    {r : Fin n} (p : (graph s).Walk r r) (hp : p.IsCycle) (hgeo : CycleDistances p) :
    ¬ (p.getVert 1 ∈ (s r).val ∧ p.getVert (p.length - 1) ∈ (s r).val) := by
  rintro ⟨first, last⟩
  have h := nash_cycle_root_two_purchases_price_bound s α hne p hp hgeo first last
  have hPrice : 2 * (((n - 1 : ℕ) : ℝ)) < α := by exact_mod_cast hα
  rw [Nat.cast_sub (show 1 ≤ n by have h := r.isLt; omega), Nat.cast_one] at hPrice
  have len := hp.three_le_length
  have hAdd : (3 : ℝ) ≤ ((2 * ((p.length - 1) / 2) + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 3 ≤ 2 * ((p.length - 1) / 2) + 2 by omega)
  linarith

#print axioms nash_cycle_root_two_purchases_price_bound
#print axioms nash_cycle_root_no_two_purchases

private lemma cycle_neighbor_at_root {V : Type*} {G : SimpleGraph V} {r x : V}
    (p : G.Walk r r) (hp : p.IsCycle) (hx : s(r, x) ∈ p.edges) :
    x = p.getVert 1 ∨ x = p.getVert (p.length - 1) := by
  obtain ⟨i, hi, he⟩ := p.mk_mem_edges_iff_exists.mp hx
  rcases Sym2.eq_iff.mp he with ⟨hr, hx'⟩ | ⟨hx', hr⟩
  · have hor := (hp.getVert_endpoint_iff hi.le).mp hr
    have hi₀ : i = 0 := by omega
    exact Or.inl (by simpa [hi₀] using hx'.symm)
  · have hor := (hp.getVert_endpoint_iff (show i + 1 ≤ p.length by omega)).mp hr
    have hi₀ : i = p.length - 1 := by omega
    exact Or.inr (by simpa [hi₀] using hx'.symm)

/-- Two distinct purchases on the same isometric cycle force an
upper bound on the price which decreases with the cycle length. -/
theorem nash_isometric_cycle_two_purchases_price_bound {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s)
    {r v x y : Fin n} (p : (graph s).Walk r r) (hp : IsometricCycle p) (hxy : x ≠ y)
    (hx : x ∈ (s v).val) (hy : y ∈ (s v).val)
    (hxEdge : s(v, x) ∈ p.edges) (hyEdge : s(v, y) ∈ p.edges) :
    (α : ℝ) + (2 * ((p.length - 1) / 2) + 2 : ℕ) ≤ 2 * (n : ℝ) := by
  let hv := p.fst_mem_support_of_mem_edges hxEdge
  let q := p.rotate v hv
  have hq : q.IsCycle := hp.1.rotate hv
  have hperm : q.edges.Perm p.edges := (p.rotate_edges v hv).perm
  have hbound first last := nash_cycle_root_two_purchases_price_bound s α hne q hq
    (hp.2 q hq hperm) first last
  have hLen : q.length = p.length := by simpa only [Walk.length_edges] using hperm.length_eq
  rcases cycle_neighbor_at_root q hq (hperm.mem_iff.mpr hxEdge) with hx' | hx' <;>
    rcases cycle_neighbor_at_root q hq (hperm.mem_iff.mpr hyEdge) with hy' | hy'
  · exact (hxy (hx'.trans hy'.symm)).elim
  · simpa only [hLen] using hbound (hx' ▸ hx) (hy' ▸ hy)
  · simpa only [hLen] using hbound (hy' ▸ hy) (hx' ▸ hx)
  · exact (hxy (hx'.trans hy'.symm)).elim

private theorem nash_isometric_cycle_at_most_one_of_price_gap {n : ℕ}
    (s : Profile n) (α : ℝ≥0) (hne : IsNashEquilibrium α s)
    {r v x y : Fin n} (p : (graph s).Walk r r) (hp : IsometricCycle p)
    (price : 2 * (n : ℝ) < (α : ℝ) + (2 * ((p.length - 1) / 2) + 2 : ℕ))
    (hx : x ∈ (s v).val) (hy : y ∈ (s v).val)
    (hxEdge : s(v, x) ∈ p.edges) (hyEdge : s(v, y) ∈ p.edges) : x = y := by
  by_contra hxy
  exact (not_lt_of_ge (nash_isometric_cycle_two_purchases_price_bound s α hne p hp hxy
    hx hy hxEdge hyEdge)) price

/-- At a sufficiently high price, each player buys at most one incident edge
of any isometric cycle. -/
theorem nash_isometric_cycle_at_most_one {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * ((n - 1 : ℕ) : ℝ≥0) < α)
    {r v x y : Fin n} (p : (graph s).Walk r r) (hp : IsometricCycle p)
    (hx : x ∈ (s v).val) (hy : y ∈ (s v).val)
    (hxEdge : s(v, x) ∈ p.edges) (hyEdge : s(v, y) ∈ p.edges) : x = y := by
  apply nash_isometric_cycle_at_most_one_of_price_gap s α hne p hp _ hx hy hxEdge hyEdge
  have hPrice : 2 * (((n - 1 : ℕ) : ℝ)) < α := by exact_mod_cast hα
  rw [Nat.cast_sub (show 1 ≤ n by have h := r.isLt; omega), Nat.cast_one] at hPrice
  have len := hp.1.three_le_length
  have hAdd : (3 : ℝ) ≤ ((2 * ((p.length - 1) / 2) + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 3 ≤ 2 * ((p.length - 1) / 2) + 2 by omega)
  linarith

/-- All cycle purchases point along the traversal or all point against it. -/
def CycleDirected {n : ℕ} (s : Profile n) {r : Fin n} (p : (graph s).Walk r r) : Prop :=
    (∀ i : Fin p.length, p.getVert (finRotate p.length i).val ∈ (s (p.getVert i.val)).val) ∨
    (∀ i : Fin p.length, p.getVert i.val ∈ (s (p.getVert (finRotate p.length i).val)).val)

/-- An isometric cycle has consistent ownership when the edge price
plus the even integer strictly above the preceding odd length exceeds (2n). -/
theorem nash_isometric_cycle_directed_of_price_gap {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s)
    {r : Fin n} (p : (graph s).Walk r r) (hp : IsometricCycle p)
    (price : 2 * (n : ℝ) < (α : ℝ) + (2 * ((p.length - 1) / 2) + 2 : ℕ)) :
    CycleDirected s p := by
  let next := finRotate p.length
  let v (i : Fin p.length) := p.getVert i.val
  let forward (i : Fin p.length) : Prop := v (next i) ∈ (s (v i)).val
  let backward (i : Fin p.length) : Prop := v i ∈ (s (v (next i))).val
  have hlength := hp.1.three_le_length
  have hedge (i : Fin p.length) : s(v i, v (next i)) ∈ p.edges := by
    change s(p.getVert i.val, p.getVert (finRotate p.length i).val) ∈ p.edges
    rw [cycle_getVert_finRotate]
    exact p.mk_mem_edges_iff_exists.mpr ⟨i.val, i.isLt, rfl⟩
  have hadj (i : Fin p.length) : forward i ∨ backward i := by
    change (graph s).Adj (v i) (v (next i))
    change (graph s).Adj (p.getVert i.val) (p.getVert (finRotate p.length i).val)
    rw [cycle_getVert_finRotate]
    exact p.adj_getVert_succ i.isLt
  have hstep (i : Fin p.length) (hf : forward (next i)) : forward i := by
    apply (hadj i).resolve_right
    intro hb
    have heq := nash_isometric_cycle_at_most_one_of_price_gap s α hne p hp price
      hb hf (by rw [Sym2.eq_swap]; exact hedge i) (hedge (next i))
    exact cycle_vertex_ne hp.1 i.isLt (next (next i)).isLt
      (fun h => finRotate_twice_ne hlength i (Fin.ext h.symm)) heq
  rcases finRotate_constant forward hstep with hall | hnone
  · exact Or.inl hall
  · exact Or.inr (fun i => (hadj i).resolve_left (hnone i))

/-- The length-only form of the orientation threshold. -/
theorem nash_isometric_cycle_directed_above_order_sub_length {n : ℕ}
    (s : Profile n) (α : ℝ≥0) (hne : IsNashEquilibrium α s)
    {r : Fin n} (p : (graph s).Walk r r) (hp : IsometricCycle p)
    (price : 2 * (n : ℝ) - p.length < α) : CycleDirected s p := by
  apply nash_isometric_cycle_directed_of_price_gap s α hne p hp
  have len := hp.1.three_le_length
  have hLen : (p.length : ℝ) ≤ ((2 * ((p.length - 1) / 2) + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show p.length ≤ 2 * ((p.length - 1) / 2) + 2 by omega)
  linarith

/-- Dippel–Vetta (2024), Lemma 3. -/
theorem nash_isometric_cycle_directed {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * ((n - 1 : ℕ) : ℝ≥0) < α)
    {r : Fin n} (p : (graph s).Walk r r) (hp : IsometricCycle p) : CycleDirected s p := by
  apply nash_isometric_cycle_directed_above_order_sub_length s α hne p hp
  have hPrice : 2 * (((n - 1 : ℕ) : ℝ)) < α := by exact_mod_cast hα
  rw [Nat.cast_sub (show 1 ≤ n by have h := r.isLt; omega), Nat.cast_one] at hPrice
  have hLen : (3 : ℝ) ≤ p.length := by exact_mod_cast hp.1.three_le_length
  linarith

#print axioms nash_isometric_cycle_directed_above_order_sub_length
#print axioms nash_isometric_cycle_at_most_one
#print axioms nash_isometric_cycle_directed

/-- Every edge on an equilibrium cycle lies on a directed shortest cycle
through that edge when the price exceeds twice the number of other players. -/
theorem nash_edge_on_cycle_has_directed_cycle {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * ((n - 1 : ℕ) : ℝ≥0) < α)
    (e : Sym2 (Fin n)) (hex : ∃ (x : Fin n) (p : (graph s).Walk x x), p.IsCycle ∧ e ∈ p.edges) :
    ∃ (x : Fin n) (p : (graph s).Walk x x), p.IsCycle ∧ e ∈ p.edges ∧ CycleDirected s p ∧
      ∀ {y} (q : (graph s).Walk y y), q.IsCycle → e ∈ q.edges → p.length ≤ q.length := by
  obtain ⟨x, p, hp, he, hmin⟩ := exists_shortest_cycle_through_edge e hex
  exact ⟨x, p, hp, he, nash_isometric_cycle_directed s α hne hα p
    (shortest_cycle_through_edge_isometric p hp e he hmin), hmin⟩

#print axioms nash_edge_on_cycle_has_directed_cycle

end TreeConjecture
