import TreeConjecture.Foundations
import TreeConjecture.CycleInequalities

set_option warningAsError true

namespace TreeConjecture

open Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped BigOperators NNReal

private lemma mem_erasePurchase {n : ℕ} (s : Profile n) {i r u v : Fin n}
    (h : v ∈ (s u).val) (hkeep : u ≠ i ∨ v ≠ r) :
    v ∈ (erasePurchase s i r u).val := by
  rcases hkeep with hu | hv
  · simpa [erasePurchase, hu] using h
  · by_cases hu : u = i <;> simp [erasePurchase, hu, hv, h]

lemma adj_erasePurchase {n : ℕ} (s : Profile n) {i r u v : Fin n}
    (h : (graph s).Adj u v) (huv : u ≠ i ∨ v ≠ r) (hvu : v ≠ i ∨ u ≠ r) :
    (graph (erasePurchase s i r)).Adj u v :=
  h.elim (fun hbuy => Or.inl (mem_erasePurchase s hbuy huv))
    (fun hbuy => Or.inr (mem_erasePurchase s hbuy hvu))

open SimpleGraph in
/-- If only one edge at the starting vertex may disappear, walks avoiding
that vertex after the first step can be transported without changing length. -/
lemma transport_avoiding {V : Type*} {G H : SimpleGraph V} {i u v : V}
    (hkeep : ∀ {a b}, a ≠ i → b ≠ i → G.Adj a b → H.Adj a b)
    (p : G.Walk u v) (havoid : i ∉ p.support) :
    ∃ q : H.Walk u v, q.length = p.length := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons a b c hab p ih =>
    rw [Walk.support_cons, List.mem_cons, not_or] at havoid
    have hb : b ≠ i := fun h => havoid.2 (h ▸ p.start_mem_support)
    obtain ⟨q, hq⟩ := ih havoid.2
    exact ⟨.cons (hkeep (fun ha => havoid.1 ha.symm) hb hab) q, by simp [hq]⟩

open SimpleGraph in
/-- An alternate walk from i to r repairs any shortest path from i
after removing the edge between i and r. -/
private lemma detour_walk {V : Type*} {G H : SimpleGraph V} {i r : V}
    (hG : G.Connected) (backup : H.Walk i r) (hbackup : 0 < backup.length)
    (hkeep : ∀ {a b}, G.Adj a b → (a ≠ i ∨ b ≠ r) → (b ≠ i ∨ a ≠ r) → H.Adj a b)
    (x : V) :
    ∃ q : H.Walk i x, q.length ≤ G.dist i x + (backup.length - 1) := by
  classical
  obtain ⟨p, hp, hlen⟩ := hG.exists_path_of_dist i x
  cases p with
  | nil => exact ⟨.nil, Nat.zero_le _⟩
  | @cons _ v _ hiv p =>
    have havoid := (Walk.cons_isPath_iff hiv p).mp hp |>.2
    obtain ⟨q, hq⟩ :=
      transport_avoiding (fun ha hb hab => hkeep hab (Or.inl ha) (Or.inl hb)) p havoid
    rw [Walk.length_cons] at hlen
    by_cases hvr : v = r
    · subst v
      refine ⟨backup.append q, ?_⟩
      rw [Walk.length_append, hq]
      omega
    · refine ⟨.cons (hkeep hiv (Or.inr hvr) (Or.inl hiv.ne.symm)) q, ?_⟩
      rw [Walk.length_cons, hq, hlen]
      exact Nat.le_add_right _ _

/-- Deleting an owned triangle edge raises the buyer's connection cost by at most n - 2. -/
lemma triangle_deletion_cost {n : ℕ} (s : Profile n) (hG : (graph s).Connected)
    {i r w : Fin n} (hiw : (graph s).Adj i w) (hwr : (graph s).Adj w r) :
    (graph (erasePurchase s i r)).Connected ∧
      distanceSum (graph (erasePurchase s i r)) i - distanceSum (graph s) i ≤ (n - 2 : ℕ) := by
  let H := graph (erasePurchase s i r)
  have hiw' : H.Adj i w := adj_erasePurchase s hiw (Or.inr hwr.ne) (Or.inl hiw.ne.symm)
  have hwr' : H.Adj w r := adj_erasePurchase s hwr (Or.inl hiw.ne.symm) (Or.inr hwr.ne)
  let backup : H.Walk i r := .cons hiw' (.cons hwr' .nil)
  have hroute (x : Fin n) : ∃ q : H.Walk i x, q.length ≤ (graph s).dist i x + 1 := by
    simpa [backup] using
      detour_walk hG backup (by simp [backup]) (adj_erasePurchase s) x
  constructor
  · apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
    exact ⟨i, fun x => ⟨(hroute x).choose⟩⟩
  · classical
    let charged := ((Finset.univ : Finset (Fin n)).erase i).erase w
    have hcard : charged.card = n - 2 := by
      dsimp [charged]
      rw [Finset.card_erase_of_mem (by simp [hiw.ne.symm]),
        Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp [Nat.sub_sub]
    have hwG := SimpleGraph.dist_eq_one_iff_adj.mpr hiw
    have hwH := SimpleGraph.dist_eq_one_iff_adj.mpr hiw'
    change distanceSum H i - distanceSum (graph s) i ≤ _
    simp only [distanceSum, ← Finset.sum_sub_distrib]
    calc
      _ = ∑ x ∈ charged, ((H.dist i x : ℝ) - ((graph s).dist i x : ℝ)) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ charged)
        intro x _ hx
        have h : x = w ∨ x = i := by
          by_cases hxw : x = w
          · exact Or.inl hxw
          · exact Or.inr (by simpa [charged, hxw] using hx)
        rcases h with rfl | rfl
        · simp [hwG, hwH]
        · simp
      _ ≤ ∑ _x ∈ charged, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        obtain ⟨q, hq⟩ := hroute x
        have hdist := (SimpleGraph.dist_le q).trans hq
        apply sub_le_iff_le_add.mpr
        exact_mod_cast (show H.dist i x ≤ 1 + (graph s).dist i x by omega)
      _ = _ := by simp [hcard]

/-- At prices above n - 2, an equilibrium graph has no triangle. -/
theorem nash_no_triangle {n : ℕ} (α : ℝ≥0) (s : Profile n)
    (hα : ((n - 2 : ℕ) : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    {i r w : Fin n} (hir : (graph s).Adj i r) (hrw : (graph s).Adj r w)
    (hwi : (graph s).Adj w i) : False := by
  have hG := nash_connected (Nat.zero_lt_of_lt i.isLt) α s hne
  have hprice : ((n - 2 : ℕ) : ℝ) < (α : ℝ) := by exact_mod_cast hα
  rcases hir with hir | hri
  · obtain ⟨hconn, hcost⟩ := triangle_deletion_cost s hG hwi.symm hrw.symm
    exact (not_le_of_gt hprice) ((nash_deletion_bound α s hne hir hconn).trans hcost)
  · obtain ⟨hconn, hcost⟩ := triangle_deletion_cost s hG hrw hwi
    exact (not_le_of_gt hprice) ((nash_deletion_bound α s hne hri hconn).trans hcost)

#print axioms nash_no_triangle

open SimpleGraph in
private lemma slope_of_distance_increase {V : Type*} {G H : SimpleGraph V} {i r x : V}
    (hG : G.Connected)
    (hkeep : ∀ {a b}, G.Adj a b → (a ≠ i ∨ b ≠ r) → (b ≠ i ∨ a ≠ r) → H.Adj a b)
    (hinc : G.dist i x < H.dist i x) :
    G.dist i x = G.dist r x + 1 := by
  classical
  obtain ⟨p, hp, hlen⟩ := hG.exists_path_of_dist i x
  cases p with
  | nil => simp at hinc
  | @cons _ v _ hiv p =>
    by_cases hvr : v = r
    · subst v
      have hlower := SimpleGraph.dist_le p
      have hupper : G.dist i x ≤ G.dist i r + G.dist r x := hG.dist_triangle
      rw [dist_eq_one_iff_adj.mpr hiv] at hupper
      rw [Walk.length_cons] at hlen
      omega
    · have havoid := (Walk.cons_isPath_iff hiv p).mp hp |>.2
      obtain ⟨q, hq⟩ :=
        transport_avoiding (fun ha hb hab => hkeep hab (Or.inl ha) (Or.inl hb)) p havoid
      have hH := SimpleGraph.dist_le (.cons (hkeep hiv (Or.inr hvr) (Or.inl hiv.ne.symm)) q)
      rw [Walk.length_cons, hq, ← Walk.length_cons hiv, hlen] at hH
      omega

open SimpleGraph in
private lemma alternate_neighbor_bound {V : Type*} {G H : SimpleGraph V} {i w x : V}
    (hG : G.Connected) (hiw : H.Adj i w)
    (hkeep : ∀ {a b}, a ≠ i → b ≠ i → G.Adj a b → H.Adj a b)
    (hw : G.dist w x < G.dist i x) :
    H.dist i x ≤ G.dist i x := by
  classical
  obtain ⟨p, _, hlen⟩ := hG.exists_path_of_dist w x
  have havoid : i ∉ p.support := by
    intro hi
    have hle := (SimpleGraph.dist_le (p.dropUntil i hi)).trans (p.length_dropUntil_le_length hi)
    omega
  obtain ⟨q, hq⟩ := transport_avoiding hkeep p havoid
  have hle := SimpleGraph.dist_le (.cons hiw q)
  rw [Walk.length_cons, hq, hlen] at hle
  omega

private lemma graph_erasePurchase_le {n : ℕ} (s : Profile n) (i r : Fin n) :
    graph (erasePurchase s i r) ≤ graph s := by
  have h (u v : Fin n) (hv : v ∈ (erasePurchase s i r u).val) : v ∈ (s u).val := by
    by_cases hu : u = i
    · have hmem : v ∈ (s u).val ∧ v ≠ r := by simpa [erasePurchase, hu] using hv
      exact hmem.1
    · simpa [erasePurchase, hu] using hv
  intro u v huv
  exact huv.imp (h u v) (h v u)


private structure DetourDeletion {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (i r : Fin n) (budget : ℕ) where
  penalty : Fin n → ℕ
  price_le : (α : ℝ) ≤ ((∑ x, penalty x : ℕ) : ℝ)
  penalty_le : ∀ x, penalty x ≤ budget
  slope : ∀ x, 0 < penalty x → (graph s).dist i x = (graph s).dist r x + 1
  alternate : ∀ {w}, (graph s).Adj i w → w ≠ r → ∀ x, 0 < penalty x →
    (graph s).dist i x ≤ (graph s).dist w x
  at_owner : penalty i = 0

open SimpleGraph in
private noncomputable def detourDeletion {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hG : (graph s).Connected) {i r : Fin n}
    (hbuy : r ∈ (s i).val) (budget : ℕ)
    (backup : (graph (erasePurchase s i r)).Walk i r) (hpos : 0 < backup.length)
    (hbudget : backup.length - 1 ≤ budget) : DetourDeletion s α i r budget := by
  let G := graph s
  let H := graph (erasePurchase s i r)
  have hroute (x : Fin n) : ∃ q : H.Walk i x, q.length ≤ G.dist i x + budget := by
    obtain ⟨q, hq⟩ := detour_walk hG backup hpos (adj_erasePurchase s) x
    exact ⟨q, hq.trans (Nat.add_le_add_left hbudget _)⟩
  have hH : H.Connected := (connected_iff_exists_forall_reachable _).mpr
    ⟨i, fun x => ⟨(hroute x).choose⟩⟩
  have hmono (x : Fin n) : G.dist i x ≤ H.dist i x :=
    (hH i x).dist_anti (graph_erasePurchase_le s i r)
  let penalty (x : Fin n) := H.dist i x - G.dist i x
  have hsum : ((∑ x, penalty x : ℕ) : ℝ) = distanceSum H i - distanceSum G i := by
    simp only [distanceSum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact Nat.cast_sub (hmono x)
  have hprice : (α : ℝ) ≤ ((∑ x, penalty x : ℕ) : ℝ) := by
    rw [hsum]
    exact nash_deletion_bound α s hne hbuy hH
  have hupper (x : Fin n) : penalty x ≤ budget := by
    obtain ⟨q, hq⟩ := hroute x
    have hle := (SimpleGraph.dist_le q).trans hq
    dsimp [penalty]
    omega
  have hinc (x : Fin n) (hx : 0 < penalty x) : G.dist i x < H.dist i x :=
    Nat.sub_pos_iff_lt.mp hx
  refine ⟨penalty, hprice, hupper, ?_, ?_, by simp [penalty]⟩
  · exact fun x hx => slope_of_distance_increase hG (adj_erasePurchase s) (hinc x hx)
  · intro w hiw hwr x hx
    have hiw' : H.Adj i w := adj_erasePurchase s hiw (Or.inr hwr) (Or.inl hiw.ne.symm)
    by_contra! hlt
    have hw : H.dist i x ≤ G.dist i x := alternate_neighbor_bound hG hiw'
      (fun ha hb hab => adj_erasePurchase s hab (Or.inl ha) (Or.inl hb)) hlt
    exact (not_le_of_gt (hinc x hx)) hw

private structure OrientedSquareDeletion {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (i r w z : Fin n) where
  penalty : Fin n → ℕ
  price_le : (α : ℝ) ≤ ((∑ x, penalty x : ℕ) : ℝ)
  penalty_le : ∀ x, penalty x ≤ 2
  slope : ∀ x, 0 < penalty x →
    (graph s).dist i x = (graph s).dist r x + 1 ∧ (graph s).dist i x ≤ (graph s).dist w x
  at_owner : penalty i = 0
  at_other_neighbor : penalty w = 0
  at_opposite : penalty z = 0

open SimpleGraph in
private noncomputable def orientedSquareDeletion {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hG : (graph s).Connected) {i r w z : Fin n}
    (hbuy : r ∈ (s i).val) (hiw : (graph s).Adj i w) (hwz : (graph s).Adj w z)
    (hzr : (graph s).Adj z r) (hiz : i ≠ z) (hwr : w ≠ r)
    (hniz : ¬ (graph s).Adj i z) :
    OrientedSquareDeletion s α i r w z := by
  let G := graph s
  let H := graph (erasePurchase s i r)
  have hiw' : H.Adj i w := adj_erasePurchase s hiw (Or.inr hwr) (Or.inl hiw.ne.symm)
  have hwz' : H.Adj w z := adj_erasePurchase s hwz (Or.inl hiw.ne.symm) (Or.inl hiz.symm)
  have hzr' : H.Adj z r := adj_erasePurchase s hzr (Or.inl hiz.symm) (Or.inr hzr.ne)
  let backup : H.Walk i r := .cons hiw' (.cons hwz' (.cons hzr' .nil))

  let D := detourDeletion s α hne hG hbuy 2 backup (by simp [backup]) (by simp [backup])
  have hslope (x : Fin n) (hx : 0 < D.penalty x) :
      G.dist i x = G.dist r x + 1 ∧ G.dist i x ≤ G.dist w x :=
    ⟨D.slope x hx, D.alternate hiw hwr x hx⟩
  refine ⟨D.penalty, D.price_le, D.penalty_le, hslope, D.at_owner, ?_, ?_⟩
  · by_contra! h
    have hp := (hslope w (Nat.pos_of_ne_zero h)).2
    rw [show G.dist i w = 1 from dist_eq_one_iff_adj.mpr hiw, SimpleGraph.dist_self] at hp
    omega
  · by_contra! h
    have hp := (hslope z (Nat.pos_of_ne_zero h)).2
    have hdist : 1 < G.dist i z := hG.one_lt_dist_of_ne_of_not_adj hiz hniz
    rw [show G.dist w z = 1 from dist_eq_one_iff_adj.mpr hwz] at hp
    omega

private structure SquareDeletion {n : ℕ} (s : Profile n) (α : ℝ≥0) (a b c d : Fin n) where
  penalty : Fin n → ℕ
  price_le : (α : ℝ) ≤ ((∑ x, penalty x : ℕ) : ℝ)
  penalty_le : ∀ x, penalty x ≤ 2
  slope : ∀ x, 0 < penalty x →
    ((graph s).dist a x = (graph s).dist b x + 1 ∧ (graph s).dist a x ≤ (graph s).dist d x) ∨
    ((graph s).dist b x = (graph s).dist a x + 1 ∧ (graph s).dist b x ≤ (graph s).dist c x)
  on_square : penalty a + penalty b + penalty c + penalty d ≤ 2

private noncomputable def squareDeletion {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hG : (graph s).Connected) {a b c d : Fin n}
    (hab : (graph s).Adj a b) (hbc : (graph s).Adj b c) (hcd : (graph s).Adj c d)
    (hda : (graph s).Adj d a) (hac : a ≠ c) (hbd : b ≠ d)
    (hnac : ¬ (graph s).Adj a c) (hnbd : ¬ (graph s).Adj b d) :
    SquareDeletion s α a b c d := by
  classical
  by_cases ha : b ∈ (s a).val
  · let E := orientedSquareDeletion s α hne hG ha hda.symm hcd.symm hbc.symm hac hbd.symm hnac
    refine ⟨E.penalty, E.price_le, E.penalty_le, fun x hx => Or.inl (E.slope x hx), ?_⟩
    simpa [E.at_owner, E.at_opposite, E.at_other_neighbor] using E.penalty_le b
  · have hb : a ∈ (s b).val := hab.resolve_left ha
    let E := orientedSquareDeletion s α hne hG hb hbc hcd hda hbd hac.symm hnbd
    refine ⟨E.penalty, E.price_le, E.penalty_le, fun x hx => Or.inr (E.slope x hx), ?_⟩
    simpa [E.at_owner, E.at_opposite, E.at_other_neighbor] using E.penalty_le a

open SimpleGraph in
private lemma adjacent_levels {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    {u v : V} (h : G.Adj u v) (x : V) :
    G.dist u x ≤ G.dist v x + 1 ∧ G.dist v x ≤ G.dist u x + 1 := by
  have h₁ : G.dist u x ≤ G.dist u v + G.dist v x := hG.dist_triangle
  have h₂ : G.dist v x ≤ G.dist v u + G.dist u x := hG.dist_triangle
  rw [dist_eq_one_iff_adj.mpr h] at h₁
  rw [dist_eq_one_iff_adj.mpr h.symm] at h₂
  omega

/-- At prices above n - 2, an equilibrium graph has no four-cycle. -/
theorem nash_no_square {n : ℕ} (α : ℝ≥0) (s : Profile n)
    (hα : ((n - 2 : ℕ) : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    {a b c d : Fin n} (hab : (graph s).Adj a b) (hbc : (graph s).Adj b c)
    (hcd : (graph s).Adj c d) (hda : (graph s).Adj d a) (hac : a ≠ c) (hbd : b ≠ d) :
    False := by
  classical
  have hG := nash_connected (Nat.zero_lt_of_lt a.isLt) α s hne
  have hnac : ¬ (graph s).Adj a c :=
    fun h => nash_no_triangle α s hα hne hab hbc h.symm
  have hnbd : ¬ (graph s).Adj b d :=
    fun h => nash_no_triangle α s hα hne hbc hcd h.symm
  let E₀ := squareDeletion s α hne hG hab hbc hcd hda hac hbd hnac hnbd
  let E₁ := squareDeletion s α hne hG hbc hcd hda hab hbd hac.symm hnbd (fun h => hnac h.symm)
  let E₂ := squareDeletion s α hne hG hcd hda hab hbc hac.symm hbd.symm
    (fun h => hnac h.symm) (fun h => hnbd h.symm)
  let E₃ := squareDeletion s α hne hG hda hab hbc hcd hbd.symm hac (fun h => hnbd h.symm) hnac
  let P (x : Fin n) := E₀.penalty x + E₁.penalty x + E₂.penalty x + E₃.penalty x
  have hwall (x : Fin n) : P x ≤ 4 :=
    square_penalty_sum (E₀.penalty_le x) (E₁.penalty_le x) (E₂.penalty_le x) (E₃.penalty_le x)
      (adjacent_levels hG hab x) (adjacent_levels hG hbc x)
      (adjacent_levels hG hcd x) (adjacent_levels hG hda x)
      (E₀.slope x) (E₁.slope x) (E₂.slope x) (E₃.slope x)
  let C : Finset (Fin n) := {a, b, c, d}
  have hC : C.card = 4 := by
    simp [C, hab.ne, hbc.ne, hcd.ne, hda.ne.symm, hac, hbd]
  have hn : 4 ≤ n := by simpa [hC] using Finset.card_le_univ C
  have hinside : ∑ x ∈ C, P x ≤ 8 := by
    simp [C, P, hab.ne, hbc.ne, hcd.ne, hda.ne.symm, hac, hbd]
    have h₀ := E₀.on_square
    have h₁ := E₁.on_square
    have h₂ := E₂.on_square
    have h₃ := E₃.on_square
    omega
  have houtside : ∑ x ∈ Finset.univ \ C, P x ≤ 4 * (n - 4) := by
    calc
      _ ≤ ∑ _x ∈ Finset.univ \ C, (4 : ℕ) := Finset.sum_le_sum (fun x _ => hwall x)
      _ = _ := by
        simp [Finset.card_sdiff_of_subset (Finset.subset_univ C), hC, Nat.mul_comm]
  have htotal : ∑ x, P x ≤ 4 * (n - 2) := by
    have hsplit := Finset.sum_sdiff (Finset.subset_univ C) (f := P)
    omega
  have hprice₀ := E₀.price_le
  have hprice₁ := E₁.price_le
  have hprice₂ := E₂.price_le
  have hprice₃ := E₃.price_le
  have hcast : ((∑ x, P x : ℕ) : ℝ) ≤ 4 * ((n - 2 : ℕ) : ℝ) := by
    exact_mod_cast htotal
  have hprice : ((n - 2 : ℕ) : ℝ) < (α : ℝ) := by exact_mod_cast hα
  simp only [P, Finset.sum_add_distrib, Nat.cast_add] at hcast
  linarith

#print axioms nash_no_square

/-- Every cycle in an equilibrium at price above n - 2 has length at least five. -/
theorem nash_cycle_length_ge_five {n : ℕ} (α : ℝ≥0) (s : Profile n)
    (hα : ((n - 2 : ℕ) : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    {v : Fin n} (p : (graph s).Walk v v) (hp : p.IsCycle) : 5 ≤ p.length := by
  by_contra! hshort
  have hmin := hp.three_le_length
  have h₀ := p.adj_getVert_succ (i := 0) (by omega)
  have h₁ := p.adj_getVert_succ (i := 1) (by omega)
  rcases (show p.length = 3 ∨ p.length = 4 by omega) with hlen | hlen
  · have h₂ : (graph s).Adj (p.getVert 2) (p.getVert 0) := by
      have h := p.adj_getVert_succ (i := 2) (by omega)
      change (graph s).Adj (p.getVert 2) (p.getVert 3) at h
      simpa only [← hlen, SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero]
        using h
    exact nash_no_triangle α s hα hne h₀ h₁ h₂
  · have h₂ := p.adj_getVert_succ (i := 2) (by omega)
    have h₃ : (graph s).Adj (p.getVert 3) (p.getVert 0) := by
      have h := p.adj_getVert_succ (i := 3) (by omega)
      change (graph s).Adj (p.getVert 3) (p.getVert 4) at h
      simpa only [← hlen, SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero]
        using h
    have distinct {i j : ℕ} (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
        p.getVert i ≠ p.getVert j := fun h =>
      hij (hp.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) h)
    exact nash_no_square α s hα hne h₀ h₁ h₂ h₃
      (distinct (by decide) (by decide) (by decide)) (distinct (by decide) (by decide) (by decide))

/-- The Tree Conjecture holds for at most four players, even at price above n - 2. -/
theorem nash_tree_of_le_four {n : ℕ} (hn : 0 < n) (hfour : n ≤ 4) (α : ℝ≥0) (s : Profile n)
    (hα : ((n - 2 : ℕ) : ℝ≥0) < α) (hne : IsNashEquilibrium α s) : (graph s).IsTree := by
  refine ⟨nash_connected hn α s hne, ?_⟩
  intro v p hp
  have hmin := nash_cycle_length_ge_five α s hα hne p hp
  have hmax := hp.nodup_dropLast_support.length_le_card
  simp [SimpleGraph.Walk.length_support] at hmax
  omega

#print axioms nash_cycle_length_ge_five
#print axioms nash_tree_of_le_four

/-- The two-purchase case of the girth estimate. If a player buys two edges
and both have detours costing at most the budget per vertex, at most one deletion
can increase the distance to any given destination. -/
theorem two_purchase_detour_bound {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {i r w : Fin n} (hwr : w ≠ r)
    (hr : r ∈ (s i).val) (hw : w ∈ (s i).val) (budget : ℕ)
    (detour₁ : (graph (erasePurchase s i r)).Walk i r)
    (detour₂ : (graph (erasePurchase s i w)).Walk i w)
    (hpos₁ : 0 < detour₁.length) (hpos₂ : 0 < detour₂.length)
    (hl₁ : detour₁.length - 1 ≤ budget) (hl₂ : detour₂.length - 1 ≤ budget) :
    2 * (α : ℝ) ≤ (n : ℝ) * (budget : ℝ) := by
  have hG := nash_connected (Nat.zero_lt_of_lt i.isLt) α s hne
  let A := detourDeletion s α hne hG hr budget detour₁ hpos₁ hl₁
  let B := detourDeletion s α hne hG hw budget detour₂ hpos₂ hl₂
  have hpoint (x : Fin n) : A.penalty x + B.penalty x ≤ budget := by
    by_cases ha : 0 < A.penalty x
    · have hb : B.penalty x = 0 := by
        by_contra! hb
        have hs := B.slope x (Nat.pos_of_ne_zero hb)
        have hl := A.alternate (Or.inl hw) hwr x ha
        omega
      simpa [hb] using A.penalty_le x
    · simpa [Nat.eq_zero_of_not_pos ha] using B.penalty_le x
  have htotal : ∑ x, (A.penalty x + B.penalty x) ≤ n * budget := by
    calc
      _ ≤ ∑ _ : Fin n, budget := Finset.sum_le_sum (fun x _ => hpoint x)
      _ = n * budget := by simp
  have htotalR : ((∑ x, (A.penalty x + B.penalty x) : ℕ) : ℝ) ≤ (n : ℝ) * (budget : ℝ) := by
    exact_mod_cast htotal
  rw [Finset.sum_add_distrib, Nat.cast_add] at htotalR
  linarith [A.price_le, B.price_le]

#print axioms two_purchase_detour_bound

/-- The directed-cycle case of the girth estimate. Each vertex buys its
successor edge, and for each deletion the remaining graph supplies a detour.
For a directed k-cycle its other arc supplies a detour of length k - 1. -/
theorem directed_cycle_detour_bound {n m : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hm : 0 < m) (vertex : Fin m → Fin n)
    (next : Equiv.Perm (Fin m)) (budget : ℕ)
    (hbuy : ∀ j, vertex (next j) ∈ (s (vertex j)).val)
    (backup : ∀ j, (graph (erasePurchase s (vertex j) (vertex (next j)))).Walk
      (vertex j) (vertex (next j)))
    (hpos : ∀ j, 0 < (backup j).length) (hbudget : ∀ j, (backup j).length - 1 ≤ budget) :
    2 * (α : ℝ) ≤ (n : ℝ) * (budget : ℝ) := by
  have hG := nash_connected (Nat.zero_lt_of_lt (vertex ⟨0, hm⟩).isLt) α s hne
  let E (j : Fin m) := detourDeletion s α hne hG (hbuy j) budget (backup j) (hpos j) (hbudget j)
  let level (x : Fin n) (j : Fin m) := ((graph s).dist (vertex j) x : ℝ)
  have hbound (x : Fin n) (j : Fin m) :
      2 * ((E j).penalty x : ℝ) ≤ (budget : ℝ) * (1 + level x j - level x (next j)) := by
    by_cases hx : 0 < (E j).penalty x
    · have hs : level x j = level x (next j) + 1 := by
        dsimp [level]
        exact_mod_cast (E j).slope x hx
      have hb : ((E j).penalty x : ℝ) ≤ (budget : ℝ) := by
        exact_mod_cast (E j).penalty_le x
      rw [hs]
      nlinarith
    · have hw : level x (next j) ≤ level x j + 1 := by
        dsimp [level]
        exact_mod_cast (adjacent_levels hG (Or.inl (hbuy j)) x).2
      have hnonneg := mul_nonneg (Nat.cast_nonneg (α := ℝ) budget)
        (show 0 ≤ 1 + level x j - level x (next j) by linarith)
      simpa [Nat.eq_zero_of_not_pos hx] using hnonneg
  have hpoint (x : Fin n) :
      ∑ j, 2 * ((E j).penalty x : ℝ) ≤ (m : ℝ) * (budget : ℝ) := by
    have hperm : (∑ j, (budget : ℝ) * level x (next j)) = ∑ j, (budget : ℝ) * level x j :=
      Equiv.sum_comp next (fun j => (budget : ℝ) * level x j)
    calc
      _ ≤ ∑ j, (budget : ℝ) * (1 + level x j - level x (next j)) :=
        Finset.sum_le_sum (fun j _ => hbound x j)
      _ = _ := by
        simp only [mul_sub, mul_add, mul_one, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          hperm, add_sub_cancel_right, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  have hprice (j : Fin m) : 2 * (α : ℝ) ≤ ∑ x, 2 * ((E j).penalty x : ℝ) := by
    have h := (E j).price_le
    simp only [Nat.cast_sum] at h
    rw [← Finset.mul_sum]
    linarith
  have hcard : 0 < (m : ℝ) := by exact_mod_cast hm
  apply (mul_le_mul_iff_right₀ hcard).mp
  calc
    (m : ℝ) * (2 * (α : ℝ)) = ∑ _j : Fin m, 2 * (α : ℝ) := by simp
    _ ≤ ∑ j, ∑ x, 2 * ((E j).penalty x : ℝ) := Finset.sum_le_sum (fun j _ => hprice j)
    _ = ∑ x, ∑ j, 2 * ((E j).penalty x : ℝ) := Finset.sum_comm
    _ ≤ ∑ _x : Fin n, (m : ℝ) * (budget : ℝ) := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = (m : ℝ) * ((n : ℝ) * (budget : ℝ)) := by simp [mul_left_comm]

#print axioms directed_cycle_detour_bound

/-- A walk that avoids the edge of a purchase survives its deletion with the same length. -/
theorem walk_erasePurchase {n : ℕ} (s : Profile n) {i r u v : Fin n}
    (p : (graph s).Walk u v) (havoid : s(i, r) ∉ p.edges) :
    ∃ q : (graph (erasePurchase s i r)).Walk u v, q.length = p.length := by
  have hkeep (e : Sym2 (Fin n)) (he : e ∈ p.edges) :
      e ∈ (graph (erasePurchase s i r)).edgeSet := by
    have hadj := p.edges_subset_edgeSet he
    induction e using Sym2.inductionOn with
    | hf a b =>
      apply (SimpleGraph.mem_edgeSet (graph (erasePurchase s i r))).mpr
      apply adj_erasePurchase s ((SimpleGraph.mem_edgeSet (graph s)).mp hadj)
      · by_cases ha : a = i
        · refine Or.inr (fun hb => havoid ?_)
          rwa [ha, hb] at he
        · exact Or.inl ha
      · by_cases hb : b = i
        · refine Or.inr (fun ha => havoid ?_)
          rw [ha, hb, Sym2.eq_swap] at he
          exact he
        · exact Or.inl hb
  exact ⟨p.transfer _ hkeep, by simp⟩

end TreeConjecture
