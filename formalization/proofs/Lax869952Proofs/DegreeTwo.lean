import Lax869952Proofs.ShortCycles
import Lax869952Proofs.DirectedGeodesics
import Lax869952Proofs.BranchDetours

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ}

/-- Reachability by a walk that avoids the specified vertex, including its endpoints. -/
def reachableAvoiding (G : SimpleGraph (Fin n)) (v u x : Fin n) : Prop :=
  ∃ p : G.Walk u x, v ∉ p.support

/-- The vertices separated from the buyer by removing the intermediate vertex. -/
noncomputable def separatedVertices (G : SimpleGraph (Fin n)) (u v : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun x => ¬ reachableAvoiding G v u x)

@[simp]
lemma mem_separatedVertices {G : SimpleGraph (Fin n)} {u v x : Fin n} :
    x ∈ separatedVertices G u v ↔ ¬ reachableAvoiding G v u x := by
  classical
  simp [separatedVertices]

/-- The vertices with a shortest route via a specified two-step prefix. -/
noncomputable def verticesViaTwoSteps (G : SimpleGraph (Fin n)) (u w : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun x => G.dist u x = 2 + G.dist w x)

@[simp]
lemma mem_verticesViaTwoSteps {G : SimpleGraph (Fin n)} {u w x : Fin n} :
    x ∈ verticesViaTwoSteps G u w ↔ G.dist u x = 2 + G.dist w x := by
  classical
  simp [verticesViaTwoSteps]

/-- A shortest route whose first edge is removed has one of two repairs.
It can enter the part separated by the intermediate vertex through that
vertex, or use the second vertex of the two-step prefix. The two new
prefixes can have different lengths. -/
private lemma two_neighbor_routes {G H : SimpleGraph (Fin n)} (hG : G.Connected)
    {u v w : Fin n} (huv : G.Adj u v) (hvw : G.Adj v w)
    (hdegree : ∀ x, G.Adj v x → reachableAvoiding G v u x → x = u ∨ x = w)
    (hkeep : ∀ {a b}, G.Adj a b → (a ≠ u ∨ b ≠ v) → (b ≠ u ∨ a ≠ v) → H.Adj a b)
    (viaV : H.Walk u v) (viaW : H.Walk u w) (x : Fin n) :
    ∃ q : H.Walk u x,
      q.length + (if x ∈ verticesViaTwoSteps G u w then 2
        else if x ∈ separatedVertices G u v then 1 else 0) ≤
      G.dist u x + (if x ∈ verticesViaTwoSteps G u w then viaW.length
        else if x ∈ separatedVertices G u v then viaV.length else 0) := by
  classical
  have keepAway {a b} (ha : a ≠ u) (hb : b ≠ u) (hab : G.Adj a b) : H.Adj a b :=
    hkeep hab (Or.inl ha) (Or.inl hb)
  by_cases hB : x ∈ verticesViaTwoSteps G u w
  · have hdist := mem_verticesViaTwoSteps.mp hB
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist w x
    have havoid : u ∉ p.support := by
      intro hu
      have hh := walk_length_ge_via p hu
      omega
    obtain ⟨q, hq⟩ := transport_avoiding keepAway p havoid
    exact ⟨viaW.append q, by simp only [hB, if_true, Walk.length_append, hq, hp]; omega⟩
  by_cases hA : x ∈ separatedVertices G u v
  · have hsep := mem_separatedVertices.mp hA
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u x
    have hvisit : v ∈ p.support := by
      by_contra h
      exact hsep ⟨p, h⟩
    have hbound := walk_length_ge_via p hvisit
    have hdist : G.dist u x = 1 + G.dist v x := by
      have htri : G.dist u x ≤ G.dist u v + G.dist v x := hG.dist_triangle
      rw [dist_eq_one_iff_adj.mpr huv] at hbound htri
      omega
    obtain ⟨r, hr⟩ := hG.exists_walk_length_eq_dist v x
    have havoid : u ∉ r.support := by
      intro hu
      have hh := walk_length_ge_via r hu
      omega
    obtain ⟨q, hq⟩ := transport_avoiding keepAway r havoid
    exact ⟨viaV.append q, by simp only [hA, hB, if_true, if_false, Walk.length_append, hq, hr]; omega⟩
  have hex : reachableAvoiding G v u x := by
    by_contra h
    exact hA (mem_separatedVertices.mpr h)
  obtain ⟨p, hp, hpLen⟩ := hG.exists_path_of_dist u x
  cases p with
  | nil => exact ⟨.nil, by simp [hA, hB]⟩
  | @cons _ a _ hua tail =>
    have hpath := Walk.cons_isPath_iff hua tail |>.mp hp
    have hav : a ≠ v := by
      intro hav
      subst a
      cases tail with
      | nil =>
        obtain ⟨r, hr⟩ := hex
        exact hr r.end_mem_support
      | @cons _ z _ hvz rest =>
        have hvfree := (Walk.cons_isPath_iff hvz rest).mp hpath.1 |>.2
        have hzu : z ≠ u := fun he =>
          hpath.2 (List.mem_cons_of_mem _ (he ▸ rest.start_mem_support))
        obtain ⟨r, hr⟩ := hex
        have hreach : reachableAvoiding G v u z :=
          ⟨r.append rest.reverse, by simp [Walk.mem_support_append_iff, Walk.support_reverse, hr, hvfree]⟩
        have hzw := (hdegree z hvz hreach).resolve_left hzu
        subst z
        have hlen : rest.length + 1 + 1 = G.dist u x := by simpa using hpLen
        have htri : G.dist u x ≤ G.dist u w + G.dist w x := hG.dist_triangle
        have huw : G.dist u w ≤ 2 := dist_le (.cons huv (.cons hvw .nil))
        have hwx := dist_le rest
        exact hB (mem_verticesViaTwoSteps.mpr (by omega))
    obtain ⟨q, hq⟩ := transport_avoiding keepAway tail hpath.2
    have ha : H.Adj u a := hkeep hua (Or.inr hav) (Or.inl hua.ne.symm)
    exact ⟨.cons ha q, by simp [hA, hB, hq, ← hpLen]⟩

private lemma indicator_sum (S : Finset (Fin n)) (c : ℝ) :
    (∑ x : Fin n, if x ∈ S then c else 0) = (S.card : ℝ) * c := by
  classical
  rw [← Finset.sum_filter]
  simp

private lemma two_neighbor_distance_bound {G H : SimpleGraph (Fin n)} (hG : G.Connected)
    {u v w : Fin n} (huv : G.Adj u v) (hvw : G.Adj v w)
    (hdegree : ∀ x, G.Adj v x → reachableAvoiding G v u x → x = u ∨ x = w)
    (hkeep : ∀ {a b}, G.Adj a b → (a ≠ u ∨ b ≠ v) → (b ≠ u ∨ a ≠ v) → H.Adj a b)
    (viaV : H.Walk u v) (viaW : H.Walk u w) :
    H.Connected ∧ ∀ x : Fin n, ((H.dist u x : ℝ) - (G.dist u x : ℝ)) ≤
      (if x ∈ separatedVertices G u v then (viaV.length : ℝ) - 1 else 0) +
      (if x ∈ verticesViaTwoSteps G u w then (viaW.length : ℝ) - 2 else 0) := by
  classical
  have routes := two_neighbor_routes hG huv hvw hdegree hkeep viaV viaW
  refine ⟨(connected_iff_exists_forall_reachable H).mpr ⟨u, fun x => ⟨(routes x).choose⟩⟩, ?_⟩
  let A := separatedVertices G u v
  let B := verticesViaTwoSteps G u w
  have hVNat : 1 ≤ viaV.length :=
    Nat.succ_le_of_lt (Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne huv.ne))
  have hV : 1 ≤ (viaV.length : ℝ) := by exact_mod_cast hVNat
  intro x
  change ((H.dist u x : ℝ) - (G.dist u x : ℝ)) ≤
    (if x ∈ A then (viaV.length : ℝ) - 1 else 0) +
    (if x ∈ B then (viaW.length : ℝ) - 2 else 0)
  exact by
    obtain ⟨p, hp⟩ := routes x
    have hd := dist_le p
    change p.length + (if x ∈ B then 2 else if x ∈ A then 1 else 0) ≤
      G.dist u x + (if x ∈ B then viaW.length else if x ∈ A then viaV.length else 0) at hp
    by_cases hb : x ∈ B
    · have hn : H.dist u x + 2 ≤ G.dist u x + viaW.length := by
        simp only [hb, if_true] at hp
        omega
      have hr : (H.dist u x : ℝ) + 2 ≤ (G.dist u x : ℝ) + viaW.length := by exact_mod_cast hn
      have ha : 0 ≤ (if x ∈ A then (viaV.length : ℝ) - 1 else 0) := by
        split <;> linarith
      rw [if_pos hb]
      linarith
    · by_cases ha : x ∈ A
      · have hn : H.dist u x + 1 ≤ G.dist u x + viaV.length := by
          simp only [hb, ha, if_false, if_true] at hp
          omega
        have hr : (H.dist u x : ℝ) + 1 ≤ (G.dist u x : ℝ) + viaV.length := by exact_mod_cast hn
        rw [if_neg hb, if_pos ha]
        linarith
      · have hn : H.dist u x ≤ G.dist u x := by
          simp only [hb, ha, if_false, Nat.add_zero] at hp
          exact hd.trans hp
        have hr : (H.dist u x : ℝ) ≤ (G.dist u x : ℝ) := by exact_mod_cast hn
        rw [if_neg hb, if_neg ha]
        linarith
private lemma two_neighbor_distanceSum_bound {G H : SimpleGraph (Fin n)} (hG : G.Connected)
    {u v w : Fin n} (huv : G.Adj u v) (hvw : G.Adj v w)
    (hdegree : ∀ x, G.Adj v x → reachableAvoiding G v u x → x = u ∨ x = w)
    (hkeep : ∀ {a b}, G.Adj a b → (a ≠ u ∨ b ≠ v) → (b ≠ u ∨ a ≠ v) → H.Adj a b)
    (viaV : H.Walk u v) (viaW : H.Walk u w) :
    H.Connected ∧ distanceSum H u - distanceSum G u ≤
      ((separatedVertices G u v).card : ℝ) * ((viaV.length : ℝ) - 1) +
      ((verticesViaTwoSteps G u w).card : ℝ) * ((viaW.length : ℝ) - 2) := by
  obtain ⟨hconn, hpoint⟩ := two_neighbor_distance_bound hG huv hvw hdegree hkeep viaV viaW
  refine ⟨hconn, ?_⟩
  let A := separatedVertices G u v
  let B := verticesViaTwoSteps G u w
  unfold distanceSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x : Fin n, ((if x ∈ A then (viaV.length : ℝ) - 1 else 0) +
        (if x ∈ B then (viaW.length : ℝ) - 2 else 0)) :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := by rw [Finset.sum_add_distrib, indicator_sum, indicator_sum]

/-- A swap across a degree-two vertex trades one extra step to its attached
part for a one-step saving at each destination with the two-step prefix. -/
theorem nash_degree_two_swap_bound (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s)
    {u v w : Fin n} (huvBuy : v ∈ (s u).val) (hvw : (graph s).Adj v w)
    (huw : u ≠ w)
    (hdegree : ∀ x, (graph s).Adj v x → reachableAvoiding (graph s) v u x → x = u ∨ x = w) :
    (verticesViaTwoSteps (graph s) u w).card ≤ (separatedVertices (graph s) u v).card := by
  let G := graph s
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have huv : G.Adj u v := Or.inl huvBuy
  let A := separatedVertices G u v
  let B := verticesViaTwoSteps G u w
  suffices hcard : (B.card : ℝ) ≤ (A.card : ℝ) by exact_mod_cast hcard
  let sold : Finset (Fin n) := {v}
  let Swapped := graph (redirect s u w huw sold)
  have keep {a b} (hab : G.Adj a b) (ha : a ≠ u ∨ b ≠ v) (hb : b ≠ u ∨ a ≠ v) :
      Swapped.Adj a b := by
    apply redirect_preserves_adj hab
    · simpa [sold] using ha
    · simpa [sold] using hb
  let viaW : Swapped.Walk u w := (redirect_adj_target s huw sold).toWalk
  have hwv : Swapped.Adj w v := keep hvw.symm (Or.inl huw.symm) (Or.inl huv.ne.symm)
  let viaV := viaW.concat hwv
  obtain ⟨hconn, hb⟩ := two_neighbor_distanceSum_bound hG huv hvw hdegree keep viaV viaW
  have hnonneg : 0 ≤ distanceSum Swapped u - distanceSum G u := by
    exact sub_nonneg.mpr (nash_swap_distanceSum_le s α hne huw huvBuy hconn)
  change distanceSum Swapped u - distanceSum G u ≤
    (A.card : ℝ) * ((viaV.length : ℝ) - 1) + (B.card : ℝ) * ((viaW.length : ℝ) - 2) at hb
  norm_num [viaV, viaW, Walk.length_concat] at hb
  linarith

/-- Shorter routes after deleting the purchase improve the degree-two price
bound by the sum of their savings over the usual detour. -/
theorem nash_degree_two_deletion_with_credits (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s)
    {u v w : Fin n} (huvBuy : v ∈ (s u).val) (hvw : (graph s).Adj v w)
    (huw : u ≠ w)
    (hdegree : ∀ x, (graph s).Adj v x → reachableAvoiding (graph s) v u x → x = u ∨ x = w)
    (arm : (graph s).Walk u w) (havoid : v ∉ arm.support) (hLength : 2 ≤ arm.length)
    (saving : Fin n → ℝ) (hSaving : ∀ x, 0 < saving x →
      x ∈ verticesViaTwoSteps (graph s) u w ∧
      ((graph (erasePurchase s u v)).dist u x : ℝ) - (graph s).dist u x + saving x
        ≤ (arm.length : ℝ) - 2) :
    (α : ℝ) + ∑ x, saving x ≤
      2 * ((arm.length : ℝ) - 1) * ((separatedVertices (graph s) u v).card : ℝ) := by
  classical
  let G := graph s
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have huv : G.Adj u v := Or.inl huvBuy
  let A := separatedVertices G u v
  let B := verticesViaTwoSteps G u w
  have hSwap := nash_degree_two_swap_bound s α hne huvBuy hvw huw hdegree
  have hcardReal : (B.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hSwap
  let Deleted := graph (erasePurchase s u v)
  have keep {a b} (hab : G.Adj a b) (ha : a ≠ u ∨ b ≠ v) (hb : b ≠ u ∨ a ≠ v) :
      Deleted.Adj a b := adj_erasePurchase s hab ha hb
  have he : s(u, v) ∉ arm.edges := fun h => havoid (arm.snd_mem_support_of_mem_edges h)
  obtain ⟨viaW, hW⟩ := walk_erasePurchase s arm he
  have hwv : Deleted.Adj w v := keep hvw.symm (Or.inl huw.symm) (Or.inl huv.ne.symm)
  let viaV := viaW.concat hwv
  obtain ⟨hconn, hpoint⟩ := two_neighbor_distance_bound hG huv hvw hdegree keep viaV viaW
  have hprice := nash_deletion_bound α s hne huvBuy hconn
  have hcredits (x : Fin n) :
      (Deleted.dist u x : ℝ) - G.dist u x + saving x ≤
      (if x ∈ A then (arm.length : ℝ) else 0) +
      (if x ∈ B then (arm.length : ℝ) - 2 else 0) := by
    by_cases hx : 0 < saving x
    · obtain ⟨hxB, hshort⟩ := hSaving x hx
      have hnonneg : 0 ≤ (if x ∈ A then (arm.length : ℝ) else 0) := by positivity
      rw [if_pos (show x ∈ B from hxB)]
      exact hshort.trans (le_add_of_nonneg_left hnonneg)
    · have hp := hpoint x
      change (Deleted.dist u x : ℝ) - G.dist u x ≤
        (if x ∈ A then (viaV.length : ℝ) - 1 else 0) +
        (if x ∈ B then (viaW.length : ℝ) - 2 else 0) at hp
      simp only [viaV, Walk.length_concat, hW, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hp
      exact (add_le_of_nonpos_right (le_of_not_gt hx)).trans hp
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hcredits x)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, indicator_sum] at hb
  change distanceSum Deleted u - distanceSum G u + (∑ x, saving x) ≤
    (A.card : ℝ) * arm.length + (B.card : ℝ) * ((arm.length : ℝ) - 2) at hb
  have hlen : (2 : ℝ) ≤ (arm.length : ℝ) := by exact_mod_cast hLength
  have hweighted := mul_le_mul_of_nonneg_right hcardReal (sub_nonneg.mpr hlen)
  nlinarith [hweighted]

/-- Degree-two estimates for a purchase into the middle vertex. The cycle
arm avoids that vertex, and the other incident edge may have either buyer. -/
theorem nash_degree_two_bounds_of_adj (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s)
    {u v w : Fin n} (huvBuy : v ∈ (s u).val) (hvw : (graph s).Adj v w)
    (huw : u ≠ w)
    (hdegree : ∀ x, (graph s).Adj v x → reachableAvoiding (graph s) v u x → x = u ∨ x = w)
    (arm : (graph s).Walk u w) (havoid : v ∉ arm.support) (hLength : 2 ≤ arm.length) :
    (verticesViaTwoSteps (graph s) u w).card ≤ (separatedVertices (graph s) u v).card ∧
    (α : ℝ) ≤ 2 * ((arm.length : ℝ) - 1) * ((separatedVertices (graph s) u v).card : ℝ) := by
  refine ⟨nash_degree_two_swap_bound s α hne huvBuy hvw huw hdegree, ?_⟩
  simpa using nash_degree_two_deletion_with_credits s α hne huvBuy hvw huw hdegree
    arm havoid hLength (fun _ => 0) (fun _ h => (lt_irrefl (0 : ℝ) h).elim)

/-- Dippel–Vetta's degree-two estimates for a directed pair of purchases. -/
theorem nash_degree_two_bounds (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 0 < α)
    {u v w : Fin n} (huvBuy : v ∈ (s u).val) (hvwBuy : w ∈ (s v).val)
    (hdegree : ∀ x, (graph s).Adj v x → reachableAvoiding (graph s) v u x → x = u ∨ x = w)
    (arm : (graph s).Walk u w) (havoid : v ∉ arm.support) (hLength : 2 ≤ arm.length) :
    (verticesViaTwoSteps (graph s) u w).card ≤ (separatedVertices (graph s) u v).card ∧
    (α : ℝ) ≤ 2 * ((arm.length : ℝ) - 1) * ((separatedVertices (graph s) u v).card : ℝ) := by
  have huw : u ≠ w := by
    intro h
    subst w
    exact nash_no_double_purchase α hα s hne huvBuy hvwBuy
  exact nash_degree_two_bounds_of_adj s α hne huvBuy (Or.inl hvwBuy) huw
    hdegree arm havoid hLength

#print axioms nash_degree_two_bounds_of_adj
#print axioms nash_degree_two_deletion_with_credits
#print axioms nash_degree_two_bounds

/-- Every neighbor of `v` in the component of `u` after deleting `v`
is adjacent to `v` in any subgraph that contains every cycle through `uv`. -/
theorem neighbor_mem_of_contains_cycles {G H : SimpleGraph (Fin n)}
    {u v x : Fin n} (huv : H.Adj v u) (hG : H ≤ G) (hvx : G.Adj v x)
    (hreach : reachableAvoiding G v u x)
    (hcycles : ∀ {r} (p : G.Walk r r), p.IsCycle → s(u, v) ∈ p.edges →
      ∀ e ∈ p.edges, e ∈ H.edgeSet) :
    H.Adj v x := by
  by_cases hxu : x = u
  · exact hxu.symm ▸ huv
  obtain ⟨p, hp⟩ := hreach
  let q := p.bypass
  have hq : v ∉ q.support := fun h => hp (p.support_bypass_subset_support h)
  let tail := q.concat hvx.symm
  have htail : tail.IsPath := (Walk.concat_isPath_iff hvx.symm).mpr ⟨p.bypass_isPath, hq⟩
  have hnot : s(v, u) ∉ tail.edges := by
    intro h
    change s(v, u) ∈ (q.concat hvx.symm).edges at h
    rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at h
    rcases h with hqEdge | hlast
    · exact hq (q.fst_mem_support_of_mem_edges hqEdge)
    · rcases Sym2.eq_iff.mp hlast with ⟨he, _⟩ | ⟨_, he⟩
      · exact hvx.ne he
      · exact hxu he.symm
  let cycle := Walk.cons (hG huv) tail
  have hc : cycle.IsCycle := (Walk.cons_isCycle_iff _ _).mpr ⟨htail, hnot⟩
  have hfirst : s(u, v) ∈ cycle.edges := by
    change s(u, v) ∈ (Walk.cons (hG huv) tail).edges
    rw [Walk.edges_cons, List.mem_cons]
    exact Or.inl Sym2.eq_swap
  have hlast : s(v, x) ∈ cycle.edges := by
    change s(v, x) ∈ (Walk.cons (hG huv) (q.concat hvx.symm)).edges
    rw [Walk.edges_cons, List.mem_cons, Walk.edges_concat,
      List.concat_eq_append, List.mem_append, List.mem_singleton]
    exact Or.inr (Or.inr Sym2.eq_swap)
  exact hcycles cycle hc hfirst _ hlast

lemma neighbors_of_degree_two {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {u v w x : Fin n} (huv : H.Adj v u) (hvw : H.Adj v w) (huw : u ≠ w)
    (hdegree : H.degree v = 2) (hx : H.Adj v x) : x = u ∨ x = w := by
  have hsub : ({u, w} : Finset (Fin n)) ⊆ H.neighborFinset v := by
    intro a ha
    rcases (show a = u ∨ a = w by simpa using ha) with hau | haw
    · exact (H.mem_neighborFinset v a).mpr (hau.symm ▸ huv)
    · exact (H.mem_neighborFinset v a).mpr (haw.symm ▸ hvw)
  have hcard : (H.neighborFinset v).card ≤ ({u, w} : Finset (Fin n)).card := by
    rw [card_neighborFinset_eq_degree, hdegree]
    simp [huw]
  have he := Finset.eq_of_subset_of_card_le hsub hcard
  have hm := (H.mem_neighborFinset v x).mpr hx
  rw [← he] at hm
  simpa using hm

/-- The local degree hypothesis follows from degree two in a subgraph
containing the cycles through the original edge. -/
theorem degree_two_neighbor_condition {G H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {u v w : Fin n} (huv : H.Adj v u) (hvw : H.Adj v w) (huw : u ≠ w)
    (hG : H ≤ G) (hdegree : H.degree v = 2)
    (hcycles : ∀ {r} (p : G.Walk r r), p.IsCycle → s(u, v) ∈ p.edges →
      ∀ e ∈ p.edges, e ∈ H.edgeSet) :
    ∀ x, G.Adj v x → reachableAvoiding G v u x → x = u ∨ x = w := by
  intro x hvx hr
  exact neighbors_of_degree_two huv hvw huw hdegree (neighbor_mem_of_contains_cycles huv hG hvx hr hcycles)

/-- The complementary arm of a cycle at a vertex of degree two. -/
theorem exists_cycle_arm_at_degree_two {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {u v w : Fin n} (huv : H.Adj v u) (hvw : H.Adj v w) (huw : u ≠ w)
    (hdegree : H.degree v = 2) (c : H.Walk v v) (hc : c.IsCycle) :
    ∃ arm : H.Walk u w, arm.IsPath ∧ v ∉ arm.support ∧ arm.length + 2 = c.length := by
  cases c with
  | nil => simp at hc
  | @cons _ a _ hva path =>
    obtain ⟨b, q, hbv, rfl⟩ : ∃ (b : Fin n) (q : H.Walk a b) (h : H.Adj b v),
        path = q.concat h := by
      cases path with
      | nil => exact (hva.ne rfl).elim
      | cons hab p => exact Walk.exists_cons_eq_concat hab p
    obtain ⟨hpath, hfirst⟩ := (Walk.cons_isCycle_iff (q.concat hbv) hva).mp hc
    obtain ⟨hq, havoid⟩ := (Walk.concat_isPath_iff hbv).mp hpath
    have hab : a ≠ b := by
      intro he
      apply hfirst
      rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton]
      exact Or.inr ((congrArg (fun x : Fin n => s(v, x)) he).trans Sym2.eq_swap)
    have ha := neighbors_of_degree_two huv hvw huw hdegree hva
    have hb := neighbors_of_degree_two huv hvw huw hdegree hbv.symm
    rcases ha with hau | haw
    · have hbw : b = w := hb.resolve_left (fun h => hab (hau.trans h.symm))
      exact ⟨q.copy hau hbw, by simpa only [Walk.isPath_copy] using hq,
        by simpa using havoid, by simp [Nat.add_assoc]⟩
    · have hbu : b = u := hb.resolve_right (fun h => hab (haw.trans h.symm))
      exact ⟨q.reverse.copy hbu haw, by simpa only [Walk.isPath_copy] using hq.reverse,
        by simpa [Walk.support_reverse] using havoid,
        by simp [Nat.add_assoc]⟩

/-- Descendants of the second child form a subset of the group whose
shortest routes from its grandparent can start with the two downward edges. -/
theorem branch_subset_verticesViaTwoSteps {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {root u v w : Fin n} (T : ShortestParents G root) (hv : v ≠ root) (hw : w ≠ root)
    (hvu : T.parent v = u) (hwv : T.parent w = v) :
    T.branch w ⊆ verticesViaTwoSteps G u w := by
  have hdv := T.parent_depth hv
  have hdw := T.parent_depth hw
  rw [hvu] at hdv
  rw [hwv] at hdw
  intro x hxw
  have hxv := T.mem_branch_of_mem_child_branch hw hxw
  rw [hwv] at hxv
  have hxu := T.mem_branch_of_mem_child_branch hv hxv
  rw [hvu] at hxu
  have hgw := T.branch_geodesic hxw hG
  have hgu := T.branch_geodesic hxu hG
  exact mem_verticesViaTwoSteps.mpr (by omega)

/-- The degree-two estimate for a directed pair of downward tree edges. -/
theorem nash_degree_two_down_branch (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 0 < α)
    {root u v w : Fin n} (T : ShortestParents (graph s) root)
    (hv : v ≠ root) (hw : w ≠ root) (hvu : T.parent v = u) (hwv : T.parent w = v)
    (huvBuy : v ∈ (s u).val) (hvwBuy : w ∈ (s v).val)
    (hdegree : ∀ x, (graph s).Adj v x → reachableAvoiding (graph s) v u x → x = u ∨ x = w)
    (arm : (graph s).Walk u w) (havoid : v ∉ arm.support) (hLength : 2 ≤ arm.length) :
    (T.branch w).card ≤ (separatedVertices (graph s) u v).card ∧
    (α : ℝ) ≤ 2 * ((arm.length : ℝ) - 1) * ((separatedVertices (graph s) u v).card : ℝ) := by
  have hG := nash_connected (Nat.zero_lt_of_lt root.isLt) α s hne
  have hbranch := Finset.card_le_card (branch_subset_verticesViaTwoSteps hG T hv hw hvu hwv)
  obtain ⟨hsize, hprice⟩ := nash_degree_two_bounds s α hne hα huvBuy hvwBuy hdegree arm havoid hLength
  exact ⟨hbranch.trans hsize, hprice⟩

/-- The degree-two price bound on a cycle applies to either owner of the
edge beyond the middle vertex. -/
theorem nash_degree_two_cycle_bound_of_adj (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (hH : H ≤ graph s)
    {u v w : Fin n} (huv : H.Adj v u) (hvw : H.Adj v w) (hdegree : H.degree v = 2)
    (huvBuy : v ∈ (s u).val) (huw : u ≠ w)
    (hcycles : ∀ {r} (p : (graph s).Walk r r), p.IsCycle → s(u, v) ∈ p.edges →
      ∀ e ∈ p.edges, e ∈ H.edgeSet)
    (c : H.Walk v v) (hc : c.IsCycle) (hcLen : 4 ≤ c.length) :
    (verticesViaTwoSteps (graph s) u w).card ≤ (separatedVertices (graph s) u v).card ∧
      (α : ℝ) ≤ 2 * ((c.length : ℝ) - 3) * ((separatedVertices (graph s) u v).card : ℝ) := by
  obtain ⟨arm, _, havoid, hlen⟩ := exists_cycle_arm_at_degree_two huv hvw huw hdegree c hc
  have hmin : 2 ≤ arm.length := by omega
  have hloc := degree_two_neighbor_condition huv hvw huw hH hdegree hcycles
  obtain ⟨hcard, hbound⟩ := nash_degree_two_bounds_of_adj s α hne huvBuy (hH hvw) huw hloc
    (arm.mapLe hH) (by simpa only [Walk.support_mapLe_eq_support] using havoid)
    (by simpa only [Walk.length_mapLe] using hmin)
  rw [Walk.length_mapLe] at hbound
  have hlenReal : (arm.length : ℝ) + 2 = (c.length : ℝ) := by exact_mod_cast hlen
  exact ⟨hcard, by nlinarith⟩

/-- The local degree-two price bound for a directed pair of purchases
and a sufficiently long cycle. -/
theorem nash_degree_two_cycle_bound_of_length (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 0 < α)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (hH : H ≤ graph s)
    {u v w : Fin n} (huv : H.Adj v u) (hvw : H.Adj v w) (hdegree : H.degree v = 2)
    (huvBuy : v ∈ (s u).val) (hvwBuy : w ∈ (s v).val)
    (hcycles : ∀ {r} (p : (graph s).Walk r r), p.IsCycle → s(u, v) ∈ p.edges →
      ∀ e ∈ p.edges, e ∈ H.edgeSet)
    (c : H.Walk v v) (hc : c.IsCycle) (hcLen : 4 ≤ c.length) :
    (verticesViaTwoSteps (graph s) u w).card ≤ (separatedVertices (graph s) u v).card ∧
    (α : ℝ) ≤ 2 * ((c.length : ℝ) - 3) * ((separatedVertices (graph s) u v).card : ℝ) := by
  have huw : u ≠ w := by
    intro h
    subst w
    exact nash_no_double_purchase α hα s hne huvBuy hvwBuy
  exact nash_degree_two_cycle_bound_of_adj s α hne H hH huv hvw hdegree
    huvBuy huw hcycles c hc hcLen

/-- The degree-two bound in terms of the length of a cycle in the subgraph.
Taking a shortest cycle through the middle vertex gives the estimate of Lemma 9. -/
theorem nash_degree_two_cycle_bound (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (hH : H ≤ graph s)
    {u v w : Fin n} (huv : H.Adj v u) (hvw : H.Adj v w) (hdegree : H.degree v = 2)
    (huvBuy : v ∈ (s u).val) (hvwBuy : w ∈ (s v).val)
    (hcycles : ∀ {r} (p : (graph s).Walk r r), p.IsCycle → s(u, v) ∈ p.edges →
      ∀ e ∈ p.edges, e ∈ H.edgeSet)
    (c : H.Walk v v) (hc : c.IsCycle) :
    (verticesViaTwoSteps (graph s) u w).card ≤ (separatedVertices (graph s) u v).card ∧
      (α : ℝ) ≤ 2 * ((c.length : ℝ) - 3) * ((separatedVertices (graph s) u v).card : ℝ) := by
  have hcLen := nash_cycle_length_ge_seven s α hα hne (c.mapLe hH) (hc.mapLe hH)
  rw [Walk.length_mapLe] at hcLen
  exact nash_degree_two_cycle_bound_of_length s α hne (lt_of_le_of_lt (by positivity) hα)
    H hH huv hvw hdegree huvBuy hvwBuy hcycles c hc (by omega)

#print axioms degree_two_neighbor_condition
#print axioms branch_subset_verticesViaTwoSteps
#print axioms nash_degree_two_down_branch
#print axioms nash_degree_two_cycle_bound_of_adj
#print axioms nash_degree_two_cycle_bound

end Lax869952Proofs
