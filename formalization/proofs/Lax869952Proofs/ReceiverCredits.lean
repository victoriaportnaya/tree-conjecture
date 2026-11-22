import Lax869952Proofs.BlockSwaps
import Lax869952Proofs.GirthDistances

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ} {S : Finset (Fin n)}

/-- An attachment reached from the other end of a cycle arm has a
shorter route than the usual detour via the end of the arm. -/
private theorem receiver_arm_saving (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    (girth : ∀ {x}, (c : (graph s).Walk x x) → c.IsCycle → 8 ≤ c.length)
    {u v w : Fin n} (huv : (blockGraph (graph s) S).Adj u v)
    (hvw : (blockGraph (graph s) S).Adj v w)
    (arm : (blockGraph (graph s) S).Walk u w) (hp : arm.IsPath)
    (havoid : v ∉ arm.support) {k : ℕ} (hk : 1 ≤ k) (hk₂ : k ≤ 2)
    (hkArm : k < arm.length) :
    let z := arm.reverse.getVert k
    ∀ x ∈ blockAttachment (graph s) S z,
      x ∈ verticesViaTwoSteps (graph s) u w ∧
      ((graph (erasePurchase s u v)).dist u x : ℝ) - (graph s).dist u x + 2 * k
        ≤ (arm.length : ℝ) - 2 := by
  classical
  let G := graph s
  let z := arm.reverse.getVert k
  let D := graph (erasePurchase s u v)
  let q := arm.reverse.take k
  let armStart := (arm.take (arm.length - k)).copy rfl (arm.getVert_reverse k).symm
  have qLen : q.length = k := by
    simp [q, min_eq_left hkArm.le]
  have pLen : armStart.length = arm.length - k := by simp [armStart]
  have qOutside (x : Fin n) (hx : x ∈ q.support) : x ∈ arm.support := by
    obtain ⟨j, hj, _⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    change (arm.reverse.take k).getVert j = x at hj
    rw [Walk.take_getVert] at hj
    exact List.mem_reverse.mp (by simpa only [Walk.support_reverse, hj] using
      arm.reverse.getVert_mem_support (k ⊓ j))
  have uOutside : u ∉ q.support := by
    intro hu
    obtain ⟨j, hj, hjLen⟩ := Walk.mem_support_iff_exists_getVert.mp hu
    rw [qLen] at hjLen
    change (arm.reverse.take k).getVert j = u at hj
    rw [Walk.take_getVert, min_eq_right hjLen] at hj
    have hlast : arm.reverse.getVert arm.length = u := by
      rw [← Walk.length_reverse arm, Walk.getVert_length]
    have he := hp.reverse.getVert_injOn (by simpa using hjLen.trans hkArm.le)
      (by simp) (hj.trans hlast.symm)
    omega
  have vOutside : v ∉ q.support := fun h => havoid (qOutside v h)
  let fromU := Walk.cons huv (Walk.cons hvw q)
  have hfromU : fromU.IsPath := by
    apply (Walk.cons_isPath_iff _ _).mpr
    refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨hp.reverse.take k, vOutside⟩, ?_⟩
    simpa only [Walk.support_cons, List.mem_cons, not_or] using
      And.intro ((blockGraph_le G S huv).ne) uOutside
  have hzS : z ∈ S := by
    have hstep := arm.reverse.adj_getVert_succ
      (i := k - 1) (by simpa only [Walk.length_reverse] using
        (show k - 1 < arm.length by omega))
    rw [show k - 1 + 1 = k by omega] at hstep
    exact hstep.2.1
  have hLe : blockGraph G S ≤ G := blockGraph_le G S
  have distOfShort {a b : Fin n} (p : (blockGraph G S).Walk a b)
      (hPath : p.IsPath) (hLen : p.length ≤ 4) : G.dist a b = p.length := by
    have hUpper : G.dist a b ≤ p.length := by simpa using dist_le (p.mapLe hLe)
    have hPathG : (p.mapLe hLe).IsPath := by
      simpa only [Walk.isPath_def, Walk.support_mapLe_eq_support] using hPath
    have hLower := min_path_length_girth_sub_le_dist girth (p.mapLe hLe) hPathG
    rw [Walk.length_mapLe, min_eq_left (show p.length ≤ 8 - p.length by omega)] at hLower
    exact le_antisymm hUpper hLower
  have dW : G.dist w z = k := (distOfShort q (hp.reverse.take k) (by omega)).trans qLen
  have dU : G.dist u z = k + 2 := by
    rw [distOfShort fromU hfromU (by simp [fromU, qLen]; omega)]
    simp [fromU, qLen, Nat.add_assoc]
  have pOutside : v ∉ (armStart.mapLe hLe).support := by
    intro hx
    rw [Walk.support_mapLe_eq_support, Walk.support_copy, Walk.support_take] at hx
    exact havoid (List.mem_of_mem_take hx)
  obtain ⟨newPrefix, newLen⟩ := walk_erasePurchase s (armStart.mapLe hLe)
    (i := u) (r := v) (fun h => pOutside ((armStart.mapLe hLe).snd_mem_support_of_mem_edges h))
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  change ∀ x ∈ blockAttachment G S z, x ∈ verticesViaTwoSteps G u w ∧
    (D.dist u x : ℝ) - G.dist u x + 2 * k ≤ (arm.length : ℝ) - 2
  intro x hx
  have dux : G.dist u x = G.dist u z + G.dist z x :=
    hS.dist_add_of_mem_blockAttachment hG hzS huv.1 hx
  have dwx : G.dist w x = G.dist w z + G.dist z x :=
    hS.dist_add_of_mem_blockAttachment hG hzS hvw.2.1 hx
  refine ⟨mem_verticesViaTwoSteps.mpr (by omega), ?_⟩
  obtain ⟨tail, hTail⟩ := hG.exists_walk_length_eq_dist z x
  have hAway : u ∉ tail.support := by
    intro hu
    have hVia := walk_length_ge_via tail hu
    change G.dist z u + G.dist u x ≤ tail.length at hVia
    rw [hTail, dux, dist_comm (u := z) (v := u), dU] at hVia
    omega
  obtain ⟨newTail, tailLen⟩ := walk_erasePurchase s tail (i := u) (r := v)
    (fun h => hAway (tail.fst_mem_support_of_mem_edges h))
  have hDetour : D.dist u x ≤ arm.length - k + G.dist z x := by
    simpa only [Walk.length_append, newLen, Walk.length_mapLe, pLen, tailLen, hTail]
      using dist_le (newPrefix.append newTail)
  have hNat : D.dist u x + 2 * k + 2 ≤ G.dist u x + arm.length := by omega
  have hReal : (D.dist u x : ℝ) + 2 * k + 2 ≤
      (G.dist u x : ℝ) + arm.length := by exact_mod_cast hNat
  linarith

/-- The attachments one and two edges beyond the middle vertex save two
and four steps per player from the degree-two deletion estimate. -/
theorem nash_receiver_cycle_bound_with_credits (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    [DecidableRel (blockGraph (graph s) S).Adj]
    (girth : ∀ {x}, (c : (graph s).Walk x x) → c.IsCycle → 8 ≤ c.length)
    {u v w : Fin n} (huv : (blockGraph (graph s) S).Adj u v)
    (hvw : (blockGraph (graph s) S).Adj v w) (huw : u ≠ w)
    (hdegree : (blockGraph (graph s) S).degree v = 2) (hBuy : v ∈ (s u).val)
    (c : (blockGraph (graph s) S).Walk v v) (hc : c.IsCycle) :
    (α : ℝ) + 6 ≤ 2 * ((c.length : ℝ) - 3) *
      ((blockAttachment (graph s) S v).card : ℝ) := by
  classical
  let G := graph s
  have hLe := blockGraph_le G S
  have hLength : 8 ≤ c.length := by
    simpa only [Walk.length_mapLe] using girth (c.mapLe hLe) (hc.mapLe hLe)
  obtain ⟨arm, hp, havoid, hlen⟩ := exists_cycle_arm_at_degree_two huv.symm hvw huw hdegree c hc
  have hArm : 6 ≤ arm.length := by omega
  let z₃ := arm.reverse.getVert 1
  let z₄ := arm.reverse.getVert 2
  let A₃ := blockAttachment G S z₃
  let A₄ := blockAttachment G S z₄
  let saving (x : Fin n) : ℝ := (if x ∈ A₃ then 2 else 0) + (if x ∈ A₄ then 4 else 0)
  have hz₃ : z₃ ∈ S := by
    have h := arm.reverse.adj_getVert_succ (i := 0) (by simpa using
      (show 0 < arm.length by omega))
    exact h.2.1
  have hz₄ : z₄ ∈ S := by
    have h := arm.reverse.adj_getVert_succ (i := 1) (by simpa using
      (show 1 < arm.length by omega))
    exact h.2.1
  have hz : z₃ ≠ z₄ := by
    intro he
    have h := hp.reverse.getVert_injOn (by simpa using (show 1 ≤ arm.length by omega))
      (by simpa using (show 2 ≤ arm.length by omega)) he
    omega
  have hdis := hS.disjoint_blockAttachments hz₃ hz₄ hz
  have hdegree' := degree_two_neighbor_condition huv.symm hvw huw hLe hdegree
    (fun p hp he => hS.cycle_edges_subset p hp huv he)
  have hSaving (x : Fin n) (hx : 0 < saving x) :
      x ∈ verticesViaTwoSteps G u w ∧
      ((graph (erasePurchase s u v)).dist u x : ℝ) - G.dist u x + saving x ≤
        ((arm.mapLe hLe).length : ℝ) - 2 := by
    by_cases hx₃ : x ∈ A₃
    · have hx₄ : x ∉ A₄ := fun h => Finset.disjoint_left.mp hdis hx₃ h
      have h := receiver_arm_saving s α hne hS girth huv hvw arm hp havoid
        (k := 1) (by decide) (by decide) (by omega) x hx₃
      norm_num [saving, hx₃, hx₄, Walk.length_mapLe] at h ⊢
      exact h
    · by_cases hx₄ : x ∈ A₄
      · have h := receiver_arm_saving s α hne hS girth huv hvw arm hp havoid
          (k := 2) (by decide) (by decide) (by omega) x hx₄
        norm_num [saving, hx₃, hx₄, Walk.length_mapLe] at h ⊢
        exact h
      · simp [saving, hx₃, hx₄] at hx
  have hbound := nash_degree_two_deletion_with_credits s α hne hBuy (hLe hvw) huw hdegree'
    (arm.mapLe hLe) (by simpa only [Walk.support_mapLe_eq_support] using havoid)
    (by simpa only [Walk.length_mapLe] using (show 2 ≤ arm.length by omega)) saving hSaving
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  rw [Walk.length_mapLe,
    hS.separatedVertices_eq_blockAttachment hG huv.1 huv.2.1 (hLe huv).ne] at hbound
  have indicator (A : Finset (Fin n)) (a : ℝ) :
      (∑ x : Fin n, if x ∈ A then a else 0) = (A.card : ℝ) * a := by
    rw [← Finset.sum_filter]
    simp
  have hSum : (∑ x : Fin n, saving x) = (A₃.card : ℝ) * 2 + (A₄.card : ℝ) * 4 := by
    simp only [saving, Finset.sum_add_distrib, indicator]
  have h₃ : (1 : ℝ) ≤ A₃.card := by exact_mod_cast blockAttachment_card_pos (G := G) (S := S) z₃
  have h₄ : (1 : ℝ) ≤ A₄.card := by exact_mod_cast blockAttachment_card_pos (G := G) (S := S) z₄
  have hLenReal : (arm.length : ℝ) + 2 = c.length := by exact_mod_cast hlen
  rw [hSum] at hbound
  nlinarith

#print axioms nash_receiver_cycle_bound_with_credits

end Lax869952Proofs
