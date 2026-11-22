import Lax869952Proofs.ShortCycles
import Mathlib.Logic.Equiv.Fin.Rotate

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

private lemma cycle_edge_detours {n : ℕ} (s : Profile n) {u : Fin n}
    (p : (graph s).Walk u u) (hp : p.IsCycle) (i : Fin p.length) :
    (∃ q : (graph (erasePurchase s (p.getVert i.val) (p.getVert (i.val + 1)))).Walk
        (p.getVert i.val) (p.getVert (i.val + 1)), q.length = p.length - 1) ∧
    (∃ q : (graph (erasePurchase s (p.getVert (i.val + 1)) (p.getVert i.val))).Walk
        (p.getVert (i.val + 1)) (p.getVert i.val), q.length = p.length - 1) := by
  let q := (p.drop (i.val + 1)).append (p.take i.val)
  have hq : q.length = p.length - 1 := by
    simp [q, Walk.length_append, Walk.take_length]
    omega
  have hi : i.val < p.edges.length := by simp [i.isLt]
  have he : p.edges[i.val] = s(p.getVert i.val, p.getVert (i.val + 1)) := Walk.getElem_edges hi
  have hn : p.edges.Nodup := hp.isTrail.edges_nodup
  have hnot : s(p.getVert i.val, p.getVert (i.val + 1)) ∉ q.edges := by
    intro h
    rw [← he] at h
    simp only [q, Walk.edges_append, Walk.edges_drop, Walk.edges_take, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨j, hj, hjEq⟩ := List.mem_iff_getElem.mp h
      have hj' : i.val + 1 + j < p.edges.length := by
        simp only [List.length_drop] at hj
        omega
      have hsame : p.edges[i.val] = p.edges[i.val + 1 + j]'hj' := by
        simpa only [List.getElem_drop] using hjEq.symm
      have hindex := hn.getElem_inj_iff.mp hsame
      omega
    · obtain ⟨j, hj, hjEq⟩ := List.mem_iff_getElem.mp h
      have hj' : j < p.edges.length := by
        simp only [List.length_take] at hj
        omega
      have hsame : p.edges[i.val] = p.edges[j]'hj' := by
        simpa only [List.getElem_take] using hjEq.symm
      have hindex := hn.getElem_inj_iff.mp hsame
      simp only [List.length_take] at hj
      omega
  constructor
  · obtain ⟨w, hw⟩ := walk_erasePurchase s q.reverse
      (by simpa only [Walk.edges_reverse, List.mem_reverse] using hnot)
    exact ⟨w, by rw [hw, Walk.length_reverse, hq]⟩
  · obtain ⟨w, hw⟩ := walk_erasePurchase s q (by rwa [Sym2.eq_swap])
    exact ⟨w, hw.trans hq⟩

private lemma finRotate_val {m : ℕ} (i : Fin m) :
    (finRotate m i).val = (i.val + 1) % m := by
  have := i.neZero
  rw [finRotate_apply, Fin.val_add]
  simp [Nat.add_mod_mod]

lemma finRotate_twice_ne {m : ℕ} (hm : 3 ≤ m) (i : Fin m) :
    finRotate m (finRotate m i) ≠ i := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [finRotate_val, Nat.mod_add_mod, Nat.add_assoc] at hv
  change (i.val + 2) % m = i.val at hv
  by_cases h : i.val + 2 < m
  · rw [Nat.mod_eq_of_lt h] at hv
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : m ≤ i.val + 2),
      Nat.mod_eq_of_lt (by omega : i.val + 2 - m < m)] at hv
    omega

lemma finRotate_constant {m : ℕ} (P : Fin m → Prop)
    (hstep : ∀ i, P (finRotate m i) → P i) : (∀ i, P i) ∨ (∀ i, ¬ P i) := by
  classical
  cases m with
  | zero => exact Or.inl (fun i => Fin.elim0 i)
  | succ m =>
    by_cases hzero : P 0
    · left
      have hlast : P (Fin.last m) := hstep _ (by simpa only [finRotate_last] using hzero)
      have hback : ∀ (k : ℕ) (hk : k ≤ m), P ⟨m - k, by omega⟩ := by
        intro k
        induction k with
        | zero =>
          intro _
          rw [show (⟨m - 0, by omega⟩ : Fin (m + 1)) = Fin.last m from Fin.ext (by simp)]
          exact hlast
        | succ k ih =>
          intro hk
          apply hstep
          rw [finRotate_of_lt (by omega : m - (k + 1) < m)]
          convert ih (by omega : k ≤ m) using 1
          exact Fin.ext (by dsimp; omega)
      intro i
      convert hback (m - i.val) (by omega) using 1
      exact Fin.ext (by dsimp; omega)
    · right
      have hforward : ∀ (k : ℕ) (hk : k ≤ m), ¬ P ⟨k, by omega⟩ := by
        intro k
        induction k with
        | zero => exact fun _ => hzero
        | succ k ih =>
          intro hk hp
          have hs := hstep ⟨k, by omega⟩
          rw [finRotate_of_lt (by omega : k < m)] at hs
          exact ih (by omega) (hs hp)
      exact fun i => hforward i.val (by omega)

lemma cycle_getVert_finRotate {V : Type*} {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (i : Fin p.length) :
    p.getVert (finRotate p.length i).val = p.getVert (i.val + 1) := by
  rw [finRotate_val]
  by_cases hi : i.val + 1 < p.length
  · rw [Nat.mod_eq_of_lt hi]
  · have hlast : i.val + 1 = p.length := by omega
    rw [hlast, Nat.mod_self, Walk.getVert_zero, Walk.getVert_length]

/-- The girth inequality of Dippel–Vetta (2024), Lemma 4.
Every cycle of length k at equilibrium satisfies 2α ≤ n(k − 2). -/
theorem nash_cycle_price_bound {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {u : Fin n} (p : (graph s).Walk u u) (hp : p.IsCycle) :
    2 * (α : ℝ) ≤ (n : ℝ) * ((p.length - 2 : ℕ) : ℝ) := by
  classical
  have hmin := hp.three_le_length
  let next := finRotate p.length
  let v (i : Fin p.length) := p.getVert i.val
  let forward (i : Fin p.length) : Prop := v (next i) ∈ (s (v i)).val
  let backward (i : Fin p.length) : Prop := v i ∈ (s (v (next i))).val
  have hnext (i : Fin p.length) : v (next i) = p.getVert (i.val + 1) :=
    cycle_getVert_finRotate p i
  have hinj : Function.Injective v := by
    intro i j h
    apply Fin.ext
    exact hp.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) h
  have hadj (i : Fin p.length) : forward i ∨ backward i := by
    change (graph s).Adj (v i) (v (next i))
    rw [hnext i]
    exact p.adj_getVert_succ i.isLt
  have hroutes (i : Fin p.length) :
      (∃ q : (graph (erasePurchase s (v i) (v (next i)))).Walk (v i) (v (next i)),
        q.length = p.length - 1) ∧
      (∃ q : (graph (erasePurchase s (v (next i)) (v i))).Walk (v (next i)) (v i),
        q.length = p.length - 1) := by
    rw [hnext i]
    exact cycle_edge_detours s p hp i
  let qf (i : Fin p.length) := (hroutes i).1.choose
  let qb (i : Fin p.length) := (hroutes i).2.choose
  have hf (i : Fin p.length) : (qf i).length = p.length - 1 := (hroutes i).1.choose_spec
  have hb (i : Fin p.length) : (qb i).length = p.length - 1 := (hroutes i).2.choose_spec
  by_cases htwo : ∃ i, backward i ∧ forward (next i)
  · obtain ⟨i, hback, hfor⟩ := htwo
    have hneigh : v i ≠ v (next (next i)) :=
      fun h => finRotate_twice_ne hmin i (hinj h).symm
    exact two_purchase_detour_bound s α hne hneigh hfor hback (p.length - 2)
      (qf (next i)) (qb i) (by rw [hf]; omega) (by rw [hb]; omega)
      (by rw [hf]; omega) (by rw [hb]; omega)
  · have hstep (i : Fin p.length) (hi : forward (next i)) : forward i :=
      (hadj i).resolve_right (fun hb' => htwo ⟨i, hb', hi⟩)
    rcases finRotate_constant forward hstep with hall | hnone
    · exact directed_cycle_detour_bound s α hne (by omega) v next (p.length - 2) hall qf
        (fun i => by rw [hf]; omega) (fun i => by rw [hf]; omega)
    · have hrev (i : Fin p.length) : v (next.symm i) ∈ (s (v i)).val := by
        have h := (hadj (next.symm i)).resolve_left (hnone _)
        change v (next.symm i) ∈ (s (v (next (next.symm i)))).val at h
        rwa [next.apply_symm_apply i] at h
      have hrouteRev (i : Fin p.length) :
          ∃ q : (graph (erasePurchase s (v i) (v (next.symm i)))).Walk (v i) (v (next.symm i)),
            q.length = p.length - 1 := by
        have h := (hroutes (next.symm i)).2
        rwa [next.apply_symm_apply i] at h
      exact directed_cycle_detour_bound s α hne (by omega) v next.symm (p.length - 2) hrev
        (fun i => (hrouteRev i).choose)
        (fun i => by rw [(hrouteRev i).choose_spec]; omega)
        (fun i => by rw [(hrouteRev i).choose_spec]; omega)

/-- Dippel–Vetta (2024), Corollary 5. At price above 2n, any cycle has at least seven edges. -/
theorem nash_cycle_length_ge_seven {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hα : 2 * (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    {u : Fin n} (p : (graph s).Walk u u) (hp : p.IsCycle) : 7 ≤ p.length := by
  by_contra! hshort
  have h₁ : p.length - 2 ≤ 4 := by omega
  have h₂ : ((p.length - 2 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast h₁
  have h₃ : 2 * (n : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hbound := nash_cycle_price_bound s α hne p hp
  have hprod := mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg (α := ℝ) n)
  linarith

#print axioms nash_cycle_price_bound
#print axioms nash_cycle_length_ge_seven

/-- The published price threshold suffices for at most six players by girth alone. -/
theorem nash_tree_of_le_six_at_two_n {n : ℕ} (hn : 0 < n) (hsix : n ≤ 6)
    (s : Profile n) (α : ℝ≥0) (hα : 2 * (n : ℝ≥0) < α)
    (hne : IsNashEquilibrium α s) : (graph s).IsTree := by
  refine ⟨nash_connected hn α s hne, ?_⟩
  intro u p hp
  have hmin := nash_cycle_length_ge_seven s α hα hne p hp
  have hmax := hp.nodup_dropLast_support.length_le_card
  simp [Walk.length_support] at hmax
  omega

#print axioms nash_tree_of_le_six_at_two_n

end Lax869952Proofs
