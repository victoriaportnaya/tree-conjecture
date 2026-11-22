import Lax869952Proofs.CycleCertificateCheck

set_option warningAsError true

namespace Lax869952Proofs.CycleCertificate

/-- Enumerate continuations of a path one adjacent value at a time. -/
private def continuations {α : Type} (values : List α) (adjacent : α → α → Bool) :
    (k : ℕ) → α → List (Fin k → α)
  | 0, _ => [Fin.elim0]
  | k + 1, prev => (values.filter (adjacent prev)).flatMap fun x =>
      (continuations values adjacent k x).map (Fin.cons x)

private theorem continuations_complete {α : Type} (values : List α) (hv : ∀ x : α, x ∈ values)
    (adjacent : α → α → Bool) {k : ℕ} (chain : Fin (k + 1) → α)
    (hChain : ∀ i : Fin k, adjacent (chain i.castSucc) (chain i.succ) = true) :
    (fun i : Fin k => chain i.succ) ∈ continuations values adjacent k (chain 0) := by
  induction k with
  | zero =>
    have he : (fun i : Fin 0 => chain i.succ) = Fin.elim0 := funext (fun i => i.elim0)
    simp [continuations, he]
  | succ k ih =>
    refine List.mem_flatMap.mpr ⟨chain (0 : Fin (k + 1)).succ, ?_, List.mem_map.mpr ⟨fun i : Fin k => chain i.succ.succ, ?_, ?_⟩⟩
    · exact List.mem_filter.mpr ⟨hv _, hChain 0⟩
    · exact ih (fun i => chain i.succ) (fun i => hChain i.succ)
    · funext i
      exact Fin.cases rfl (fun _ => rfl) i

private def closeLabel {m : ℕ} (a b : Fin m) : Bool :=
  decide (a.val ≤ b.val + 1 ∧ b.val ≤ a.val + 1)

private abbrev Normalized {k : ℕ} (l : Labels k) : Prop := ∃ i, (l i).val = 0

private theorem normalize_labels {k : ℕ} (l : Labels (k + 1)) (hl : Lipschitz l) :
    ∃ l' : Labels (k + 1), Lipschitz l' ∧ Normalized l' ∧
      ∃ shift : ℕ, ∀ i, (l i).val = shift + (l' i).val := by
  obtain ⟨j, _, hMin⟩ := Finset.exists_min_image Finset.univ (fun i => (l i).val)
    ⟨0, Finset.mem_univ _⟩
  let l' (i : Fin (k + 1)) : Fin ((k + 1) / 2 + 1) :=
    ⟨(l i).val - (l j).val, lt_of_le_of_lt (Nat.sub_le _ _) (l i).isLt⟩
  have hShift (i) : (l i).val = (l j).val + (l' i).val := by
    have h := hMin i (Finset.mem_univ _)
    dsimp only [l']
    omega
  refine ⟨l', ?_, ⟨j, by simp [l']⟩, (l j).val, hShift⟩
  intro i
  have h := hl i
  rw [hShift i, hShift (next i)] at h
  omega

private theorem impact_shift {k : ℕ} (m : Move k) {l l' : Labels k} {b : ℕ}
    (hShift : ∀ i, (l i).val = b + (l' i).val) : m.impact l = m.impact l' := by
  unfold Move.impact Move.candidates
  have hBase : m.baseline l ↔ m.baseline l' := by
    constructor <;> intro h j hj he <;> specialize h j hj <;>
      have h1 := hShift j <;> have h2 := hShift m.buyer <;> omega
  have hOld : (if m.baseline l then [0] else [] : List ℤ) =
      (if m.baseline l' then [0] else []) := by
    by_cases h : m.baseline l
    · simp only [if_pos h, if_pos (hBase.mp h)]
    · simp only [if_neg h, if_neg (fun hp => h (hBase.mpr hp))]
  rw [hOld]
  congr 2
  apply List.filterMap_congr
  intro i _
  have hSafe : m.safe l i ↔ m.safe l' i := by
    have h1 := hShift i
    have h2 := hShift m.buyer
    unfold Move.safe
    omega
  by_cases h : m.safe l i
  · rw [if_pos h, if_pos (hSafe.mp h)]
    congr 1
    rw [hShift i, hShift m.buyer]
    push_cast
    omega
  · rw [if_neg h, if_neg (fun hp => h (hSafe.mpr hp))]

private theorem weightedImpact_shift {k : ℕ} (moves : WeightedMoves k) {l l' : Labels k} {b : ℕ}
    (hShift : ∀ i, (l i).val = b + (l' i).val) :
    weightedImpact l moves = weightedImpact l' moves := by
  induction moves with
  | nil => rfl
  | cons wm ms ih =>
    obtain ⟨w, m⟩ := wm
    simp only [weightedImpact, impact_shift m hShift, ih]

private theorem foldl_min_le_initial (xs : List ℤ) (a : ℤ) :
    xs.foldl min a ≤ a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (ih (min a x)).trans (min_le_left a x)

private theorem foldl_min_le_candidate {xs : List ℤ} {y : ℤ} (hy : y ∈ xs) (a : ℤ) :
    xs.foldl min a ≤ y := by
  induction xs generalizing a with
  | nil => simp at hy
  | cons x xs ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (foldl_min_le_initial xs (min a y)).trans (min_le_right a y)
    · exact ih hy (min a x)

/-- The route-length check proves that the sentinel in `impact` is never used.
If deletion can change the old shortest path, its first vertex is safe. -/
private theorem impact_lt_of_routes {k : ℕ} (m : Move k) (l : Labels k)
    (hRoutes : ∀ j, (m.route j).length < k) : m.impact l < (k + 1 : ℤ) := by
  by_cases h : m.baseline l
  · have hm : (0 : ℤ) ∈ m.candidates l := by
      rw [Move.candidates, if_pos h]
      simp
    exact (foldl_min_le_candidate hm _).trans_lt (by positivity)
  · unfold Move.baseline at h
    push Not at h
    obtain ⟨j, _, hBefore⟩ := h
    have hSafe : m.safe l j := by
      unfold Move.safe
      omega
    have hm : ((m.route j).length + ((l j).val : ℤ) - ((l m.buyer).val : ℤ)) ∈
        m.candidates l := by
      apply List.mem_append.mpr
      right
      exact List.mem_filterMap.mpr ⟨j, List.mem_finRange j, if_pos hSafe⟩
    have hRoute := hRoutes j
    exact (foldl_min_le_candidate hm _).trans_lt (by omega)

/-- Check a single batch of normalized labels with the given initial value. -/
def checkPathHead {k : ℕ} (moves : WeightedMoves (k + 1)) (num den : ℕ)
    (head : Fin ((k + 1) / 2 + 1)) : Bool :=
  (continuations (List.finRange ((k + 1) / 2 + 1)) closeLabel k head).all fun tail =>
    let l := Fin.cons head tail
    !decide (Normalized l) || !decide (Lipschitz l) ||
      decide ((den : ℤ) * weightedImpact l moves ≤ (num : ℤ) * (savings moves : ℤ))

theorem checks_of_checkPathHeads {k : ℕ} {o : Orientation (k + 1)} {moves : WeightedMoves (k + 1)}
    {num den : ℕ}
    (hValid : (moves.all fun wm => decide (wm.2.Valid o ∧
      ∀ j, (wm.2.route j).length < k + 1)) = true)
    (hSavings : 0 < savings moves)
    (hHeads : ∀ a, checkPathHead moves num den a = true) : Checks o moves num den := by
  have hMove wm (hm : wm ∈ moves) :=
    of_decide_eq_true (List.all_eq_true.mp hValid wm hm)
  refine ⟨fun wm hm => (hMove wm hm).1, hSavings, ?_⟩
  intro l hl
  obtain ⟨l', hLip, hZero, b, hShift⟩ := normalize_labels l hl
  have hPath (i : Fin k) : closeLabel (l' i.castSucc) (l' i.succ) = true := by
    have he : next i.castSucc = i.succ := by
      apply Fin.ext
      change (i.val + 1) % (k + 1) = i.val + 1
      have hi := i.isLt
      exact Nat.mod_eq_of_lt (by omega)
    unfold closeLabel
    apply decide_eq_true
    simpa only [he] using hLip i.castSucc
  have hMem := continuations_complete (List.finRange ((k + 1) / 2 + 1))
    List.mem_finRange closeLabel l' hPath
  have hEval := List.all_eq_true.mp (hHeads (l' 0)) _ hMem
  have he : Fin.cons (l' 0) (fun i : Fin k => l' i.succ) = l' := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  change (!decide (Normalized (Fin.cons (l' 0) _)) ||
    !decide (Lipschitz (Fin.cons (l' 0) _)) || _) = true at hEval
  rw [he] at hEval
  simp only [decide_eq_true hZero, decide_eq_true hLip, Bool.not_true, Bool.false_or] at hEval
  refine ⟨fun wm hm => impact_lt_of_routes wm.2 l (hMove wm hm).2, ?_⟩
  rw [weightedImpact_shift moves hShift]
  exact of_decide_eq_true hEval

end Lax869952Proofs.CycleCertificate
