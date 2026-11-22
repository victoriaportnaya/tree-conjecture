import Lax869952Proofs.CycleCertificate

set_option warningAsError true

namespace Lax869952Proofs.CycleCertificate

def vectors {α : Type} (values : List α) : (k : ℕ) → List (Fin k → α)
  | 0 => [Fin.elim0]
  | k + 1 => values.flatMap fun x => (vectors values k).map (Fin.cons x)

theorem mem_vectors {α : Type} (values : List α) (hv : ∀ x : α, x ∈ values)
    {k : ℕ} (f : Fin k → α) : f ∈ vectors values k := by
  induction k with
  | zero =>
    have he : f = Fin.elim0 := funext (fun i => i.elim0)
    simp [vectors, he]
  | succ k ih =>
    apply List.mem_flatMap.mpr
    refine ⟨f 0, hv _, List.mem_map.mpr ⟨fun i => f i.succ, ih _, ?_⟩⟩
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

def checkLabel {k : ℕ} (moves : WeightedMoves k) (num den : ℕ) (l : Labels k) : Bool :=
  !decide (Lipschitz l) ||
    ((moves.all fun wm => decide (wm.2.impact l < (k + 1 : ℤ))) &&
      decide ((den : ℤ) * weightedImpact l moves ≤ (num : ℤ) * (savings moves : ℤ)))

def checkMoves {k : ℕ} (o : Orientation k) (moves : WeightedMoves k) (num den : ℕ) : Bool :=
  (moves.all fun wm => decide (wm.2.Valid o)) && decide (0 < savings moves) &&
    (vectors (List.finRange (k / 2 + 1)) k).all (checkLabel moves num den)

theorem checks_of_checkMoves {k : ℕ} {o : Orientation k} {moves : WeightedMoves k} {num den}
    (h : checkMoves o moves num den = true) : Checks o moves num den := by
  simp only [checkMoves, Bool.and_eq_true_iff] at h
  refine ⟨fun wm hm => of_decide_eq_true (List.all_eq_true.mp h.1.1 wm hm),
    of_decide_eq_true h.1.2, ?_⟩
  intro l hl
  have hMem := mem_vectors (List.finRange (k / 2 + 1)) List.mem_finRange l
  have hLabel := List.all_eq_true.mp h.2 l hMem
  have hTrue : decide (Lipschitz l) = true := decide_eq_true hl
  rw [checkLabel, hTrue] at hLabel
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true_iff] at hLabel
  exact ⟨fun wm hm => of_decide_eq_true (List.all_eq_true.mp hLabel.1 wm hm),
    of_decide_eq_true hLabel.2⟩

end Lax869952Proofs.CycleCertificate
