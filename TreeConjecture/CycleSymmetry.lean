import TreeConjecture.CycleLabelCheck

set_option warningAsError true

namespace TreeConjecture.CycleCertificate

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped NNReal

variable {k n : ℕ}

def cycleIndex (a : Fin k) (reversed : Bool) (i : Fin k) : Fin k :=
  if reversed then a - i else a + i

def reorient (o : Orientation k) (a : Fin k) (reversed : Bool) (i : Fin k) : Bool :=
  if reversed then !(o (cycleIndex a reversed (next i))) else o (cycleIndex a reversed i)

/-- Rotations and reflections preserve the metric and consecutive pairs. -/
abbrev Symmetries (k : ℕ) : Prop :=
  ∀ (a : Fin k) (rev : Bool),
    (∀ i j, cycleIndex a rev i = cycleIndex a rev j → i = j) ∧
    (∀ i j, cycleDistance (cycleIndex a rev i) (cycleIndex a rev j) = cycleDistance i j) ∧
    (∀ i, if rev then next (cycleIndex a rev (next i)) = cycleIndex a rev i
      else next (cycleIndex a rev i) = cycleIndex a rev (next i))

private def Embedding.reindex {G : SimpleGraph (Fin n)} (e : Embedding G k)
    (h : Symmetries k) (a : Fin k) (rev : Bool) : Embedding G k where
  vertex := ⟨fun i => e.vertex (cycleIndex a rev i), fun _ _ he => (h a rev).1 _ _ (e.vertex.injective he)⟩
  adjacent i := by
    change G.Adj (e.vertex (cycleIndex a rev i)) (e.vertex (cycleIndex a rev (next i)))
    cases rev
    · have he := (h a false).2.2 i
      simp only [Bool.false_eq_true, if_false] at he
      rw [← he]
      exact e.adjacent _
    · have he := (h a true).2.2 i
      simp only [if_true] at he
      rw [← he]
      exact (e.adjacent _).symm
  isometric i j := (e.isometric _ _).trans ((h a rev).2.1 i j)

private theorem models_reindex (s : Profile n) (e : Embedding (graph s) k)
    (h : Symmetries k) {o : Orientation k} (ho : Models s e o) (a : Fin k) (rev : Bool) :
    Models s (e.reindex h a rev) (reorient o a rev) := by
  intro i
  cases rev
  · have he := (h a false).2.2 i
    simp only [Bool.false_eq_true, if_false] at he
    let j := cycleIndex a false i
    change (if o j then e.vertex j ∈ (s (e.vertex (cycleIndex a false (next i)))).val
      else e.vertex (cycleIndex a false (next i)) ∈ (s (e.vertex j)).val)
    rw [← he]
    exact ho _
  · have he := (h a true).2.2 i
    simp only [if_true] at he
    let j := cycleIndex a true (next i)
    have hNext : next j = cycleIndex a true i := he
    change (if !o j then e.vertex (cycleIndex a true i) ∈ (s (e.vertex j)).val
      else e.vertex j ∈ (s (e.vertex (cycleIndex a true i))).val)
    rw [← hNext]
    have hBuy := ho j
    cases hBit : o j <;> simp [hBit] at hBuy ⊢ <;> exact hBuy

abbrev Representatives (k : ℕ) := List (Orientation k × WeightedMoves k)

def covered (certs : Representatives k) (o : Orientation k) : Bool :=
  (List.finRange k).any fun a => [false, true].any fun rev =>
    certs.any fun c => decide (∀ i, reorient o a rev i = c.1 i)

theorem price_bound_from_representatives (s : Profile n) (α : ℝ≥0) (hne : IsNashEquilibrium α s)
    (hk : 0 < k + 1) (e : Embedding (graph s) (k + 1)) (num den : ℕ)
    (hSym : Symmetries (k + 1)) (certs : Representatives (k + 1))
    (hChecked : ∀ c ∈ certs, Checks c.1 c.2 num den)
    (hCoverage : (vectors [false, true] (k + 1)).all (covered certs) = true) :
    (den : ℝ) * α ≤ (num : ℝ) * (n : ℝ) := by
  obtain ⟨o, ho⟩ := exists_orientation s e
  have hMem := mem_vectors [false, true] (by intro b; cases b <;> simp) o
  have hc := List.all_eq_true.mp hCoverage o hMem
  unfold covered at hc
  obtain ⟨a, _, ha⟩ := List.any_eq_true.mp hc
  obtain ⟨rev, _, hr⟩ := List.any_eq_true.mp ha
  obtain ⟨c, hcMem, hEq⟩ := List.any_eq_true.mp hr
  have he : reorient o a rev = c.1 := funext (of_decide_eq_true hEq)
  have hModel := models_reindex s e hSym ho a rev
  rw [he] at hModel
  exact price_bound_for_orientation s α hne hk (e.reindex hSym a rev) num den c.1 hModel c.2
    (hChecked c hcMem)

end TreeConjecture.CycleCertificate
