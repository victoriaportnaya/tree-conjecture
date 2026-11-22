import Lean.Elab.Tactic.Omega

set_option warningAsError true

namespace TreeConjecture

/-- A square has four deletion penalties for a fixed destination.

A positive penalty requires the owner to be one level above the other
endpoint, with its second cycle neighbor no closer to the destination. -/
theorem square_penalty_sum {a b c d p q r s : Nat}
    (hp : p ≤ 2) (hq : q ≤ 2) (hr : r ≤ 2) (hs : s ≤ 2)
    (hab : a ≤ b + 1 ∧ b ≤ a + 1) (hbc : b ≤ c + 1 ∧ c ≤ b + 1)
    (hcd : c ≤ d + 1 ∧ d ≤ c + 1) (hda : d ≤ a + 1 ∧ a ≤ d + 1)
    (hp_pos : 0 < p → (a = b + 1 ∧ a ≤ d) ∨ (b = a + 1 ∧ b ≤ c))
    (hq_pos : 0 < q → (b = c + 1 ∧ b ≤ a) ∨ (c = b + 1 ∧ c ≤ d))
    (hr_pos : 0 < r → (c = d + 1 ∧ c ≤ b) ∨ (d = c + 1 ∧ d ≤ a))
    (hs_pos : 0 < s → (d = a + 1 ∧ d ≤ c) ∨ (a = d + 1 ∧ a ≤ b)) :
    p + q + r + s ≤ 4 := by
  have hp' : p = 0 ∨ (a = b + 1 ∧ a ≤ d) ∨ (b = a + 1 ∧ b ≤ c) :=
    if h : 0 < p then Or.inr (hp_pos h) else Or.inl (by omega)
  have hq' : q = 0 ∨ (b = c + 1 ∧ b ≤ a) ∨ (c = b + 1 ∧ c ≤ d) :=
    if h : 0 < q then Or.inr (hq_pos h) else Or.inl (by omega)
  have hr' : r = 0 ∨ (c = d + 1 ∧ c ≤ b) ∨ (d = c + 1 ∧ d ≤ a) :=
    if h : 0 < r then Or.inr (hr_pos h) else Or.inl (by omega)
  have hs' : s = 0 ∨ (d = a + 1 ∧ d ≤ c) ∨ (a = d + 1 ∧ a ≤ b) :=
    if h : 0 < s then Or.inr (hs_pos h) else Or.inl (by omega)
  omega

/-- A pentagon edge with the displayed target and following component
weights incurs deletion penalty `3 * target + next`. An unprofitable
forward swap requires `next ≤ target`. -/
private def StablePentagonEdge (target next penalty : Nat) : Prop :=
  next ≤ target ∧ penalty = 3 * target + next

/-- Under the weighted pentagon swap inequalities, some owned edge
has deletion penalty at most the total weight minus one. -/
theorem pentagon_deletion_bound {a b c d e p q r s t : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hab : StablePentagonEdge b c p ∨ StablePentagonEdge a e p)
    (hbc : StablePentagonEdge c d q ∨ StablePentagonEdge b a q)
    (hcd : StablePentagonEdge d e r ∨ StablePentagonEdge c b r)
    (hde : StablePentagonEdge e a s ∨ StablePentagonEdge d c s)
    (hea : StablePentagonEdge a b t ∨ StablePentagonEdge e d t) :
    p + 1 ≤ a + b + c + d + e ∨ q + 1 ≤ a + b + c + d + e ∨
      r + 1 ≤ a + b + c + d + e ∨ s + 1 ≤ a + b + c + d + e ∨
      t + 1 ≤ a + b + c + d + e := by
  simp only [StablePentagonEdge] at hab hbc hcd hde hea
  omega

#print axioms square_penalty_sum
#print axioms pentagon_deletion_bound

end TreeConjecture
