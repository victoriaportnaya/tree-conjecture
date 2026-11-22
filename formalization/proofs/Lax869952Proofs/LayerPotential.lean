import Lax869952Proofs.RetainedRoutes

set_option warningAsError true

namespace Lax869952Proofs

open scoped BigOperators

/-- Neighbor counts and purchases at one distance layer. Counts are integers
because the potential is signed. -/
structure LayerCounts where
  earlier : ℤ
  later : ℤ
  same : ℤ
  buyEarlier : ℤ
  buyLater : ℤ
  buySame : ℤ

namespace LayerCounts

def Valid (c : LayerCounts) : Prop :=
  0 ≤ c.earlier ∧ 0 ≤ c.later ∧ 0 ≤ c.same ∧
  0 ≤ c.buyEarlier ∧ 0 ≤ c.buyLater ∧ 0 ≤ c.buySame ∧
  c.buyEarlier + c.buyLater + c.buySame ≤ 1 ∧
  (c.earlier ≤ 1 → c.buyEarlier = 0) ∧
  (c.later = 0 → c.buyLater = 0) ∧
  (c.same = 0 → c.buySame = 0)

def incoming (c : LayerCounts) : ℤ :=
  if 2 ≤ c.earlier then c.earlier - c.buyEarlier else 0

def degree (c : LayerCounts) : ℤ := c.earlier + c.later + c.same

def potential (c : LayerCounts) : ℤ := 2 * c.earlier - 3 * c.incoming

def defect (c : LayerCounts) : ℤ :=
  4 * c.later - 6 * c.buyLater - c.potential + 2 * c.same - 4 * c.buySame

/-- In minimum degree three, a negative contribution requires a particular
cubic vertex incident to an equal-layer edge. -/
theorem cubic_pattern_of_negative (c : LayerCounts) (h : c.Valid)
    (hd : 3 ≤ c.degree) (hneg : c.defect < 0) :
    c.earlier = 1 ∧
      (c.later = 1 ∧ c.same = 1 ∧ c.buyLater = 1 ∨
        c.later = 0 ∧ c.same = 2 ∧ c.buySame = 1) := by
  rcases c with ⟨p, q, l, a, b, t⟩
  rcases h with ⟨hp, hq, hl, ha, hb, ht, hcap, ha0, hb0, ht0⟩
  dsimp [degree, defect, potential, incoming] at *
  split at hneg <;> omega

/-- At the earliest occupied layer of a subgraph of minimum degree three,
every vertex contributes strictly positively. -/
theorem defect_pos_of_no_earlier (c : LayerCounts) (h : c.Valid)
    (hd : 3 ≤ c.degree) (hp : c.earlier = 0) : 0 < c.defect := by
  rcases c with ⟨p, q, l, a, b, t⟩
  rcases h with ⟨hp', hq, hl, ha, hb, ht, hcap, ha0, hb0, ht0⟩
  dsimp [degree, defect, potential, incoming] at *
  split <;> omega

end LayerCounts

/-- A strictly positive contribution cannot be absorbed if all other
contributions are nonnegative and both ends of the layer calculation vanish. -/
theorem layer_potential_obstruction (Φ defect : ℕ → ℤ) (top start : ℕ)
    (hTop : Φ top = 0) (hBase : Φ 0 = 0) (hStart : start < top)
    (hStep : ∀ i, 2 * Φ (i + 1) - Φ i = defect i)
    (hPos : 0 < defect start) : ∃ i, defect i < 0 := by
  by_contra! all
  have hNonneg (i : ℕ) : 0 ≤ Φ i := by
    induction i with
    | zero => omega
    | succ i ih =>
      have step := hStep i
      have sign := all i
      omega
  have hAfter (i : ℕ) (hi : start < i) : 0 < Φ i := by
    induction i with
    | zero => omega
    | succ i ih =>
      have step := hStep i
      have nonneg := hNonneg i
      by_cases hi' : start < i
      · have prev := ih hi'
        have sign := all i
        omega
      · have eq : i = start := by omega
        subst i
        omega
  have last := hAfter top hStart
  omega

end Lax869952Proofs
