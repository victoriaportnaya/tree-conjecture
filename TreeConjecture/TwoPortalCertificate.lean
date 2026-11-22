import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic

set_option warningAsError true

namespace TreeConjecture.TwoPortalCertificate

/-- A deviation deletes all cycle purchases of its buyer and buys at most
one new edge. The distances have predecessor witnesses in the changed cycle. -/
structure Move where
  buyer : Fin 8
  target : Option (Fin 8)
  multiplicity : ℕ
  distance : Fin 8 → ℕ

def owns (o : ℕ) (u v : Fin 8) : Bool :=
  ((u.val + 1) % 8 == v.val && o.testBit u.val) ||
  ((v.val + 1) % 8 == u.val && !o.testBit v.val)

def adjacencyAfter (o : ℕ) (m : Move) (u v : Fin 8) : Bool :=
  let buys (a b : Fin 8) :=
    if a == m.buyer then m.target == some b else owns o a b
  buys u v || buys v u

def valid (o : ℕ) (m : Move) : Bool :=
  (m.target != some m.buyer) && (m.distance m.buyer == 0) &&
  (List.finRange 8).all (fun z =>
    decide (m.distance z ≤ 7) &&
    (z == m.buyer ||
      (List.finRange 8).any (fun y =>
        adjacencyAfter o m z y && m.distance y + 1 == m.distance z)))

def priceChange (o : ℕ) (m : Move) : ℤ :=
  (if m.target.isSome then 1 else 0) -
    (((List.finRange 8).filter (owns o m.buyer)).length : ℤ)

def originalDistance (i j : Fin 8) : ℕ :=
  min ((i.val + 8 - j.val) % 8) ((j.val + 8 - i.val) % 8)

/-- Columns 0–7 are cycle vertices. Columns 8–22 are external distance
labels, with portal distance difference clamped to the interval [-7,7]. -/
def columnDistance (d : Fin 8 → ℕ) (column : Fin 23) : ℕ :=
  if h : column.val < 8 then d ⟨column.val, h⟩
  else
    let j := column.val - 8
    min (d 0 + (j - 7)) (d 4 + (7 - j))

def distanceChange (m : Move) (column : Fin 23) : ℤ :=
  (columnDistance m.distance column : ℤ) -
    (columnDistance (originalDistance m.buyer) column : ℤ)

def combinedPrice (o : ℕ) (moves : List Move) : ℤ :=
  (moves.map fun m => (m.multiplicity : ℤ) * priceChange o m).sum

def combinedDistance (moves : List Move) (column : Fin 23) : ℤ :=
  (moves.map fun m => (m.multiplicity : ℤ) * distanceChange m column).sum

def check (o : ℕ) (moves : List Move) : Bool :=
  moves.all (valid o) &&
    decide (combinedPrice o moves < 0) &&
    (List.finRange 23).all (fun c => decide (combinedDistance moves c ≤ -combinedPrice o moves))

theorem checked_conditions {o : ℕ} {moves : List Move} (h : check o moves = true) :
    (∀ m ∈ moves, valid o m = true) ∧ combinedPrice o moves < 0 ∧
      ∀ column, combinedDistance moves column ≤ -combinedPrice o moves := by
  simp only [check, Bool.and_eq_true_iff] at h
  exact ⟨fun m hm => List.all_eq_true.mp h.1.1 m hm, of_decide_eq_true h.1.2,
    fun c => of_decide_eq_true (List.all_eq_true.mp h.2 c (List.mem_finRange c))⟩

end TreeConjecture.TwoPortalCertificate
