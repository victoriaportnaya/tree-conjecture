import TreeConjecture.Foundations

set_option warningAsError true

namespace TreeConjecture

open Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped BigOperators NNReal

open SimpleGraph in
private lemma level_le_of_walk {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (level : V → ℕ) (hedge : ∀ a b, G.Adj a b → level b ≤ level a + 1) :
    level v ≤ level u + p.length := by
  induction p with
  | nil => simp
  | @cons a b _ hab p ih =>
    have h := hedge a b hab
    simp only [Walk.length_cons]
    omega

open SimpleGraph in
/-- A distance labeling certificate consists of a zero label at the root,
unit edge differences, and a predecessor one level lower at each other vertex. -/
theorem connected_and_dist_eq_of_labels {V : Type*} (G : SimpleGraph V) (root : V)
    (level : V → ℕ) (hroot : level root = 0)
    (hedge : ∀ a b, G.Adj a b → level b ≤ level a + 1)
    (hpred : ∀ v ≠ root, ∃ u, G.Adj u v ∧ level v = level u + 1) :
    G.Connected ∧ ∀ v, G.dist root v = level v := by
  classical
  have routes : ∀ k v, level v = k → ∃ p : G.Walk root v, p.length = k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hk
      by_cases hv : v = root
      · subst v
        exact ⟨.nil, by simpa [hroot] using hk⟩
      · obtain ⟨u, huv, hstep⟩ := hpred v hv
        obtain ⟨p, hp⟩ := ih (level u) (by omega) u rfl
        exact ⟨p.concat huv, by rw [Walk.length_concat, hp]; omega⟩
  have hconn : G.Connected := (connected_iff_exists_forall_reachable _).mpr
    ⟨root, fun v => ⟨(routes (level v) v rfl).choose⟩⟩
  refine ⟨hconn, fun v => ?_⟩
  obtain ⟨p, hp⟩ := routes (level v) v rfl
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist root v
  have hlow := level_le_of_walk q level hedge
  rw [hroot, zero_add, hq] at hlow
  exact le_antisymm (hp ▸ SimpleGraph.dist_le p) hlow

private def profileFromFinsets {n : ℕ} (bought : Fin n → Finset (Fin n))
    (h : ∀ i, i ∉ bought i) : Profile n :=
  fun i => ⟨↑(bought i), h i⟩

private lemma finiteLabelCheck {n : ℕ} (bought : Fin n → Finset (Fin n))
    (h : ∀ i, i ∉ bought i) (root : Fin n) (level : Fin n → ℕ)
    (hroot : level root = 0)
    (hedge : ∀ a b, (b ∈ bought a ∨ a ∈ bought b) → level b ≤ level a + 1)
    (hpred : ∀ v ≠ root, ∃ u, (v ∈ bought u ∨ u ∈ bought v) ∧ level v = level u + 1) :
    (graph (profileFromFinsets bought h)).Connected ∧
      ∀ v, (graph (profileFromFinsets bought h)).dist root v = level v :=
  connected_and_dist_eq_of_labels _ root level hroot hedge hpred

private def eightBefore (i : Fin 8) : Finset (Fin 8) :=
  match i.val with
  | 2 => {6, 7}
  | 4 => {5, 7}
  | 5 => {3, 6}
  | 6 => {1}
  | 7 => {0}
  | _ => ∅

private def eightAfter (i : Fin 8) : Finset (Fin 8) :=
  if i = 2 then {5} else eightBefore i

private def beforeLabels (i : Fin 8) : ℕ := #[2, 2, 0, 3, 2, 2, 1, 1][i.val]!
private def afterLabels (i : Fin 8) : ℕ := #[4, 3, 0, 2, 2, 1, 2, 3][i.val]!

/-- The eight-player profile whose player 2 has a two-out, one-in deviation. -/
def eightPlayerProfile : Profile 8 := profileFromFinsets eightBefore (by decide)

private def eightDeviation : Profile 8 := profileFromFinsets eightAfter (by decide)

/-- Lean checks the eight-player witness against the original game model.
Player 2 saves one edge purchase, and its distance sum rises from 13 to 17. -/
theorem eight_player_multi_edge_refutation (α : ℝ≥0) (hα : 4 < α) :
    ¬ IsNashEquilibrium α eightPlayerProfile := by
  intro hne
  obtain ⟨hbConn, hbDist⟩ := finiteLabelCheck eightBefore (by decide) 2 beforeLabels
    (by decide) (by decide) (by decide)
  obtain ⟨haConn, haDist⟩ := finiteLabelCheck eightAfter (by decide) 2 afterLabels
    (by decide) (by decide) (by decide)
  change (graph eightPlayerProfile).Connected at hbConn
  change (graph eightDeviation).Connected at haConn
  change ∀ v, (graph eightPlayerProfile).dist 2 v = beforeLabels v at hbDist
  change ∀ v, (graph eightDeviation).dist 2 v = afterLabels v at haDist
  have hchange (i : Fin 8) (hi : i ≠ 2) : eightDeviation i = eightPlayerProfile i := by
    apply Subtype.ext
    simp [eightDeviation, eightPlayerProfile, profileFromFinsets, eightAfter, hi]
  have h := nash_finite_cost_le α eightPlayerProfile eightDeviation hbConn haConn hne 2 hchange
  have hbCount : ((eightPlayerProfile 2).val.ncard : ℝ) = 2 := by
    change (((eightBefore 2 : Finset (Fin 8)) : Set (Fin 8)).ncard : ℝ) = 2
    rw [Set.ncard_coe_finset]
    exact_mod_cast (show (eightBefore 2).card = 2 by decide)
  have haCount : ((eightDeviation 2).val.ncard : ℝ) = 1 := by
    change (((eightAfter 2 : Finset (Fin 8)) : Set (Fin 8)).ncard : ℝ) = 1
    rw [Set.ncard_coe_finset]
    exact_mod_cast (show (eightAfter 2).card = 1 by decide)
  have hbSum : distanceSum (graph eightPlayerProfile) 2 = 13 := by
    simp only [distanceSum, hbDist, ← Nat.cast_sum]
    exact_mod_cast (show (∑ v, beforeLabels v) = 13 by decide)
  have haSum : distanceSum (graph eightDeviation) 2 = 17 := by
    simp only [distanceSum, haDist, ← Nat.cast_sum]
    exact_mod_cast (show (∑ v, afterLabels v) = 17 by decide)
  have hprice : 4 < (α : ℝ) := by exact_mod_cast hα
  simp only [finiteCost, hbCount, haCount, hbSum, haSum] at h
  linarith

#print axioms connected_and_dist_eq_of_labels
#print axioms eight_player_multi_edge_refutation

end TreeConjecture
