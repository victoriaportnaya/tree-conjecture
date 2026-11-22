import Lax869952Proofs.ThreadLengthBound

set_option warningAsError true

namespace Lax869952Proofs

open scoped BigOperators

/-- Exponential weight required by a thread of length at least five. -/
def threadCharge (length : ℕ) : ℕ := if 5 ≤ length then 2 ^ (length - 3) else 0

private theorem threadCharge_affine (length : ℕ) : 8 * length ≤ threadCharge length + 40 := by
  by_cases small : length < 7
  · have cases : length = 0 ∨ length = 1 ∨ length = 2 ∨ length = 3 ∨
        length = 4 ∨ length = 5 ∨ length = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have exp (d : ℕ) : 8 * d + 16 ≤ 2 ^ (d + 4) := by
      induction d with
      | zero => decide
      | succ d ih =>
        rw [show d + 1 + 4 = d + 4 + 1 by omega, pow_succ]
        omega
    have h := exp (length - 7)
    have hl : 5 ≤ length := by omega
    rw [show length - 7 + 4 = length - 3 by omega] at h
    unfold threadCharge
    rw [if_pos hl]
    omega

/-- Summing the local price inequalities charges the disjoint thread
suffixes against one common budget. -/
theorem thread_cycle_charge_bound {ι : Type*} [Fintype ι]
    (length suffixMass lastMass : ι → ℕ) (c n : ℕ) (α : ℝ)
    (cycleLength : 3 ≤ c) (budget : (∑ i, suffixMass i) ≤ n)
    (tail : ∀ i, 5 ≤ length i → threadCharge (length i) * lastMass i ≤ suffixMass i)
    (price : ∀ i, 5 ≤ length i → α ≤ 2 * ((c : ℝ) - 3) * (lastMass i : ℝ)) :
    α * (∑ i, (threadCharge (length i) : ℝ)) ≤ 2 * ((c : ℝ) - 3) * n := by
  have nonneg : (0 : ℝ) ≤ 2 * ((c : ℝ) - 3) := by
    have h : (3 : ℝ) ≤ c := by exact_mod_cast cycleLength
    linarith
  have column (i : ι) : α * (threadCharge (length i) : ℝ) ≤
      2 * ((c : ℝ) - 3) * (suffixMass i : ℝ) := by
    by_cases long : 5 ≤ length i
    · have localPrice := mul_le_mul_of_nonneg_right (price i long)
        (Nat.cast_nonneg (threadCharge (length i)) : (0 : ℝ) ≤ _)
      have localTail : (threadCharge (length i) : ℝ) * (lastMass i : ℝ) ≤ suffixMass i := by
        exact_mod_cast tail i long
      have useWeight := mul_le_mul_of_nonneg_left localTail nonneg
      nlinarith only [localPrice, useWeight]
    · simp only [threadCharge, if_neg long, Nat.cast_zero, mul_zero]
      exact mul_nonneg nonneg (Nat.cast_nonneg _)
  have budgetReal : (∑ i, (suffixMass i : ℝ)) ≤ n := by exact_mod_cast budget
  rw [Finset.mul_sum]
  apply (Finset.sum_le_sum fun i _ => column i).trans
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left budgetReal nonneg

/-- At price above the order, the total length of a lifted cycle is
strictly less than twenty thirds of its number of core edges minus one. -/
theorem thread_cycle_length_bound {ι : Type*} [Fintype ι]
    (length suffixMass lastMass : ι → ℕ) (c n : ℕ) (α : ℝ)
    (cycleLength : 4 ≤ c) (sumLength : (∑ i, length i) = c)
    (high : (n : ℝ) < α) (budget : (∑ i, suffixMass i) ≤ n)
    (tail : ∀ i, 5 ≤ length i → threadCharge (length i) * lastMass i ≤ suffixMass i)
    (price : ∀ i, 5 ≤ length i → α ≤ 2 * ((c : ℝ) - 3) * (lastMass i : ℝ)) :
    6 * (c + 1) < 40 * Fintype.card ι := by
  let f (i : ι) := (threadCharge (length i) : ℝ)
  have charges := thread_cycle_charge_bound length suffixMass lastMass c n α
    (by omega) budget tail price
  change α * (∑ i, f i) ≤ 2 * ((c : ℝ) - 3) * n at charges
  have cReal : (4 : ℝ) ≤ c := by exact_mod_cast cycleLength
  have alphaPos : 0 < α := lt_of_le_of_lt (Nat.cast_nonneg _) high
  have smaller : (∑ i, f i) < 2 * ((c : ℝ) - 3) := by
    by_contra! no
    have h1 := mul_le_mul_of_nonneg_left no alphaPos.le
    have h2 := mul_lt_mul_of_pos_right high (show 0 < 2 * ((c : ℝ) - 3) by linarith)
    nlinarith only [h1, h2, charges]
  have affine (i : ι) : 8 * (length i : ℝ) ≤ f i + 40 := by
    dsimp [f]
    exact_mod_cast threadCharge_affine (length i)
  have lower := Finset.sum_le_sum (s := Finset.univ) (fun i _ => affine i)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at lower
  have cSum : (∑ i, (length i : ℝ)) = c := by exact_mod_cast sumLength
  rw [cSum] at lower
  have result : (6 : ℝ) * ((c : ℝ) + 1) < 40 * (Fintype.card ι : ℝ) := by
    linarith
  exact_mod_cast result

#print axioms thread_cycle_length_bound

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

/-- A cycle expressed as a family of degree-two paths obeys the joint
length bound. The supplied paths have disjoint interior suffixes, their
lengths add to the cycle length, and their charged vertices lie on it. -/
theorem nash_block_cycle_of_thread_paths_length_bound {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x r : Fin n} (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {u}, (c : (graph s).Walk u u) → c.IsCycle → 8 ≤ c.length)
    (c : (blockGraph (graph s) S).Walk r r) (hc : c.IsCycle)
    {ι : Type*} [Fintype ι] (a b : ι → Fin n)
    (p : ∀ i, DegreeTwoBlockPath (graph s) S x (a i) (b i))
    (distinct : ∀ i, a i ≠ b i)
    (near : ∀ i, (graph s).dist (a i) x ≤ (graph s).dist (b i) x)
    (sumLength : (∑ i, (p i).walk.length) = c.length)
    (onCycle : ∀ i, 5 ≤ (p i).walk.length →
      (p i).walk.getVert ((p i).walk.length - 1) ∈ c.support)
    (disjoint : ∀ i j, i ≠ j → Disjoint
      ((Finset.Ico 2 (p i).walk.length).image (p i).walk.getVert)
      ((Finset.Ico 2 (p j).walk.length).image (p j).walk.getVert)) :
    6 * (c.length + 1) < 40 * Fintype.card ι := by
  classical
  let len (i : ι) := (p i).walk.length
  let mass (z : Fin n) := (blockAttachment (graph s) S z).card
  let suffix (i : ι) := (Finset.Ico 2 (len i)).image (p i).walk.getVert
  let w (i : ι) := ∑ z ∈ suffix i, mass z
  let last (i : ι) := mass ((p i).walk.getVert (len i - 1))
  have hG := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  have pairwise : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint suffix :=
    fun i _ j _ h => disjoint i j h
  have budget : (∑ i, w i) ≤ n := by
    change (∑ i, ∑ z ∈ suffix i, mass z) ≤ n
    rw [← Finset.sum_biUnion pairwise]
    calc
      _ ≤ ∑ z ∈ S, mass z := by
        apply Finset.sum_le_sum_of_subset
        intro z hz
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
        exact ((p i).walk.adj_getVert_succ (Finset.mem_Ico.mp hk).2).1
      _ = n := hS.sum_blockAttachment_card hG
  have cycleLength : 8 ≤ c.length := by
    simpa only [Walk.length_mapLe] using girth (c.mapLe (blockGraph_le (graph s) S)) (hc.mapLe _)
  apply thread_cycle_length_bound len w last c.length n (α : ℝ)
    (cycleLength.trans' (by decide)) sumLength (by exact_mod_cast hα) budget
  · intro i long
    have used := nash_block_long_path_suffix_mass s α hne hS hx (distinct i) hMax girth
      (p i) long (near i)
    have eq : w i = ∑ j ∈ Finset.Ico 2 (len i), mass ((p i).walk.getVert j) := by
      apply Finset.sum_image
      intro j hj k hk he
      exact (p i).isPath.getVert_injOn (Finset.mem_Ico.mp hj).2.le
        (Finset.mem_Ico.mp hk).2.le he
    simpa only [threadCharge, if_pos long, len, last, eq] using used
  · intro i long
    let atTail := c.rotate _ (onCycle i long)
    have atTailCycle : atTail.IsCycle := hc.rotate (onCycle i long)
    have hLength : atTail.length = c.length := by
      simpa only [Walk.length_edges] using (c.rotate_edges _ (onCycle i long)).perm.length_eq
    have localPrice := nash_block_long_path_cycle_price_bound s α hα hne hS hx (distinct i)
      hMax girth (p i) long (near i) atTail atTailCycle
    simpa only [hLength, last, mass, len] using localPrice

#print axioms nash_block_cycle_of_thread_paths_length_bound

end Lax869952Proofs
