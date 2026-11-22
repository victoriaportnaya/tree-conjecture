/- The finite cost and ownership lemmas adapt Lax899194Proofs.Costs and
   Lax899194Proofs.Ownership from lax-899194 (Apache-2.0). -/
import Lax869952.NashEquilibrium
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic.Linarith

set_option warningAsError true

namespace Lax869952Proofs

open Lax869952.NetworkCreationGame Lax869952.PlayerCost Lax869952.NashEquilibrium
open scoped BigOperators NNReal ENNReal

variable {n : ℕ}

def treeAt (price : ℝ≥0) : Prop :=
  ∀ s : Profile n, IsNashEquilibrium price s → (graph s).IsTree

def conjecture : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ price : ℝ≥0, (n : ℝ≥0) < price → treeAt (n := n) price

def dippelVettaStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ price : ℝ≥0, 2 * (n : ℝ≥0) < price → treeAt (n := n) price

noncomputable def starDeviation (s : Profile n) (i : Fin n) : Profile n :=
  fun j => ⟨if j = i then {j}ᶜ else (s j).val, by
    split_ifs <;> simp [(s j).property]⟩

lemma starDeviation_other (s : Profile n) (i j : Fin n) (hji : j ≠ i) :
    starDeviation s i j = s j := by
  apply Subtype.ext
  simp [starDeviation, hji]

lemma starDeviation_connected (s : Profile n) (i : Fin n) :
    (graph (starDeviation s i)).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨i, fun j => ?_⟩
  by_cases h : j = i
  · subst j
    exact ⟨.nil⟩
  · have hadj : (graph (starDeviation s i)).Adj i j := Or.inl (by simp [starDeviation, h])
    exact ⟨.cons hadj .nil⟩

noncomputable def distanceSum (G : SimpleGraph (Fin n)) (i : Fin n) : ℝ :=
  ∑ j : Fin n, (G.dist i j : ℝ)

noncomputable def finiteCost (α : ℝ≥0) (s : Profile n) (i : Fin n) : ℝ :=
  (α : ℝ) * (s i).val.ncard + distanceSum (graph s) i

lemma distance_coe (G : SimpleGraph (Fin n)) (hG : G.Connected) (i j : Fin n) :
    (G.edist i j).toENNReal = (G.dist i j : ℝ≥0∞) := by
  rw [← (hG i j).coe_dist_eq_edist]
  simp

lemma cost_ne_top (α : ℝ≥0) (s : Profile n) (hs : (graph s).Connected)
    (i : Fin n) : playerCost α s i ≠ ⊤ := by
  unfold playerCost
  simp only [distance_coe _ hs, ENNReal.add_ne_top, ENNReal.sum_ne_top]
  constructor
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp)
  · simp

lemma cost_toReal (α : ℝ≥0) (s : Profile n) (hs : (graph s).Connected)
    (i : Fin n) : (playerCost α s i).toReal = finiteCost α s i := by
  unfold playerCost finiteCost distanceSum
  simp only [distance_coe _ hs]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp))
    (ENNReal.sum_ne_top.mpr (by simp))]
  rw [ENNReal.toReal_sum (by simp)]
  simp

/-- Every player can acquire a finite cost by linking to all other players. -/
theorem nash_connected (hn : 0 < n) (α : ℝ≥0) (s : Profile n)
    (hne : IsNashEquilibrium α s) : (graph s).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  let i : Fin n := ⟨0, hn⟩
  refine ⟨i, fun j => ?_⟩
  have hdeviation := hne i (starDeviation s i) (fun k hk => starDeviation_other s i k hk)
  have hfinite := cost_ne_top α _ (starDeviation_connected s i) i
  have hcost : playerCost α s i ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hdeviation (lt_top_iff_ne_top.mpr hfinite))
  unfold playerCost at hcost
  have hterm := (ENNReal.sum_ne_top.mp (ENNReal.add_ne_top.mp hcost).2) j (Finset.mem_univ j)
  by_contra h
  apply hterm
  rw [SimpleGraph.edist_eq_top_of_not_reachable h]
  simp

noncomputable def erasePurchase (s : Profile n) (i r : Fin n) : Profile n :=
  fun j => ⟨if j = i then (s j).val \ {r} else (s j).val, by
    split_ifs
    · exact fun h => (s j).property h.1
    · exact (s j).property⟩

lemma erasePurchase_other (s : Profile n) (i r j : Fin n) (hji : j ≠ i) :
    erasePurchase s i r j = s j := by
  apply Subtype.ext
  simp [erasePurchase, hji]

lemma erasePurchase_count (s : Profile n) (i r : Fin n) (hr : r ∈ (s i).val) :
    (erasePurchase s i r i).val.ncard + 1 = (s i).val.ncard := by
  simpa [erasePurchase] using Set.ncard_sdiff_singleton_add_one hr

lemma graph_erasePurchase_eq (s : Profile n) (i r : Fin n) (hr : i ∈ (s r).val) :
    graph (erasePurchase s i r) = graph s := by
  have hir : i ≠ r := by
    intro h
    subst r
    exact (s i).property hr
  apply SimpleGraph.ext
  funext a b
  apply propext
  change (b ∈ (erasePurchase s i r a).val ∨ a ∈ (erasePurchase s i r b).val) ↔
    (b ∈ (s a).val ∨ a ∈ (s b).val)
  by_cases ha : a = i
  · subst a
    by_cases hb : b = i
    · subst b
      simp [erasePurchase, (s i).property]
    · by_cases hbr : b = r
      · subst b
        simp [erasePurchase, hir.symm, hr]
      · simp [erasePurchase, hb, hbr]
  · by_cases hb : b = i
    · subst b
      by_cases har : a = r
      · subst a
        simp [erasePurchase, hir.symm, hr]
      · simp [erasePurchase, ha, har]
    · simp [erasePurchase, ha, hb]

lemma nash_finite_cost_le (α : ℝ≥0) (s t : Profile n)
    (hs : (graph s).Connected) (ht : (graph t).Connected) (hne : IsNashEquilibrium α s)
    (i : Fin n) (hchange : ∀ j : Fin n, j ≠ i → t j = s j) :
    finiteCost α s i ≤ finiteCost α t i := by
  rw [← cost_toReal α s hs i, ← cost_toReal α t ht i]
  exact ENNReal.toReal_mono (cost_ne_top α t ht i) (hne i t hchange)

/-- The distance cost increase from a connected one-edge deletion bounds the edge price. -/
theorem nash_deletion_bound (α : ℝ≥0) (s : Profile n)
    (hne : IsNashEquilibrium α s) {i r : Fin n} (hr : r ∈ (s i).val)
    (hconn : (graph (erasePurchase s i r)).Connected) :
    (α : ℝ) ≤ distanceSum (graph (erasePurchase s i r)) i - distanceSum (graph s) i := by
  have hs := nash_connected (Nat.zero_lt_of_lt i.isLt) α s hne
  have hc := nash_finite_cost_le α s (erasePurchase s i r) hs hconn hne i
    (fun j hj => erasePurchase_other s i r j hj)
  have hcount : ((erasePurchase s i r i).val.ncard : ℝ) + 1 = (s i).val.ncard := by
    exact_mod_cast erasePurchase_count s i r hr
  unfold finiteCost at hc
  rw [← hcount] at hc
  linarith [mul_add (α : ℝ) ((erasePurchase s i r i).val.ncard : ℝ) 1]

theorem nash_no_double_purchase (α : ℝ≥0) (hα : 0 < α) (s : Profile n)
    (hne : IsNashEquilibrium α s) {i r : Fin n} (hr : r ∈ (s i).val) :
    i ∉ (s r).val := by
  intro hi
  have he := graph_erasePurchase_eq s i r hi
  have ht : (graph (erasePurchase s i r)).Connected := by
    rw [he]
    exact nash_connected (Nat.zero_lt_of_lt i.isLt) α s hne
  have hb := nash_deletion_bound α s hne hr ht
  rw [he, sub_self] at hb
  exact (not_le_of_gt (by exact_mod_cast hα : (0 : ℝ) < α)) hb

/-- Final counting step of Dippel–Vetta with the structural input separated. -/
theorem degree_count_contradiction {outEdges rootDegree excess overlaps : ℕ}
    (hcount : rootDegree + excess = 2 * outEdges)
    (hcapacity : 2 * outEdges ≤ excess + overlaps) (hoverlap : overlaps < rootDegree) :
    False := by omega

#print axioms nash_connected
#print axioms nash_deletion_bound
#print axioms nash_no_double_purchase
#print axioms degree_count_contradiction

end Lax869952Proofs
