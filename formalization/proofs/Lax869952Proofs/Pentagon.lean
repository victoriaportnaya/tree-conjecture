import Lax869952Proofs.PentagonData
import Lax869952Proofs.CycleCertificateCheck

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

namespace CycleCertificate

def Embedding.of_isometric_cycle {n k : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n}
    (p : G.Walk u u) (hp : IsometricCycle p) (hk : p.length = k) : Embedding G k where
  vertex := ⟨fun i => p.getVert i.val, by
    intro i j he
    apply Fin.ext
    exact hp.1.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) he⟩
  adjacent i := by
    change G.Adj (p.getVert i.val) (p.getVert (next i).val)
    have hi : i.val < p.length := by omega
    have hNext : p.getVert (next i).val = p.getVert (i.val + 1) := by
      change p.getVert ((i.val + 1) % k) = _
      by_cases h : i.val + 1 < k
      · rw [Nat.mod_eq_of_lt h]
      · have he : i.val + 1 = k := by omega
        rw [he, Nat.mod_self, ← hk, Walk.getVert_length, Walk.getVert_zero]
    rw [hNext]
    exact p.adj_getVert_succ hi
  isometric i j := by
    change G.dist (p.getVert i.val) (p.getVert j.val) = cycleDistance i j
    have hDistances := hp.2 p hp.1 (List.Perm.refl _)
    by_cases h : i.val ≤ j.val
    · rw [hDistances i.val j.val h (by omega)]
      simp only [cycleDistance, max_eq_right h, min_eq_left h, hk]
    · have h' : j.val ≤ i.val := by omega
      rw [dist_comm, hDistances j.val i.val h' (by omega)]
      simp only [cycleDistance, max_eq_left h', min_eq_right h', hk]

private theorem fin_five_cases (i : Fin 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  have h : ∀ i : Fin 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
  exact h i

-- Separate the closed computations so Lean can release its reduction cache
-- before checking the next group of four orientations.
section
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem pentagon_prefix_0 (b3 b4 : Bool) :
    let o : Orientation 5 := ![false, false, false, b3, b4]
    checkMoves o (pentagonCertificate o) 6 7 = true := by
  cases b3 <;> cases b4 <;> decide

private theorem pentagon_prefix_1 (b3 b4 : Bool) :
    let o : Orientation 5 := ![false, false, true, b3, b4]
    checkMoves o (pentagonCertificate o) 6 7 = true := by
  cases b3 <;> cases b4 <;> decide

private theorem pentagon_prefix_2 (b3 b4 : Bool) :
    let o : Orientation 5 := ![false, true, false, b3, b4]
    checkMoves o (pentagonCertificate o) 6 7 = true := by
  cases b3 <;> cases b4 <;> decide

private theorem pentagon_prefix_3 (b3 b4 : Bool) :
    let o : Orientation 5 := ![false, true, true, b3, b4]
    checkMoves o (pentagonCertificate o) 6 7 = true := by
  cases b3 <;> cases b4 <;> decide

private theorem pentagon_prefix_4 (b3 b4 : Bool) :
    let o : Orientation 5 := ![true, false, false, b3, b4]
    checkMoves o (pentagonCertificate o) 6 7 = true := by
  cases b3 <;> cases b4 <;> decide

private theorem pentagon_prefix_5 (b3 b4 : Bool) :
    let o : Orientation 5 := ![true, false, true, b3, b4]
    checkMoves o (pentagonCertificate o) 6 7 = true := by
  cases b3 <;> cases b4 <;> decide

private theorem pentagon_prefix_6 (b3 b4 : Bool) :
    let o : Orientation 5 := ![true, true, false, b3, b4]
    checkMoves o (pentagonCertificate o) 6 7 = true := by
  cases b3 <;> cases b4 <;> decide

private theorem pentagon_prefix_7 (b3 b4 : Bool) :
    let o : Orientation 5 := ![true, true, true, b3, b4]
    checkMoves o (pentagonCertificate o) 6 7 = true := by
  cases b3 <;> cases b4 <;> decide

end

private theorem pentagonCertificate_checked (o : Orientation 5) :
    Checks o (pentagonCertificate o) 6 7 := by
  apply checks_of_checkMoves
  have hVec : ![o 0, o 1, o 2, o 3, o 4] = o := by
    funext i
    rcases fin_five_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [← hVec]
  generalize o 0 = b0, o 1 = b1, o 2 = b2, o 3 = b3, o 4 = b4
  cases b0 <;> cases b1 <;> cases b2
  · exact pentagon_prefix_0 b3 b4
  · exact pentagon_prefix_1 b3 b4
  · exact pentagon_prefix_2 b3 b4
  · exact pentagon_prefix_3 b3 b4
  · exact pentagon_prefix_4 b3 b4
  · exact pentagon_prefix_5 b3 b4
  · exact pentagon_prefix_6 b3 b4
  · exact pentagon_prefix_7 b3 b4

#print axioms pentagonCertificate_checked

end CycleCertificate

/-- Every isometric pentagon at equilibrium bounds the price by `6 * n / 7`,
irrespective of the purchases on the cycle or the graph outside it. -/
theorem nash_isometric_pentagon_price_bound {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {u : Fin n} (p : (graph s).Walk u u)
    (hp : IsometricCycle p) (hlen : p.length = 5) :
    7 * (α : ℝ) ≤ 6 * (n : ℝ) := by
  simpa using CycleCertificate.price_bound s α hne (by decide : 0 < 5)
    (CycleCertificate.Embedding.of_isometric_cycle p hp hlen)
    6 7 CycleCertificate.pentagonCertificate CycleCertificate.pentagonCertificate_checked

/-- At the price in the Tree Conjecture, every equilibrium cycle has
length at least six. -/
theorem nash_cycle_length_ge_six {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    {u : Fin n} (p : (graph s).Walk u u) (hp : p.IsCycle) : 6 ≤ p.length := by
  have hPrice : ((n - 2 : ℕ) : ℝ≥0) < α := by
    exact (show ((n - 2 : ℕ) : ℝ≥0) ≤ (n : ℝ≥0) by exact_mod_cast Nat.sub_le n 2).trans_lt hα
  have hFive := nash_cycle_length_ge_five α s hPrice hne p hp
  by_contra hSix
  have hLen : p.length = 5 := by omega
  have hIso := globally_shortest_cycle_isometric p hp fun q hq =>
    hLen.symm ▸ nash_cycle_length_ge_five α s hPrice hne q hq
  have hBound := nash_isometric_pentagon_price_bound s α hne p hIso hLen
  have hAR : (n : ℝ) < α := by exact_mod_cast hα
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  linarith

theorem nash_tree_of_le_five_at_n {n : ℕ} (hn : 0 < n) (hsmall : n ≤ 5)
    (s : Profile n) (α : ℝ≥0) (hα : (n : ℝ≥0) < α)
    (hne : IsNashEquilibrium α s) : (graph s).IsTree := by
  refine ⟨nash_connected hn α s hne, ?_⟩
  intro u p hp
  have hMin := nash_cycle_length_ge_six s α hα hne p hp
  have hMax := hp.nodup_dropLast_support.length_le_card
  simp [Walk.length_support] at hMax
  omega

#print axioms nash_isometric_pentagon_price_bound
#print axioms nash_cycle_length_ge_six
#print axioms nash_tree_of_le_five_at_n

end Lax869952Proofs
