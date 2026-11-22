import Lax869952Proofs.LayerPotential

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph
open scoped BigOperators

namespace RootedOwnership

variable {V : Type*} [Fintype V]

noncomputable section

variable (K : SimpleGraph V) (level : V → ℕ) (owns : V → V → Prop)

def earlier (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun u => K.Adj v u ∧ level u + 1 = level v

def later (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun u => K.Adj v u ∧ level v + 1 = level u

def same (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun u => K.Adj v u ∧ level u = level v

def boughtEarlier (v : V) : Finset V := by
  classical
  exact (earlier K level v).filter fun u => owns v u ∧ 2 ≤ (earlier K level v).card

def boughtLater (v : V) : Finset V := by
  classical
  exact (later K level v).filter fun u => owns v u ∧ 2 ≤ (earlier K level u).card

def boughtSame (v : V) : Finset V := by
  classical
  exact (same K level v).filter fun u => owns v u

def paidByEarlier (v : V) : Finset V := by
  classical
  exact (earlier K level v).filter fun u => owns u v ∧ 2 ≤ (earlier K level v).card

def inLayer (i : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun u => level u = i

@[simp] theorem mem_earlier {v u : V} :
    u ∈ earlier K level v ↔ K.Adj v u ∧ level u + 1 = level v := by
  classical
  simp [earlier]

@[simp] theorem mem_later {v u : V} :
    u ∈ later K level v ↔ K.Adj v u ∧ level v + 1 = level u := by
  classical
  simp [later]

@[simp] theorem mem_same {v u : V} :
    u ∈ same K level v ↔ K.Adj v u ∧ level u = level v := by
  classical
  simp [same]

def counts (v : V) : LayerCounts :=
  ⟨(earlier K level v).card, (later K level v).card, (same K level v).card,
    (boughtEarlier K level owns v).card, (boughtLater K level owns v).card,
    (boughtSame K level owns v).card⟩

omit [Fintype V] in
private theorem count_as_sum (f : Finset V) : (f.card : ℤ) = ∑ _x ∈ f, (1 : ℤ) := by
  simp

omit [Fintype V] in
private theorem incidence_comm (A B : Finset V) (P : V → V → Prop) [DecidableRel P] :
    (∑ u ∈ A, ((B.filter (P u)).card : ℤ)) =
      ∑ v ∈ B, ((A.filter fun u => P u v).card : ℤ) := by
  simp_rw [count_as_sum, Finset.sum_filter]
  exact Finset.sum_comm

private theorem supported_incidence_comm (i j : ℕ) (P : V → V → Prop)
    [DecidableRel P] (support : ∀ u v, P u v → (level u = i ↔ level v = j)) :
    (∑ u ∈ inLayer level i, ((Finset.univ.filter (P u)).card : ℤ)) =
      ∑ v ∈ inLayer level j, ((Finset.univ.filter fun u => P u v).card : ℤ) := by
  classical
  have left (u : V) (hu : u ∈ inLayer level i) :
      (Finset.univ.filter (P u)) = (inLayer level j).filter (P u) := by
    have lev : level u = i := by simpa [inLayer] using hu
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, inLayer]
    exact ⟨fun h => ⟨(support u v h).mp lev, h⟩, And.right⟩
  have right (v : V) (hv : v ∈ inLayer level j) :
      (Finset.univ.filter fun u => P u v) = (inLayer level i).filter (fun u => P u v) := by
    have lev : level v = j := by simpa [inLayer] using hv
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, inLayer]
    exact ⟨fun h => ⟨(support u v h).mpr lev, h⟩, And.right⟩
  calc
    _ = ∑ u ∈ inLayer level i, (((inLayer level j).filter (P u)).card : ℤ) :=
      Finset.sum_congr rfl fun u hu => by rw [left u hu]
    _ = ∑ v ∈ inLayer level j, (((inLayer level i).filter fun u => P u v).card : ℤ) :=
      incidence_comm _ _ _
    _ = _ := Finset.sum_congr rfl fun v hv => by rw [right v hv]

private theorem later_sum (i : ℕ) :
    (∑ u ∈ inLayer level i, ((later K level u).card : ℤ)) =
      ∑ v ∈ inLayer level (i + 1), ((earlier K level v).card : ℤ) := by
  classical
  let P (u v : V) := K.Adj u v ∧ level u + 1 = level v
  have swapped := supported_incidence_comm level i (i + 1) P
    (fun _ _ h => by unfold P at h; omega)
  unfold later earlier
  simpa only [P, adj_comm (G := K)] using swapped

private theorem boughtLater_sum (i : ℕ) :
    (∑ u ∈ inLayer level i, ((boughtLater K level owns u).card : ℤ)) =
      ∑ v ∈ inLayer level (i + 1), ((paidByEarlier K level owns v).card : ℤ) := by
  classical
  let P (u v : V) := (K.Adj u v ∧ level u + 1 = level v) ∧
    owns u v ∧ 2 ≤ (earlier K level v).card
  have swapped := supported_incidence_comm level i (i + 1) P
    (fun _ _ h => by unfold P at h; omega)
  unfold boughtLater paidByEarlier later earlier
  simp only [Finset.filter_filter]
  simpa only [P, earlier, adj_comm (G := K), and_comm, and_left_comm] using swapped

variable (hOwner : ∀ {u v : V}, K.Adj u v →
  (owns u v ∧ ¬ owns v u) ∨ (owns v u ∧ ¬ owns u v))

omit [Fintype V] in
private theorem split_owned (A : Finset V) (P Q : V → Prop) [DecidablePred P]
    [DecidablePred Q] (exclusive : ∀ u ∈ A, (P u ∧ ¬ Q u) ∨ (Q u ∧ ¬ P u)) :
    (A.filter P).card + (A.filter Q).card = A.card := by
  classical
  have disj : Disjoint (A.filter P) (A.filter Q) := by
    refine Finset.disjoint_left.mpr fun u hu hv => ?_
    obtain ⟨hA, hP⟩ := Finset.mem_filter.mp hu
    have hQ := (Finset.mem_filter.mp hv).2
    exact (exclusive u hA).elim (fun h => h.2 hQ) (fun h => h.2 hP)
  have union : A.filter P ∪ A.filter Q = A := by
    ext u
    simp only [Finset.mem_union, Finset.mem_filter]
    exact ⟨fun h => h.elim And.left And.left, fun h =>
      (exclusive u h).elim (fun hP => Or.inl ⟨h, hP.1⟩) (fun hQ => Or.inr ⟨h, hQ.1⟩)⟩
  rw [← Finset.card_union_of_disjoint disj, union]

include hOwner in
private theorem incoming_eq_card (v : V) :
    (counts K level owns v).incoming = (paidByEarlier K level owns v).card := by
  classical
  by_cases large : 2 ≤ (earlier K level v).card
  · have balance := split_owned (earlier K level v) (owns v) (fun u => owns u v)
      (fun u hu => hOwner ((mem_earlier K level).mp hu).1)
    have hEq : ((earlier K level v).card : ℤ) =
        ((earlier K level v).filter (owns v)).card +
        ((earlier K level v).filter fun u => owns u v).card := by
      exact_mod_cast balance.symm
    dsimp [LayerCounts.incoming, counts]
    rw [if_pos (by exact_mod_cast large)]
    simp only [boughtEarlier, paidByEarlier, large, and_true]
    linarith
  · dsimp [LayerCounts.incoming, counts]
    unfold paidByEarlier
    simp only [large, and_false, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
    exact if_neg (by exact_mod_cast large)

include hOwner in
private theorem same_sum (i : ℕ) :
    (∑ u ∈ inLayer level i, ((same K level u).card : ℤ)) =
      2 * ∑ u ∈ inLayer level i, ((boughtSame K level owns u).card : ℤ) := by
  classical
  let Q (u v : V) := K.Adj u v ∧ level v = level u ∧ owns u v
  let incomingSame (v : V) := (same K level v).filter fun u => owns u v
  have swapped := supported_incidence_comm level i i Q
    (fun _ _ h => by unfold Q at h; omega)
  have double :
      (∑ u ∈ inLayer level i, ((boughtSame K level owns u).card : ℤ)) =
        ∑ u ∈ inLayer level i, ((incomingSame u).card : ℤ) := by
    unfold boughtSame incomingSame same
    simp only [Finset.filter_filter]
    simpa only [Q, adj_comm (G := K), eq_comm, and_assoc] using swapped
  have term (v : V) : ((same K level v).card : ℤ) =
      ((boughtSame K level owns v).card : ℤ) + ((incomingSame v).card : ℤ) := by
    have h := split_owned (same K level v) (owns v) (fun u => owns u v)
      (fun u hu => hOwner ((mem_same K level).mp hu).1)
    exact_mod_cast h.symm
  simp_rw [term, Finset.sum_add_distrib, ← double]
  omega

include hOwner in
private theorem potential_step (i : ℕ) :
    2 * (∑ v ∈ inLayer level (i + 1), (counts K level owns v).potential) -
      (∑ v ∈ inLayer level i, (counts K level owns v).potential) =
      ∑ v ∈ inLayer level i, (counts K level owns v).defect := by
  classical
  have hLater : (∑ v ∈ inLayer level i, (counts K level owns v).later) =
      ∑ v ∈ inLayer level (i + 1), (counts K level owns v).earlier :=
    later_sum K level i
  have hBought : (∑ v ∈ inLayer level i, (counts K level owns v).buyLater) =
      ∑ v ∈ inLayer level (i + 1), (counts K level owns v).incoming := by
    change (∑ v ∈ inLayer level i, ((boughtLater K level owns v).card : ℤ)) = _
    simp_rw [incoming_eq_card K level owns hOwner]
    exact boughtLater_sum K level owns i
  have hSame : (∑ v ∈ inLayer level i, (counts K level owns v).same) =
      2 * ∑ v ∈ inLayer level i, (counts K level owns v).buySame :=
    same_sum K level owns hOwner i
  simp only [LayerCounts.defect, LayerCounts.potential, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith only [hLater, hBought, hSame]

variable (hStep : ∀ {u v : V}, K.Adj u v →
  level u ≤ level v + 1 ∧ level v ≤ level u + 1)

include hStep in
theorem counts_degree [DecidableRel K.Adj] (v : V) :
    (counts K level owns v).degree = K.degree v := by
  classical
  have cover : earlier K level v ∪ later K level v ∪ same K level v = K.neighborFinset v := by
    ext u
    simp only [earlier, later, same, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro adj
      have depths := hStep adj
      by_cases heq : level u = level v
      · exact Or.inr ⟨adj, heq⟩
      · by_cases hless : level u < level v
        · exact Or.inl (Or.inl ⟨adj, by omega⟩)
        · exact Or.inl (Or.inr ⟨adj, by omega⟩)
  have disjNear : Disjoint (earlier K level v) (later K level v) := by
    apply Finset.disjoint_left.mpr
    intro u he hl
    have e := ((mem_earlier K level).mp he).2
    have l := ((mem_later K level).mp hl).2
    omega
  have disjSame : Disjoint (earlier K level v ∪ later K level v) (same K level v) := by
    apply Finset.disjoint_left.mpr
    intro u he hs
    have eq := ((mem_same K level).mp hs).2
    rcases Finset.mem_union.mp he with h | h
    · have e := ((mem_earlier K level).mp h).2
      omega
    · have l := ((mem_later K level).mp h).2
      omega
  have card := congrArg Finset.card cover
  rw [Finset.card_union_of_disjoint disjSame, Finset.card_union_of_disjoint disjNear,
    SimpleGraph.card_neighborFinset_eq_degree] at card
  dsimp [LayerCounts.degree, counts]
  exact_mod_cast card

private theorem valid_counts (v : V)
    (capacity : (boughtEarlier K level owns v).card +
      (boughtLater K level owns v).card + (boughtSame K level owns v).card ≤ 1) :
    (counts K level owns v).Valid := by
  classical
  dsimp [LayerCounts.Valid, counts]
  refine ⟨by positivity, by positivity, by positivity, by positivity, by positivity,
    by positivity, by exact_mod_cast capacity, ?_, ?_, ?_⟩
  · intro small
    have notLarge : ¬ 2 ≤ (earlier K level v).card := by exact_mod_cast (by omega :
      ¬ (2 : ℤ) ≤ (earlier K level v).card)
    simp [boughtEarlier, notLarge]
  · intro eq
    have empty : later K level v = ∅ :=
      Finset.card_eq_zero.mp (by exact_mod_cast eq)
    simp [boughtLater, empty]
  · intro eq
    have empty : same K level v = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast eq)
    simp [boughtSame, empty]

include hOwner hStep in
/-- If every vertex in a nonempty finite graph has degree at least three,
one-purchase capacity across distance layers forces a specific cubic
vertex on an equal-layer edge. The levels need not be intrinsic distances. -/
theorem exists_cubic_pattern [Nonempty V] [DecidableRel K.Adj]
    (hMin : ∀ v, 3 ≤ K.degree v)
    (capacity : ∀ v, (boughtEarlier K level owns v).card +
      (boughtLater K level owns v).card + (boughtSame K level owns v).card ≤ 1) :
    ∃ v, (counts K level owns v).earlier = 1 ∧
      ((counts K level owns v).later = 1 ∧ (counts K level owns v).same = 1 ∧
        (counts K level owns v).buyLater = 1 ∨
       (counts K level owns v).later = 0 ∧ (counts K level owns v).same = 2 ∧
        (counts K level owns v).buySame = 1) := by
  classical
  let Φ (i : ℕ) := ∑ v ∈ inLayer level i, (counts K level owns v).potential
  let delta (i : ℕ) := ∑ v ∈ inLayer level i, (counts K level owns v).defect
  obtain ⟨x, _, least⟩ := Finset.exists_min_image Finset.univ level Finset.univ_nonempty
  obtain ⟨y, _, greatest⟩ := Finset.exists_max_image Finset.univ level Finset.univ_nonempty
  have early {i : ℕ} {v : V} (hv : level v = i) (minimal : ∀ u, i ≤ level u) :
      earlier K level v = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have e := ((mem_earlier K level).mp hu).2
    have low := minimal u
    omega
  have base : Φ 0 = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    have hl : level v = 0 := by simpa [inLayer] using hv
    simp [LayerCounts.potential, LayerCounts.incoming, counts, early hl (fun _ => Nat.zero_le _)]
  have last : Φ (level y + 1) = 0 := by
    have empty : inLayer level (level y + 1) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have eq : level v = level y + 1 := by simpa [inLayer] using hv
      have hy := greatest v (Finset.mem_univ v)
      omega
    simp [Φ, empty]
  have hDegree (v : V) : 3 ≤ (counts K level owns v).degree := by
    rw [counts_degree K level owns hStep v]
    exact_mod_cast hMin v
  have positive : 0 < delta (level x) := by
    have hEach (v : V) (hv : v ∈ inLayer level (level x)) :
        0 < (counts K level owns v).defect := by
      have hl : level v = level x := by simpa [inLayer] using hv
      exact LayerCounts.defect_pos_of_no_earlier _ (valid_counts K level owns v (capacity v))
        (hDegree v) (by simp [counts, early hl (fun u => least u (Finset.mem_univ u))])
    have hx : x ∈ inLayer level (level x) := by simp [inLayer]
    exact (hEach x hx).trans_le (Finset.single_le_sum (fun v hv => (hEach v hv).le) hx)
  have within : level x < level y + 1 := Nat.lt_succ_of_le (greatest x (Finset.mem_univ x))
  obtain ⟨i, hneg⟩ := layer_potential_obstruction Φ delta (level y + 1) (level x)
    last base within (potential_step K level owns hOwner) positive
  have someNeg : ∃ v ∈ inLayer level i, (counts K level owns v).defect < 0 := by
    by_contra! no
    exact not_lt_of_ge (Finset.sum_nonneg no) hneg
  obtain ⟨v, _, hv⟩ := someNeg
  exact ⟨v, LayerCounts.cubic_pattern_of_negative _ (valid_counts K level owns v (capacity v))
    (hDegree v) hv⟩

end

end RootedOwnership

end Lax869952Proofs
