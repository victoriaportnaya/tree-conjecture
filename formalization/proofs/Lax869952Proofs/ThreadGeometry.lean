import Lax869952Proofs.ThreadForest
import Lax869952Proofs.GirthDistances

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

/-- The distance recurrence along a degree-two path has the two-ended formula. -/
theorem threadDistance_eq_of_recurrence (D : ℕ → ℕ) (L : ℕ)
    (step : ∀ i < L, D i ≤ D (i + 1) + 1 ∧ D (i + 1) ≤ D i + 1)
    (inside : ∀ i, 0 < i → i < L → D i = min (D (i - 1)) (D (i + 1)) + 1)
    {i : ℕ} (hi : i ≤ L) : D i = threadDistance L (D 0) (D L) i := by
  have left (j : ℕ) (hj : j ≤ L) : D j ≤ j + D 0 := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hPrev := ih (by omega)
      have hNext := (step j (by omega)).2
      omega
  have right (k : ℕ) (hk : k ≤ L) : D (L - k) ≤ k + D L := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hPrev := ih (by omega)
      have hNext := (step (L - (k + 1)) (by omega)).1
      rw [show L - (k + 1) + 1 = L - k by omega] at hNext
      omega
  have hRight := right (L - i) (by omega)
  rw [show L - (L - i) = i by omega] at hRight
  refine le_antisymm (le_min (left i hi) hRight) ?_
  let F := threadDistance L (D 0) (D L)
  have stepF {j k : ℕ} (h₁ : j ≤ k + 1) (h₂ : L - j ≤ L - k + 1) :
      F j ≤ F k + 1 := by
    change min (j + D 0) (L - j + D L) ≤ min (k + D 0) (L - k + D L) + 1
    omega
  have lower : ∀ d j, D j = d → j ≤ L → F j ≤ d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro j hDj hj
      by_cases hZero : j = 0
      · subst j
        exact (min_le_left _ _).trans (by omega)
      by_cases hEnd : j = L
      · subst j
        exact (min_le_right _ _).trans (by omega)
      have hRec := inside j (by omega) (by omega)
      rcases le_total (D (j - 1)) (D (j + 1)) with h | h
      · rw [min_eq_left h] at hRec
        have hPrev := ih _ (by omega) (j - 1) rfl (by omega)
        exact (stepF (j := j) (k := j - 1) (by omega) (by omega)).trans (by omega)
      · rw [min_eq_right h] at hRec
        have hNext := ih _ (by omega) (j + 1) rfl (by omega)
        exact (stepF (j := j) (k := j + 1) (by omega) (by omega)).trans (by omega)
  exact lower (D i) i rfl hi

variable {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}
variable [DecidableRel (blockGraph G S).Adj] {A B x : Fin n}

/-- A block path has two-ended distances to every target outside its interior. -/
theorem block_path_dist_to_external_target (hS : IsBiconnectedBlock G S)
    (hG : G.Connected) (hx : x ∈ S) (p : (blockGraph G S).Walk A B) (hp : p.IsPath)
    (degree : ∀ i, 0 < i → i < p.length → (blockGraph G S).degree (p.getVert i) = 2)
    (avoid : ∀ i, 0 < i → i < p.length → p.getVert i ≠ x)
    {j : ℕ} (hj : j ≤ p.length) :
    G.dist (p.getVert j) x = threadDistance p.length (G.dist A x) (G.dist B x) j := by
  let D := fun i => G.dist (p.getVert i) x
  have step (i : ℕ) (hi : i < p.length) : D i ≤ D (i + 1) + 1 ∧ D (i + 1) ≤ D i + 1 := by
    have he := blockGraph_le G S (p.adj_getVert_succ hi)
    have h₁ : D i ≤ G.dist (p.getVert i) (p.getVert (i + 1)) + D (i + 1) :=
      hG.dist_triangle
    have h₂ : D (i + 1) ≤ G.dist (p.getVert (i + 1)) (p.getVert i) + D i :=
      hG.dist_triangle
    rw [dist_eq_one_iff_adj.mpr he] at h₁
    rw [dist_eq_one_iff_adj.mpr he.symm] at h₂
    omega
  have recurrence (i : ℕ) (hi : 0 < i) (hL : i < p.length) :
      D i = min (D (i - 1)) (D (i + 1)) + 1 := by
    have heL := p.adj_getVert_succ (i := i - 1) (by omega : i - 1 < p.length)
    rw [show i - 1 + 1 = i by omega] at heL
    have heR := p.adj_getVert_succ hL
    have hdifferent : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
      intro he
      have hn := hp.getVert_injOn
        (show i - 1 ∈ {k | k ≤ p.length} by simp; omega)
        (show i + 1 ∈ {k | k ≤ p.length} by simp; omega) he
      omega
    have hLdist := (step (i - 1) (by omega)).2
    rw [show i - 1 + 1 = i by omega] at hLdist
    have hRdist := (step i hL).1
    refine le_antisymm (by omega) ?_
    obtain ⟨q, hPath, hLen⟩ := hG.exists_path_of_dist (p.getVert i) x
    have hSupport := hS.path_support_subset heR.1 hx q hPath
    obtain ⟨v, hv, tail, rfl⟩ := Walk.exists_eq_cons_of_ne (avoid i hi hL) q
    have hvS : v ∈ S := hSupport v (by simp [Walk.support_cons])
    have hvBlock : (blockGraph G S).Adj (p.getVert i) v := ⟨heR.1, hvS, hv⟩
    have hNeighbor := neighbors_of_degree_two heL.symm heR hdifferent (degree i hi hL) hvBlock
    have ht := dist_le tail
    rw [Walk.length_cons] at hLen
    change tail.length + 1 = D i at hLen
    rcases hNeighbor with h | h
    · have hd : D (i - 1) = G.dist v x := congrArg (fun u => G.dist u x) h.symm
      have hLower := hd.le.trans ht
      omega
    · have hd : D (i + 1) = G.dist v x := congrArg (fun u => G.dist u x) h.symm
      have hLower := hd.le.trans ht
      omega
  simpa only [D, Walk.getVert_zero, Walk.getVert_length] using
    threadDistance_eq_of_recurrence D p.length step recurrence hj

/-- Any three-edge simple path is a geodesic under a girth bound of eight. -/
theorem dist_eq_three_of_girth_eight
    (girth : ∀ {v}, (q : G.Walk v v) → q.IsCycle → 8 ≤ q.length)
    {u v : Fin n} (q : G.Walk u v) (hq : q.IsPath) (hLength : q.length = 3) :
    G.dist u v = 3 := by
  have hUpper := dist_le q
  by_contra! h
  have hLong := girth_le_path_length_add_dist_of_not_shortest girth q hq (by omega)
  omega

/-- The indexed thread data associated to a simple path of internal degree two. -/
def DegreeTwoBlockThread.ofWalk (p : (blockGraph G S).Walk A B) (hp : p.IsPath)
    (degree : ∀ i, 0 < i → i < p.length → (blockGraph G S).degree (p.getVert i) = 2)
    (girth : ∀ {v}, (q : G.Walk v v) → q.IsCycle → 8 ≤ q.length) :
    DegreeTwoBlockThread G S A B p.length where
  vertex := p.getVert
  start_eq := p.getVert_zero
  end_eq := p.getVert_length
  adjacent := fun _ hi => p.adj_getVert_succ hi
  degree := degree
  three := by
    intro i hi
    let q := (p.drop i).take 3
    have hq : q.IsPath := (hp.drop i).take 3
    have hLength : q.length = 3 := by
      simp only [q, Walk.take_length, Walk.drop_length]
      exact min_eq_left (by omega)
    have h := dist_eq_three_of_girth_eight girth (q.mapLe (blockGraph_le G S)) (hq.mapLe _)
      (by simpa only [Walk.length_mapLe] using hLength)
    simpa only [Walk.drop_getVert] using h

/-- Long-thread data follow from a block path, a girth bound and an external target. -/
def LongBlockThreadTo.ofWalk (hS : IsBiconnectedBlock G S)
    (hG : G.Connected) (hx : x ∈ S)
    (girth : ∀ {v}, (q : G.Walk v v) → q.IsCycle → 8 ≤ q.length)
    (p : (blockGraph G S).Walk A B) (hp : p.IsPath) (hLong : 5 ≤ p.length)
    (degree : ∀ i, 0 < i → i < p.length → (blockGraph G S).degree (p.getVert i) = 2)
    (avoid : ∀ i, 0 < i → i < p.length → p.getVert i ≠ x) :
    LongBlockThreadTo G S x A B where
  length := p.length
  long := hLong
  thread := DegreeTwoBlockThread.ofWalk p hp degree girth
  metric := fun _ hi => block_path_dist_to_external_target hS hG hx p hp degree avoid hi
  boundary := by
    intro h
    have hA := hG.dist_eq_zero_iff.mp h
    rw [← hA, dist_comm]
    by_contra! hh
    have hShort : G.dist A B < (p.mapLe (blockGraph_le G S)).length := by
      rw [Walk.length_mapLe]
      omega
    have hg := girth_le_path_length_add_dist_of_not_shortest girth
      (p.mapLe (blockGraph_le G S)) (hp.mapLe _) hShort
    rw [Walk.length_mapLe] at hg
    omega

/-- Two distinct end segments into a vertex give a three-edge cross geodesic. -/
theorem DegreeTwoBlockThread.cross_distance {L M : ℕ}
    (P : DegreeTwoBlockThread G S A B L) {C : Fin n}
    (Q : DegreeTwoBlockThread G S C B M)
    (hL : 3 ≤ L) (hM : 3 ≤ M) (hG : G.Connected)
    (girth : ∀ {v}, (q : G.Walk v v) → q.IsCycle → 8 ≤ q.length)
    (hTail : P.vertex (L - 1) ≠ Q.vertex (M - 1))
    (hCross : P.vertex (L - 2) ≠ Q.vertex (M - 1)) :
    G.dist (P.vertex (L - 2)) (Q.vertex (M - 1)) = 3 := by
  have h₁ := blockGraph_le G S (P.penultimate_adj hL)
  have h₂ := blockGraph_le G S (P.last_adj hL)
  have h₃ := blockGraph_le G S (Q.last_adj hM).symm
  have hStart : P.vertex (L - 2) ≠ B := by
    intro he
    have hTwo := P.dist_penultimate_to_end hL hG
    rw [he, dist_self] at hTwo
    omega
  let p := Walk.cons h₁ (Walk.cons h₂ (Walk.cons h₃ Walk.nil))
  have hPath : p.IsPath := by
    simp [p, Walk.isPath_def, h₁.ne, h₂.ne, h₃.ne, hStart, hTail, hCross]
  exact dist_eq_three_of_girth_eight girth p hPath rfl

#print axioms block_path_dist_to_external_target
#print axioms LongBlockThreadTo.ofWalk
#print axioms DegreeTwoBlockThread.cross_distance

/-- A simple block path with degree-two interior avoiding the target. -/
structure DegreeTwoBlockPath {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    [DecidableRel (blockGraph G S).Adj] (x A B : Fin n) where
  walk : (blockGraph G S).Walk A B
  isPath : walk.IsPath
  degree : ∀ i, 0 < i → i < walk.length → (blockGraph G S).degree (walk.getVert i) = 2
  avoid : ∀ i, 0 < i → i < walk.length → walk.getVert i ≠ x

/-- A degree-two block path of length at least five. -/
structure LongDegreeTwoBlockPath {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    [DecidableRel (blockGraph G S).Adj] (x A B : Fin n)
    extends DegreeTwoBlockPath G S x A B where
  long : 5 ≤ walk.length

/-- Two penultimate purchases on paths with disjoint interiors give incompatible
bounds at their common endpoint. -/
theorem nash_block_no_two_penultimate_path_purchases {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B C : Fin n}
    (girth : ∀ {v}, (q : (graph s).Walk v v) → q.IsCycle → 8 ≤ q.length)
    (p : DegreeTwoBlockPath (graph s) S x A B)
    (q : DegreeTwoBlockPath (graph s) S x C B)
    (hP : 3 ≤ p.walk.length) (hQ : 3 ≤ q.walk.length)
    (hBuyP : p.walk.getVert (p.walk.length - 1) ∈ (s (p.walk.getVert (p.walk.length - 2))).val)
    (hBuyQ : q.walk.getVert (q.walk.length - 1) ∈ (s (q.walk.getVert (q.walk.length - 2))).val)
    (disjoint : ∀ i j, 0 < i → i < p.walk.length → 0 < j → j < q.walk.length →
      p.walk.getVert i ≠ q.walk.getVert j) : False := by
  have hG := nash_connected (Nat.zero_lt_of_lt B.isLt) α s hne
  let P := DegreeTwoBlockThread.ofWalk p.walk p.isPath p.degree girth
  let Q := DegreeTwoBlockThread.ofWalk q.walk q.isPath q.degree girth
  have tail : p.walk.getVert (p.walk.length - 1) ≠ q.walk.getVert (q.walk.length - 1) :=
    disjoint _ _ (by omega) (by omega) (by omega) (by omega)
  have crossP : p.walk.getVert (p.walk.length - 2) ≠ q.walk.getVert (q.walk.length - 1) :=
    disjoint _ _ (by omega) (by omega) (by omega) (by omega)
  have crossQ : q.walk.getVert (q.walk.length - 2) ≠ p.walk.getVert (p.walk.length - 1) :=
    (disjoint _ _ (by omega) (by omega) (by omega) (by omega)).symm
  exact nash_block_no_two_penultimate_purchases s α hne hS P Q hP hQ hBuyP hBuyQ
    (P.cross_distance Q hP hQ hG girth tail crossP)
    (Q.cross_distance P hQ hP hG girth tail.symm crossQ)

/-- The incoming-thread obstruction for actual block paths with disjoint interiors. -/
theorem nash_block_no_two_incoming_long_paths {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x A B C : Fin n} (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {v}, (q : (graph s).Walk v v) → q.IsCycle → 8 ≤ q.length)
    (p : LongDegreeTwoBlockPath (graph s) S x A B)
    (q : LongDegreeTwoBlockPath (graph s) S x C B)
    (hAB : A ≠ B) (hCB : C ≠ B)
    (hNearP : (graph s).dist A x ≤ (graph s).dist B x)
    (hNearQ : (graph s).dist C x ≤ (graph s).dist B x)
    (disjoint : ∀ i j, 0 < i → i < p.walk.length → 0 < j → j < q.walk.length →
      p.walk.getVert i ≠ q.walk.getVert j) : False := by
  have hG := nash_connected (Nat.zero_lt_of_lt x.isLt) α s hne
  let P := LongBlockThreadTo.ofWalk hS hG hx girth p.walk p.isPath p.long p.degree p.avoid
  let Q := LongBlockThreadTo.ofWalk hS hG hx girth q.walk q.isPath q.long q.degree q.avoid
  have hLp := p.long
  have hLq := q.long
  have hP : 3 ≤ P.length := by change 3 ≤ p.walk.length; omega
  have hQ : 3 ≤ Q.length := by change 3 ≤ q.walk.length; omega
  exact nash_block_no_two_penultimate_path_purchases s α hne hS girth
    p.toDegreeTwoBlockPath q.toDegreeTwoBlockPath hP hQ
    (nash_block_long_thread_penultimate_purchase s α hne hS P hAB hx hMax hNearP)
    (nash_block_long_thread_penultimate_purchase s α hne hS Q hCB hx hMax hNearQ)
    disjoint

/-- A simple graph represented by internally disjoint long paths avoiding the
interior location of a maximum attachment is acyclic. -/
theorem nash_block_long_path_graph_isAcyclic {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) {S : Finset (Fin n)}
    (hS : IsBiconnectedBlock (graph s) S) [DecidableRel (blockGraph (graph s) S).Adj]
    {x : Fin n} (hx : x ∈ S)
    (hMax : ∀ z ∈ S, (blockAttachment (graph s) S z).card ≤
      (blockAttachment (graph s) S x).card)
    (girth : ∀ {v}, (q : (graph s).Walk v v) → q.IsCycle → 8 ≤ q.length)
    (H : SimpleGraph (Fin n))
    (paths : ∀ {u v}, H.Adj v u → LongDegreeTwoBlockPath (graph s) S x u v)
    (disjoint : ∀ {u v w} (hu : H.Adj v u) (hw : H.Adj v w), u ≠ w →
      ∀ i j, 0 < i → i < (paths hu).walk.length → 0 < j → j < (paths hw).walk.length →
        (paths hu).walk.getVert i ≠ (paths hw).walk.getVert j) :
    H.IsAcyclic := by
  apply isAcyclic_of_unique_lower_neighbor H (fun u => (graph s).dist u x)
  intro v u w hu hw hNearP hNearQ
  by_contra hNe
  exact nash_block_no_two_incoming_long_paths s α hne hS hx hMax girth
    (paths hu) (paths hw) hu.ne.symm hw.ne.symm hNearP hNearQ (disjoint hu hw hNe)

#print axioms nash_block_no_two_penultimate_path_purchases
#print axioms nash_block_no_two_incoming_long_paths
#print axioms nash_block_long_path_graph_isAcyclic

end Lax869952Proofs
