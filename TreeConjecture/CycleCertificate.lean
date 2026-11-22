import TreeConjecture.LayerDeviations
import TreeConjecture.Redirect

set_option warningAsError true

namespace TreeConjecture

open SimpleGraph Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped BigOperators NNReal

namespace CycleCertificate

variable {k n : ℕ}

def next (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

abbrev neighbors (i j : Fin k) : Prop := next i = j ∨ next j = i

def cycleDistance (i j : Fin k) : ℕ :=
  let gap := max i.val j.val - min i.val j.val
  min gap (k - gap)

theorem cycleDistance_le_half (i j : Fin k) : cycleDistance i j ≤ k / 2 := by
  dsimp [cycleDistance]
  omega

abbrev Orientation (k : ℕ) := Fin k → Bool
abbrev Labels (k : ℕ) := Fin k → Fin (k / 2 + 1)

abbrev Lipschitz (l : Labels k) : Prop :=
  ∀ i, (l i).val ≤ (l (next i)).val + 1 ∧ (l (next i)).val ≤ (l i).val + 1

/-- A labelled cycle whose shorter arcs realize the ambient distances. -/
structure Embedding (G : SimpleGraph (Fin n)) (k : ℕ) where
  vertex : Fin k ↪ Fin n
  adjacent : ∀ i, G.Adj (vertex i) (vertex (next i))
  isometric : ∀ i j, G.dist (vertex i) (vertex j) = cycleDistance i j

/-- The affected purchases and one surviving route from the buyer to
each cycle vertex. The routes record successive vertices after the buyer. -/
structure Move (k : ℕ) where
  buyer : Fin k
  sold : List (Fin k)
  link : Option (Fin k)
  route : Fin k → List (Fin k)

namespace Move

def saved (m : Move k) : ℕ := m.sold.toFinset.card - (if m.link.isSome then 1 else 0)

abbrev owned (o : Orientation k) (i j : Fin k) : Prop :=
  (next i = j ∧ o i = false) ∨ (next j = i ∧ o j = true)

abbrev validAdj (m : Move k) (i j : Fin k) : Prop :=
  (neighbors i j ∧ (i ≠ m.buyer ∨ j ∉ m.sold) ∧ (j ≠ m.buyer ∨ i ∉ m.sold)) ∨
    (i = m.buyer ∧ m.link = some j) ∨ (j = m.buyer ∧ m.link = some i)

def routeOK (m : Move k) (i j : Fin k) : List (Fin k) → Bool
  | [] => decide (i = j)
  | x :: path => decide (m.validAdj i x) && m.routeOK x j path

abbrev Valid (m : Move k) (o : Orientation k) : Prop :=
  (∀ j ∈ m.sold, owned o m.buyer j) ∧
    m.link ≠ some m.buyer ∧ (if m.link.isSome then 1 else 0) ≤ m.sold.toFinset.card ∧
    ∀ j, m.routeOK m.buyer j (m.route j) = true

abbrev safe (m : Move k) (l : Labels k) (j : Fin k) : Prop :=
  (l j).val < (l m.buyer).val + cycleDistance m.buyer j

abbrev baseline (m : Move k) (l : Labels k) : Prop :=
  ∀ j ∈ m.sold, (l m.buyer).val ≠ (l j).val + 1

/-- Upper bounds on the signed distance change to a vertex of type `l`.
The old route is covered when no sold edge can start a shortest path.
Each other candidate comes from a route to a safe cycle vertex. -/
def candidates (m : Move k) (l : Labels k) : List ℤ :=
  (if m.baseline l then [0] else []) ++ (List.finRange k).filterMap fun j =>
    if m.safe l j then
      some ((m.route j).length + ((l j).val : ℤ) - ((l m.buyer).val : ℤ))
    else none

def impact (m : Move k) (l : Labels k) : ℤ :=
  (m.candidates l).foldl min (k + 1 : ℤ)

end Move

private theorem foldl_min_mem (xs : List ℤ) (start : ℤ) : xs.foldl min start ∈ start :: xs := by
  induction xs generalizing start with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp (ih (min start a)) with he | he
    · rcases min_choice start a with h | h
      · exact List.mem_cons.mpr (Or.inl (he.trans h))
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl (he.trans h))))
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons_of_mem _ he))

private theorem safe_shortest_avoids {G : SimpleGraph (Fin n)} {u j x : Fin n}
    (p : G.Walk j x) (hp : p.length = G.dist j x)
    (hSafe : G.dist j x < G.dist j u + G.dist u x) : u ∉ p.support := by
  intro hMem
  obtain ⟨a, b, h⟩ := p.mem_support_iff_exists_append.mp hMem
  have ha := SimpleGraph.dist_le a
  have hb := SimpleGraph.dist_le b
  rw [h, Walk.length_append] at hp
  omega

private theorem indexedRoute {H : SimpleGraph (Fin n)} (v : Fin k → Fin n) (m : Move k)
    (hAdj : ∀ {i j}, m.validAdj i j → H.Adj (v i) (v j))
    {i j : Fin k} (path : List (Fin k)) (h : m.routeOK i j path = true) :
    ∃ p : H.Walk (v i) (v j), p.length = path.length := by
  induction path generalizing i with
  | nil =>
    have he : i = j := of_decide_eq_true h
    subst j
    exact ⟨.nil, rfl⟩
  | cons a as ih =>
    obtain ⟨ha, hs⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨p, hp⟩ := ih hs
    exact ⟨.cons (hAdj (of_decide_eq_true ha)) p, by simp [hp]⟩

private theorem labels_exist {G : SimpleGraph (Fin n)} (hG : G.Connected) (hk : 0 < k)
    (e : Embedding G k) (x : Fin n) :
    ∃ l : Labels k, Lipschitz l ∧ ∃ b : ℕ, ∀ j, G.dist (e.vertex j) x = b + (l j).val := by
  classical
  let d (j : Fin k) := G.dist (e.vertex j) x
  obtain ⟨j, _, hMin⟩ := Finset.exists_min_image Finset.univ d ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hMin' (i) : d j ≤ d i := hMin i (Finset.mem_univ _)
  have hUpper (i) : d i ≤ d j + k / 2 := by
    have ht : d i ≤ G.dist (e.vertex i) (e.vertex j) + d j := hG.dist_triangle
    rw [e.isometric] at ht
    have hHalf := cycleDistance_le_half i j
    omega
  let l (i : Fin k) : Fin (k / 2 + 1) := ⟨d i - d j, by have := hUpper i; omega⟩
  have hEq (i) : d i = d j + (l i).val := by dsimp only [l]; have := hMin' i; omega
  refine ⟨l, ?_, d j, hEq⟩
  intro i
  have hi := dist_eq_one_iff_adj.mpr (e.adjacent i)
  have hf : d i ≤ G.dist (e.vertex i) (e.vertex (next i)) + d (next i) := hG.dist_triangle
  have hr : d (next i) ≤ G.dist (e.vertex (next i)) (e.vertex i) + d i := hG.dist_triangle
  rw [dist_comm (u := e.vertex (next i)), hi] at hr
  rw [hi] at hf
  rw [hEq i, hEq (next i)] at hf hr
  omega

private theorem move_routes (s : Profile n) (e : Embedding (graph s) k) (m : Move k)
    (t : Profile n) (hG : (graph s).Connected)
    (hKeep : ∀ {a b}, (graph s).Adj a b →
      (a ≠ e.vertex m.buyer ∨ b ∉ m.sold.toFinset.image e.vertex) →
      (b ≠ e.vertex m.buyer ∨ a ∉ m.sold.toFinset.image e.vertex) → (graph t).Adj a b)
    (hLink : ∀ j, m.link = some j → (graph t).Adj (e.vertex m.buyer) (e.vertex j))
    (hRoutes : ∀ j, m.routeOK m.buyer j (m.route j) = true)
    (x : Fin n) (l : Labels k) (b : ℕ)
    (hLabels : ∀ j, (graph s).dist (e.vertex j) x = b + (l j).val)
    (hImpact : m.impact l < (k + 1 : ℤ)) :
    ∃ p : (graph t).Walk (e.vertex m.buyer) x,
      (p.length : ℤ) - ((graph s).dist (e.vertex m.buyer) x : ℤ) ≤ m.impact l := by
  classical
  let G := graph s
  let H := graph t
  let u := e.vertex m.buyer
  let sold := m.sold.toFinset.image e.vertex
  have hMoveAdj {i j : Fin k} (h : m.validAdj i j) : H.Adj (e.vertex i) (e.vertex j) := by
    rcases h with ⟨hEdge, hi, hj⟩ | ⟨hi, he⟩ | ⟨hj, he⟩
    · have hEdge' : G.Adj (e.vertex i) (e.vertex j) := by
        rcases hEdge with hEdge | hEdge
        · exact hEdge ▸ e.adjacent i
        · exact hEdge ▸ (e.adjacent j).symm
      have hNotMem {a : Fin k} (ha : a ∉ m.sold) : e.vertex a ∉ sold := by
        intro hm
        obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hm
        exact ha (e.vertex.injective he ▸ List.mem_toFinset.mp hc)
      exact hKeep hEdge'
        (hi.imp (fun hn he => hn (e.vertex.injective he)) hNotMem)
        (hj.imp (fun hn he => hn (e.vertex.injective he)) hNotMem)
    · exact hi ▸ hLink j he
    · exact hj ▸ (hLink i he).symm
  have hMem : m.impact l ∈ m.candidates l := by
    rcases List.mem_cons.mp (foldl_min_mem (m.candidates l) (k + 1 : ℤ)) with he | hm
    · exact (ne_of_lt hImpact he).elim
    · exact hm
  unfold Move.candidates at hMem
  rcases List.mem_append.mp hMem with hOld | hOther
  · by_cases hBase : m.baseline l
    · simp only [if_pos hBase, List.mem_singleton] at hOld
      obtain ⟨p, hp, hLen⟩ := hG.exists_path_of_dist u x
      by_cases hx : x = u
      · subst x
        exact ⟨.nil, by simp [hOld, u]⟩
      · obtain ⟨y, hadj, tail, rfl⟩ := Walk.exists_eq_cons_of_ne (fun he => hx he.symm) p
        have hKeepFirst : y ∉ sold := by
          intro hy
          obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp hy
          have hDist : G.dist u x = G.dist y x + 1 := by
            have hb : G.dist y x ≤ tail.length := SimpleGraph.dist_le tail
            have ht : G.dist u x ≤ G.dist u y + G.dist y x := hG.dist_triangle
            rw [dist_eq_one_iff_adj.mpr hadj] at ht
            rw [Walk.length_cons] at hLen
            change tail.length + 1 = G.dist u x at hLen
            omega
          rw [← hjy, hLabels j] at hDist
          change G.dist (e.vertex m.buyer) x = _ at hDist
          rw [hLabels m.buyer] at hDist
          exact hBase j (List.mem_toFinset.mp hj) (by omega)
        have hAvoid := (Walk.cons_isPath_iff hadj tail).mp hp |>.2
        obtain ⟨q, hq⟩ := transport_avoiding (H := H)
          (fun ha hb hab => hKeep hab (Or.inl ha) (Or.inl hb)) tail hAvoid
        refine ⟨.cons (hKeep hadj (Or.inr hKeepFirst) (Or.inl hadj.ne.symm)) q, ?_⟩
        rw [Walk.length_cons, hq, ← Walk.length_cons hadj, hLen, hOld]
        change ((G.dist u x : ℕ) : ℤ) - (G.dist u x : ℤ) ≤ 0
        omega
    · simp [hBase] at hOld
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hOther
    by_cases hs : m.safe l j
    · simp only [if_pos hs, Option.some.injEq] at hj
      obtain ⟨p, hp⟩ := indexedRoute e.vertex m hMoveAdj (m.route j) (hRoutes j)
      obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist (e.vertex j) x
      have hSafe : G.dist (e.vertex j) x < G.dist (e.vertex j) u + G.dist u x := by
        rw [dist_comm (u := e.vertex j) (v := u), e.isometric]
        change G.dist (e.vertex j) x < cycleDistance m.buyer j + G.dist (e.vertex m.buyer) x
        rw [hLabels j, hLabels m.buyer]
        change (l j).val < (l m.buyer).val + cycleDistance m.buyer j at hs
        omega
      obtain ⟨q', hq'⟩ := transport_avoiding (H := H)
        (fun ha hb hab => hKeep hab (Or.inl ha) (Or.inl hb)) q (safe_shortest_avoids q hq hSafe)
      refine ⟨p.append q', ?_⟩
      rw [Walk.length_append, hp, hq', hq, hLabels j, hLabels m.buyer, ← hj]
      push_cast
      omega
    · simp [hs] at hj

private theorem move_apply (s : Profile n) (e : Embedding (graph s) k) (m : Move k)
    (o : Orientation k)
    (hOrient : ∀ i, if o i then e.vertex i ∈ (s (e.vertex (next i))).val
      else e.vertex (next i) ∈ (s (e.vertex i)).val)
    (hValid : m.Valid o) :
    let u := e.vertex m.buyer
    let sold := m.sold.toFinset.image e.vertex
    ∃ t : Profile n,
      (∀ {a b}, (graph s).Adj a b → (a ≠ u ∨ b ∉ sold) →
         (b ≠ u ∨ a ∉ sold) → (graph t).Adj a b) ∧
      (∀ j, m.link = some j → (graph t).Adj u (e.vertex j)) ∧
      ((t u).val.ncard + m.saved ≤ (s u).val.ncard) ∧
      (∀ a, a ≠ u → t a = s a) := by
  classical
  intro u sold
  have hOwn (a : Fin n) (ha : a ∈ sold) : a ∈ (s u).val := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    rcases hValid.1 j (List.mem_toFinset.mp hj) with ⟨he, ho⟩ | ⟨he, ho⟩
    · simpa only [ho, Bool.false_eq_true, if_false, he, u] using hOrient m.buyer
    · have hh := hOrient j
      simp only [ho, if_true] at hh
      rw [he] at hh
      exact hh
  have hCard : sold.card = m.sold.toFinset.card := Finset.card_image_of_injective _ e.vertex.injective
  cases hLink : m.link with
  | none =>
    refine ⟨sellPurchases s u sold, fun h ha hb => sellPurchases_adj h ha hb, ?_, ?_, ?_⟩
    · intro j he
      simp at he
    · have hp := sellPurchases_count s u sold hOwn
      rw [hCard] at hp
      simpa [Move.saved, hLink] using hp.le
    · exact fun a ha => sellPurchases_other s u a sold ha
  | some j =>
    have huj : u ≠ e.vertex j := by
      intro he
      have hEq := e.vertex.injective he
      exact hValid.2.1 (by rw [hLink, hEq])
    refine ⟨redirect s u (e.vertex j) huj sold, fun h ha hb => redirect_preserves_adj h ha hb, ?_, ?_, ?_⟩
    · intro a he
      rw [Option.some.injEq] at he
      subst a
      exact redirect_adj_target s huj sold
    · have hEnough : 1 ≤ m.sold.toFinset.card := by simpa [hLink] using hValid.2.2.1
      have h := redirect_card_le s huj sold hOwn
      rw [hCard] at h
      have hSave : m.saved = m.sold.toFinset.card - 1 := by simp [Move.saved, hLink]
      omega
    · exact fun _ ha => redirect_other s huj sold ha

private theorem move_nash_bound (s : Profile n) (α : ℝ≥0) (hne : IsNashEquilibrium α s)
    (hG : (graph s).Connected) (e : Embedding (graph s) k)
    (o : Orientation k)
    (hOrient : ∀ i, if o i then e.vertex i ∈ (s (e.vertex (next i))).val
      else e.vertex (next i) ∈ (s (e.vertex i)).val)
    (m : Move k) (hValid : m.Valid o) (l : Fin n → Labels k) (b : Fin n → ℕ)
    (hLabels : ∀ x j, (graph s).dist (e.vertex j) x = b x + (l x j).val)
    (hImpact : ∀ x, m.impact (l x) < (k + 1 : ℤ)) :
    (m.saved : ℝ) * α ≤ ∑ x, (m.impact (l x) : ℝ) := by
  classical
  obtain ⟨t, hKeep, hLink, hCount, hOther⟩ := move_apply s e m o hOrient hValid
  have hWalk x := move_routes s e m t hG hKeep hLink hValid.2.2.2 x _ _ (hLabels x) (hImpact x)
  let u := e.vertex m.buyer
  have hT : (graph t).Connected :=
    (connected_iff_exists_forall_reachable _).mpr ⟨u, fun x => ⟨(hWalk x).choose⟩⟩
  have hPoint (x : Fin n) : ((graph t).dist u x : ℝ) - ((graph s).dist u x : ℝ) ≤
      (m.impact (l x) : ℝ) := by
    obtain ⟨p, hp⟩ := hWalk x
    have hReal : (p.length : ℝ) - ((graph s).dist u x : ℝ) ≤ (m.impact (l x) : ℝ) := by
      exact_mod_cast hp
    have hLen : ((graph t).dist u x : ℝ) ≤ (p.length : ℝ) := by exact_mod_cast SimpleGraph.dist_le p
    linarith
  have hSum := Finset.sum_le_sum fun x (_ : x ∈ (Finset.univ : Finset (Fin n))) => hPoint x
  rw [Finset.sum_sub_distrib] at hSum
  change distanceSum (graph t) u - distanceSum (graph s) u ≤ _ at hSum
  have hNash := nash_finite_cost_le α s t hG hT hne u hOther
  have hCountR : ((t u).val.ncard : ℝ) + (m.saved : ℝ) ≤ ((s u).val.ncard : ℝ) := by
    exact_mod_cast hCount
  have hMul := mul_le_mul_of_nonneg_right hCountR ((NNReal.zero_le_coe : (0 : ℝ) ≤ α))
  unfold finiteCost at hNash
  linarith only [hSum, hNash, hMul]

abbrev WeightedMoves (k : ℕ) := List (ℕ × Move k)

def savings : WeightedMoves k → ℕ
  | [] => 0
  | (w, m) :: ms => w * m.saved + savings ms

def weightedImpact (l : Labels k) : WeightedMoves k → ℤ
  | [] => 0
  | (w, m) :: ms => (w : ℤ) * m.impact l + weightedImpact l ms

/-- The finite conditions for a weighted collection of Nash inequalities
to prove a price bound of `numerator * n / denominator`. -/
abbrev Checks (o : Orientation k) (moves : WeightedMoves k) (numerator denominator : ℕ) : Prop :=
  (∀ wm ∈ moves, wm.2.Valid o) ∧ 0 < savings moves ∧
    ∀ l : Labels k, Lipschitz l →
      (∀ wm ∈ moves, wm.2.impact l < (k + 1 : ℤ)) ∧
        (denominator : ℤ) * weightedImpact l moves ≤ (numerator : ℤ) * (savings moves : ℤ)

private theorem weighted_nash (α : ℝ≥0) (l : Fin n → Labels k) (moves : WeightedMoves k)
    (h : ∀ wm ∈ moves, (wm.2.saved : ℝ) * α ≤ ∑ x, (wm.2.impact (l x) : ℝ)) :
    (savings moves : ℝ) * α ≤ ∑ x, (weightedImpact (l x) moves : ℝ) := by
  induction moves with
  | nil => simp [savings, weightedImpact]
  | cons wm ms ih =>
    obtain ⟨w, m⟩ := wm
    have hm := h (w, m) (List.mem_cons_self)
    have hs := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have ht := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) w)
    simp only [savings, weightedImpact, Nat.cast_add, Nat.cast_mul, Int.cast_add,
      Int.cast_mul, Int.cast_natCast, Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith only [ht, hs]

abbrev Models (s : Profile n) (e : Embedding (graph s) k) (o : Orientation k) : Prop :=
  ∀ i, if o i then e.vertex i ∈ (s (e.vertex (next i))).val
    else e.vertex (next i) ∈ (s (e.vertex i)).val

theorem exists_orientation (s : Profile n) (e : Embedding (graph s) k) :
    ∃ o, Models s e o := by
  classical
  let o (i : Fin k) := if e.vertex (next i) ∈ (s (e.vertex i)).val then false else true
  refine ⟨o, fun i => ?_⟩
  by_cases h : e.vertex (next i) ∈ (s (e.vertex i)).val
  · simp [o, h]
  · simpa [o, h] using (e.adjacent i).resolve_left h

/-- Soundness of the cycle certificates for arbitrary finite networks.
The checks quantify over cycle labels and allow arbitrary outside vertices. -/
theorem price_bound_for_orientation (s : Profile n) (α : ℝ≥0) (hne : IsNashEquilibrium α s)
    (hk : 0 < k) (e : Embedding (graph s) k) (num den : ℕ)
    (o : Orientation k) (hOrient : Models s e o) (moves : WeightedMoves k)
    (hCertificate : Checks o moves num den) :
    (den : ℝ) * α ≤ (num : ℝ) * (n : ℝ) := by
  classical
  have hG := nash_connected (Nat.zero_lt_of_lt (e.vertex ⟨0, hk⟩).isLt) α s hne
  obtain ⟨hValid, hPos, hPoints⟩ := hCertificate
  choose l hl using fun x : Fin n => labels_exist hG hk e x
  choose b hb using fun x => (hl x).2
  have hBound := weighted_nash α l moves fun wm hm =>
    move_nash_bound s α hne hG e o hOrient wm.2 (hValid wm hm) l b hb
      (fun x => (hPoints (l x) (hl x).1).1 wm hm)
  have hLocal (x : Fin n) : (den : ℝ) * (weightedImpact (l x) moves : ℝ) ≤
      (num : ℝ) * (savings moves : ℝ) := by
    exact_mod_cast (hPoints (l x) (hl x).1).2
  have hTotal := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin n))) => hLocal x)
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hTotal
  have hs := mul_le_mul_of_nonneg_left hBound (Nat.cast_nonneg (α := ℝ) den)
  have hsPos : 0 < (savings moves : ℝ) := by exact_mod_cast hPos
  apply (mul_le_mul_iff_right₀ hsPos).mp
  linarith only [hs, hTotal]

theorem price_bound (s : Profile n) (α : ℝ≥0) (hne : IsNashEquilibrium α s)
    (hk : 0 < k) (e : Embedding (graph s) k) (num den : ℕ)
    (certificate : Orientation k → WeightedMoves k)
    (hCertificate : ∀ o, Checks o (certificate o) num den) :
    (den : ℝ) * α ≤ (num : ℝ) * (n : ℝ) := by
  obtain ⟨o, ho⟩ := exists_orientation s e
  exact price_bound_for_orientation s α hne hk e num den o ho (certificate o) (hCertificate o)

end CycleCertificate
end TreeConjecture
