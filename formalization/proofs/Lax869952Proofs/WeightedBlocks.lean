import Lax869952Proofs.BlockSwaps
import Lax869952Proofs.Addition
import Lax869952Proofs.Redirect
import Lax869952Proofs.RootedShortestPaths

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ} {G D : SimpleGraph (Fin n)} {S : Finset (Fin n)}

/-- All edges with an endpoint outside the block are unchanged. -/
def AgreeOutsideBlock (G D : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ ⦃u v⦄, u ∉ S ∨ v ∉ S → (G.Adj u v ↔ D.Adj u v)

theorem AgreeOutsideBlock.symm (h : AgreeOutsideBlock G D S) : AgreeOutsideBlock D G S :=
  fun _ _ hOutside => (h hOutside).symm

private theorem firstEntry_transport (hAgree : AgreeOutsideBlock G D S)
    {x z : Fin n} (p : G.Walk x z) (hEntry : FirstEntryInto S p) :
    ∃ q : D.Walk x z, q.length = p.length ∧ FirstEntryInto S q := by
  have hEdges (e : Sym2 (Fin n)) (he : e ∈ p.edges) : e ∈ D.edgeSet := by
    induction e using Sym2.ind with
    | h a b =>
      have hab : G.Adj a b := p.adj_of_mem_edges he
      have outside : a ∉ S ∨ b ∉ S := by
        by_contra! inside
        exact hab.ne ((hEntry a (p.fst_mem_support_of_mem_edges he) inside.1).trans
          (hEntry b (p.snd_mem_support_of_mem_edges he) inside.2).symm)
      exact (hAgree outside).mp hab
  let q := p.transfer D hEdges
  refine ⟨q, Walk.length_transfer p hEdges, ?_⟩
  intro a ha haS
  exact hEntry a (by simpa only [q, Walk.support_transfer] using ha) haS

private theorem firstEntry_prefix {x y : Fin n} (p : G.Walk x y) (hy : y ∈ S) :
    ∃ z ∈ S, ∃ q : G.Walk x z, q.length ≤ p.length ∧ FirstEntryInto S q := by
  induction p with
  | nil => exact ⟨_, hy, .nil, le_rfl, by simp [FirstEntryInto]⟩
  | @cons a b c hab p ih =>
    by_cases ha : a ∈ S
    · exact ⟨a, ha, .nil, Nat.zero_le _, by simp [FirstEntryInto]⟩
    · obtain ⟨z, hz, q, hl, hf⟩ := ih hy
      refine ⟨z, hz, .cons hab q, by simpa only [Walk.length_cons] using Nat.succ_le_succ hl, ?_⟩
      intro v hv hvS
      rcases List.mem_cons.mp hv with rfl | hq
      · exact (ha hvS).elim
      · exact hf v hq hvS

private theorem attachment_distance_invariant (hS : IsBiconnectedBlock G S)
    (hAgree : AgreeOutsideBlock G D S) (hG : G.Connected) (hD : D.Connected)
    {x z : Fin n} (hz : z ∈ S) (hx : x ∈ blockAttachment G S z) :
    D.dist x z = G.dist x z := by
  obtain ⟨entry, hEntry⟩ := mem_blockAttachment.mp hx
  apply le_antisymm
  · obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x z
    obtain ⟨a, ha, q, hql, hqf⟩ := firstEntry_prefix p hz
    have he := hS.first_entry_unique ha hz q entry hqf hEntry
    obtain ⟨q', hq', _⟩ := firstEntry_transport hAgree q hqf
    subst a
    exact (dist_le q').trans (hq'.le.trans (hql.trans hp.le))
  · obtain ⟨p, hp⟩ := hD.exists_walk_length_eq_dist x z
    obtain ⟨a, ha, q, hql, hqf⟩ := firstEntry_prefix p hz
    obtain ⟨q', hq', hqf'⟩ := firstEntry_transport hAgree.symm q hqf
    have he := hS.first_entry_unique ha hz q' entry hqf' hEntry
    subst a
    exact (dist_le q').trans (hq'.le.trans (hql.trans hp.le))

/-- Changing edges within a block preserves the entry and distance offset of each
attached vertex. The resulting block need not remain two-connected. -/
theorem IsBiconnectedBlock.dist_add_after_block_change (hS : IsBiconnectedBlock G S)
    (hAgree : AgreeOutsideBlock G D S) (hG : G.Connected) (hD : D.Connected)
    {u z x : Fin n} (hu : u ∈ S) (hz : z ∈ S) (hx : x ∈ blockAttachment G S z) :
    D.dist u x = D.dist u z + G.dist z x := by
  obtain ⟨entry, hEntry⟩ := mem_blockAttachment.mp hx
  obtain ⟨p, hp⟩ := hD.exists_walk_length_eq_dist x u
  obtain ⟨a, ha, q, hSub, hFirst⟩ := exists_first_entry_walk p hu
  obtain ⟨q', _, hFirst'⟩ := firstEntry_transport hAgree.symm q hFirst
  have equal := hS.first_entry_unique ha hz q' entry hFirst' hEntry
  have hVisit : z ∈ p.support := equal ▸ hSub q.end_mem_support
  have lower := walk_length_ge_via p hVisit
  rw [hp] at lower
  have upper : D.dist x u ≤ D.dist x z + D.dist z u := hD.dist_triangle
  have distEntry := attachment_distance_invariant hS hAgree hG hD hz hx
  rw [dist_comm (u := u) (v := x), dist_comm (u := u) (v := z),
    dist_comm (u := z) (v := x), ← distEntry, Nat.add_comm]
  exact le_antisymm upper lower

/-- It suffices to keep the induced block connected when the exterior is unchanged. -/
theorem IsBiconnectedBlock.connected_after_block_change (hS : IsBiconnectedBlock G S)
    (hAgree : AgreeOutsideBlock G D S) (hG : G.Connected) {u : Fin n}
    (hReach : ∀ z ∈ S, (blockGraph D S).Reachable u z) : D.Connected := by
  apply (connected_iff_exists_forall_reachable D).mpr
  refine ⟨u, fun x => ?_⟩
  obtain ⟨z, hz, _⟩ := hS.exists_unique_entry hG x
  obtain ⟨p, hp⟩ := hz.2
  obtain ⟨q, _, _⟩ := firstEntry_transport hAgree p hp
  exact ((hReach z hz.1).mono (blockGraph_le D S)).trans q.reachable.symm

/-- Projecting exterior vertices to their original entries collapses exterior
edges and preserves internal ones. Thus exterior walks cannot shorten a route
in the changed core. -/
theorem IsBiconnectedBlock.block_dist_after_block_change (hS : IsBiconnectedBlock G S)
    (hAgree : AgreeOutsideBlock G D S) (hG : G.Connected) (hD : D.Connected)
    {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) :
    (blockGraph D S).dist u v = D.dist u v := by
  classical
  let entry (a : Fin n) := (hS.exists_unique_entry hG a).choose
  have entrySpec (a : Fin n) :
      (entry a ∈ S ∧ ∃ p : G.Walk a (entry a), FirstEntryInto S p) ∧
        ∀ z, (z ∈ S ∧ ∃ p : G.Walk a z, FirstEntryInto S p) → z = entry a :=
    (hS.exists_unique_entry hG a).choose_spec
  have fixed {a : Fin n} (ha : a ∈ S) : entry a = a :=
    ((entrySpec a).2 a ⟨ha, .nil, by simp [FirstEntryInto]⟩).symm
  have sameEntry {a b : Fin n} (ha : a ∉ S) (hab : D.Adj a b) : entry a = entry b := by
    have hOld := (hAgree (Or.inl ha)).mpr hab
    obtain ⟨q, hq⟩ := (entrySpec b).1.2
    have hFirst : FirstEntryInto S (.cons hOld q) := by
      intro k hk hkS
      rcases List.mem_cons.mp hk with rfl | hqk
      · exact (ha hkS).elim
      · exact hq k hqk hkS
    exact ((entrySpec a).2 _ ⟨(entrySpec b).1.1, .cons hOld q, hFirst⟩).symm
  have project {a b : Fin n} (p : D.Walk a b) :
      ∃ q : (blockGraph D S).Walk (entry a) (entry b), q.length ≤ p.length := by
    induction p with
    | nil => exact ⟨.nil, le_rfl⟩
    | @cons a b c hab p ih =>
      obtain ⟨q, hq⟩ := ih
      by_cases ha : a ∈ S
      · by_cases hb : b ∈ S
        · have hlink : (blockGraph D S).Adj (entry a) (entry b) := by
            rw [fixed ha, fixed hb]
            exact ⟨ha, hb, hab⟩
          exact ⟨.cons hlink q, by simpa only [Walk.length_cons] using Nat.succ_le_succ hq⟩
        · have e := sameEntry hb hab.symm
          exact ⟨q.copy e rfl, by
            simpa only [Walk.length_copy, Walk.length_cons] using (hq.trans (Nat.le_succ _))⟩
      · have e := sameEntry ha hab
        exact ⟨q.copy e.symm rfl, by
          simpa only [Walk.length_copy, Walk.length_cons] using (hq.trans (Nat.le_succ _))⟩
  obtain ⟨p, hp⟩ := hD.exists_walk_length_eq_dist u v
  obtain ⟨q, hq⟩ := project p
  let r := q.copy (fixed hu) (fixed hv)
  have hLen : r.length ≤ D.dist u v := by simpa only [r, Walk.length_copy, ← hp] using hq
  exact ((dist_le r).trans hLen).antisymm (r.reachable.dist_anti (blockGraph_le D S))

/-- The original attachment sets partition all the players. -/
theorem IsBiconnectedBlock.biUnion_blockAttachment (hS : IsBiconnectedBlock G S)
    (hG : G.Connected) : S.biUnion (blockAttachment G S) = Finset.univ := by
  classical
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  obtain ⟨z, hz, _⟩ := hS.exists_unique_entry hG x
  exact ⟨z, hz.1, mem_blockAttachment.mpr hz.2⟩

private theorem attachment_pairwiseDisjoint (hS : IsBiconnectedBlock G S) :
    (↑S : Set (Fin n)).PairwiseDisjoint (blockAttachment G S) :=
  fun _ hx _ hy hne => hS.disjoint_blockAttachments hx hy hne

theorem IsBiconnectedBlock.sum_blockAttachment_card (hS : IsBiconnectedBlock G S)
    (hG : G.Connected) : (∑ z ∈ S, (blockAttachment G S z).card) = n := by
  classical
  rw [← Finset.card_biUnion (attachment_pairwiseDisjoint hS), hS.biUnion_blockAttachment hG]
  simp

/-- Distance sum inside the changed core with weights from the original graph. -/
noncomputable def weightedBlockDistance (G D : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (u : Fin n) : ℝ :=
  ∑ z ∈ S, ((blockAttachment G S z).card : ℝ) * ((blockGraph D S).dist u z : ℝ)

private noncomputable def attachmentOffset (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℝ :=
  ∑ z ∈ S, ∑ x ∈ blockAttachment G S z, (G.dist z x : ℝ)

theorem IsBiconnectedBlock.distanceSum_eq_weightedBlockDistance_add
    (hS : IsBiconnectedBlock G S) (hAgree : AgreeOutsideBlock G D S)
    (hG : G.Connected) (hD : D.Connected) {u : Fin n} (hu : u ∈ S) :
    distanceSum D u = weightedBlockDistance G D S u + attachmentOffset G S := by
  classical
  have hPartition : distanceSum D u = ∑ z ∈ S, ∑ x ∈ blockAttachment G S z, (D.dist u x : ℝ) := by
    rw [← Finset.sum_biUnion (attachment_pairwiseDisjoint hS), hS.biUnion_blockAttachment hG]
    rfl
  rw [hPartition, weightedBlockDistance, attachmentOffset, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  have hzDist (x : Fin n) (hx : x ∈ blockAttachment G S z) :
      (D.dist u x : ℝ) = ((blockGraph D S).dist u z : ℝ) + (G.dist z x : ℝ) := by
    rw [hS.dist_add_after_block_change hAgree hG hD hu hz hx,
      hS.block_dist_after_block_change hAgree hG hD hu hz]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hzDist, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

/-- The weighted cost of a player for purchases and distances inside one block. -/
noncomputable def weightedBlockCost (α : ℝ≥0) (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (s : Profile n) (u : Fin n) : ℝ :=
  (α : ℝ) * ((s u).val ∩ (↑S : Set (Fin n))).ncard +
    weightedBlockDistance G (graph s) S u

private theorem agreeOutsideBlock_of_deviation {s t : Profile n} {u : Fin n} (hu : u ∈ S)
    (hChange : ∀ j, j ≠ u → t j = s j)
    (hOutside : ∀ j ∉ S, j ∈ (t u).val ↔ j ∈ (s u).val) :
    AgreeOutsideBlock (graph s) (graph t) S := by
  intro a b hOutsideAB
  change (b ∈ (s a).val ∨ a ∈ (s b).val) ↔ (b ∈ (t a).val ∨ a ∈ (t b).val)
  have buy {x y : Fin n} (h : x ∉ S ∨ y ∉ S) : y ∈ (s x).val ↔ y ∈ (t x).val := by
    by_cases hx : x = u
    · subst x
      exact (hOutside y (h.resolve_left (fun hNot => hNot hu))).symm
    · rw [hChange x hx]
  exact or_congr (buy hOutsideAB) (buy hOutsideAB.symm)

/-- A connected unilateral change of purchases inside a block satisfies
exactly the corresponding weighted Nash inequality. -/
theorem nash_weighted_block_inequality (α : ℝ≥0) (s t : Profile n)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    {u : Fin n} (hu : u ∈ S) (hChange : ∀ j, j ≠ u → t j = s j)
    (hOutside : ∀ j ∉ S, j ∈ (t u).val ↔ j ∈ (s u).val)
    (hReach : ∀ z ∈ S, (blockGraph (graph t) S).Reachable u z) :
    weightedBlockCost α (graph s) S s u ≤ weightedBlockCost α (graph s) S t u := by
  have hG := nash_connected (Nat.zero_lt_of_lt u.isLt) α s hne
  have hAgree := agreeOutsideBlock_of_deviation hu hChange hOutside
  have hD := hS.connected_after_block_change hAgree hG hReach
  have hCost := nash_finite_cost_le α s t hG hD hne u hChange
  have hSameOutside : (t u).val \ (↑S : Set (Fin n)) = (s u).val \ (↑S : Set (Fin n)) := by
    ext j
    exact ⟨fun h => ⟨(hOutside j h.2).mp h.1, h.2⟩,
      fun h => ⟨(hOutside j h.2).mpr h.1, h.2⟩⟩
  have hSplitS := Set.ncard_inter_add_ncard_sdiff_eq_ncard (s u).val (↑S : Set (Fin n))
  have hSplitT := Set.ncard_inter_add_ncard_sdiff_eq_ncard (t u).val (↑S : Set (Fin n))
  unfold finiteCost at hCost
  rw [← hSplitS, ← hSplitT, hSameOutside, Nat.cast_add, Nat.cast_add, mul_add, mul_add,
    hS.distanceSum_eq_weightedBlockDistance_add (fun _ _ _ => Iff.rfl) hG hG hu,
    hS.distanceSum_eq_weightedBlockDistance_add hAgree hG hD hu] at hCost
  unfold weightedBlockCost
  linarith

#print axioms nash_weighted_block_inequality

/-- A route between different attachments must pass through their entries. -/
theorem IsBiconnectedBlock.dist_between_attachments (hS : IsBiconnectedBlock G S)
    (hG : G.Connected) {v z x y : Fin n} (hv : v ∈ S) (hz : z ∈ S) (hvz : v ≠ z)
    (hx : x ∈ blockAttachment G S v) (hy : y ∈ blockAttachment G S z) :
    G.dist x y = G.dist x v + G.dist v z + G.dist z y := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x y
  obtain ⟨q, hq⟩ := mem_blockAttachment.mp hy
  have hSep : x ∈ separatedVertices G z v :=
    (hS.separatedVertices_eq_blockAttachment hG hz hv hvz.symm).symm ▸ hx
  have hVisit : v ∈ p.support := by
    by_contra hNoVisit
    have hqv : v ∉ q.support := fun h => hvz (hq v h hv)
    exact (mem_separatedVertices.mp hSep)
      ⟨(p.append q).reverse, by simp [Walk.mem_support_append_iff, hNoVisit, hqv]⟩
  have lower := walk_length_ge_via p hVisit
  rw [hp] at lower
  have hTri : G.dist x y ≤ G.dist x v + G.dist v y := hG.dist_triangle
  rw [le_antisymm hTri lower, hS.dist_add_of_mem_blockAttachment hG hz hv hy, Nat.add_assoc]

/-- Any attachment with an exterior player supplies the single-addition
inequalities of a pendant leaf, with the original attachment weights. -/
theorem nash_weighted_leaf_inequality (α : ℝ≥0) (s : Profile n)
    (hne : IsNashEquilibrium α s) (hS : IsBiconnectedBlock (graph s) S)
    {v r : Fin n} (hv : v ∈ S) (hr : r ∈ S) (hvr : v ≠ r)
    (hWeight : 1 < (blockAttachment (graph s) S v).card) :
    (∑ z ∈ S, ((blockAttachment (graph s) S z).card : ℝ) *
      max 0 (((blockGraph (graph s) S).dist v z : ℝ) -
        ((blockGraph (graph s) S).dist r z : ℝ))) ≤ (α : ℝ) := by
  classical
  let G := graph s
  let H := blockGraph G S
  have hG := nash_connected (Nat.zero_lt_of_lt v.isLt) α s hne
  obtain ⟨x, hx, hxv⟩ := (blockAttachment G S v).exists_mem_ne hWeight v
  obtain ⟨q, hq⟩ := mem_blockAttachment.mp hx
  have hxOut : x ∉ S := fun h => hxv (hq x q.start_mem_support h)
  have hxr : x ≠ r := fun h => hxOut (h.symm ▸ hr)
  have hNotAdj : ¬ G.Adj x r := by
    intro h
    let p : G.Walk x r := .cons h .nil
    have hp : FirstEntryInto S p := by
      intro a ha haS
      have hCases : a = x ∨ a = r := by simpa [p] using ha
      exact hCases.elim (fun h => (hxOut (h ▸ haS)).elim) id
    exact hvr (hS.first_entry_unique hv hr q p hq hp)
  have hAddition := nash_addition_distance_bound s α hne hxr hNotAdj
  have hDistance (u z : Fin n) (hu : u ∈ S) (hz : z ∈ S) :
      H.dist u z = G.dist u z :=
    hS.block_dist_after_block_change (fun _ _ _ => Iff.rfl) hG hG hu hz
  have hxDist : (1 : ℝ) ≤ (G.dist x v : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (dist_ne_zero_iff_ne_and_reachable.mpr ⟨hxv, hG x v⟩))
  have hTerm (z : Fin n) (hz : z ∈ S) (y : Fin n) (hy : y ∈ blockAttachment G S z) :
      max 0 ((H.dist v z : ℝ) - (H.dist r z : ℝ)) ≤
        max 0 ((G.dist x y : ℝ) - (G.dist r y : ℝ) - 1) := by
    by_cases h : z = v
    · subst z
      rw [dist_self, Nat.cast_zero, zero_sub, max_eq_left (neg_nonpos.mpr (Nat.cast_nonneg _))]
      exact le_max_left _ _
    · have hXY := hS.dist_between_attachments hG hv hz (Ne.symm h) hx hy
      have hRY := hS.dist_add_of_mem_blockAttachment hG hz hr hy
      rw [hDistance v z hv hz, hDistance r z hr hz, hXY, hRY]
      push_cast
      exact max_le_max_left 0 (by linarith)
  change (∑ z ∈ S, ((blockAttachment G S z).card : ℝ) *
    max 0 ((H.dist v z : ℝ) - (H.dist r z : ℝ))) ≤ (α : ℝ)
  calc
    _ = ∑ z ∈ S, ∑ y ∈ blockAttachment G S z,
        max 0 ((H.dist v z : ℝ) - (H.dist r z : ℝ)) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ z ∈ S, ∑ y ∈ blockAttachment G S z,
        max 0 ((G.dist x y : ℝ) - (G.dist r y : ℝ) - 1) :=
      Finset.sum_le_sum fun z hz => Finset.sum_le_sum (hTerm z hz)
    _ = ∑ y : Fin n, max 0 ((G.dist x y : ℝ) - (G.dist r y : ℝ) - 1) := by
      rw [← Finset.sum_biUnion (attachment_pairwiseDisjoint hS), hS.biUnion_blockAttachment hG]
    _ ≤ (α : ℝ) := hAddition

#print axioms nash_weighted_leaf_inequality

/-- A player can replace purchases going no further from the target than
the player is, while preserving the target's old shortest-path bounds. -/
theorem nash_redirect_toward_root_bound (α : ℝ≥0) (s : Profile n)
    (hne : IsNashEquilibrium α s) {i r : Fin n} (hir : i ≠ r)
    (sold : Finset (Fin n)) (hBuy : ∀ z ∈ sold, z ∈ (s i).val)
    (hDepth : ∀ z ∈ sold, (graph s).dist r z ≤ (graph s).dist r i) :
    distanceSum (graph s) i + (α : ℝ) * (sold.card : ℝ) ≤
      distanceSum (graph s) r + ((n - 1 : ℕ) : ℝ) + (α : ℝ) := by
  let G := graph s
  let D := graph (redirect s i r hir sold)
  have hG := nash_connected (Nat.zero_lt_of_lt i.isLt) α s hne
  apply nash_redirect_bound s α hne hir sold hBuy
  intro z hz
  rcases hz with rfl | hz
  · have hAdj : D.Adj r z := (redirect_adj_target s hir sold).symm
    have hdist := dist_ne_zero_iff_ne_and_reachable.mpr ⟨hir.symm, hG r z⟩
    exact ⟨.cons hAdj .nil, Nat.one_le_iff_ne_zero.mpr hdist⟩
  · obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist r z
    have hzi : z ≠ i := fun h => (s i).property (h ▸ hBuy z hz)
    have hAvoid : i ∉ p.support := by
      intro hMem
      have hLength := walk_length_ge_via p hMem
      have hDist := dist_ne_zero_iff_ne_and_reachable.mpr ⟨hzi.symm, hG i z⟩
      have hLe := hDepth z hz
      omega
    have hEdge (e : Sym2 (Fin n)) (he : e ∈ p.edges) : e ∈ D.edgeSet := by
      induction e using Sym2.ind with
      | h a b =>
        have ha : a ≠ i := fun h => hAvoid (h ▸ p.fst_mem_support_of_mem_edges he)
        have hb : b ≠ i := fun h => hAvoid (h ▸ p.snd_mem_support_of_mem_edges he)
        exact redirect_preserves_adj (p.adj_of_mem_edges he) (Or.inl ha) (Or.inl hb)
    exact ⟨p.transfer D hEdge, by rw [Walk.length_transfer, hp]⟩

private theorem one_purchase_of_redirect_bound (α : ℝ≥0) (s : Profile n)
    (hα : (n : ℝ≥0) < α) {i r : Fin n} (sold : Finset (Fin n))
    (hSum : distanceSum (graph s) r ≤ distanceSum (graph s) i)
    (hRedirect : distanceSum (graph s) i + (α : ℝ) * (sold.card : ℝ) ≤
      distanceSum (graph s) r + ((n - 1 : ℕ) : ℝ) + (α : ℝ)) :
    sold.card ≤ 1 := by
  by_contra! hLarge
  have hLargeReal : (2 : ℝ) ≤ (sold.card : ℝ) := by
    exact_mod_cast (show 2 ≤ sold.card by omega)
  have hCount := mul_le_mul_of_nonneg_left hLargeReal (NNReal.zero_le_coe : 0 ≤ (α : ℝ))
  have hN : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hαReal : (n : ℝ) < α := by exact_mod_cast hα
  linarith

/-- If the target has no greater total distance, at most one purchase can
point to a vertex no further from that target than the buyer. -/
theorem nash_at_most_one_purchase_toward_root_of_le_distanceSum (α : ℝ≥0)
    (s : Profile n) (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    {i r : Fin n} (hir : i ≠ r) (hSum : distanceSum (graph s) r ≤ distanceSum (graph s) i)
    (sold : Finset (Fin n)) (hBuy : ∀ z ∈ sold, z ∈ (s i).val)
    (hDepth : ∀ z ∈ sold, (graph s).dist r z ≤ (graph s).dist r i) :
    sold.card ≤ 1 :=
  one_purchase_of_redirect_bound α s hα sold hSum
    (nash_redirect_toward_root_bound α s hne hir sold hBuy hDepth)

/-- Purchases that do not go to a child in the chosen shortest-path tree
can all be redirected to the root. If the root has no greater distance
sum than the buyer, there is at most one such purchase at price above n. -/
theorem nash_at_most_one_purchase_not_to_child (α : ℝ≥0) (s : Profile n)
    (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s) {i r : Fin n} (hir : i ≠ r)
    (hSum : distanceSum (graph s) r ≤ distanceSum (graph s) i)
    (T : ShortestParents (graph s) r)
    (sold : Finset (Fin n)) (hBuy : ∀ z ∈ sold, z ∈ (s i).val)
    (hNotChild : ∀ z ∈ sold, T.parent z ≠ i) :
    sold.card ≤ 1 := by
  let G := graph s
  let D := graph (redirect s i r hir sold)
  have hG := nash_connected (Nat.zero_lt_of_lt i.isLt) α s hne
  have routes (d : ℕ) (z : Fin n) (hd : G.dist r z = d) :
      ∃ p : D.Walk r z, p.length ≤ d := by
    induction d using Nat.strong_induction_on generalizing z with
    | h d ih =>
      by_cases hzRoot : z = r
      · subst z
        exact ⟨.nil, Nat.zero_le _⟩
      by_cases hzBuyer : z = i
      · subst z
        have hAdj : D.Adj r i := (redirect_adj_target s hir sold).symm
        have hdist := dist_ne_zero_iff_ne_and_reachable.mpr ⟨hir.symm, hG r i⟩
        exact ⟨.cons hAdj .nil, by rw [← hd]; exact Nat.one_le_iff_ne_zero.mpr hdist⟩
      · have hParentDepth := T.parent_depth hzRoot
        change G.dist r (T.parent z) + 1 = G.dist r z at hParentDepth
        obtain ⟨p, hp⟩ := ih (G.dist r (T.parent z)) (by omega) (T.parent z) rfl
        have keeps : T.parent z ≠ i ∨ z ∉ sold := by
          by_cases hp : T.parent z = i
          · exact Or.inr (fun hz => hNotChild z hz hp)
          · exact Or.inl hp
        have hAdj : D.Adj (T.parent z) z :=
          redirect_preserves_adj (T.parent_adj hzRoot).symm keeps (Or.inl hzBuyer)
        exact ⟨p.concat hAdj, by rw [Walk.length_concat]; omega⟩
  exact one_purchase_of_redirect_bound α s hα sold hSum
    (nash_redirect_bound s α hne hir sold hBuy (fun z _ => routes (G.dist r z) z rfl))

/-- If a block vertex has an exterior attachment, any other vertex buys
at most two block edges that go no further from that vertex than itself. -/
theorem nash_block_at_most_two_purchases_toward_attachment (α : ℝ≥0) (s : Profile n)
    (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    (hS : IsBiconnectedBlock (graph s) S) {i r : Fin n} (hi : i ∈ S) (hr : r ∈ S)
    (hir : i ≠ r) (hWeight : 1 < (blockAttachment (graph s) S r).card)
    (sold : Finset (Fin n)) (hBuy : ∀ z ∈ sold, z ∈ S ∧ z ∈ (s i).val)
    (hDepth : ∀ z ∈ sold, (blockGraph (graph s) S).dist r z ≤ (blockGraph (graph s) S).dist r i) :
    sold.card ≤ 2 := by
  let G := graph s
  let H := blockGraph G S
  have hG := nash_connected (Nat.zero_lt_of_lt i.isLt) α s hne
  have agree : AgreeOutsideBlock G G S := fun _ _ _ => Iff.rfl
  have hLeaf := nash_weighted_leaf_inequality α s hne hS hr hi hir.symm hWeight
  have hSum : weightedBlockDistance G G S r - weightedBlockDistance G G S i ≤ (α : ℝ) := by
    unfold weightedBlockDistance
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_le_sum (g := fun z => ((blockAttachment G S z).card : ℝ) *
      max 0 ((H.dist r z : ℝ) - (H.dist i z : ℝ))) ?_).trans hLeaf
    intro z _
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _)
  have hAmbient : distanceSum G r - distanceSum G i ≤ (α : ℝ) := by
    rw [hS.distanceSum_eq_weightedBlockDistance_add agree hG hG hr,
      hS.distanceSum_eq_weightedBlockDistance_add agree hG hG hi]
    linarith
  have hRedirect := nash_redirect_toward_root_bound α s hne hir sold
    (fun z hz => (hBuy z hz).2) (fun z hz => by
      rw [← hS.block_dist_after_block_change agree hG hG hr (hBuy z hz).1,
        ← hS.block_dist_after_block_change agree hG hG hr hi]
      exact hDepth z hz)
  by_contra! hLarge
  have hLargeReal : (3 : ℝ) ≤ (sold.card : ℝ) := by
    exact_mod_cast (show 3 ≤ sold.card by omega)
  have hPrice := mul_le_mul_of_nonneg_left hLargeReal (NNReal.zero_le_coe : 0 ≤ (α : ℝ))
  have hN : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hαReal : (n : ℝ) < α := by exact_mod_cast hα
  change distanceSum G i + (α : ℝ) * (sold.card : ℝ) ≤
    distanceSum G r + ((n - 1 : ℕ) : ℝ) + (α : ℝ) at hRedirect
  linarith

#print axioms nash_block_at_most_two_purchases_toward_attachment

/-- Adding a link bounds the distance-sum difference between any two players. -/
theorem nash_distanceSum_sub_le_price_add_order (α : ℝ≥0) (s : Profile n)
    (hne : IsNashEquilibrium α s) {i r : Fin n} (hir : i ≠ r) :
    distanceSum (graph s) r - distanceSum (graph s) i ≤ (α : ℝ) + n := by
  let G := graph s
  have hG := nash_connected (Nat.zero_lt_of_lt i.isLt) α s hne
  let saving (x : Fin n) := max 0 ((G.dist r x : ℝ) - (G.dist i x : ℝ) - 1)
  have hSavings : (∑ x : Fin n, saving x) ≤ (α : ℝ) := by
    by_cases hAdj : G.Adj r i
    · have zeroSaving (x : Fin n) : saving x = 0 := by
        have triangle : G.dist r x ≤ G.dist r i + G.dist i x := hG.dist_triangle
        rw [dist_eq_one_iff_adj.mpr hAdj] at triangle
        have hLe : (G.dist r x : ℝ) ≤ 1 + (G.dist i x : ℝ) := by exact_mod_cast triangle
        exact max_eq_left (by linarith)
      simpa only [zeroSaving, Finset.sum_const_zero] using (NNReal.zero_le_coe : 0 ≤ (α : ℝ))
    · exact nash_addition_distance_bound s α hne hir.symm hAdj
  unfold distanceSum
  rw [← Finset.sum_sub_distrib]
  change (∑ x : Fin n, ((G.dist r x : ℝ) - (G.dist i x : ℝ))) ≤ (α : ℝ) + n
  calc
    _ ≤ ∑ x : Fin n, (saving x + 1) := by
      apply Finset.sum_le_sum
      intro x _
      have h := le_max_right (0 : ℝ) ((G.dist r x : ℝ) - (G.dist i x : ℝ) - 1)
      change _ ≤ max 0 ((G.dist r x : ℝ) - (G.dist i x : ℝ) - 1) + 1
      linarith
    _ = (∑ x : Fin n, saving x) + n := by simp [Finset.sum_add_distrib]
    _ ≤ (α : ℝ) + n := by linarith

/-- Without an attachment assumption, a player still buys at most three edges
whose far endpoints are no further from a fixed target than the player is. -/
theorem nash_at_most_three_purchases_toward_root (α : ℝ≥0) (s : Profile n)
    (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s) {i r : Fin n} (hir : i ≠ r)
    (sold : Finset (Fin n)) (hBuy : ∀ z ∈ sold, z ∈ (s i).val)
    (hDepth : ∀ z ∈ sold, (graph s).dist r z ≤ (graph s).dist r i) :
    sold.card ≤ 3 := by
  have hRedirect := nash_redirect_toward_root_bound α s hne hir sold hBuy hDepth
  have hSum := nash_distanceSum_sub_le_price_add_order α s hne hir
  by_contra! hLarge
  have hLargeReal : (4 : ℝ) ≤ (sold.card : ℝ) := by
    exact_mod_cast (show 4 ≤ sold.card by omega)
  have hCount := mul_le_mul_of_nonneg_left hLargeReal (NNReal.zero_le_coe : 0 ≤ (α : ℝ))
  have hN : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hαReal : (n : ℝ) < α := by exact_mod_cast hα
  linarith

#print axioms nash_at_most_three_purchases_toward_root

end Lax869952Proofs
