import Lax869952Proofs.BlockLayerCount
import Lax869952Proofs.BlockDegreePattern

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped BigOperators NNReal

variable {n : ℕ}

/-- The buyers of edges of the block lying outside the parent tree. -/
noncomputable def offTreeBuyers (s : Profile n) {r : Fin n}
    (T : ShortestParents (graph s) r) (S : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact S.filter fun u => ∃ v, (blockGraph (graph s) S).Adj u v ∧
    v ∈ (s u).val ∧ ¬ T.tree.Adj u v

@[simp]
theorem mem_offTreeBuyers {s : Profile n} {r u : Fin n}
    {T : ShortestParents (graph s) r} {S : Finset (Fin n)} :
    u ∈ offTreeBuyers s T S ↔ u ∈ S ∧ ∃ v, (blockGraph (graph s) S).Adj u v ∧
      v ∈ (s u).val ∧ ¬ T.tree.Adj u v := by
  classical
  simp only [offTreeBuyers, Finset.mem_filter]

/-- If each player buys at most one edge outside the parent tree, the
block's edges are covered by its parent edges and one edge per off-tree buyer. -/
theorem block_edge_card_le_of_unique_offTree_purchases (s : Profile n)
    {S : Finset (Fin n)} {r : Fin n} (T : ShortestParents (graph s) r)
    [DecidableRel (blockGraph (graph s) S).Adj]
    (hUnique : ∀ {u v w : Fin n}, (blockGraph (graph s) S).Adj u v →
      v ∈ (s u).val → ¬ T.tree.Adj u v → (blockGraph (graph s) S).Adj u w →
      w ∈ (s u).val → ¬ T.tree.Adj u w → v = w) :
    (blockGraph (graph s) S).edgeFinset.card ≤ (S.erase r).card + (offTreeBuyers s T S).card := by
  classical
  let H := blockGraph (graph s) S
  let O := offTreeBuyers s T S
  have target (u : Fin n) (hu : u ∈ O) : ∃ v, H.Adj u v ∧ v ∈ (s u).val ∧ ¬ T.tree.Adj u v :=
    (mem_offTreeBuyers.mp hu).2
  let endpoint (u : Fin n) := if hu : u ∈ O then (target u hu).choose else u
  let extras := O.image fun u => s(u, endpoint u)
  let parents := (S.erase r).image fun u => s(u, T.parent u)
  have extra (u v : Fin n) (hadj : H.Adj u v) (hbuy : v ∈ (s u).val) (hoff : ¬ T.tree.Adj u v) :
      s(u, v) ∈ extras := by
    have hu : u ∈ O := mem_offTreeBuyers.mpr ⟨hadj.1, v, hadj, hbuy, hoff⟩
    obtain ⟨hAdj', hBuy', hOff'⟩ := (target u hu).choose_spec
    have he := hUnique hAdj' hBuy' hOff' hadj hbuy hoff
    exact Finset.mem_image.mpr ⟨u, hu, by simp only [endpoint, dif_pos hu, he]⟩
  have parent (u v : Fin n) (hu : u ∈ S) (hne : u ≠ v) (hp : T.parent u = v) :
      s(u, v) ∈ parents := by
    have hur : u ≠ r := by
      intro he
      subst u
      exact hne (T.parent_root.symm.trans hp)
    exact Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨hur, hu⟩, by rw [hp]⟩
  have cover : H.edgeFinset ⊆ parents ∪ extras := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      have hadj : H.Adj u v := mem_edgeFinset.mp he
      by_cases hTree : T.tree.Adj u v
      · apply Finset.mem_union_left
        rcases hTree.2 with hp | hp
        · exact parent u v hadj.1 hTree.ne hp
        · rw [Sym2.eq_swap]
          exact parent v u hadj.2.1 hTree.ne.symm hp
      · apply Finset.mem_union_right
        rcases hadj.2.2 with hu | hv
        · exact extra u v hadj hu hTree
        · rw [Sym2.eq_swap]
          exact extra v u hadj.symm hv (fun h => hTree h.symm)
  calc
    H.edgeFinset.card ≤ (parents ∪ extras).card := Finset.card_le_card cover
    _ ≤ parents.card + extras.card := Finset.card_union_le parents extras
    _ ≤ (S.erase r).card + O.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le

/-- The buyer and the first two ancestors associated with an off-tree purchase. -/
def offTreeBuyerTriple {G : SimpleGraph (Fin n)} {r : Fin n}
    (T : ShortestParents G r) (u : Fin n) : Finset (Fin n) :=
  {u, T.parent u, T.parent (T.parent u)}

theorem nash_layer_one_purchase_unique (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {r x y z : Fin n} (T : ShortestParents (graph s) r) {H : SimpleGraph (Fin n)}
    (hRoot : distanceSum (graph s) r ≤ distanceSum (graph s) x)
    (hy : InOutEdgeLayer s T H 1 x y) (hz : InOutEdgeLayer s T H 1 x z) : y = z := by
  classical
  by_contra hNe
  have hLayer (w : Fin n) (hw : w ∈ ({y, z} : Finset (Fin n))) : InOutEdgeLayerPlus s T H 1 x w := by
    rcases (show w = y ∨ w = z by simpa using hw) with rfl | rfl
    · exact Or.inl hy
    · exact Or.inl hz
  have hCard := nash_layer_purchase_card_le s α hne hα T H hRoot {y, z} (by decide) hLayer
  simp [hNe] at hCard

/-- An out-edge chain that records the buyer of the final off-tree link. -/
private inductive ChainTo (s : Profile n) {r : Fin n}
    (T : ShortestParents (graph s) r) (H : SimpleGraph (Fin n)) : ℕ → Fin n → Fin n → Fin n → Prop
  | out {u v} : H.Adj u v → v ∈ (s u).val → ¬ T.tree.Adj u v → ChainTo s T H 0 u v u
  | down {i u v w x} : H.Adj u v → v ∈ (s u).val → v ≠ r → T.parent v = u →
      ChainTo s T H i v w x → ChainTo s T H (i + 1) u v x

private theorem ChainTo.toOutEdgeChain {s : Profile n} {r : Fin n}
    {T : ShortestParents (graph s) r} {H : SimpleGraph (Fin n)} {i : ℕ} {u v x : Fin n}
    (p : ChainTo s T H i u v x) : OutEdgeChain s T H i u v := by
  induction p with
  | out h hb hOff => exact .out h hb hOff
  | down hadj hb hv hParent _ ih => exact .down hadj hb hv hParent ih

private theorem ChainTo.source_eq_of_first_edge_at_one {s : Profile n} {r : Fin n}
    {T : ShortestParents (graph s) r} {H : SimpleGraph (Fin n)} {i j : ℕ} {u v x y : Fin n}
    (p : ChainTo s T H i u v x) (q : ChainTo s T H j u v y) (hi : i ≤ 1) (hj : j ≤ 1) :
    x = y := by
  cases p with
  | out hadj _ hOff =>
    cases q with
    | out => rfl
    | down _ _ _ hvp _ => exact (hOff ⟨hadj.ne, Or.inr hvp⟩).elim
  | @down i _ _ w _ hadj _ _ hvp p =>
    cases q with
    | out _ _ hOff => exact (hOff ⟨hadj.ne, Or.inr hvp⟩).elim
    | @down j _ _ z _ _ _ _ _ q =>
      obtain rfl : i = 0 := by omega
      obtain rfl : j = 0 := by omega
      cases p
      cases q
      rfl

private theorem ChainTo.source_eq_of_first_edge_at_two {s : Profile n} {r : Fin n}
    {T : ShortestParents (graph s) r} {H : SimpleGraph (Fin n)} {i j : ℕ} {u v x y : Fin n}
    (hRoot : ∀ {a b}, H.Adj a b → distanceSum (graph s) r ≤ distanceSum (graph s) b)
    (α : ℝ≥0) (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    (p : ChainTo s T H i u v x) (q : ChainTo s T H j u v y) (hi : i ≤ 2) (hj : j ≤ 2) :
    x = y := by
  cases p with
  | out hadj _ hOff =>
    cases q with
    | out => rfl
    | down _ _ _ hvp _ => exact (hOff ⟨hadj.ne, Or.inr hvp⟩).elim
  | @down i _ _ w _ hadj _ _ hvp p =>
    cases q with
    | out _ _ hOff => exact (hOff ⟨hadj.ne, Or.inr hvp⟩).elim
    | @down j _ _ z _ _ _ _ _ q =>
      have hi' : i ≤ 1 := by omega
      have hj' : j ≤ 1 := by omega
      have hEq := nash_layer_one_purchase_unique s α hne hα T (hRoot hadj)
        ⟨i, hi', p.toOutEdgeChain⟩ ⟨j, hj', q.toOutEdgeChain⟩
      subst z
      exact p.source_eq_of_first_edge_at_one q hi' hj'

private theorem nash_off_tree_buyer_chain_to (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {S : Finset (Fin n)} (hS : IsBiconnectedBlock (graph s) S) {r : Fin n}
    (hr : r ∈ S) (hRoot : ∀ x ∈ S, distanceSum (graph s) r ≤ distanceSum (graph s) x)
    (T : ShortestParents (graph s) r) {u x : Fin n}
    (hx : x ∈ offTreeBuyers s T S) (hu : u ∈ offTreeBuyerTriple T x) :
    ∃ v, ∃ i ≤ 2, ChainTo s T (blockGraph (graph s) S) i u v x := by
  classical
  have ⟨hxS, y, hAdj, hBuy, hOff⟩ := mem_offTreeBuyers.mp hx
  let a := T.parent x
  let b := T.parent a
  have hG := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  have hDepth := nash_out_edge_depth_ge_three s α hne hα T (Or.inl hBuy) hOff
  have hxNe : x ≠ r := fun he => by simp [he] at hDepth
  have haNe : a ≠ r := by
    have h := T.parent_depth hxNe
    change (graph s).dist r a + 1 = (graph s).dist r x at h
    intro he
    rw [he, dist_self] at h
    omega
  have haMem := hS.parent_mem hG hr hxS hxNe T
  have hbMem := hS.parent_mem hG hr haMem haNe T
  have haAdj : (blockGraph (graph s) S).Adj a x := ⟨haMem, hxS, (T.parent_adj hxNe).symm⟩
  have hbAdj : (blockGraph (graph s) S).Adj b a := ⟨hbMem, haMem, (T.parent_adj haNe).symm⟩
  obtain ⟨hBuyA, hBuyB⟩ := nash_block_off_tree_first_two_parent_purchases s α hne hα hS hr hRoot
    T hAdj hBuy hOff
  have hLayer₀ : ChainTo s T (blockGraph (graph s) S) 0 x y x := .out hAdj hBuy hOff
  have hLayer₁ : ChainTo s T (blockGraph (graph s) S) 1 a x x := .down haAdj hBuyA hxNe rfl hLayer₀
  rcases (show u = x ∨ u = a ∨ u = b by simpa [offTreeBuyerTriple, a, b] using hu) with
      rfl | rfl | rfl
  · exact ⟨y, 0, by decide, hLayer₀⟩
  · exact ⟨x, 1, by decide, hLayer₁⟩
  · exact ⟨a, 2, le_rfl, .down hbAdj hBuyB haNe rfl hLayer₁⟩

/-- The number of off-tree triples passing through a vertex is at most
one plus its indicator for buying two edges in X₂. -/
theorem nash_off_tree_triple_load_le (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * (n : ℝ≥0) < α)
    {S : Finset (Fin n)} (hS : IsBiconnectedBlock (graph s) S) {r : Fin n}
    (hr : r ∈ S) (hRoot : ∀ x ∈ S, distanceSum (graph s) r ≤ distanceSum (graph s) x)
    (T : ShortestParents (graph s) r) {u : Fin n} (hu : u ∈ S)
    [Decidable (u ∈ twoSecondLayerBuyers s T S)] [∀ x : Fin n, Decidable (u ∈ offTreeBuyerTriple T x)] :
    ((offTreeBuyers s T S).filter fun x => u ∈ offTreeBuyerTriple T x).card
      ≤ 1 + if u ∈ twoSecondLayerBuyers s T S then 1 else 0 := by
  classical
  let H := blockGraph (graph s) S
  let O := (offTreeBuyers s T S).filter fun x => u ∈ offTreeBuyerTriple T x
  let P := (Finset.univ : Finset (Fin n)).filter fun v => InOutEdgeLayer s T H 2 u v
  have chains (x : Fin n) (hx : x ∈ O) : ∃ v, ∃ i ≤ 2, ChainTo s T H i u v x :=
    nash_off_tree_buyer_chain_to s α hne hα hS hr hRoot T (Finset.mem_filter.mp hx).1
      (Finset.mem_filter.mp hx).2
  let f (x : Fin n) := if hx : x ∈ O then (chains x hx).choose else x
  have fChain (x : Fin n) (hx : x ∈ O) : ∃ i ≤ 2, ChainTo s T H i u (f x) x := by
    simpa only [f, dif_pos hx] using (chains x hx).choose_spec
  have hMaps : Set.MapsTo f (↑O : Set (Fin n)) (↑P : Set (Fin n)) := by
    intro x hx
    obtain ⟨i, hi, h⟩ := fChain x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, hi, h.toOutEdgeChain⟩⟩
  have hInj : (↑O : Set (Fin n)).InjOn f := by
    intro x hx y hy he
    obtain ⟨i, hi, hp⟩ := fChain x hx
    obtain ⟨j, hj, hq⟩ := fChain y hy
    rw [← he] at hq
    have rootBound {a b : Fin n} (hab : H.Adj a b) : distanceSum (graph s) r ≤ distanceSum (graph s) b :=
      hRoot _ hab.2.1
    exact hp.source_eq_of_first_edge_at_two rootBound α hne hα hq hi hj
  have hO := Finset.card_le_card_of_injOn f hMaps hInj
  have hP : P.card ≤ 2 := by
    have h := nash_layer_purchase_card_le s α hne hα T H (hRoot u hu) P (k := 2) le_rfl
      (fun v hv => Or.inl (Finset.mem_filter.mp hv).2)
    simpa using h
  change O.card ≤ 1 + if u ∈ twoSecondLayerBuyers s T S then 1 else 0
  by_cases hTwo : u ∈ twoSecondLayerBuyers s T S
  · simp only [if_pos hTwo]
    omega
  · have hOne : P.card ≤ 1 := by
      by_contra hMany
      obtain ⟨v, hv, w, hw, hNe⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
      exact hTwo (Finset.mem_filter.mpr ⟨hu, v, w, hNe, (Finset.mem_filter.mp hv).2,
        (Finset.mem_filter.mp hw).2⟩)
    simp only [if_neg hTwo, add_zero]
    omega

#print axioms nash_off_tree_triple_load_le

end Lax869952Proofs
