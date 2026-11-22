import Lax869952Proofs.Redirect
import Lax869952Proofs.RootedShortestPaths

set_option warningAsError true

namespace Lax869952Proofs

open SimpleGraph Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal

lemma walk_length_ge_via {V : Type*} {G : SimpleGraph V} {a b v : V}
    (p : G.Walk a b) (hv : v ∈ p.support) :
    G.dist a v + G.dist v b ≤ p.length := by
  obtain ⟨q, t, rfl⟩ := p.mem_support_iff_exists_append.mp hv
  rw [Walk.length_append]
  exact Nat.add_le_add (SimpleGraph.dist_le q) (SimpleGraph.dist_le t)

private lemma shortest_append_parts {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    {a b c : V} (p : G.Walk a b) (q : G.Walk b c)
    (hpq : (p.append q).length = G.dist a c) :
    p.length = G.dist a b ∧ q.length = G.dist b c := by
  rw [Walk.length_append] at hpq
  have hab := SimpleGraph.dist_le p
  have hbc := SimpleGraph.dist_le q
  have hac : G.dist a c ≤ G.dist a b + G.dist b c := hG.dist_triangle
  omega

private lemma transfer_redirect {n : ℕ} {s : Profile n} {i r a b : Fin n} (hir : i ≠ r)
    (sold : Finset (Fin n)) (p : (graph s).Walk a b)
    (havoid : ∀ j ∈ sold, s(i, j) ∉ p.edges) :
    ∃ q : (graph (redirect s i r hir sold)).Walk a b, q.length = p.length := by
  have hkeep : ∀ e ∈ p.edges, e ∈ (graph (redirect s i r hir sold)).edgeSet := by
    intro e
    induction e using Sym2.ind with
    | h x y =>
      intro he
      have hxy : (graph s).Adj x y := p.edges_subset_edgeSet he
      exact redirect_preserves_other_edge hxy (fun j hj heq => havoid j hj (heq ▸ he))
  exact ⟨p.transfer _ hkeep, p.length_transfer hkeep⟩

private lemma transfer_redirect_avoiding_buyer {n : ℕ} {s : Profile n} {i r a b : Fin n}
    (hir : i ≠ r) (sold : Finset (Fin n)) (p : (graph s).Walk a b) (ha : i ∉ p.support) :
    ∃ q : (graph (redirect s i r hir sold)).Walk a b, q.length = p.length :=
  transfer_redirect hir sold p (fun _ _ hh => ha (p.fst_mem_support_of_mem_edges hh))

private lemma redirect_shortest_of_competing_walk {n : ℕ} {s : Profile n}
    (hG : (graph s).Connected) {i r j : Fin n} (hir : i ≠ r) (sold : Finset (Fin n))
    (p : (graph (redirect s i r hir sold)).Walk r j)
    (hp : p.length ≤ (graph s).dist r i + (graph s).dist i j) :
    ∃ q : (graph (redirect s i r hir sold)).Walk r j, q.length ≤ (graph s).dist r j := by
  by_cases hshort : p.length ≤ (graph s).dist r j
  · exact ⟨p, hshort⟩
  · obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist r j
    have hi : i ∉ q.support := fun hi => hshort (hp.trans ((walk_length_ge_via q hi).trans_eq hq))
    obtain ⟨t, ht⟩ := transfer_redirect_avoiding_buyer hir sold q hi
    exact ⟨t, (ht.trans hq).le⟩

/-- Two shortest branches with distinct first and last edges cannot have
both first edges and one chosen last edge purchased forward. -/
private lemma nash_no_shortest_fork {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * ((n - 1 : ℕ) : ℝ≥0) < α)
    {r a b x y z : Fin n} (ha : a ∈ (s r).val) (hb : b ∈ (s r).val) (hab : a ≠ b)
    (hx : z ∈ (s x).val) (hy : (graph s).Adj y z) (hxy : x ≠ y)
    (p : (graph s).Walk a x) (q : (graph s).Walk b y)
    (hp : p.length + 2 = (graph s).dist r z)
    (hq : q.length + 2 = (graph s).dist r z) : False := by
  classical
  let G := graph s
  change p.length + 2 = G.dist r z at hp
  change q.length + 2 = G.dist r z at hq
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  have hra : G.Adj r a := Or.inl ha
  have hrb : G.Adj r b := Or.inl hb
  have hxz : G.Adj x z := Or.inl hx
  let P := Walk.cons hra p
  let Q := Walk.cons hrb q
  have hPL : P.length = G.dist r x :=
    (shortest_append_parts hG P hxz.toWalk (by simpa [P] using hp)).1
  have hQL : Q.length = G.dist r y :=
    (shortest_append_parts hG Q hy.toWalk (by simpa [Q] using hq)).1
  have hP : P.length = p.length + 1 := rfl
  have hQ : Q.length = q.length + 1 := rfl
  have hxr : x ≠ r := by
    intro he
    have hzero : G.dist r x = 0 := by simp [he]
    omega
  have hyr : y ≠ r := by
    intro he
    have hzero : G.dist r y = 0 := by simp [he]
    omega
  have hzr : z ≠ r := by
    intro he
    rw [he, dist_self] at hp
    omega
  have hswap : distanceSum G x ≤ distanceSum G r + ((n - 1 : ℕ) : ℝ) := by
    let sold : Finset (Fin n) := {z}
    let H := graph (redirect s x r hxr sold)
    have avoids (v : Fin n) (w : G.Walk r v) (hw : w.length < G.dist r z) :
        ∀ j ∈ sold, s(x, j) ∉ w.edges := by
      intro j hj he
      have hje : j = z := Finset.mem_singleton.mp hj
      subst j
      have hz := walk_length_ge_via w (w.snd_mem_support_of_mem_edges he)
      omega
    obtain ⟨P', hP'⟩ := transfer_redirect hxr sold P (avoids x P (by omega))
    obtain ⟨Q', hQ'⟩ := transfer_redirect hxr sold Q (avoids y Q (by omega))
    have hyz : H.Adj y z := by
      apply redirect_preserves_other_edge hy
      intro j hj he
      have hje : j = z := Finset.mem_singleton.mp hj
      subst j
      rcases Sym2.eq_iff.mp he with ⟨he', _⟩ | ⟨_, he'⟩
      · exact hxy he'.symm
      · exact hxz.ne he'.symm
    have hrepair (j : Fin n) (hj : j = x ∨ j ∈ sold) :
        ∃ w : H.Walk r j, w.length ≤ G.dist r j := by
      rcases hj with rfl | hj
      · exact ⟨P', (hP'.trans hPL).le⟩
      · have hje : j = z := Finset.mem_singleton.mp hj
        subst j
        exact ⟨Q'.concat hyz, by rw [Walk.length_concat, hQ']; omega⟩
    have hbuy (j : Fin n) (hj : j ∈ sold) : j ∈ (s x).val :=
      (Finset.mem_singleton.mp hj).symm ▸ hx
    have bound := nash_redirect_bound s α hne hxr sold hbuy hrepair
    simp [sold] at bound
    linarith
  have hdouble : distanceSum G r + (α : ℝ) ≤ distanceSum G x + ((n - 1 : ℕ) : ℝ) := by
    let sold : Finset (Fin n) := {a, b}
    let H := graph (redirect s r x hxr.symm sold)
    have hpr : r ∉ p.support := by
      intro hr
      have hh := walk_length_ge_via p hr
      change G.dist a r + G.dist r x ≤ p.length at hh
      omega
    have hqr : r ∉ q.support := by
      intro hr
      have hh := walk_length_ge_via q hr
      change G.dist b r + G.dist r y ≤ q.length at hh
      omega
    obtain ⟨p', hp'⟩ := transfer_redirect_avoiding_buyer hxr.symm sold p hpr
    obtain ⟨q', hq'⟩ := transfer_redirect_avoiding_buyer hxr.symm sold q hqr
    have hxz' : H.Adj x z := redirect_preserves_adj hxz (Or.inl hxr) (Or.inl hzr)
    have hyz' : H.Adj y z := redirect_preserves_adj hy (Or.inl hyr) (Or.inl hzr)
    have hrepair (j : Fin n) (hj : j = r ∨ j ∈ sold) :
        ∃ w : H.Walk x j, w.length ≤ G.dist x j := by
      rcases hj with he | hj
      · subst j
        have hrx : H.Adj r x := redirect_adj_target s hxr.symm sold
        exact ⟨hrx.symm.toWalk, by simpa using Nat.succ_le_of_lt (hG.pos_dist_of_ne hxr)⟩
      · have hj' : j = a ∨ j = b := by simpa [sold] using hj
        rcases hj' with he | he
        · subst j
          apply redirect_shortest_of_competing_walk hG hxr.symm sold p'.reverse
          rw [Walk.length_reverse, hp', SimpleGraph.dist_comm (u := x) (v := r)]
          change p.length ≤ G.dist r x + G.dist r a
          omega
        · subst j
          apply redirect_shortest_of_competing_walk hG hxr.symm sold
            (Walk.cons hxz' (Walk.cons hyz'.symm q'.reverse))
          rw [Walk.length_cons, Walk.length_cons, Walk.length_reverse, hq',
            SimpleGraph.dist_comm (u := x) (v := r)]
          change q.length + 1 + 1 ≤ G.dist r x + G.dist r b
          rw [dist_eq_one_iff_adj.mpr hrb]
          omega
    have hbuy (j : Fin n) (hj : j ∈ sold) : j ∈ (s r).val := by
      have hj' : j = a ∨ j = b := by simpa [sold] using hj
      rcases hj' with rfl | rfl
      · exact ha
      · exact hb
    have hcard : sold.card = 2 := by simp [sold, hab]
    have bound := nash_redirect_bound s α hne hxr.symm sold hbuy hrepair
    rw [hcard] at bound
    norm_num at bound
    linarith
  have hprice : 2 * ((n - 1 : ℕ) : ℝ) < (α : ℝ) := by exact_mod_cast hα
  linarith

/-- Every step from a vertex is along an edge purchased by that vertex. -/
def PurchaseDirected {n : ℕ} (s : Profile n) {x y : Fin n} (p : (graph s).Walk x y) : Prop :=
  ∀ d ∈ p.darts, d.snd ∈ (s d.fst).val

@[simp]
lemma purchaseDirected_cons {n : ℕ} {s : Profile n} {x y z : Fin n}
    (h : (graph s).Adj x y) (p : (graph s).Walk y z) :
    PurchaseDirected s (.cons h p) ↔ y ∈ (s x).val ∧ PurchaseDirected s p := by
  simp [PurchaseDirected, Walk.darts_cons]

@[simp]
lemma purchaseDirected_concat {n : ℕ} {s : Profile n} {x y z : Fin n}
    (h : (graph s).Adj y z) (p : (graph s).Walk x y) :
    PurchaseDirected s (p.concat h) ↔ PurchaseDirected s p ∧ z ∈ (s y).val := by
  simp [PurchaseDirected, List.concat_eq_append, or_imp, forall_and]

/-- At high prices there is at most one purchase-directed shortest path
from any fixed start to any fixed destination. -/
theorem nash_purchase_directed_geodesic_unique {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * ((n - 1 : ℕ) : ℝ≥0) < α)
    {r z : Fin n} (p q : (graph s).Walk r z)
    (hp : p.length = (graph s).dist r z) (hq : q.length = (graph s).dist r z)
    (hpd : PurchaseDirected s p) (hqd : PurchaseDirected s q) : p = q := by
  classical
  let G := graph s
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt r.isLt) α s hne
  suffices h : ∀ k (r z : Fin n) (p q : G.Walk r z),
      G.dist r z = k → p.length = G.dist r z → q.length = G.dist r z →
      PurchaseDirected s p → PurchaseDirected s q → p = q from h _ r z p q rfl hp hq hpd hqd
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro r z p q hk hp hq hpd hqd
    by_cases hsmall : k ≤ 1
    · exact Walk.eq_of_length_le_one (by omega) (by omega)
    have hpos : 1 < G.dist r z := by omega
    cases p with
    | nil => simp at hpos
    | @cons _ a _ hra pa =>
      cases q with
      | nil => simp at hpos
      | @cons _ b _ hrb qb =>
        obtain ⟨ha, hpa⟩ := (purchaseDirected_cons hra pa).mp hpd
        obtain ⟨hb, hqb⟩ := (purchaseDirected_cons hrb qb).mp hqd
        have hplen : pa.length + 1 = k := by simpa [hk] using hp
        have hqlen : qb.length + 1 = k := by simpa [hk] using hq
        by_cases hab : a = b
        · subst b
          have hp₂ := (shortest_append_parts hG hra.toWalk pa (by simpa using hp)).2
          have hq₂ := (shortest_append_parts hG hrb.toWalk qb (by simpa using hq)).2
          have he := ih pa.length (by omega) a z pa qb hp₂.symm hp₂ hq₂ hpa hqb
          rw [he]
        · obtain ⟨x, px, hxz, hpx⟩ : ∃ (x : Fin n) (t : G.Walk a x) (h : G.Adj x z),
                pa = t.concat h := by
              cases pa with
              | nil => simp at hplen; omega
              | cons hadj tail => exact Walk.exists_cons_eq_concat hadj tail
          obtain ⟨y, qy, hyz, hqy⟩ : ∃ (y : Fin n) (t : G.Walk b y) (h : G.Adj y z),
                qb = t.concat h := by
              cases qb with
              | nil => simp at hqlen; omega
              | cons hadj tail => exact Walk.exists_cons_eq_concat hadj tail
          subst pa
          subst qb
          rw [← Walk.concat_cons] at hp hq ⊢
          have hx := ((purchaseDirected_concat hxz px).mp hpa).2
          by_cases hxy : x = y
          · subst y
            have hp₁ := (shortest_append_parts hG (.cons hra px) hxz.toWalk hp).1
            have hq₁ := (shortest_append_parts hG (.cons hrb qy) hyz.toWalk hq).1
            have hp' : PurchaseDirected s (.cons hra px) :=
              (purchaseDirected_cons hra px).mpr ⟨ha, ((purchaseDirected_concat hxz px).mp hpa).1⟩
            have hq' : PurchaseDirected s (.cons hrb qy) :=
              (purchaseDirected_cons hrb qy).mpr ⟨hb, ((purchaseDirected_concat hyz qy).mp hqb).1⟩
            have hlen : (Walk.cons hra px).length < k := by
              rw [Walk.length_concat] at hp
              omega
            have he := ih _ hlen r x _ _ hp₁.symm hp₁ hq₁ hp' hq'
            rw [he]
            rfl
          · exact (nash_no_shortest_fork s α hne hα ha hb hab hx hyz hxy px qy
              (by simpa [Nat.add_assoc] using hp) (by simpa [Nat.add_assoc] using hq)).elim

#print axioms nash_purchase_directed_geodesic_unique

/-- In equilibrium at high prices, one shortest-path tree contains every
purchase-directed shortest path from its root. -/
theorem exists_purchase_directed_shortest_parents {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hα : 2 * ((n - 1 : ℕ) : ℝ≥0) < α)
    (root : Fin n) :
    ∃ T : ShortestParents (graph s) root, ∀ {x} (p : (graph s).Walk root x),
      p.length = (graph s).dist root x → PurchaseDirected s p →
      ∀ e ∈ p.edges, e ∈ T.tree.edgeSet := by
  classical
  let G := graph s
  have hG : G.Connected := nash_connected (Nat.zero_lt_of_lt root.isLt) α s hne
  let base := chooseShortestParents hG root
  let preferred (x y : Fin n) : Prop :=
    ∃ p : G.Walk root y, PurchaseDirected s p ∧ x ∈ (s y).val ∧
      p.length + 1 = G.dist root x
  let parent (x : Fin n) : Fin n :=
    if h : ∃ y, preferred x y then h.choose else base.parent x
  have hnone : ¬ ∃ y, preferred root y := by
    rintro ⟨y, p, _, _, hp⟩
    simp at hp
  have hdepth (x y : Fin n) (hy : preferred x y) : G.dist root y + 1 = G.dist root x := by
    obtain ⟨p, _, h, hp⟩ := hy
    have hadj : G.Adj y x := Or.inl h
    have hlen := (shortest_append_parts hG p hadj.toWalk (by simpa using hp)).1
    rwa [hlen] at hp
  let T : ShortestParents G root := {
    parent := parent
    parent_root := by simp [parent, hnone, base.parent_root]
    parent_adj := by
      intro x hx
      unfold parent
      split
      · rename_i h
        obtain ⟨_, _, hbuy, _⟩ := h.choose_spec
        exact Or.inr hbuy
      · exact base.parent_adj hx
    parent_depth := by
      intro x hx
      unfold parent
      split
      · rename_i h
        exact hdepth x _ h.choose_spec
      · exact base.parent_depth hx }
  have hparent {x y : Fin n} (h : preferred x y) : T.parent x = y := by
    have he : ∃ z, preferred x z := ⟨y, h⟩
    change parent x = y
    unfold parent
    rw [dif_pos he]
    obtain ⟨p, hpd, hpBuy, hp⟩ := he.choose_spec
    obtain ⟨q, hqd, hqBuy, hq⟩ := h
    have hpx : G.Adj he.choose x := Or.inl hpBuy
    have hqx : G.Adj y x := Or.inl hqBuy
    have hsame := nash_purchase_directed_geodesic_unique s α hne hα
      (p.concat hpx) (q.concat hqx) (by simpa using hp) (by simpa using hq)
      ((purchaseDirected_concat hpx p).mpr ⟨hpd, hpBuy⟩)
      ((purchaseDirected_concat hqx q).mpr ⟨hqd, hqBuy⟩)
    exact (Walk.concat_inj hsame).choose
  have hall : ∀ k x (p : G.Walk root x), p.length = k → p.length = G.dist root x →
      PurchaseDirected s p → ∀ e ∈ p.edges, e ∈ T.tree.edgeSet := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x p hk hp hd e he
      obtain ⟨y, q, hyx, rfl⟩ : ∃ (y : Fin n) (q : G.Walk root y) (h : G.Adj y x),
          p = q.concat h := by
        cases p with
        | nil => simp at he
        | cons hadj tail => exact Walk.exists_cons_eq_concat hadj tail
      obtain ⟨hqd, hx⟩ := (purchaseDirected_concat hyx q).mp hd
      have hlen : q.length + 1 = G.dist root x := by simpa using hp
      have hshort := (shortest_append_parts hG q hyx.toWalk hp).1
      have hk' : q.length < k := by rw [← hk, Walk.length_concat]; omega
      rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact ih _ hk' y q rfl hshort hqd e he
      · exact ⟨hyx.ne, Or.inr (hparent ⟨q, hqd, hx, hlen⟩)⟩
  exact ⟨T, fun p => hall p.length _ p rfl⟩

#print axioms exists_purchase_directed_shortest_parents

end Lax869952Proofs
