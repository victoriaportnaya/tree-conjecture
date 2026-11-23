import Lax869952.TreeAtDoublePrice
import Lax869952.GirthAtPopulationPrice
import Lax869952.SmallGames
import Lax869952.ReceiverDeletionBound
import Lax869952.LeafAdditionInequality
import Lax869952Proofs.CycleBlocks
import Lax869952Proofs.ReceiverCredits
import Lax869952Proofs.ShortCycleBounds
import Lax869952Proofs.TreeTheorem
import Lax869952Proofs.WeightedBlocks

namespace Lax869952Proofs

open Lax869952 Lax869952.NetworkCreationGame Lax869952.NashEquilibrium
open scoped NNReal BigOperators

private theorem of_archive_block {V : Type*} {G : SimpleGraph V} {S : Finset V}
    (h : BlockGeometry.IsBiconnectedBlock G S) : IsBiconnectedBlock G S :=
  ⟨⟨h.twoConnected.card_ge_three, @h.twoConnected.walk⟩,
    fun T hST hT => h.maximal T hST ⟨hT.card_ge_three, @hT.walk⟩⟩

/--
---
conclusion: Lax869952.TreeAtDoublePrice.statement
---
The argument passes to a cyclic maximal biconnected block and a compatible shortest-path tree. Layered deviations bound the repeated purchase incidences and the resulting count contradicts the block degree sum.
-/
theorem tree_above_twice_population {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 2 * (n : ℝ≥0) < α)
    (s : Profile n) (hne : IsNashEquilibrium α s) : (graph s).IsTree :=
  nash_tree_of_two_n_lt_alpha hn α hα s hne

#print axioms tree_above_twice_population

/--
---
conclusion: Lax869952.GirthAtPopulationPrice.statement
---
After excluding triangles and squares, use the certificates for isometric cycles of length five, six and seven. Lean checks the normalized distance labels, orientation coverage and weighted deviation inequalities. Any shortest cycle of the equilibrium graph is isometric.
-/
theorem girth_at_population_price {n : ℕ} (s : Profile n) (α : ℝ≥0)
    (hα : (n : ℝ≥0) < α) (hne : IsNashEquilibrium α s)
    {u : Fin n} (p : (graph s).Walk u u) (hp : p.IsCycle) : 8 ≤ p.length :=
  nash_cycle_length_ge_eight s α hα hne p hp

#print axioms girth_at_population_price

/--
---
conclusion: Lax869952.SmallGames.statement
---
In a cyclic block at the stated price, some vertex has block degree at least three. The girth-eight condition then requires at least eleven block vertices.
-/
theorem tree_for_up_to_ten_players {n : ℕ} (hn : 0 < n) (hsmall : n ≤ 10)
    (s : Profile n) (α : ℝ≥0) (hα : (n : ℝ≥0) < α)
    (hne : IsNashEquilibrium α s) : (graph s).IsTree :=
  nash_tree_of_le_ten_at_n hn hsmall s α hα hne

#print axioms tree_for_up_to_ten_players

/--
---
conclusion: Lax869952.ReceiverDeletionBound.statement
---
Compare the equal-cost swap past the receiver with deletion of the edge. Two destinations on the complementary cycle arc improve the standard deletion estimate by two and four units, respectively.
-/
theorem receiver_deletion_bound {n : ℕ} {S : Finset (Fin n)} (s : Profile n) (α : ℝ≥0)
    (hne : IsNashEquilibrium α s) (hS : BlockGeometry.IsBiconnectedBlock (graph s) S)
    [blockDecidable : DecidableRel (BlockGeometry.blockGraph (graph s) S).Adj]
    (girth : ∀ {x}, (p : (graph s).Walk x x) → p.IsCycle → 8 ≤ p.length)
    {u v w : Fin n} (huv : (BlockGeometry.blockGraph (graph s) S).Adj u v)
    (hvw : (BlockGeometry.blockGraph (graph s) S).Adj v w) (huw : u ≠ w)
    (hdegree : (BlockGeometry.blockGraph (graph s) S).degree v = 2)
    (hBuy : v ∈ (s u).val)
    (c : (BlockGeometry.blockGraph (graph s) S).Walk v v) (hc : c.IsCycle) :
    (α : ℝ) + 6 ≤ 2 * ((c.length : ℝ) - 3) *
      ((BlockGeometry.blockAttachment (graph s) S v).card : ℝ) :=
  @nash_receiver_cycle_bound_with_credits n S s α hne (of_archive_block hS)
    blockDecidable girth u v w huv hvw huw hdegree hBuy c hc

#print axioms receiver_deletion_bound

/--
---
conclusion: Lax869952.LeafAdditionInequality.statement
---
Choose a player outside the block attached at $v$. A link from that player to $r$ saves at least the positive part of the difference in block distances for each destination. Nash equilibrium bounds the sum of these savings by the edge price.
-/
theorem leaf_addition_inequality {n : ℕ} {S : Finset (Fin n)} (α : ℝ≥0) (s : Profile n)
    (hne : IsNashEquilibrium α s) (hS : BlockGeometry.IsBiconnectedBlock (graph s) S)
    {v r : Fin n} (hv : v ∈ S) (hr : r ∈ S) (hvr : v ≠ r)
    (hWeight : 1 < (BlockGeometry.blockAttachment (graph s) S v).card) :
    (∑ z ∈ S, ((BlockGeometry.blockAttachment (graph s) S z).card : ℝ) *
      max 0 (((BlockGeometry.blockGraph (graph s) S).dist v z : ℝ) -
        ((BlockGeometry.blockGraph (graph s) S).dist r z : ℝ))) ≤ (α : ℝ) :=
  nash_weighted_leaf_inequality α s hne (of_archive_block hS) hv hr hvr hWeight

#print axioms leaf_addition_inequality

end Lax869952Proofs
