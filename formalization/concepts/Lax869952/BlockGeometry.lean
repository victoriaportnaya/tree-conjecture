import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Powerset

/-!
---
title: Maximal biconnected blocks and their attachment weights
type: definition
---
A block is a maximal vertex set of size at least three that stays connected
after removal of any one vertex. The block graph is induced on that set
and retains the ambient vertex type. The attachment of a block vertex $v$
contains each player with a walk whose first entry into the block is $v$.
Its weight is the cardinality of that attachment.
-/

namespace Lax869952.BlockGeometry

variable {V : Type*} {G : SimpleGraph V}

/-- The induced two-connected vertex set, expressed in ambient walks. -/
structure TwoConnectedOn (G : SimpleGraph V) (S : Finset V) : Prop where
  card_ge_three : 3 ≤ S.card
  walk (z : V) {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ p : G.Walk x y, (∀ a ∈ p.support, a ∈ S) ∧ z ∉ p.support

/-- Maximality excludes bridge blocks. -/
structure IsBiconnectedBlock (G : SimpleGraph V) (S : Finset V) : Prop where
  twoConnected : TwoConnectedOn G S
  maximal (T : Finset V) : S ⊆ T → TwoConnectedOn G T → T ⊆ S

def blockGraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph V :=
  ((⊤ : G.Subgraph).induce (↑S : Set V)).spanningCoe

def FirstEntryInto (S : Finset V) {x y : V} (p : G.Walk x y) : Prop :=
  ∀ a ∈ p.support, a ∈ S → a = y

noncomputable def blockAttachment {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun x => ∃ p : G.Walk x v, FirstEntryInto S p)

end Lax869952.BlockGeometry
