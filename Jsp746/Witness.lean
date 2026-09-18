import Jsp746.Graph

namespace Jsp746

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Independently searched 42-edge obstruction; coordinates are actual labels in `[1,17]`. -/
def witnessEdges : List (ℕ × ℕ) :=
  [(1, 3), (1, 5), (1, 7), (1, 11), (1, 13), (1, 15), (2, 5), (2, 6), (2, 10), (2, 13), (3, 6), (3, 8), (3, 10), (3, 12), (3, 17), (4, 7), (4, 10), (4, 11), (4, 12), (4, 13), (5, 9), (5, 12), (5, 16), (6, 7), (6, 11), (6, 15), (7, 9), (7, 17), (8, 9), (8, 13), (8, 14), (8, 15), (9, 10), (9, 11), (10, 15), (10, 16), (11, 14), (12, 14), (13, 16), (14, 16), (15, 17), (16, 17)]

def witnessAdj (a b : Fin 17) : Prop :=
  (a.val + 1, b.val + 1) ∈ witnessEdges ∨
    (b.val + 1, a.val + 1) ∈ witnessEdges

instance : DecidableRel witnessAdj := by
  unfold witnessAdj
  infer_instance

private theorem witness_irreflexive : ∀ a : Fin 17, ¬ witnessAdj a a := by
  decide +kernel

/-- The finite graph on the positive integer labels 1 through 17. -/
def witness : SimpleGraph (Fin 17) where
  Adj := witnessAdj
  symm := by intro a b h; exact h.elim Or.inr Or.inl
  loopless := ⟨witness_irreflexive⟩

instance : DecidableRel witness.Adj := inferInstanceAs (DecidableRel witnessAdj)

/-- The obstruction has exactly 42 unordered edges; no edge-minimality is claimed. -/
theorem witness_edge_count : witness.edgeFinset.card = 42 := by
  decide +kernel

/-- This exhaustive finite check is reduced by the Lean kernel. -/
theorem witness_noTriangle : NoTriangle witness := by
  unfold NoTriangle
  decide +kernel

theorem witness_cliqueFree : witness.CliqueFree 3 :=
  (noTriangle_iff_cliqueFree witness).mp witness_noTriangle

/-- Every eligible positive Schur triple contains an edge. -/
theorem witness_covers_sums : ∀ a b c : Fin 17,
    a.val < b.val → c.val + 1 = (a.val + 1) + (b.val + 1) →
      witness.Adj a b ∨ witness.Adj a c ∨ witness.Adj b c := by
  decide +kernel

theorem witness_noSchurTriple : ¬ HasFiniteSchurTriple witness := by
  rintro ⟨a, b, c, hab, hc, hnab, hnac, hnbc⟩
  exact (witness_covers_sums a b c hab hc).elim hnab (fun h => h.elim hnac hnbc)

theorem seventeen_counterexample :
    ∃ G : SimpleGraph (Fin 17), G.CliqueFree 3 ∧ ¬ HasFiniteSchurTriple G :=
  ⟨witness, witness_cliqueFree, witness_noSchurTriple⟩

end Jsp746
