import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.NormNum

namespace Jsp746

/-- The usual triangle-free condition, expressed without an enumeration of vertex subsets. -/
def NoTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c)

theorem noTriangle_iff_cliqueFree {V : Type*} (G : SimpleGraph V) :
    NoTriangle G ↔ G.CliqueFree 3 := by
  classical
  constructor
  · intro h s hs
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact h a b c ⟨hab, hac, hbc⟩
  · intro h a b c habc
    exact h {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr habc)

/-- Positive, distinct summands, with all three vertices pairwise nonadjacent.
The vertex numbered `i : Fin n` carries the positive integer label `i.val + 1`. -/
def HasFiniteSchurTriple {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c : Fin n, a.val < b.val ∧
    c.val + 1 = (a.val + 1) + (b.val + 1) ∧
    ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c

/-- The original assertion restricted to the labeled interval `[1,n]`. -/
def FiniteSchurProperty (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → HasFiniteSchurTriple G

end Jsp746
