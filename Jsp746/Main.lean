import Jsp746.Refutation
import Jsp746.Witness

namespace Jsp746

/-- The checked finite refutation forces an independent positive Schur triple. -/
theorem independent_schur_triple_of_relation (e : ℕ → ℕ → Prop)
    (htri : ∀ i j k, 1 ≤ i → i < j → j < k → k ≤ 18 →
      ¬ (e i j ∧ e i k ∧ e j k)) :
    ∃ a b : ℕ, 1 ≤ a ∧ a < b ∧ a + b ≤ 18 ∧
      ¬ e a b ∧ ¬ e a (a + b) ∧ ¬ e b (a + b) := by
  classical
  by_contra h
  apply sat_refutation e htri
  intro a b ha hab hs
  by_contra he
  apply h
  refine ⟨a, b, ha, hab, hs, ?_, ?_, ?_⟩ <;> tauto

/-- A version allowing any map from integer labels into a triangle-free graph. -/
theorem independent_schur_triple_of_map {V : Type*} (G : SimpleGraph V)
    (hG : G.CliqueFree 3) (f : ℕ → V) :
    ∃ a b : ℕ, 1 ≤ a ∧ a < b ∧ a + b ≤ 18 ∧
      ¬ G.Adj (f a) (f b) ∧ ¬ G.Adj (f a) (f (a + b)) ∧
      ¬ G.Adj (f b) (f (a + b)) := by
  apply independent_schur_triple_of_relation (fun i j => G.Adj (f i) (f j))
  intro i j k _ _ _ _
  exact (noTriangle_iff_cliqueFree G).mpr hG (f i) (f j) (f k)

/-- Full graph-on-natural-numbers assertion, with ordinary addition and distinct positive summands. -/
theorem natural_graph (G : SimpleGraph ℕ) (hG : G.CliqueFree 3) :
    ∃ a b : ℕ, 1 ≤ a ∧ a < b ∧ b < a + b ∧ a + b ≤ 18 ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a (a + b) ∧ ¬ G.Adj b (a + b) := by
  obtain ⟨a, b, ha, hab, hs, h1, h2, h3⟩ :=
    independent_schur_triple_of_map G hG id
  exact ⟨a, b, ha, hab, by omega, hs, h1, h2, h3⟩

/-- The original infinite integer-graph assertion. No finiteness assumption on the graph is made. -/
theorem integer_graph (G : SimpleGraph ℤ) (hG : G.CliqueFree 3) :
    ∃ a b : ℤ, 0 < a ∧ a < b ∧ b < a + b ∧ a + b ≤ 18 ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a (a + b) ∧ ¬ G.Adj b (a + b) := by
  obtain ⟨a, b, ha, hab, hs, h1, h2, h3⟩ :=
    independent_schur_triple_of_map G hG (fun k => (k : ℤ))
  refine ⟨(a : ℤ), (b : ℤ), ?_, ?_, ?_, ?_, h1, ?_, ?_⟩
  · exact_mod_cast (show 0 < a by omega)
  · exact_mod_cast hab
  · exact_mod_cast (show b < a + b by omega)
  · exact_mod_cast hs
  · simpa only [Nat.cast_add] using h2
  · simpa only [Nat.cast_add] using h3

/-- On every finite labeled interval of length at least 18, an independent Schur triple exists. -/
theorem finite_upper {n : ℕ} (hn : 18 ≤ n) : FiniteSchurProperty n := by
  intro G hG
  let f (k : ℕ) : Fin n := ⟨(k - 1) % n, Nat.mod_lt _ (by omega)⟩
  have hf (k : ℕ) (h1 : 1 ≤ k) (h18 : k ≤ 18) : (f k).val + 1 = k := by
    dsimp [f]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨a, b, ha, hab, hs, h1, h2, h3⟩ :=
    independent_schur_triple_of_map G hG f
  have hfa := hf a ha (by omega)
  have hfb := hf b (by omega) (by omega)
  have hfs := hf (a + b) (by omega) hs
  exact ⟨f a, f b, f (a + b), by omega, by omega, h1, h2, h3⟩

/-- Restricting the explicit obstruction gives a counterexample on every shorter interval. -/
theorem finite_lower {n : ℕ} (hn : n ≤ 17) : ¬ FiniteSchurProperty n := by
  intro h
  let f (a : Fin n) : Fin 17 := ⟨a.val, lt_of_lt_of_le a.isLt hn⟩
  let G : SimpleGraph (Fin n) := witness.comap f
  have hG : G.CliqueFree 3 := by
    apply (noTriangle_iff_cliqueFree G).mp
    intro a b c habc
    exact witness_noTriangle (f a) (f b) (f c) habc
  obtain ⟨a, b, c, hab, hc, h1, h2, h3⟩ := h G hG
  apply witness_noSchurTriple
  exact ⟨f a, f b, f c, hab, hc, h1, h2, h3⟩

/-- Exact threshold, including empty and small intervals. -/
theorem finite_threshold (n : ℕ) : FiniteSchurProperty n ↔ 18 ≤ n := by
  constructor
  · intro h
    by_contra hn
    exact finite_lower (by omega) h
  · exact finite_upper

end Jsp746
