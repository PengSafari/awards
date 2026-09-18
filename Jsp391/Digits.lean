import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Positional digits, finite reconstruction and convergence. Indices start at zero,
so the zeroth digit is the leading digit of the normalized target. -/
noncomputable section
open scoped BigOperators
open Filter Topology
namespace Jsp391

def digit (g : ℕ) (t : ℝ) (n : ℕ) : ℤ :=
  ⌊t * (g : ℝ) ^ n⌋ - (g : ℤ) * ⌊t * (g : ℝ) ^ n / g⌋

theorem digit_bounds {g : ℕ} (hg : 2 ≤ g) (t : ℝ) (n : ℕ) :
    0 ≤ digit g t n ∧ digit g t n < g := by
  have hg0 : 0 < (g : ℝ) := by exact_mod_cast (by omega : 0 < g)
  let x := t * (g : ℝ) ^ n
  let q : ℤ := ⌊x / g⌋
  have hlow : (q : ℝ) * g ≤ x :=
    (le_div_iff₀ hg0).mp (Int.floor_le (x / g))
  have hhigh : x < ((q : ℝ) + 1) * g :=
    (div_lt_iff₀ hg0).mp (Int.lt_floor_add_one (x / g))
  have hl : (g : ℤ) * q ≤ ⌊x⌋ := Int.le_floor.mpr (by push_cast; nlinarith)
  have hu : ⌊x⌋ < (g : ℤ) * q + g := Int.floor_lt.mpr (by push_cast; nlinarith)
  change 0 ≤ ⌊x⌋ - (g : ℤ) * q ∧ ⌊x⌋ - (g : ℤ) * q < g
  omega

theorem digit_zero {g : ℕ} {t : ℝ} (hg : 2 ≤ g) (ht1 : 1 ≤ t) (htg : t < g) :
    digit g t 0 = ⌊t⌋ := by
  have hg0 : 0 < (g : ℝ) := by exact_mod_cast (by omega : 0 < g)
  have hf : ⌊t / (g : ℝ)⌋ = (0 : ℤ) :=
    Int.floor_eq_zero_iff.mpr ⟨div_nonneg (by linarith) hg0.le,
      (div_lt_one hg0).mpr htg⟩
  simp [digit, hf]

theorem digit_succ {g : ℕ} (hg : 2 ≤ g) (t : ℝ) (n : ℕ) :
    digit g t (n + 1) = ⌊t * (g : ℝ) ^ (n + 1)⌋ - (g : ℤ) * ⌊t * (g : ℝ) ^ n⌋ := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  have hx : t * (g : ℝ) ^ (n + 1) / g = t * (g : ℝ) ^ n := by
    rw [pow_succ, ← mul_assoc, mul_div_cancel_right₀ _ hg0]
  rw [digit, hx]

def partialSum (g : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (digit g t i : ℝ) / (g : ℝ) ^ i

theorem partialSum_eq {g : ℕ} {t : ℝ} (hg : 2 ≤ g) (ht1 : 1 ≤ t) (htg : t < g)
    (n : ℕ) : partialSum g t n = (⌊t * (g : ℝ) ^ n⌋ : ℝ) / (g : ℝ) ^ n := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  induction n with
  | zero => simp [partialSum, digit_zero hg ht1 htg]
  | succ n ih =>
    rw [partialSum, Finset.sum_range_succ]
    change partialSum g t n + _ = _
    rw [ih, digit_succ hg]
    push_cast
    rw [pow_succ]
    field_simp
    ring

theorem partialSum_tendsto {g : ℕ} {t : ℝ} (hg : 2 ≤ g) (ht1 : 1 ≤ t) (htg : t < g) :
    Tendsto (partialSum g t) atTop (𝓝 t) := by
  have hg1 : 1 < (g : ℝ) := by exact_mod_cast (by omega : 1 < g)
  have ht0 : 0 ≤ t := by linarith
  have hlim := (tendsto_nat_floor_mul_div_atTop ht0).comp
    (tendsto_pow_atTop_atTop_of_one_lt hg1)
  have heq : partialSum g t = fun n : ℕ => (⌊t * (g : ℝ) ^ n⌋₊ : ℝ) / (g : ℝ) ^ n := by
    funext n
    rw [partialSum_eq hg ht1 htg]
    rw [← Int.natCast_floor_eq_floor (mul_nonneg ht0 (pow_nonneg (by linarith) n))]
    simp
  rw [heq]
  exact hlim

end Jsp391
