import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The alternating recurrence in Stoll's digit construction

The mathematical construction is Thomas Stoll's Theorem 1.3 (2005).
This implementation indexes the paper's `u₁` by zero. It verifies the actual
recursive sequence through a pair of transition identities.
-/

namespace Jsp391

noncomputable section

def alpha (g : ℕ) (t : ℝ) : ℝ :=
  (g : ℝ) / (((g : ℝ) - 1) * (t + g))

def beta (g : ℕ) (t : ℝ) : ℝ :=
  ((g : ℝ) - 1) * (t + g)

def IsAdmissible (g : ℕ) (e : ℝ) : Prop :=
  -1 / (g : ℝ) ≤ e ∧ e < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g

def trajectory (g : ℕ) (t e : ℝ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      if n % 2 = 0 then
        ⌊alpha g t * ((trajectory g t e n : ℝ) + e)⌋
      else
        ⌊beta g t * ((trajectory g t e n : ℝ) + 1 / ((g : ℝ) - 1))⌋

/-- Integer geometric sums avoid any convention about integer division. -/
def repunit (g : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => repunit g n + (g : ℤ) ^ n

theorem repunit_identity (g n : ℕ) :
    ((g : ℝ) - 1) * (repunit g n : ℝ) = (g : ℝ) ^ n - 1 := by
  induction n with
  | zero => simp [repunit]
  | succ n ih =>
      simp only [repunit, Int.cast_add, Int.cast_pow, Int.cast_natCast, pow_succ]
      nlinarith

theorem admissible_scaled {g : ℕ} {e : ℝ} (hg : 2 ≤ g)
    (he : IsAdmissible g e) :
    -1 ≤ (g : ℝ) * e ∧ (g : ℝ) * e < ((g : ℝ) + 1) * ((g : ℝ) - 2) := by
  have hp : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  exact ⟨by simpa [mul_comm] using (div_le_iff₀ hp).mp he.1,
    by simpa [mul_comm] using (lt_div_iff₀ hp).mp he.2⟩

theorem first_step (g : ℕ) (t e : ℝ) (hg : 2 ≤ g)
    (ht : 1 ≤ t) (he : IsAdmissible g e) :
    trajectory g t e 1 = 0 := by
  have hgr : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hd : 0 < ((g : ℝ) - 1) * (t + g) := mul_pos (by linarith) (by linarith)
  obtain ⟨hel, heu⟩ := admissible_scaled hg he
  simp only [trajectory, Nat.zero_mod, ↓reduceIte, Int.cast_one]
  apply Int.floor_eq_iff.mpr
  simp only [Int.cast_zero, zero_add, alpha, div_mul_eq_mul_div]
  constructor
  · apply div_nonneg _ hd.le
    nlinarith
  · apply (div_lt_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ (g : ℝ) - 1 by linarith) (show 0 ≤ t - 1 by linarith)]

theorem expansion_step (g n : ℕ) (t : ℝ) (hg : 2 ≤ g) :
    ⌊beta g t * ((repunit g n : ℝ) + 1 / ((g : ℝ) - 1))⌋ =
      ⌊(t + g) * (g : ℝ) ^ n⌋ := by
  have hn : (g : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ g := by exact_mod_cast hg
    linarith
  congr 1
  dsimp [beta]
  have hi := repunit_identity g n
  field_simp
  rw [hi]
  ring

/-- The cancellation after clearing the positive denominator is the key step.
The only error bounds used are `floor x ≤ x < floor x + 1`. -/
theorem contraction_step (g n : ℕ) (t e : ℝ) (hg : 2 ≤ g)
    (ht : 1 ≤ t) (he : IsAdmissible g e) :
    ⌊alpha g t * ((⌊(t + g) * (g : ℝ) ^ n⌋ : ℤ) + e)⌋ =
      repunit g (n + 1) := by
  have hgr : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < g := by linarith
  have hd : 0 < ((g : ℝ) - 1) * (t + g) := mul_pos (by linarith) (by linarith)
  obtain ⟨hel, heu⟩ := admissible_scaled hg he
  have hlo := Int.floor_le ((t + g) * (g : ℝ) ^ n)
  have hhi := Int.lt_floor_add_one ((t + g) * (g : ℝ) ^ n)
  have hlo' := mul_le_mul_of_nonneg_left hlo hgpos.le
  have hhi' := mul_lt_mul_of_pos_left hhi hgpos
  have hr := repunit_identity g (n + 1)
  rw [pow_succ] at hr
  have hr' := congrArg (fun x : ℝ => x * (t + g)) hr
  apply Int.floor_eq_iff.mpr
  rw [alpha, div_mul_eq_mul_div]
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (div_lt_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ (g : ℝ) - 2 by linarith) (show 0 ≤ t - 1 by linarith)]

/-- Both halves of each pair are obtained from the original recursion. -/
theorem trajectory_pairs (g : ℕ) (t e : ℝ) (hg : 2 ≤ g)
    (ht : 1 ≤ t) (he : IsAdmissible g e) (n : ℕ) :
    trajectory g t e (2 * n + 1) = repunit g n ∧
      trajectory g t e (2 * n + 2) = ⌊(t + g) * (g : ℝ) ^ n⌋ := by
  have expand (k : ℕ) (hk : trajectory g t e (2 * k + 1) = repunit g k) :
      trajectory g t e (2 * k + 2) = ⌊(t + g) * (g : ℝ) ^ k⌋ := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, trajectory]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod,
      Nat.one_mod, zero_add, one_ne_zero, ↓reduceIte, hk]
    exact expansion_step g k t hg
  induction n with
  | zero =>
      have h0 : trajectory g t e (2 * 0 + 1) = repunit g 0 := by
        simpa [repunit] using first_step g t e hg ht he
      exact ⟨h0, expand 0 h0⟩
  | succ n ih =>
      have hnext : trajectory g t e (2 * (n + 1) + 1) = repunit g (n + 1) := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by omega, trajectory]
        simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod,
          zero_add, ↓reduceIte, ih.2]
        exact contraction_step g n t e hg ht he
      exact ⟨hnext, expand (n + 1) hnext⟩

theorem expanded_floor (g n : ℕ) (t : ℝ) :
    ⌊(t + g) * (g : ℝ) ^ n⌋ =
      (g : ℤ) ^ (n + 1) + ⌊t * (g : ℝ) ^ n⌋ := by
  have hid : (t + g) * (g : ℝ) ^ n =
      t * (g : ℝ) ^ n + (((g : ℤ) ^ (n + 1) : ℤ) : ℝ) := by
    push_cast
    rw [pow_succ]
    ring
  rw [hid, Int.floor_add_intCast]
  ring

theorem leading_floor (g : ℕ) (t : ℝ) (hg : 2 ≤ g)
    (ht : 1 ≤ t) (htg : t < g) : ⌊t / (g : ℝ)⌋ = (0 : ℤ) := by
  have hp : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  apply Int.floor_eq_iff.mpr
  simp only [Int.cast_zero, zero_add]
  exact ⟨div_nonneg (by linarith) hp.le, (div_lt_one hp).mpr htg⟩

/-- Uniform extraction, including the leading digit (`n = 0`). -/
theorem extraction (g : ℕ) (t e : ℝ) (hg : 2 ≤ g)
    (ht : 1 ≤ t) (htg : t < g) (he : IsAdmissible g e) (n : ℕ) :
    trajectory g t e (2 * n + 2) - (g : ℤ) * trajectory g t e (2 * n) =
      ⌊t * (g : ℝ) ^ n⌋ - (g : ℤ) * ⌊t * (g : ℝ) ^ n / (g : ℝ)⌋ := by
  have hu := (trajectory_pairs g t e hg ht he n).2
  rw [hu, expanded_floor]
  cases n with
  | zero =>
      simp [trajectory, leading_floor g t hg ht htg]
  | succ n =>
      have hu' := (trajectory_pairs g t e hg ht he n).2
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, hu', expanded_floor]
      have hgn : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
      have hc : t * (g : ℝ) ^ (n + 1) / (g : ℝ) = t * (g : ℝ) ^ n := by
        rw [pow_succ, mul_div_assoc, mul_div_cancel_right₀ _ hgn]
      rw [hc, pow_succ]
      ring

end

end Jsp391
