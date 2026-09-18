import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Normalization for Stoll's digit recurrence, including targets below one. -/
noncomputable section
namespace Jsp391

def exponent (g : ℕ) (w : ℝ) : ℤ := ⌊Real.logb g w⌋

def normalized (g : ℕ) (w : ℝ) : ℝ := w / (g : ℝ) ^ exponent g w

theorem normalized_bounds {g : ℕ} {w : ℝ} (hg : 2 ≤ g) (hw : 0 < w) :
    1 ≤ normalized g w ∧ normalized g w < g := by
  have hg1 : 1 < g := by omega
  have hg0 : 0 < (g : ℝ) := by exact_mod_cast (by omega : 0 < g)
  have hp : 0 < (g : ℝ) ^ Int.log g w := zpow_pos hg0 _
  have hlo := Int.zpow_log_le_self hg1 hw
  have hhi := Int.lt_zpow_succ_log_self (R := ℝ) hg1 w
  simp only [normalized, exponent, Real.floor_logb_natCast hw.le]
  constructor
  · apply (le_div_iff₀ hp).2
    simpa using hlo
  · apply (div_lt_iff₀ hp).2
    simpa [zpow_add₀ hg0.ne', mul_comm] using hhi

theorem normalized_reconstruct {g : ℕ} (hg : 2 ≤ g) (w : ℝ) :
    normalized g w * (g : ℝ) ^ exponent g w = w := by
  have hg0 : 0 < (g : ℝ) := by exact_mod_cast (by omega : 0 < g)
  exact div_mul_cancel₀ w (zpow_ne_zero _ hg0.ne')

end Jsp391
