import Jsp391.Core
import Jsp391.Digits
import Jsp391.Normalization

/-! Complete arbitrary-base, arbitrary-positive-target form of Stoll's Theorem 1.3. -/
noncomputable section
open scoped BigOperators
open Filter Topology
namespace Jsp391

/-- The digits extracted from the actual recurrence for the unnormalized target `w`. -/
def output (g : ℕ) (w e : ℝ) (n : ℕ) : ℤ :=
  trajectory g (normalized g w) e (2 * n + 2) -
    (g : ℤ) * trajectory g (normalized g w) e (2 * n)

def reconstruction (g : ℕ) (w e : ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (n + 1), (output g w e i : ℝ) / (g : ℝ) ^ i) *
    (g : ℝ) ^ exponent g w

theorem output_eq_digit {g : ℕ} {w e : ℝ} (hg : 2 ≤ g) (hw : 0 < w)
    (he : IsAdmissible g e) (n : ℕ) :
    output g w e n = digit g (normalized g w) n := by
  obtain ⟨ht, htg⟩ := normalized_bounds hg hw
  exact extraction g (normalized g w) e hg ht htg he n

theorem output_bounds {g : ℕ} {w e : ℝ} (hg : 2 ≤ g) (hw : 0 < w)
    (he : IsAdmissible g e) (n : ℕ) :
    0 ≤ output g w e n ∧ output g w e n < g := by
  rw [output_eq_digit hg hw he]
  exact digit_bounds hg _ n

theorem first_digit_positive {g : ℕ} {w e : ℝ} (hg : 2 ≤ g) (hw : 0 < w)
    (he : IsAdmissible g e) : 1 ≤ output g w e 0 := by
  obtain ⟨ht, htg⟩ := normalized_bounds hg hw
  rw [output_eq_digit hg hw he, digit_zero hg ht htg]
  exact Int.le_floor.mpr (by simpa using ht)

theorem reconstruction_tendsto {g : ℕ} {w e : ℝ} (hg : 2 ≤ g) (hw : 0 < w)
    (he : IsAdmissible g e) : Tendsto (reconstruction g w e) atTop (𝓝 w) := by
  obtain ⟨ht, htg⟩ := normalized_bounds hg hw
  have hf : reconstruction g w e = fun n =>
      partialSum g (normalized g w) n * (g : ℝ) ^ exponent g w := by
    funext n
    simp only [reconstruction, partialSum, output_eq_digit hg hw he]
  rw [hf]
  simpa only [normalized_reconstruct hg w] using
    (partialSum_tendsto hg ht htg).mul_const ((g : ℝ) ^ exponent g w)

/-- The coefficient `beta` is the paper's `g / alpha`. -/
theorem beta_eq_div_alpha {g : ℕ} {t : ℝ} (hg : 2 ≤ g) :
    beta g t = (g : ℝ) / alpha g t := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  simp [alpha, beta, hg0]

/-- Every permitted base has an admissible shift, including base two. -/
theorem admissible_choice {g : ℕ} (hg : 2 ≤ g) : IsAdmissible g (-1 / (g : ℝ)) := by
  have hgr : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < g := by linarith
  refine ⟨le_rfl, ?_⟩
  apply (div_lt_div_iff_of_pos_right hg0).2
  nlinarith [mul_nonneg (show 0 ≤ (g : ℝ) + 1 by linarith)
    (show 0 ≤ (g : ℝ) - 2 by linarith)]

/-- All bases, positive targets, admissible shifts and digit positions; the
weighted recurrence outputs reconstruct the original target, not only its mantissa. -/
theorem jsp_000391 (g : ℕ) (w e : ℝ) (hg : 2 ≤ g) (hw : 0 < w)
    (he : IsAdmissible g e) :
    (∀ n, output g w e n = digit g (normalized g w) n) ∧
    (∀ n, 0 ≤ output g w e n ∧ output g w e n < g) ∧
    1 ≤ output g w e 0 ∧
    Tendsto (reconstruction g w e) atTop (𝓝 w) :=
  ⟨output_eq_digit hg hw he, output_bounds hg hw he,
    first_digit_positive hg hw he, reconstruction_tendsto hg hw he⟩

end Jsp391
