import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Physical logarithmic envelope for paper boundary losses

This low-level module fixes the coefficient used to dominate line-family and
literal-cell cardinality losses.  It also records the elementary small-scale
quadratic logarithm absorption shared by the numerical balancing modules.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperBoundaryLogCoefficient : ℝ :=
  max (5 * Real.log 163 / Real.log 2 + 2)
    (5 / Real.log 2)

lemma exists_delta_boundary_log_square
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        3 ≤ Real.log delta⁻¹ ∧
          C * (1 + Real.log delta⁻¹) ≤
            (Real.log delta⁻¹) ^ 2 := by
  let threshold : ℝ := max 3 (2 * C)
  have hThresholdPos : 0 < threshold := by
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let delta₀ : ℝ := Real.exp (-threshold)
  have hdelta₀Pos : 0 < delta₀ := Real.exp_pos _
  have hdelta₀One : delta₀ ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hThresholdPos.le)
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaBound
  have hInverse :
      Real.exp threshold ≤ delta⁻¹ := by
    have hinv :=
      one_div_le_one_div_of_le hdelta hdeltaBound
    simpa [delta₀, Real.exp_neg] using hinv
  have hLogLower :
      threshold ≤ Real.log delta⁻¹ := by
    have hlog :=
      Real.log_le_log (Real.exp_pos threshold) hInverse
    simpa using hlog
  have hLogThree : 3 ≤ Real.log delta⁻¹ :=
    (le_max_left _ _).trans hLogLower
  have hLogCoefficient : 2 * C ≤ Real.log delta⁻¹ :=
    (le_max_right _ _).trans hLogLower
  have hLogNonneg : 0 ≤ Real.log delta⁻¹ := by linarith
  refine ⟨hLogThree, ?_⟩
  calc
    C * (1 + Real.log delta⁻¹)
        ≤ C * (2 * Real.log delta⁻¹) := by
      gcongr
      linarith
    _ = (2 * C) * Real.log delta⁻¹ := by ring
    _ ≤ Real.log delta⁻¹ * Real.log delta⁻¹ := by
      gcongr
    _ = (Real.log delta⁻¹) ^ 2 := by ring

end Kakeya.Assouad

end
