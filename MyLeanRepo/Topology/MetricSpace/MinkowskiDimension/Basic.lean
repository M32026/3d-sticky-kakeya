import MyLeanRepo.Topology.MetricSpace.MinkowskiDimension
import Mathlib.Analysis.Asymptotics.ExpGrowth

/-!
# Basic properties of Minkowski dimensions

Monotonicity of the dyadic covering sequence and the comparison
`lowerMinkowskiDim ≤ upperMinkowskiDim`.
-/

namespace Metric

open ExpGrowth

variable {X : Type*} [PseudoEMetricSpace X]

/-- The dyadic covering sequence is monotone: as the radius decreases,
the covering number increases. -/
lemma dyadicCoveringSequence_monotone (s : Set X) :
    Monotone (dyadicCoveringSequence s) := by
  intro n m hnm
  have h1 : (2 : NNReal) ^ n ≤ (2 : NNReal) ^ m := by
    exact pow_le_pow_right' (by norm_num) hnm
  have h2 : ((2 : NNReal) ^ m)⁻¹ ≤ ((2 : NNReal) ^ n)⁻¹ := by
    have h21 : ((2 : NNReal) ^ n : ℝ) ≤ ((2 : NNReal) ^ m : ℝ) := by exact_mod_cast h1
    have h22 : (((2 : NNReal) ^ m : ℝ)⁻¹) ≤ (((2 : NNReal) ^ n : ℝ)⁻¹) := by
      gcongr
    exact_mod_cast h22
  have h3 : coveringNumber (((2 : NNReal) ^ n)⁻¹) s ≤
      coveringNumber (((2 : NNReal) ^ m)⁻¹) s :=
    coveringNumber_anti (h := h2)
  simpa [dyadicCoveringSequence] using mod_cast h3

/-- Lower Minkowski dimension is at most upper Minkowski dimension. -/
lemma lowerMinkowskiDim_le_upperMinkowskiDim (s : Set X) :
    lowerMinkowskiDim s ≤ upperMinkowskiDim s := by
  let u := dyadicCoveringSequence s
  have h : expGrowthInf u ≤ expGrowthSup u := expGrowthInf_le_expGrowthSup
  have hpos : (0 : EReal) < ENNReal.log 2 := by
    simp
  have h4 : expGrowthInf u / ENNReal.log 2 ≤ expGrowthSup u / ENNReal.log 2 := by
    gcongr
  exact EReal.toENNReal_le_toENNReal h4

end Metric
