import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulScaleAbsorption
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalParentScaleBound

/-!
# Canonical scale loss for the faithful short-curve assembly

The canonical parent tangency scale is independent of `M_parent`, but its
cutoffs still contribute polynomial losses. Write `a` for the metric
two-ends exponent and use `a^2` for the tangency exponent.

After the representative scales cancel, the non-logarithmic loss is

`(B + 4) * a + (B + 29 / 8) * a^2`,

where `B` contains the Proposition 26 exponent and the `7/2` power of the
tangent-ball cover cardinality. One further copy of `a` is split between the
remaining cubic scale loss and all ordinary polylogarithmic factors: each gets
an `a/2` budget. This module chooses `a` only after the two Proposition 26
constants are known, but still before the physical scale, family, and
multiplicity are quantified.
-/

namespace Kakeya.Cinematic

noncomputable def faithfulCanonicalBranchParameter
    (D C_positive C_singleton : ℝ) : ℝ :=
  max C_positive C_singleton +
    (7 / 2 : ℝ) * (Real.log D / Real.log 2)

noncomputable def faithfulCanonicalRepresentativeLoss
    (branchParameter metricExponent : ℝ) : ℝ :=
  (branchParameter + 4) * metricExponent +
    (branchParameter + 29 / 8) * metricExponent ^ 2

noncomputable def faithfulCanonicalFullLoss
    (branchParameter metricExponent : ℝ) : ℝ :=
  faithfulCanonicalRepresentativeLoss
      branchParameter metricExponent +
    metricExponent

noncomputable def faithfulCanonicalOrdinaryLoss
    (metricExponent : ℝ) : ℝ :=
  metricExponent / 2

noncomputable def faithfulCanonicalStructuredScaleLoss
    (branchParameter metricExponent : ℝ) : ℝ :=
  (3 / 4 : ℝ) *
      faithfulCanonicalParentScaleLoss metricExponent +
    (branchParameter + 1) *
      (metricExponent + metricExponent ^ 2)

lemma faithfulCanonicalStructuredScaleLoss_eq
    (branchParameter metricExponent : ℝ) :
    faithfulCanonicalStructuredScaleLoss
        branchParameter metricExponent =
      faithfulCanonicalRepresentativeLoss
          branchParameter metricExponent +
        (9 / 4 : ℝ) * metricExponent ^ 3 := by
  dsimp only [faithfulCanonicalStructuredScaleLoss,
    faithfulCanonicalParentScaleLoss,
    faithfulCanonicalRepresentativeLoss]
  ring

lemma faithfulCanonicalStructuredScaleLoss_le_full
    (branchParameter metricExponent : ℝ)
    (hmetric : 0 ≤ metricExponent)
    (hmetricUpper : metricExponent ≤ 1 / 16) :
    faithfulCanonicalStructuredScaleLoss
        branchParameter metricExponent ≤
      faithfulCanonicalFullLoss
        branchParameter metricExponent := by
  rw [faithfulCanonicalStructuredScaleLoss_eq]
  dsimp only [faithfulCanonicalFullLoss]
  have hsquare :
      metricExponent ^ 2 ≤ 1 / 256 := by
    nlinarith [sq_nonneg metricExponent]
  have hcubic :
      (9 / 4 : ℝ) * metricExponent ^ 3 ≤
        metricExponent := by
    have hcubicRaw :
        metricExponent * metricExponent ^ 2 ≤
          metricExponent * (1 / 256) :=
      mul_le_mul_of_nonneg_left hsquare hmetric
    nlinarith
  linarith

lemma faithfulCanonicalStructuredScaleLoss_add_ordinary_le_full
    (branchParameter metricExponent : ℝ)
    (hmetric : 0 ≤ metricExponent)
    (hmetricUpper : metricExponent ≤ 1 / 16) :
    faithfulCanonicalStructuredScaleLoss
          branchParameter metricExponent +
        faithfulCanonicalOrdinaryLoss metricExponent ≤
      faithfulCanonicalFullLoss
        branchParameter metricExponent := by
  rw [faithfulCanonicalStructuredScaleLoss_eq]
  dsimp only [faithfulCanonicalOrdinaryLoss,
    faithfulCanonicalFullLoss]
  have hsquare :
      metricExponent ^ 2 ≤ 1 / 256 := by
    nlinarith [sq_nonneg metricExponent]
  have hcubic :
      (9 / 4 : ℝ) * metricExponent ^ 3 ≤
        metricExponent / 2 := by
    have hcubicRaw :
        metricExponent * metricExponent ^ 2 ≤
          metricExponent * (1 / 256) :=
      mul_le_mul_of_nonneg_left hsquare hmetric
    nlinarith
  linarith

lemma faithful_canonical_loss_expansion
    (branchParameter metricExponent : ℝ)
    (hmetric : 0 < metricExponent) :
    (branchParameter + 29 / 8) * metricExponent +
          (13 / 4 : ℝ) * metricExponent ^ 2 +
          metricExponent ^ 3 *
            (branchParameter / metricExponent +
              3 / (8 * metricExponent) +
              3 / (8 * metricExponent ^ 2)) =
        faithfulCanonicalRepresentativeLoss
          branchParameter metricExponent := by
  dsimp only [faithfulCanonicalRepresentativeLoss]
  field_simp [hmetric.ne']
  ring

lemma faithfulCanonicalBranchParameter_nonneg
    (D C_positive C_singleton : ℝ)
    (hD : 1 ≤ D)
    (hC_positive : 1 ≤ C_positive) :
    0 ≤
      faithfulCanonicalBranchParameter
        D C_positive C_singleton := by
  have hlogD : 0 ≤ Real.log D :=
    Real.log_nonneg hD
  have hlogTwo : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have hbranch :
      0 ≤ max C_positive C_singleton := by
    linarith [le_max_left C_positive C_singleton]
  dsimp only [faithfulCanonicalBranchParameter]
  positivity

lemma faithfulCanonicalRepresentativeLoss_le
    (branchParameter metricExponent : ℝ)
    (hbranch : 0 ≤ branchParameter)
    (hmetric : 0 ≤ metricExponent)
    (hmetricUpper : metricExponent ≤ 1 / 16) :
    faithfulCanonicalRepresentativeLoss
        branchParameter metricExponent ≤
      (2 * branchParameter + 8) * metricExponent := by
  dsimp only [faithfulCanonicalRepresentativeLoss]
  have hsquare :
      metricExponent ^ 2 ≤ metricExponent / 16 := by
    nlinarith [sq_nonneg metricExponent]
  nlinarith [mul_nonneg hbranch hmetric]

lemma faithfulCanonicalFullLoss_le
    (branchParameter metricExponent : ℝ)
    (hbranch : 0 ≤ branchParameter)
    (hmetric : 0 ≤ metricExponent)
    (hmetricUpper : metricExponent ≤ 1 / 16) :
    faithfulCanonicalFullLoss
        branchParameter metricExponent ≤
      (2 * branchParameter + 8) * metricExponent := by
  dsimp only [faithfulCanonicalFullLoss,
    faithfulCanonicalRepresentativeLoss]
  have hsquare :
      metricExponent ^ 2 ≤ metricExponent / 16 := by
    nlinarith [sq_nonneg metricExponent]
  nlinarith [mul_nonneg hbranch hmetric]

lemma choose_faithful_canonical_metric_exponent
    (targetExponent D C_positive C_singleton : ℝ)
    (htarget : 0 < targetExponent)
    (hD : 1 ≤ D)
    (hC_positive : 1 ≤ C_positive) :
    ∃ metricExponent : ℝ,
      metricExponent =
          min targetExponent 1 /
            (2 *
              max 8
                (2 *
                    faithfulCanonicalBranchParameter
                      D C_positive C_singleton +
                  8)) ∧
      0 < metricExponent ∧
      metricExponent ≤ 1 / 16 ∧
      8 * metricExponent < targetExponent ∧
      faithfulCanonicalRepresentativeLoss
          (faithfulCanonicalBranchParameter
            D C_positive C_singleton)
          metricExponent <
        targetExponent ∧
      faithfulCanonicalFullLoss
          (faithfulCanonicalBranchParameter
            D C_positive C_singleton)
          metricExponent <
        targetExponent ∧
      (3 / 2 : ℝ) *
          (metricExponent + metricExponent ^ 2 +
            metricExponent ^ 2) <
        targetExponent := by
  let branchParameter :=
    faithfulCanonicalBranchParameter
      D C_positive C_singleton
  have hbranch : 0 ≤ branchParameter := by
    dsimp only [branchParameter]
    exact faithfulCanonicalBranchParameter_nonneg
      D C_positive C_singleton hD hC_positive
  rcases choose_internal_metric_exponent_for_loss
      targetExponent (2 * branchParameter + 8)
      htarget with
    ⟨metricExponent, hmetricEq, hmetricPos,
      hmetricUpper, height, hbudget, hsmallJoint⟩
  have hfullLoss :
      faithfulCanonicalFullLoss
          branchParameter metricExponent ≤
        (2 * branchParameter + 8) * metricExponent :=
    faithfulCanonicalFullLoss_le
      branchParameter metricExponent hbranch
      hmetricPos.le hmetricUpper
  have hrepresentative :
      faithfulCanonicalRepresentativeLoss
          branchParameter metricExponent ≤
        faithfulCanonicalFullLoss
          branchParameter metricExponent := by
    dsimp only [faithfulCanonicalFullLoss]
    linarith
  exact
    ⟨metricExponent, by simpa [branchParameter] using hmetricEq,
      hmetricPos, hmetricUpper, height,
      hrepresentative.trans_lt (hfullLoss.trans_lt hbudget),
      hfullLoss.trans_lt hbudget, hsmallJoint⟩

end Kakeya.Cinematic
