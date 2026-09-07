import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWACardinalityLower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWADeltaMax
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ProbabilisticAssertionDCore

/-!
# Unified body-CWA probabilistic Assertion-D core

Choose the Bernoulli denominator

`D = target * C * family.enncard * deltaTubeVolume delta`.

The body-CWA cardinality lower bound gives
`1 ≤ C * family.enncard * deltaTubeVolume delta`, so `target ≤ D`.
The sampling fraction then cancels both `target` and the ambient cardinality.
This avoids a low/high `deltaMax` split and uses only complete public body-CWA
data.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Unified structural wrapper for probabilistic finite-core production. -/
theorem pure_wz2_body_cwa_probabilistic_assertionD_core
    (requestedCardLoss coreCardLoss ktEta assertionEta : ℝ)
    (hrequestedCardLoss : 0 < requestedCardLoss)
    (hcoreCardLoss : 0 < coreCardLoss)
    (hcoreRequested : coreCardLoss ≤ requestedCardLoss)
    (hktEta : 0 < ktEta)
    (hassertionEta : 0 < assertionEta)
    (hstrict : ktEta + coreCardLoss < assertionEta) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          family.Nonempty →
          family.IsInUnitBall →
          ∀ shading : Kakeya.Streamlined.TubeShading family,
            ∀ densityConstant C : ENNReal,
              ∀ thinningEta : ℝ,
                0 < densityConstant →
                C ≠ 0 →
                C ≠ ⊤ →
                0 < thinningEta →
                WZ2PaperBodyConvexWolffBound
                  family.toBodyFamily C →
                (∀ index,
                  densityConstant * (family.tube index).volume ≤
                    MeasureTheory.volume
                      (shading.carrier index)) →
                C * Kakeya.deltaTubeVolume delta ≤
                  densityConstant →
                ∀ net :
                    Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet
                      delta,
                  (net.testSets.card : ℝ) *
                        Real.exp (-(11 - Real.exp 1) *
                          (Kakeya.realRpowENN delta
                            (-thinningEta)).toReal) +
                      Real.exp (-(3 - Real.exp 1) *
                        ((C * Kakeya.deltaTubeVolume delta).toReal)⁻¹) <
                    1 / 8 →
                  Kakeya.realRpowENN delta assertionEta ≤
                    densityConstant →
                  pureWZ2ThinnedDeltaMax net thinningEta ≤
                    Kakeya.realRpowENN delta (-ktEta) →
                  Kakeya.realRpowENN delta
                      (-2 + coreCardLoss) ≤
                    (pureWZ2ThinnedAnalyticConflictBound
                          net thinningEta + 1)⁻¹ *
                      densityConstant *
                      ((1 / 2 : ENNReal) *
                        (C * Kakeya.deltaTubeVolume delta)⁻¹ *
                        densityConstant) →
                  Nonempty
                    (PureWZ2FiniteAssertionDCore
                      (assertionEta := assertionEta)
                      (requestedCardLoss := requestedCardLoss)
                      family shading) := by
  rcases
      pure_wz2_probabilistic_assertionD_core
        requestedCardLoss coreCardLoss ktEta assertionEta
        hrequestedCardLoss hcoreCardLoss hcoreRequested
        hktEta hassertionEta hstrict with
    ⟨conversionDelta₀, hconversionDelta₀,
      hconversionDelta₀One, hconvert⟩
  refine
    ⟨conversionDelta₀, hconversionDelta₀,
      hconversionDelta₀One, ?_⟩
  intro delta hdelta hdeltaBound family hfamilyNonempty
    hfamilyBall shading densityConstant C thinningEta
    hdensityPositive hCzero hCtop hthinningEta hCWA
    hperTube hCV net hunion hdensityWeak hktWeak
    hcardinality
  have hdeltaOne : delta ≤ 1 :=
    hdeltaBound.trans hconversionDelta₀One
  let target := Kakeya.realRpowENN delta (-thinningEta)
  let tubeVolume := Kakeya.deltaTubeVolume delta
  let massCoefficient := C * family.enncard * tubeVolume
  let D := target * massCoefficient
  have htargetPositive : 0 < target :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta _)
  have htargetTop : target ≠ ⊤ := by
    simp [target, Kakeya.realRpowENN]
  have htubePositive : 0 < tubeVolume :=
    (tube_volume_scaling.2.1 delta
      hdelta hdeltaOne).1
  have htubeTop : tubeVolume ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta
      hdelta hdeltaOne).2
  have hfamilyTop : family.enncard ≠ ⊤ := by
    change (family.card : ENNReal) ≠ ⊤
    simp
  have hmassCoefficientZero : massCoefficient ≠ 0 :=
    mul_ne_zero (mul_ne_zero hCzero (by
      change (family.card : ENNReal) ≠ 0
      exact_mod_cast hfamilyNonempty.ne')) htubePositive.ne'
  have hmassCoefficientTop : massCoefficient ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hCtop hfamilyTop) htubeTop
  have hDtop : D ≠ ⊤ :=
    ENNReal.mul_ne_top htargetTop hmassCoefficientTop
  have hbaseCard :=
    pure_wz2_body_cwa_cardinality_lower
      hdelta hdeltaOne hfamilyNonempty
      hCzero hCtop hCWA
  have honeMass : (1 : ENNReal) ≤ massCoefficient := by
    have hscaled :=
      mul_le_mul_right' hbaseCard
        (C * tubeVolume)
    have hcancel :
        (C * tubeVolume) *
            ((C * tubeVolume)⁻¹ * family.enncard) =
          family.enncard := by
      rw [← mul_assoc,
        ENNReal.mul_inv_cancel
          (mul_ne_zero hCzero htubePositive.ne')
          (ENNReal.mul_ne_top hCtop htubeTop),
        one_mul]
    have hleft :
        (C * tubeVolume) *
            (C⁻¹ * tubeVolume⁻¹) =
          1 := by
      rw [show
        C⁻¹ * tubeVolume⁻¹ =
          (C * tubeVolume)⁻¹ by
        exact
          (ENNReal.mul_inv
            (Or.inl hCzero) (Or.inl hCtop)).symm]
      exact ENNReal.mul_inv_cancel
        (mul_ne_zero hCzero htubePositive.ne')
        (ENNReal.mul_ne_top hCtop htubeTop)
    change
      C⁻¹ * tubeVolume⁻¹ ≤ family.enncard at hbaseCard
    have hscaled' :=
      mul_le_mul_left' hbaseCard (C * tubeVolume)
    rw [hleft] at hscaled'
    simpa [massCoefficient, mul_assoc, mul_comm, mul_left_comm]
      using hscaled'
  have hthin : target ≤ D := by
    calc
      target = target * 1 := (mul_one target).symm
      _ ≤ target * massCoefficient := by gcongr
  have hdeltaMax :
      family.toBodyFamily.deltaMax ≤ D := by
    have hbase :=
      pure_wz2_deltaMax_le_of_body_cwa
        hdelta hdeltaOne hCtop hCWA
    exact hbase.trans (by
      change massCoefficient ≤ target * massCoefficient
      calc
        massCoefficient = 1 * massCoefficient := (one_mul _).symm
        _ ≤ target * massCoefficient := by
          gcongr
          have hone :
              (1 : ENNReal) ≤ target := by
            have h :=
              pure_wz2_rpowENN_antitone
                hdelta hdeltaOne
                (by linarith : -thinningEta ≤ 0)
            simpa [target, Kakeya.realRpowENN] using h
          exact hone)
  have hsourceDense :
      shading.IsLambdaDense densityConstant := by
    change
      densityConstant *
          (∑ index : Fin family.card,
            (family.tube index).volume) ≤
        ∑ index : Fin family.card,
          MeasureTheory.volume (shading.carrier index)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun index _ => hperTube index
  have hfamilyMass :
      family.toBodyFamily.mass =
        family.enncard * tubeVolume := by
    rw [tubeFamily_mass_eq_nominal]
    rfl
  have hmassLower :
      densityConstant * family.enncard * tubeVolume ≤
        shading.mass := by
    change
      densityConstant * family.toBodyFamily.mass ≤
        shading.mass at hsourceDense
    rw [hfamilyMass] at hsourceDense
    simpa [mul_assoc] using hsourceDense
  have hfraction :
      target / D = massCoefficient⁻¹ := by
    rw [show D = target * massCoefficient by rfl]
    rw [div_eq_mul_inv,
      ENNReal.mul_inv
        (Or.inl htargetPositive.ne')
        (Or.inl htargetTop)]
    rw [← mul_assoc,
      ENNReal.mul_inv_cancel
        htargetPositive.ne' htargetTop,
      one_mul]
  have hmu :
      tubeVolume ≤ (target / D) * shading.mass := by
    rw [hfraction]
    have hCV' :
        C * tubeVolume ≤ densityConstant := hCV
    have hmain :
        massCoefficient * tubeVolume ≤ shading.mass := by
      calc
        massCoefficient * tubeVolume =
            (C * tubeVolume) *
              (family.enncard * tubeVolume) := by
          simp [massCoefficient]
          ring
        _ ≤ densityConstant *
              (family.enncard * tubeVolume) := by
          gcongr
        _ ≤ shading.mass := by
          simpa [mul_assoc] using hmassLower
    apply
      (ENNReal.mul_le_mul_iff_right
        hmassCoefficientZero hmassCoefficientTop).mp
    calc
      massCoefficient * tubeVolume ≤ shading.mass := hmain
      _ = massCoefficient *
          (massCoefficient⁻¹ * shading.mass) := by
        rw [← mul_assoc,
          ENNReal.mul_inv_cancel
            hmassCoefficientZero hmassCoefficientTop,
          one_mul]
  have hunion' :
      (net.testSets.card : ℝ) *
            Real.exp (-(11 - Real.exp 1) * target.toReal) +
          Real.exp (-(3 - Real.exp 1) *
            (target.toReal / D.toReal) *
            (family.card : ℝ)) <
        1 / 8 := by
    have hmassCoefficientReal :
        0 < massCoefficient.toReal :=
      ENNReal.toReal_pos hmassCoefficientZero
        hmassCoefficientTop
    have htargetReal :
        0 < target.toReal :=
      ENNReal.toReal_pos htargetPositive.ne' htargetTop
    have hDreal :
        D.toReal =
          target.toReal * massCoefficient.toReal := by
      simp [D, ENNReal.toReal_mul]
    have hmassCoefficientRealEq :
        massCoefficient.toReal =
          C.toReal * (family.card : ℝ) *
            tubeVolume.toReal := by
      simp [massCoefficient, ENNReal.toReal_mul,
        Kakeya.Streamlined.TubeFamily.enncard]
    have hfamilyReal :
        family.enncard.toReal = (family.card : ℝ) := by
      simp [Kakeya.Streamlined.TubeFamily.enncard]
    have hcoefficientReal :
        (C * tubeVolume).toReal =
          C.toReal * tubeVolume.toReal := by
      rw [ENNReal.toReal_mul]
    have hsimplify :
        (target.toReal / D.toReal) * (family.card : ℝ) =
          tubeVolume.toReal⁻¹ * C.toReal⁻¹ := by
      rw [hDreal]
      rw [hmassCoefficientRealEq]
      have hfamilyPositive : 0 < (family.card : ℝ) := by
        exact_mod_cast hfamilyNonempty
      have hCReal : 0 < C.toReal :=
        ENNReal.toReal_pos hCzero hCtop
      have htubeReal : 0 < tubeVolume.toReal :=
        ENNReal.toReal_pos htubePositive.ne' htubeTop
      field_simp [htargetReal.ne', hfamilyPositive.ne',
        hCReal.ne', htubeReal.ne']
    have hexponent :
        -(3 - Real.exp 1) *
            (target.toReal / D.toReal) *
            (family.card : ℝ) =
          -(3 - Real.exp 1) *
            (tubeVolume.toReal⁻¹ * C.toReal⁻¹) := by
      rw [mul_assoc, hsimplify]
    rw [hexponent]
    simpa [target] using hunion
  have hcardinality' :
      Kakeya.realRpowENN delta (-2 + coreCardLoss) ≤
        (((pureWZ2ThinnedAnalyticConflictBound
              net thinningEta + 1)⁻¹ *
            densityConstant) *
          ((1 / 2 : ENNReal) *
            (target / D) * densityConstant)) *
          family.enncard := by
    rw [hfraction]
    have hcancel :
        (massCoefficient⁻¹ * densityConstant) *
            family.enncard =
          (C * tubeVolume)⁻¹ * densityConstant := by
      rw [show
        massCoefficient =
          (C * tubeVolume) * family.enncard by
        simp [massCoefficient]
        ring]
      rw [ENNReal.mul_inv
        (Or.inl (mul_ne_zero hCzero htubePositive.ne'))
        (Or.inl (ENNReal.mul_ne_top hCtop htubeTop))]
      rw [show
        ((C * tubeVolume)⁻¹ * family.enncard⁻¹ *
            densityConstant) * family.enncard =
          (C * tubeVolume)⁻¹ * densityConstant *
            (family.enncard⁻¹ * family.enncard) by ring]
      rw [ENNReal.inv_mul_cancel
        (by
          change (family.card : ENNReal) ≠ 0
          exact_mod_cast hfamilyNonempty.ne')
        hfamilyTop, mul_one]
    calc
      Kakeya.realRpowENN delta (-2 + coreCardLoss) ≤
          (pureWZ2ThinnedAnalyticConflictBound
                net thinningEta + 1)⁻¹ *
            densityConstant *
            ((1 / 2 : ENNReal) *
              (C * tubeVolume)⁻¹ * densityConstant) :=
        hcardinality
      _ =
          (((pureWZ2ThinnedAnalyticConflictBound
                net thinningEta + 1)⁻¹ *
              densityConstant) *
            ((1 / 2 : ENNReal) *
              massCoefficient⁻¹ * densityConstant)) *
            family.enncard := by
        calc
          (pureWZ2ThinnedAnalyticConflictBound
                  net thinningEta + 1)⁻¹ *
              densityConstant *
              ((1 / 2 : ENNReal) *
                (C * tubeVolume)⁻¹ * densityConstant) =
            (pureWZ2ThinnedAnalyticConflictBound
                  net thinningEta + 1)⁻¹ *
              densityConstant *
              ((1 / 2 : ENNReal) *
                ((massCoefficient⁻¹ * densityConstant) *
                  family.enncard)) := by
                    rw [hcancel]
                    ring
          _ =
            (((pureWZ2ThinnedAnalyticConflictBound
                  net thinningEta + 1)⁻¹ *
                densityConstant) *
              ((1 / 2 : ENNReal) *
                massCoefficient⁻¹ * densityConstant)) *
              family.enncard := by ring
  exact
    hconvert delta hdelta hdeltaBound family
      hfamilyNonempty hfamilyBall shading densityConstant
      D thinningEta hdensityPositive hDtop hthinningEta
      hdeltaMax hthin hperTube net hmu hunion'
      hdensityWeak hktWeak hcardinality'

end Kakeya.Assouad

end
