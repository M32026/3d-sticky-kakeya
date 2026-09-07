import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.WeightedSelection
import MyLeanRepo.Kakeya.Assouad.LargeSlope.LowMultiplicityTail
import MyLeanRepo.Kakeya.Assouad.TubeVolumeRatio
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockPYZVolumeSimplification
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionBasicArithmetic

/-!
# Monomial lower bound for paper Lemma 7.12

This module turns the representative cinematic pullback data into the
explicit power-law lower bound used by the final absorption step.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Fixed denominator in the representative Lemma 7.12 lower bound. -/
def parameterBlockProjectionMonomialConstant : ENNReal :=
  4096000 *
    parameterBlockRepresentativeCopiedFiberCap ^ 3

/--
After multiplying by one fixed constant, the representative cinematic area
dominates the exact monomial predicted by the paper proof.
-/
lemma parameterBlockProjection_scaled_monomial_lower
    {delta epsilon eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {f : SlopeFunction}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    (localBlock :
      ParameterLocalFullBlockData clustered epsilon)
    (representatives :
      ParameterLocalRepresentativeBlockData localBlock)
    (amplification :
      ParameterBlockAmplificationData
        delta localBlock.blockScale
        (1 - 20 * epsilon ^ 2)
        localBlock.centeredPoints)
    (pullback :
      ParameterBlockRepresentativeCinematicPullbackData
        localBlock representatives amplification f
        (parameterBlockProjectionPYZLoss epsilon)
        (parameterBlockProjectionPerTubeThreshold delta eta))
    (hdelta : 0 < delta)
    (hdelta_half : delta ≤ 1 / 2)
    (hepsilon : 0 < epsilon) :
    parameterBlockProjectionMonomialConstant *
        volume (twistedUnion pullback.shading f) ≥
      amplification.translations.enncard ^ 2 *
        Kakeya.realRpowENN delta (3 + 12 * eta +
          3 * parameterBlockProjectionPYZLoss epsilon) *
        localBlock.sourcePoints.enncard ^ 3 := by
  let translations := amplification.translations.enncard
  let mass := pullback.shading.mass
  let fiberCap := parameterBlockRepresentativeCopiedFiberCap
  have htranslations : 0 < translations := by
    dsimp only [translations, DiscreteSet.enncard]
    exact_mod_cast amplification.translations_nonempty.card_pos
  have htranslations_top : translations ≠ ⊤ := by
    dsimp only [translations, DiscreteSet.enncard]
    exact ENNReal.natCast_ne_top _
  have hmass_lower := pullback.mass_lower
  have hthreshold_pos :
      0 < parameterBlockProjectionPerTubeThreshold delta eta := by
    unfold parameterBlockProjectionPerTubeThreshold
    have hvolume :
        0 < Kakeya.deltaTubeVolume delta :=
      (tube_volume_scaling.2.1 delta hdelta
        (hdelta_half.trans (by norm_num))).1
    apply ENNReal.mul_pos
    · exact (ENNReal.mul_pos
        (by norm_num)
        (by
          simp only [Kakeya.realRpowENN]
          exact (ENNReal.ofReal_pos.mpr
            (Real.rpow_pos_of_pos hdelta _)).ne')).ne'
    · exact hvolume.ne'
  have hsource_pos :
      0 < localBlock.sourcePoints.enncard := by
    dsimp only [DiscreteSet.enncard]
    exact_mod_cast localBlock.sourcePoints_nonempty.card_pos
  have hmass : 0 < mass := by
    have hlower :
        0 <
          (1 / 2 : ENNReal) *
            (parameterBlockProjectionPerTubeThreshold delta eta *
              localBlock.sourcePoints.enncard) := by
      apply ENNReal.mul_pos
      · norm_num
      · exact (ENNReal.mul_pos
          hthreshold_pos.ne' hsource_pos.ne').ne'
    exact hlower.trans_le hmass_lower
  have hmass_top : mass ≠ ⊤ := by
    dsimp only [mass, Kakeya.Streamlined.Shading.mass]
    exact ENNReal.sum_ne_top.mpr fun index _ =>
      tubeShading_carrier_volume_ne_top pullback.shading index
  have hfiberCap : 0 < fiberCap := by
    norm_num [fiberCap,
      parameterBlockRepresentativeCopiedFiberCap]
  have hfiberCap_top : fiberCap ≠ ⊤ := by
    norm_num [fiberCap,
      parameterBlockRepresentativeCopiedFiberCap]
  have hpyz :
      0 < parameterBlockProjectionPYZLoss epsilon := by
    unfold parameterBlockProjectionPYZLoss
    positivity
  have hflat :=
    parameterBlockPYZ_volume_simplification
      translations mass fiberCap
      delta (parameterBlockProjectionPYZLoss epsilon)
      htranslations htranslations_top
      hmass hmass_top
      hfiberCap hfiberCap_top
      hdelta hpyz
  have hvolume_flat :
      volume (twistedUnion pullback.shading f) ≥
        translations ^ 2 * mass ^ 3 /
          ((ENNReal.ofReal (20 * delta)) ^ 3 *
            fiberCap ^ 3 *
            ENNReal.ofReal
              (Real.rpow delta
                (-3 * parameterBlockProjectionPYZLoss epsilon))) := by
    rw [← hflat]
    exact pullback.volume_lower
  have hmass_mono :
      ((1 / 2 : ENNReal) *
          (parameterBlockProjectionPerTubeThreshold delta eta *
            localBlock.sourcePoints.enncard)) ^ 3 ≤
        mass ^ 3 := by
    gcongr
  have htube :
      ENNReal.ofReal ((1 / 2 : ℝ) * delta ^ 2) ≤
        Kakeya.deltaTubeVolume delta :=
    deltaTubeVolume_quadratic_lower hdelta hdelta_half
  have hthreshold :
      (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (2 + 4 * eta) ≤
        parameterBlockProjectionPerTubeThreshold delta eta := by
    unfold parameterBlockProjectionPerTubeThreshold
    have hdelta_two :
        ENNReal.ofReal ((1 / 2 : ℝ) * delta ^ 2) =
          (1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta 2 := by
      simp [Kakeya.realRpowENN, Real.rpow_two,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [hdelta_two] at htube
    have hquarter :
        (1 / 4 : ENNReal) =
          (1 / 2 : ENNReal) * (1 / 2 : ENNReal) := by
      simp only [one_div]
      have hfour : (4 : ENNReal) = 2 * 2 := by norm_num
      rw [hfour, ENNReal.mul_inv
        (Or.inl (by norm_num : (2 : ENNReal) ≠ 0))
        (Or.inl (by norm_num : (2 : ENNReal) ≠ ⊤))]
    calc
      (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (2 + 4 * eta) =
          (1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta (4 * eta) *
              ((1 / 2 : ENNReal) *
                Kakeya.realRpowENN delta 2) := by
        rw [realRpowENN_add hdelta]
        rw [hquarter]
        ring
      _ ≤
          (1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta (4 * eta) *
              Kakeya.deltaTubeVolume delta := by
        gcongr
  have hmass_power :
      (1 / 512 : ENNReal) *
          Kakeya.realRpowENN delta (6 + 12 * eta) *
            localBlock.sourcePoints.enncard ^ 3 ≤
        mass ^ 3 := by
    have hthreshold_card :
        (1 / 4 : ENNReal) *
              Kakeya.realRpowENN delta (2 + 4 * eta) *
              localBlock.sourcePoints.enncard ≤
            parameterBlockProjectionPerTubeThreshold delta eta *
              localBlock.sourcePoints.enncard := by
      gcongr
    have hhalf :
        (1 / 2 : ENNReal) *
              ((1 / 4 : ENNReal) *
                Kakeya.realRpowENN delta (2 + 4 * eta) *
                localBlock.sourcePoints.enncard) ≤
            (1 / 2 : ENNReal) *
              (parameterBlockProjectionPerTubeThreshold delta eta *
                localBlock.sourcePoints.enncard) := by
      gcongr
    have hcubed :
        ((1 / 2 : ENNReal) *
              ((1 / 4 : ENNReal) *
                Kakeya.realRpowENN delta (2 + 4 * eta) *
                localBlock.sourcePoints.enncard)) ^ 3 ≤
            mass ^ 3 := by
      exact (pow_le_pow_left₀ (by positivity) hhalf 3).trans hmass_mono
    have hpower :
        (Kakeya.realRpowENN delta (2 + 4 * eta)) ^ 3 =
          Kakeya.realRpowENN delta (6 + 12 * eta) := by
      rw [pow_three]
      rw [← realRpowENN_add hdelta,
        ← realRpowENN_add hdelta]
      congr 1
      ring
    have hconstant :
        ((1 / 2 : ENNReal) * (1 / 4 : ENNReal)) ^ 3 =
          (1 / 512 : ENNReal) := by
      simp only [one_div]
      have hbase :
          (2 : ENNReal)⁻¹ * (4 : ENNReal)⁻¹ =
            (8 : ENNReal)⁻¹ := by
        have height : (8 : ENNReal) = 2 * 4 := by norm_num
        rw [height, ENNReal.mul_inv
          (Or.inl (by norm_num : (2 : ENNReal) ≠ 0))
          (Or.inl (by norm_num : (2 : ENNReal) ≠ ⊤))]
      rw [hbase, pow_three]
      have hfive : (512 : ENNReal) = (8 * 8) * 8 := by
        norm_num
      rw [hfive,
        ENNReal.mul_inv
          (Or.inl
            (mul_ne_zero
              (by norm_num : (8 : ENNReal) ≠ 0)
              (by norm_num : (8 : ENNReal) ≠ 0)))
          (Or.inl
            (ENNReal.mul_ne_top
              (by norm_num : (8 : ENNReal) ≠ ⊤)
              (by norm_num : (8 : ENNReal) ≠ ⊤))),
        ENNReal.mul_inv
          (Or.inl (by norm_num : (8 : ENNReal) ≠ 0))
          (Or.inl (by norm_num : (8 : ENNReal) ≠ ⊤))]
      ring
    calc
      (1 / 512 : ENNReal) *
            Kakeya.realRpowENN delta (6 + 12 * eta) *
            localBlock.sourcePoints.enncard ^ 3 =
          (((1 / 2 : ENNReal) * (1 / 4 : ENNReal)) ^ 3) *
            (Kakeya.realRpowENN delta (2 + 4 * eta)) ^ 3 *
            localBlock.sourcePoints.enncard ^ 3 := by
        rw [hconstant, hpower]
      _ =
          ((1 / 2 : ENNReal) *
            ((1 / 4 : ENNReal) *
              Kakeya.realRpowENN delta (2 + 4 * eta) *
              localBlock.sourcePoints.enncard)) ^ 3 := by
        ring
      _ ≤ mass ^ 3 := hcubed
  have hdelta_factor :
      (ENNReal.ofReal (20 * delta)) ^ 3 =
        8000 * Kakeya.realRpowENN delta 3 := by
    have hrpow_three :
        Real.rpow delta (3 : ℝ) = delta ^ 3 := by
      simpa using Real.rpow_natCast delta 3
    simp [Kakeya.realRpowENN, hrpow_three,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20),
      pow_three, ENNReal.ofReal_mul hdelta.le]
    ring
  have hloss_factor :
      ENNReal.ofReal
          (Real.rpow delta
            (-3 * parameterBlockProjectionPYZLoss epsilon)) *
        Kakeya.realRpowENN delta
          (3 * parameterBlockProjectionPYZLoss epsilon) = 1 := by
    change
      Kakeya.realRpowENN delta
          (-3 * parameterBlockProjectionPYZLoss epsilon) *
        Kakeya.realRpowENN delta
          (3 * parameterBlockProjectionPYZLoss epsilon) = 1
    rw [← realRpowENN_add hdelta]
    simp [Kakeya.realRpowENN]
  have hdenominator_zero :
      (ENNReal.ofReal (20 * delta)) ^ 3 *
          fiberCap ^ 3 *
          ENNReal.ofReal
            (Real.rpow delta
              (-3 * parameterBlockProjectionPYZLoss epsilon)) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (pow_ne_zero 3
          (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)))
        (pow_ne_zero 3 hfiberCap.ne'))
      (ENNReal.ofReal_ne_zero_iff.mpr
        (Real.rpow_pos_of_pos hdelta _))
  have hdenominator_top :
      (ENNReal.ofReal (20 * delta)) ^ 3 *
          fiberCap ^ 3 *
          ENNReal.ofReal
            (Real.rpow delta
              (-3 * parameterBlockProjectionPYZLoss epsilon)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top hfiberCap_top))
      ENNReal.ofReal_ne_top
  have hscaled :
      parameterBlockProjectionMonomialConstant *
          (translations ^ 2 * mass ^ 3 /
            ((ENNReal.ofReal (20 * delta)) ^ 3 *
              fiberCap ^ 3 *
              ENNReal.ofReal
                (Real.rpow delta
                  (-3 * parameterBlockProjectionPYZLoss epsilon)))) ≥
        translations ^ 2 *
          Kakeya.realRpowENN delta (3 + 12 * eta +
            3 * parameterBlockProjectionPYZLoss epsilon) *
          localBlock.sourcePoints.enncard ^ 3 := by
    let denominator : ENNReal :=
      (ENNReal.ofReal (20 * delta)) ^ 3 *
        fiberCap ^ 3 *
        ENNReal.ofReal
          (Real.rpow delta
            (-3 * parameterBlockProjectionPYZLoss epsilon))
    let target : ENNReal :=
      translations ^ 2 *
        Kakeya.realRpowENN delta
          (3 + 12 * eta +
            3 * parameterBlockProjectionPYZLoss epsilon) *
        localBlock.sourcePoints.enncard ^ 3
    let numerator : ENNReal :=
      translations ^ 2 * mass ^ 3
    have hmass_scaled :
        512 * mass ^ 3 ≥
          Kakeya.realRpowENN delta (6 + 12 * eta) *
            localBlock.sourcePoints.enncard ^ 3 := by
      have h := mul_le_mul_left' hmass_power (512 : ENNReal)
      calc
        Kakeya.realRpowENN delta (6 + 12 * eta) *
              localBlock.sourcePoints.enncard ^ 3 =
            (512 : ENNReal) *
              ((1 / 512 : ENNReal) *
                (Kakeya.realRpowENN delta (6 + 12 * eta) *
                  localBlock.sourcePoints.enncard ^ 3)) := by
            rw [one_div]
            rw [← mul_assoc,
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
              one_mul]
        _ ≤ 512 * mass ^ 3 := by
          simpa [mul_assoc] using h
    have htarget_denominator :
        target * denominator =
          translations ^ 2 *
            (8000 * fiberCap ^ 3 *
              (Kakeya.realRpowENN delta (6 + 12 * eta) *
                localBlock.sourcePoints.enncard ^ 3)) := by
      dsimp only [target, denominator]
      rw [hdelta_factor]
      have hpower :
          Kakeya.realRpowENN delta
                (3 + 12 * eta +
                  3 * parameterBlockProjectionPYZLoss epsilon) *
              Kakeya.realRpowENN delta 3 *
              ENNReal.ofReal
                (Real.rpow delta
                  (-3 * parameterBlockProjectionPYZLoss epsilon)) =
            Kakeya.realRpowENN delta (6 + 12 * eta) := by
        have hfirst :
            Kakeya.realRpowENN delta
                  (3 + 12 * eta +
                    3 * parameterBlockProjectionPYZLoss epsilon) *
                Kakeya.realRpowENN delta 3 =
              Kakeya.realRpowENN delta
                (6 + 12 * eta +
                  3 * parameterBlockProjectionPYZLoss epsilon) := by
          rw [← realRpowENN_add hdelta]
          congr 1
          ring
        rw [hfirst]
        have hnegative :
            ENNReal.ofReal
                (Real.rpow delta
                  (-3 * parameterBlockProjectionPYZLoss epsilon)) =
              Kakeya.realRpowENN delta
                (-3 * parameterBlockProjectionPYZLoss epsilon) := rfl
        rw [hnegative, ← realRpowENN_add hdelta]
        congr 1
        ring
      calc
        translations ^ 2 *
              Kakeya.realRpowENN delta
                (3 + 12 * eta +
                  3 * parameterBlockProjectionPYZLoss epsilon) *
              localBlock.sourcePoints.enncard ^ 3 *
              (8000 * Kakeya.realRpowENN delta 3 *
                fiberCap ^ 3 *
                ENNReal.ofReal
                  (Real.rpow delta
                    (-3 * parameterBlockProjectionPYZLoss epsilon))) =
            translations ^ 2 * (8000 * fiberCap ^ 3 *
              ((Kakeya.realRpowENN delta
                  (3 + 12 * eta +
                    3 * parameterBlockProjectionPYZLoss epsilon) *
                Kakeya.realRpowENN delta 3 *
                ENNReal.ofReal
                  (Real.rpow delta
                    (-3 * parameterBlockProjectionPYZLoss epsilon))) *
                localBlock.sourcePoints.enncard ^ 3)) := by
              ring
        _ = translations ^ 2 *
              (8000 * fiberCap ^ 3 *
                (Kakeya.realRpowENN delta (6 + 12 * eta) *
                  localBlock.sourcePoints.enncard ^ 3)) := by
              rw [hpower]
    have hconstant :
        parameterBlockProjectionMonomialConstant =
          8000 * 512 * fiberCap ^ 3 := by
      simp [parameterBlockProjectionMonomialConstant, fiberCap]
      norm_num
    have hcross :
        target * denominator ≤
          parameterBlockProjectionMonomialConstant * numerator := by
      rw [htarget_denominator, hconstant]
      dsimp only [numerator]
      calc
        translations ^ 2 *
              (8000 * fiberCap ^ 3 *
                (Kakeya.realRpowENN delta (6 + 12 * eta) *
                  localBlock.sourcePoints.enncard ^ 3)) ≤
            translations ^ 2 *
              (8000 * fiberCap ^ 3 * (512 * mass ^ 3)) := by
          gcongr
        _ = (8000 * 512 * fiberCap ^ 3) *
              (translations ^ 2 * mass ^ 3) := by
          ring
    have hquotient :
        target ≤
          parameterBlockProjectionMonomialConstant *
            (numerator / denominator) := by
      have hrewrite :
          parameterBlockProjectionMonomialConstant *
              (numerator / denominator) =
            (parameterBlockProjectionMonomialConstant *
              numerator) / denominator := by
        simp only [div_eq_mul_inv]
        ring
      rw [hrewrite]
      exact
        (ENNReal.le_div_iff_mul_le
          (Or.inl hdenominator_zero)
          (Or.inl hdenominator_top)).2 hcross
    simpa [target, numerator, denominator] using hquotient
  exact hscaled.trans (mul_le_mul_left' hvolume_flat _)

end Kakeya.Assouad
