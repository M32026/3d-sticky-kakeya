import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionAbsorption
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionCellBound
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionCountLower
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionMonomialLower

/-!
# Paper Lemma 7.12 projection arithmetic

Assemble the corrected selected-scale cinematic lower bound against the
linear projected-cell globalization cost.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Complete fixed coefficient paid by the Lemma 7.12 arithmetic. -/
def parameterBlockProjectionTotalConstant (base : ℕ) : ENNReal :=
  parameterBlockProjectionMonomialConstant *
    (100000 : ENNReal) ^ 5 *
    parameterBlockProjectionCellConstant base

theorem parameter_block_projection_arithmetic :
    ParameterBlockProjectionArithmeticStatement := by
  intro base hbase epsilon eta
    hepsilon hepsilon_small heta heta_small
  have htotal_top :
      parameterBlockProjectionTotalConstant base ≠ ⊤ := by
    unfold parameterBlockProjectionTotalConstant
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · unfold parameterBlockProjectionMonomialConstant
        apply ENNReal.mul_ne_top
        · norm_num
        · exact ENNReal.pow_ne_top (by
            norm_num [parameterBlockRepresentativeCopiedFiberCap])
      · exact ENNReal.pow_ne_top (by norm_num)
    · unfold parameterBlockProjectionCellConstant
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)
          ENNReal.coe_ne_top)
        ENNReal.ofReal_ne_top
  rcases exists_parameterBlockProjection_absorption
      (parameterBlockProjectionTotalConstant base)
      htotal_top hepsilon hepsilon_small heta heta_small with
    ⟨deltaAbsorb, hdeltaAbsorb,
      hdeltaAbsorb_one, hAbsorb⟩
  let delta₀ := min deltaAbsorb (1 / 2)
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_one : delta₀ < 1 :=
    (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨delta₀, hdelta₀, hdelta₀_one, ?_⟩
  intro delta hdelta hdelta_le F Y f prepared hprepared
    windowedShading C lambda clustered
    localBlock representatives amplification pullback
    level cellSystem
  let rho := localBlock.blockScale
  let ratio := delta / rho
  let loss :=
    12 * eta +
      3 * parameterBlockProjectionPYZLoss epsilon
  let effective :=
    parameterBlockProjectionEffectiveExponent epsilon eta
  let monomialConstant :=
    parameterBlockProjectionMonomialConstant
  let countConstant : ENNReal := (100000 : ENNReal) ^ 5
  let cellConstant :=
    parameterBlockProjectionCellConstant base
  let totalConstant :=
    parameterBlockProjectionTotalConstant base
  let localVolume :=
    volume (twistedUnion pullback.shading f)
  let cellFactor :=
    4 *
      (projectedFiberOSCinematicCellBound
        prepared.base level 131
        (parameterBlockProjectionRadiusBlocks base) : ENNReal) *
      projectedFiberOSPreparedCellThickeningBound prepared rho
  have hdelta_absorb : delta ≤ deltaAbsorb :=
    hdelta_le.trans (min_le_left _ _)
  have hdelta_half : delta ≤ 1 / 2 :=
    hdelta_le.trans (min_le_right _ _)
  have hrho : 0 < rho := localBlock.blockScale_pos
  have hdelta_rho : delta ≤ rho := localBlock.fine_le_block
  have hrho_one : rho ≤ 1 := by
    dsimp only [rho]
    linarith [localBlock.blockScale_small]
  have hratio : 0 < ratio := by
    dsimp only [ratio]
    positivity
  have hratio_one : ratio ≤ 1 := by
    dsimp only [ratio]
    exact (div_le_one hrho).2 hdelta_rho
  have hloss : 0 ≤ loss := by
    dsimp only [loss, parameterBlockProjectionPYZLoss]
    positivity
  have hmonomial :
      amplification.translations.enncard ^ 2 *
          Kakeya.realRpowENN delta (3 + loss) *
          localBlock.sourcePoints.enncard ^ 3 ≤
        monomialConstant * localVolume := by
    have h :=
      parameterBlockProjection_scaled_monomial_lower
        localBlock representatives amplification pullback
        hdelta hdelta_half hepsilon
    simpa [loss, monomialConstant, localVolume,
      add_assoc] using h
  have hcentered_card :
      localBlock.centeredPoints.enncard =
        localBlock.sourcePoints.enncard :=
    parameterLocalFullBlock_centered_enncard localBlock
  have hcount :
      Kakeya.realRpowENN rho 1 *
          Kakeya.realRpowENN ratio (60 * epsilon ^ 2) *
          Kakeya.realRpowENN delta loss ≤
        countConstant *
          (amplification.translations.enncard ^ 2 *
            Kakeya.realRpowENN delta (3 + loss) *
            localBlock.sourcePoints.enncard ^ 3) := by
    have hpoints :
        Kakeya.realRpowENN
            (rho / delta) (1 - 20 * epsilon ^ 2) ≤
          100000 * localBlock.sourcePoints.enncard := by
      calc
        Kakeya.realRpowENN
              (rho / delta) (1 - 20 * epsilon ^ 2)
            ≤ 100000 * localBlock.centeredPoints.enncard :=
          localBlock.local_cardinality
        _ = 100000 * localBlock.sourcePoints.enncard := by
          rw [hcentered_card]
    have h :=
      parameterBlockProjection_count_product_lower
        (loss := loss)
        hdelta hrho
        amplification.translations_card_lower
        hpoints
    simpa [ratio, countConstant] using h
  have hcount_volume :
      Kakeya.realRpowENN rho 1 *
          Kakeya.realRpowENN ratio (60 * epsilon ^ 2) *
          Kakeya.realRpowENN delta loss ≤
        countConstant * monomialConstant * localVolume := by
    calc
      Kakeya.realRpowENN rho 1 *
            Kakeya.realRpowENN ratio (60 * epsilon ^ 2) *
            Kakeya.realRpowENN delta loss
          ≤ countConstant *
              (amplification.translations.enncard ^ 2 *
                Kakeya.realRpowENN delta (3 + loss) *
                localBlock.sourcePoints.enncard ^ 3) := hcount
      _ ≤ countConstant * (monomialConstant * localVolume) := by
        gcongr
      _ = countConstant * monomialConstant * localVolume := by
        ring
  have hratio_loss :
      Kakeya.realRpowENN ratio (loss / epsilon ^ 2) ≤
        Kakeya.realRpowENN delta loss := by
    exact
      parameterBlockProjection_ratio_loss_le_delta_loss
        hdelta hrho hepsilon hloss
        localBlock.separated_scale
  have heffective :
      effective =
        60 * epsilon ^ 2 + loss / epsilon ^ 2 := by
    dsimp only [effective,
      parameterBlockProjectionEffectiveExponent, loss]
  have heffective_product :
      Kakeya.realRpowENN ratio effective =
        Kakeya.realRpowENN ratio (60 * epsilon ^ 2) *
          Kakeya.realRpowENN ratio (loss / epsilon ^ 2) := by
    rw [heffective, realRpowENN_add hratio]
  have heffective_volume :
      Kakeya.realRpowENN rho 1 *
          Kakeya.realRpowENN ratio effective ≤
        countConstant * monomialConstant * localVolume := by
    rw [heffective_product]
    calc
      Kakeya.realRpowENN rho 1 *
            (Kakeya.realRpowENN ratio (60 * epsilon ^ 2) *
              Kakeya.realRpowENN ratio (loss / epsilon ^ 2))
          ≤ Kakeya.realRpowENN rho 1 *
              (Kakeya.realRpowENN ratio (60 * epsilon ^ 2) *
                Kakeya.realRpowENN delta loss) := by
        gcongr
      _ =
          Kakeya.realRpowENN rho 1 *
            Kakeya.realRpowENN ratio (60 * epsilon ^ 2) *
            Kakeya.realRpowENN delta loss := by
        ring
      _ ≤ countConstant * monomialConstant * localVolume :=
        hcount_volume
  have hcell :
      cellFactor ≤ cellConstant * ENNReal.ofReal rho := by
    have h :=
      parameterBlockProjection_cellFactor_le
        prepared base level hprepared cellSystem hrho hrho_one
    simpa [cellFactor, cellConstant, rho] using h
  have habsorb :
      totalConstant * Kakeya.realRpowENN ratio epsilon ≤
        Kakeya.realRpowENN ratio effective := by
    have h :=
      hAbsorb delta rho hdelta hdelta_absorb
        hrho hdelta_rho localBlock.separated_scale
    simpa [ratio, effective, totalConstant] using h
  have htotal :
      totalConstant =
        monomialConstant * countConstant * cellConstant := by
    simp [totalConstant,
      parameterBlockProjectionTotalConstant,
      monomialConstant, countConstant, cellConstant]
  have hscaled_goal :
      countConstant * monomialConstant *
          (Kakeya.realRpowENN ratio epsilon * cellFactor) ≤
        countConstant * monomialConstant * localVolume := by
    calc
      countConstant * monomialConstant *
            (Kakeya.realRpowENN ratio epsilon * cellFactor)
          ≤ countConstant * monomialConstant *
              (Kakeya.realRpowENN ratio epsilon *
                (cellConstant * ENNReal.ofReal rho)) := by
        gcongr
      _ =
          (totalConstant *
            Kakeya.realRpowENN ratio epsilon) *
              Kakeya.realRpowENN rho 1 := by
        rw [htotal]
        simp [Kakeya.realRpowENN, Real.rpow_one]
        ring
      _ ≤
          Kakeya.realRpowENN ratio effective *
            Kakeya.realRpowENN rho 1 := by
        gcongr
      _ =
          Kakeya.realRpowENN rho 1 *
            Kakeya.realRpowENN ratio effective := by ring
      _ ≤ countConstant * monomialConstant * localVolume :=
        heffective_volume
  have hcancel_zero :
      countConstant * monomialConstant ≠ 0 := by
    unfold countConstant monomialConstant
    apply mul_ne_zero
    · norm_num
    · unfold parameterBlockProjectionMonomialConstant
      norm_num [parameterBlockRepresentativeCopiedFiberCap]
  have hcancel_top :
      countConstant * monomialConstant ≠ ⊤ := by
    unfold countConstant monomialConstant
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (by norm_num))
      (by
        unfold parameterBlockProjectionMonomialConstant
        exact ENNReal.mul_ne_top (by norm_num)
          (ENNReal.pow_ne_top (by
            norm_num [parameterBlockRepresentativeCopiedFiberCap])))
  have hcancelled :
      Kakeya.realRpowENN ratio epsilon * cellFactor ≤
        localVolume :=
    (ENNReal.mul_le_mul_iff_right
      hcancel_zero hcancel_top).mp hscaled_goal
  dsimp only [ratio, cellFactor, localVolume, rho] at hcancelled
  simpa [mul_assoc] using hcancelled

end Kakeya.Assouad
