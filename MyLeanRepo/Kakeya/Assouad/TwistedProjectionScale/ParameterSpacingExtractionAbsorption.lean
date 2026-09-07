import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FrostmanToKatzTaoWeightedCard
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingSelectedCellFrostman

/-!
# Absorb the Lemma 7.10 Katz--Tao extraction loss
-/

noncomputable section

namespace Kakeya.Assouad

theorem exists_parameterSpacing_extraction_absorption
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ,
        0 < delta →
        delta ≤ delta₀ →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            ∀ C lambda : ENNReal,
              ∀ clustered :
                  TubeParameterClusterFrostmanData
                    F Y C lambda delta,
                ∀ profile :
                    ParameterSpacingProfileAssemblyData
                      (epsilon := epsilon) clustered,
                  ∀ selectedCell :
                      ParameterSpacingSelectedCellData profile,
                    let fineScale :=
                      normalizedParameterBlockFineScale
                        delta selectedCell.blockScale
                    weightedFrostmanToKatzTaoConstant
                        (1 - epsilon ^ 2) *
                        ENNReal.ofReal
                          (1 + Real.log fineScale⁻¹) *
                        Kakeya.realRpowENN fineScale
                          (7 * epsilon ^ 2) ≤
                      100000 := by
  let extractionConstant :=
    weightedFrostmanToKatzTaoConstant
      (1 - epsilon ^ 2)
  have hextraction_top :
      extractionConstant ≠ ⊤ := by
    dsimp only [extractionConstant,
      weightedFrostmanToKatzTaoConstant]
    exact ENNReal.ofReal_ne_top
  have hepsilon_four : 0 < epsilon ^ 4 := by
    positivity
  rcases exists_delta_log_absorbed_ennreal
      extractionConstant hextraction_top
      hepsilon_four (n := 1) (by norm_num) with
    ⟨delta₀, hdelta₀, hdelta₀_one, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀_one, ?_⟩
  intro delta hdelta hdelta_le
    F Y C lambda clustered profile selectedCell
  let fineScale :=
    normalizedParameterBlockFineScale
      delta selectedCell.blockScale
  have hblock : 0 < selectedCell.blockScale :=
    selectedCell.blockScale_pos
  have hfine_pos : 0 < fineScale := by
    dsimp only [fineScale,
      normalizedParameterBlockFineScale]
    positivity
  have hblock_one :
      selectedCell.blockScale ≤ 1 := by
    linarith [selectedCell.blockScale_small]
  have hdelta_fine : delta ≤ fineScale := by
    dsimp only [fineScale,
      normalizedParameterBlockFineScale]
    calc
      delta = delta / 1 := by ring
      _ ≤ delta / selectedCell.blockScale := by
        exact div_le_div_of_nonneg_left
          hdelta.le hblock hblock_one
  have hfine_delta_power :
      fineScale ≤ Real.rpow delta (epsilon ^ 2) :=
    parameterSpacing_selectedCell_fineScale_le_delta_power
      selectedCell hdelta
  have hlog :
      ENNReal.ofReal (1 + Real.log fineScale⁻¹) ≤
        ENNReal.ofReal (1 + Real.log delta⁻¹) := by
    apply ENNReal.ofReal_mono
    gcongr
  have hpower :
      Kakeya.realRpowENN fineScale
          (7 * epsilon ^ 2) ≤
        Kakeya.realRpowENN delta
          (7 * epsilon ^ 4) := by
    simp only [Kakeya.realRpowENN]
    apply ENNReal.ofReal_mono
    calc
      Real.rpow fineScale (7 * epsilon ^ 2) ≤
          Real.rpow
            (Real.rpow delta (epsilon ^ 2))
            (7 * epsilon ^ 2) :=
        Real.rpow_le_rpow hfine_pos.le
          hfine_delta_power
          (by positivity)
      _ = Real.rpow delta (7 * epsilon ^ 4) := by
        calc
          Real.rpow
                (Real.rpow delta (epsilon ^ 2))
                (7 * epsilon ^ 2) =
              Real.rpow delta
                ((epsilon ^ 2) *
                  (7 * epsilon ^ 2)) :=
            (Real.rpow_mul hdelta.le
              (epsilon ^ 2) (7 * epsilon ^ 2)).symm
          _ = Real.rpow delta (7 * epsilon ^ 4) := by
            congr 1
            ring
  have hlog_absorb :
      extractionConstant *
          ENNReal.ofReal
            (1 + Real.log delta⁻¹) ≤
        Kakeya.realRpowENN delta
          (-(epsilon ^ 4)) := by
    simpa using
      habsorb delta hdelta hdelta_le
  have hdelta_one : delta ≤ 1 :=
    hdelta_le.trans hdelta₀_one
  have hfinal_power :
      Kakeya.realRpowENN delta
          (6 * epsilon ^ 4) ≤ 1 := by
    simp only [Kakeya.realRpowENN]
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
    apply ENNReal.ofReal_mono
    simpa using
      Real.rpow_le_one hdelta.le hdelta_one
        (by positivity : 0 ≤ 6 * epsilon ^ 4)
  calc
    weightedFrostmanToKatzTaoConstant
          (1 - epsilon ^ 2) *
          ENNReal.ofReal
            (1 + Real.log fineScale⁻¹) *
          Kakeya.realRpowENN fineScale
            (7 * epsilon ^ 2) =
        extractionConstant *
          ENNReal.ofReal
            (1 + Real.log fineScale⁻¹) *
          Kakeya.realRpowENN fineScale
            (7 * epsilon ^ 2) := by rfl
    _ ≤
        (extractionConstant *
          ENNReal.ofReal
            (1 + Real.log delta⁻¹)) *
          Kakeya.realRpowENN delta
            (7 * epsilon ^ 4) := by
      gcongr
    _ ≤
        Kakeya.realRpowENN delta
            (-(epsilon ^ 4)) *
          Kakeya.realRpowENN delta
            (7 * epsilon ^ 4) := by
      gcongr
    _ =
        Kakeya.realRpowENN delta
          (6 * epsilon ^ 4) := by
      rw [← realRpowENN_add hdelta]
      congr 1
      ring
    _ ≤ 1 := hfinal_power
    _ ≤ 100000 := by norm_num

end Kakeya.Assouad
