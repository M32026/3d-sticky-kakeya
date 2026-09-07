import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedFineVolume
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedLayerLocalVolumeBranchesInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedLayerFixedAmbientVolumeAssembly

/-!
# Lambda-aware fixed-bin local-volume branches
-/

open MeasureTheory

namespace Kakeya.Cinematic

theorem ambient_restricted_selected_layer_local_volume_branches :
    AmbientRestrictedSelectedLayerLocalVolumeBranchesStatement := by
  intro hCancel
  intro family E K D delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume
    fineSetup coarseSetup massExponent refinement degreeSetup
    q_fiber fiberBound fiberCoefficient heavySetup radius A cover
    C_positive C_singleton retention parentArea tangencyScale cardUpper
    hA hCpos hCsing hret hfiberCoefficient hparentArea htangencyScale
    hC_shading hdelta hcardUpper hambientCard hpositiveLog
    hsingletonLog cardinalityResult
  let ambientCard :=
    (data.ambientSource.cluster center (3 * tRep)).card
  let selected := refinement.selected.card
  let support := 2 ^ heavySetup.supportLevel
  let layerMass : ℝ :=
    ((2 : ENNReal) ^ refinement.layer.val * refinement.cutoff).toReal
  let fineArea : ℝ :=
    ambientRestrictedSelectedFineGeometricArea
      C_shading delta C_R tRep DeltaRep
  let layerFactor : ℝ := ((2 * refinement.massFactor : ℕ) : ℝ)
  let positiveBase : ℝ :=
    ambientRestrictedPositiveLayerBaseCoefficientOfFiber
      fiberCoefficient
      (Nat.log2 refinement.selected.card + 1)
      heavySetup.degreeLoss
      (Nat.log2 heavySetup.ambient.card + 1)
      retention tangencyScale cover.centers.card C_positive
      coarseSetup.tangency A data.mu
  let singletonBase : ℝ :=
    ambientRestrictedSingletonLayerBaseCoefficientOfFiber
      fiberCoefficient
      (Nat.log2 refinement.selected.card + 1)
      heavySetup.degreeLoss
      (Nat.log2 heavySetup.ambient.card + 1)
      retention tangencyScale cover.centers.card C_singleton
      coarseSetup.tangency A data.mu
  have hLambda_pos :
      0 <
        (2 : ENNReal) ^ refinement.layer.val * refinement.cutoff :=
    ENNReal.mul_pos (by simp) refinement.cutoff_pos.ne'
  have hLambda_ne_top :
      (2 : ENNReal) ^ refinement.layer.val *
          refinement.cutoff ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) refinement.cutoff_ne_top
  have hlayerMass : 0 < layerMass := by
    exact ENNReal.toReal_pos hLambda_pos.ne' hLambda_ne_top
  have hfineArea : 0 ≤ fineArea := by
    simp only [fineArea, ambientRestrictedSelectedFineGeometricArea]
    positivity
  have hlayerFine : layerMass ≤ fineArea := by
    exact ambient_restricted_selected_layer_mass_le_fine_area
      data center hE fineSetup coarseSetup refinement
        hC_shading hdelta
  have hlayerFactor : 0 ≤ layerFactor := by
    positivity
  have hvolume :
      volume (ambientRestrictedSet data center) ≤
        (selected : ENNReal) *
          ENNReal.ofReal (layerFactor * layerMass) := by
    simpa [selected, layerFactor, layerMass] using
      ambient_restricted_selected_fine_volume_of_layer_toReal
        data center hE fineSetup coarseSetup refinement
  have htangency_nonneg : 0 ≤ coarseSetup.tangency := by
    linarith [coarseSetup.tangency_ge_five]
  have hfiniteLoss :
      0 ≤ 24 * fiberCoefficient *
        ((Nat.log2 refinement.selected.card : ℝ) + 1) *
        (heavySetup.degreeLoss : ℝ) *
        ((Nat.log2 heavySetup.ambient.card : ℝ) + 1) *
        Real.rpow retention (-1) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity) hfiberCoefficient)
            (by positivity))
          (by positivity))
        (by positivity))
      (Real.rpow_nonneg hret.le _)
  have htangencyPower :
      0 ≤ Real.rpow tangencyScale (3 / 4 : ℝ) :=
    Real.rpow_nonneg htangencyScale _
  have hmuPower :
      0 ≤ Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hpositiveBase : 0 ≤ positiveBase := by
    simp only [positiveBase,
      ambientRestrictedPositiveLayerBaseCoefficientOfFiber]
    have hcluster :
        0 ≤ (cover.centers.card : ℝ) ^ 2 *
          (C_positive * Real.rpow coarseSetup.tangency C_positive *
            Real.rpow A C_positive) := by
      exact mul_nonneg (sq_nonneg _) <|
        mul_nonneg
          (mul_nonneg (by linarith)
            (Real.rpow_nonneg htangency_nonneg _))
          (Real.rpow_nonneg (by linarith) _)
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hfiniteLoss htangencyPower) hcluster)
      hmuPower
  have hsingletonBase : 0 ≤ singletonBase := by
    simp only [singletonBase,
      ambientRestrictedSingletonLayerBaseCoefficientOfFiber]
    have hcluster :
        0 ≤ (cover.centers.card : ℝ) ^ 2 *
          (C_singleton * Real.rpow coarseSetup.tangency C_singleton *
            Real.rpow A C_singleton) := by
      exact mul_nonneg (sq_nonneg _) <|
        mul_nonneg
          (mul_nonneg (by linarith)
            (Real.rpow_nonneg htangency_nonneg _))
          (Real.rpow_nonneg (by linarith) _)
    have hcentersPower :
        0 ≤ Real.rpow
          (2 * (cover.centers.card : ℝ)) (3 / 2 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hfiniteLoss htangencyPower)
          hcluster)
        hcentersPower)
      hmuPower
  cases cardinalityResult with
  | positive hcard =>
      have hcard' :
          (selected : ℝ) ≤
            (positiveBase *
                Real.rpow (parentArea / layerMass) (1 / 4 : ℝ)) *
              Real.rpow
                (8 * (cover.centers.card : ℝ) *
                  (ambientCard : ℝ))
                (3 / 2 : ℝ) *
              Real.log
                (8 * (cover.centers.card : ℝ) *
                  (ambientCard : ℝ) / (support : ℝ)) := by
        convert hcard using 1
        simp [selected, ambientCard, support, layerMass, positiveBase,
          ambientRestrictedPositiveLayerBaseCoefficientOfFiber,
          ambientRestrictedPositiveCardinalityCoefficientOfFiber]
        ring
      have hresult :=
        selected_layer_fixed_ambient_volume_assembly
          hCancel fixed_ambient_rpow_fine_volume_assembly
          (E := ambientRestrictedSet data center)
          selected ambientCard (8 * (cover.centers.card : ℝ))
          cardUpper positiveBase
          (Real.log
            (8 * (cover.centers.card : ℝ) *
              (ambientCard : ℝ) / (support : ℝ)))
          layerFactor parentArea fineArea layerMass
          (by positivity) hcardUpper hambientCard hpositiveBase
          hpositiveLog hlayerFactor hparentArea hfineArea
          hlayerMass hlayerFine hcard' hvolume
      exact AmbientRestrictedSelectedLocalVolumeResult.positive <| by
        simpa [selected, ambientCard, support, layerFactor, fineArea,
          positiveBase, ambientRestrictedLayerLinearizedLocalCoefficient]
          using hresult
  | singleton hcard =>
      have hcard' :
          (selected : ℝ) ≤
            (singletonBase *
                Real.rpow (parentArea / layerMass) (1 / 4 : ℝ)) *
              Real.rpow (2 * (ambientCard : ℝ)) (3 / 2 : ℝ) *
              Real.log (2 * (ambientCard : ℝ)) := by
        convert hcard using 1
        simp [selected, ambientCard, layerMass, singletonBase,
          ambientRestrictedSingletonLayerBaseCoefficientOfFiber,
          ambientRestrictedSingletonCardinalityCoefficientOfFiber]
        ring
      have hresult :=
        selected_layer_fixed_ambient_volume_assembly
          hCancel fixed_ambient_rpow_fine_volume_assembly
          (E := ambientRestrictedSet data center)
          selected ambientCard 2 cardUpper singletonBase
          (Real.log (2 * (ambientCard : ℝ)))
          layerFactor parentArea fineArea layerMass
          (by norm_num) hcardUpper hambientCard hsingletonBase
          hsingletonLog hlayerFactor hparentArea hfineArea
          hlayerMass hlayerFine hcard' hvolume
      exact AmbientRestrictedSelectedLocalVolumeResult.singleton <| by
        simpa [selected, ambientCard, layerFactor, fineArea,
          singletonBase, ambientRestrictedLayerLinearizedLocalCoefficient]
          using hresult

end Kakeya.Cinematic
