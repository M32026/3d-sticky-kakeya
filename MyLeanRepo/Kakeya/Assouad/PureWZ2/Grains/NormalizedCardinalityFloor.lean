import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PolylogAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SelectedCardinalityCancellation
import MyLeanRepo.Kakeya.Assouad.TubeVolumeRatio
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling

/-!
# Cardinality inherited by a cropped normalization

The normalization record retains a polylogarithmic fraction of the ordinary
source shaded mass before applying its affine frame and dense cubicalization.
The retained ordinary shading still lives on the selected ordinary tube
family, so its mass is at most the nominal mass of that family.  Since the
cropped family is index-equivalent to the selected family, this transports a
source union-volume lower bound into a cardinality lower bound for the exact
cropped family used downstream.

No support or nearby-CWA property of the cropped family is used here.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- Below unit scale the normalization's polylogarithmic retention factor is
strictly positive and finite. -/
lemma pure_refinement_fraction_pos_ne_top
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (logExponent : ℕ) :
    0 < wz2PaperPureRefinementFraction delta logExponent ∧
      wz2PaperPureRefinementFraction delta logExponent ≠ ⊤ := by
  have hlog : 0 < Real.log (1 / delta) :=
    Real.log_pos (one_lt_one_div hdelta hdeltaOne)
  let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  have hlogZero : logTerm ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hlog).ne'
  have hlogTop : logTerm ≠ ⊤ := ENNReal.ofReal_ne_top
  have hinvPos : 0 < logTerm⁻¹ := ENNReal.inv_pos.mpr hlogTop
  have hinvTop : logTerm⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hlogZero
  have hpowPos : 0 < logTerm⁻¹ ^ logExponent := by
    exact (pow_ne_zero logExponent hinvPos.ne').bot_lt
  have hpowTop : logTerm⁻¹ ^ logExponent ≠ ⊤ := by
    exact ENNReal.pow_ne_top hinvTop
  simpa [wz2PaperPureRefinementFraction, logTerm] using
    And.intro hpowPos hpowTop

/-- A normalization's selected/cropped family cardinality pays for the
retained ordinary source volume. -/
theorem normalized_cropped_cardinality_from_source_volume
    {sigma inputLoss outputLoss delta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := outputLoss) source logExponent) :
    wz2PaperPureRefinementFraction delta logExponent *
        volume source.shading.union ≤
      ENNReal.ofReal (3 * Real.pi) *
        Kakeya.realRpowENN delta 2 *
          normalized.croppedFamily.enncard := by
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 := source.extremal.delta_le_one
  have hunionMass : volume source.shading.union ≤ source.shading.mass := by
    have hunionEq : source.shading.union =
        ⋃ index : Fin source.family.card, source.shading.carrier index := by
      apply Set.ext
      intro point
      constructor
      · rintro ⟨index, hpoint⟩
        exact Set.mem_iUnion.mpr ⟨index, hpoint⟩
      · intro hpoint
        rcases Set.mem_iUnion.mp hpoint with ⟨index, hindex⟩
        exact ⟨index, hindex⟩
    rw [hunionEq]
    exact MeasureTheory.measure_iUnion_fintype_le
      volume source.shading.carrier
  have hordinaryMass : normalized.ordinaryRefined.mass ≤
      normalized.selected.family.toBodyFamily.mass := by
    apply Finset.sum_le_sum
    intro index _
    exact measure_mono (normalized.ordinaryRefined.subset_body index)
  have hselectedCard : normalized.selected.family.card =
      normalized.croppedFamily.card := by
    simpa using Fintype.card_congr normalized.indexEquiv
  have hselectedEnncard : normalized.selected.family.enncard =
      normalized.croppedFamily.enncard := by
    simp only [Kakeya.Streamlined.TubeFamily.enncard]
    rw [hselectedCard]
  have htubeVolume : Kakeya.deltaTubeVolume delta ≤
      ENNReal.ofReal (3 * Real.pi) * Kakeya.realRpowENN delta 2 := by
    have hraw := deltaTubeVolume_upper_pi hdelta
    have hreal : Real.pi * delta ^ 2 * (1 + 2 * delta) ≤
        (3 * Real.pi) * delta ^ 2 := by
      have hfactor : 1 + 2 * delta ≤ 3 := by linarith
      calc
        Real.pi * delta ^ 2 * (1 + 2 * delta) ≤
            Real.pi * delta ^ 2 * 3 := by
          exact mul_le_mul_of_nonneg_left hfactor
            (mul_nonneg Real.pi_pos.le (sq_nonneg delta))
        _ = (3 * Real.pi) * delta ^ 2 := by ring
    have hofReal := ENNReal.ofReal_mono hreal
    have hfactor : ENNReal.ofReal ((3 * Real.pi) * delta ^ 2) =
        ENNReal.ofReal (3 * Real.pi) *
          Kakeya.realRpowENN delta 2 := by
      rw [ENNReal.ofReal_mul (by positivity)]
      simp [Kakeya.realRpowENN, Real.rpow_two]
    exact hraw.trans (by simpa [hfactor] using hofReal)
  calc
    wz2PaperPureRefinementFraction delta logExponent *
        volume source.shading.union ≤
      wz2PaperPureRefinementFraction delta logExponent *
        source.shading.mass := by gcongr
    _ ≤ normalized.ordinaryRefined.mass := normalized.retained_mass
    _ ≤ normalized.selected.family.toBodyFamily.mass := hordinaryMass
    _ = normalized.selected.family.enncard *
        Kakeya.deltaTubeVolume delta := by
      rw [tubeFamily_mass_eq_nominal]
      rfl
    _ ≤ normalized.selected.family.enncard *
        (ENNReal.ofReal (3 * Real.pi) *
          Kakeya.realRpowENN delta 2) := by gcongr
    _ = ENNReal.ofReal (3 * Real.pi) *
        Kakeya.realRpowENN delta 2 *
          normalized.croppedFamily.enncard := by
      rw [hselectedEnncard]
      ring

/-- A power lower bound for the source union transfers through normalization
after paying an explicit polylogarithmic slack certificate. -/
theorem normalized_cropped_cardinality_from_power_floor
    {sigma inputLoss outputLoss delta sourceExponent targetExponent : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := outputLoss) source logExponent)
    (hdeltaOne : delta < 1)
    (hsourceFloor : Kakeya.realRpowENN delta sourceExponent ≤
      volume source.shading.union)
    (hpolylog :
      (wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
          Kakeya.realRpowENN delta targetExponent ≤
        Kakeya.realRpowENN delta sourceExponent) :
    Kakeya.realRpowENN delta targetExponent ≤
      ENNReal.ofReal (3 * Real.pi) *
        Kakeya.realRpowENN delta 2 *
          normalized.croppedFamily.enncard := by
  let fraction := wz2PaperPureRefinementFraction delta logExponent
  have hfraction := pure_refinement_fraction_pos_ne_top
    source.extremal.delta_pos hdeltaOne logExponent
  have hinverseFloor : fraction⁻¹ *
      Kakeya.realRpowENN delta targetExponent ≤
        volume source.shading.union :=
    hpolylog.trans (hsourceFloor.trans le_rfl)
  have htargetFloor : Kakeya.realRpowENN delta targetExponent ≤
      fraction * volume source.shading.union := by
    exact (ENNReal.inv_mul_le_iff hfraction.1.ne' hfraction.2).mp
      hinverseFloor
  exact htargetFloor.trans <| by
    simpa [fraction] using
      normalized_cropped_cardinality_from_source_volume normalized

/-- Choose a sufficiently small normalized critical configuration so that
the critical volume floor and the normalization's polylogarithmic loss yield
an explicit cardinality power floor on the exact cropped family.

The structural loss is chosen by `critical_floor` before normalization; this
is the quantifier order used in the paper's Lemma 11 preparation. -/
theorem exists_normalized_critical_cardinality_floor
    {sigma : ℝ} {normalizationExponent : ℕ}
    (critical : PureWZ2CriticalPackage sigma)
    (hNormalization :
      PureWZ2CroppedCriticalNormalizationAt normalizationExponent)
    (floorLoss structuralBudget powerGap deltaTarget : ℝ)
    (hfloorLoss : 0 < floorLoss)
    (hstructuralBudget : 0 < structuralBudget)
    (hpowerGap : 0 < powerGap)
    (hdeltaTarget : 0 < deltaTarget) :
    ∃ (structuralLoss inputLoss delta : ℝ)
      (source : PureWZ2ExtremalConfiguration sigma inputLoss delta)
      (normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := structuralLoss) source normalizationExponent),
      0 < structuralLoss ∧
      structuralLoss ≤ structuralBudget ∧
      0 < inputLoss ∧
      inputLoss ≤ structuralLoss ∧
      0 < delta ∧
      delta ≤ deltaTarget ∧
      Kakeya.realRpowENN delta (sigma + floorLoss + powerGap) ≤
        ENNReal.ofReal (3 * Real.pi) *
          Kakeya.realRpowENN delta 2 *
            normalized.croppedFamily.enncard ∧
      (ENNReal.ofReal (3 * Real.pi))⁻¹ *
          Kakeya.realRpowENN delta
            (sigma + floorLoss + powerGap + structuralLoss) ≤
        normalized.croppedRefined.mass := by
  rcases critical.critical_floor floorLoss structuralBudget
      hfloorLoss hstructuralBudget with
    ⟨structuralLoss, floorDelta, hstructuralLoss,
      hstructuralLossBudget, hfloorDelta, hfloorDeltaOne, hfloor⟩
  rcases polylog_absorption_bound powerGap normalizationExponent hpowerGap with
    ⟨polylogThreshold, hpolylogThreshold, hpolylogThresholdOne,
      hpolylogBound⟩
  let deltaRequest : ℝ :=
    min deltaTarget
      (min floorDelta (min (1 / 24 : ℝ) (1 / polylogThreshold)))
  have hdeltaRequest : 0 < deltaRequest := by
    dsimp only [deltaRequest]
    positivity
  rcases hNormalization sigma critical structuralLoss deltaRequest
      hstructuralLoss hdeltaRequest with
    ⟨inputLoss, delta, hinputLoss, hinputLossStructural, hdelta,
      hdeltaRequestBound, source, ⟨normalized⟩⟩
  have hdeltaTargetBound : delta ≤ deltaTarget :=
    hdeltaRequestBound.trans (min_le_left _ _)
  have hdeltaFloor : delta ≤ floorDelta :=
    hdeltaRequestBound.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaSmall : delta ≤ (1 / 24 : ℝ) :=
    hdeltaRequestBound.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaOne : delta < 1 := by linarith
  have hdeltaInvThreshold : delta ≤ 1 / polylogThreshold :=
    hdeltaRequestBound.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  have hinverseThreshold : polylogThreshold ≤ 1 / delta := by
    apply (le_div_iff₀ hdelta).2
    calc
      polylogThreshold * delta ≤
          polylogThreshold * (1 / polylogThreshold) := by gcongr
      _ = 1 := by field_simp [hpolylogThreshold.ne']
  have hsourceExtremal : WZ2PaperPureIsExtremal
      sigma structuralLoss source.family source.shading :=
    source.extremal.mono_loss hinputLossStructural
  have hsourceFloor :
      Kakeya.realRpowENN delta (sigma + floorLoss) ≤
        volume source.shading.union :=
    hfloor delta hdelta hdeltaFloor source.family
      hsourceExtremal.nonempty source.shading
      hsourceExtremal.cwa_nearby_scales hsourceExtremal.dense
  have hpolylog :
      (wz2PaperPureRefinementFraction
          delta normalizationExponent)⁻¹ *
          Kakeya.realRpowENN delta (sigma + floorLoss + powerGap) ≤
        Kakeya.realRpowENN delta (sigma + floorLoss) := by
    refine phase1_hslack
      (delta := delta)
      (midLoss := sigma + floorLoss + powerGap)
      (inputLoss := sigma + floorLoss)
      (logExponent := normalizationExponent)
      hdelta hdeltaOne ?_ ?_
      (X_polylog := polylogThreshold) hpolylogThreshold ?_
      hinverseThreshold
    · linarith [critical.sigma_pos]
    · linarith
    · intro x hx
      simpa [add_sub_cancel_left] using hpolylogBound x hx
  have hcardinality := normalized_cropped_cardinality_from_power_floor
    normalized hdeltaOne hsourceFloor hpolylog
  let C : ENNReal := ENNReal.ofReal (3 * Real.pi)
  have hCZero : C ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hCTop : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbody : Kakeya.realRpowENN delta 2 *
      normalized.croppedFamily.enncard ≤
        (wz1PaperBodyFamily normalized.croppedFamily).mass :=
    paperBodyFamily_mass_lower_rpow_two hdelta
      (hdeltaSmall.trans (by norm_num)) normalized.line_class
  have hdenseMass : Kakeya.realRpowENN delta structuralLoss *
      (Kakeya.realRpowENN delta 2 *
        normalized.croppedFamily.enncard) ≤
          normalized.croppedRefined.mass := by
    exact (mul_le_mul_left' hbody
      (Kakeya.realRpowENN delta structuralLoss)).trans
      normalized.final_extremal.dense
  have hmassFloor : C⁻¹ *
      Kakeya.realRpowENN delta
        (sigma + floorLoss + powerGap + structuralLoss) ≤
      normalized.croppedRefined.mass := by
    have hscaled := mul_le_mul_left' hcardinality
      (C⁻¹ * Kakeya.realRpowENN delta structuralLoss)
    have hcancel : C⁻¹ * C = 1 := ENNReal.inv_mul_cancel hCZero hCTop
    calc
      C⁻¹ * Kakeya.realRpowENN delta
          (sigma + floorLoss + powerGap + structuralLoss) =
          C⁻¹ * Kakeya.realRpowENN delta structuralLoss *
            Kakeya.realRpowENN delta (sigma + floorLoss + powerGap) := by
        rw [Kakeya.Assouad.realRpowENN_add hdelta]
        ring
      _ ≤ C⁻¹ * Kakeya.realRpowENN delta structuralLoss *
          (C * (Kakeya.realRpowENN delta 2 *
            normalized.croppedFamily.enncard)) := by
        simpa [C, mul_assoc] using hscaled
      _ = Kakeya.realRpowENN delta structuralLoss *
          (Kakeya.realRpowENN delta 2 *
            normalized.croppedFamily.enncard) := by
        rw [show C⁻¹ * Kakeya.realRpowENN delta structuralLoss *
            (C * (Kakeya.realRpowENN delta 2 *
              normalized.croppedFamily.enncard)) =
            (C⁻¹ * C) *
              (Kakeya.realRpowENN delta structuralLoss *
                (Kakeya.realRpowENN delta 2 *
                  normalized.croppedFamily.enncard)) by ring,
          hcancel, one_mul]
      _ ≤ normalized.croppedRefined.mass := hdenseMass
  exact ⟨structuralLoss, inputLoss, delta, source, normalized,
    hstructuralLoss, hstructuralLossBudget, hinputLoss,
    hinputLossStructural, hdelta, hdeltaTargetBound, hcardinality,
    by simpa [C] using hmassFloor⟩

end Kakeya.Assouad.PureWZ2

end
