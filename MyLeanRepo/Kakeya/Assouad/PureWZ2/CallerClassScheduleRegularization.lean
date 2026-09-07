import MyLeanRepo.Kakeya.Assouad.PureWZ2.CompleteParentScheduleRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ParentQuotientNetSelection

/-!
# Complete-parent regularization inside one quotient caller class

Fix one caller parent from the quotient-net cover.  Mask the actual-fiber
weights outside its quotient class and apply complete-parent schedule
regularization.  The normalization weight is the class weight divided by the
ambient fine cardinality.

Positive selected weights force every surviving actual parent to remain in
the chosen caller class.  Consequently the selected fine family is a union
of complete actual fibers inside one caller fiber, retains a controlled share
of that caller's shaded mass, and satisfies pure Definition 2.12 at every
nearby scale.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Actual parents assigned to one quotient caller center. -/
def PureWZ2ParentQuotientNetSelectionData.callerActualParents
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading)
    (callerParent : Fin data.callerCoarse.card) :
    Finset (Fin nearby.scaleData.coarse.card) :=
  Finset.univ.filter fun actualParent =>
    data.net.center actualParent =
      data.callerCenter callerParent

/-- Shaded mass of one quotient caller class, measured on complete actual
fibers. -/
def PureWZ2ParentQuotientNetSelectionData.callerActualWeight
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading)
    (callerParent : Fin data.callerCoarse.card) :
    ENNReal :=
  ∑ actualParent ∈ data.callerActualParents callerParent,
    pureWZ2ActualFiberShadedMass shading actualParent

/-- Masked actual-parent weight supported on one quotient caller class. -/
def PureWZ2ParentQuotientNetSelectionData.maskedCallerActualWeight
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading)
    (callerParent : Fin data.callerCoarse.card)
    (actualParent : Fin nearby.scaleData.coarse.card) :
    ENNReal :=
  if data.net.center actualParent =
      data.callerCenter callerParent then
    pureWZ2ActualFiberShadedMass shading actualParent
  else
    0

theorem PureWZ2ParentQuotientNetSelectionData.sum_maskedCallerActualWeight
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading)
    (callerParent : Fin data.callerCoarse.card) :
    (∑ actualParent : Fin nearby.scaleData.coarse.card,
        data.maskedCallerActualWeight
          callerParent actualParent) =
      data.callerActualWeight callerParent := by
  unfold maskedCallerActualWeight
  unfold callerActualWeight callerActualParents
  rw [Finset.sum_filter]

/--
Regularize complete actual fibers inside one quotient caller class.
-/
theorem caller_class_schedule_regularization
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant R : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (callerParent : Fin quotient.callerCoarse.card)
    (fineNonempty : fine.Nonempty)
    (classWeightPos :
      0 < quotient.callerActualWeight callerParent)
    (classWeight_ne_top :
      quotient.callerActualWeight callerParent ≠ ⊤)
    (weightUpper : ENNReal)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (actualWeightUpper :
      ∀ actualParent,
        pureWZ2ActualFiberShadedMass
            shading actualParent ≤
          weightUpper *
            wz2PaperOrdinaryFullFiberCount
              fine actualNearby.scaleData.coarse
              actualParent)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate : Fin coordinateCount,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (scaleGap :
      ∀ coordinate : Fin coordinateCount,
        4 * ((scheduled coordinate).rho - delta) ≤
            actualNearby.rho ∨
          4 * (actualNearby.rho - delta) ≤
            (scheduled coordinate).rho)
    (R_pos : 0 < R)
    (R_ne_top : R ≠ ⊤)
    (R_one : 1 ≤ R)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ (scales coordinate).1 ∧
          ENNReal.ofReal (scales coordinate).1 <
            R * ENNReal.ofReal requested.1)
    (window_absorption :
      R * ambientConstant ≤ outputConstant)
    (output_ne_top : outputConstant ≠ ⊤)
    (restriction_absorption :
      wz2PaperPureNearbyRestrictionConstant
          ambientConstant
          (quotient.callerActualWeight callerParent *
            fine.enncard⁻¹)
          (max ambientConstant
            (ambientConstant *
              pureWZ2CompleteParentDegreeConstant
                actualNearby.scaleData.coarse.card coordinateCount))
          (pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card coordinateCount *
            weightUpper) ≤
        outputConstant) :
    ∃ (selectedActualParents :
        Finset (Fin actualNearby.scaleData.coarse.card))
      (complete :
        PureWZ2CompleteParentRestrictionData
          actualNearby.scaleData.cover selectedActualParents)
      (regularizationLoss selectedWeightLevel : ENNReal),
      selectedActualParents ⊆
        quotient.callerActualParents callerParent ∧
      regularizationLoss ≠ ⊤ ∧
      regularizationLoss =
        pureWZ2CompleteParentRegularizationLoss
          actualNearby.scaleData.coarse.card coordinateCount ∧
      0 < selectedWeightLevel ∧
      selectedWeightLevel ≠ ⊤ ∧
      (∀ parent ∈ selectedActualParents,
        0 <
          pureWZ2ActualFiberShadedMass shading parent) ∧
      quotient.callerActualWeight callerParent ≤
        regularizationLoss *
          ∑ parent ∈ selectedActualParents,
            pureWZ2ActualFiberShadedMass shading parent ∧
      WZ2PaperPureCWAAtNearbyScales
        complete.selectedFine.family outputConstant := by
  let classWeight :=
    quotient.callerActualWeight callerParent
  have fineENN_ne_zero : fine.enncard ≠ 0 := by
    change (fine.card : ENNReal) ≠ 0
    exact_mod_cast (ne_of_gt fineNonempty)
  have fineENN_ne_top : fine.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  let normalizationWeight :=
    classWeight * fine.enncard⁻¹
  have normalizationWeight_ne_zero :
      normalizationWeight ≠ 0 :=
    mul_ne_zero classWeightPos.ne'
      (ENNReal.inv_ne_zero.mpr fineENN_ne_top)
  have normalizationWeight_ne_top :
      normalizationWeight ≠ ⊤ :=
    ENNReal.mul_ne_top classWeight_ne_top
      (ENNReal.inv_ne_top.mpr fineENN_ne_zero)
  have normalizationIdentity :
      normalizationWeight * fine.enncard =
        classWeight := by
    dsimp only [normalizationWeight]
    rw [mul_assoc,
      ENNReal.inv_mul_cancel
        fineENN_ne_zero fineENN_ne_top,
      mul_one]
  let maskedWeight :=
    quotient.maskedCallerActualWeight callerParent
  have totalMasked :
      (∑ actualParent : Fin actualNearby.scaleData.coarse.card,
          maskedWeight actualParent) =
        classWeight := by
    exact quotient.sum_maskedCallerActualWeight callerParent
  have totalWeightLower :
      normalizationWeight * fine.enncard ≤
        ∑ actualParent : Fin actualNearby.scaleData.coarse.card,
          maskedWeight actualParent := by
    rw [normalizationIdentity, totalMasked]
  have maskedWeightUpper :
      ∀ actualParent,
        maskedWeight actualParent ≤
          weightUpper *
            wz2PaperOrdinaryFullFiberCount
              fine actualNearby.scaleData.coarse
              actualParent := by
    intro actualParent
    by_cases hclass :
        quotient.net.center actualParent =
          quotient.callerCenter callerParent
    · simp [maskedWeight,
        PureWZ2ParentQuotientNetSelectionData.maskedCallerActualWeight,
        hclass]
      exact actualWeightUpper actualParent
    · simp [maskedWeight,
        PureWZ2ParentQuotientNetSelectionData.maskedCallerActualWeight,
        hclass]
  rcases
      complete_parent_schedule_regularization
        ambient actualNearby fineNonempty maskedWeight
        normalizationWeight weightUpper
        normalizationWeight_ne_zero
        normalizationWeight_ne_top
        weightUpper_ne_top totalWeightLower
        maskedWeightUpper
        coordinateCount coordinateCountPos
        scales scheduled scaleGap
        R_pos R_ne_top R_one rounding
        window_absorption output_ne_top
        restriction_absorption
    with
    ⟨selectedActualParents, complete,
      _degreeConstant, regularizationLoss,
      selectedWeightLevel,
      _degreeTop, regularizationTop,
      regularizationEq,
      selectedWeightLevelPos,
      selectedWeightLevelTop,
      selectedWeightPos,
      retainedWeight, _selectedWeightBand,
      _cardinalityRetention, selectedCWA⟩
  have selectedSubset :
      selectedActualParents ⊆
        quotient.callerActualParents callerParent := by
    intro actualParent hselected
    have hpositive :=
      selectedWeightPos actualParent hselected
    by_contra hclass
    have hnot :
        quotient.net.center actualParent ≠
          quotient.callerCenter callerParent := by
      simpa [
        PureWZ2ParentQuotientNetSelectionData.callerActualParents,
        Finset.mem_filter
      ] using hclass
    have hzero :
        maskedWeight actualParent = 0 := by
      simp [maskedWeight,
        PureWZ2ParentQuotientNetSelectionData.maskedCallerActualWeight,
        hnot]
    rw [hzero] at hpositive
    exact lt_irrefl 0 hpositive
  have retainedWeight' :
      classWeight ≤
        regularizationLoss *
          ∑ parent ∈ selectedActualParents,
            pureWZ2ActualFiberShadedMass
              shading parent := by
    rw [← totalMasked]
    exact retainedWeight.trans_eq <| by
      congr 1
      apply Finset.sum_congr rfl
      intro parent hparent
      have hclass := selectedSubset hparent
      have hcenter :
          quotient.net.center parent =
            quotient.callerCenter callerParent :=
        (Finset.mem_filter.mp hclass).2
      simp [maskedWeight,
        PureWZ2ParentQuotientNetSelectionData.maskedCallerActualWeight,
        hcenter]
  have positiveOriginal :
      ∀ parent ∈ selectedActualParents,
        0 <
          pureWZ2ActualFiberShadedMass shading parent := by
    intro parent hparent
    have hclass := selectedSubset hparent
    have hcenter :
        quotient.net.center parent =
          quotient.callerCenter callerParent :=
      (Finset.mem_filter.mp hclass).2
    have hpositive := selectedWeightPos parent hparent
    simpa [maskedWeight,
      PureWZ2ParentQuotientNetSelectionData.maskedCallerActualWeight,
      hcenter] using hpositive
  exact
    ⟨selectedActualParents, complete,
      regularizationLoss, selectedWeightLevel,
      selectedSubset,
      regularizationTop,
      regularizationEq,
      selectedWeightLevelPos,
      selectedWeightLevelTop,
      positiveOriginal,
      retainedWeight',
      selectedCWA⟩

end Kakeya.Assouad

end
