import MyLeanRepo.Kakeya.Assouad.PureWZ2.PositiveCallerSupport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FiniteCallerCenterSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterUniformConflictDegree

/-!
# Caller-weight preselection before complete-parent regularization

Positive caller mass has no uniform lower bound.  This module performs the
existing finite caller-center weighted selection on the original quotient
caller masses before any per-caller complete-parent regularizer is run.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The positive caller centers, viewed as a subfamily of the quotient
caller family. -/
noncomputable def pureWZ2PostDeletionPositiveCallerBase
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading) :
    WZ2PaperPureTubeSubfamily quotient.callerCoarse where
  family :=
    (quotient.callerCover.hitParentSubfamily
      quotient.positiveCallerFine).family
  embedding :=
    (quotient.callerCover.hitParentSubfamily
      quotient.positiveCallerFine).embedding
  tube_eq :=
    (quotient.callerCover.hitParentSubfamily
      quotient.positiveCallerFine).tube_eq

/-- Original shaded mass of one positive quotient caller class. -/
def pureWZ2PostDeletionPositiveCallerWeight
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (parent :
      Fin (pureWZ2PostDeletionPositiveCallerBase quotient).family.card) :
    ENNReal :=
  quotient.callerActualWeight
    ((pureWZ2PostDeletionPositiveCallerBase quotient).embedding parent)

/--
The existing simultaneous finite caller-center selection, applied before
per-caller complete-parent regularization and weighted by the original caller
class masses.
-/
structure PureWZ2PostDeletionCallerWeightPreselectionData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (coordinateCount : ℕ)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant) where
  Color : Fin coordinateCount → Type
  colorFintype : ∀ coordinate, Fintype (Color coordinate)
  colorDecidableEq : ∀ coordinate, DecidableEq (Color coordinate)
  colorNonempty : ∀ coordinate, Nonempty (Color coordinate)
  coloring :
    ∀ coordinate,
      PureWZ2CallerCenterEnvelopeColoringData
        quotient (scheduled coordinate)
        (pureWZ2PostDeletionPositiveCallerBase quotient)
        (Color coordinate)
  selection :
    PureWZ2FiniteCallerCenterSelectionData
      quotient (pureWZ2PostDeletionPositiveCallerBase quotient)
      coordinateCount scales scheduled Color coloring
      (pureWZ2PostDeletionPositiveCallerWeight quotient)
  selected :
    WZ2PaperPureTubeSubfamily
      (pureWZ2PostDeletionPositiveCallerBase quotient).family
  selected_eq : selected = selection.selected
  selected_nonempty : selected.family.Nonempty
  retentionConstant : ENNReal
  retentionConstant_eq :
    retentionConstant = selection.retentionConstant
  retained_weight :
    (∑ parent :
        Fin (pureWZ2PostDeletionPositiveCallerBase quotient).family.card,
      pureWZ2PostDeletionPositiveCallerWeight quotient parent) ≤
        retentionConstant *
          ∑ parent : Fin selected.family.card,
            pureWZ2PostDeletionPositiveCallerWeight quotient
              (selected.embedding parent)
  weightLevel : ENNReal
  weightLevel_pos : 0 < weightLevel
  weight_band :
    ∀ parent : Fin selected.family.card,
      weightLevel ≤
          pureWZ2PostDeletionPositiveCallerWeight quotient
            (selected.embedding parent) ∧
        pureWZ2PostDeletionPositiveCallerWeight quotient
            (selected.embedding parent) ≤
          2 * weightLevel
  total_weight_eq :
    (∑ parent :
        Fin (pureWZ2PostDeletionPositiveCallerBase quotient).family.card,
      pureWZ2PostDeletionPositiveCallerWeight quotient parent) =
        quotient.selectedShading.mass

/-- Perform caller weight-band selection before any local regularizer. -/
theorem pureWZ2_postDeletion_caller_weight_preselection
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (fineNonempty : fine.Nonempty)
    (fineBoundedBase : HasBoundedBase fine 4)
    (selectedMassPos : 0 < quotient.selectedShading.mass)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant) :
    Nonempty
      (PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled) := by
  let callerBase := pureWZ2PostDeletionPositiveCallerBase quotient
  let weight := pureWZ2PostDeletionPositiveCallerWeight quotient
  let Color : Fin coordinateCount → Type :=
    fun _ =>
      Fin (pureWZ2CallerCenterUniformConflictDegree + 1)
  let coloring :
      ∀ coordinate,
        PureWZ2CallerCenterEnvelopeColoringData
          quotient (scheduled coordinate) callerBase
          (Color coordinate) :=
    fun coordinate =>
      Classical.choice
        (pureWZ2_caller_center_envelope_uniform_coloring
          quotient (scheduled coordinate) callerBase fineNonempty
            fineBoundedBase)
  let selection :
      PureWZ2FiniteCallerCenterSelectionData
        quotient callerBase coordinateCount scales scheduled
        Color coloring weight :=
    Classical.choice <|
      pureWZ2_finite_caller_center_selection
        quotient callerBase coordinateCount coordinateCountPos
        scales scheduled Color coloring weight
  have totalWeightEq :
      (∑ parent : Fin callerBase.family.card, weight parent) =
        quotient.selectedShading.mass := by
    change
      (∑ parent :
          Fin (quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).family.card,
        quotient.callerActualWeight
          ((quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).embedding parent)) =
        quotient.selectedShading.mass
    exact quotient.sum_positive_hitParent_weight
  have selectedNonempty : selection.selected.family.Nonempty := by
    by_contra hempty
    have selectedSumZero :
        (∑ parent : Fin selection.selected.family.card,
          weight (selection.selected.embedding parent)) = 0 := by
      apply Finset.sum_eq_zero
      intro parent _
      exact Fin.elim0 (Nat.eq_zero_of_not_pos hempty ▸ parent)
    have retained := selection.retained_weight
    rw [selectedSumZero, mul_zero, totalWeightEq] at retained
    exact (not_le_of_gt selectedMassPos) retained
  letI colorFintype : ∀ coordinate, Fintype (Color coordinate) :=
    fun coordinate => inferInstance
  letI colorDecidableEq :
      ∀ coordinate, DecidableEq (Color coordinate) :=
    fun coordinate => inferInstance
  letI colorNonempty : ∀ coordinate, Nonempty (Color coordinate) :=
    fun coordinate => inferInstance
  exact
    ⟨{
      Color := Color
      colorFintype := colorFintype
      colorDecidableEq := colorDecidableEq
      colorNonempty := colorNonempty
      coloring := coloring
      selection := selection
      selected := selection.selected
      selected_eq := rfl
      selected_nonempty := selectedNonempty
      retentionConstant := selection.retentionConstant
      retentionConstant_eq := rfl
      retained_weight := selection.retained_weight
      weightLevel := selection.weightLevel
      weightLevel_pos := selection.weightLevel_pos
      weight_band := selection.weight_band
      total_weight_eq := by
        simpa [callerBase, weight] using totalWeightEq
    }⟩

namespace PureWZ2PostDeletionCallerWeightPreselectionData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {coordinateCount : ℕ}
    {scales : Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}

/-- The selected caller band, reindexed directly into the quotient caller
family.  Its family is definitionally the preselection output, while its
embedding records both provenance steps. -/
noncomputable def selectedCallerBase
    (data :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled) :
    WZ2PaperPureTubeSubfamily quotient.callerCoarse where
  family := data.selected.family
  embedding :=
    data.selected.embedding.trans
      (pureWZ2PostDeletionPositiveCallerBase quotient).embedding
  tube_eq := by
    intro parent
    rw [data.selected.tube_eq,
      (pureWZ2PostDeletionPositiveCallerBase quotient).tube_eq]
    rfl

/--
Exact family-dependent normalization floor delivered by preselection.
Unlike mere positivity, this estimate survives division by the ambient fine
cardinality and is uniform over every selected caller class.
-/
theorem selected_normalization_weight_lower
    (data :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (parent : Fin data.selected.family.card) :
    quotient.selectedShading.mass * fine.enncard⁻¹ ≤
      data.retentionConstant *
        ((pureWZ2PostDeletionPositiveCallerBase
          quotient).family.enncard * 2) *
        (pureWZ2PostDeletionPositiveCallerWeight quotient
            (data.selected.embedding parent) *
          fine.enncard⁻¹) := by
  let callerBase := pureWZ2PostDeletionPositiveCallerBase quotient
  let weight := pureWZ2PostDeletionPositiveCallerWeight quotient
  have selectedSumUpper :
      (∑ index : Fin data.selected.family.card,
          weight (data.selected.embedding index)) ≤
        data.selected.family.enncard *
          (2 * data.weightLevel) := by
    calc
      (∑ index : Fin data.selected.family.card,
          weight (data.selected.embedding index)) ≤
          ∑ _index : Fin data.selected.family.card,
            2 * data.weightLevel := by
        exact Finset.sum_le_sum fun index _ =>
          (data.weight_band index).2
      _ =
          data.selected.family.enncard *
            (2 * data.weightLevel) := by
        simp [Kakeya.Streamlined.TubeFamily.enncard,
          Finset.sum_const]
  have selectedCardLe :
      data.selected.family.card ≤ callerBase.family.card :=
    by
      simpa [callerBase] using
        Fintype.card_le_of_injective
          data.selected.embedding
          data.selected.embedding.injective
  have selectedENNCardLe :
      data.selected.family.enncard ≤ callerBase.family.enncard := by
    change
      (data.selected.family.card : ENNReal) ≤
        (callerBase.family.card : ENNReal)
    exact_mod_cast selectedCardLe
  have totalToParent :
      quotient.selectedShading.mass ≤
        data.retentionConstant *
          (callerBase.family.enncard * 2) *
          weight (data.selected.embedding parent) := by
    calc
      quotient.selectedShading.mass =
          ∑ index : Fin callerBase.family.card, weight index := by
        simpa [callerBase, weight] using data.total_weight_eq.symm
      _ ≤
          data.retentionConstant *
            ∑ index : Fin data.selected.family.card,
              weight (data.selected.embedding index) :=
        data.retained_weight
      _ ≤
          data.retentionConstant *
            (data.selected.family.enncard *
              (2 * data.weightLevel)) := by
        gcongr
      _ ≤
          data.retentionConstant *
            (callerBase.family.enncard *
              (2 * weight
                (data.selected.embedding parent))) := by
        gcongr
        exact (data.weight_band parent).1
      _ =
          data.retentionConstant *
            (callerBase.family.enncard * 2) *
            weight (data.selected.embedding parent) := by
        ring
  calc
    quotient.selectedShading.mass * fine.enncard⁻¹ ≤
        (data.retentionConstant *
          (callerBase.family.enncard * 2) *
          weight (data.selected.embedding parent)) *
            fine.enncard⁻¹ := by
      gcongr
    _ =
        data.retentionConstant *
          (callerBase.family.enncard * 2) *
          (weight (data.selected.embedding parent) *
            fine.enncard⁻¹) := by
      ring

/-- Forward lower bound for the selected caller weight level. The number of
hit caller parents is at most the number of ambient fine tubes, so the
runtime cardinality cancels against the ambient density normalization. -/
theorem weightLevel_density_lower
    (data :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (fineNonempty : fine.Nonempty)
    (density : ENNReal)
    (ambientDensity :
      density * fine.enncard ≤ shading.mass) :
    density ≤
      ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
        data.retentionConstant * 2) * data.weightLevel := by
  let callerBase := pureWZ2PostDeletionPositiveCallerBase quotient
  let weight := pureWZ2PostDeletionPositiveCallerWeight quotient
  have callerCardLePositive :
      callerBase.family.card ≤ quotient.positiveCallerFine.family.card := by
    change
      (quotient.callerCover.hitParentSubfamily
        quotient.positiveCallerFine).family.card ≤
          quotient.positiveCallerFine.family.card
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_surjective
        (quotient.callerCover.hitParent quotient.positiveCallerFine)
        (quotient.callerCover.hitParent_surjective
          quotient.positiveCallerFine)
  have positiveCardLeFine :
      quotient.positiveCallerFine.family.card ≤ fine.card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective
        (quotient.positiveCallerFine.embedding.trans
          quotient.selected.embedding)
        (quotient.positiveCallerFine.embedding.trans
          quotient.selected.embedding).injective
  have callerENNCardLe :
      callerBase.family.enncard ≤ fine.enncard := by
    change (callerBase.family.card : ENNReal) ≤ (fine.card : ENNReal)
    exact_mod_cast callerCardLePositive.trans positiveCardLeFine
  have selectedSumUpper :
      (∑ index : Fin data.selected.family.card,
          weight (data.selected.embedding index)) ≤
        callerBase.family.enncard * (2 * data.weightLevel) := by
    calc
      (∑ index : Fin data.selected.family.card,
          weight (data.selected.embedding index)) ≤
          ∑ _index : Fin data.selected.family.card,
            2 * data.weightLevel := by
        exact Finset.sum_le_sum fun index _ =>
          (data.weight_band index).2
      _ =
          data.selected.family.enncard * (2 * data.weightLevel) := by
        simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const]
      _ ≤ callerBase.family.enncard * (2 * data.weightLevel) := by
        gcongr
        change
          (data.selected.family.card : ENNReal) ≤
            (callerBase.family.card : ENNReal)
        have selectedCardLe :
            data.selected.family.card ≤ callerBase.family.card := by
          simpa only [Fintype.card_fin] using
            Fintype.card_le_of_injective
              data.selected.embedding data.selected.embedding.injective
        exact_mod_cast selectedCardLe
  have sourceToLevel :
      density * fine.enncard ≤
        (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          data.retentionConstant * 2) * data.weightLevel) *
          fine.enncard := by
    calc
      density * fine.enncard ≤ shading.mass := ambientDensity
      _ ≤
          (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            quotient.selectedShading.mass :=
        quotient.retained_mass
      _ =
          (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            (∑ index : Fin callerBase.family.card, weight index) := by
        rw [← data.total_weight_eq]
      _ ≤
          (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            (data.retentionConstant *
              ∑ index : Fin data.selected.family.card,
                weight (data.selected.embedding index)) := by
        gcongr
        exact data.retained_weight
      _ ≤
          (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            (data.retentionConstant *
              (callerBase.family.enncard * (2 * data.weightLevel))) := by
        gcongr
      _ ≤
          (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            (data.retentionConstant *
              (fine.enncard * (2 * data.weightLevel))) := by
        gcongr
      _ =
          (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            data.retentionConstant * 2) * data.weightLevel) *
            fine.enncard := by ring
  have fineCardZero : fine.enncard ≠ 0 := by
    change (fine.card : ENNReal) ≠ 0
    exact_mod_cast (Nat.ne_of_gt fineNonempty)
  have fineCardTop : fine.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  exact
    (ENNReal.mul_le_mul_iff_right fineCardZero fineCardTop).mp
      (by simpa [mul_comm] using sourceToLevel)

/-- The preselected weight level is finite because every selected original
caller weight is finite. -/
theorem weightLevel_ne_top
    (data :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled) :
    data.weightLevel ≠ ⊤ := by
  let parent : Fin data.selected.family.card :=
    ⟨0, data.selected_nonempty⟩
  have lower := (data.weight_band parent).1
  have weightTop :
      pureWZ2PostDeletionPositiveCallerWeight quotient
          (data.selected.embedding parent) ≠ ⊤ := by
    exact quotient.callerActualWeight_ne_top _
  intro levelTop
  rw [levelTop] at lower
  exact weightTop (top_unique lower)

/--
Runtime local CWA constant after caller preselection.  This depends on the
already selected common weight level, but introduces no runtime cutoff.
Uniform power absorption is deliberately postponed to the family-free lower
bound for that level.
-/
def localFiberConstant
    (data :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (R weightUpper : ENNReal) : ENNReal :=
  max (R * ambientConstant)
    (wz2PaperPureNearbyRestrictionConstant
      ambientConstant
      (data.weightLevel * fine.enncard⁻¹)
      (max ambientConstant
        (ambientConstant *
          pureWZ2CompleteParentDegreeConstant
            actualNearby.scaleData.coarse.card coordinateCount))
      (pureWZ2CompleteParentRegularizationLoss
          actualNearby.scaleData.coarse.card coordinateCount *
        weightUpper))

theorem localFiberConstant_ne_top
    (data :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    {R weightUpper : ENNReal}
    (R_ne_top : R ≠ ⊤)
    (ambient_ne_top : ambientConstant ≠ ⊤)
    (weightUpper_ne_top : weightUpper ≠ ⊤) :
    data.localFiberConstant R weightUpper ≠ ⊤ := by
  apply max_ne_top
  · exact ENNReal.mul_ne_top R_ne_top ambient_ne_top
  · unfold wz2PaperPureNearbyRestrictionConstant
    apply max_ne_top ambient_ne_top
    apply max_ne_top
    · exact max_ne_top ambient_ne_top <|
        ENNReal.mul_ne_top ambient_ne_top ENNReal.coe_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.inv_ne_top.mpr <|
            mul_ne_zero data.weightLevel_pos.ne'
              (ENNReal.inv_ne_zero.mpr (by
                simp [Kakeya.Streamlined.TubeFamily.enncard]))
        · apply ENNReal.mul_ne_top
          · exact ENNReal.mul_ne_top ambient_ne_top <|
              ENNReal.mul_ne_top ENNReal.coe_ne_top weightUpper_ne_top
          · exact max_ne_top ambient_ne_top <|
              ENNReal.mul_ne_top ambient_ne_top ENNReal.coe_ne_top
      · exact ambient_ne_top

theorem localFiber_window_absorption
    (data :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (R weightUpper : ENNReal) :
    R * ambientConstant ≤ data.localFiberConstant R weightUpper :=
  le_max_left _ _

theorem localFiber_restriction_absorption
    (data :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (R weightUpper : ENNReal)
    (parent : Fin data.selected.family.card) :
    wz2PaperPureNearbyRestrictionConstant
        ambientConstant
        (pureWZ2PostDeletionPositiveCallerWeight quotient
            (data.selected.embedding parent) *
          fine.enncard⁻¹)
        (max ambientConstant
          (ambientConstant *
            pureWZ2CompleteParentDegreeConstant
              actualNearby.scaleData.coarse.card coordinateCount))
        (pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card coordinateCount *
          weightUpper) ≤
      data.localFiberConstant R weightUpper := by
  apply le_max_of_le_right
  unfold wz2PaperPureNearbyRestrictionConstant
  apply max_le_max_left
  apply max_le_max_left
  gcongr
  exact (data.weight_band parent).1

/-- Named actual-formula absorption for the corrected post-deletion order. -/
theorem
    pureWZ2_postDeletion_actual_formula_restriction_absorption_after_preselection
    (data :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (R weightUpper : ENNReal)
    (parent : Fin data.selected.family.card) :
    wz2PaperPureNearbyRestrictionConstant
        ambientConstant
        (pureWZ2PostDeletionPositiveCallerWeight quotient
            (data.selected.embedding parent) *
          fine.enncard⁻¹)
        (max ambientConstant
          (ambientConstant *
            pureWZ2CompleteParentDegreeConstant
              actualNearby.scaleData.coarse.card coordinateCount))
        (pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card coordinateCount *
          weightUpper) ≤
      data.localFiberConstant R weightUpper :=
  data.localFiber_restriction_absorption R weightUpper parent

end PureWZ2PostDeletionCallerWeightPreselectionData

end Kakeya.Assouad

end
