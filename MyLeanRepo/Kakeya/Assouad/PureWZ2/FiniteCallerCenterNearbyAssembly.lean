import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterUniformConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FiniteCallerCenterSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterEnvelopeBodyCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FinitePureNearbyAssembly
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureHitParentRestriction

/-!
# Finite caller-center nearby-scale assembly

At every scheduled ambient Definition 2.12 witness, use the uniform
caller-center envelope coloring.  One simultaneous color-vector and owner-degree
selection produces a single caller subfamily.  The exact monochromatic cover
at each coordinate then supplies literal scale data for that same family.

All asymptotic bookkeeping remains explicit: callers provide the common
output-constant inequalities and the actual-scale rounding window.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2FiniteCallerCenterNearbyAssemblyData
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
    (callerBase :
      WZ2PaperPureTubeSubfamily quotient.callerCoarse)
    (coordinateCount : ℕ)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (weight : Fin callerBase.family.card → ENNReal)
    (outputConstant : ENNReal) where
  Color : Fin coordinateCount → Type
  colorFintype : ∀ coordinate, Fintype (Color coordinate)
  colorDecidableEq : ∀ coordinate, DecidableEq (Color coordinate)
  colorNonempty : ∀ coordinate, Nonempty (Color coordinate)
  coloring :
    ∀ coordinate,
      PureWZ2CallerCenterEnvelopeColoringData
        quotient (scheduled coordinate) callerBase
        (Color coordinate)
  selection :
    PureWZ2FiniteCallerCenterSelectionData
      quotient callerBase coordinateCount scales scheduled
      Color coloring weight
  selected_nonempty : selection.selected.family.Nonempty
  scaleCover :
    ∀ coordinate,
      WZ2PaperPureScaleCoverData
        selection.selected.family
        (19 * (scheduled coordinate).rho)
        outputConstant
  literal_cwa :
    WZ2PaperPureCWAAtNearbyScales
      selection.selected.family outputConstant

/--
Assemble one finite simultaneous caller-center selection and all literal
nearby-scale witnesses on the selected caller family.
-/
theorem pureWZ2_finite_caller_center_nearby_assembly
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
    (callerBase :
      WZ2PaperPureTubeSubfamily quotient.callerCoarse)
    (fineNonempty : fine.Nonempty)
    (fineBoundedBase : HasBoundedBase fine 4)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (callerScheduled :
      ∀ coordinate,
        callerRequested.1 ≤ (scheduled coordinate).rho)
    (weight : Fin callerBase.family.card → ENNReal)
    (totalWeightPos :
      0 < ∑ index : Fin callerBase.family.card, weight index)
    (outputConstant : ENNReal)
    (outputOne : 1 ≤ outputConstant)
    (outputTop : outputConstant ≠ ⊤)
    (scaleAbsorption :
      ∀ coordinate,
        max
            (pureWZ2FiniteCallerCenterDegreeConstant
              coordinateCount callerBase.family.card)
            ((27 : ENNReal) *
              Kakeya.deltaTubeVolume
                (19 * (scheduled coordinate).rho) *
              (Kakeya.deltaTubeVolume callerRequested.1)⁻¹) ≤
          outputConstant)
    (rounding :
      ∀ requested :
          WZ2PaperRequestedScale callerRequested.1,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ 19 * (scheduled coordinate).rho ∧
          ENNReal.ofReal (19 * (scheduled coordinate).rho) <
            outputConstant * ENNReal.ofReal requested.1) :
    Nonempty
      (PureWZ2FiniteCallerCenterNearbyAssemblyData
        quotient callerBase coordinateCount scales scheduled
        weight outputConstant) := by
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
    Classical.choice
      (pureWZ2_finite_caller_center_selection
        quotient callerBase coordinateCount coordinateCountPos
        scales scheduled Color coloring weight)
  have selectedNonempty :
      selection.selected.family.Nonempty := by
    by_contra hempty
    have hcard :
        selection.selected.family.card = 0 := by
      exact Nat.eq_zero_of_not_pos hempty
    have hselectedSum :
        (∑ index : Fin selection.selected.family.card,
          weight (selection.selected.embedding index)) = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      exfalso
      have hindex := index.isLt
      omega
    have hretained := selection.retained_weight
    rw [hselectedSum, mul_zero] at hretained
    exact (not_le_of_gt totalWeightPos) hretained
  let monochromatic :
      ∀ coordinate,
        PureWZ2CallerCenterMonochromaticEnvelopeCoverData
          (coloring coordinate) selection.selected :=
    fun coordinate =>
      Classical.choice
        ((coloring coordinate).monochromatic_cover
          selection.selected
          (selection.colorVector coordinate)
          (selection.monochromatic coordinate)
          (callerScheduled coordinate))
  have selectedUniform :
      ∀ coordinate,
        WZ2PaperPureFullFibersAreCUniform
          selection.selected.family
          (monochromatic coordinate).selectedCoarse.family
          selection.degreeConstant := by
    intro coordinate first second
    have hfirst :
        0 <
          ((Finset.univ :
            Finset (Fin selection.selected.family.card)).filter
              fun index =>
                pureWZ2CallerCenterScheduledOwner
                    quotient (scheduled coordinate)
                    (callerBase.embedding
                      (selection.selected.embedding index)) =
                  (monochromatic coordinate).selectedCoarse.embedding
                    first).card := by
      rw [←
        (monochromatic coordinate).fullFiberIndices_eq_owner first]
      exact
        Finset.card_pos.mpr
          ((monochromatic coordinate).full_fiber_nonempty first)
    have hsecond :
        0 <
          ((Finset.univ :
            Finset (Fin selection.selected.family.card)).filter
              fun index =>
                pureWZ2CallerCenterScheduledOwner
                    quotient (scheduled coordinate)
                    (callerBase.embedding
                      (selection.selected.embedding index)) =
                  (monochromatic coordinate).selectedCoarse.embedding
                    second).card := by
      rw [←
        (monochromatic coordinate).fullFiberIndices_eq_owner second]
      exact
        Finset.card_pos.mpr
          ((monochromatic coordinate).full_fiber_nonempty second)
    have huniform :=
      selection.degree_uniform coordinate
        ((monochromatic coordinate).selectedCoarse.embedding first)
        ((monochromatic coordinate).selectedCoarse.embedding second)
        hfirst hsecond
    change
      ((wz2PaperOrdinaryFullFiberIndices
          selection.selected.family
          (monochromatic coordinate).selectedCoarse.family
          first).card : ENNReal) ≤
        selection.degreeConstant *
          ((wz2PaperOrdinaryFullFiberIndices
            selection.selected.family
            (monochromatic coordinate).selectedCoarse.family
            second).card : ENNReal)
    rw [
      (monochromatic coordinate).fullFiberIndices_eq_owner first,
      (monochromatic coordinate).fullFiberIndices_eq_owner second]
    exact huniform
  let rawScale :
      ∀ coordinate,
        WZ2PaperPureScaleCoverData
          selection.selected.family
          (19 * (scheduled coordinate).rho)
          (max selection.degreeConstant
            ((27 : ENNReal) *
              Kakeya.deltaTubeVolume
                (19 * (scheduled coordinate).rho) *
              (Kakeya.deltaTubeVolume callerRequested.1)⁻¹)) :=
    fun coordinate =>
      callerCenterMonochromaticEnvelopeScaleDataOfVolume
        (monochromatic coordinate)
        selection.degreeConstant
        (selectedUniform coordinate)
  have rawConstantLe :
      ∀ coordinate,
        max selection.degreeConstant
            ((27 : ENNReal) *
              Kakeya.deltaTubeVolume
                (19 * (scheduled coordinate).rho) *
              (Kakeya.deltaTubeVolume callerRequested.1)⁻¹) ≤
          outputConstant := by
    intro coordinate
    rw [selection.degreeConstant_eq]
    exact scaleAbsorption coordinate
  let scaleCover :
      ∀ coordinate,
        WZ2PaperPureScaleCoverData
          selection.selected.family
          (19 * (scheduled coordinate).rho)
          outputConstant :=
    fun coordinate =>
      (rawScale coordinate).mono (rawConstantLe coordinate)
  have familyDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct
        selection.selected.family :=
    (quotient.caller_ordinary_distinct.subfamily callerBase).subfamily
      selection.selected
  let scaleWitness :
      ∀ coordinate : Fin coordinateCount,
        Σ actualScale : ℝ,
          WZ2PaperPureScaleCoverData
            selection.selected.family actualScale outputConstant :=
    fun coordinate =>
      ⟨19 * (scheduled coordinate).rho, scaleCover coordinate⟩
  let outputScales :
      Fin coordinateCount →
        WZ2PaperRequestedScale callerRequested.1 :=
    fun _ =>
      ⟨callerRequested.1, le_rfl, callerRequested.2.2⟩
  have literalCWA :
      WZ2PaperPureCWAAtNearbyScales
        selection.selected.family outputConstant :=
    pureWZ2_nearby_from_finite_rounding
      (actualNearby.scaleData.delta_pos.trans_le
        callerRequested.2.1)
      outputOne outputTop familyDistinct
      coordinateCount coordinateCountPos outputScales
      scaleWitness rounding
  exact
    ⟨{
      Color := Color
      colorFintype := fun _ => inferInstance
      colorDecidableEq := fun _ => inferInstance
      colorNonempty := fun _ => inferInstance
      coloring := coloring
      selection := selection
      selected_nonempty := selectedNonempty
      scaleCover := scaleCover
      literal_cwa := literalCWA
    }⟩

end Kakeya.Assouad

end
