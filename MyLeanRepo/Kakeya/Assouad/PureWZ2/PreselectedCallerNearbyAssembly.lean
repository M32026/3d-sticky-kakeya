import MyLeanRepo.Kakeya.Assouad.PureWZ2.PostDeletionCallerWeightPreselection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterEnvelopeBodyCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FinitePureNearbyAssembly

/-!
# Nearby CWA on the preselected caller band

Reuse the exact coloring and finite selection already paid for by caller
weight preselection; no second caller selection is performed.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2PreselectedCallerNearbyAssemblyData
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
          fine (scales coordinate) ambientConstant)
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (outputConstant : ENNReal) where
  scaleCover :
    ∀ coordinate,
      WZ2PaperPureScaleCoverData
        preselection.selected.family
        (19 * (scheduled coordinate).rho)
        outputConstant
  literal_cwa :
    WZ2PaperPureCWAAtNearbyScales
      preselection.selected.family outputConstant

theorem pureWZ2_preselected_caller_nearby_assembly
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
    (coordinateCountPos : 0 < coordinateCount)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (callerScheduled :
      ∀ coordinate,
        callerRequested.1 ≤ (scheduled coordinate).rho)
    (outputConstant : ENNReal)
    (outputOne : 1 ≤ outputConstant)
    (outputTop : outputConstant ≠ ⊤)
    (scaleAbsorption :
      ∀ coordinate,
        max
            (pureWZ2FiniteCallerCenterDegreeConstant
              coordinateCount
              (pureWZ2PostDeletionPositiveCallerBase
                quotient).family.card)
            ((27 : ENNReal) *
              Kakeya.deltaTubeVolume
                (19 * (scheduled coordinate).rho) *
              (Kakeya.deltaTubeVolume callerRequested.1)⁻¹) ≤
          outputConstant)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale callerRequested.1,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ 19 * (scheduled coordinate).rho ∧
          ENNReal.ofReal (19 * (scheduled coordinate).rho) <
            outputConstant * ENNReal.ofReal requested.1) :
    Nonempty
      (PureWZ2PreselectedCallerNearbyAssemblyData
        quotient coordinateCount scales scheduled preselection
        outputConstant) := by
  let callerBase := pureWZ2PostDeletionPositiveCallerBase quotient
  let selection := preselection.selection
  letI colorFintype :
      ∀ coordinate, Fintype (preselection.Color coordinate) :=
    preselection.colorFintype
  letI colorDecidableEq :
      ∀ coordinate, DecidableEq (preselection.Color coordinate) :=
    preselection.colorDecidableEq
  letI colorNonempty :
      ∀ coordinate, Nonempty (preselection.Color coordinate) :=
    preselection.colorNonempty
  let monochromatic :
      ∀ coordinate,
        PureWZ2CallerCenterMonochromaticEnvelopeCoverData
          (preselection.coloring coordinate) selection.selected :=
    fun coordinate =>
      Classical.choice
        ((preselection.coloring coordinate).monochromatic_cover
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
  let scaleCover :
      ∀ coordinate,
        WZ2PaperPureScaleCoverData
          selection.selected.family
          (19 * (scheduled coordinate).rho)
          outputConstant :=
    fun coordinate =>
      (rawScale coordinate).mono <| by
        rw [selection.degreeConstant_eq]
        exact scaleAbsorption coordinate
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
    fun _ => ⟨callerRequested.1, le_rfl, callerRequested.2.2⟩
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
      scaleCover := by
        rw [preselection.selected_eq]
        simpa only [selection] using scaleCover
      literal_cwa := by
        rw [preselection.selected_eq]
        simpa only [selection] using literalCWA
    }⟩

end Kakeya.Assouad

end
