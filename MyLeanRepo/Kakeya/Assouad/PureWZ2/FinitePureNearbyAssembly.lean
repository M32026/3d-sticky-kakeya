import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal

/-!
# Pure nearby CWA from a finite rounded schedule

This is the abstract assembly layer after all simultaneous selection has
already been performed.  Every requested scale is rounded upward to one
scheduled coordinate; the scheduled pure scale witness is then weakened to
the common output constant.
-/

noncomputable section

namespace Kakeya.Assouad

theorem pureWZ2_nearby_from_finite_witnesses
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {outputConstant : ENNReal}
    (hdelta : 0 < delta)
    (outputOne : 1 ≤ outputConstant)
    (outputTop : outputConstant ≠ ⊤)
    (familyDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct family)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (scaleWitness :
      ∀ coordinate : Fin coordinateCount,
        Σ actualScale : ℝ,
          WZ2PaperPureScaleCoverData
            family actualScale outputConstant)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤
            (scaleWitness coordinate).1 ∧
          ENNReal.ofReal
              (scaleWitness coordinate).1 <
            outputConstant * ENNReal.ofReal requested.1) :
    WZ2PaperPureCWAAtNearbyScales family outputConstant := by
  refine
    ⟨hdelta, ⟨outputOne, outputTop⟩,
      familyDistinct, ?_⟩
  intro requested
  rcases rounding requested with
    ⟨coordinate, hrequested, hwindow⟩
  exact
    ⟨{
      rho := (scaleWitness coordinate).1
      requested_le := hrequested
      within_factor := hwindow
      scaleData := (scaleWitness coordinate).2
    }⟩

/--
Compatibility wrapper retaining the requested-scale list used by older
callers.  The actual witnesses and the rounding relation carry all data used
by the conclusion.
-/
theorem pureWZ2_nearby_from_finite_rounding
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {outputConstant : ENNReal}
    (hdelta : 0 < delta)
    (outputOne : 1 ≤ outputConstant)
    (outputTop : outputConstant ≠ ⊤)
    (familyDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct family)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (_scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scaleWitness :
      ∀ coordinate : Fin coordinateCount,
        Σ actualScale : ℝ,
          WZ2PaperPureScaleCoverData
            family actualScale outputConstant)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤
            (scaleWitness coordinate).1 ∧
          ENNReal.ofReal
              (scaleWitness coordinate).1 <
            outputConstant * ENNReal.ofReal requested.1) :
    WZ2PaperPureCWAAtNearbyScales family outputConstant :=
  pureWZ2_nearby_from_finite_witnesses
    hdelta outputOne outputTop familyDistinct
    coordinateCount coordinateCountPos scaleWitness rounding

end Kakeya.Assouad

end
