import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteNearbyScheduleStatements

/-!
# Recover nearby-scale CWA from a finite regularized schedule

For each requested scale, use the representative witness selected by the
finite schedule. Restrict its carrier-faithful literal cover to the selected
family and its hit parents.  The weighted calculation uses the auxiliary
assigned view only through the proved equality with strict full fibers; the
result is repackaged as a literal partitioning witness before returning it.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PaperFiniteNearbyScheduleData.regularize
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {levelCount : ℕ}
    (schedule :
      WZ2PaperFiniteNearbyScheduleData
        (family := family)
        ambientConstant outputConstant levelCount)
    (houtputOne : 1 ≤ outputConstant)
    (hline : WZ1PaperIsLineClass family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (weight retentionConstant degreeConstant : ENNReal)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hglobalRetention :
      weight * family.enncard ≤
        retentionConstant * selected.family.enncard)
    (hdegree :
      ∀ coordinate,
        ∀ first second :
            Fin (schedule.witness coordinate).scaleData.coarse.card,
          0 <
              ((Finset.univ :
                  Finset (Fin selected.family.card)).filter
                fun source =>
                  (schedule.witness coordinate).scaleData.cover.parent
                      (selected.embedding source) =
                    first).card →
            0 <
              ((Finset.univ :
                  Finset (Fin selected.family.card)).filter
                fun source =>
                  (schedule.witness coordinate).scaleData.cover.parent
                      (selected.embedding source) =
                    second).card →
            ((((Finset.univ :
                Finset (Fin selected.family.card)).filter
              fun source =>
                (schedule.witness coordinate).scaleData.cover.parent
                    (selected.embedding source) =
                  first).card : ℕ) : ENNReal) ≤
              degreeConstant *
                ((((Finset.univ :
                    Finset (Fin selected.family.card)).filter
                  fun source =>
                    (schedule.witness coordinate).scaleData.cover.parent
                        (selected.embedding source) =
                      second).card : ℕ) : ENNReal))
    (habsorb :
      max degreeConstant
          ((weight⁻¹ *
              (ambientConstant * retentionConstant * degreeConstant)) *
            ambientConstant) ≤
        outputConstant) :
    WZ2PaperCWACoversAtNearbyScales
      selected.family outputConstant := by
  refine ⟨houtputOne, hline.subfamily selected, ?_⟩
  intro requestedScale
  let coordinate := schedule.representative requestedScale
  let ambient := schedule.witness coordinate
  have hselectedUniform :
      ∀ first second :
          Fin (ambient.scaleData.cover.hitParentSubfamily
            selected).family.card,
        (ambient.scaleData.cover.restrictToHitParents
          selected).fiberCount first ≤
          degreeConstant *
            (ambient.scaleData.cover.restrictToHitParents
              selected).fiberCount second := by
    apply
      ambient.scaleData.cover
        |>.restrictToHitParents_fiber_uniform_of_subfamily
          selected degreeConstant
    intro first second hfirst hsecond
    exact hdegree coordinate first second hfirst hsecond
  let restricted :=
    WZ2PaperLiteralScaleCoverData.restrictToSelectedHitParents
      (data := ambient.scaleData)
      (selected := selected)
      (weight := weight)
      (selectedConstant := degreeConstant)
      (retentionConstant := retentionConstant)
      hweightZero hweightTop hglobalRetention hselectedUniform
  refine
    ⟨{
      rho := ambient.rho
      rho_pos := ambient.rho_pos
      requested_le := schedule.requested_le requestedScale
      within_factor := schedule.within_output requestedScale
      scaleData := restricted.mono habsorb }⟩

end Kakeya.Assouad

end
