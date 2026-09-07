import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PureFiniteNearbySchedule
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureNearbyRestriction

/-!
# Restrict a public pure finite nearby schedule

All selected parent maps below come from the same public strict-fiber covers
stored in the schedule.  The one-scale restriction therefore retains the
canonical actual-John body CWA rather than substituting an assigned subfiber.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Recover public pure nearby-scale CWA from simultaneous degree regularity
on the finite representative schedule. -/
theorem PureWZ2FiniteNearbyScheduleData.restrictOfWeightedRetention
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {levelCount : ℕ}
    (ambientCWA :
      WZ2PaperPureCWAAtNearbyScales family ambientConstant)
    (schedule : PureWZ2FiniteNearbyScheduleData
      (family := family) ambientConstant outputConstant levelCount)
    (hscheduleFinite : WZ2PaperFiniteErrorConstant outputConstant)
    (selected : WZ2PaperPureTubeSubfamily family)
    (selectedNonempty : selected.family.Nonempty)
    (weight selectedConstant retentionConstant : ENNReal)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hretentionTop : retentionConstant ≠ ⊤)
    (hselectedTop : selectedConstant ≠ ⊤)
    (hglobalRetention :
      weight * family.enncard ≤
        retentionConstant * selected.family.enncard)
    (degreeUniform :
      ∀ coordinate,
        ∀ first second :
            Fin (schedule.witness coordinate).scaleData.coarse.card,
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  (schedule.witness coordinate).scaleData.cover.parent
                      (selected.embedding source) = first).card →
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  (schedule.witness coordinate).scaleData.cover.parent
                      (selected.embedding source) = second).card →
          (((Finset.univ :
            Finset (Fin selected.family.card)).filter fun source =>
              (schedule.witness coordinate).scaleData.cover.parent
                  (selected.embedding source) = first).card : ENNReal) ≤
            selectedConstant *
              (((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  (schedule.witness coordinate).scaleData.cover.parent
                      (selected.embedding source) = second).card : ENNReal)) :
    WZ2PaperPureCWAAtNearbyScales selected.family
      (max outputConstant
        (wz2PaperPureNearbyRestrictionConstant
          ambientConstant weight selectedConstant retentionConstant)) := by
  let restrictionConstant := wz2PaperPureNearbyRestrictionConstant
    ambientConstant weight selectedConstant retentionConstant
  have hambientFinite : ambientConstant ≠ ⊤ := ambientCWA.2.1.2
  have hinverseTop : weight⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hweightZero
  have hratioTop :
      (weight⁻¹ *
          (ambientConstant * retentionConstant * selectedConstant)) *
        ambientConstant ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hinverseTop
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top hambientFinite hretentionTop) hselectedTop))
      hambientFinite
  have hrestrictionFinite : WZ2PaperFiniteErrorConstant restrictionConstant := by
    have hambientOne : 1 ≤ ambientConstant := ambientCWA.2.1.1
    exact ⟨hambientOne.trans (le_max_left _ _),
      max_ne_top hambientFinite
        (max_ne_top hselectedTop hratioTop)⟩
  have hfinalFinite : WZ2PaperFiniteErrorConstant
      (max outputConstant restrictionConstant) :=
    ⟨hscheduleFinite.1.trans (le_max_left _ _),
      max_ne_top hscheduleFinite.2 hrestrictionFinite.2⟩
  refine ⟨ambientCWA.1, hfinalFinite,
    ambientCWA.2.2.1.subfamily selected, ?_⟩
  · intro requested
    let coordinate := schedule.representative requested
    let ambient := schedule.witness coordinate
    let selectedCoarse := ambient.scaleData.cover.hitParentSubfamily selected
    have hselectedCoarseNonempty : selectedCoarse.family.Nonempty :=
      ambient.scaleData.cover.hitParentSubfamily_nonempty
        selected selectedNonempty
    let restrictedCover :=
      ambient.scaleData.cover.restrictToHitParents selected
    have hselectedUniform :
        WZ2PaperPureFullFibersAreCUniform
          selected.family selectedCoarse.family selectedConstant :=
      ambient.scaleData.cover
        |>.restrictToHitParents_fullFiber_uniform_of_subfamily
          ambient.scaleData.rho_pos.le selected selectedConstant
          (degreeUniform coordinate)
    let raw := ambient.scaleData.restrictOfWeightedRetention
      selected selectedCoarse hselectedCoarseNonempty restrictedCover
      hweightZero hweightTop hglobalRetention hselectedUniform
    have hrawRestriction :
        max selectedConstant
            ((weight⁻¹ *
                (ambientConstant * retentionConstant * selectedConstant)) *
              ambientConstant) ≤ restrictionConstant := le_max_right _ _
    have hraw :
        max selectedConstant
            ((weight⁻¹ *
                (ambientConstant * retentionConstant * selectedConstant)) *
              ambientConstant) ≤
          max outputConstant restrictionConstant :=
      hrawRestriction.trans (le_max_right _ _)
    exact ⟨{
      rho := ambient.rho
      requested_le := schedule.requested_le requested
      within_factor := schedule.within_output requested |>.trans_le (by
        gcongr
        exact le_max_left outputConstant restrictionConstant)
      scaleData := raw.mono hraw
    }⟩

end Kakeya.Assouad

end
