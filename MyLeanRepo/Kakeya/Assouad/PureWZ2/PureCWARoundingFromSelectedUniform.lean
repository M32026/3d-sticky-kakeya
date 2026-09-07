import MyLeanRepo.Kakeya.Assouad.PureWZ2.DegreeUniformRestrictedCWA

/-!
# Pure CWA rounding from selected full-fiber uniformity

The complete-parent route proves selected full-fiber uniformity differently
on the two sides of the actual scale:

* finer scheduled covers are retained fiberwise in full;
* coarser scheduled covers are controlled by selected actual-parent class
  counts.

This module performs the remaining common assembly.  It rounds every requested
scale upward to a finite scheduled witness and applies
`WZ2PaperPureScaleCoverData.restrictOfWeightedRetention` using the already
proved selected full-fiber uniformity at that witness.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Recover pure nearby-scale CWA from a finite rounding schedule once every
scheduled restricted cover has uniform complete fibers.
-/
theorem pure_cwa_restrict_with_rounding_of_selected_uniform
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant R : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (selectedNonempty : selected.family.Nonempty)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduledWitness :
      ∀ coordinate : Fin coordinateCount,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (selectedConstant retentionConstant weight : ENNReal)
    (weight_ne_zero : weight ≠ 0)
    (weight_ne_top : weight ≠ ⊤)
    (retention_ne_top : retentionConstant ≠ ⊤)
    (selectedConstant_ne_top : selectedConstant ≠ ⊤)
    (globalRetention :
      weight * fine.enncard ≤
        retentionConstant * selected.family.enncard)
    (selectedUniform :
      ∀ coordinate : Fin coordinateCount,
        WZ2PaperPureFullFibersAreCUniform
          selected.family
          ((scheduledWitness coordinate).scaleData.cover
            |>.hitParentSubfamily selected).family
          selectedConstant)
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
          ambientConstant weight
          selectedConstant retentionConstant ≤
        outputConstant) :
    WZ2PaperPureCWAAtNearbyScales
      selected.family outputConstant := by
  have delta_pos : 0 < delta := ambient.1
  have ambient_le_output :
      ambientConstant ≤ outputConstant := by
    calc
      ambientConstant =
          1 * ambientConstant := by simp
      _ ≤ R * ambientConstant := by gcongr
      _ ≤ outputConstant := window_absorption
  have outputFinite :
      WZ2PaperFiniteErrorConstant outputConstant :=
    ⟨ambient.2.1.1.trans ambient_le_output,
      output_ne_top⟩
  refine
    ⟨delta_pos, outputFinite,
      ambient.2.2.1.subfamily selected, ?_⟩
  intro requested
  rcases rounding requested with
    ⟨coordinate, requestedScheduled, scheduledWindow⟩
  let scheduled := scales coordinate
  let nearby := scheduledWitness coordinate
  let selectedCoarse :=
    nearby.scaleData.cover.hitParentSubfamily selected
  have selectedCoarseNonempty :
      selectedCoarse.family.Nonempty :=
    nearby.scaleData.cover.hitParentSubfamily_nonempty
      selected selectedNonempty
  let restrictedCover :=
    nearby.scaleData.cover.restrictToHitParents selected
  let rawScale :=
    nearby.scaleData.restrictOfWeightedRetention
      selected selectedCoarse selectedCoarseNonempty
      restrictedCover
      weight_ne_zero weight_ne_top
      globalRetention (selectedUniform coordinate)
  let restrictedConstant :=
    max selectedConstant
      ((weight⁻¹ *
          (ambientConstant * retentionConstant *
            selectedConstant)) *
        ambientConstant)
  have restricted_le_output :
      restrictedConstant ≤ outputConstant := by
    have h :
        restrictedConstant ≤
          wz2PaperPureNearbyRestrictionConstant
            ambientConstant weight
            selectedConstant retentionConstant :=
      le_max_right _ _
    exact h.trans restriction_absorption
  let weakenedScale :=
    rawScale.mono restricted_le_output
  have requested_le_actual :
      requested.1 ≤ nearby.rho := by
    exact
      requestedScheduled.trans nearby.requested_le
  have actual_window :
      ENNReal.ofReal nearby.rho <
        outputConstant * ENNReal.ofReal requested.1 := by
    calc
      ENNReal.ofReal nearby.rho <
          ambientConstant *
            ENNReal.ofReal scheduled.1 :=
        nearby.within_factor
      _ ≤
          ambientConstant *
            (R * ENNReal.ofReal requested.1) := by
        gcongr
      _ =
          (R * ambientConstant) *
            ENNReal.ofReal requested.1 := by ring
      _ ≤
          outputConstant *
            ENNReal.ofReal requested.1 := by
        gcongr
  exact
    ⟨{
      rho := nearby.rho
      requested_le := requested_le_actual
      within_factor := actual_window
      scaleData := weakenedScale
    }⟩

end Kakeya.Assouad

end
