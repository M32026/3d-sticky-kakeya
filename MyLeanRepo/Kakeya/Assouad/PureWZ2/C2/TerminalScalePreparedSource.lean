import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Refinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Section6CoverAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.GrainRestriction
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Same-scale Pure grain data on the terminal sticky refinement

The terminal construction keeps the source tube radius.  Its single sticky
application only supplies the `sqrt delta` balanced cover.  This module
restricts the original global slope and local plane map to the selected
same-scale refinement, preserving their literal paper AD certificates.

No CWA inheritance for an arbitrary subfamily is asserted.  The eventual
same-extremizer grain producer is responsible for the final CWA package.
-/

noncomputable section

namespace Kakeya.Assouad

/--
All same-scale data needed to run terminal Lemma 23 on the sticky refinement.
-/
structure PureWZ2TerminalPreparedSource
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (terminal : PureWZ2TerminalScaleStickyData
      source stickyLoss logExponent) where
  shading : WZ1PaperTubeShading terminal.sticky.selected.family :=
    terminal.sticky.refined
  shading_eq : shading = terminal.sticky.refined
  line_class : WZ1PaperIsLineClass terminal.sticky.selected.family
  cubical : WZ1PaperIsCubicalShading shading
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  nonempty : terminal.sticky.selected.family.Nonempty
  volume_lower : Kakeya.realRpowENN delta (sigma + stickyLoss) ≤
    MeasureTheory.volume shading.union
  multiplicity : ℕ := terminal.sticky.fineMultiplicity
  multiplicity_pos : 0 < multiplicity
  constant_multiplicity :
    shading.HasConstantMultiplicity multiplicity (2 * multiplicity)
  globalGrains : PureWZ2BoundedLipschitzGlobalGrainData shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  global_slope_eq : globalGrains.slope = source.globalGrains.slope
  localGrains : PureWZ2LocalGrainData shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  planeMap_vertical_bound :
    ∀ point : {point : Point3 // point ∈ shading.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2

theorem PureWZ2TerminalScaleStickyData.prepareSource
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (terminal : PureWZ2TerminalScaleStickyData
      source stickyLoss logExponent) :
    Nonempty (PureWZ2TerminalPreparedSource source terminal) := by
  let restrictedGlobal :=
    source.globalGrains.toPureWZ2LipschitzGlobalGrainData.restrictSubfamilyWithShading
      terminal.sticky.selected terminal.sticky.refined terminal.sticky.subshading
  let globalGrains :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound restrictedGlobal <| by
      intro z hz
      exact source.globalGrains.slope_bound z hz
  let localGrains := source.localGrains.restrictSubfamilyWithShading
    terminal.sticky.selected terminal.sticky.refined terminal.sticky.subshading
  exact ⟨{
    shading := terminal.sticky.refined
    shading_eq := rfl
    line_class := source.line_class.subfamily terminal.sticky.selected
    cubical := terminal.sticky.refined_cubical
    delta_pos := source.extremal.delta_pos
    delta_le_one := source.extremal.delta_le_one
    nonempty := terminal.sticky.selected_nonempty
    volume_lower := terminal.sticky.refined_volume_lower
    multiplicity := terminal.sticky.fineMultiplicity
    multiplicity_pos := terminal.sticky.fineMultiplicity_pos
    constant_multiplicity := terminal.sticky.refined_multiplicity_band
    globalGrains := globalGrains
    global_slope_eq := rfl
    localGrains := localGrains
    planeMap_vertical_bound := by
      intro point
      exact source.planeMap_vertical_bound
        ⟨point, by
          rcases point.property with ⟨index, hpoint⟩
          exact ⟨terminal.sticky.selected.embedding index,
            terminal.sticky.subshading index hpoint⟩⟩
  }⟩

/-- Every active terminal `sqrt delta` parent carries the expected source floor. -/
theorem PureWZ2TerminalScaleStickyData.source_floor_power
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (terminal : PureWZ2TerminalScaleStickyData
      source stickyLoss logExponent) :
    Kakeya.realRpowENN delta
        (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) ≤
      terminal.sticky.balanced.cellMass := by
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hsqrt : terminal.sqrtRequested.1 = Real.sqrt delta :=
    terminal.sqrtRequested_eq
  have hcube : MeasureTheory.volume
      (wz1PaperGridCube terminal.sqrtRequested.1 (0, 0, 0)) =
        Kakeya.realRpowENN delta (3 / 2) := by
    rw [wz1PaperGridCube_volume_exact
      terminal.sticky.coarse_extremal.delta_pos, hsqrt]
    simp only [Kakeya.realRpowENN, Real.sqrt_eq_rpow]
    apply congrArg ENNReal.ofReal
    calc
      (Real.rpow delta (1 / 2)) ^ 3 =
          Real.rpow delta ((1 / 2 : ℝ) * (3 : ℕ)) :=
        (Real.rpow_mul_natCast hdelta.le (1 / 2) 3).symm
      _ = Real.rpow delta (3 / 2) := by congr 1 <;> ring
  have hcoarsePower :
      Kakeya.realRpowENN terminal.sqrtRequested.1
          (sigma - stickyLoss) =
        Kakeya.realRpowENN delta ((sigma - stickyLoss) / 2) := by
    rw [hsqrt]
    simp only [Kakeya.realRpowENN, Real.sqrt_eq_rpow]
    apply congrArg ENNReal.ofReal
    calc
      (Real.rpow delta (1 / 2)).rpow (sigma - stickyLoss) =
          Real.rpow delta ((1 / 2) * (sigma - stickyLoss)) :=
        (Real.rpow_mul hdelta.le (1 / 2) (sigma - stickyLoss)).symm
      _ = Real.rpow delta ((sigma - stickyLoss) / 2) := by
        congr 1 <;> ring
  have hraw := terminal.sticky.source_floor_raw hdelta
  rw [hcube, hcoarsePower, ← realRpowENN_add hdelta] at hraw
  let denominator :=
    Kakeya.realRpowENN delta ((sigma - stickyLoss) / 2)
  have hdenomZero : denominator ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta _))
  have hdenomTop : denominator ≠ ⊤ := by
    simp [denominator, Kakeya.realRpowENN]
  have htarget :
      Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) * denominator =
        Kakeya.realRpowENN delta (sigma + stickyLoss + 3 / 2) := by
    dsimp only [denominator]
    rw [← realRpowENN_add hdelta]
    congr 1
    ring
  apply (ENNReal.mul_le_mul_iff_left hdenomZero hdenomTop).mp
  rw [htarget]
  simpa [denominator, add_comm, add_left_comm, add_assoc, mul_comm] using hraw

end Kakeya.Assouad
