import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SelectedCardinalityCancellation
import MyLeanRepo.Kakeya.Assouad.PropStickyConvexWolffCoverTransfer
import MyLeanRepo.Kakeya.Assouad.PropStickyConvexWolffSubfamilyTransfer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCardinalityRetention
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalCapAbsorption

/-!
# Top-level CWA bridges for a pure sticky output

The first bridge transfers a top-level Convex--Wolff bound from the source
family to the selected fine family.  All losses are displayed explicitly:
one density inverse, one polylogarithmic retention inverse, and the fixed
paper-tube volume constant.

The second bridge transfers that selected-family bound to the coarse sticky
family under an explicit assigned-fiber uniformity estimate.  The Section 6
cover stores line-distance cover rather than literal carrier containment, so
we also record the quantitative scale separation used to derive the latter.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- A refinement shading has no more mass than the ambient shading restricted
to the same selected tube indices. -/
lemma PureWZ2PropStickyData.refined_mass_le_restrict
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) :
    data.refined.mass ≤
      (restrictPaperShading data.selected sourceShading).mass := by
  rw [restrictPaperShading_mass]
  change
    (∑ index : Fin data.selected.family.card,
        volume (data.refined.carrier index)) ≤
      ∑ index : Fin data.selected.family.card,
        volume
          (sourceShading.carrier (data.selected.embedding index))
  exact Finset.sum_le_sum fun index _ =>
    measure_mono (data.subshading index)

/-- Source density plus sticky mass retention transfers top-level CWA to the
selected fine family, with every multiplicative loss left visible. -/
theorem PureWZ2PropStickyData.selected_top_level_cwa
    {delta sigma sourceLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (sourceExtremal :
      WZ2PaperCroppedIsExtremal
        sigma sourceLoss source sourceShading)
    (sourceLine : WZ1PaperIsLineClass source)
    (hdeltaSmall : delta ≤ 1 / 24)
    (C : ENNReal)
    (sourceCWA : WZ2PaperConvexWolffBound source C) :
    WZ2PaperConvexWolffBound data.selected.family
      (((Kakeya.realRpowENN delta sourceLoss)⁻¹ *
          ((wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
            (55296 * Kakeya.deltaTubeVolume 1))) * C) := by
  let density : ENNReal :=
    Kakeya.realRpowENN delta sourceLoss
  let fraction : ENNReal :=
    wz2PaperPureRefinementFraction delta logExponent
  let geometryConstant : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1
  have hdeltaStrict : delta < 1 := by
    linarith
  have hfractionZero : fraction ≠ 0 := by
    change wz1PaperRefinementFraction delta logExponent ≠ 0
    exact wz1PaperRefinementFraction_ne_zero
      sourceExtremal.delta_pos hdeltaStrict logExponent
  have hfractionTop : fraction ≠ ⊤ := by
    change wz1PaperRefinementFraction delta logExponent ≠ ⊤
    exact wz1PaperRefinementFraction_ne_top
      sourceExtremal.delta_pos hdeltaStrict logExponent
  have hdensityZero : density ≠ 0 := by
    simp [density, Kakeya.realRpowENN,
      Real.rpow_pos_of_pos sourceExtremal.delta_pos]
  have hdensityTop : density ≠ ⊤ := by
    simp [density, Kakeya.realRpowENN]
  have hbody :
      Kakeya.realRpowENN delta 2 * source.enncard ≤
        (wz1PaperBodyFamily source).mass :=
    PureWZ2.paperBodyFamily_mass_lower_rpow_two
      sourceExtremal.delta_pos
      (hdeltaSmall.trans (by norm_num)) sourceLine
  have hambientMass :
      density * source.enncard * Kakeya.realRpowENN delta 2 ≤
        sourceShading.mass := by
    calc
      density * source.enncard * Kakeya.realRpowENN delta 2 =
          density *
            (Kakeya.realRpowENN delta 2 * source.enncard) := by
        ring
      _ ≤ density * (wz1PaperBodyFamily source).mass := by
        gcongr
      _ ≤ sourceShading.mass := sourceExtremal.dense
  have hretained :
      sourceShading.mass ≤
        fraction⁻¹ *
          (restrictPaperShading data.selected sourceShading).mass := by
    have hraw :
        fraction * sourceShading.mass ≤
          (restrictPaperShading data.selected sourceShading).mass :=
      data.retained_mass.trans data.refined_mass_le_restrict
    calc
      sourceShading.mass =
          (fraction⁻¹ * fraction) * sourceShading.mass := by
        rw [ENNReal.inv_mul_cancel hfractionZero hfractionTop, one_mul]
      _ = fraction⁻¹ *
          (fraction * sourceShading.mass) := by
        rw [mul_assoc]
      _ ≤ fraction⁻¹ *
          (restrictPaperShading data.selected sourceShading).mass := by
        gcongr
  have hcardinality :
      density * source.enncard ≤
        (fraction⁻¹ * geometryConstant) *
          data.selected.family.enncard := by
    simpa [geometryConstant] using
      wz2PaperWeightedCardinality_retained_from_subfamily_mass
        sourceExtremal.delta_pos hdeltaSmall sourceLine
        sourceShading data.selected density fraction⁻¹
        hambientMass hretained
  simpa [density, fraction, geometryConstant] using
    sourceCWA.subfamily_of_weighted_cardinality
      data.selected hdensityZero hdensityTop hcardinality

/-- A strict Section 6 line cover gives literal paper-carrier containment once
the coarse radius is at least six times the fine radius. -/
theorem wz2PaperTubeCarrierCovers_of_strict_cover
    {delta rho : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hscale : 6 * delta ≤ rho)
    (hfine : WZ1PaperTubeInLineClass fine)
    (hcoarse : WZ1PaperTubeInLineClass coarse)
    (hcover : WZ1PaperTubeCovers fine coarse) :
    WZ2PaperTubeCarrierCovers fine coarse := by
  intro point hpoint
  rcases hpoint with ⟨hthickening, hbox⟩
  rcases
      exists_dist_le_of_mem_cthickening_closed
        (isClosed_tubeAxisLine fine)
        (by positivity : 0 ≤ 6 * delta) hthickening
    with ⟨fineAxisPoint, hfineAxis, hpointFineAxis⟩
  let height := point (2 : Fin 3)
  let fineAtHeight := wz1PaperAxisPointAtHeight fine height
  let coarseAtHeight := wz1PaperAxisPointAtHeight coarse height
  have hheight : |height| ≤ 1 := by
    simpa [height, Kakeya.Streamlined.axisBox] using hbox.2.2
  have hpointFineHeight :
      dist point fineAtHeight ≤ 12 * delta := by
    have hprojection :=
      wz1Paper_axisPointAtHeight_dist_point_le_two_mul
        hfine point fineAxisPoint hfineAxis
    rw [dist_comm] at hprojection
    exact hprojection.trans (by nlinarith)
  have hfineCoarseHeight :
      dist fineAtHeight coarseAtHeight ≤ 3 * rho := by
    have haxis :=
      wz1PaperAxisPointAtHeight_dist_le hfine hcoarse hheight
    exact haxis.trans (by
      dsimp only [WZ1PaperTubeCovers] at hcover
      nlinarith)
  have hpointCoarseHeight :
      dist point coarseAtHeight ≤ 6 * rho := by
    calc
      dist point coarseAtHeight ≤
          dist point fineAtHeight +
            dist fineAtHeight coarseAtHeight :=
        dist_triangle _ _ _
      _ ≤ 12 * delta + 3 * rho := by
        gcongr
      _ ≤ 6 * rho := by
        nlinarith
  have hcoarseAxis :
      coarseAtHeight ∈ tubeAxisLine coarse :=
    wz1PaperAxisPointAtHeight_mem_axis coarse height
  exact
    ⟨Metric.mem_cthickening_of_dist_le
        point coarseAtHeight (6 * rho)
        _ hcoarseAxis hpointCoarseHeight,
      hbox⟩

/-- Transfer selected-family top-level CWA to the actual coarse sticky family
through the canonical Section 6 parent map and an explicit fiber-uniformity
constant. -/
theorem PureWZ2PropStickyData.coarse_top_level_cwa_of_fiber_uniform
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (hdelta : 0 < delta)
    (hscale : 6 * delta ≤ rho.1)
    (K C : ENNReal)
    (fiberUniform :
      ∀ first second : Fin data.coarse.card,
        ((Finset.univ.filter fun fineIndex =>
          data.cover.toPaperTubeCover.parent fineIndex = first).card :
            ENNReal) ≤
          K *
            ((Finset.univ.filter fun fineIndex =>
              data.cover.toPaperTubeCover.parent fineIndex = second).card :
                ENNReal))
    (selectedCWA :
      WZ2PaperConvexWolffBound data.selected.family C) :
    WZ2PaperConvexWolffBound data.coarse (K * C) := by
  apply paperConvexWolffBound_of_uniform_cover
      data.cover.toPaperTubeCover.parent
      data.cover.toPaperTubeCover.parent_surjective
      (fun fineIndex => ?_) K C fiberUniform selectedCWA
  exact wz2PaperTubeCarrierCovers_of_strict_cover
    hdelta
    data.coarse_extremal.delta_pos hscale
    (data.cover.fine_line_class fineIndex)
    (data.cover.coarse_line_class
      (data.cover.toPaperTubeCover.parent fineIndex))
    (data.cover.toPaperTubeCover.parent_covers fineIndex)

/-- Every surjective finite parent map is uniformly bounded with the crude
constant `#fine`.  This is mathematically valid but intentionally leaves the
potentially non-absorbable cardinality cost visible. -/
lemma PureWZ2PropStickyData.crude_fiber_uniform
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) :
    ∀ first second : Fin data.coarse.card,
      ((Finset.univ.filter fun fineIndex =>
        data.cover.toPaperTubeCover.parent fineIndex = first).card :
          ENNReal) ≤
        data.selected.family.enncard *
          ((Finset.univ.filter fun fineIndex =>
            data.cover.toPaperTubeCover.parent fineIndex = second).card :
              ENNReal) := by
  intro first second
  let firstFiber : Finset (Fin data.selected.family.card) :=
    Finset.univ.filter fun fineIndex =>
      data.cover.toPaperTubeCover.parent fineIndex = first
  let secondFiber : Finset (Fin data.selected.family.card) :=
    Finset.univ.filter fun fineIndex =>
      data.cover.toPaperTubeCover.parent fineIndex = second
  have hfirst : firstFiber.card ≤ data.selected.family.card := by
    have hsubset : firstFiber ⊆
        (Finset.univ : Finset (Fin data.selected.family.card)) := by
      exact Finset.subset_univ _
    simpa using Finset.card_le_card hsubset
  have hsecond : 1 ≤ (secondFiber.card : ENNReal) := by
    rcases data.cover.toPaperTubeCover.parent_surjective second with
      ⟨fineIndex, hparent⟩
    have hmem : fineIndex ∈ secondFiber := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hparent⟩
    exact_mod_cast Finset.one_le_card.mpr ⟨fineIndex, hmem⟩
  calc
    (firstFiber.card : ENNReal) ≤
        data.selected.family.enncard := by
      change (firstFiber.card : ENNReal) ≤
        (data.selected.family.card : ENNReal)
      exact_mod_cast hfirst
    _ = data.selected.family.enncard * 1 := by simp
    _ ≤ data.selected.family.enncard *
        (secondFiber.card : ENNReal) := by
      gcongr

/-- Unconditional coarse CWA with the exact crude fiber-cardinality cost. -/
theorem PureWZ2PropStickyData.coarse_top_level_cwa_crude
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (hdelta : 0 < delta)
    (hscale : 6 * delta ≤ rho.1)
    (C : ENNReal)
    (selectedCWA :
      WZ2PaperConvexWolffBound data.selected.family C) :
    WZ2PaperConvexWolffBound data.coarse
      (data.selected.family.enncard * C) := by
  exact data.coarse_top_level_cwa_of_fiber_uniform
    hdelta hscale data.selected.family.enncard C
    data.crude_fiber_uniform selectedCWA

end Kakeya.Assouad

end
