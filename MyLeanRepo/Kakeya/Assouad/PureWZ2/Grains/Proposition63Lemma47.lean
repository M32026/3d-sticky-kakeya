import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma44
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureNearbyFiniteLipschitzCoefficient
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FiniteLipschitzSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DirectionalPointPacking
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalFinitePlaneMap

/-!
# The Lemma 4.7 step in Proposition 6.3

This module starts from the actual coarse pair and cellwise-constant plane
map produced by `Proposition63Lemma44Data`.  It first makes the paper's
high-multiplicity refinement, uses robust transversality to certify the
close-direction hypothesis on that same refinement, and then runs the finite
pure nearby-scale variation argument.

The output records that its plane-map function is literally the same ambient
function as the Lemma 4.4 map.  Thus this is a spatial refinement of `W`, not
a second construction of an unrelated weak plane map.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The complete paper Lemma 4.7 output used after the Lemma 4.4 coarse
pair.  It records only the stable conclusion consumed downstream: a genuine
subshading, the unchanged plane-map function, Lipschitz control, an auditable
mass ledger, and restored extremality. -/
structure Proposition63Lemma47Data
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss sourceLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    (lemma44 : Proposition63Lemma44Data lemma43 sticky sourceLoss)
    (outputLoss coefficient : ℝ) where
  shading : WZ1PaperTubeShading sticky.coarse
  subshading : PaperIsSubshading shading lemma44.coarseShading
  cubical : WZ1PaperIsCubicalShading shading
  planeMap : PaperWZ1WeakPlaneMapData shading rho.1
  same_plane_map : planeMap.planeMap = lemma44.planeMap.planeMap
  lipschitz : LipschitzWith (Real.toNNReal coefficient)
    (fun point : {point : Point3 // point ∈ shading.union} =>
      planeMap.planeMap point)
  massLoss : ENNReal
  massLoss_pos : 0 < massLoss
  massLoss_ne_top : massLoss ≠ ⊤
  mass_retention :
    massLoss⁻¹ * lemma44.coarseShading.mass ≤ shading.mass
  extremal : WZ2PaperCroppedIsExtremal
    sigma outputLoss sticky.coarse shading
  top_level_cwa : WZ2PaperConvexWolffBound sticky.coarse
    (Kakeya.realRpowENN rho.1 (-outputLoss))

/-- Package the output of the extremality-restored finite iteration as the
stable Lemma 4.7 object.  In particular no high-multiplicity intermediate
shading is exposed or reconstructed here. -/
def Proposition63ExtremalFiniteLipschitzData.toLemma47
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss sourceLoss
      outputLoss coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky sourceLoss}
    (data : Proposition63ExtremalFiniteLipschitzData
      (sigma := sigma) lemma44.coarseShading lemma44.planeMap
        outputLoss coefficient)
    (htopLevel : WZ2PaperConvexWolffBound sticky.coarse
      (Kakeya.realRpowENN rho.1 (-outputLoss))) :
    Proposition63Lemma47Data lemma44 outputLoss coefficient where
  shading := data.shading
  subshading := data.subshading
  cubical := data.cubical
  planeMap := data.planeMap
  same_plane_map := data.same_plane_map
  lipschitz := data.lipschitz
  massLoss := data.massLoss
  massLoss_pos := data.massLoss_pos
  massLoss_ne_top := data.massLoss_ne_top
  mass_retention := data.mass_retention
  extremal := data.extremal
  top_level_cwa := htopLevel

/-- Canonical Lemma 4.7 runtime wrapper.  The finite loss schedule has already
been chosen backwards.  At runtime the genuine coarse re-entry retained by
the preceding rich Proposition 6.2 call is reused, Lemma 4.4 extremality is
weakened to the returned input loss, and all scales are then run forwards. -/
theorem proposition63_paper_lemma47_of_extremal_finite_schedule
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      reentrySourceLoss reentryNormalizationLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent N : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) lemma43.shading normalizationExponent
        reentrySourceLoss reentryNormalizationLoss}
    (rich : Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading reentry rho)
    (lemma44 : Proposition63Lemma44Data lemma43 rich.data lemma44Loss)
    (schedule : Proposition63ExtremalFiniteLipschitzScheduleData
      sigma outputLoss N)
    (hdeltaSchedule : rho.1 ≤ schedule.delta₀)
    (hsourceLoss : rich.coarseSourceLoss ≤ schedule.rootSourceLoss)
    (hnormalizationLoss :
      rich.coarseNormalizationLoss ≤ schedule.rootNormalizationLoss)
    (hlemma44Input : lemma44Loss ≤ schedule.inputLoss)
    (haxial : ∀ index point,
      point ∈ reentry.geometry.frame ''
          reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8) :
    Nonempty (Proposition63Lemma47Data lemma44 outputLoss
      (Real.rpow rho.1 (-outputLoss))) := by
  let ambientReentry := rich.coarseReentry haxial
  have currentExtremal : WZ2PaperCroppedIsExtremal sigma
      schedule.inputLoss rich.data.coarse lemma44.coarseShading :=
    lemma44.coarse_extremal.mono_loss hlemma44Input
  rcases schedule.run rich.data.coarse_extremal.delta_pos hdeltaSchedule
      ambientReentry hsourceLoss hnormalizationLoss lemma44.coarseShading
      currentExtremal lemma44.coarse_subshading lemma44.planeMap
      lemma44.planeMap_constant_on_cells
      rich.data.coarse_extremal.delta_pos.le le_rfl with ⟨finite⟩
  have topLevel : WZ2PaperConvexWolffBound rich.data.coarse
      (Kakeya.realRpowENN rho.1 (-outputLoss)) := by
    apply weaken_convex_wolff_bound ambientReentry.cropped_top_level_cwa
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      rich.data.coarse_extremal.delta_pos
      rich.data.coarse_extremal.delta_le_one (by
        linarith [hnormalizationLoss,
          schedule.rootNormalizationLoss_le_finite,
          schedule.finiteLoss_lt_output])
  exact ⟨finite.toLemma47 topLevel⟩

/-- Paper-order Lemma 4.7 on the actual Lemma 4.4 coarse pair.

The hypotheses after `htopCWA` are the finite scale schedule and the scalar
inequalities paid by the outer parameter hierarchy.  In particular, the
direction threshold is an integer multiple of the tube radius, so the
close-direction bound is derived from the essentially-distinct line packing
carried by the second Proposition 6.2 output.  The scalar `hpackingAbsorb`
then compares that geometric bound with the explicit high-multiplicity
threshold.  No pointwise close-count assumption and no second, unrelated
multiplicity band are introduced.
-/
theorem proposition63_paper_lemma47_same_plane_map
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss sourceLoss
      outputLoss coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent N : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    (lemma44 : Proposition63Lemma44Data lemma43 sticky sourceLoss)
    {C : ENNReal}
    (_htopCWA : WZ2PaperConvexWolffBound sticky.coarse C)
    (requested : ℕ → WZ2PaperRequestedScale rho.1)
    (spatialScale variationScale kappa : ℕ → ℝ)
    (densityPower : ℕ → ENNReal)
    (K : ℕ → ℕ)
    (densityLoss : ℝ)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * sourceLoss)
    (hsourceLoss : 0 < sourceLoss)
    (hsourceSmall : Kakeya.realRpowENN rho.1 sourceLoss < 1 / 4)
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (directionK : ℕ → ℕ)
    (hdirectionKOne : ∀ coordinate, coordinate < N →
      1 ≤ directionK coordinate)
    (hkappaEq : ∀ coordinate, coordinate < N →
      kappa coordinate = (directionK coordinate : ℝ) * rho.1)
    (hdirectionKScale : ∀ coordinate, coordinate < N →
      (directionK coordinate : ℝ) * rho.1 ≤ 1 / 2)
    (hdensityEq : ∀ coordinate, coordinate < N →
      densityPower coordinate =
        Kakeya.realRpowENN rho.1 densityLoss)
    (hpackingPowerAbsorb : ∀ coordinate, coordinate < N →
      (24 * ((proposition63DirectionalPointPackingConstant *
          directionK coordinate ^ 2 : ℕ) : ENNReal)) *
        ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN rho.1 (-sigma + 4 * sourceLoss))
    (hactualSmall : ∀ coordinate, coordinate < N →
      ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
        (requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < N →
      8 * ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
        (requested coordinate)).rho < kappa coordinate)
    (hspatialPositive : ∀ coordinate, coordinate < N →
      0 < spatialScale coordinate)
    (hvariationPositive : ∀ coordinate, coordinate < N →
      0 < variationScale coordinate)
    (hK : ∀ coordinate, coordinate < N → 0 < K coordinate)
    (hspatialAligned : ∀ coordinate, coordinate < N →
      spatialScale coordinate = (K coordinate : ℝ) * rho.1)
    (hcoefficient : 0 < coefficient)
    (hcovers : ∀ d : ℝ, rho.1 < d → d ≤ 4 →
      coefficient * d < 2 →
      ∃ coordinate, coordinate < N ∧ d ≤ spatialScale coordinate ∧
        variationScale coordinate ≤ coefficient * d)
    (hsourceOutput : sourceLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (htopAbsorb : C ≤ Kakeya.realRpowENN rho.1 (-outputLoss))
    (hrestore : proposition63Lemma43MassLoss
          (∏ coordinate ∈ Finset.range N, densityPower coordinate ^ 2)
          (2 * (∏ coordinate ∈ Finset.range N,
              27 * (2 *
                (wz1OrientationCapCount
                  (10 *
                      (rho.1 +
                        4 *
                          ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
                            (requested coordinate)).rho) /
                        (kappa coordinate -
                          8 *
                            ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
                              (requested coordinate)).rho))
                  (variationScale coordinate) : ENNReal))) * 27) *
          Kakeya.realRpowENN rho.1 outputLoss ≤
        Kakeya.realRpowENN rho.1 sourceLoss) :
    Nonempty (Proposition63Lemma47Data lemma44 outputLoss coefficient) := by
  rcases high_multiplicity_direction_input lemma44.coarse_extremal
      sticky.cover.coarse_line_class (hrhoSmall.trans (by norm_num))
      hdensityLoss hsourceLoss hsourceSmall with
    ⟨highMultiplicity, high, hhighSub, hhighCubical, hhighMultiplicity,
      hhighDensity, hhighMass, _hhighCommon, _hhighMultiplicityPos⟩
  have hdensityPositive : ∀ coordinate, coordinate < N →
      0 < densityPower coordinate := by
    intro coordinate hcoordinate
    rw [hdensityEq coordinate hcoordinate]
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos lemma44.coarse_extremal.delta_pos _)
  have hdensityFinite : ∀ coordinate, coordinate < N →
      densityPower coordinate ≠ ⊤ := by
    intro coordinate hcoordinate
    rw [hdensityEq coordinate hcoordinate]
    simp [Kakeya.realRpowENN]
  have hdensity : ∀ coordinate, coordinate < N →
      densityPower coordinate * sticky.coarse.enncard ≤
        (highMultiplicity : ENNReal) := by
    intro coordinate hcoordinate
    rw [hdensityEq coordinate hcoordinate]
    simpa [hdensityLoss] using hhighDensity
  let highPlaneMap :=
    paperWeakPlaneMapRestrict lemma44.planeMap hhighSub
  have hhighPlaneCell : ∀ first second,
      wz1PaperGridIndex rho.1 first =
        wz1PaperGridIndex rho.1 second →
      highPlaneMap.planeMap first = highPlaneMap.planeMap second :=
    lemma44.planeMap_constant_on_cells
  have hclose : ∀ coordinate, coordinate < N →
      ∀ point ∈ high.union, ∀ index,
        point ∈ high.carrier index →
        2 * paperCloseDirectionCount high point index
            (kappa coordinate) ≤ highMultiplicity := by
    intro coordinate hcoordinate point _hpoint index hpoint
    have hpointSource : point ∈ lemma44.coarseShading.union :=
      ⟨index, hhighSub index hpoint⟩
    have hcountSource :
        (paperCloseDirectionCount lemma44.coarseShading point index
          (kappa coordinate) : ENNReal) ≤
          ((proposition63DirectionalPointPackingConstant *
            directionK coordinate ^ 2 : ℕ) : ENNReal) := by
      have hpacking := proposition63_close_direction_count_quadratic
        (rho := rho.1) (K := directionK coordinate)
        sticky.cover.coarse_essentially_distinct
        sticky.cover.coarse_line_class lemma44.coarse_extremal.delta_pos
        hrhoSmall (hdirectionKOne coordinate hcoordinate)
        (hdirectionKScale coordinate hcoordinate)
        point index (hhighSub index hpoint)
      exact_mod_cast (by
        simpa [hkappaEq coordinate hcoordinate] using hpacking)
    have hcountMonotone :
        (paperCloseDirectionCount high point index
          (kappa coordinate) : ENNReal) ≤
          (paperCloseDirectionCount lemma44.coarseShading point index
            (kappa coordinate) : ENNReal) := by
      exact_mod_cast proposition63_close_direction_count_transfer
        hhighSub point index (kappa coordinate)
    have hcountENN :
        (2 : ENNReal) *
            (paperCloseDirectionCount high point index
              (kappa coordinate) : ENNReal) ≤
          (highMultiplicity : ENNReal) := by
      calc
        (2 : ENNReal) *
              (paperCloseDirectionCount high point index
                (kappa coordinate) : ENNReal) ≤
            2 * ((proposition63DirectionalPointPackingConstant *
              directionK coordinate ^ 2 : ℕ) : ENNReal) := by
                exact mul_le_mul_left'
                  (hcountMonotone.trans hcountSource) 2
        _ ≤ densityPower coordinate * sticky.coarse.enncard := by
          rw [hdensityEq coordinate hcoordinate]
          apply density_power_cardinality_ge_fixed
              lemma44.coarse_extremal
              (2 * ((proposition63DirectionalPointPackingConstant *
                directionK coordinate ^ 2 : ℕ) : ENNReal))
              (hrhoSmall.trans (by norm_num)) hdensityLoss
          convert hpackingPowerAbsorb coordinate hcoordinate using 1 <;>
            norm_num <;> ring
        _ ≤ (highMultiplicity : ENNReal) :=
          hdensity coordinate hcoordinate
    exact_mod_cast hcountENN
  rcases paper_pure_nearby_cwa_fixed_plane_map_finite_lipschitz_coefficient
      lemma44.coarse_extremal.cwa_nearby_scales high
      lemma44.coarse_extremal.nonempty sticky.cover.coarse_line_class
      hhighCubical highPlaneMap hhighPlaneCell
      highMultiplicity hhighMultiplicity N requested spatialScale
      variationScale kappa densityPower hclose
      hdensity lemma44.coarse_extremal.delta_pos.le
      hactualSmall hparentKappa K hK
      hspatialPositive hvariationPositive hspatialAligned
      lemma44.coarse_extremal.delta_pos hcoefficient hcovers with
    ⟨final, finalPlaneMap, hfinalSubBand, hsameBandMap, hfinalCubical,
      hfinalMultiplicity, hfinalLipschitz, hfiniteMass⟩
  let finiteLeft : ENNReal :=
    ∏ coordinate ∈ Finset.range N, densityPower coordinate ^ 2
  let finiteRight : ENNReal :=
    (∏ coordinate ∈ Finset.range N,
      27 * (2 *
        (wz1OrientationCapCount
          (10 *
              (rho.1 +
                4 *
                  ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
                    (requested coordinate)).rho) /
                (kappa coordinate -
                  8 *
                    ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
                      (requested coordinate)).rho))
          (variationScale coordinate) : ENNReal))) * 27
  let massLoss : ENNReal :=
    proposition63Lemma43MassLoss finiteLeft (2 * finiteRight)
  have hfinalSub : PaperIsSubshading final lemma44.coarseShading :=
    fun index => (hfinalSubBand index).trans (hhighSub index)
  have hsourceHigh : lemma44.coarseShading.mass ≤
      2 * high.mass := by
    have htwice := mul_le_mul_left' hhighMass (2 : ENNReal)
    have htwoHalf : (2 : ENNReal) * (1 / 2) = 1 := by
      rw [show (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ by norm_num]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    calc
      lemma44.coarseShading.mass =
          2 * ((1 / 2 : ENNReal) * lemma44.coarseShading.mass) := by
        rw [← mul_assoc, htwoHalf, one_mul]
      _ ≤ 2 * high.mass := htwice
  have hcombinedMass : finiteLeft * lemma44.coarseShading.mass ≤
      (2 * finiteRight) * final.mass := by
    calc
      finiteLeft * lemma44.coarseShading.mass ≤
          finiteLeft * (2 * high.mass) := by gcongr
      _ = 2 * (finiteLeft * high.mass) := by ring
      _ ≤ 2 * (finiteRight * final.mass) := by
        exact mul_le_mul_left'
          (by simpa [finiteLeft, finiteRight] using hfiniteMass)
          2
      _ = (2 * finiteRight) * final.mass := by ring
  have hfiniteLeftPos : 0 < finiteLeft := by
    dsimp only [finiteLeft]
    rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro coordinate hcoordinate
    exact (ENNReal.pow_pos
      (hdensityPositive coordinate (Finset.mem_range.mp hcoordinate)) 2).ne'
  have hfiniteLeftTop : finiteLeft ≠ ⊤ := by
    dsimp only [finiteLeft]
    apply ENNReal.prod_ne_top
    intro coordinate _
    exact ENNReal.pow_ne_top
      (hdensityFinite coordinate (Finset.mem_range.mp ‹_›))
  have hfiniteRightTop : finiteRight ≠ ⊤ := by
    dsimp only [finiteRight]
    exact ENNReal.mul_ne_top
      (ENNReal.prod_ne_top fun _ _ =>
        ENNReal.mul_ne_top (by norm_num)
          (ENNReal.mul_ne_top (by norm_num) (by simp)))
      (by norm_num)
  have hmassLossPos : 0 < massLoss := by
    exact proposition63Lemma43MassLoss_pos _ _
  have hmassLossTop : massLoss ≠ ⊤ := by
    exact proposition63Lemma43MassLoss_ne_top hfiniteLeftPos
      (ENNReal.mul_ne_top (by norm_num) hfiniteRightTop)
  have hmassRetention : massLoss⁻¹ * lemma44.coarseShading.mass ≤
      final.mass := by
    exact proposition63Lemma43MassLoss_inv_mul_le hfiniteLeftPos
      hfiniteLeftTop (ENNReal.mul_ne_top (by norm_num) hfiniteRightTop)
      hcombinedMass
  have hfinalExtremal : WZ2PaperCroppedIsExtremal
      sigma outputLoss sticky.coarse final := by
    apply transfer_cropped_extremal_to_subshading massLoss
      hmassLossPos hmassLossTop lemma44.coarse_extremal hfinalSub
      hmassRetention hfinalCubical hsourceOutput
    · simpa only [massLoss, finiteLeft, finiteRight, mul_assoc] using
        hrestore
    · exact lemma44.coarse_extremal.delta_pos
    · exact lemma44.coarse_extremal.delta_le_one
    · exact houtputLoss
  have hfinalTopCWA : WZ2PaperConvexWolffBound sticky.coarse
      (Kakeya.realRpowENN rho.1 (-outputLoss)) := by
    intro convexSet hconvex
    exact (_htopCWA convexSet hconvex).trans (by gcongr)
  refine ⟨{
    shading := final
    subshading := hfinalSub
    cubical := hfinalCubical
    planeMap := finalPlaneMap
    same_plane_map := ?_
    lipschitz := ?_
    massLoss := massLoss
    massLoss_pos := hmassLossPos
    massLoss_ne_top := hmassLossTop
    mass_retention := hmassRetention
    extremal := hfinalExtremal
    top_level_cwa := hfinalTopCWA
  }⟩
  · exact hsameBandMap.trans rfl
  · exact hfinalLipschitz

/-- The Proposition 6.3 specialization of Lemma 4.7: consume the fixed-length
power-scale schedule rather than exposing its four coordinate functions and
the terminal covering argument separately.  The remaining assumptions are
the geometric close-count/density inputs and the loss absorptions from the
outer epsilon hierarchy. -/
theorem proposition63_paper_lemma47_from_finite_schedule
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss sourceLoss
      outputLoss coefficient ratio : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent N : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    (lemma44 : Proposition63Lemma44Data lemma43 sticky sourceLoss)
    {C : ENNReal}
    (_htopCWA : WZ2PaperConvexWolffBound sticky.coarse C)
    (schedule : Proposition63FiniteLipschitzSchedule
      rho.1 coefficient ratio N)
    (kappa : ℕ → ℝ)
    (densityPower : ℕ → ENNReal)
    (densityLoss : ℝ)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * sourceLoss)
    (hsourceLoss : 0 < sourceLoss)
    (hsourceSmall : Kakeya.realRpowENN rho.1 sourceLoss < 1 / 4)
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (directionK : ℕ → ℕ)
    (hdirectionKOne : ∀ coordinate, coordinate < N →
      1 ≤ directionK coordinate)
    (hkappaEq : ∀ coordinate, coordinate < N →
      kappa coordinate = (directionK coordinate : ℝ) * rho.1)
    (hdirectionKScale : ∀ coordinate, coordinate < N →
      (directionK coordinate : ℝ) * rho.1 ≤ 1 / 2)
    (hdensityEq : ∀ coordinate, coordinate < N →
      densityPower coordinate =
        Kakeya.realRpowENN rho.1 densityLoss)
    (hpackingPowerAbsorb : ∀ coordinate, coordinate < N →
      (24 * ((proposition63DirectionalPointPackingConstant *
          directionK coordinate ^ 2 : ℕ) : ENNReal)) *
        ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN rho.1 (-sigma + 4 * sourceLoss))
    (hactualSmall : ∀ coordinate, coordinate < N →
      ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
        (schedule.requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < N →
      8 * ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
        (schedule.requested coordinate)).rho < kappa coordinate)
    (hcoefficient : 0 < coefficient)
    (hsourceOutput : sourceLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (htopAbsorb : C ≤ Kakeya.realRpowENN rho.1 (-outputLoss))
    (hrestore : proposition63Lemma43MassLoss
          (∏ coordinate ∈ Finset.range N, densityPower coordinate ^ 2)
          (2 * (∏ coordinate ∈ Finset.range N,
              27 * (2 *
                (wz1OrientationCapCount
                  (10 *
                      (rho.1 +
                        4 *
                          ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
                            (schedule.requested coordinate)).rho) /
                        (kappa coordinate -
                          8 *
                            ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
                              (schedule.requested coordinate)).rho))
                  (schedule.variationScale coordinate) : ENNReal))) * 27) *
          Kakeya.realRpowENN rho.1 outputLoss ≤
        Kakeya.realRpowENN rho.1 sourceLoss) :
    Nonempty (Proposition63Lemma47Data lemma44 outputLoss coefficient) := by
  exact proposition63_paper_lemma47_same_plane_map lemma44 _htopCWA
    schedule.requested schedule.spatialScale schedule.variationScale
    kappa densityPower schedule.K densityLoss hdensityLoss hsourceLoss
    hsourceSmall hrhoSmall
    directionK hdirectionKOne hkappaEq hdirectionKScale
    hdensityEq hpackingPowerAbsorb hactualSmall
    hparentKappa schedule.spatial_pos schedule.variation_pos schedule.K_pos
    schedule.spatial_aligned hcoefficient schedule.covers hsourceOutput
    houtputLoss htopAbsorb hrestore

end Kakeya.Assouad.PureWZ2

end
