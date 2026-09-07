import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalPublicSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalBallCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ExactDiagonalCubicalGlobalAD

/-!
# Finite-slice global AD for the actual direct half-offset terminal

This is the cubical global-AD argument for the literal
`TerminalGeometry.cubicalShading`.  A target point is returned to its exact
terminal witness and then to the ambient source configuration.  Cubicality is
used only on that original same-output source shading.  The lower faces which
occur over one target slice lie in a fixed finite window, independent of the
runtime scales.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalGeometry

/-- A fixed source-cell radius for one terminal horizontal slice.  It is
deliberately rounded up only after all source-to-target scale ratios have been
cancelled. -/
def finiteSliceHeightCellRadius : ℕ :=
  Nat.ceil (128 * pureWZ2DirectHorizontalScale * Real.sqrt 3) + 1

/-- The fixed finite family of original source-grid height cells associated
to a terminal height. -/
def finiteSliceHeightCells (terminal : commonSource.TerminalGeometry)
    (z : ℝ) : Finset ℤ :=
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let sourceCenter := source.c + (source.d - source.c) / 2 *
    (terminal.box.center 2 +
      z / pureWZ2DirectHalfOffsetTerminalLambda + 1)
  let radius : ℤ := finiteSliceHeightCellRadius
  Finset.Icc (Int.floor (sourceCenter / delta) - radius)
    (Int.floor (sourceCenter / delta) + radius)

@[simp] theorem finiteSliceHeightCells_card
    (terminal : commonSource.TerminalGeometry) (z : ℝ) :
    (finiteSliceHeightCells commonSource terminal z).card =
      2 * finiteSliceHeightCellRadius + 1 := by
  unfold finiteSliceHeightCells
  rw [Int.card_Icc]
  omega

theorem finiteSliceHeightCells_nonempty
    (terminal : commonSource.TerminalGeometry) (z : ℝ) :
    (finiteSliceHeightCells commonSource terminal z).Nonempty := by
  apply Finset.card_pos.mp
  rw [finiteSliceHeightCells_card]
  omega

/-- The affine translation in the scalar projection identity.  Both maps are
centered only in the first coordinate, while the terminal box has zero
second coordinate, so this translation is independent of the height cell. -/
def finiteSliceProjectionOffset (terminal : commonSource.TerminalGeometry) : ℝ :=
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let anisotropicCenter := pureWZ2DirectAnisotropicCenter terminal.retubing.popular
  0 - pureWZ2DirectHalfOffsetTerminalLambda *
      ((anisotropicRescalingMap (pureWZ2DirectGeometrySlope source)
        source.c source.d source.m anisotropicCenter) (0 : Fin 3)) -
    pureWZ2DirectHalfOffsetTerminalLambda * (terminal.box.center 0)

/-- Exact height formula for the total affine terminal map. -/
theorem totalAffineMap_coord_two
    (terminal : commonSource.TerminalGeometry) (point : Point3) :
    totalAffineMap commonSource terminal point 2 =
      pureWZ2DirectHalfOffsetTerminalLambda *
        (2 * (point 2 -
          commonSource.halfOffsetAssembly.horizontalSource.c) /
            (commonSource.halfOffsetAssembly.horizontalSource.d -
              commonSource.halfOffsetAssembly.horizontalSource.c) - 1 -
          terminal.box.center 2) := by
  simp [totalAffineMap, pureWZ2LineClassNormalizationMap,
    anisotropicCenteredRescalingMap, anisotropicRescalingMap, point3]

/-- The exact terminal projection is a fixed affine image of the ambient
source projection.  This statement is used only at genuine exact witnesses,
so the safe public slope agrees there with the literal transported slope. -/
theorem exact_projection_eq_source
    (terminal : commonSource.TerminalGeometry)
    (exactPoint : {point : Point3 // point ∈ terminal.exactShading.union}) :
    let sourcePoint :=
      commonSource.halfOffsetTerminalSourcePoint terminal.retubing terminal.box
        pureWZ2DirectHalfOffsetTerminalLambda_pos
        (exactSetPoint commonSource terminal exactPoint)
    inner ℝ (exactPoint : Point3)
        (globalGrainDirection
          (safePublicSlope commonSource terminal ((exactPoint : Point3) 2))) =
      pureWZ2DirectHalfOffsetTerminalLambda *
          inner ℝ (sourcePoint : Point3)
            (globalGrainDirection
              (commonSource.halfOffsetAssembly.globalSlope
                ((sourcePoint : Point3) 2))) +
        finiteSliceProjectionOffset commonSource terminal := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let rawPoint := commonSource.halfOffsetTerminalRawPoint terminal.retubing
    terminal.box pureWZ2DirectHalfOffsetTerminalLambda_pos
      (exactSetPoint commonSource terminal exactPoint)
  let sourcePoint := commonSource.halfOffsetTerminalSourcePoint terminal.retubing
    terminal.box pureWZ2DirectHalfOffsetTerminalLambda_pos
      (exactSetPoint commonSource terminal exactPoint)
  have hrawHeight : (rawPoint : Point3) 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases rawPoint.property with ⟨index, hpoint⟩
    have hbox := terminal.retubing.raw.exactShading.subset_body index hpoint
    exact abs_le.mp <| by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.2.2
  have hinverseHeight : terminal.box.center 2 +
      (exactPoint : Point3) 2 / pureWZ2DirectHalfOffsetTerminalLambda =
        (rawPoint : Point3) 2 := by
    have hmap := commonSource.halfOffsetTerminal_map_rawPoint terminal.retubing
      terminal.box pureWZ2DirectHalfOffsetTerminalLambda_pos
        (exactSetPoint commonSource terminal exactPoint)
    have hcoord := congrArg (fun point : Point3 => point 2) hmap
    simp only [pureWZ2LineClassNormalizationMap, point3_coord2] at hcoord
    change pureWZ2DirectHalfOffsetTerminalLambda *
      ((rawPoint : Point3) 2 - terminal.box.center 2) =
        (exactPoint : Point3) 2 at hcoord
    rw [← hcoord]
    field_simp [pureWZ2DirectHalfOffsetTerminalLambda_pos.ne']
    ring
  have hsafe := safePublicSlope_eq_exactGlobalSlope commonSource terminal
    ((exactPoint : Point3) 2) (by rwa [hinverseHeight])
  rw [hsafe]
  have hline := pureWZ2LineClassNormalization_projection_pointwise
    commonSource.halfOffsetAssembly.exactGlobalSlope terminal.box.center
      (rawPoint : Point3) pureWZ2DirectHalfOffsetTerminalLambda_pos
      ((exactPoint : Point3) 2) (by
        have hmapEq :
            pureWZ2LineClassNormalizationMap terminal.box.center
                pureWZ2DirectHalfOffsetTerminalLambda (rawPoint : Point3) =
              (exactPoint : Point3) := by
          exact commonSource.halfOffsetTerminal_map_rawPoint terminal.retubing
            terminal.box pureWZ2DirectHalfOffsetTerminalLambda_pos
              (exactSetPoint commonSource terminal exactPoint)
        exact congrArg (fun point : Point3 => point 2) hmapEq)
  rw [show pureWZ2LineClassNormalizationMap terminal.box.center
      pureWZ2DirectHalfOffsetTerminalLambda (rawPoint : Point3) =
        (exactPoint : Point3) by
      exact commonSource.halfOffsetTerminal_map_rawPoint terminal.retubing
        terminal.box pureWZ2DirectHalfOffsetTerminalLambda_pos
          (exactSetPoint commonSource terminal exactPoint)] at hline
  have hsourceMap : anisotropicCenteredRescalingMap
      (pureWZ2DirectGeometrySlope source) source.c source.d source.m
      (pureWZ2DirectAnisotropicCenter terminal.retubing.popular)
      (sourcePoint : Point3) = (rawPoint : Point3) := by
    change anisotropicCenteredRescalingMap
      (pureWZ2DirectGeometrySlope source) source.c source.d source.m
      (pureWZ2DirectAnisotropicCenter terminal.retubing.popular)
      (terminal.retubing.raw.exactSourcePoint rawPoint) = rawPoint
    exact terminal.retubing.raw.map_exactSourcePoint rawPoint
  have hsourceHeight : (sourcePoint : Point3) 2 =
      source.c + (source.d - source.c) / 2 *
        ((rawPoint : Point3) 2 + 1) := by
    have hcoord := congrArg (fun point : Point3 => point 2) hsourceMap
    simp only [anisotropicCenteredRescalingMap, anisotropicRescalingMap,
      point3_coord2, PiLp.sub_apply] at hcoord
    have hlength : source.d - source.c ≠ 0 :=
      sub_ne_zero.mpr source.ordered.ne'
    field_simp [hlength] at hcoord ⊢
    linarith
  have hanisotropic := anisotropic_projection_pointwise_withShear
    (c := source.c) (d := source.d) (m := source.m)
    (pureWZ2DirectGeometrySlope source)
    commonSource.halfOffsetAssembly.globalSlope source.ordered
    source.slopeScale_pos ((rawPoint : Point3) 2) (sourcePoint : Point3)
    hsourceHeight
  have hslopeFormula :
      anisotropicRescaledSlopeWithShear
          commonSource.halfOffsetAssembly.globalSlope source.c source.d source.m
          ((pureWZ2DirectGeometrySlope source)
            (source.c + (source.d - source.c) / 2))
          ((rawPoint : Point3) 2) =
        commonSource.halfOffsetAssembly.exactGlobalSlope
          ((rawPoint : Point3) 2) := by
    simpa [source, pureWZ2DirectGeometrySlope] using
      (commonSource.halfOffsetAssembly.exactGlobalSlope_formula
        ((rawPoint : Point3) 2)).symm
  rw [hslopeFormula] at hanisotropic
  have hcentered :
      inner ℝ (rawPoint : Point3)
          (globalGrainDirection
            (commonSource.halfOffsetAssembly.exactGlobalSlope
              ((rawPoint : Point3) 2))) =
        inner ℝ (sourcePoint : Point3)
            (globalGrainDirection
              (commonSource.halfOffsetAssembly.globalSlope
                ((sourcePoint : Point3) 2))) -
          anisotropicRescalingMap (pureWZ2DirectGeometrySlope source)
            source.c source.d source.m
            (pureWZ2DirectAnisotropicCenter terminal.retubing.popular) 0 := by
    let mapped := anisotropicRescalingMap (pureWZ2DirectGeometrySlope source)
      source.c source.d source.m (sourcePoint : Point3)
    let shift := (anisotropicRescalingMap (pureWZ2DirectGeometrySlope source)
      source.c source.d source.m
      (pureWZ2DirectAnisotropicCenter terminal.retubing.popular)) 0
    have hrawPoint : (rawPoint : Point3) = mapped - point3 shift 0 0 := by
      exact hsourceMap.symm
    have hmappedHeight : mapped 2 = (rawPoint : Point3) 2 := by
      rw [hrawPoint]
      simp [mapped, shift, point3]
    have hshiftedHeight : (mapped - point3 shift 0 0) 2 = mapped 2 := by
      simp [point3]
    rw [hrawPoint, hshiftedHeight]
    calc
      inner ℝ (mapped - point3 shift 0 0)
          (globalGrainDirection
            (commonSource.halfOffsetAssembly.exactGlobalSlope (mapped 2))) =
        inner ℝ mapped
            (globalGrainDirection
              (commonSource.halfOffsetAssembly.exactGlobalSlope (mapped 2))) -
          shift := by
            simp [globalGrainDirection, PiLp.inner_apply,
              Fin.sum_univ_succ, point3]
            ring
      _ = inner ℝ (sourcePoint : Point3)
            (globalGrainDirection
              (commonSource.halfOffsetAssembly.globalSlope
                ((sourcePoint : Point3) 2))) - shift := by
          rw [show mapped = anisotropicRescalingMap
              (pureWZ2DirectGeometrySlope source) source.c source.d source.m
              (sourcePoint : Point3) by rfl, hmappedHeight, hanisotropic]
  rw [hcentered] at hline
  have hcenterProjection :
      inner ℝ terminal.box.center
          (globalGrainDirection
            (commonSource.halfOffsetAssembly.exactGlobalSlope
              ((rawPoint : Point3) 2))) = terminal.box.center 0 := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ,
      terminal.box.center_y]
  rw [hcenterProjection] at hline
  dsimp only [sourcePoint]
  dsimp only [finiteSliceProjectionOffset]
  dsimp only [source] at hline ⊢
  linarith


/-- A normalized public slope is two-Lipschitz on the paper interval. -/
theorem safePublicSlope_lipschitzOn
    (terminal : commonSource.TerminalGeometry) :
    LipschitzOnWith 2 (safePublicSlope commonSource terminal)
      (Set.Icc (-1 : ℝ) 1) := by
  have hdiff : Differentiable ℝ (safePublicSlope commonSource terminal) :=
    (safePublicSlope commonSource terminal).contDiff.differentiable (by norm_num)
  apply (convex_Icc (-1 : ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
  · intro z _hz
    exact hdiff.differentiableAt
  · intro z hz
    apply NNReal.coe_le_coe.mp
    simpa [Real.norm_eq_abs] using
      (safePublicSlope_nonsingular commonSource terminal z hz).2.1

/-- A finite public-slope bound which has no inverse target-scale factor. -/
def finiteSlicePublicSlopeBound (terminal : commonSource.TerminalGeometry) : ℝ :=
  |safePublicSlope commonSource terminal 0| + 2

theorem safePublicSlope_abs_le_finiteSlicePublicSlopeBound
    (terminal : commonSource.TerminalGeometry)
    {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    |safePublicSlope commonSource terminal z| ≤
      finiteSlicePublicSlopeBound commonSource terminal := by
  have hlip := (safePublicSlope_lipschitzOn commonSource terminal).dist_le_mul
    z hz 0 (by norm_num)
  have hdifference :
      |safePublicSlope commonSource terminal z -
          safePublicSlope commonSource terminal 0| ≤ 2 := by
    calc
      _ ≤ 2 * |z| := by simpa [Real.dist_eq] using hlip
      _ ≤ 2 := by
        have hzAbs : |z| ≤ 1 := abs_le.mpr hz
        nlinarith
  unfold finiteSlicePublicSlopeBound
  calc
    |safePublicSlope commonSource terminal z| ≤
        |safePublicSlope commonSource terminal 0| +
          |safePublicSlope commonSource terminal z -
            safePublicSlope commonSource terminal 0| := by
      have h := abs_add_le
        (safePublicSlope commonSource terminal 0)
        (safePublicSlope commonSource terminal z -
          safePublicSlope commonSource terminal 0)
      simpa [add_sub_cancel] using h
    _ ≤ _ := add_le_add_right hdifference
      |safePublicSlope commonSource terminal 0|

theorem finiteSlicePublicSlopeBound_nonneg
    (terminal : commonSource.TerminalGeometry) :
    0 ≤ finiteSlicePublicSlopeBound commonSource terminal := by
  unfold finiteSlicePublicSlopeBound
  positivity

/-- Explicit source-power envelope for the safe public slope. -/
def finiteSliceAbsorbableSlopeBound : ℝ :=
  pureWZ2DirectHalfOffsetTerminalLambda *
    (2 + 400 * commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2) + 2

/-- The same bound is quantitatively absorbable by a fixed negative power of
the original source scale.  No inverse terminal radius occurs here. -/
theorem finiteSlicePublicSlopeBound_le_sourcePower
    (terminal : commonSource.TerminalGeometry) :
    finiteSlicePublicSlopeBound commonSource terminal ≤
      finiteSliceAbsorbableSlopeBound commonSource := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  have hcenter : terminal.box.center 2 ∈ Set.Icc (-1 : ℝ) 1 :=
    box_center_height_mem commonSource terminal
  have hinverse : terminal.box.center 2 +
      0 / pureWZ2DirectHalfOffsetTerminalLambda ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa using hcenter
  rw [finiteSlicePublicSlopeBound,
    safePublicSlope_eq_transport commonSource terminal 0 hinverse]
  rw [abs_mul, abs_of_pos pureWZ2DirectHalfOffsetTerminalLambda_pos]
  rw [show terminal.box.center 2 +
      0 / pureWZ2DirectHalfOffsetTerminalLambda = terminal.box.center 2 by ring]
  have hinner :
      |anisotropicRescaledSlopeWithShear
          commonSource.commonBand.band.lemma31.data.globalSlope
          commonSource.subband.left commonSource.subband.right
          ((9 : ℝ) / 10 * commonSource.commonBand.band.slopeScale)
          (safeHalfOffsetFrameSlope commonSource) (terminal.box.center 2)| ≤
        2 + 400 * commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2 := by
    unfold anisotropicRescaledSlopeWithShear
    let sourceHeight := pureWZ2CoupledSourceHeight commonSource.subband
      (terminal.box.center 2)
    have hsourceSubband : sourceHeight ∈
        Set.Icc commonSource.subband.left commonSource.subband.right :=
      pureWZ2CoupledSourceHeight_mem commonSource.subband hcenter
    have hsourceBand : sourceHeight ∈
        Set.Icc commonSource.commonBand.band.left
          commonSource.commonBand.band.right :=
      ⟨commonSource.subband.left_mem.trans hsourceSubband.1,
        hsourceSubband.2.trans commonSource.subband.right_mem⟩
    have hvalue :=
      commonSource.commonBand.band.lemma31.data.globalSlope_normalized
        sourceHeight
        ⟨commonSource.commonBand.band.lemma31.data.scaleData.slabLeft_mem.trans
            (commonSource.commonBand.band.left_mem.trans hsourceBand.1),
          hsourceBand.2.trans
            (commonSource.commonBand.band.right_mem.trans
              commonSource.commonBand.band.lemma31.data.scaleData.slabRight_mem)⟩
        |>.1
    have hoffset : |safeHalfOffsetFrameSlope commonSource| ≤ 1 / 2 := by
      simpa [safeHalfOffsetFrameSlope] using
        (PureWZ2HalfOffsetHorizontalSourceData.offset_abs_le
          commonSource.halfOffsetAssembly_compatibility)
    have hdenom : 0 <
        ((9 : ℝ) / 10 * commonSource.commonBand.band.slopeScale) *
          (commonSource.subband.right - commonSource.subband.left) / 2 := by
      positivity [commonSource.commonBand.band.slopeScale_pos,
        sub_pos.mpr commonSource.subband.ordered]
    have hnumerator :
        |commonSource.commonBand.band.lemma31.data.globalSlope
              sourceHeight -
            safeHalfOffsetFrameSlope commonSource| ≤ 3 / 2 := by
      calc
        _ ≤ |commonSource.commonBand.band.lemma31.data.globalSlope
                sourceHeight| +
              |safeHalfOffsetFrameSlope commonSource| := abs_sub _ _
        _ ≤ 1 + 1 / 2 := add_le_add hvalue hoffset
        _ = 3 / 2 := by norm_num
    have hlength : commonSource.subband.right - commonSource.subband.left =
        commonSource.halfOffsetAssembly.rho.1 / 100 := by
      calc
        commonSource.subband.right - commonSource.subband.left =
            commonSource.halfOffsetAssembly.horizontalSource.d -
              commonSource.halfOffsetAssembly.horizontalSource.c := by
          rw [commonSource.halfOffsetAssembly_source_coordinates.1,
            commonSource.halfOffsetAssembly_source_coordinates.2.1]
        _ = commonSource.halfOffsetAssembly.horizontalSource.source_length /
              100 :=
          commonSource.halfOffsetAssembly.horizontalSource.length_eq
        _ = commonSource.halfOffsetAssembly.rho.1 / 100 := by
          rw [commonSource.halfOffsetAssembly.horizontalSource_scale]
    have hrho : 0 < commonSource.halfOffsetAssembly.rho.1 :=
      commonSource.halfOffsetAssembly.cfg.extremal.delta_pos.trans_le
        commonSource.halfOffsetAssembly.rho.2.1
    change |commonSource.commonBand.band.lemma31.data.globalSlope sourceHeight / _ -
      safeHalfOffsetFrameSlope commonSource / _| ≤ _
    rw [← sub_div, abs_div, abs_of_pos hdenom]
    apply (div_le_iff₀ hdenom).2
    rw [hlength]
    have hslope : 0 < commonSource.commonBand.band.slopeScale :=
      commonSource.commonBand.band.slopeScale_pos
    have hslopeLower : commonSource.halfOffsetAssembly.rho.1 ≤
        commonSource.commonBand.band.slopeScale := by
      calc
        commonSource.halfOffsetAssembly.rho.1 =
            commonSource.halfOffsetAssembly.horizontalSource.source_length :=
          commonSource.halfOffsetAssembly.horizontalSource_scale.symm
        _ ≤ commonSource.halfOffsetAssembly.horizontalSource.m :=
          commonSource.halfOffsetAssembly.horizontalSource.slopeScale_lower
        _ = (9 : ℝ) / 10 * commonSource.commonBand.band.slopeScale :=
          commonSource.halfOffsetAssembly_source_coordinates.2.2
        _ ≤ commonSource.commonBand.band.slopeScale := by
          nlinarith [commonSource.commonBand.band.slopeScale_pos]
    calc
      |commonSource.commonBand.band.lemma31.data.globalSlope
            sourceHeight -
          safeHalfOffsetFrameSlope commonSource| ≤ 3 / 2 := hnumerator
      _ ≤ (2 + 400 * commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2) *
          (((9 : ℝ) / 10 * commonSource.commonBand.band.slopeScale) *
            (commonSource.halfOffsetAssembly.rho.1 / 100) / 2) := by
        have hfactor : 0 < ((9 : ℝ) / 10 *
            commonSource.commonBand.band.slopeScale) *
              (commonSource.halfOffsetAssembly.rho.1 / 100) / 2 := by positivity
        have hsmall : commonSource.halfOffsetAssembly.rho.1 ≤ 1 / 6400 :=
          commonSource.halfOffsetAssembly.rho_tiny
        have hslopeRho := mul_le_mul hslopeLower le_rfl hrho.le hslope.le
        field_simp [hrho.ne']
        nlinarith [hslopeRho]
  simpa [finiteSliceAbsorbableSlopeBound, add_comm] using add_le_add_right
    (mul_le_mul_of_nonneg_left hinner
      pureWZ2DirectHalfOffsetTerminalLambda_pos.le) 2

/-- Membership in a centered integer-cell window from a scale-normalized
height estimate. -/
theorem heightCell_mem_finiteSliceHeightCells
    (terminal : commonSource.TerminalGeometry) (z height : ℝ)
    (hdelta : 0 < delta)
    (hclose :
      |height -
        (commonSource.halfOffsetAssembly.horizontalSource.c +
          (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c) / 2 *
            (terminal.box.center 2 +
              z / pureWZ2DirectHalfOffsetTerminalLambda + 1))| ≤
        (finiteSliceHeightCellRadius : ℝ) * delta) :
    Int.floor (height / delta) ∈
      finiteSliceHeightCells commonSource terminal z := by
  let center := commonSource.halfOffsetAssembly.horizontalSource.c +
    (commonSource.halfOffsetAssembly.horizontalSource.d -
      commonSource.halfOffsetAssembly.horizontalSource.c) / 2 *
      (terminal.box.center 2 +
        z / pureWZ2DirectHalfOffsetTerminalLambda + 1)
  let radius : ℤ := finiteSliceHeightCellRadius
  have hquotient : |height / delta - center / delta| ≤
      (finiteSliceHeightCellRadius : ℝ) := by
    rw [show height / delta - center / delta =
      (height - center) / delta by ring, abs_div, abs_of_pos hdelta]
    exact (div_le_iff₀ hdelta).2 hclose
  unfold finiteSliceHeightCells
  rw [Finset.mem_Icc]
  have hlowerReal : center / delta - finiteSliceHeightCellRadius ≤
      height / delta := by linarith [(abs_le.mp hquotient).1]
  have hupperReal : height / delta ≤
      center / delta + finiteSliceHeightCellRadius := by
    linarith [(abs_le.mp hquotient).2]
  constructor
  · simpa [center, radius] using Int.floor_le_floor hlowerReal
  · simpa [center, radius] using Int.floor_le_floor hupperReal

/-- Moving an ambient cubical source point to the lower face of its original
`delta`-cell changes the source projection by at most one source scale. -/
theorem source_lower_projection_dist_le
    {point : Point3}
    (hpoint : point ∈ commonSource.halfOffsetAssembly.cfg.shading.union) :
    let height := pureWZ2PaperCellLowerHeight delta point
    let lower := pureWZ2ReplaceHeight point height
    dist
        (inner ℝ point
          (globalGrainDirection
            (commonSource.halfOffsetAssembly.globalSlope (point 2))))
        (inner ℝ lower
          (globalGrainDirection
            (commonSource.halfOffsetAssembly.globalSlope height))) ≤ delta := by
  let height := pureWZ2PaperCellLowerHeight delta point
  let lower := pureWZ2ReplaceHeight point height
  have hdelta : 0 < delta :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  rcases hpoint with ⟨index, hpointCarrier⟩
  have hlowerCarrier : lower ∈
      commonSource.halfOffsetAssembly.cfg.shading.carrier index := by
    exact commonSource.halfOffsetAssembly_cfg_cubical.replaceHeight_lower_mem
      hdelta hpointCarrier
  have hpointBox :=
    commonSource.halfOffsetAssembly.cfg.shading.subset_body index hpointCarrier
  have hlowerBox :=
    commonSource.halfOffsetAssembly.cfg.shading.subset_body index hlowerCarrier
  have hpointHeight : point 2 ∈ Set.Icc (-1 : ℝ) 1 :=
    abs_le.mp <| by
      simpa [Kakeya.Streamlined.axisBox] using hpointBox.2.2.2
  have hlowerHeight : height ∈ Set.Icc (-1 : ℝ) 1 :=
    abs_le.mp <| by
      simpa [lower, Kakeya.Streamlined.axisBox] using hlowerBox.2.2.2
  have hslope :=
    (SlopeFunction.lipschitzOn_unit_of_normalized
      commonSource.halfOffsetAssembly.globalSlope
      commonSource.halfOffsetAssembly.globalSlope_normalized).dist_le_mul
        (point 2) hpointHeight height hlowerHeight
  have hslopeClose :
      |commonSource.halfOffsetAssembly.globalSlope (point 2) -
        commonSource.halfOffsetAssembly.globalSlope height| ≤ delta := by
    calc
      _ ≤ |point 2 - height| := by
        simpa [Real.dist_eq] using hslope
      _ ≤ delta := pureWZ2PaperCellLowerHeight_close hdelta point
  have hpointY : |point 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpointBox.2.2.1
  dsimp only [height, lower]
  rw [Real.dist_eq]
  have hidentity :
      inner ℝ point
            (globalGrainDirection
              (commonSource.halfOffsetAssembly.globalSlope (point 2))) -
          inner ℝ lower
            (globalGrainDirection
              (commonSource.halfOffsetAssembly.globalSlope height)) =
        (commonSource.halfOffsetAssembly.globalSlope (point 2) -
          commonSource.halfOffsetAssembly.globalSlope height) * point 1 := by
    simp [lower, pureWZ2ReplaceHeight, globalGrainDirection,
      PiLp.inner_apply, Fin.sum_univ_succ, point3]
    ring
  rw [hidentity, abs_mul]
  calc
    _ ≤ delta * 1 := mul_le_mul hslopeClose hpointY (abs_nonneg _) hdelta.le
    _ = delta := mul_one delta

/-- Source-scale cubical transport for the actual direct half-offset terminal.
The only multiplicity loss is the fixed finite height window, and the
thickening radius is `targetDelta` times a finite slope factor. -/
theorem cubicalShading_global_ad_finiteSlice
    (terminal : commonSource.TerminalGeometry)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (safePublicSlope commonSource terminal z))
          (horizontalSlice terminal.cubicalShading.union z))
        terminal.targetDelta (1 - sigma)
        ((2 * (Nat.ceil
            (((finiteSliceAbsorbableSlopeBound commonSource + 3) *
                Real.sqrt 3) + 1) + 1) : ENNReal) ^ 3 *
          (((2 * finiteSliceHeightCellRadius + 1 : ℕ) : ENNReal) *
            Kakeya.realRpowENN delta
              (-commonSource.halfOffsetAssembly.technicalLoss))) := by
  have hdelta : 0 < delta :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hlambda : 0 < pureWZ2DirectHalfOffsetTerminalLambda :=
    pureWZ2DirectHalfOffsetTerminalLambda_pos
  have hsourceLipschitz :=
    SlopeFunction.lipschitzOn_unit_of_normalized
      commonSource.halfOffsetAssembly.globalSlope
      commonSource.halfOffsetAssembly.globalSlope_normalized
  have hsourceAD : ∀ height : ℝ,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (commonSource.halfOffsetAssembly.globalSlope height))
          (horizontalSlice
            commonSource.halfOffsetAssembly.cfg.shading.union height))
        delta (1 - sigma)
        (Kakeya.realRpowENN delta
          (-commonSource.halfOffsetAssembly.technicalLoss)) := by
    intro height
    by_cases hheight : height ∈ Set.Icc (-1 : ℝ) 1
    · have h := commonSource.halfOffsetAssembly.cfg.globalGrains.global_ad_slope
        height hheight
      rw [← commonSource.halfOffsetAssembly.globalSlope_eq_source height hheight] at h
      exact h
    · rw [commonSource.halfOffsetAssembly.cfg.shading.horizontalSlice_empty_of_not_mem_unit
        hheight]
      simp only [scalarProjection, Set.image_empty]
      have hseed := commonSource.halfOffsetAssembly.cfg.globalGrains.global_ad_slope
        0 (by norm_num)
      refine ⟨hseed.1, by linarith, by linarith, hseed.2.2.2.1,
        hseed.2.2.2.2.1, ?_⟩
      intro rho hrho _hrhoLower left length _hlength
      simp
  have hbase : pureWZ2DirectHalfOffsetTerminalLambda * delta ≤
      terminal.targetDelta := by
    have hdeltaPre :=
      commonSource.halfOffsetAssembly.delta_le_directPreHorizontalScale
    have hraw :=
      commonSource.halfOffsetAssembly.directHorizontalRawTargetScale_le_target
    have hlambdaScale := pureWZ2DirectHalfOffsetTerminalLambda_le_horizontalScale
    have hdeltaNonneg := hdelta.le
    have hpreNonneg :=
      commonSource.halfOffsetAssembly.directPreHorizontalScale_pos.le
    calc
      pureWZ2DirectHalfOffsetTerminalLambda * delta ≤
          pureWZ2DirectHorizontalScale *
            commonSource.halfOffsetAssembly.directPreHorizontalScale := by
        exact mul_le_mul hlambdaScale hdeltaPre hdeltaNonneg
          pureWZ2DirectHorizontalScale_pos.le
      _ ≤ 4 * pureWZ2DirectHorizontalScale *
          commonSource.halfOffsetAssembly.directPreHorizontalScale := by
        nlinarith [mul_nonneg pureWZ2DirectHorizontalScale_pos.le hpreNonneg]
      _ ≤ terminal.targetDelta := by
        simpa [pureWZ2DirectHorizontalRawTargetScale] using hraw
  intro z hz
  let heightCells := finiteSliceHeightCells commonSource terminal z
  let offset : ℤ → ℝ := fun _ =>
    finiteSliceProjectionOffset commonSource terminal
  let D := terminal.targetDelta *
    (((finiteSliceAbsorbableSlopeBound commonSource + 3) *
      Real.sqrt 3) + 1)
  have hheightCells : heightCells.Nonempty := by
    exact finiteSliceHeightCells_nonempty commonSource terminal z
  have hraw := commonSource.halfOffsetAssembly_cfg_cubical
    |>.targetProjection_ad_of_source_witness_indexed_all
      hdelta commonSource.halfOffsetLineClassTargetDelta_pos
      commonSource.halfOffsetAssembly.globalSlope heightCells hheightCells
      hsourceAD (a := pureWZ2DirectHalfOffsetTerminalLambda)
      (offset := offset)
      (target := scalarProjection
        (globalGrainDirection (safePublicSlope commonSource terminal z))
        (horizontalSlice terminal.cubicalShading.union z))
      (D := D) hlambda hbase (by
        rintro value ⟨point, ⟨hpoint, hpointHeight⟩, rfl⟩
        let targetPoint : {point : Point3 // point ∈
            terminal.cubicalShading.union} := ⟨point, hpoint⟩
        rcases commonSource.halfOffsetLineClassActualCubicalShading_targetWitness
            terminal.retubing terminal.box targetPoint with
          ⟨exactSet, hexactDistance⟩
        let exactPoint : {point : Point3 // point ∈
            terminal.exactShading.union} :=
          ⟨exactSet, by rw [terminal.exact_union]; exact exactSet.property⟩
        let sourcePoint :=
          commonSource.halfOffsetTerminalSourcePoint terminal.retubing terminal.box
            pureWZ2DirectHalfOffsetTerminalLambda_pos exactSet
        rcases sourcePoint.property with ⟨sourceIndex, hsourceCarrier⟩
        have hsourceAmbient : (sourcePoint : Point3) ∈
            commonSource.halfOffsetAssembly.cfg.shading.union :=
          ⟨sourceIndex, commonSource.halfOffsetAssembly_source_subconfiguration
            sourceIndex hsourceCarrier⟩
        let height := pureWZ2PaperCellLowerHeight delta (sourcePoint : Point3)
        let lowerSource := pureWZ2ReplaceHeight (sourcePoint : Point3) height
        have hsourceHeight : (sourcePoint : Point3) 2 ∈ Set.Icc (-1 : ℝ) 1 := by
          have hbox := commonSource.halfOffsetAssembly.cfg.shading.subset_body
            sourceIndex
            (commonSource.halfOffsetAssembly_source_subconfiguration
              sourceIndex hsourceCarrier)
          exact abs_le.mp <| by
            simpa [Kakeya.Streamlined.axisBox] using hbox.2.2.2
        have hlowerAmbient : lowerSource ∈
            commonSource.halfOffsetAssembly.cfg.shading.union :=
          ⟨sourceIndex,
            commonSource.halfOffsetAssembly_cfg_cubical.replaceHeight_lower_mem
              hdelta
              (commonSource.halfOffsetAssembly_source_subconfiguration
                sourceIndex hsourceCarrier)⟩
        have hexactHeight : (exactPoint : Point3) 2 ∈ Set.Icc (-1 : ℝ) 1 := by
          rcases exactPoint.property with ⟨index, hcarrier⟩
          have hbox := terminal.exactShading.subset_body index hcarrier
          exact abs_le.mp <| by
            simpa [Kakeya.Streamlined.axisBox] using hbox.2.2.2
        have hexactHeightDistance :
            |(exactPoint : Point3) 2 - z| ≤
              terminal.targetDelta * Real.sqrt 3 := by
          have hcoordinate :=
            (PiLp.norm_apply_le (point - (exactPoint : Point3))
              (2 : Fin 3)).trans <| by
                simpa [dist_eq_norm] using hexactDistance
          simpa [PiLp.sub_apply, hpointHeight, abs_sub_comm] using hcoordinate
        let sourceCenter :=
          commonSource.halfOffsetAssembly.horizontalSource.c +
            (commonSource.halfOffsetAssembly.horizontalSource.d -
              commonSource.halfOffsetAssembly.horizontalSource.c) / 2 *
              (terminal.box.center 2 +
                z / pureWZ2DirectHalfOffsetTerminalLambda + 1)
        have hsourceFormula : (sourcePoint : Point3) 2 =
            commonSource.halfOffsetAssembly.horizontalSource.c +
              (commonSource.halfOffsetAssembly.horizontalSource.d -
                commonSource.halfOffsetAssembly.horizontalSource.c) / 2 *
                (terminal.box.center 2 +
                  (exactPoint : Point3) 2 /
                    pureWZ2DirectHalfOffsetTerminalLambda + 1) := by
          have hmap := totalAffineMap_halfOffsetTerminalSourcePoint
            commonSource terminal exactPoint
          have hcoord := congrArg (fun q : Point3 => q 2) hmap
          rw [totalAffineMap_coord_two commonSource terminal] at hcoord
          have hlength : 0 <
              commonSource.halfOffsetAssembly.horizontalSource.d -
                commonSource.halfOffsetAssembly.horizontalSource.c :=
            sub_pos.mpr commonSource.halfOffsetAssembly.horizontalSource.ordered
          have hlambdaNe := pureWZ2DirectHalfOffsetTerminalLambda_pos.ne'
          have hexactSetEq : exactSetPoint commonSource terminal exactPoint =
              exactSet := Subtype.ext rfl
          rw [hexactSetEq] at hcoord
          dsimp only [sourcePoint] at hcoord ⊢
          field_simp [hlength.ne', hlambdaNe] at hcoord ⊢
          linear_combination hcoord
        have htargetPre : terminal.targetDelta <
            8 * pureWZ2DirectHorizontalScale *
              commonSource.halfOffsetAssembly.directPreHorizontalScale := by
          change commonSource.halfOffsetLineClassTargetDelta < _
          exact (pureWZ2DirectHorizontalTargetScale_lt_two_mul_raw
              commonSource.halfOffsetAssembly.directHorizontalRawTargetScale_pos
              commonSource.halfOffsetAssembly.directHorizontalRawTargetScale_half)
            |>.trans_eq (by
              unfold pureWZ2DirectHorizontalRawTargetScale
              ring)
        have hpreLength :
            commonSource.halfOffsetAssembly.directPreHorizontalScale <
              32 * delta /
                (commonSource.halfOffsetAssembly.horizontalSource.d -
                  commonSource.halfOffsetAssembly.horizontalSource.c) := by
          have h :=
            commonSource.halfOffsetAssembly.directPreHorizontalScale_upper
          rw [commonSource.halfOffsetAssembly.horizontalSource.length_eq,
            commonSource.halfOffsetAssembly.horizontalSource_scale]
          have hrho : 0 < commonSource.halfOffsetAssembly.rho.1 :=
            commonSource.halfOffsetAssembly.cfg.extremal.delta_pos.trans_le
              commonSource.halfOffsetAssembly.rho.2.1
          convert h using 1
          field_simp [hrho.ne']
          ring
        have hsourceCenterClose :
            |(sourcePoint : Point3) 2 - sourceCenter| ≤
              (finiteSliceHeightCellRadius : ℝ) * delta := by
          have hlength : 0 <
              commonSource.halfOffsetAssembly.horizontalSource.d -
                commonSource.halfOffsetAssembly.horizontalSource.c :=
            sub_pos.mpr commonSource.halfOffsetAssembly.horizontalSource.ordered
          have htargetBound : terminal.targetDelta ≤
              256 * pureWZ2DirectHorizontalScale * delta /
                (commonSource.halfOffsetAssembly.horizontalSource.d -
                  commonSource.halfOffsetAssembly.horizontalSource.c) := by
            calc
              terminal.targetDelta ≤ 8 * pureWZ2DirectHorizontalScale *
                  commonSource.halfOffsetAssembly.directPreHorizontalScale :=
                htargetPre.le
              _ ≤ 8 * pureWZ2DirectHorizontalScale *
                  (32 * delta /
                    (commonSource.halfOffsetAssembly.horizontalSource.d -
                      commonSource.halfOffsetAssembly.horizontalSource.c)) := by
                exact mul_le_mul_of_nonneg_left hpreLength.le
                  (mul_nonneg (by norm_num)
                    pureWZ2DirectHorizontalScale_pos.le)
              _ = _ := by ring
          rw [hsourceFormula]
          dsimp only [sourceCenter]
          rw [show
              (commonSource.halfOffsetAssembly.horizontalSource.c +
                  (commonSource.halfOffsetAssembly.horizontalSource.d -
                    commonSource.halfOffsetAssembly.horizontalSource.c) / 2 *
                    (terminal.box.center 2 +
                      (exactPoint : Point3) 2 /
                        pureWZ2DirectHalfOffsetTerminalLambda + 1)) -
                (commonSource.halfOffsetAssembly.horizontalSource.c +
                  (commonSource.halfOffsetAssembly.horizontalSource.d -
                    commonSource.halfOffsetAssembly.horizontalSource.c) / 2 *
                    (terminal.box.center 2 +
                      z / pureWZ2DirectHalfOffsetTerminalLambda + 1)) =
                ((commonSource.halfOffsetAssembly.horizontalSource.d -
                  commonSource.halfOffsetAssembly.horizontalSource.c) /
                    (2 * pureWZ2DirectHalfOffsetTerminalLambda)) *
                  ((exactPoint : Point3) 2 - z) by
              field_simp [hlambda.ne']; ring]
          rw [abs_mul, abs_of_pos (div_pos hlength
            (mul_pos (by norm_num) hlambda))]
          have hceil : 128 * pureWZ2DirectHorizontalScale * Real.sqrt 3 ≤
              (finiteSliceHeightCellRadius : ℝ) := by
            unfold finiteSliceHeightCellRadius
            have h := Nat.le_ceil
              (128 * pureWZ2DirectHorizontalScale * Real.sqrt 3)
            exact h.trans (by norm_num)
          calc
            _ ≤ ((commonSource.halfOffsetAssembly.horizontalSource.d -
                  commonSource.halfOffsetAssembly.horizontalSource.c) /
                    (2 * pureWZ2DirectHalfOffsetTerminalLambda)) *
                (terminal.targetDelta * Real.sqrt 3) := by gcongr
            _ ≤ 128 * pureWZ2DirectHorizontalScale * delta * Real.sqrt 3 := by
              calc
                  (commonSource.halfOffsetAssembly.horizontalSource.d -
                      commonSource.halfOffsetAssembly.horizontalSource.c) /
                        (2 * pureWZ2DirectHalfOffsetTerminalLambda) *
                      (terminal.targetDelta * Real.sqrt 3) =
                    ((commonSource.halfOffsetAssembly.horizontalSource.d -
                      commonSource.halfOffsetAssembly.horizontalSource.c) /
                        (2 * pureWZ2DirectHalfOffsetTerminalLambda) *
                      terminal.targetDelta) * Real.sqrt 3 := by ring
                _ ≤ (128 * pureWZ2DirectHorizontalScale * delta) *
                      Real.sqrt 3 := by
                  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg 3)
                  calc
                    (commonSource.halfOffsetAssembly.horizontalSource.d -
                        commonSource.halfOffsetAssembly.horizontalSource.c) /
                          (2 * pureWZ2DirectHalfOffsetTerminalLambda) *
                        terminal.targetDelta ≤
                      (commonSource.halfOffsetAssembly.horizontalSource.d -
                        commonSource.halfOffsetAssembly.horizontalSource.c) /
                          (2 * pureWZ2DirectHalfOffsetTerminalLambda) *
                        (256 * pureWZ2DirectHorizontalScale * delta /
                          (commonSource.halfOffsetAssembly.horizontalSource.d -
                            commonSource.halfOffsetAssembly.horizontalSource.c)) := by
                      exact mul_le_mul_of_nonneg_left htargetBound
                        (div_pos hlength (mul_pos (by norm_num) hlambda)).le
                    _ ≤ 128 * pureWZ2DirectHorizontalScale * delta := by
                      field_simp [hlength.ne']
                      have hlambdaOne :=
                        pureWZ2DirectHalfOffsetTerminalLambda_one_le
                      nlinarith [pureWZ2DirectHorizontalScale_pos, hdelta]
                _ = _ := by ring
            _ ≤ (finiteSliceHeightCellRadius : ℝ) * delta := by
              rw [show 128 * pureWZ2DirectHorizontalScale * delta *
                  Real.sqrt 3 =
                (128 * pureWZ2DirectHorizontalScale * Real.sqrt 3) * delta
                by ring]
              exact mul_le_mul_of_nonneg_right hceil hdelta.le
        have hcell : Int.floor ((sourcePoint : Point3) 2 / delta) ∈
            heightCells := by
          exact heightCell_mem_finiteSliceHeightCells commonSource terminal z
            ((sourcePoint : Point3) 2) hdelta hsourceCenterClose
        refine ⟨(sourcePoint : Point3), hsourceAmbient, hcell, ?_⟩
        have htargetSlope :
            |safePublicSlope commonSource terminal z| ≤
              finiteSliceAbsorbableSlopeBound commonSource :=
          (safePublicSlope_abs_le_finiteSlicePublicSlopeBound
            commonSource terminal hz).trans
              (finiteSlicePublicSlopeBound_le_sourcePower commonSource terminal)
        have hslopeError :
            |safePublicSlope commonSource terminal z -
              safePublicSlope commonSource terminal ((exactPoint : Point3) 2)| ≤
                2 * (terminal.targetDelta * Real.sqrt 3) := by
          have hlip := (safePublicSlope_lipschitzOn commonSource terminal)
            |>.dist_le_mul z hz ((exactPoint : Point3) 2) hexactHeight
          calc
            _ ≤ 2 * |z - (exactPoint : Point3) 2| := by
              simpa [Real.dist_eq] using hlip
            _ ≤ 2 * (terminal.targetDelta * Real.sqrt 3) := by
              gcongr
              simpa [abs_sub_comm] using hexactHeightDistance
        have hexactY : |(exactPoint : Point3) 1| ≤ 1 := by
          rcases exactPoint.property with ⟨index, hcarrier⟩
          have hbox := terminal.exactShading.subset_body index hcarrier
          simpa [Kakeya.Streamlined.axisBox] using hbox.2.2.1
        have htargetExact := pureWZ2_globalProjection_dist_le_of_point_slope_error
          point (exactPoint : Point3)
          (safePublicSlope commonSource terminal z)
          (safePublicSlope commonSource terminal ((exactPoint : Point3) 2))
          (terminal.targetDelta * Real.sqrt 3)
          (2 * (terminal.targetDelta * Real.sqrt 3))
          (finiteSliceAbsorbableSlopeBound commonSource) 1
          (mul_nonneg commonSource.halfOffsetLineClassTargetDelta_pos.le
            (Real.sqrt_nonneg 3))
          (mul_nonneg (by norm_num)
            (mul_nonneg commonSource.halfOffsetLineClassTargetDelta_pos.le
              (Real.sqrt_nonneg 3)))
          ((finiteSlicePublicSlopeBound_nonneg commonSource terminal).trans
            (finiteSlicePublicSlopeBound_le_sourcePower commonSource terminal))
          (by norm_num) hexactDistance htargetSlope hslopeError hexactY
        have hexactProjection :=
          exact_projection_eq_source commonSource terminal exactPoint
        have hlower := source_lower_projection_dist_le commonSource hsourceAmbient
        have hlowerScaled :
            dist
              (pureWZ2DirectHalfOffsetTerminalLambda *
                  inner ℝ (sourcePoint : Point3)
                    (globalGrainDirection
                      (commonSource.halfOffsetAssembly.globalSlope
                        ((sourcePoint : Point3) 2))) +
                finiteSliceProjectionOffset commonSource terminal)
              (pureWZ2DirectHalfOffsetTerminalLambda *
                  inner ℝ lowerSource
                    (globalGrainDirection
                      (commonSource.halfOffsetAssembly.globalSlope height)) +
                finiteSliceProjectionOffset commonSource terminal) ≤
              pureWZ2DirectHalfOffsetTerminalLambda * delta := by
          rw [Real.dist_eq]
          rw [show
              (pureWZ2DirectHalfOffsetTerminalLambda *
                    inner ℝ (sourcePoint : Point3)
                      (globalGrainDirection
                        (commonSource.halfOffsetAssembly.globalSlope
                          ((sourcePoint : Point3) 2))) +
                  finiteSliceProjectionOffset commonSource terminal) -
                (pureWZ2DirectHalfOffsetTerminalLambda *
                    inner ℝ lowerSource
                      (globalGrainDirection
                        (commonSource.halfOffsetAssembly.globalSlope height)) +
                  finiteSliceProjectionOffset commonSource terminal) =
              pureWZ2DirectHalfOffsetTerminalLambda *
                (inner ℝ (sourcePoint : Point3)
                    (globalGrainDirection
                      (commonSource.halfOffsetAssembly.globalSlope
                        ((sourcePoint : Point3) 2))) -
                  inner ℝ lowerSource
                    (globalGrainDirection
                      (commonSource.halfOffsetAssembly.globalSlope height))) by
                ring, abs_mul, abs_of_pos hlambda]
          exact mul_le_mul_of_nonneg_left hlower hlambda.le
        calc
          dist
              (inner ℝ point
                (globalGrainDirection (safePublicSlope commonSource terminal z)))
              (pureWZ2DirectHalfOffsetTerminalLambda *
                  inner ℝ lowerSource
                    (globalGrainDirection
                      (commonSource.halfOffsetAssembly.globalSlope height)) +
                finiteSliceProjectionOffset commonSource terminal) ≤
            dist
              (inner ℝ point
                (globalGrainDirection (safePublicSlope commonSource terminal z)))
              (inner ℝ (exactPoint : Point3)
                (globalGrainDirection
                  (safePublicSlope commonSource terminal
                    ((exactPoint : Point3) 2)))) +
            dist
              (inner ℝ (exactPoint : Point3)
                (globalGrainDirection
                  (safePublicSlope commonSource terminal
                    ((exactPoint : Point3) 2))))
              (pureWZ2DirectHalfOffsetTerminalLambda *
                  inner ℝ lowerSource
                    (globalGrainDirection
                      (commonSource.halfOffsetAssembly.globalSlope height)) +
                finiteSliceProjectionOffset commonSource terminal) :=
            dist_triangle _ _ _
          _ = dist
              (inner ℝ point
                (globalGrainDirection (safePublicSlope commonSource terminal z)))
              (inner ℝ (exactPoint : Point3)
                (globalGrainDirection
                  (safePublicSlope commonSource terminal
                    ((exactPoint : Point3) 2)))) +
            dist
              (pureWZ2DirectHalfOffsetTerminalLambda *
                  inner ℝ (sourcePoint : Point3)
                    (globalGrainDirection
                      (commonSource.halfOffsetAssembly.globalSlope
                        ((sourcePoint : Point3) 2))) +
                finiteSliceProjectionOffset commonSource terminal)
              (pureWZ2DirectHalfOffsetTerminalLambda *
                  inner ℝ lowerSource
                    (globalGrainDirection
                      (commonSource.halfOffsetAssembly.globalSlope height)) +
                finiteSliceProjectionOffset commonSource terminal) := by
            rw [hexactProjection]
            rfl
          _ ≤
              ((1 + finiteSliceAbsorbableSlopeBound commonSource) *
                  (terminal.targetDelta * Real.sqrt 3) +
                1 * (2 * (terminal.targetDelta * Real.sqrt 3))) +
              pureWZ2DirectHalfOffsetTerminalLambda * delta :=
            add_le_add htargetExact hlowerScaled
          _ ≤ D := by
            dsimp only [D]
            calc
              _ ≤ ((1 + finiteSliceAbsorbableSlopeBound commonSource) *
                    (terminal.targetDelta * Real.sqrt 3) +
                  1 * (2 * (terminal.targetDelta * Real.sqrt 3))) +
                terminal.targetDelta := add_le_add_right hbase _
              _ = terminal.targetDelta *
                  (((finiteSliceAbsorbableSlopeBound commonSource + 3) *
                    Real.sqrt 3) + 1) := by ring
        ) (hD := by
          dsimp only [D]
          apply mul_pos commonSource.halfOffsetLineClassTargetDelta_pos
          have hsqrt := Real.sqrt_nonneg 3
          have hbound := (finiteSlicePublicSlopeBound_nonneg commonSource terminal).trans
            (finiteSlicePublicSlopeBound_le_sourcePower commonSource terminal)
          nlinarith)
  have hratio : D / terminal.targetDelta =
      ((finiteSliceAbsorbableSlopeBound commonSource + 3) *
        Real.sqrt 3) + 1 := by
    dsimp only [D]
    field_simp [commonSource.halfOffsetLineClassTargetDelta_pos.ne']
  rw [hratio] at hraw
  simpa [heightCells, finiteSliceHeightCells_card] using hraw

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
