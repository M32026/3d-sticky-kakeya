import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7ExactGlobalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CubicalSliceADBridge

/-!
# Cubical global AD preparation for the direct Node 7 target

This file starts the paper-faithful recubicalization route.  In particular, a
point of the saturated direct target shading is traced to an exact affine
image of a source point in the original ambient configuration, at the same
source index and in the same target grid cell.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

namespace PureWZ2Node7AffineDiagonalPreparationData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- Every point of the direct saturated target shading has a source witness
in the original ambient configuration whose exact affine image occupies the
same target grid cell.  This retains the synchronized source index. -/
theorem localizedShading_exact_source_witness
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.selected.localizedFamily.card)
    (point : Point3)
    (hpoint : point ∈ data.selected.localizedShading.carrier index) :
    ∃ source : Point3,
      source ∈ commonSource.commonBand.band.lemma31.data.cfg.shading.carrier
        (data.sourceRegularization.regularized.selected.embedding index) ∧
      wz1PaperGridIndex data.affineScale.targetDelta point =
        wz1PaperGridIndex data.affineScale.targetDelta
          (pureWZ2AffineDiagonalMapCentered
            data.affineScale.slopeData.frameSlope data.selected.center
            data.affineScale.slopeData.heightScale
            data.affineScale.slopeData.transverseScale 1 source) := by
  have hpublic : point ∈ data.selected.shading.carrier
      (data.selected.localizedToPublicIndex index) := hpoint
  rw [data.selected.shading_carrier] at hpublic
  rcases hpublic with
    ⟨imagePoint, ⟨source, hsource, rfl⟩, hcell⟩
  refine ⟨source, ?_, ?_⟩
  · have hsubband : source ∈ commonSource.subband.shading.carrier
        (data.sourceRegularization.regularized.selected.embedding index) := by
      have hindex : data.selected.localizedToPublicIndex index = index := rfl
      rw [hindex] at hsource
      rw [data.popular.popular.restricted_carrier] at hsource
      exact hsource.1
    exact commonSource.commonBand.band.source_subshading _ <| by
      rw [commonSource.subband.carrier_eq] at hsubband
      exact hsubband.1
  · exact hcell

/-- The same exact witness, retaining its literal popular-box membership. -/
theorem localizedShading_popular_source_witness
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.selected.localizedFamily.card)
    (point : Point3)
    (hpoint : point ∈ data.selected.localizedShading.carrier index) :
    ∃ source : Point3,
      source ∈ data.popular.popular.restricted.carrier
        (data.sourceRegularization.regularized.selected.embedding index) ∧
      dist point
          (pureWZ2AffineDiagonalMapCentered
            data.affineScale.slopeData.frameSlope data.selected.center
            data.affineScale.slopeData.heightScale
            data.affineScale.slopeData.transverseScale 1 source) <
        2 * data.affineScale.targetDelta := by
  have hpublic : point ∈ data.selected.shading.carrier
      (data.selected.localizedToPublicIndex index) := hpoint
  rw [data.selected.shading_carrier] at hpublic
  rcases hpublic with
    ⟨imagePoint, ⟨source, hsource, rfl⟩, hcell⟩
  refine ⟨source, ?_, ?_⟩
  · have hindex : data.selected.localizedToPublicIndex index = index := rfl
    simpa only [hindex] using hsource
  · apply wz1_paper_grid_cube_diameter_lt_two_rho
      data.affineScale.targetDelta_pos
      (cell := wz1PaperGridIndex data.affineScale.targetDelta point)
    · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
    · exact (mem_wz1PaperGridCube _ _ _).mpr hcell.symm

/-- Algebraic difference formula for the fixed-frame Möbius coordinate. -/
theorem node7MobiusRotatedValue_sub
    {q first second : ℝ}
    (hfirst : 1 + q * first ≠ 0) (hsecond : 1 + q * second ≠ 0) :
    node7MobiusRotatedValue q first -
        node7MobiusRotatedValue q second =
      (1 + q ^ 2) * (first - second) /
        ((1 + q * first) * (1 + q * second)) := by
  unfold node7MobiusRotatedValue
  have hfirst' : 1 + first * q ≠ 0 := by simpa [mul_comm] using hfirst
  have hsecond' : 1 + second * q ≠ 0 := by simpa [mul_comm] using hsecond
  field_simp [hfirst, hsecond, hfirst', hsecond']
  ring

/-- Indexed affine-scale version of the finite-slice cubical AD bridge. -/
theorem targetProjection_ad_of_source_witness_indexed_scales_all
    {sourceDelta targetDelta alpha D : ℝ} {C : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily sourceDelta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (slope : ℝ → ℝ) (heightCells : Finset ℤ)
    (hheightCells : heightCells.Nonempty)
    (hsourceAD : ∀ height : ℝ,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope height))
          (horizontalSlice shading.union height)) sourceDelta alpha C)
    (scale offset : ℤ → ℝ)
    (hscale : ∀ cell ∈ heightCells, 0 < scale cell)
    (hbase : ∀ cell ∈ heightCells,
      scale cell * sourceDelta ≤ targetDelta)
    (target : Set ℝ)
    (hwitness : ∀ value ∈ target,
      ∃ point ∈ shading.union,
        let cell := Int.floor (point 2 / sourceDelta)
        cell ∈ heightCells ∧
          dist value
            (scale cell * inner ℝ
                (pureWZ2ReplaceHeight point
                  (pureWZ2PaperCellLowerHeight sourceDelta point))
                (globalGrainDirection
                  (slope (pureWZ2PaperCellLowerHeight sourceDelta point))) +
              offset cell) ≤ D)
    (hD : 0 < D) :
    PureWZ2PaperADSet1 target targetDelta alpha
      ((2 * (Nat.ceil (D / targetDelta) + 1) : ENNReal) ^ 3 *
        ((heightCells.card : ENNReal) * C)) := by
  let pieces : ℤ → Set ℝ := fun cell =>
    (fun value : ℝ => scale cell * value + offset cell) ''
      scalarProjection
        (globalGrainDirection (slope ((cell : ℝ) * sourceDelta)))
        (horizontalSlice shading.union ((cell : ℝ) * sourceDelta))
  have hpieces : ∀ cell ∈ heightCells,
      PureWZ2PaperADSet1 (pieces cell) targetDelta alpha C := by
    intro cell hcell
    have haffine := PureWZ2PaperADSet1.affine_transfer
      (b := offset cell) (hsourceAD ((cell : ℝ) * sourceDelta))
      (hscale cell hcell)
    exact PureWZ2PaperADSet1.weaken_scale haffine htargetDelta
      (hbase cell hcell)
  have hunion : PureWZ2PaperADSet1
      (⋃ cell ∈ heightCells, pieces cell) targetDelta alpha
        ((heightCells.card : ENNReal) * C) :=
    PureWZ2PaperADSet1.finite_iUnion hheightCells hpieces
  apply hunion.of_subset_cthickening_general (epsilon := D)
  · intro value hvalue
    rcases hwitness value hvalue with ⟨point, hpoint, hcell, hdist⟩
    let cell : ℤ := Int.floor (point 2 / sourceDelta)
    let lower := pureWZ2ReplaceHeight point
      (pureWZ2PaperCellLowerHeight sourceDelta point)
    have hlower : lower ∈ shading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hcubical.replaceHeight_lower_mem hsourceDelta hindex⟩
    have hlowerSlice : lower ∈ horizontalSlice shading.union
        ((cell : ℝ) * sourceDelta) := by
      refine ⟨hlower, ?_⟩
      simp [lower, cell, pureWZ2PaperCellLowerHeight]
    refine ⟨scale cell * inner ℝ lower
        (globalGrainDirection (slope ((cell : ℝ) * sourceDelta))) +
          offset cell, ?_, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨cell, Set.mem_iUnion.mpr ⟨hcell,
        ⟨inner ℝ lower
            (globalGrainDirection (slope ((cell : ℝ) * sourceDelta))),
          ⟨lower, hlowerSlice, rfl⟩, rfl⟩⟩⟩
    · simpa [lower, cell, pureWZ2PaperCellLowerHeight] using hdist
  · exact hD

/-- The exact affine witness supplied above is within one target grid-cell
diameter of the saturated target point. -/
theorem localizedShading_dist_exact_image_lt_two_targetDelta
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.selected.localizedFamily.card)
    (point : Point3)
    (hpoint : point ∈ data.selected.localizedShading.carrier index) :
    ∃ source : Point3,
      source ∈ commonSource.commonBand.band.lemma31.data.cfg.shading.carrier
        (data.sourceRegularization.regularized.selected.embedding index) ∧
      dist point
          (pureWZ2AffineDiagonalMapCentered
            data.affineScale.slopeData.frameSlope data.selected.center
            data.affineScale.slopeData.heightScale
            data.affineScale.slopeData.transverseScale 1 source) <
        2 * data.affineScale.targetDelta := by
  rcases data.localizedShading_exact_source_witness index point hpoint with
    ⟨source, hsource, hcell⟩
  refine ⟨source, hsource, ?_⟩
  apply wz1_paper_grid_cube_diameter_lt_two_rho
    data.affineScale.targetDelta_pos
    (cell := wz1PaperGridIndex data.affineScale.targetDelta point)
  · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
  · exact (mem_wz1PaperGridCube _ _ _).mpr hcell.symm

/-- Replacing a synchronized source witness by the lower face of its ambient
paper cell stays in the ambient configuration. -/
theorem localizedShading_lower_source_mem_configuration
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.selected.localizedFamily.card)
    (point : Point3)
    (hpoint : point ∈ data.selected.localizedShading.carrier index) :
    ∃ source : Point3,
      source ∈ commonSource.commonBand.band.lemma31.data.cfg.shading.carrier
        (data.sourceRegularization.regularized.selected.embedding index) ∧
      pureWZ2ReplaceHeight source
          (pureWZ2PaperCellLowerHeight delta source) ∈
        commonSource.commonBand.band.lemma31.data.cfg.shading.carrier
          (data.sourceRegularization.regularized.selected.embedding index) := by
  rcases data.localizedShading_exact_source_witness index point hpoint with
    ⟨source, hsource, _⟩
  refine ⟨source, hsource, ?_⟩
  exact commonSource.commonBand.band.lemma31.data.cfg.cubical
    |>.replaceHeight_lower_mem
      commonSource.commonBand.band.lemma31.data.cfg.extremal.delta_pos hsource

/-- The exact source witness of a target point at height `t` lies within four
source grid scales of the source height corresponding to `t`.  This is the
quantitative input for the fixed seventeen-cell recubicalization window. -/
theorem localizedShading_sourceHeight_close
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.selected.localizedFamily.card)
    (point : Point3) (t : ℝ)
    (hpoint : point ∈ data.selected.localizedShading.carrier index)
    (hpointHeight : point 2 = t) :
    ∃ source : Point3,
      source ∈ commonSource.commonBand.band.lemma31.data.cfg.shading.carrier
        (data.sourceRegularization.regularized.selected.embedding index) ∧
      |source 2 -
          (data.affineScale.slopeData.anchor +
            t / data.affineScale.slopeData.heightScale)| ≤ 4 * delta := by
  rcases data.localizedShading_dist_exact_image_lt_two_targetDelta
      index point hpoint with ⟨source, hsource, hdist⟩
  let image := pureWZ2AffineDiagonalMapCentered
    data.affineScale.slopeData.frameSlope data.selected.center
    data.affineScale.slopeData.heightScale
    data.affineScale.slopeData.transverseScale 1 source
  have hheight : 0 < data.affineScale.slopeData.heightScale :=
    lt_of_lt_of_le (by norm_num) data.affineScale.height_lower
  have hcenter : data.selected.center 2 =
      data.affineScale.slopeData.anchor := by
    rw [data.selected.center_eq]
    simp [pureWZ2AffineDiagonalCommonCenter, point3]
  have hcoordinate : |image 2 - t| ≤
      2 * data.affineScale.targetDelta := by
    have hcoord := PiLp.dist_apply_le point image (2 : Fin 3)
    rw [Real.dist_eq, hpointHeight] at hcoord
    simpa [abs_sub_comm] using hcoord.trans hdist.le
  have hsourceDifference :
      source 2 -
          (data.affineScale.slopeData.anchor +
            t / data.affineScale.slopeData.heightScale) =
        (image 2 - t) / data.affineScale.slopeData.heightScale := by
    dsimp only [image]
    rw [pureWZ2AffineDiagonalMapCentered_coord_two, hcenter]
    field_simp [hheight.ne']
    ring
  refine ⟨source, hsource, ?_⟩
  rw [hsourceDifference, abs_div, abs_of_pos hheight]
  calc
    |image 2 - t| / data.affineScale.slopeData.heightScale ≤
        (2 * data.affineScale.targetDelta) /
          data.affineScale.slopeData.heightScale := by gcongr
    _ = 4 * delta := by
      rw [data.affineScale.targetDelta_eq]
      field_simp [hheight.ne']
      ring

/-- The nonsingular analysis slope vanishes at zero and is therefore bounded
by two throughout the paper height window. -/
theorem analysisSlope_abs_le_two_cubical
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |data.analysisSlope t| ≤ 2 := by
  have hdifferentiable : Differentiable ℝ data.analysisSlope :=
    data.analysisSlope.contDiff.differentiable (by norm_num)
  have hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖deriv data.analysisSlope x‖ ≤ (2 : ℝ) := by
    intro x hx
    simpa [Real.norm_eq_abs] using
      (data.analysisSlope_nonsingular x hx).2.1
  have hlip := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hdifferentiable.differentiableAt) hderiv
    (show (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 by norm_num) ht
  rw [data.analysisSlope_zero] at hlip
  have htAbs : |t| ≤ 1 := abs_le.mpr ht
  have hnormT : ‖t - (0 : ℝ)‖ ≤ 1 := by
    simpa [Real.norm_eq_abs] using htAbs
  have hfinal := hlip.trans (mul_le_mul_of_nonneg_left hnormT (by norm_num))
  simpa [Real.norm_eq_abs] using hfinal

theorem analysisSlope_lipschitzOn_two_cubical
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    LipschitzOnWith 2 data.analysisSlope (Set.Icc (-1 : ℝ) 1) := by
  have hdifferentiable : Differentiable ℝ data.analysisSlope :=
    data.analysisSlope.contDiff.differentiable (by norm_num)
  apply (convex_Icc (-1 : ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
  · intro x _
    exact hdifferentiable.differentiableAt
  · intro x hx
    apply NNReal.coe_le_coe.mp
    simpa [Real.norm_eq_abs] using
      (data.analysisSlope_nonsingular x hx).2.1

/-- Fixed projection-thickening factor for direct cubical recubicalization. -/
def Node7CubicalGlobalADProjectionFactor
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) : ℝ :=
  8

/-- The explicit constant in the direct cubical global-AD conclusion. -/
def Node7CubicalGlobalADConstant
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) : ENNReal :=
  (2 * (Nat.ceil data.Node7CubicalGlobalADProjectionFactor + 1) : ENNReal) ^ 3 *
    (17 * commonSource.commonBand.band.sourceConstant)

/-- The fixed numerical margin left after the two relative Möbius
denominator bounds.  Keeping this calculation outside the geometric proof
also keeps the latter within Lean's default elaboration budget. -/
private theorem node7_mobius_grid_numeric
    {B m d : ℝ} (hB : 0 < B) (hm : 0 < m) (hd : 0 ≤ d) :
    B * ((8 / 5 : ℝ) * m * d) ≤
      (3 * ((4 / 5 : ℝ) * m / B) * d) *
        (((99 / 100 : ℝ) * B) * ((98 / 100 : ℝ) * B)) := by
  have hcommon : 0 ≤ B * m * d := mul_nonneg (mul_nonneg hB.le hm.le) hd
  calc
    B * ((8 / 5 : ℝ) * m * d) =
        (8 / 5 : ℝ) * (B * m * d) := by ring
    _ ≤ (3 * (4 / 5 : ℝ) * (99 / 100 : ℝ) * (98 / 100 : ℝ)) *
        (B * m * d) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) hcommon
    _ = (3 * ((4 / 5 : ℝ) * m / B) * d) *
        (((99 / 100 : ℝ) * B) * ((98 / 100 : ℝ) * B)) := by
      field_simp [hB.ne']

/-- The normalized source-cell slope error uses only three quarters of the
available target-scale budget. -/
private theorem node7_normalized_grid_slope_numeric
    {gamma d : ℝ} (hgamma : 0 < gamma) (hd : 0 ≤ d) :
    (3 * gamma * d) / (gamma ^ 2 / 1000) ≤
      2 * (2 * (1000 / gamma) * d) := by
  have hden : 0 < gamma ^ 2 / 1000 := by positivity
  rw [div_le_iff₀ hden]
  have hright :
      (2 * (2 * (1000 / gamma) * d)) * (gamma ^ 2 / 1000) =
        4 * gamma * d := by
    field_simp [hgamma.ne']
    ring
  rw [hright]
  nlinarith only [mul_nonneg hgamma.le hd]

private theorem node7_projection_error_numeric
    {d : ℝ} (hd : 0 ≤ d) :
    (1 + (2 : ℝ)) * ((5 / 2 : ℝ) * d) +
        (1 / 800 : ℝ) * (6 * d) ≤ 8 * d := by
  nlinarith only [hd]

/-- On one source grid cell the derivative-band slope varies by the local
slope scale times the source mesh.  This is the refinement which keeps the
Möbius recubicalization loss absolute. -/
theorem sourceSlope_grid_difference_le
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)
    {sourceHeight lowerHeight : ℝ}
    (hsourceHeightSubband : sourceHeight ∈
      Set.Icc commonSource.subband.left commonSource.subband.right)
    (hlowerPaper : lowerHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hlowerClose : |sourceHeight - lowerHeight| ≤ delta) :
    |commonSource.commonBand.band.lemma31.data.globalSlope sourceHeight -
        commonSource.commonBand.band.lemma31.data.globalSlope lowerHeight| ≤
      (8 / 5 : ℝ) * commonSource.commonBand.band.slopeScale * delta := by
  let sourceSlope := commonSource.commonBand.band.lemma31.data.globalSlope
  have hdelta : 0 < delta :=
    commonSource.commonBand.band.lemma31.data.cfg.extremal.delta_pos
  have hsourceBand : sourceHeight ∈ Set.Icc
      commonSource.commonBand.band.left commonSource.commonBand.band.right :=
    ⟨commonSource.subband.left_mem.trans hsourceHeightSubband.1,
      hsourceHeightSubband.2.trans commonSource.subband.right_mem⟩
  have hsourcePaper : sourceHeight ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨commonSource.commonBand.band.lemma31.data.scaleData.slabLeft_mem.trans
        (commonSource.commonBand.band.left_mem.trans hsourceBand.1),
      hsourceBand.2.trans <| commonSource.commonBand.band.right_mem.trans
        commonSource.commonBand.band.lemma31.data.scaleData.slabRight_mem⟩
  have hremainder := pureWZ2_normalized_slope_taylor_remainder
    sourceSlope
    commonSource.commonBand.band.lemma31.data.globalSlope_normalized
    (left := -1) (right := 1) (anchor := sourceHeight)
    (z := lowerHeight) (by norm_num) (by norm_num)
    (by norm_num) hsourcePaper hlowerPaper
  have hderiv : |deriv sourceSlope sourceHeight| ≤
      (51 / 50 : ℝ) * commonSource.commonBand.band.slopeScale := by
    calc
      _ ≤ commonSource.commonBand.band.slopeScale +
          commonSource.commonBand.band.lemma31.data.rho.1 / 50 :=
        commonSource.commonBand.band.derivative_tight_upper
          sourceHeight hsourceBand
      _ ≤ commonSource.commonBand.band.slopeScale +
          commonSource.commonBand.band.slopeScale / 50 := by
        gcongr
        exact commonSource.commonBand.band.slopeScale_lower
      _ = (51 / 50 : ℝ) * commonSource.commonBand.band.slopeScale := by ring
  have hdeltaSlope : delta ≤ commonSource.commonBand.band.slopeScale := by
    have hrhoPower : commonSource.commonBand.band.lemma31.data.rho.1 ^ 8 ≤
        commonSource.commonBand.band.lemma31.data.rho.1 := by
      simpa using pow_le_pow_of_le_one
        (commonSource.commonBand.band.lemma31.data.rho.2.1.trans' hdelta.le)
        (commonSource.commonBand.band.lemma31.rho_tiny.trans (by norm_num))
        (by norm_num : 1 ≤ 8)
    exact commonSource.commonBand.band.lemma31.delta_le_rho_eight.trans
      (hrhoPower.trans commonSource.commonBand.band.slopeScale_lower)
  have hidentity : sourceSlope sourceHeight - sourceSlope lowerHeight =
      -(sourceSlope lowerHeight - sourceSlope sourceHeight -
          deriv sourceSlope sourceHeight * (lowerHeight - sourceHeight)) -
        deriv sourceSlope sourceHeight * (lowerHeight - sourceHeight) := by ring
  rw [hidentity]
  calc
    _ ≤ |sourceSlope lowerHeight - sourceSlope sourceHeight -
          deriv sourceSlope sourceHeight * (lowerHeight - sourceHeight)| +
        |deriv sourceSlope sourceHeight *
          (lowerHeight - sourceHeight)| := by
      simpa only [abs_neg, sub_zero, zero_sub] using
        abs_sub_le
          (-(sourceSlope lowerHeight - sourceSlope sourceHeight -
            deriv sourceSlope sourceHeight * (lowerHeight - sourceHeight)))
          0 (deriv sourceSlope sourceHeight * (lowerHeight - sourceHeight))
    _ ≤ (1 / 2 : ℝ) * (lowerHeight - sourceHeight) ^ 2 +
        ((51 / 50 : ℝ) * commonSource.commonBand.band.slopeScale) * delta := by
      apply add_le_add hremainder
      rw [abs_mul]
      calc
        |deriv sourceSlope sourceHeight| * |lowerHeight - sourceHeight| ≤
            ((51 / 50 : ℝ) * commonSource.commonBand.band.slopeScale) *
              |lowerHeight - sourceHeight| :=
          mul_le_mul_of_nonneg_right hderiv (abs_nonneg _)
        _ ≤ ((51 / 50 : ℝ) * commonSource.commonBand.band.slopeScale) *
            delta :=
          mul_le_mul_of_nonneg_left
            (by simpa [abs_sub_comm] using hlowerClose)
            (mul_nonneg (by norm_num)
              commonSource.commonBand.band.slopeScale_pos.le)
    _ ≤ (8 / 5 : ℝ) * commonSource.commonBand.band.slopeScale * delta := by
      have hdiffSq : (lowerHeight - sourceHeight) ^ 2 ≤ delta ^ 2 := by
        have habs : |lowerHeight - sourceHeight| ≤ delta := by
          simpa [abs_sub_comm] using hlowerClose
        rw [abs_le] at habs
        nlinarith only [habs.1, habs.2]
      have hdeltaSq : delta ^ 2 ≤
          commonSource.commonBand.band.slopeScale * delta := by
        nlinarith [hdeltaSlope, hdelta.le]
      calc
        _ ≤ (1 / 2 : ℝ) * delta ^ 2 +
            ((51 / 50 : ℝ) * commonSource.commonBand.band.slopeScale) *
              delta := by
          exact add_le_add_left
            (mul_le_mul_of_nonneg_left hdiffSq
              (by norm_num : (0 : ℝ) ≤ 1 / 2)) _
        _ ≤ (1 / 2 : ℝ) *
              (commonSource.commonBand.band.slopeScale * delta) +
            ((51 / 50 : ℝ) * commonSource.commonBand.band.slopeScale) *
              delta := by
          exact add_le_add_left
            (mul_le_mul_of_nonneg_left hdeltaSq
              (by norm_num : (0 : ℝ) ≤ 1 / 2)) _
        _ = (38 / 25 : ℝ) *
            commonSource.commonBand.band.slopeScale * delta := by ring
        _ ≤ (8 / 5 : ℝ) *
            commonSource.commonBand.band.slopeScale * delta := by
          have hproductNonneg : 0 ≤
              commonSource.commonBand.band.slopeScale * delta :=
            mul_nonneg commonSource.commonBand.band.slopeScale_pos.le hdelta.le
          nlinarith

/-- Global AD for the actual saturated direct-selected shading.  Saturation
is handled pointwise through an exact affine source witness and a seventeen
cell source-height window; no target slice is discarded outside the active
interval. -/
theorem localizedShading_global_ad
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (data.analysisSlope t))
          (horizontalSlice data.selected.localizedShading.union t))
        data.affineScale.targetDelta (1 - sigma)
        data.Node7CubicalGlobalADConstant := by
  have hdelta : 0 < delta :=
    commonSource.commonBand.band.lemma31.data.cfg.extremal.delta_pos
  intro t ht
  let sourceCenter := data.affineScale.slopeData.anchor +
    t / data.affineScale.slopeData.heightScale
  let heightCells := pureWZ2CenteredHeightCells delta sourceCenter
  let coefficient : ℤ → ℝ := fun cell =>
    let denominator := 1 + data.affineScale.slopeData.frameSlope *
      commonSource.commonBand.band.lemma31.data.globalSlope
        ((cell : ℝ) * delta)
    if (9 / 10 : ℝ) ≤ denominator then
      pureWZ2HorizontalNorm data.affineScale.slopeData.frameSlope / denominator
    else 1
  let offset : ℤ → ℝ := fun cell =>
    -coefficient cell * inner ℝ data.selected.center
      (globalGrainDirection
        (commonSource.commonBand.band.lemma31.data.globalSlope
          ((cell : ℝ) * delta)))
  let D : ℝ := 8 * data.affineScale.targetDelta
  have hheightCells : heightCells.Nonempty := by
    apply Finset.card_pos.mp
    rw [show heightCells.card = 17 by
      simpa only [heightCells] using
        pureWZ2CenteredHeightCells_card delta sourceCenter]
    norm_num
  have hraw :=
    targetProjection_ad_of_source_witness_indexed_scales_all
        commonSource.commonBand.band.lemma31.data.cfg.cubical
        hdelta data.affineScale.targetDelta_pos
        commonSource.commonBand.band.lemma31.data.globalSlope
        heightCells hheightCells
        (commonSource.commonBand.band.configuration_global_ad_all
          hsigma hsigmaOne)
        coefficient offset
        (by
          intro cell _
          dsimp only [coefficient]
          split_ifs with hden
          · exact div_pos (pureWZ2HorizontalNorm_pos _)
              ((by norm_num : (0 : ℝ) < 9 / 10).trans_le hden)
          · norm_num)
        (by
          intro cell hcell
          have hcoeff : coefficient cell ≤ 2 := by
            dsimp only [coefficient]
            split_ifs with hden
            · apply (div_le_iff₀ ((by norm_num : (0 : ℝ) < 9 / 10).trans_le
                hden)).2
              have hnormSq := pureWZ2HorizontalNorm_sq
                data.affineScale.slopeData.frameSlope
              have hq := data.affineScale.slopeData.frameSlope_bound
              have hnorm : pureWZ2HorizontalNorm
                  data.affineScale.slopeData.frameSlope ≤ 3 / 2 := by
                nlinarith [sq_nonneg
                  (pureWZ2HorizontalNorm
                    data.affineScale.slopeData.frameSlope),
                  pureWZ2HorizontalNorm_pos
                    data.affineScale.slopeData.frameSlope,
                  abs_le.mp hq]
              nlinarith
            · norm_num
          have htwoDelta : 2 * delta ≤ data.affineScale.targetDelta := by
            rw [data.affineScale.targetDelta_eq]
            nlinarith [data.affineScale.height_lower, hdelta.le]
          exact (mul_le_mul_of_nonneg_right hcoeff hdelta.le).trans htwoDelta)
        (target := scalarProjection
          (globalGrainDirection (data.analysisSlope t))
          (horizontalSlice data.selected.localizedShading.union t))
        (D := D) (by
          rintro value ⟨point, ⟨hpointUnion, hpointHeight⟩, rfl⟩
          rcases hpointUnion with ⟨index, hpoint⟩
          rcases data.localizedShading_popular_source_witness
              index point hpoint with ⟨source, hsourcePopular, hexactDistance⟩
          have hsourceSubband : source ∈ commonSource.subband.shading.carrier
              (data.sourceRegularization.regularized.selected.embedding
                index) := by
            rw [data.popular.popular.restricted_carrier] at hsourcePopular
            exact hsourcePopular.1
          have hsource : source ∈
              commonSource.commonBand.band.lemma31.data.cfg.shading.carrier
                (data.sourceRegularization.regularized.selected.embedding
                  index) :=
            commonSource.commonBand.band.source_subshading _ <| by
              rw [commonSource.subband.carrier_eq] at hsourceSubband
              exact hsourceSubband.1
          let exactPoint := pureWZ2AffineDiagonalMapCentered
            data.affineScale.slopeData.frameSlope data.selected.center
            data.affineScale.slopeData.heightScale
            data.affineScale.slopeData.transverseScale 1 source
          have hheight : 0 < data.affineScale.slopeData.heightScale :=
            lt_of_lt_of_le (by norm_num) data.affineScale.height_lower
          have hcenterHeight : data.selected.center 2 =
              data.affineScale.slopeData.anchor := by
            rw [data.selected.center_eq]
            simp [pureWZ2AffineDiagonalCommonCenter, point3]
          have hexactHeightDistance : |exactPoint 2 - t| ≤
              2 * data.affineScale.targetDelta := by
            have hcoord := PiLp.dist_apply_le point exactPoint (2 : Fin 3)
            rw [Real.dist_eq, hpointHeight] at hcoord
            simpa [abs_sub_comm] using hcoord.trans hexactDistance.le
          have hsourceClose : |source 2 - sourceCenter| ≤ 4 * delta := by
            have hsourceDifference : source 2 - sourceCenter =
                (exactPoint 2 - t) /
                  data.affineScale.slopeData.heightScale := by
              dsimp only [sourceCenter, exactPoint]
              rw [pureWZ2AffineDiagonalMapCentered_coord_two, hcenterHeight]
              field_simp [hheight.ne']
              ring
            rw [hsourceDifference, abs_div, abs_of_pos hheight]
            calc
              |exactPoint 2 - t| /
                    data.affineScale.slopeData.heightScale ≤
                  (2 * data.affineScale.targetDelta) /
                    data.affineScale.slopeData.heightScale := by gcongr
              _ = 4 * delta := by
                rw [data.affineScale.targetDelta_eq]
                field_simp [hheight.ne']
                ring
          have hcell : Int.floor (source 2 / delta) ∈ heightCells :=
            pureWZ2_heightCell_mem_centered hdelta (by
              have hdeltaNonneg := hdelta.le
              simpa only [sourceCenter] using
                hsourceClose.trans (by nlinarith))
          refine ⟨source, ⟨_, hsource⟩, hcell, ?_⟩
          let lowerSource := pureWZ2ReplaceHeight source
            (pureWZ2PaperCellLowerHeight delta source)
          let lowerHeight := pureWZ2PaperCellLowerHeight delta source
          let lowerImage := pureWZ2AffineDiagonalMapCentered
            data.affineScale.slopeData.frameSlope data.selected.center
            data.affineScale.slopeData.heightScale
            data.affineScale.slopeData.transverseScale 1 lowerSource
          have hlower : lowerSource ∈
              commonSource.commonBand.band.lemma31.data.cfg.shading.carrier
                (data.sourceRegularization.regularized.selected.embedding
                  index) :=
            commonSource.commonBand.band.lemma31.data.cfg.cubical
              |>.replaceHeight_lower_mem hdelta hsource
          have hlowerBox :=
            commonSource.commonBand.band.lemma31.data.cfg.shading.subset_body
              (data.sourceRegularization.regularized.selected.embedding index)
              hlower |>.2
          have hlowerHeight : lowerSource 2 ∈ Set.Icc (-1 : ℝ) 1 := by
            exact abs_le.mp <| by
              simpa [Kakeya.Streamlined.axisBox] using hlowerBox.2.2
          have htargetSlope : |data.analysisSlope t| ≤ 2 :=
            data.analysisSlope_abs_le_two_cubical ht
          have himageLower : dist exactPoint lowerImage ≤
              data.affineScale.targetDelta / 2 := by
            rw [dist_eq_norm]
            rw [show exactPoint - lowerImage =
                pureWZ2AffineDiagonalLinear
                  data.affineScale.slopeData.frameSlope
                  data.affineScale.slopeData.heightScale
                  data.affineScale.slopeData.transverseScale 1
                  (source - lowerSource) by
              dsimp only [exactPoint, lowerImage]
              exact pureWZ2AffineDiagonalMapCentered_sub
                data.affineScale.slopeData.frameSlope data.selected.center
                source lowerSource data.affineScale.slopeData.heightScale
                data.affineScale.slopeData.transverseScale 1]
            have hsourceDifference : source - lowerSource =
                (source 2 - lowerHeight) •
                  (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : Point3) := by
              ext coordinate
              fin_cases coordinate <;>
                simp [lowerSource, lowerHeight, pureWZ2ReplaceHeight, point3]
            rw [hsourceDifference, pureWZ2AffineDiagonalLinear_smul, norm_smul]
            have hunit : ‖pureWZ2AffineDiagonalLinear
                data.affineScale.slopeData.frameSlope
                data.affineScale.slopeData.heightScale
                data.affineScale.slopeData.transverseScale 1
                (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : Point3)‖ =
              data.affineScale.slopeData.heightScale := by
              rw [show pureWZ2AffineDiagonalLinear
                  data.affineScale.slopeData.frameSlope
                  data.affineScale.slopeData.heightScale
                  data.affineScale.slopeData.transverseScale 1
                  (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : Point3) =
                (EuclideanSpace.single (2 : Fin 3)
                  data.affineScale.slopeData.heightScale : Point3) by
                    ext coordinate
                    fin_cases coordinate <;>
                      simp [pureWZ2AffineDiagonalLinear, point3]]
              simp [Real.norm_eq_abs, abs_of_pos hheight]
            rw [hunit]
            have hclose := pureWZ2PaperCellLowerHeight_close hdelta source
            calc
              |source 2 - lowerHeight| *
                    data.affineScale.slopeData.heightScale ≤
                  delta * data.affineScale.slopeData.heightScale := by gcongr
              _ = data.affineScale.targetDelta / 2 := by
                rw [data.affineScale.targetDelta_eq]
                ring
          have hlowerDistance : dist point lowerImage ≤
              (5 / 2 : ℝ) * data.affineScale.targetDelta := by
            calc
              dist point lowerImage ≤ dist point exactPoint +
                  dist exactPoint lowerImage := dist_triangle _ _ _
              _ ≤ 2 * data.affineScale.targetDelta +
                  data.affineScale.targetDelta / 2 :=
                add_le_add hexactDistance.le himageLower
              _ = (5 / 2 : ℝ) * data.affineScale.targetDelta := by ring
          have hexactHeight : exactPoint 2 ∈ Set.Icc (-1 : ℝ) 1 := by
            have hexactCarrier : exactPoint ∈ data.exactShading.carrier index :=
              ⟨source, hsourcePopular, rfl⟩
            have hbox := data.exactShading.subset_body index hexactCarrier |>.2
            exact abs_le.mp <| by
              simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
          have hslopeFirst :
              |data.analysisSlope t - data.analysisSlope (exactPoint 2)| ≤
                4 * data.affineScale.targetDelta := by
            have hlip := data.analysisSlope_lipschitzOn_two_cubical.dist_le_mul
              t ht (exactPoint 2) hexactHeight
            calc
              _ ≤ 2 * |t - exactPoint 2| := by
                simpa [Real.dist_eq] using hlip
              _ ≤ 4 * data.affineScale.targetDelta := by
                have := hexactHeightDistance
                rw [abs_sub_comm] at this
                nlinarith
          have hsourceHeightSubband : source 2 ∈
              Set.Icc commonSource.subband.left commonSource.subband.right := by
            rw [commonSource.subband.carrier_eq] at hsourceSubband
            exact hsourceSubband.2
          have hexactActive : exactPoint 2 ∈
              Set.Icc data.activeLeft data.activeRight := by
            have hexactCarrier : exactPoint ∈ data.exactShading.carrier index :=
              ⟨source, hsourcePopular, rfl⟩
            exact data.exactShading_height_mem_active index exactPoint
              hexactCarrier
          have hsourceHeightIdentity :
              data.affineScale.slopeData.anchor + exactPoint 2 /
                  data.affineScale.slopeData.heightScale = source 2 := by
            rw [show exactPoint 2 =
                data.affineScale.slopeData.heightScale *
                  (source 2 - data.affineScale.slopeData.anchor) by
              dsimp only [exactPoint]
              rw [pureWZ2AffineDiagonalMapCentered_coord_two, hcenterHeight]
              ring]
            field_simp [hheight.ne']
            ring
          have hexactSlope : data.analysisSlope (exactPoint 2) =
              node7MobiusRotatedValue data.affineScale.slopeData.frameSlope
                (commonSource.commonBand.band.lemma31.data.globalSlope
                  (source 2)) /
                data.affineScale.slopeData.transverseScale := by
            rw [data.analysisSlope_eq_on_active hexactActive]
            unfold exactSlopeValue node7ExactNormalizedSlopeValue
            rw [hsourceHeightIdentity]
          have hlowerClose : |source 2 - lowerHeight| ≤ delta :=
            pureWZ2PaperCellLowerHeight_close hdelta source
          have hsourceSlopeClose :
              |commonSource.commonBand.band.lemma31.data.globalSlope
                    (source 2) -
                commonSource.commonBand.band.lemma31.data.globalSlope
                    lowerHeight| ≤ delta := by
            have hsourcePaper : source 2 ∈ Set.Icc (-1 : ℝ) 1 := by
              have hbox :=
                commonSource.commonBand.band.lemma31.data.cfg.shading.subset_body
                  (data.sourceRegularization.regularized.selected.embedding
                    index) hsource |>.2
              exact abs_le.mp <| by
                simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
            have hlip := SlopeFunction.lipschitzOn_unit_of_normalized
              commonSource.commonBand.band.lemma31.data.globalSlope
              commonSource.commonBand.band.lemma31.data.globalSlope_normalized
              |>.dist_le_mul (source 2) hsourcePaper lowerHeight (by
                simpa only [lowerSource, pureWZ2ReplaceHeight_apply_two]
                  using hlowerHeight)
            calc
              _ ≤ |source 2 - lowerHeight| := by
                simpa [Real.dist_eq] using hlip
              _ ≤ delta := hlowerClose
          have hsourceSlopeCloseRefined :
              |commonSource.commonBand.band.lemma31.data.globalSlope
                    (source 2) -
                commonSource.commonBand.band.lemma31.data.globalSlope
                    lowerHeight| ≤
                (8 / 5 : ℝ) * commonSource.commonBand.band.slopeScale *
                  delta := by
            have hlowerPaper : lowerHeight ∈ Set.Icc (-1 : ℝ) 1 := by
              simpa only [lowerSource, pureWZ2ReplaceHeight_apply_two]
                using hlowerHeight
            exact sourceSlope_grid_difference_le commonSource
              hsourceHeightSubband hlowerPaper hlowerClose
          have hq := data.affineScale.slopeData.frameSlope_bound
          have hsourceFrame :
              |commonSource.commonBand.band.lemma31.data.globalSlope
                    (source 2) - data.affineScale.slopeData.frameSlope| ≤
                1 / 200 := by
            rw [data.node7Scale.frame_at_left]
            have hlip := SlopeFunction.lipschitzOn_unit_of_normalized
              commonSource.commonBand.band.lemma31.data.globalSlope
              commonSource.commonBand.band.lemma31.data.globalSlope_normalized
            have hleftPaper : commonSource.subband.left ∈
                Set.Icc (-1 : ℝ) 1 :=
              ⟨commonSource.commonBand.band.lemma31.data.scaleData.slabLeft_mem.trans
                  (commonSource.commonBand.band.left_mem.trans
                    commonSource.subband.left_mem),
                commonSource.subband.ordered.le.trans
                  (commonSource.subband.right_mem.trans
                    (commonSource.commonBand.band.right_mem.trans
                      commonSource.commonBand.band.lemma31.data.scaleData.slabRight_mem))⟩
            have hsourcePaper : source 2 ∈ Set.Icc (-1 : ℝ) 1 := by
              exact ⟨hleftPaper.1.trans hsourceHeightSubband.1,
                hsourceHeightSubband.2.trans <|
                  commonSource.subband.right_mem.trans <|
                    commonSource.commonBand.band.right_mem.trans
                      commonSource.commonBand.band.lemma31.data.scaleData.slabRight_mem⟩
            have hdiff := hlip.dist_le_mul (source 2) hsourcePaper
              commonSource.subband.left hleftPaper
            have hlength : |source 2 - commonSource.subband.left| ≤
                commonSource.subband.right - commonSource.subband.left := by
              rw [abs_le]
              constructor <;> linarith [hsourceHeightSubband.1,
                hsourceHeightSubband.2]
            calc
              _ ≤ |source 2 - commonSource.subband.left| := by
                simpa [Real.dist_eq] using hdiff
              _ ≤ commonSource.subband.right - commonSource.subband.left :=
                hlength
              _ = commonSource.commonBand.band.lemma31.data.rho.1 / 5000 := by
                rw [commonSource.subband.length_eq,
                  commonSource.commonBand.band.length_eq]
                ring
              _ ≤ 1 / 200 := by
                linarith [commonSource.commonBand.band.lemma31.rho_tiny]
          have hdeltaTiny : delta ≤ 1 / 200 := by
            have hrhoPos : 0 <
                commonSource.commonBand.band.lemma31.data.rho.1 :=
              hdelta.trans_le
                commonSource.commonBand.band.lemma31.data.rho.2.1
            have hrhoOne :
                commonSource.commonBand.band.lemma31.data.rho.1 ≤ 1 :=
              commonSource.commonBand.band.lemma31.rho_tiny.trans (by norm_num)
            have hpow : commonSource.commonBand.band.lemma31.data.rho.1 ^ 8 ≤
                commonSource.commonBand.band.lemma31.data.rho.1 := by
              simpa using pow_le_pow_of_le_one hrhoPos.le hrhoOne
                (by norm_num : 1 ≤ 8)
            exact commonSource.commonBand.band.lemma31.delta_le_rho_eight.trans
              (hpow.trans <|
                commonSource.commonBand.band.lemma31.rho_tiny.trans (by norm_num))
          have hlowerFrame :
              |commonSource.commonBand.band.lemma31.data.globalSlope
                    lowerHeight - data.affineScale.slopeData.frameSlope| ≤
                1 / 100 := by
            calc
              _ ≤ |commonSource.commonBand.band.lemma31.data.globalSlope
                    lowerHeight -
                    commonSource.commonBand.band.lemma31.data.globalSlope
                      (source 2)| +
                  |commonSource.commonBand.band.lemma31.data.globalSlope
                    (source 2) - data.affineScale.slopeData.frameSlope| :=
                abs_sub_le _ _ _
              _ ≤ delta + 1 / 200 := by
                rw [abs_sub_comm]
                gcongr
              _ ≤ 1 / 100 := by linarith
          have hdenSource := node7Mobius_denominator_ne_zero hq
            (hsourceFrame.trans (by norm_num))
          have hdenLower : 1 + data.affineScale.slopeData.frameSlope *
              commonSource.commonBand.band.lemma31.data.globalSlope
                lowerHeight ≠ 0 := by
            apply node7Mobius_denominator_ne_zero hq
            exact hlowerFrame
          have hmobiusDifference :
              |node7MobiusRotatedValue data.affineScale.slopeData.frameSlope
                    (commonSource.commonBand.band.lemma31.data.globalSlope
                      (source 2)) -
                node7MobiusRotatedValue data.affineScale.slopeData.frameSlope
                    (commonSource.commonBand.band.lemma31.data.globalSlope
                      lowerHeight)| ≤
                3 * data.affineScale.slopeData.rotatedSlopeScale * delta := by
            rw [node7MobiusRotatedValue_sub hdenSource hdenLower, abs_div,
              abs_mul]
            let q := data.affineScale.slopeData.frameSlope
            let B := 1 + q ^ 2
            let m := commonSource.commonBand.band.slopeScale
            have hBPos : 0 < B := by dsimp only [B, q]; positivity
            have hdenSourceLower : (99 / 100 : ℝ) * B ≤
                1 + q * commonSource.commonBand.band.lemma31.data.globalSlope
                  (source 2) := by
              have hqMul : |q *
                  (commonSource.commonBand.band.lemma31.data.globalSlope
                    (source 2) - q)| ≤ 1 / 200 := by
                rw [abs_mul]
                calc
                  |q| * |commonSource.commonBand.band.lemma31.data.globalSlope
                        (source 2) - q| ≤ 1 * (1 / 200) :=
                    mul_le_mul hq hsourceFrame (abs_nonneg _) (by norm_num)
                  _ = 1 / 200 := one_mul _
              have hBOne : (1 : ℝ) ≤ B := by
                dsimp only [B]
                exact le_add_of_nonneg_right (sq_nonneg q)
              rw [abs_le] at hqMul
              have herrorLower : -(1 / 200 : ℝ) ≤ q *
                  (commonSource.commonBand.band.lemma31.data.globalSlope
                    (source 2) - q) := hqMul.1
              have hidentity : 1 + q *
                    commonSource.commonBand.band.lemma31.data.globalSlope
                      (source 2) =
                  B + q *
                    (commonSource.commonBand.band.lemma31.data.globalSlope
                      (source 2) - q) := by
                dsimp only [B]
                ring
              rw [hidentity]
              have hsmall : (1 / 200 : ℝ) ≤ (1 / 100 : ℝ) * B := by
                nlinarith only [hBOne]
              linarith only [herrorLower, hsmall]
            have hdenLowerLower : (98 / 100 : ℝ) * B ≤
                1 + q * commonSource.commonBand.band.lemma31.data.globalSlope
                  lowerHeight := by
              have hqMul : |q *
                  (commonSource.commonBand.band.lemma31.data.globalSlope
                    lowerHeight -
                   commonSource.commonBand.band.lemma31.data.globalSlope
                    (source 2))| ≤ delta := by
                rw [abs_mul]
                calc
                  |q| * |commonSource.commonBand.band.lemma31.data.globalSlope
                        lowerHeight -
                      commonSource.commonBand.band.lemma31.data.globalSlope
                        (source 2)| ≤ 1 * delta := by
                    gcongr
                    simpa [abs_sub_comm] using hsourceSlopeClose
                  _ = delta := one_mul _
              have hdeltaHundred : delta ≤ (1 / 100 : ℝ) * B := by
                calc
                  delta ≤ 1 / 200 := hdeltaTiny
                  _ ≤ 1 / 100 := by norm_num
                  _ = (1 / 100 : ℝ) * 1 := by ring
                  _ ≤ (1 / 100 : ℝ) * B := by
                    apply mul_le_mul_of_nonneg_left _ (by norm_num)
                    dsimp only [B]
                    exact le_add_of_nonneg_right (sq_nonneg q)
              rw [abs_le] at hqMul
              have herrorLower : -delta ≤ q *
                  (commonSource.commonBand.band.lemma31.data.globalSlope
                    lowerHeight -
                   commonSource.commonBand.band.lemma31.data.globalSlope
                    (source 2)) := hqMul.1
              have hidentity : 1 + q *
                    commonSource.commonBand.band.lemma31.data.globalSlope
                      lowerHeight =
                  (1 + q *
                    commonSource.commonBand.band.lemma31.data.globalSlope
                      (source 2)) +
                  q * (commonSource.commonBand.band.lemma31.data.globalSlope
                    lowerHeight -
                    commonSource.commonBand.band.lemma31.data.globalSlope
                      (source 2)) := by ring
              change (98 / 100 : ℝ) * B ≤
                1 + q * commonSource.commonBand.band.lemma31.data.globalSlope
                  lowerHeight
              rw [hidentity]
              linarith only [hdenSourceLower, herrorLower, hdeltaHundred]
            have hdenProductPos : 0 <
                (1 + data.affineScale.slopeData.frameSlope *
                    commonSource.commonBand.band.lemma31.data.globalSlope
                      (source 2)) *
                  (1 + data.affineScale.slopeData.frameSlope *
                    commonSource.commonBand.band.lemma31.data.globalSlope
                      lowerHeight) :=
              mul_pos (lt_of_lt_of_le (mul_pos (by norm_num) hBPos)
                hdenSourceLower)
                (lt_of_lt_of_le (mul_pos (by norm_num) hBPos)
                  hdenLowerLower)
            have hBNonneg : 0 ≤
                1 + data.affineScale.slopeData.frameSlope ^ 2 :=
              add_nonneg (by norm_num)
                (sq_nonneg data.affineScale.slopeData.frameSlope)
            rw [abs_of_nonneg hBNonneg, abs_of_pos hdenProductPos]
            apply (div_le_iff₀ hdenProductPos).2
            rw [data.node7Scale.rotated_scale_eq]
            unfold pureWZ2Node7RotatedSlopeScale
            rw [← data.node7Scale.frame_at_left]
            dsimp only [B, q, m] at hdenSourceLower hdenLowerLower hBPos ⊢
            have hproductLower :
                ((99 / 100 : ℝ) *
                    (1 + data.affineScale.slopeData.frameSlope ^ 2)) *
                  ((98 / 100 : ℝ) *
                    (1 + data.affineScale.slopeData.frameSlope ^ 2)) ≤
                (1 + data.affineScale.slopeData.frameSlope *
                    commonSource.commonBand.band.lemma31.data.globalSlope
                      (source 2)) *
                  (1 + data.affineScale.slopeData.frameSlope *
                    commonSource.commonBand.band.lemma31.data.globalSlope
                      lowerHeight) :=
              mul_le_mul hdenSourceLower hdenLowerLower
                (mul_nonneg (by norm_num) hBPos.le)
                (le_trans (mul_nonneg (by norm_num) hBPos.le)
                  hdenSourceLower)
            have hmPos := commonSource.commonBand.band.slopeScale_pos
            have hdeltaNonneg := hdelta.le
            have hnum := mul_le_mul_of_nonneg_left hsourceSlopeCloseRefined
              hBNonneg
            apply hnum.trans
            calc
              (1 + data.affineScale.slopeData.frameSlope ^ 2) *
                    ((8 / 5 : ℝ) *
                      commonSource.commonBand.band.slopeScale * delta) ≤
                  (3 * ((4 / 5 : ℝ) *
                      commonSource.commonBand.band.slopeScale /
                        (1 + data.affineScale.slopeData.frameSlope ^ 2)) *
                    delta) *
                    (((99 / 100 : ℝ) *
                        (1 + data.affineScale.slopeData.frameSlope ^ 2)) *
                      ((98 / 100 : ℝ) *
                        (1 + data.affineScale.slopeData.frameSlope ^ 2))) := by
                exact node7_mobius_grid_numeric hBPos hmPos hdeltaNonneg
              _ ≤ (3 * ((4 / 5 : ℝ) *
                      commonSource.commonBand.band.slopeScale /
                        (1 + data.affineScale.slopeData.frameSlope ^ 2)) *
                    delta) *
                  ((1 + data.affineScale.slopeData.frameSlope *
                      commonSource.commonBand.band.lemma31.data.globalSlope
                        (source 2)) *
                    (1 + data.affineScale.slopeData.frameSlope *
                      commonSource.commonBand.band.lemma31.data.globalSlope
                        lowerHeight)) := by
                exact mul_le_mul_of_nonneg_left hproductLower (by positivity)
          have htransverse : 0 <
              data.affineScale.slopeData.transverseScale :=
            data.affineScale.transverse_pos
          have hslopeSecond :
              |data.analysisSlope (exactPoint 2) -
                  node7MobiusRotatedValue
                    data.affineScale.slopeData.frameSlope
                    (commonSource.commonBand.band.lemma31.data.globalSlope
                      lowerHeight) /
                    data.affineScale.slopeData.transverseScale| ≤
                2 * data.affineScale.targetDelta := by
            rw [hexactSlope, ← sub_div, abs_div, abs_of_pos htransverse]
            calc
              _ ≤ (3 * data.affineScale.slopeData.rotatedSlopeScale * delta) /
                    data.affineScale.slopeData.transverseScale := by gcongr
              _ ≤ 2 * data.affineScale.targetDelta := by
                rw [data.affineScale.targetDelta_eq,
                  data.affineScale.slopeData.heightScale_eq,
                  data.affineScale.slopeData.transverseScale_eq,
                  data.node7Scale.normalization_thousand]
                exact node7_normalized_grid_slope_numeric
                  data.affineScale.slopeData.rotatedSlopeScale_pos hdelta.le
          have hslopeError :
              |data.analysisSlope t -
                  node7MobiusRotatedValue
                    data.affineScale.slopeData.frameSlope
                    (commonSource.commonBand.band.lemma31.data.globalSlope
                      lowerHeight) /
                    data.affineScale.slopeData.transverseScale| ≤
                6 * data.affineScale.targetDelta := by
            exact (abs_sub_le _ _ _).trans <| by
              linarith [hslopeFirst, hslopeSecond]
          have hbox := by
            rw [data.popular.popular.restricted_carrier,
              data.popular.popular.box_eq] at hsourcePopular
            exact hsourcePopular.2.1
          have hx : |source 0 - data.selected.center 0| ≤ 1 / 16 := by
            have hcenter : data.selected.center 0 =
                data.popular.popular.center 0 := by
              rw [data.selected.center_eq]
              simp [pureWZ2AffineDiagonalCommonCenter, point3]
            rw [hcenter]
            have hraw := hbox (0 : Fin 3)
            simp [point3] at hraw
            norm_num at hraw
            exact hraw
          have hy : |source 1 - data.selected.center 1| ≤ 1 / 16 := by
            have hcenter : data.selected.center 1 =
                data.popular.popular.center 1 := by
              rw [data.selected.center_eq]
              simp [pureWZ2AffineDiagonalCommonCenter, point3]
            rw [hcenter]
            have hraw := hbox (1 : Fin 3)
            simp [point3] at hraw
            norm_num at hraw
            exact hraw
          have hlowerY : |lowerImage 1| ≤ 1 / 800 := by
            rw [show lowerImage 1 =
                data.affineScale.slopeData.transverseScale *
                  ((-data.affineScale.slopeData.frameSlope *
                      (source 0 - data.selected.center 0) +
                    (source 1 - data.selected.center 1)) /
                    pureWZ2HorizontalNorm
                      data.affineScale.slopeData.frameSlope) by
              dsimp only [lowerImage]
              rw [pureWZ2AffineDiagonalMapCentered_coord_one _ _ _ _ _
                data.affineScale.transverse_pos.ne' one_ne_zero]
              simp [lowerSource]]
            rw [abs_mul, abs_div, abs_of_pos htransverse,
              abs_of_pos (pureWZ2HorizontalNorm_pos _)]
            have hhorizontal := affineHorizontalFirstBound
              (frame := -data.affineScale.slopeData.frameSlope)
              (x := source 1 - data.selected.center 1)
              (y := source 0 - data.selected.center 0)
              (bound := 1 / 16) (by simpa) hy hx (by norm_num)
            have hhorizontal' :
                |-data.affineScale.slopeData.frameSlope *
                      (source 0 - data.selected.center 0) +
                    (source 1 - data.selected.center 1)| /
                  pureWZ2HorizontalNorm
                    data.affineScale.slopeData.frameSlope ≤ 1 / 8 := by
              convert hhorizontal using 1 <;>
                norm_num [pureWZ2HorizontalNorm, add_comm, mul_comm,
                  mul_left_comm]
            calc
              _ ≤ data.affineScale.slopeData.transverseScale * (1 / 8) := by
                gcongr
              _ ≤ (1 / 100 : ℝ) * (1 / 8) := by
                gcongr
                exact data.affineScale.transverse_le
              _ = 1 / 800 := by norm_num
          have hprojection : dist
              (inner ℝ point (globalGrainDirection (data.analysisSlope t)))
              (inner ℝ lowerImage
                (globalGrainDirection
                  (node7MobiusRotatedValue
                    data.affineScale.slopeData.frameSlope
                    (commonSource.commonBand.band.lemma31.data.globalSlope
                      lowerHeight) /
                    data.affineScale.slopeData.transverseScale))) ≤
                8 * data.affineScale.targetDelta := by
            have h := pureWZ2_globalProjection_dist_le_of_point_slope_error
              point lowerImage (data.analysisSlope t)
              (node7MobiusRotatedValue
                data.affineScale.slopeData.frameSlope
                (commonSource.commonBand.band.lemma31.data.globalSlope
                  lowerHeight) / data.affineScale.slopeData.transverseScale)
              ((5 / 2 : ℝ) * data.affineScale.targetDelta)
              (6 * data.affineScale.targetDelta) 2 (1 / 800)
              (mul_nonneg (by norm_num) data.affineScale.targetDelta_pos.le)
              (mul_nonneg (by norm_num) data.affineScale.targetDelta_pos.le)
              (by norm_num) (by norm_num)
              hlowerDistance htargetSlope hslopeError hlowerY
            exact h.trans <| node7_projection_error_numeric
              data.affineScale.targetDelta_pos.le
          have hprojectionIdentity :=
            pureWZ2AffineDiagonalCentered_projection_identity
              data.affineScale.slopeData.frameSlope data.selected.center
              data.affineScale.slopeData.heightScale
              data.affineScale.slopeData.transverseScale 1
              (commonSource.commonBand.band.lemma31.data.globalSlope
                lowerHeight) lowerSource
              data.affineScale.transverse_pos.ne' hdenLower
          have hrotatedValue :
              node7MobiusRotatedValue
                  data.affineScale.slopeData.frameSlope
                  (commonSource.commonBand.band.lemma31.data.globalSlope
                    lowerHeight) =
                pureWZ2RotatedSlopeValue
                  data.affineScale.slopeData.frameSlope
                  (commonSource.commonBand.band.lemma31.data.globalSlope
                    lowerHeight) := by
            rfl
          rw [hrotatedValue] at hprojection
          rw [show lowerImage = pureWZ2AffineDiagonalMapCentered
              data.affineScale.slopeData.frameSlope data.selected.center
              data.affineScale.slopeData.heightScale
              data.affineScale.slopeData.transverseScale 1 lowerSource by rfl,
            hprojectionIdentity] at hprojection
          have hdenLowerBound := node7Mobius_denominator_lower hq hlowerFrame
          have hcoefficientCell :
              coefficient (Int.floor (source 2 / delta)) =
                pureWZ2HorizontalNorm data.affineScale.slopeData.frameSlope /
                  (1 + data.affineScale.slopeData.frameSlope *
                    commonSource.commonBand.band.lemma31.data.globalSlope
                      lowerHeight) := by
            dsimp only [coefficient]
            have hlowerHeightEq :
                (Int.floor (source 2 / delta) : ℝ) * delta = lowerHeight :=
              rfl
            rw [hlowerHeightEq]
            rw [if_pos (hdenLowerBound.trans' (by norm_num))]
          change dist
              (inner ℝ point
                (globalGrainDirection (data.analysisSlope t)))
              (coefficient (Int.floor (source 2 / delta)) *
                  inner ℝ lowerSource
                    (globalGrainDirection
                      (commonSource.commonBand.band.lemma31.data.globalSlope
                        lowerHeight)) +
                offset (Int.floor (source 2 / delta))) ≤ D
          change dist
              (inner ℝ point
                (globalGrainDirection (data.analysisSlope t)))
              (coefficient (Int.floor (source 2 / delta)) *
                  inner ℝ lowerSource
                    (globalGrainDirection
                      (commonSource.commonBand.band.lemma31.data.globalSlope
                        lowerHeight)) +
                offset (Int.floor (source 2 / delta))) ≤
            8 * data.affineScale.targetDelta
          rw [hcoefficientCell]
          dsimp only [offset]
          rw [hcoefficientCell]
          rw [show (Int.floor (source 2 / delta) : ℝ) * delta = lowerHeight by
            rfl]
          convert hprojection using 1 <;>
            simp only [one_mul, inner_sub_left] <;> ring)
        (mul_pos (by norm_num) data.affineScale.targetDelta_pos)
  have hratio : D / data.affineScale.targetDelta =
      data.Node7CubicalGlobalADProjectionFactor := by
    dsimp only [D, Node7CubicalGlobalADProjectionFactor]
    field_simp [data.affineScale.targetDelta_pos.ne']
  rw [hratio] at hraw
  simpa [heightCells, pureWZ2CenteredHeightCells_card,
    Node7CubicalGlobalADConstant] using hraw

end PureWZ2Node7AffineDiagonalPreparationData

end Kakeya.Assouad

end
