import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalPlaneExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffinePreimageBallCover

/-!
# Finite source-ball covers for the direct half-offset terminal

This module packages the two successive affine maps from the ambient
half-offset source to the actual exact terminal.  Its difference map is the
offset-projective total linear map, so the sharp finite preimage-ball cover
applies at every occupied exact terminal anchor.
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

/-- The total affine point map from the ambient half-offset source to the
actual terminal coordinates. -/
def totalAffineMap (terminal : commonSource.TerminalGeometry) :
    Point3 → Point3 :=
  fun point =>
    let source := commonSource.halfOffsetAssembly.horizontalSource
    pureWZ2LineClassNormalizationMap terminal.box.center
      pureWZ2DirectHalfOffsetTerminalLambda
      (anisotropicCenteredRescalingMap
        (pureWZ2DirectGeometrySlope source) source.c source.d source.m
        (pureWZ2DirectAnisotropicCenter terminal.retubing.popular) point)

/-- Differences of the total affine map are exactly the offset-diagonal
linear map used by the finite-cover theorem. -/
theorem totalAffineMap_sub (terminal : commonSource.TerminalGeometry)
    (first second : Point3) :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    totalAffineMap commonSource terminal first -
        totalAffineMap commonSource terminal second =
      pureWZ2OffsetProjectiveTotalLinear
        (PureWZ2HalfOffsetHorizontalSourceData.offset source)
        (source.m * (source.d - source.c) / 2)
        (2 / (source.d - source.c))
        pureWZ2DirectHalfOffsetTerminalLambda (first - second) := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  have hlineClass (firstImage secondImage : Point3) :
      pureWZ2LineClassNormalizationMap terminal.box.center
          pureWZ2DirectHalfOffsetTerminalLambda firstImage -
        pureWZ2LineClassNormalizationMap terminal.box.center
          pureWZ2DirectHalfOffsetTerminalLambda secondImage =
      pureWZ2LineClassNormalizationLinear
        pureWZ2DirectHalfOffsetTerminalLambda
        (firstImage - secondImage) := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2LineClassNormalizationMap,
        pureWZ2LineClassNormalizationLinear, point3] <;> ring
  change pureWZ2LineClassNormalizationMap terminal.box.center
        pureWZ2DirectHalfOffsetTerminalLambda
        (anisotropicCenteredRescalingMap
          (pureWZ2DirectGeometrySlope source) source.c source.d source.m
          (pureWZ2DirectAnisotropicCenter terminal.retubing.popular) first) -
      pureWZ2LineClassNormalizationMap terminal.box.center
        pureWZ2DirectHalfOffsetTerminalLambda
        (anisotropicCenteredRescalingMap
          (pureWZ2DirectGeometrySlope source) source.c source.d source.m
          (pureWZ2DirectAnisotropicCenter terminal.retubing.popular) second) = _
  rw [hlineClass, anisotropicCenteredRescalingMap_sub]
  rw [← pureWZ2OffsetProjectiveTotalLinear_eq_lineClass_dPhi]
  congr 1

/-- The two affine equivalences making up the total terminal map show that it
is injective on the whole ambient source space. -/
theorem totalAffineMap_injective (terminal : commonSource.TerminalGeometry) :
    Function.Injective (totalAffineMap commonSource terminal) := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  intro first second heq
  apply (anisotropicCenteredRescalingAffineEquiv
    (pureWZ2DirectGeometrySlope source) source.c source.d source.m
    (pureWZ2DirectAnisotropicCenter terminal.retubing.popular) source.ordered
    source.slopeScale_pos).injective
  rw [anisotropicCenteredRescalingAffineEquiv_apply,
    anisotropicCenteredRescalingAffineEquiv_apply]
  apply (pureWZ2LineClassNormalizationAffineEquiv terminal.box.center
    pureWZ2DirectHalfOffsetTerminalLambda
    pureWZ2DirectHalfOffsetTerminalLambda_pos).injective
  rw [pureWZ2LineClassNormalizationAffineEquiv_apply,
    pureWZ2LineClassNormalizationAffineEquiv_apply]
  exact heq

/-- The canonical source point of an actual exact terminal point is a right
inverse of the total affine map. -/
@[simp] theorem totalAffineMap_halfOffsetTerminalSourcePoint
    (terminal : commonSource.TerminalGeometry)
    (exactPoint : {point : Point3 // point ∈ terminal.exactShading.union}) :
    totalAffineMap commonSource terminal
        (commonSource.halfOffsetTerminalSourcePoint terminal.retubing
          terminal.box pureWZ2DirectHalfOffsetTerminalLambda_pos
          (exactSetPoint commonSource terminal exactPoint)) =
      exactPoint := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  change pureWZ2LineClassNormalizationMap terminal.box.center
      pureWZ2DirectHalfOffsetTerminalLambda
      (anisotropicCenteredRescalingMap
        (pureWZ2DirectGeometrySlope source) source.c source.d source.m
        (pureWZ2DirectAnisotropicCenter terminal.retubing.popular)
        (terminal.retubing.raw.exactSourcePoint
          (commonSource.halfOffsetTerminalRawPoint terminal.retubing
            terminal.box pureWZ2DirectHalfOffsetTerminalLambda_pos
            (exactSetPoint commonSource terminal exactPoint)))) = exactPoint
  rw [terminal.retubing.raw.map_exactSourcePoint]
  exact commonSource.halfOffsetTerminal_map_rawPoint terminal.retubing
    terminal.box pureWZ2DirectHalfOffsetTerminalLambda_pos
      (exactSetPoint commonSource terminal exactPoint)

/-- The ambient source subset which maps into the actual exact terminal.
The explicit intersection records that it belongs to the genuine half-offset
source shading rather than merely to the ambient space. -/
def exactTerminalSourceSet (terminal : commonSource.TerminalGeometry) :
    Set Point3 :=
  commonSource.halfOffsetAssembly.horizontalSource.sourceShading.union ∩
    totalAffineMap commonSource terminal ⁻¹' terminal.exactShading.union

theorem exactTerminalSourceSet_subset_sourceShading
    (terminal : commonSource.TerminalGeometry) :
    exactTerminalSourceSet commonSource terminal ⊆
      commonSource.halfOffsetAssembly.horizontalSource.sourceShading.union :=
  inter_subset_left

/-- On the explicit source subset of the exact terminal, the canonical
terminal-source construction is literally the original ambient source point.
-/
@[simp] theorem halfOffsetTerminalSourcePoint_totalAffineMap
    (terminal : commonSource.TerminalGeometry)
    (sourcePoint : Point3)
    (hsourcePoint : sourcePoint ∈
      exactTerminalSourceSet commonSource terminal) :
    commonSource.halfOffsetTerminalSourcePoint terminal.retubing terminal.box
        pureWZ2DirectHalfOffsetTerminalLambda_pos
        (exactSetPoint commonSource terminal
          (⟨totalAffineMap commonSource terminal sourcePoint, hsourcePoint.2⟩ :
            {point : Point3 // point ∈ terminal.exactShading.union})) =
      (⟨sourcePoint, hsourcePoint.1⟩ :
        {point : Point3 // point ∈
          commonSource.halfOffsetAssembly.horizontalSource.sourceShading.union}) := by
  apply Subtype.ext
  apply totalAffineMap_injective commonSource terminal
  exact totalAffineMap_halfOffsetTerminalSourcePoint commonSource terminal
    (⟨totalAffineMap commonSource terminal sourcePoint, hsourcePoint.2⟩ :
      {point : Point3 // point ∈ terminal.exactShading.union})

/-- The actual exact terminal is precisely the image of its explicit ambient
half-offset source subset. -/
theorem exactShading_union_eq_totalAffineMap_image
    (terminal : commonSource.TerminalGeometry) :
    terminal.exactShading.union =
      totalAffineMap commonSource terminal ''
        exactTerminalSourceSet commonSource terminal := by
  apply Set.Subset.antisymm
  · intro target htarget
    let exactPoint : {point : Point3 // point ∈ terminal.exactShading.union} :=
      ⟨target, htarget⟩
    let sourcePoint : Point3 :=
      commonSource.halfOffsetTerminalSourcePoint terminal.retubing terminal.box
        pureWZ2DirectHalfOffsetTerminalLambda_pos
        (exactSetPoint commonSource terminal exactPoint)
    refine ⟨sourcePoint, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact (commonSource.halfOffsetTerminalSourcePoint terminal.retubing
          terminal.box pureWZ2DirectHalfOffsetTerminalLambda_pos
          (exactSetPoint commonSource terminal exactPoint)).property
      · change totalAffineMap commonSource terminal sourcePoint ∈
          terminal.exactShading.union
        rw [show totalAffineMap commonSource terminal sourcePoint = target by
          exact totalAffineMap_halfOffsetTerminalSourcePoint commonSource
            terminal exactPoint]
        exact htarget
    · exact totalAffineMap_halfOffsetTerminalSourcePoint commonSource terminal
        exactPoint
  · rintro target ⟨sourcePoint, hsourcePoint, rfl⟩
    exact hsourcePoint.2

/-- Intersecting the actual exact terminal with a target ball is exactly the
image of the explicit source subset whose total-map image lies in that ball.
The anchor is arbitrary, so in particular it may be any occupied exact
terminal point. -/
theorem exactShading_union_inter_closedBall_eq_totalAffineMap_image
    (terminal : commonSource.TerminalGeometry) (anchor : Point3) (radius : ℝ) :
    terminal.exactShading.union ∩ Metric.closedBall anchor radius =
      totalAffineMap commonSource terminal ''
        (exactTerminalSourceSet commonSource terminal ∩
          totalAffineMap commonSource terminal ⁻¹'
            Metric.closedBall anchor radius) := by
  apply Set.Subset.antisymm
  · rintro target ⟨htargetExact, htargetBall⟩
    rw [exactShading_union_eq_totalAffineMap_image commonSource terminal]
      at htargetExact
    rcases htargetExact with ⟨sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, ⟨hsourcePoint, htargetBall⟩, rfl⟩
  · rintro target ⟨sourcePoint, ⟨hsourcePoint, hsourceBall⟩, rfl⟩
    exact ⟨hsourcePoint.2, hsourceBall⟩

/-- A sharp finite cover of the total-map preimage of a ball anchored at an
actual exact terminal point. -/
theorem totalAffineMap_exact_preimage_closedBall_sharp_finite_cover
    (terminal : commonSource.TerminalGeometry)
    (exactPoint : {point : Point3 // point ∈ terminal.exactShading.union})
    {radius : ℝ} (hradius : 0 < radius) :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    let b := source.m * (source.d - source.c) / 2
    ∃ centers : Finset Point3,
      (centers.card : ℝ) ≤ 9 * b⁻¹ ∧
      totalAffineMap commonSource terminal ⁻¹'
          Metric.closedBall (exactPoint : Point3) radius ⊆
        ⋃ sourceCenter ∈ centers,
          Metric.closedBall sourceCenter (7 * radius / 4) := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let a := PureWZ2HalfOffsetHorizontalSourceData.offset source
  let b := source.m * (source.d - source.c) / 2
  let S := 2 / (source.d - source.c)
  let center : Point3 :=
    commonSource.halfOffsetTerminalSourcePoint terminal.retubing terminal.box
      pureWZ2DirectHalfOffsetTerminalLambda_pos
      (exactSetPoint commonSource terminal exactPoint)
  have ha : |a| ≤ 1 / 2 :=
    PureWZ2HalfOffsetHorizontalSourceData.offset_abs_le
      commonSource.halfOffsetAssembly_compatibility
  have hlengthPos : 0 < source.d - source.c := sub_pos.mpr source.ordered
  have hb : 0 < b := by
    dsimp only [b]
    exact div_pos (mul_pos source.slopeScale_pos hlengthPos) (by norm_num)
  have hlengthUpper : source.d - source.c ≤ 2 := by
    linarith [source.left_mem, source.right_mem]
  have hb_one : b ≤ 1 := by
    dsimp only [b]
    have hproduct := mul_le_mul source.slopeScale_le_one hlengthUpper
      hlengthPos.le (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hS : 1 ≤ S := by
    dsimp only [S]
    exact (le_div_iff₀ hlengthPos).2 (by simpa using hlengthUpper)
  have hcenter : totalAffineMap commonSource terminal center = exactPoint :=
    totalAffineMap_halfOffsetTerminalSourcePoint commonSource terminal exactPoint
  have hdifference : ∀ point,
      totalAffineMap commonSource terminal point -
          totalAffineMap commonSource terminal center =
        pureWZ2OffsetProjectiveTotalLinear a b S
          pureWZ2DirectHalfOffsetTerminalLambda (point - center) := by
    intro point
    exact totalAffineMap_sub commonSource terminal point center
  have hcover :=
    pureWZ2OffsetProjectiveTotal_difference_preimage_closedBall_sharp_finite_cover
      (F := totalAffineMap commonSource terminal) ha hb hb_one hS
      pureWZ2DirectHalfOffsetTerminalLambda_one_le hradius center hdifference
  rw [hcenter] at hcover
  exact hcover

/-- Square-root-scale specialization at an actual exact terminal anchor. -/
theorem totalAffineMap_exact_preimage_sqrtBall_sharp_finite_cover
    (terminal : commonSource.TerminalGeometry)
    (exactPoint : {point : Point3 // point ∈ terminal.exactShading.union})
    {rho : ℝ} (hrho : 0 < rho) :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    let b := source.m * (source.d - source.c) / 2
    ∃ centers : Finset Point3,
      (centers.card : ℝ) ≤ 9 * b⁻¹ ∧
      totalAffineMap commonSource terminal ⁻¹'
          Metric.closedBall (exactPoint : Point3) (Real.sqrt rho) ⊆
        ⋃ sourceCenter ∈ centers,
          Metric.closedBall sourceCenter (7 * Real.sqrt rho / 4) := by
  exact totalAffineMap_exact_preimage_closedBall_sharp_finite_cover
    commonSource terminal exactPoint (Real.sqrt_pos.2 hrho)

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
