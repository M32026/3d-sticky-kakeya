import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64CommonWindow
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.CoaxialCoverGeometry
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.BoundedFamilyAssembly
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance

/-!
# Three-tube retubing for the exact Proposition 6.4 map

This is the ordinary-tube part of the mild-rescaling step in `wz2_64.tex`.
The exact affine image of one shaded short-slab piece has height in `[-1,1]`.
Its supporting line has positive vertical component strictly larger than
`2 / 3`, so the relevant axis interval has length strictly less than three
and is covered by three consecutive unit segments.

The construction uses the exact Proposition 6.4 map, including the shear at
the active height and the first-coordinate normalization.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The positively oriented exact-image direction. -/
def pureWZ2Proposition64RetubingDirection
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta) : Point3 :=
  wz1PaperDirection
    (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
      halfHeight normalization translation hhalfHeight hnormalization
      sourceTube)

/-- The two endpoints of the exact-image axis over the normalized height
window `[-1,1]`. -/
def pureWZ2Proposition64RetubingLowerPoint
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta) : Point3 :=
  wz1PaperAxisPointAtHeight
    (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
      halfHeight normalization translation hhalfHeight hnormalization
      sourceTube) (-1)

def pureWZ2Proposition64RetubingUpperPoint
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta) : Point3 :=
  wz1PaperAxisPointAtHeight
    (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
      halfHeight normalization translation hhalfHeight hnormalization
      sourceTube) 1

/-- The signed length of the image-axis interval over target heights
`[-1,1]`. -/
def pureWZ2Proposition64RetubingLength
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta) : ℝ :=
  2 / pureWZ2Proposition64RetubingDirection targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube 2

/-- The synchronized three child bases on the exact image line. -/
def pureWZ2Proposition64RetubingChildBase
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta)
    (slot : Fin 3) : Point3 :=
  let lower := pureWZ2Proposition64RetubingLowerPoint targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube
  let upper := pureWZ2Proposition64RetubingUpperPoint targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube
  let direction := pureWZ2Proposition64RetubingDirection targetDelta g
    slabCenter anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube
  Fin.cases lower
    (fun remaining : Fin 2 =>
      Fin.cases (lower + direction)
        (fun _ : Fin 1 => upper - direction) remaining) slot

/-- One ordinary target tube in the synchronized three-slot cover. -/
def pureWZ2Proposition64RetubingChildTube
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta)
    (slot : Fin 3) : Kakeya.DeltaTube targetDelta where
  base := pureWZ2Proposition64RetubingChildBase targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube slot
  direction := pureWZ2Proposition64RetubingDirection targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube
  direction_unit := wz1PaperDirection_norm _

@[simp] theorem pureWZ2Proposition64RetubingChildTube_direction
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta)
    (slot : Fin 3) :
    (pureWZ2Proposition64RetubingChildTube targetDelta g slabCenter
      anchorHeight halfHeight normalization translation hhalfHeight
      hnormalization sourceTube slot).direction =
    pureWZ2Proposition64RetubingDirection targetDelta g slabCenter
      anchorHeight halfHeight normalization translation hhalfHeight
      hnormalization sourceTube := rfl

/-- The oriented target direction has the same vertical component as the
absolute vertical component of the stored exact-image direction. -/
theorem pureWZ2Proposition64RetubingDirection_two
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta) :
    pureWZ2Proposition64RetubingDirection targetDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization sourceTube 2 =
      |(pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight hnormalization
          sourceTube).direction 2| := by
  unfold pureWZ2Proposition64RetubingDirection wz1PaperDirection
  split_ifs with hdirection
  · exact (abs_of_nonneg hdirection).symm
  · simp only [PiLp.neg_apply]
    exact (abs_of_neg (lt_of_not_ge hdirection)).symm

/-- The target-height interval has axial length strictly less than three. -/
theorem pureWZ2Proposition64RetubingLength_lt_three
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight : ℝ)
    (translation : Point3)
    {halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : halfHeight ≤ 1 / 20)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : (1 / 2 : ℝ) ≤ |sourceTube.direction 2|) :
    pureWZ2Proposition64RetubingLength targetDelta g slabCenter anchorHeight
      halfHeight normalization translation hhalfHeight (by linarith)
      sourceTube < 3 := by
  have hvertical := pureWZ2Proposition64ImageTube_vertical_two_thirds
    (targetDelta := targetDelta) g slabCenter anchorHeight translation hhalfHeight
    hhalfHeightSmall hnormalization hanchorSlope sourceTube hsourceVertical
  have hnormalizationPos : 0 < normalization := by
    linarith
  rw [pureWZ2Proposition64RetubingLength]
  have hdirection :
      pureWZ2Proposition64RetubingDirection targetDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        (by linarith) sourceTube 2 =
      |(pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight
          hnormalizationPos
          sourceTube).direction 2| :=
    pureWZ2Proposition64RetubingDirection_two targetDelta g slabCenter
      anchorHeight halfHeight normalization translation hhalfHeight
      (by linarith) sourceTube
  rw [hdirection]
  exact (div_lt_iff₀ (by linarith : 0 <
    |(pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
      halfHeight normalization translation hhalfHeight
      hnormalizationPos
      sourceTube).direction 2|)).2 (by nlinarith)

/-- The upper and lower normalized-height axis points differ by the signed
retubing length in the positive paper direction. -/
theorem pureWZ2Proposition64RetubingUpper_sub_lower
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight : ℝ)
    (translation : Point3)
    {halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta)
    (htargetVertical : (1 / 2 : ℝ) ≤
      |(pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight hnormalization
        sourceTube).direction 2|) :
    pureWZ2Proposition64RetubingUpperPoint targetDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization sourceTube -
      pureWZ2Proposition64RetubingLowerPoint targetDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization sourceTube =
      pureWZ2Proposition64RetubingLength targetDelta g slabCenter
          anchorHeight halfHeight normalization translation hhalfHeight
          hnormalization sourceTube •
        pureWZ2Proposition64RetubingDirection targetDelta g slabCenter
          anchorHeight halfHeight normalization translation hhalfHeight
          hnormalization sourceTube := by
  let target := pureWZ2Proposition64ImageTube targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube
  let direction := wz1PaperDirection target
  have hdirection : 0 < direction 2 := by
    rw [show direction 2 = |target.direction 2| by
      exact pureWZ2Proposition64RetubingDirection_two targetDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization sourceTube]
    linarith
  dsimp only [pureWZ2Proposition64RetubingUpperPoint,
    pureWZ2Proposition64RetubingLowerPoint,
    pureWZ2Proposition64RetubingLength,
    pureWZ2Proposition64RetubingDirection]
  unfold wz1PaperAxisPointAtHeight
  field_simp [hdirection.ne']
  module

/-- Difference formula for two prescribed-height points on one paper-oriented
axis. -/
theorem wz1PaperAxisPointAtHeight_eq_add
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (first second : ℝ) :
    wz1PaperAxisPointAtHeight tube second =
      wz1PaperAxisPointAtHeight tube first +
        ((second - first) / wz1PaperDirection tube 2) •
          wz1PaperDirection tube := by
  unfold wz1PaperAxisPointAtHeight
  module

/-- The prescribed-height parametrization recovers an axis point at its own
height. -/
theorem pureWZ2_wz1PaperAxisPointAtHeight_eq_of_mem_axis
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube)
    {point : Point3} (hpoint : point ∈ tubeAxisLine tube) :
    wz1PaperAxisPointAtHeight tube (point 2) = point := by
  have hdist := wz1Paper_axisPointAtHeight_dist_le_of_axis_point
    hline (point 2) 0 hpoint (by simp)
  exact dist_eq_zero.mp (le_antisymm (by simpa using hdist) dist_nonneg)

/-- Every exact-image shaded point is covered by the three synchronized
ordinary target tubes. -/
theorem pureWZ2Proposition64Retubing_three_child_cover
    {sourceDelta targetDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    (translation : Point3)
    {halfHeight normalization : ℝ}
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : halfHeight ≤ 1 / 20)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hradius : 180 * sourceDelta ≤ targetDelta)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    (htargetLine : WZ1PaperTubeInLineClass
      (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight (by linarith)
        sourceTube))
    (sourceSet : Set Point3)
    (hsourceSet : sourceSet ⊆
      wz1PaperTubeCarrier sourceTube ∩
        horizontalSlab (slabCenter - halfHeight)
          (slabCenter + halfHeight)) :
    pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation '' sourceSet ⊆
      ⋃ slot : Fin 3,
        (pureWZ2Proposition64RetubingChildTube targetDelta g slabCenter
          anchorHeight halfHeight normalization translation hhalfHeight
          (by linarith) sourceTube slot).carrier := by
  let target := pureWZ2Proposition64ImageTube targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    (by linarith) sourceTube
  let direction := pureWZ2Proposition64RetubingDirection targetDelta g
    slabCenter anchorHeight halfHeight normalization translation hhalfHeight
    (by linarith) sourceTube
  let lower := pureWZ2Proposition64RetubingLowerPoint targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    (by linarith) sourceTube
  let upper := pureWZ2Proposition64RetubingUpperPoint targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    (by linarith) sourceTube
  let length := pureWZ2Proposition64RetubingLength targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    (by linarith) sourceTube
  have htargetVerticalStrong :=
    pureWZ2Proposition64ImageTube_vertical_two_thirds (targetDelta := targetDelta) g slabCenter
      anchorHeight translation hhalfHeight hhalfHeightSmall hnormalization
      hanchorSlope sourceTube hsourceLine.vertical
  have htargetVertical : (1 / 2 : ℝ) ≤ |target.direction 2| := by
    dsimp only [target]
    linarith
  have hdirectionTwo : direction 2 = |target.direction 2| :=
    pureWZ2Proposition64RetubingDirection_two targetDelta g slabCenter
      anchorHeight halfHeight normalization translation hhalfHeight
      (by linarith) sourceTube
  have hdirectionPos : 0 < direction 2 := by rw [hdirectionTwo]; linarith
  have hlengthNonneg : 0 ≤ length := by
    dsimp only [length, pureWZ2Proposition64RetubingLength]
    positivity
  have hlengthLt : length < 3 := by
    exact pureWZ2Proposition64RetubingLength_lt_three targetDelta g slabCenter
      anchorHeight translation hhalfHeight hhalfHeightSmall hnormalization
      hanchorSlope sourceTube hsourceLine.vertical
  have hupperLower : upper - lower = length • direction := by
    exact pureWZ2Proposition64RetubingUpper_sub_lower targetDelta g slabCenter
      anchorHeight translation hhalfHeight (by linarith) sourceTube
      htargetVertical
  intro imagePoint himagePoint
  rcases himagePoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  have hsource := hsourceSet hsourcePoint
  let sourceAxisPoint :=
    wz1PaperAxisPointAtHeight sourceTube (sourcePoint 2)
  let targetAxisPoint :=
    pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
      normalization translation sourceAxisPoint
  have htargetAxis : targetAxisPoint ∈ tubeAxisLine target := by
    rw [show tubeAxisLine target =
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation '' tubeAxisLine sourceTube by
      exact pureWZ2Proposition64ImageTube_axisLine targetDelta g slabCenter
        anchorHeight translation hhalfHeight (by linarith) sourceTube]
    exact ⟨sourceAxisPoint,
      wz1PaperAxisPointAtHeight_mem_axis sourceTube (sourcePoint 2), rfl⟩
  have htargetHeight : targetAxisPoint 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    dsimp only [targetAxisPoint]
    rw [pureWZ2Proposition64TranslatedMap_apply_two, htranslationHeight]
    have hsourceAxisHeight : sourceAxisPoint 2 = sourcePoint 2 :=
      wz1PaperAxisPointAtHeight_coord_two hsourceLine (sourcePoint 2)
    rw [hsourceAxisHeight]
    simpa using pureWZ2Proposition64Map_height_mem g
      (slabCenter := slabCenter) (halfHeight := halfHeight)
      anchorHeight normalization hhalfHeight hsource.2
  have htargetAxisEq :
      wz1PaperAxisPointAtHeight target (targetAxisPoint 2) = targetAxisPoint :=
    pureWZ2_wz1PaperAxisPointAtHeight_eq_of_mem_axis
      htargetLine htargetAxis
  have haxisFromLower : targetAxisPoint = lower +
      ((targetAxisPoint 2 + 1) / direction 2) • direction := by
    calc
      targetAxisPoint =
          wz1PaperAxisPointAtHeight target (targetAxisPoint 2) :=
        htargetAxisEq.symm
      _ = wz1PaperAxisPointAtHeight target (-1) +
          ((targetAxisPoint 2 - (-1)) / wz1PaperDirection target 2) •
            wz1PaperDirection target :=
        wz1PaperAxisPointAtHeight_eq_add target (-1) (targetAxisPoint 2)
      _ = lower + ((targetAxisPoint 2 + 1) / direction 2) • direction := by
        simp only [target, lower, direction,
          pureWZ2Proposition64RetubingLowerPoint,
          pureWZ2Proposition64RetubingDirection]
        ring_nf
  let parameter := (targetAxisPoint 2 + 1) / direction 2
  have hparameter : 0 ≤ parameter ∧ parameter ≤ length := by
    constructor
    · exact div_nonneg (by linarith [htargetHeight.1]) hdirectionPos.le
    · dsimp only [parameter, length,
        pureWZ2Proposition64RetubingLength]
      apply (div_le_div_iff_of_pos_right hdirectionPos).2
      linarith [htargetHeight.2]
  have hsegment : targetAxisPoint ∈
      Kakeya.unitSegment lower direction ∪
        Kakeya.unitSegment (lower + direction) direction ∪
          Kakeya.unitSegment (upper - direction) direction := by
    exact three_segment_coverage length hlengthNonneg hlengthLt hupperLower
      ⟨parameter, hparameter.1, hparameter.2, haxisFromLower⟩
  have hdistance : dist
      (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation sourcePoint) targetAxisPoint ≤ targetDelta := by
    exact (pureWZ2Proposition64TranslatedMap_sameHeightAxis_dist_le
      hsourceDelta g slabCenter anchorHeight halfHeight normalization
      translation (by linarith) hanchorSlope sourceTube hsourceLine
      hsource.1).trans hradius
  rcases hsegment with hzeroOrOne | htwo
  · rcases hzeroOrOne with hzero | hone
    · refine Set.mem_iUnion.mpr ⟨(0 : Fin 3), ?_⟩
      exact Metric.mem_cthickening_of_dist_le _ targetAxisPoint targetDelta _
        hzero hdistance
    · refine Set.mem_iUnion.mpr ⟨(1 : Fin 3), ?_⟩
      exact Metric.mem_cthickening_of_dist_le _ targetAxisPoint targetDelta _
        hone hdistance
  · refine Set.mem_iUnion.mpr ⟨(2 : Fin 3), ?_⟩
    exact Metric.mem_cthickening_of_dist_le _ targetAxisPoint targetDelta _
      htwo hdistance

/-- Package the exact-map construction as the repository's standard
source-indexed three-tube cover. -/
def pureWZ2Proposition64ThreeTubeImageCover
    {sourceDelta targetDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    (translation : Point3)
    {halfHeight normalization : ℝ}
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : halfHeight ≤ 1 / 20)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hradius : 180 * sourceDelta ≤ targetDelta)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (hsourceSlab : ∀ source, sourceShading.carrier source ⊆
      horizontalSlab (slabCenter - halfHeight)
        (slabCenter + halfHeight))
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (htargetLine : WZ1PaperIsLineClass
      (pureWZ2Proposition64ImageFamily targetDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight (by linarith)
        sourceFamily)) :
    ThreeTubeImageCover (rho := targetDelta) sourceFamily
      (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
        halfHeight normalization translation)
      (fun source => sourceShading.carrier source) where
  tube source slot :=
    pureWZ2Proposition64RetubingChildTube targetDelta g slabCenter
      anchorHeight halfHeight normalization translation hhalfHeight
      (by linarith) (sourceFamily.tube source) slot
  covered source := by
    apply pureWZ2Proposition64Retubing_three_child_cover hsourceDelta g
      slabCenter anchorHeight translation htranslationHeight hhalfHeight
      hhalfHeightSmall hnormalization hanchorSlope hradius
      (sourceFamily.tube source) (hsourceLine source) (htargetLine source)
      (sourceShading.carrier source)
    intro point hpoint
    refine ⟨sourceShading.subset_body source hpoint, ?_⟩
    exact hsourceSlab source hpoint
  vertical source slot := by
    rw [pureWZ2Proposition64RetubingChildTube_direction,
      pureWZ2Proposition64RetubingDirection_two]
    have hstrong := pureWZ2Proposition64ImageTube_vertical_two_thirds
      (targetDelta := targetDelta) g slabCenter anchorHeight translation
      hhalfHeight hhalfHeightSmall hnormalization hanchorSlope
      (sourceFamily.tube source) (hsourceLine source).vertical
    have hhalfTwoThirds : (1 / 2 : ℝ) ≤ 2 / 3 := by norm_num
    exact hhalfTwoThirds.trans (by simpa only [abs_abs] using hstrong.le)

/-- Every child in the exact three-tube cover has exactly the affine image of
its source supporting axis. -/
theorem pureWZ2Proposition64RetubingChildTube_axisLine
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight : ℝ)
    (translation : Point3)
    {halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta)
    (htargetLine : WZ1PaperTubeInLineClass
      (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight hnormalization
        sourceTube))
    (slot : Fin 3) :
    tubeAxisLine
        (pureWZ2Proposition64RetubingChildTube targetDelta g slabCenter
          anchorHeight halfHeight normalization translation hhalfHeight
          hnormalization sourceTube slot) =
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation '' tubeAxisLine sourceTube := by
  have himageAxis := pureWZ2Proposition64ImageTube_axisLine targetDelta g
    slabCenter anchorHeight translation hhalfHeight hnormalization sourceTube
  let target := pureWZ2Proposition64ImageTube targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube
  let direction := pureWZ2Proposition64RetubingDirection targetDelta g
    slabCenter anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube
  let lower := pureWZ2Proposition64RetubingLowerPoint targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube
  let upper := pureWZ2Proposition64RetubingUpperPoint targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube
  have hlower : lower ∈ tubeAxisLine target :=
    wz1PaperAxisPointAtHeight_mem_axis target (-1)
  have hupper : upper ∈ tubeAxisLine target :=
    wz1PaperAxisPointAtHeight_mem_axis target 1
  have hbase :
      (pureWZ2Proposition64RetubingChildTube targetDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization sourceTube slot).base ∈ tubeAxisLine target := by
    fin_cases slot
    · change lower ∈ tubeAxisLine target
      exact hlower
    · change lower + direction ∈ tubeAxisLine target
      rcases wz1Paper_axis_exists_parameter htargetLine hlower with
        ⟨parameter, hparameter⟩
      have hmem :=
        wz1TubeAxisZeroPoint_add_smul_paperDirection_mem_axis
          target (parameter + 1)
      rw [hparameter]
      simpa only [direction, pureWZ2Proposition64RetubingDirection,
        add_smul, one_smul, add_assoc] using hmem
    · change upper - direction ∈ tubeAxisLine target
      rcases wz1Paper_axis_exists_parameter htargetLine hupper with
        ⟨parameter, hparameter⟩
      have hmem :=
        wz1TubeAxisZeroPoint_add_smul_paperDirection_mem_axis
          target (parameter - 1)
      have heq : upper - direction =
          wz1TubeAxisZeroPoint target +
            (parameter - 1) • wz1PaperDirection target := by
        rw [hparameter]
        dsimp only [direction, pureWZ2Proposition64RetubingDirection, target]
        module
      rw [heq]
      exact hmem
  have hbasePaper : ∃ baseParameter : ℝ,
      (pureWZ2Proposition64RetubingChildTube targetDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization sourceTube slot).base =
        wz1TubeAxisZeroPoint target +
          baseParameter • wz1PaperDirection target :=
    wz1Paper_axis_exists_parameter htargetLine hbase
  have hsame : tubeAxisLine
      (pureWZ2Proposition64RetubingChildTube targetDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization sourceTube slot) = tubeAxisLine target := by
    apply Set.Subset.antisymm
    · rintro point ⟨parameter, rfl⟩
      rcases hbasePaper with ⟨baseParameter, hbaseEq⟩
      have hmem :=
        wz1TubeAxisZeroPoint_add_smul_paperDirection_mem_axis
          target (baseParameter + parameter)
      rw [hbaseEq]
      simpa only [pureWZ2Proposition64RetubingChildTube_direction,
        pureWZ2Proposition64RetubingDirection, add_smul, add_assoc]
        using hmem
    · intro point hpoint
      rcases wz1Paper_axis_exists_parameter htargetLine hpoint with
        ⟨parameter, hparameter⟩
      rcases hbasePaper with ⟨baseParameter, hbaseEq⟩
      refine ⟨parameter - baseParameter, ?_⟩
      rw [hparameter, hbaseEq]
      simp only [pureWZ2Proposition64RetubingChildTube_direction,
        pureWZ2Proposition64RetubingDirection]
      module
  exact hsame.trans himageAxis

/-- Coaxial children inherit the fixed line class from the exact-image line. -/
theorem pureWZ2Proposition64RetubingChildTube_lineClass
    (targetDelta : ℝ) (g : ℝ → ℝ)
    (slabCenter anchorHeight : ℝ)
    (translation : Point3)
    {halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta)
    (htargetLine : WZ1PaperTubeInLineClass
      (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight hnormalization
        sourceTube))
    (slot : Fin 3) :
    WZ1PaperTubeInLineClass
      (pureWZ2Proposition64RetubingChildTube targetDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization sourceTube slot) := by
  let target := pureWZ2Proposition64ImageTube targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube
  let child := pureWZ2Proposition64RetubingChildTube targetDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
    hnormalization sourceTube slot
  have hchildDirection : child.direction = wz1PaperDirection target := rfl
  have hdirectionPos : 0 < child.direction 2 := by
    rw [hchildDirection]
    linarith [htargetLine.1]
  have hchildPaperDirection : wz1PaperDirection child = child.direction := by
    simp [wz1PaperDirection, hdirectionPos.le]
  have hchildVertical : (1 / 2 : ℝ) ≤ wz1PaperDirection child 2 := by
    rw [hchildPaperDirection, hchildDirection]
    exact htargetLine.1
  have hchildAxis : tubeAxisLine child = tubeAxisLine target := by
    have hchildExact := pureWZ2Proposition64RetubingChildTube_axisLine
      targetDelta g slabCenter anchorHeight translation hhalfHeight
      hnormalization sourceTube htargetLine slot
    have htargetExact := pureWZ2Proposition64ImageTube_axisLine targetDelta g
      slabCenter anchorHeight translation hhalfHeight hnormalization sourceTube
    exact hchildExact.trans htargetExact.symm
  have htargetZeroMem : wz1TubeAxisZeroPoint target ∈ tubeAxisLine child := by
    rw [hchildAxis]
    exact wz1TubeAxisZeroPoint_mem_axis target
  have htargetZeroHeight : wz1TubeAxisZeroPoint target 2 = 0 :=
    wz1TubeAxisZeroPoint_coord_two target htargetLine.vertical
  have hchildZero : wz1TubeAxisZeroPoint child = wz1TubeAxisZeroPoint target :=
    wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
      (by
        rw [hchildDirection]
        have hpaperAbs : |wz1PaperDirection target 2| =
            wz1PaperDirection target 2 := abs_of_nonneg (by linarith [htargetLine.1])
        rw [hpaperAbs]
        exact htargetLine.1)
      htargetZeroMem htargetZeroHeight
  refine ⟨hchildVertical, ?_, ?_⟩
  · rw [hchildZero]
    exact htargetLine.2.1
  · rw [hchildZero]
    exact htargetLine.2.2

/-- Coaxial strengthening of the exact Proposition 6.4 three-tube cover. -/
def pureWZ2Proposition64CoaxialThreeTubeImageCover
    {sourceDelta targetDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    (translation : Point3)
    {halfHeight normalization : ℝ}
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : halfHeight ≤ 1 / 20)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hradius : 180 * sourceDelta ≤ targetDelta)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (hsourceSlab : ∀ source, sourceShading.carrier source ⊆
      horizontalSlab (slabCenter - halfHeight)
        (slabCenter + halfHeight))
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (htargetLine : WZ1PaperIsLineClass
      (pureWZ2Proposition64ImageFamily targetDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight (by linarith)
        sourceFamily)) :
    CoaxialThreeTubeImageCover (rho := targetDelta) sourceFamily
      (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
        halfHeight normalization translation)
      (fun source => sourceShading.carrier source) where
  toThreeTubeImageCover := pureWZ2Proposition64ThreeTubeImageCover
    hsourceDelta g slabCenter anchorHeight translation htranslationHeight
    hhalfHeight hhalfHeightSmall hnormalization hanchorSlope hradius
    sourceFamily sourceShading hsourceSlab hsourceLine htargetLine
  coaxial source _hsource slot :=
    pureWZ2Proposition64RetubingChildTube_axisLine targetDelta g slabCenter
      anchorHeight translation hhalfHeight (by linarith)
      (sourceFamily.tube source) (htargetLine source) slot

/-- Every member of the flattened exact retubing lies in the fixed paper line
class. -/
theorem pureWZ2Proposition64ThreeTubeImageCover_lineClass
    {sourceDelta targetDelta : ℝ}
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (htargetLine : WZ1PaperIsLineClass
      (pureWZ2Proposition64ImageFamily targetDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight hnormalization
        sourceFamily))
    (cover : ThreeTubeImageCover (rho := targetDelta) sourceFamily
      (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
        halfHeight normalization translation)
      (fun source => sourceShading.carrier source))
    (hcoverTube : ∀ source slot, cover.tube source slot =
      pureWZ2Proposition64RetubingChildTube targetDelta g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
        hnormalization (sourceFamily.tube source) slot) :
    WZ1PaperIsLineClass
      (flattenThreeTubeImageCover sourceFamily
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation)
        (fun source => sourceShading.carrier source) cover) := by
  intro target
  let pair := finProdFinEquiv.symm target
  change WZ1PaperTubeInLineClass (cover.tube pair.1 pair.2)
  rw [hcoverTube pair.1 pair.2]
  exact pureWZ2Proposition64RetubingChildTube_lineClass targetDelta g
    slabCenter anchorHeight translation hhalfHeight hnormalization
    (sourceFamily.tube pair.1) (htargetLine pair.1) pair.2

/-- The flattened target index remembers its selected source parent and its
one of three synchronized axial slots. -/
def pureWZ2Proposition64ThreeTubeSourceParent
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (map : Point3 → Point3)
    (source : Fin sourceFamily.card → Set Point3)
    (cover : ThreeTubeImageCover (rho := targetDelta) sourceFamily map source) :
    Fin (flattenThreeTubeImageCover sourceFamily map source cover).card →
      Fin sourceFamily.card := fun target =>
  (finProdFinEquiv.symm target).1

/-- Safe whole-cell shading on the complete exact three-tube cover. -/
def pureWZ2Proposition64ThreeTubeSafeShading
    {sourceDelta targetDelta : ℝ}
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (cover : ThreeTubeImageCover (rho := targetDelta) sourceFamily
      (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
        halfHeight normalization translation)
      (fun source => sourceShading.carrier source)) :
    WZ1PaperTubeShading
      (flattenThreeTubeImageCover sourceFamily
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation)
        (fun source => sourceShading.carrier source) cover) where
  carrier target :=
    let parent := pureWZ2Proposition64ThreeTubeSourceParent
      sourceFamily
      (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
        halfHeight normalization translation)
      (fun source => sourceShading.carrier source) cover target
    pureWZ2Proposition64SafeCubicalCarrier targetDelta
      ((flattenThreeTubeImageCover sourceFamily
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation)
        (fun source => sourceShading.carrier source) cover).tube target)
      (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation '' sourceShading.carrier parent)
  measurable_carrier _target :=
    pureWZ2Proposition64SafeCubicalCarrier_measurable _ _ _
  subset_body _target :=
    pureWZ2Proposition64SafeCubicalCarrier_subset_tube _ _ _

/-- Geometric output of the exact three-tube stage, before weighted
essential-distinct cleanup. -/
structure PureWZ2Proposition64ThreeTubeRediscretizationData
    {sourceDelta targetDelta : ℝ}
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily) where
  cover : ThreeTubeImageCover (rho := targetDelta) sourceFamily
    (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
      halfHeight normalization translation)
    (fun source => sourceShading.carrier source)
  family : Kakeya.Streamlined.TubeFamily targetDelta :=
    flattenThreeTubeImageCover sourceFamily
      (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
        halfHeight normalization translation)
      (fun source => sourceShading.carrier source) cover
  family_eq : family = flattenThreeTubeImageCover sourceFamily
    (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
      halfHeight normalization translation)
    (fun source => sourceShading.carrier source) cover
  shading : WZ1PaperTubeShading family
  sourceParent : Fin family.card → Fin sourceFamily.card
  sourceParent_eq : ∀ target, sourceParent target =
    (finProdFinEquiv.symm (family_eq ▸ target)).1
  source_image_covered : ∀ source,
    pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation '' sourceShading.carrier source ⊆
      family.toBodyFamily.union
  axis_provenance : ∀ target,
    tubeAxisLine (family.tube target) =
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation ''
          tubeAxisLine (sourceFamily.tube (sourceParent target))
  line_class : WZ1PaperIsLineClass family
  cubical : WZ1PaperIsCubicalShading shading
  cell_meets_source_image : ∀ target point,
    point ∈ shading.carrier target →
      ∃ imagePoint ∈
          pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation ''
            sourceShading.carrier (sourceParent target),
        wz1PaperGridIndex targetDelta point =
          wz1PaperGridIndex targetDelta imagePoint
  slice_meets_source_image : ∀ target point,
    point ∈ shading.carrier target →
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, point 2 = z →
        ∃ imagePoint ∈ (
            pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation ''
              sourceShading.carrier (sourceParent target)) ∩
            wz1PaperGridCube targetDelta
              (wz1PaperGridIndex targetDelta point),
          imagePoint 2 = z
  shading_near_source_image : ∀ target,
    shading.carrier target ⊆
      Metric.cthickening (2 * targetDelta)
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation ''
          sourceShading.carrier (sourceParent target))

/-- Assemble the exact three-tube family and its safe cubical shading. -/
noncomputable def pureWZ2Proposition64ThreeTubeRediscretization
    {sourceDelta targetDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    (translation : Point3)
    {halfHeight normalization : ℝ}
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : halfHeight ≤ 1 / 20)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hradius : 180 * sourceDelta ≤ targetDelta)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (hsourceSlab : ∀ source, sourceShading.carrier source ⊆
      horizontalSlab (slabCenter - halfHeight)
        (slabCenter + halfHeight))
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (htargetLine : WZ1PaperIsLineClass
      (pureWZ2Proposition64ImageFamily targetDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight (by linarith)
        sourceFamily)) :
    PureWZ2Proposition64ThreeTubeRediscretizationData
      (targetDelta := targetDelta) g slabCenter
      anchorHeight halfHeight normalization translation sourceFamily
      sourceShading := by
  let cover := pureWZ2Proposition64ThreeTubeImageCover hsourceDelta g
    slabCenter anchorHeight translation htranslationHeight hhalfHeight
    hhalfHeightSmall hnormalization hanchorSlope hradius sourceFamily
    sourceShading hsourceSlab hsourceLine htargetLine
  let family := flattenThreeTubeImageCover sourceFamily
    (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
      normalization translation) (fun source => sourceShading.carrier source)
    cover
  let shading := pureWZ2Proposition64ThreeTubeSafeShading g slabCenter
    anchorHeight halfHeight normalization translation sourceFamily
    sourceShading cover
  exact
    { cover := cover
      family := family
      family_eq := rfl
      shading := shading
      sourceParent := pureWZ2Proposition64ThreeTubeSourceParent sourceFamily
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation)
        (fun source => sourceShading.carrier source) cover
      sourceParent_eq := fun _ => rfl
      source_image_covered := by
        intro source
        exact flattenThreeTubeImageCover_covered sourceFamily
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation)
          (fun source => sourceShading.carrier source) cover source
      axis_provenance := by
        intro target
        let pair := finProdFinEquiv.symm target
        change tubeAxisLine (cover.tube pair.1 pair.2) = _
        rw [show cover.tube pair.1 pair.2 =
          pureWZ2Proposition64RetubingChildTube targetDelta g slabCenter
            anchorHeight halfHeight normalization translation hhalfHeight
            (by linarith) (sourceFamily.tube pair.1) pair.2 by rfl]
        exact pureWZ2Proposition64RetubingChildTube_axisLine targetDelta g
          slabCenter anchorHeight translation hhalfHeight (by linarith)
          (sourceFamily.tube pair.1) (htargetLine pair.1) pair.2
      line_class := by
        apply pureWZ2Proposition64ThreeTubeImageCover_lineClass g slabCenter
          anchorHeight halfHeight normalization translation hhalfHeight
          (by linarith) sourceFamily sourceShading htargetLine cover
        intro source slot
        rfl
      cubical := by
        intro target point hpoint
        exact pureWZ2Proposition64SafeCubicalCarrier_isCubical
          _ _ _ point hpoint
      cell_meets_source_image := by
        intro target point hpoint
        exact pureWZ2Proposition64SafeCubicalCarrier_cell_meets_image
          _ _ _ hpoint
      slice_meets_source_image := by
        intro target point hpoint z hz hheight
        rcases Set.mem_iUnion.mp hpoint with ⟨cell, hpointCell⟩
        rcases cell.2.2.2 z hz ⟨point, hpointCell, hheight⟩ with
          ⟨imagePoint, ⟨hsourceImage, _himageCell⟩, himageHeight⟩
        have hindex : wz1PaperGridIndex targetDelta point = cell.1 :=
          (mem_wz1PaperGridCube _ _ _).mp hpointCell
        exact ⟨imagePoint, ⟨hsourceImage, by simpa [hindex] using _himageCell⟩,
          himageHeight⟩
      shading_near_source_image := by
        intro target
        exact pureWZ2Proposition64SafeCubicalCarrier_near_image
          _ _ (by linarith [hsourceDelta, hradius]) _ }

/-- The exact three-tube construction implements the common geometric
interface consumed by the final Proposition 6.4 assembly. -/
noncomputable def
    PureWZ2Proposition64ThreeTubeRediscretizationData.toActualImageData
    {sourceDelta targetDelta : ℝ}
    {g : SlopeFunction}
    {slabCenter anchorHeight halfHeight normalization : ℝ}
    {translation : Point3}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    (data : PureWZ2Proposition64ThreeTubeRediscretizationData
      (targetDelta := targetDelta) g slabCenter anchorHeight halfHeight
        normalization translation sourceFamily sourceShading)
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (htargetDelta : 0 < targetDelta)
    (hnormalized :
      (pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
        normalization).IsNormalized) :
    PureWZ2Proposition64ActualImageRediscretizationData
      (targetDelta := targetDelta) g slabCenter anchorHeight halfHeight
        normalization translation hhalfHeight hnormalization
        sourceFamily sourceShading where
  translation_height := htranslationHeight
  family := data.family
  shading := data.shading
  sourceParent := data.sourceParent
  axis_provenance := data.axis_provenance
  shading_near_source_image := data.shading_near_source_image
  cubical := data.cubical
  cell_meets_source_image := data.cell_meets_source_image
  projection_close := by
    intro z hz value hvalue
    rcases hvalue with
      ⟨point, ⟨⟨targetIndex, htarget⟩, hheight⟩, rfl⟩
    let sourceImage :=
      pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation ''
        sourceShading.carrier (data.sourceParent targetIndex)
    rcases data.slice_meets_source_image targetIndex point htarget z hz hheight with
      ⟨imagePoint, ⟨himagePoint, himageCell⟩, himageHeight⟩
    have hpointCell : point ∈ wz1PaperGridCube targetDelta
        (wz1PaperGridIndex targetDelta point) :=
      (mem_wz1PaperGridCube _ _ _).mpr rfl
    have himageDist : dist point imagePoint < 2 * targetDelta :=
      wz1_paper_grid_cube_diameter_lt_two_rho
        htargetDelta hpointCell himageCell
    have hslope :
        |pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
            normalization z| ≤ 1 := (hnormalized z hz).1
    have hsingleZero :
        ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp [Fin.sum_univ_succ]
    have hsingleOne :
        ‖EuclideanSpace.single (1 : Fin 3) (1 : ℝ)‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp [Fin.sum_univ_succ]
    have hdirection :
        ‖globalGrainDirection
            (pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
              normalization z)‖ ≤ 2 := by
      unfold globalGrainDirection
      calc
        ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
            pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
                normalization z •
              EuclideanSpace.single (1 : Fin 3) (1 : ℝ)‖ ≤
            ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ +
              ‖pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
                  normalization z •
                EuclideanSpace.single (1 : Fin 3) (1 : ℝ)‖ := norm_add_le _ _
        _ = 1 + |pureWZ2Proposition64Slope g slabCenter anchorHeight
            halfHeight normalization z| := by
          rw [hsingleZero, norm_smul, Real.norm_eq_abs,
            hsingleOne, mul_one]
        _ ≤ 2 := by linarith
    have hclose :
        |inner ℝ point
              (globalGrainDirection
                (pureWZ2Proposition64Slope g slabCenter anchorHeight
                  halfHeight normalization z)) -
            inner ℝ imagePoint
              (globalGrainDirection
                (pureWZ2Proposition64Slope g slabCenter anchorHeight
                  halfHeight normalization z))| ≤
          4 * targetDelta := by
      rw [← inner_sub_left]
      calc
        |inner ℝ (point - imagePoint)
            (globalGrainDirection
              (pureWZ2Proposition64Slope g slabCenter anchorHeight
                halfHeight normalization z))| ≤
            ‖point - imagePoint‖ *
              ‖globalGrainDirection
                (pureWZ2Proposition64Slope g slabCenter anchorHeight
                  halfHeight normalization z)‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ dist point imagePoint * 2 := by
          rw [dist_eq_norm]
          gcongr
        _ ≤ 4 * targetDelta := by linarith
    refine ⟨inner ℝ imagePoint
        (globalGrainDirection
          (pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
            normalization z)), ?_, hclose⟩
    refine ⟨imagePoint, ⟨?_, himageHeight⟩, rfl⟩
    rcases himagePoint with ⟨sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, ⟨data.sourceParent targetIndex, hsourcePoint⟩, rfl⟩

/-- Attach the exact three-tube retubing to the common horizontal window. -/
noncomputable def PureWZ2Proposition64CommonWindowData.toThreeTubeCover
    {sourceDelta targetDelta : ℝ}
    {g : SlopeFunction}
    {slabCenter anchorHeight halfHeight normalization : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    (common : PureWZ2Proposition64CommonWindowData g slabCenter anchorHeight
      halfHeight normalization sourceFamily sourceShading)
    (hsourceDelta : 0 < sourceDelta)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : halfHeight ≤ 1 / 20)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hradius : 180 * sourceDelta ≤ targetDelta)
    (hsourceSlab : ∀ source, sourceShading.carrier source ⊆
      horizontalSlab (slabCenter - halfHeight)
        (slabCenter + halfHeight))
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (htargetDelta : 0 < targetDelta)
    (hnormalized :
      (pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
        normalization).IsNormalized) :
    CoaxialThreeTubeImageCover (rho := targetDelta)
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        sourceFamily common.selected).family
      (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
        halfHeight normalization common.translation)
      (fun source =>
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            sourceFamily common.selected) sourceShading).carrier source) := by
  let selectedSource :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset sourceFamily common.selected
  let selectedShading : WZ1PaperTubeShading selectedSource.family :=
    restrictPaperShading selectedSource sourceShading
  have hselectedSlab : ∀ source, selectedShading.carrier source ⊆
      horizontalSlab (slabCenter - halfHeight)
        (slabCenter + halfHeight) := by
    intro source point hpoint
    exact hsourceSlab (selectedSource.embedding source) hpoint
  have hselectedLine : WZ1PaperIsLineClass selectedSource.family :=
    hsourceLine.subfamily selectedSource
  let image := common.toImage hsourceLine hhalfHeight hhalfHeightSmall
    (by linarith) hanchorSlope htargetDelta hnormalized
  have hselectedTargetLine : WZ1PaperIsLineClass
      (pureWZ2Proposition64ImageFamily targetDelta g slabCenter anchorHeight
        halfHeight normalization common.translation hhalfHeight (by linarith)
        selectedSource.family) := by
    exact image.line_class
  exact pureWZ2Proposition64CoaxialThreeTubeImageCover
    hsourceDelta g slabCenter anchorHeight common.translation
    common.translation_height hhalfHeight hhalfHeightSmall hnormalization
    hanchorSlope hradius selectedSource.family selectedShading hselectedSlab
    hselectedLine hselectedTargetLine

/-- The prepared Proposition 6.4 slab supplies the exact source-support
hypothesis needed by the three-tube construction. -/
theorem PureWZ2Proposition64PreparedData.shading_subset_shortSlab
    {sigma inputLoss sourceDelta finalLoss hierarchyLoss rawLoss
      extensionConstant : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta}
    {hierarchy : PureWZ2LocallyLinearHierarchyData
      source finalLoss hierarchyLoss}
    {raw : PureWZ2RawC2GlobalGrainData hierarchy.shading sigma
      (Kakeya.realRpowENN sourceDelta (-finalLoss)) rawLoss
        extensionConstant}
    (prepared : PureWZ2Proposition64PreparedData hierarchy raw) :
    ∀ sourceIndex, prepared.slab.shading.carrier sourceIndex ⊆
      horizontalSlab
        (prepared.slab.center - prepared.slab.halfHeight)
        (prepared.slab.center + prepared.slab.halfHeight) := by
  intro sourceIndex point hpoint
  rw [prepared.slab.carrier_eq] at hpoint
  simpa [prepared.slab.slab_eq] using hpoint.2

/-- Start the exact ordinary retubing directly from prepared data and its
common-window selection. -/
noncomputable def PureWZ2Proposition64PreparedData.toThreeTubeRediscretization
    {sigma inputLoss sourceDelta finalLoss hierarchyLoss rawLoss
      extensionConstant targetDelta : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta}
    {hierarchy : PureWZ2LocallyLinearHierarchyData
      source finalLoss hierarchyLoss}
    {raw : PureWZ2RawC2GlobalGrainData hierarchy.shading sigma
      (Kakeya.realRpowENN sourceDelta (-finalLoss)) rawLoss
        extensionConstant}
    (prepared : PureWZ2Proposition64PreparedData hierarchy raw)
    (common : PureWZ2Proposition64CommonWindowData
      prepared.restrictedRaw.slope prepared.slab.center
      prepared.slab.anchorHeight prepared.slab.halfHeight
      prepared.normalization source.family prepared.slab.shading)
    (hhalfHeightSmall : prepared.slab.halfHeight ≤ 1 / 20)
    (hnormalization : 9 ≤ prepared.normalization)
    (htargetDelta : 0 < targetDelta)
    (hradius : 180 * sourceDelta ≤ targetDelta) :
    PureWZ2Proposition64ThreeTubeRediscretizationData
      (targetDelta := targetDelta) prepared.restrictedRaw.slope
      prepared.slab.center prepared.slab.anchorHeight prepared.slab.halfHeight
      prepared.normalization common.translation
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        source.family common.selected).family
      (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          source.family common.selected) prepared.slab.shading) := by
  let selectedSource :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset source.family common.selected
  let selectedShading : WZ1PaperTubeShading selectedSource.family :=
    restrictPaperShading selectedSource prepared.slab.shading
  let image := common.toImage source.line_class prepared.slab.halfHeight_pos
    hhalfHeightSmall prepared.normalization_one
    prepared.normalized.anchor_value_bound htargetDelta
    (by simpa only [prepared.normalized.slope_eq] using
      prepared.normalized.normalized)
  apply pureWZ2Proposition64ThreeTubeRediscretization
    source.extremal.delta_pos prepared.restrictedRaw.slope
    prepared.slab.center prepared.slab.anchorHeight common.translation
    common.translation_height prepared.slab.halfHeight_pos hhalfHeightSmall
    hnormalization prepared.normalized.anchor_value_bound hradius
    selectedSource.family selectedShading
  · intro sourceIndex point hpoint
    exact prepared.shading_subset_shortSlab
      (selectedSource.embedding sourceIndex) hpoint
  · exact source.line_class.subfamily selectedSource
  have hline := image.line_class
  change WZ1PaperIsLineClass
    (pureWZ2Proposition64ImageFamily targetDelta prepared.restrictedRaw.slope
      prepared.slab.center prepared.slab.anchorHeight prepared.slab.halfHeight
      prepared.normalization common.translation prepared.slab.halfHeight_pos
      (by linarith)
      (Kakeya.Streamlined.TubeSubfamily.fromFinset source.family
        common.selected).family) at hline
  simpa only [selectedSource] using hline

/-- The prepared common-window output supplies an exact three-tube ordinary
rediscretization whenever the chosen target radius pays the fixed transverse
error. -/
theorem PureWZ2Proposition64PreparedData.existsThreeTubeRediscretization
    {sigma inputLoss sourceDelta finalLoss hierarchyLoss rawLoss
      extensionConstant targetDelta : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta}
    {hierarchy : PureWZ2LocallyLinearHierarchyData
      source finalLoss hierarchyLoss}
    {raw : PureWZ2RawC2GlobalGrainData hierarchy.shading sigma
      (Kakeya.realRpowENN sourceDelta (-finalLoss)) rawLoss
        extensionConstant}
    (prepared : PureWZ2Proposition64PreparedData hierarchy raw)
    (hhalfHeightSmall : prepared.slab.halfHeight ≤ 1 / 20)
    (hnormalization : 9 ≤ prepared.normalization)
    (htargetDelta : 0 < targetDelta)
    (hradius : 180 * sourceDelta ≤ targetDelta) :
    Nonempty
      (Σ common : PureWZ2Proposition64CommonWindowData
          prepared.restrictedRaw.slope prepared.slab.center
          prepared.slab.anchorHeight prepared.slab.halfHeight
          prepared.normalization source.family prepared.slab.shading,
        PureWZ2Proposition64ThreeTubeRediscretizationData
          (targetDelta := targetDelta) prepared.restrictedRaw.slope
          prepared.slab.center prepared.slab.anchorHeight
          prepared.slab.halfHeight prepared.normalization common.translation
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            source.family common.selected).family
          (restrictPaperShading
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              source.family common.selected) prepared.slab.shading)) := by
  rcases prepared.selectCommonWindow hnormalization with ⟨common⟩
  exact ⟨⟨common, prepared.toThreeTubeRediscretization common
    hhalfHeightSmall hnormalization htargetDelta hradius⟩⟩

end Kakeya.Assouad

end
