import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicCenteredMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicDirectionBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RescaledZeroPointBounds

/-!
# Canonical paper tube on an exact triangular image line

The stored unit segment is centered at target height zero.  The supporting
line is exactly the image of the source supporting line under the affine map
from Proposition 6.5.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The exact image of the source axis at the midpoint of the selected band. -/
def anisotropicPaperTargetCenter
    (g : SlopeFunction) (c d m : ℝ)
    (center : Point3)
    {sourceDelta : ℝ} (source : Kakeya.DeltaTube sourceDelta) : Point3 :=
  anisotropicCenteredRescalingMap g c d m center
    (wz1PaperAxisPointAtHeight source (c + (d - c) / 2))

/-- A target tube centered at height zero on the exact image line. -/
def anisotropicPaperTargetTube
    (g : SlopeFunction) (c d m : ℝ) (center : Point3) (targetDelta : ℝ)
    (hcd : c < d) (hm : 0 < m)
    {sourceDelta : ℝ} (source : Kakeya.DeltaTube sourceDelta) :
    Kakeya.DeltaTube targetDelta where
  base := anisotropicPaperTargetCenter g c d m center source -
    (1 / 2 : ℝ) • anisotropicAnchoredDirection g c d m source
  direction := anisotropicAnchoredDirection g c d m source
  direction_unit := anisotropicAnchoredDirection_unit g hcd hm source

@[simp] theorem anisotropicPaperTargetTube_direction
    (g : SlopeFunction) {c d m targetDelta sourceDelta : ℝ}
    (center : Point3)
    (hcd : c < d) (hm : 0 < m)
    (source : Kakeya.DeltaTube sourceDelta) :
    (anisotropicPaperTargetTube g c d m center targetDelta hcd hm source).direction =
      anisotropicAnchoredDirection g c d m source := rfl

theorem anisotropicPaperTargetCenter_coord_two
    (g : SlopeFunction) {c d m sourceDelta : ℝ}
    (center : Point3) (hcenter : center 2 = c + (d - c) / 2)
    (hcd : c < d) (source : Kakeya.DeltaTube sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source) :
    anisotropicPaperTargetCenter g c d m center source 2 = 0 := by
  rw [anisotropicPaperTargetCenter]
  unfold anisotropicCenteredRescalingMap
  simp only [PiLp.sub_apply, anisotropicRescalingMap_coord]
  have hpointThree : (point3
      (center 0 + g (c + (d - c) / 2) * center 1) 0 0) 2 = 0 := by
    simp [point3]
  rw [hpointThree]
  rw [wz1PaperAxisPointAtHeight_coord_two hsource]
  field_simp [(sub_pos.mpr hcd).ne']
  ring

theorem anisotropicPaperTargetCenter_coord_one
    (g : SlopeFunction) {c d m sourceDelta : ℝ}
    (center : Point3)
    (source : Kakeya.DeltaTube sourceDelta) :
    anisotropicPaperTargetCenter g c d m center source 1 =
      (m * (d - c) / 2) *
        (wz1PaperAxisPointAtHeight source (c + (d - c) / 2) 1) := by
  simp [anisotropicPaperTargetCenter, anisotropicCenteredRescalingMap,
    anisotropicRescalingMap, point3]

theorem anisotropicPaperTargetTube_midpoint
    (g : SlopeFunction) {c d m targetDelta sourceDelta : ℝ}
    (center : Point3)
    (hcd : c < d) (hm : 0 < m)
    (source : Kakeya.DeltaTube sourceDelta) :
    wz2PaperTubeMidpoint
        (anisotropicPaperTargetTube g c d m center targetDelta hcd hm source) =
      anisotropicPaperTargetCenter g c d m center source := by
  simp [wz2PaperTubeMidpoint, anisotropicPaperTargetTube]

theorem anisotropicPaperTargetTube_axis
    (g : SlopeFunction) {c d m targetDelta sourceDelta : ℝ}
    (center : Point3)
    (hcd : c < d) (hm : 0 < m)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source) :
    tubeAxisLine
        (anisotropicPaperTargetTube g c d m center targetDelta hcd hm source) =
      anisotropicCenteredRescalingMap g c d m center '' tubeAxisLine source := by
  let sourceCenter :=
    wz1PaperAxisPointAtHeight source (c + (d - c) / 2)
  let targetCenter := anisotropicPaperTargetCenter g c d m center source
  let imageDirection := dPhiLin g c d m (wz1PaperDirection source)
  let targetDirection := anisotropicAnchoredDirection g c d m source
  have himageDirection : imageDirection ≠ 0 := by
    intro hzero
    have hsourceDirection : wz1PaperDirection source ≠ 0 := by
      intro hsourceZero
      have hnorm := congrArg norm hsourceZero
      rw [wz1PaperDirection_norm source, norm_zero] at hnorm
      norm_num at hnorm
    apply hsourceDirection
    apply dPhiLin_injective g c d m hcd hm
    rw [show dPhiLin g c d m (wz1PaperDirection source) =
        imageDirection by rfl, hzero]
    simp [dPhiLin, point3]
  have himageNorm : 0 < ‖imageDirection‖ :=
    norm_pos_iff.mpr himageDirection
  have hsourceCenter : sourceCenter ∈ tubeAxisLine source :=
    wz1PaperAxisPointAtHeight_mem_axis source _
  have hsourceLine : tubeAxisLine source =
      {point | ∃ parameter : ℝ,
        point = sourceCenter + parameter • wz1PaperDirection source} := by
    ext point
    constructor
    · intro hpoint
      rcases wz1Paper_axis_exists_parameter hsource hpoint with
        ⟨parameter, hparameter⟩
      rcases wz1Paper_axis_exists_parameter hsource hsourceCenter with
        ⟨centerParameter, hcenterParameter⟩
      refine ⟨parameter - centerParameter, ?_⟩
      rw [hparameter, hcenterParameter]
      module
    · rintro ⟨parameter, rfl⟩
      rcases wz1Paper_axis_exists_parameter hsource hsourceCenter with
        ⟨centerParameter, hcenterParameter⟩
      rw [hcenterParameter]
      have hmem := wz1TubeAxisZeroPoint_add_smul_paperDirection_mem_axis
        source (centerParameter + parameter)
      convert hmem using 1 <;> module
  ext target
  constructor
  · rintro ⟨parameter, rfl⟩
    rw [hsourceLine]
    refine ⟨sourceCenter +
        ((parameter - 1 / 2) / ‖imageDirection‖) •
          wz1PaperDirection source,
      ⟨(parameter - 1 / 2) / ‖imageDirection‖, rfl⟩, ?_⟩
    change
        anisotropicCenteredRescalingMap g c d m center
          (sourceCenter +
            ((parameter - 1 / 2) / ‖imageDirection‖) •
              wz1PaperDirection source) =
        (targetCenter - (1 / 2 : ℝ) • targetDirection) +
          parameter • targetDirection
    rw [anisotropicCenteredRescalingMap_add_smul]
    change
      targetCenter +
          ((parameter - 1 / 2) / ‖imageDirection‖) • imageDirection =
        (targetCenter - (1 / 2 : ℝ) •
          ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)) +
          parameter • ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)
    have hcoefficient :
        ((parameter - 1 / 2) / ‖imageDirection‖) =
          (parameter - 1 / 2) * ‖imageDirection‖⁻¹ := by
      field_simp [himageNorm.ne']
    rw [hcoefficient]
    module
  · rintro ⟨sourcePoint, hsourcePoint, rfl⟩
    rw [hsourceLine] at hsourcePoint
    rcases hsourcePoint with ⟨parameter, rfl⟩
    refine ⟨1 / 2 + parameter * ‖imageDirection‖, ?_⟩
    change
      anisotropicCenteredRescalingMap g c d m center
          (sourceCenter + parameter • wz1PaperDirection source) =
        (targetCenter - (1 / 2 : ℝ) • targetDirection) +
          (1 / 2 + parameter * ‖imageDirection‖) • targetDirection
    rw [anisotropicCenteredRescalingMap_add_smul]
    change
      targetCenter + parameter • imageDirection =
        (targetCenter - (1 / 2 : ℝ) •
          ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)) +
          (1 / 2 + parameter * ‖imageDirection‖) •
            ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)
    have hcancel : ‖imageDirection‖ * ‖imageDirection‖⁻¹ = 1 :=
      mul_inv_cancel₀ himageNorm.ne'
    simp only [smul_smul]
    rw [show (1 / 2 + parameter * ‖imageDirection‖) *
          ‖imageDirection‖⁻¹ =
        (1 / 2) * ‖imageDirection‖⁻¹ + parameter by
      rw [add_mul, mul_assoc, hcancel, mul_one]]
    module

theorem anisotropicPaperTargetTube_vertical
    (g : SlopeFunction) {c d m targetDelta sourceDelta : ℝ}
    (center : Point3)
    (hg : g.IsNormalized) (hcd : c < d)
    (hdc : d - c ≤ 1 / 25) (hm : 0 < m) (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source) :
    (1 / 2 : ℝ) ≤
      |(anisotropicPaperTargetTube
        g c d m center targetDelta hcd hm source).direction 2| := by
  exact anisotropicAnchoredDirection_vertical
    g hg hcd hdc hm hmOne hsub source hsource

theorem anisotropicPaperTargetTube_direction_two_pos
    (g : SlopeFunction) {c d m targetDelta sourceDelta : ℝ}
    (center : Point3)
    (hcd : c < d) (hm : 0 < m)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source) :
    0 < (anisotropicPaperTargetTube
      g c d m center targetDelta hcd hm source).direction 2 := by
  have hsourceTwo : 0 < wz1PaperDirection source 2 := by
    linarith [hsource.1]
  let image := dPhiLin g c d m (wz1PaperDirection source)
  have himageTwo : image 2 = (2 / (d - c)) *
      wz1PaperDirection source 2 := by
    simp [image, dPhiLin, point3]
  have himageTwoPos : 0 < image 2 := by
    rw [himageTwo]
    positivity
  have himageNormPos : 0 < ‖image‖ := by
    apply norm_pos_iff.mpr
    intro hzero
    have : image 2 = 0 := by rw [hzero]; simp
    linarith
  change 0 < (‖image‖⁻¹ : ℝ) * image 2
  positivity

/-- The target center is the canonical height-zero point of the image line. -/
theorem anisotropicPaperTargetTube_zeroPoint
    (g : SlopeFunction) {c d m targetDelta sourceDelta : ℝ}
    (center : Point3) (hcenter : center 2 = c + (d - c) / 2)
    (hcd : c < d) (hm : 0 < m)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source)
    (hvertical : (1 / 2 : ℝ) ≤
      |(anisotropicPaperTargetTube
        g c d m center targetDelta hcd hm source).direction 2|) :
    wz1TubeAxisZeroPoint
        (anisotropicPaperTargetTube g c d m center targetDelta hcd hm source) =
      anisotropicPaperTargetCenter g c d m center source := by
  apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero hvertical
  · rw [anisotropicPaperTargetTube_axis g center hcd hm source hsource]
    exact ⟨wz1PaperAxisPointAtHeight source (c + (d - c) / 2),
      wz1PaperAxisPointAtHeight_mem_axis source _, rfl⟩
  · exact anisotropicPaperTargetCenter_coord_two
      g center hcenter hcd source hsource

theorem anisotropicPaperTargetTube_lineClass
    (g : SlopeFunction) {c d m targetDelta sourceDelta : ℝ}
    (center : Point3) (hcenter : center 2 = c + (d - c) / 2)
    (hg : g.IsNormalized) (hcd : c < d)
    (hdc : d - c ≤ 1 / 25) (hm : 0 < m) (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source)
    (hzeroX : |anisotropicPaperTargetCenter g c d m center source 0| ≤ 1 / 3)
    (hzeroY : |anisotropicPaperTargetCenter g c d m center source 1| ≤ 1 / 3) :
    WZ1PaperTubeInLineClass
      (anisotropicPaperTargetTube
        g c d m center targetDelta hcd hm source) := by
  let target := anisotropicPaperTargetTube
    g c d m center targetDelta hcd hm source
  have hvertical : (1 / 2 : ℝ) ≤ |target.direction 2| := by
    exact anisotropicPaperTargetTube_vertical
      (targetDelta := targetDelta)
      g center hg hcd hdc hm hmOne hsub source hsource
  have hpositive : 0 < target.direction 2 := by
    exact anisotropicPaperTargetTube_direction_two_pos
      (targetDelta := targetDelta) g center hcd hm source hsource
  have hzero : wz1TubeAxisZeroPoint target =
      anisotropicPaperTargetCenter g c d m center source := by
    exact anisotropicPaperTargetTube_zeroPoint
      (targetDelta := targetDelta)
      g center hcenter hcd hm source hsource hvertical
  refine ⟨?_, ?_, ?_⟩
  · unfold wz1PaperDirection
    rw [if_pos hpositive.le]
    rw [abs_of_pos hpositive] at hvertical
    exact hvertical
  · rw [hzero]
    exact hzeroX
  · rw [hzero]
    exact hzeroY

end Kakeya.Assouad

end
