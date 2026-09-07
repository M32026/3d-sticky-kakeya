import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicPaperRetubingGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperInfrastructure

/-!
# Paper-shading compatible retubing for Proposition 6.5

This module packages the exact triangular affine image, one target tube on
each image supporting line, and the literal induced cube shading.  No
ordinary-unit-segment shading is substituted for the cropped paper shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The one-to-one exact image-line family. -/
def anisotropicPaperTargetFamily
    {sourceDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (g : SlopeFunction) (c d m : ℝ) (center : Point3)
    (targetDelta : ℝ) (hcd : c < d) (hm : 0 < m) :
    Kakeya.Streamlined.TubeFamily targetDelta where
  card := sourceFamily.card
  tube source := anisotropicPaperTargetTube
    g c d m center targetDelta hcd hm (sourceFamily.tube source)

/-- Output of exact triangular retubing before centered-conflict cleanup. -/
structure PureWZ2AnisotropicPaperRetubingData
    {sourceDelta targetDelta c d m : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (center : Point3)
    (hcd : c < d) (hm : 0 < m) where
  center_height : center 2 = c + (d - c) / 2
  shading : WZ1PaperTubeShading
    (anisotropicPaperTargetFamily
      sourceFamily g c d m center targetDelta hcd hm)
  line_class : WZ1PaperIsLineClass
    (anisotropicPaperTargetFamily
      sourceFamily g c d m center targetDelta hcd hm)
  midpoint_local : ∀ index,
    ‖wz2PaperTubeMidpoint
      ((anisotropicPaperTargetFamily
        sourceFamily g c d m center targetDelta hcd hm).tube index)‖ ≤ 3
  midpoint_height_zero : ∀ index,
    wz2PaperTubeMidpoint
      ((anisotropicPaperTargetFamily
        sourceFamily g c d m center targetDelta hcd hm).tube index) 2 = 0
  direction_two_pos : ∀ index,
    0 < ((anisotropicPaperTargetFamily
      sourceFamily g c d m center targetDelta hcd hm).tube index).direction 2
  cubical : WZ1PaperIsCubicalShading shading
  axis : ∀ index,
    tubeAxisLine
        ((anisotropicPaperTargetFamily
          sourceFamily g c d m center targetDelta hcd hm).tube index) =
      anisotropicCenteredRescalingMap g c d m center ''
        tubeAxisLine (sourceFamily.tube index)
  shading_carrier : ∀ index,
    shading.carrier index =
      wz1PaperCubicalSaturation targetDelta
        (anisotropicCenteredRescalingMap g c d m center ''
          sourceShading.carrier index)
  exact_image_subset : ∀ index,
    anisotropicCenteredRescalingMap g c d m center ''
        sourceShading.carrier index ⊆ shading.carrier index
  union_image_subset :
    anisotropicCenteredRescalingMap g c d m center ''
      sourceShading.union ⊆ shading.union
  mass_lower : ENNReal.ofReal m * sourceShading.mass ≤ shading.mass

theorem construct_anisotropic_paper_retubing
    {sourceDelta targetDelta c d m S : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (center : Point3)
    (hg : g.IsNormalized) (hcd : c < d)
    (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hS : S = 2 / (d - c))
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : 0 < targetDelta)
    (hradius : S * (18 * sourceDelta) + 2 * targetDelta ≤
      6 * targetDelta)
    (count : ℕ) (hcount : 0 < count)
    (halign : targetDelta * (count : ℝ) = 1)
    (hcenterTwo : center 2 = c + (d - c) / 2)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hsourceWindow : ∀ index point,
      point ∈ sourceShading.carrier index →
        |point 0 - center 0| ≤ 1 / 16 ∧
        |point 1 - center 1| ≤ 1 / 16 ∧
        c ≤ point 2 ∧ point 2 < d)
    (hcenterY : |center 1| ≤ 1)
    (hzeroX : ∀ index,
      |anisotropicPaperTargetCenter g c d m center
        (sourceFamily.tube index) 0| ≤ 1 / 3)
    (hzeroY : ∀ index,
      |anisotropicPaperTargetCenter g c d m center
        (sourceFamily.tube index) 1| ≤ 1 / 3) :
    Nonempty (PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta)
      sourceFamily sourceShading g center hcd hm) := by
  let family := anisotropicPaperTargetFamily
    sourceFamily g c d m center targetDelta hcd hm
  let targetCarrier : Fin family.card → Set Point3 := fun index =>
    wz1PaperCubicalSaturation targetDelta
      (anisotropicCenteredRescalingMap g c d m center ''
        sourceShading.carrier index)
  have htargetLine : WZ1PaperIsLineClass family := by
    intro index
    exact anisotropicPaperTargetTube_lineClass
      g center hcenterTwo hg hcd hdc hm hmOne hsub
      (sourceFamily.tube index) (hsourceLine index)
      (hzeroX index) (hzeroY index)
  have htargetAxis : ∀ index,
      tubeAxisLine (family.tube index) =
        anisotropicCenteredRescalingMap g c d m center ''
          tubeAxisLine (sourceFamily.tube index) := by
    intro index
    exact anisotropicPaperTargetTube_axis
      g center hcd hm (sourceFamily.tube index) (hsourceLine index)
  have hcarrierSubset : ∀ index : Fin sourceFamily.card, targetCarrier index ⊆
      wz1PaperTubeCarrier (family.tube index) := by
    intro index targetPoint htargetPoint
    change targetPoint ∈ wz1PaperCubicalSaturation targetDelta
      (anisotropicCenteredRescalingMap g c d m center ''
        sourceShading.carrier index) at htargetPoint
    constructor
    · exact anisotropicPaperCubicalSaturation_subset_targetCarrier
        g hg hcd hdc hm hmOne hsub hS hsourceDelta htargetDelta hradius
        center (sourceFamily.tube index) (hsourceLine index)
        (sourceShading.carrier index) (sourceShading.subset_body index)
        htargetPoint
    · have himageWindow : ∀ imagePoint ∈
          (anisotropicCenteredRescalingMap g c d m center ''
            sourceShading.carrier index),
          ∀ coordinate : Fin 3,
            -1 ≤ imagePoint coordinate ∧ imagePoint coordinate < 1 := by
        intro imagePoint himagePoint coordinate
        rcases himagePoint with ⟨sourcePoint, hsourcePoint, rfl⟩
        rcases hsourceWindow index sourcePoint hsourcePoint with
          ⟨hx, hy, hz⟩
        have hgmid : |g (c + (d - c) / 2)| ≤ 1 :=
          (hg _ (hsub ⟨by linarith, by linarith⟩)).1
        fin_cases coordinate
        · change -1 ≤
              anisotropicCenteredRescalingMap g c d m center sourcePoint 0 ∧
            anisotropicCenteredRescalingMap g c d m center sourcePoint 0 < 1
          have hcoord :
              anisotropicCenteredRescalingMap g c d m center sourcePoint 0 =
                (sourcePoint 0 - center 0) +
                  g (c + (d - c) / 2) *
                    (sourcePoint 1 - center 1) := by
            simp [anisotropicCenteredRescalingMap,
              anisotropicRescalingMap, point3]
            ring
          rw [hcoord]
          have hbound :
              |(sourcePoint 0 - center 0) +
                  g (c + (d - c) / 2) *
                    (sourcePoint 1 - center 1)| ≤ 1 / 8 := by
            calc
              |(sourcePoint 0 - center 0) +
                    g (c + (d - c) / 2) *
                      (sourcePoint 1 - center 1)| ≤
                  |sourcePoint 0 - center 0| +
                    |g (c + (d - c) / 2)| *
                      |sourcePoint 1 - center 1| := by
                    simpa [abs_mul] using
                      (abs_add_le (sourcePoint 0 - center 0)
                        (g (c + (d - c) / 2) *
                          (sourcePoint 1 - center 1)))
              _ ≤ 1 / 16 + 1 * (1 / 16) := by gcongr
              _ = 1 / 8 := by norm_num
          have hlt := hbound.trans_lt (by norm_num : (1 / 8 : ℝ) < 1)
          exact ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2⟩
        · change -1 ≤
              anisotropicCenteredRescalingMap g c d m center sourcePoint 1 ∧
            anisotropicCenteredRescalingMap g c d m center sourcePoint 1 < 1
          have hK : 0 ≤ m * (d - c) / 2 := by positivity
          have hcoord :
              anisotropicCenteredRescalingMap g c d m center sourcePoint 1 =
                (m * (d - c) / 2) * sourcePoint 1 := by
            simp [anisotropicCenteredRescalingMap,
              anisotropicRescalingMap, point3]
          rw [hcoord]
          have hKOne : m * (d - c) / 2 ≤ 1 / 50 := by
            calc
              m * (d - c) / 2 ≤ 1 * (1 / 25 : ℝ) / 2 := by
                gcongr
              _ = 1 / 50 := by norm_num
          have hsourceY : |sourcePoint 1| ≤ 17 / 16 := by
            calc
              |sourcePoint 1| =
                  |(sourcePoint 1 - center 1) + center 1| := by ring_nf
              _ ≤ |sourcePoint 1 - center 1| + |center 1| := abs_add_le _ _
              _ ≤ 1 / 16 + 1 := by gcongr
              _ = 17 / 16 := by norm_num
          have hbound :
              m * (d - c) / 2 * |sourcePoint 1| ≤ 17 / 800 := by
            calc
              m * (d - c) / 2 * |sourcePoint 1| ≤
                  (1 / 50 : ℝ) * (17 / 16) := by gcongr
              _ = 17 / 800 := by ring
          have habs :
              |m * (d - c) / 2 * sourcePoint 1| ≤ 17 / 800 := by
            rw [show m * (d - c) / 2 * sourcePoint 1 =
              (m * (d - c) / 2) * sourcePoint 1 by ring,
              abs_mul, abs_of_nonneg hK]
            exact hbound
          have hlt := habs.trans_lt (by norm_num : (17 / 800 : ℝ) < 1)
          exact ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2⟩
        · change -1 ≤
              anisotropicCenteredRescalingMap g c d m center sourcePoint 2 ∧
            anisotropicCenteredRescalingMap g c d m center sourcePoint 2 < 1
          have hcoord :
              anisotropicCenteredRescalingMap g c d m center sourcePoint 2 =
                2 * (sourcePoint 2 - c) / (d - c) - 1 := by
            simp [anisotropicCenteredRescalingMap,
              anisotropicRescalingMap, point3]
          rw [hcoord]
          have hdcPos : 0 < d - c := by linarith
          have hrewrite :
              2 * (sourcePoint 2 - c) / (d - c) =
                2 * ((sourcePoint 2 - c) / (d - c)) := by ring
          rw [hrewrite]
          have hratioNonnegative :
              0 ≤ (sourcePoint 2 - c) / (d - c) := by
            exact div_nonneg (by linarith [hz.1]) hdcPos.le
          have hratioLt :
              (sourcePoint 2 - c) / (d - c) < 1 := by
            exact (div_lt_one hdcPos).2 (by linarith [hz.2])
          constructor
          · have hnonnegative :
                0 ≤ 2 * ((sourcePoint 2 - c) / (d - c)) := by positivity
            linarith
          · have hltTwo :
                2 * ((sourcePoint 2 - c) / (d - c)) < 2 := by
              nlinarith
            linarith
      exact anisotropicPaperCubicalSaturation_subset_axisBox
        htargetDelta hcount halign
        (anisotropicCenteredRescalingMap g c d m center ''
          sourceShading.carrier index)
        himageWindow htargetPoint
  let shading : WZ1PaperTubeShading family :=
    { carrier := targetCarrier
      measurable_carrier := fun _ =>
        wz1PaperCubicalSaturation_measurable _ _
      subset_body := hcarrierSubset }
  have hcubical : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint
    exact wz1PaperCubicalSaturation_isCubical
      targetDelta _ point hpoint
  have himageSubset : ∀ index : Fin sourceFamily.card,
      anisotropicCenteredRescalingMap g c d m center ''
          sourceShading.carrier index ⊆ shading.carrier index := by
    intro index point hpoint
    change point ∈ targetCarrier index
    exact ⟨point, hpoint, rfl⟩
  have hunionSubset :
      anisotropicCenteredRescalingMap g c d m center ''
          sourceShading.union ⊆ shading.union := by
    rintro target ⟨source, ⟨index, hsource⟩, rfl⟩
    exact ⟨index, himageSubset index ⟨source, hsource, rfl⟩⟩
  have hmass : ENNReal.ofReal m * sourceShading.mass ≤ shading.mass := by
    change ENNReal.ofReal m *
        (∑ index, volume (sourceShading.carrier index)) ≤
      ∑ index, volume (shading.carrier index)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro index _
    have himageMeasure : volume
          (anisotropicCenteredRescalingMap g c d m center ''
            sourceShading.carrier index) ≤
        volume (shading.carrier index) :=
      measure_mono (himageSubset index)
    rw [volume_image_anisotropicCenteredRescalingMap
      g hcd hm center _ (sourceShading.measurable_carrier index)]
      at himageMeasure
    exact himageMeasure
  have hmidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (family.tube index)‖ ≤ 3 := by
    intro index
    change ‖wz2PaperTubeMidpoint
      (anisotropicPaperTargetTube
        g c d m center targetDelta hcd hm (sourceFamily.tube index))‖ ≤ 3
    rw [anisotropicPaperTargetTube_midpoint]
    have hx := hzeroX index
    have hy := hzeroY index
    have hz : anisotropicPaperTargetCenter g c d m center
        (sourceFamily.tube index) 2 = 0 :=
      anisotropicPaperTargetCenter_coord_two
        (m := m) g center hcenterTwo hcd
          (sourceFamily.tube index) (hsourceLine index)
    have hnorm := point3_coord_norm_sq
      (anisotropicPaperTargetCenter g c d m center
        (sourceFamily.tube index))
    have hxSq : (anisotropicPaperTargetCenter g c d m center
        (sourceFamily.tube index) 0) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
      rw [← sq_abs]
      gcongr
    have hySq : (anisotropicPaperTargetCenter g c d m center
        (sourceFamily.tube index) 1) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
      rw [← sq_abs]
      gcongr
    nlinarith [hxSq, hySq, sq_abs
      (anisotropicPaperTargetCenter g c d m center
        (sourceFamily.tube index) 0),
      sq_abs (anisotropicPaperTargetCenter g c d m center
        (sourceFamily.tube index) 1),
      norm_nonneg (anisotropicPaperTargetCenter g c d m center
        (sourceFamily.tube index))]
  exact ⟨{
    center_height := hcenterTwo
    shading := shading
    line_class := htargetLine
    midpoint_local := hmidpoint
    midpoint_height_zero := fun index => by
      change wz2PaperTubeMidpoint
          (anisotropicPaperTargetTube g c d m center targetDelta hcd hm
            (sourceFamily.tube index)) 2 = 0
      rw [anisotropicPaperTargetTube_midpoint]
      exact anisotropicPaperTargetCenter_coord_two
        g center hcenterTwo hcd (sourceFamily.tube index)
          (hsourceLine index)
    direction_two_pos := fun index =>
      anisotropicPaperTargetTube_direction_two_pos
        g center hcd hm (sourceFamily.tube index) (hsourceLine index)
    cubical := hcubical
    axis := htargetAxis
    shading_carrier := fun _ => rfl
    exact_image_subset := himageSubset
    union_image_subset := hunionSubset
    mass_lower := hmass
  }⟩

end Kakeya.Assouad

end
