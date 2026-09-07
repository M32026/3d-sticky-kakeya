import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicAffineEquiv
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicAnchoredThreeTubeCover
import MyLeanRepo.Kakeya.Assouad.TranslationInfrastructure
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeParameters

/-!
# Horizontally centered form of the exact Proposition 6.5 triangular map

This is only a post-composition by one common translation in the first
coordinate.  Its linear part, Jacobian, and transformed line-parameter
differences are therefore those of the uncentered anisotropic rescaling map.
Because the second coordinate is not translated, the twisted projection is
changed only by an additive constant.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Translate only the first coordinate of the exact triangular image so that
the first coordinate of one common source point is sent to zero. -/
def anisotropicCenteredRescalingMap
    (g : SlopeFunction) (c d m : ℝ) (center point : Point3) : Point3 :=
  anisotropicRescalingMap g c d m point -
    point3 (anisotropicRescalingMap g c d m center 0) 0 0

/-- The horizontally centered exact triangular map as an affine
equivalence. -/
noncomputable def anisotropicCenteredRescalingAffineEquiv
    (g : SlopeFunction) (c d m : ℝ) (center : Point3)
    (hcd : c < d) (hm : 0 < m) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  (anisotropicRescalingAffineEquiv g c d m hcd hm).trans
    (AffineEquiv.constVAdd ℝ Point3
      (-point3 (anisotropicRescalingMap g c d m center 0) 0 0))

@[simp] theorem anisotropicCenteredRescalingAffineEquiv_apply
    (g : SlopeFunction) (c d m : ℝ) (center : Point3)
    (hcd : c < d) (hm : 0 < m) (point : Point3) :
    anisotropicCenteredRescalingAffineEquiv
        g c d m center hcd hm point =
      anisotropicCenteredRescalingMap g c d m center point := by
  simp [anisotropicCenteredRescalingAffineEquiv,
    anisotropicCenteredRescalingMap, AffineEquiv.trans_apply,
    AffineEquiv.constVAdd_apply]
  abel

@[simp] theorem anisotropicCenteredRescalingAffineEquiv_linear
    (g : SlopeFunction) (c d m : ℝ) (center : Point3)
    (hcd : c < d) (hm : 0 < m) :
    (anisotropicCenteredRescalingAffineEquiv
      g c d m center hcd hm).linear =
      anisotropicRescalingLinearEquiv g c d m hcd hm := by
  rfl

theorem anisotropicCenteredRescalingMap_center_coord_zero
    (g : SlopeFunction) (c d m : ℝ) (center : Point3) :
    anisotropicCenteredRescalingMap g c d m center center 0 = 0 := by
  simp [anisotropicCenteredRescalingMap, point3]

theorem anisotropicCenteredRescalingMap_sub
    (g : SlopeFunction) (c d m : ℝ) (center first second : Point3) :
    anisotropicCenteredRescalingMap g c d m center first -
        anisotropicCenteredRescalingMap g c d m center second =
      dPhiLin g c d m (first - second) := by
  unfold anisotropicCenteredRescalingMap
  rw [show
    (anisotropicRescalingMap g c d m first -
          point3 (anisotropicRescalingMap g c d m center 0) 0 0) -
        (anisotropicRescalingMap g c d m second -
          point3 (anisotropicRescalingMap g c d m center 0) 0 0) =
      anisotropicRescalingMap g c d m first -
        anisotropicRescalingMap g c d m second by abel]
  rw [← anisotropicRescalingLinearMap_apply_eq_dPhiLin]
  have hfirst := anisotropicRescalingMap_eq g c d m first
  have hsecond := anisotropicRescalingMap_eq g c d m second
  rw [hfirst, hsecond]
  simp only [map_sub]
  abel

theorem anisotropicCenteredRescalingMap_add_smul
    (g : SlopeFunction) (c d m : ℝ) (center point direction : Point3)
    (parameter : ℝ) :
    anisotropicCenteredRescalingMap g c d m center
        (point + parameter • direction) =
      anisotropicCenteredRescalingMap g c d m center point +
        parameter • dPhiLin g c d m direction := by
  unfold anisotropicCenteredRescalingMap
  rw [anisotropicRescalingMap_add_smul]
  abel

theorem anisotropicCenteredRescalingMap_dist_le_height
    (g : SlopeFunction) {c d m S : ℝ}
    (hg : g.IsNormalized) (hcd : c < d)
    (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hS : S = 2 / (d - c))
    (center first second : Point3) :
    dist (anisotropicCenteredRescalingMap g c d m center first)
        (anisotropicCenteredRescalingMap g c d m center second) ≤
      S * dist first second := by
  have h := anisotropicRescalingMap_dist_le_height
    g hg hcd hdc hm hmOne hsub hS first second
  simpa [anisotropicCenteredRescalingMap, dist_eq_norm] using h

theorem volume_image_anisotropicCenteredRescalingMap
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (center : Point3) (source : Set Point3)
    (hsource : MeasurableSet source) :
    volume (anisotropicCenteredRescalingMap g c d m center '' source) =
      ENNReal.ofReal m * volume source := by
  let shift : Point3 :=
    -point3 (anisotropicRescalingMap g c d m center 0) 0 0
  have himage :
      anisotropicCenteredRescalingMap g c d m center '' source =
        (fun point : Point3 => point + shift) ''
          (anisotropicRescalingMap g c d m '' source) := by
    ext point
    constructor
    · rintro ⟨sourcePoint, hsourcePoint, rfl⟩
      exact ⟨anisotropicRescalingMap g c d m sourcePoint,
        ⟨sourcePoint, hsourcePoint, rfl⟩, by
          simp [anisotropicCenteredRescalingMap, shift]
          abel⟩
    · rintro ⟨imagePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
      exact ⟨sourcePoint, hsourcePoint, by
        simp [anisotropicCenteredRescalingMap, shift]
        abel⟩
  have himageMeasurable :
      MeasurableSet (anisotropicRescalingMap g c d m '' source) := by
    have heq : anisotropicRescalingMap g c d m '' source =
        anisotropicRescalingAffineEquiv g c d m hcd hm '' source := by
      ext point
      simp only [Set.mem_image]
      constructor
      · rintro ⟨preimage, hpreimage, rfl⟩
        exact ⟨preimage, hpreimage,
          anisotropicRescalingAffineEquiv_apply
            g c d m hcd hm preimage⟩
      · rintro ⟨preimage, hpreimage, rfl⟩
        exact ⟨preimage, hpreimage,
          (anisotropicRescalingAffineEquiv_apply
            g c d m hcd hm preimage).symm⟩
    rw [heq]
    let equiv :=
      (anisotropicRescalingAffineEquiv g c d m hcd hm)
        |>.toHomeomorphOfFiniteDimensional
        |>.toMeasurableEquiv
    exact equiv.measurableSet_image.mpr hsource
  rw [himage, TranslationInfrastructure.volume_translate himageMeasurable]
  exact volume_image_anisotropicRescalingMap g hcd hm source hsource

/-- The centered map changes only the target x-intercept by one common
constant.  Its other vertical-chart parameters agree with the uncentered
exact triangular map. -/
def anisotropicCenteredTubeParams
    (g : SlopeFunction) (c d m : ℝ) (center : Point3)
    (params : TubeParams) : TubeParams :=
  let raw := anisotropicTubeParams g c d m params
  { raw with
    a := raw.a - anisotropicRescalingMap g c d m center 0 }

theorem anisotropicCenteredTubeParams_sub_eq
    (g : SlopeFunction) (c d m : ℝ) (center : Point3)
    (first second : TubeParams) :
    let centeredFirst := anisotropicCenteredTubeParams
      g c d m center first
    let centeredSecond := anisotropicCenteredTubeParams
      g c d m center second
    let rawFirst := anisotropicTubeParams g c d m first
    let rawSecond := anisotropicTubeParams g c d m second
    centeredFirst.a - centeredSecond.a = rawFirst.a - rawSecond.a ∧
      centeredFirst.b - centeredSecond.b = rawFirst.b - rawSecond.b ∧
      centeredFirst.c - centeredSecond.c = rawFirst.c - rawSecond.c ∧
      centeredFirst.d - centeredSecond.d = rawFirst.d - rawSecond.d := by
  dsimp only [anisotropicCenteredTubeParams]
  exact ⟨by ring, rfl, rfl, rfl⟩

theorem anisotropicCenteredRescalingMap_axisPointAtHeight
    {sourceDelta : ℝ}
    (g : SlopeFunction) {c d m : ℝ} (hcd : c < d)
    (center : Point3)
    (source : Kakeya.DeltaTube sourceDelta)
    (hvertical : source.direction (2 : Fin 3) ≠ 0)
    (z : ℝ) :
    let sourceHeight := c + (d - c) / 2 * (z + 1)
    let point := anisotropicCenteredRescalingMap g c d m center
      (tubeAxisPointAtHeight source sourceHeight)
    let params := anisotropicCenteredTubeParams g c d m center
      (tubeParamsOfTube source)
    point 0 = params.a + params.c * z ∧
      point 1 = params.b + params.d * z ∧ point 2 = z := by
  dsimp only
  have hraw := anisotropicRescalingMap_axisPointAtHeight
    (m := m) g hcd source hvertical z
  rcases hraw with ⟨hzero, hone, htwo⟩
  exact ⟨by
      rw [anisotropicCenteredRescalingMap]
      simp only [PiLp.sub_apply]
      have hpointThree : (point3
          (anisotropicRescalingMap g c d m center 0) 0 0) 0 =
          anisotropicRescalingMap g c d m center 0 := by simp [point3]
      rw [hpointThree]
      dsimp only [anisotropicCenteredTubeParams]
      rw [hzero]
      ring,
    by
      rw [anisotropicCenteredRescalingMap]
      simp only [PiLp.sub_apply, point3]
      dsimp only [anisotropicCenteredTubeParams]
      simpa using hone,
    by
      rw [anisotropicCenteredRescalingMap]
      simp only [PiLp.sub_apply, point3]
      simpa using htwo⟩

/-- Whole-line provenance determines the exact centered target parameters. -/
theorem tubeParamsOfTube_eq_anisotropicCentered_of_axis_image
    {sourceDelta targetDelta : ℝ}
    (g : SlopeFunction) {c d m : ℝ} (hcd : c < d)
    (center : Point3)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : source.direction (2 : Fin 3) ≠ 0)
    (target : Kakeya.DeltaTube targetDelta)
    (htargetVertical : target.direction (2 : Fin 3) ≠ 0)
    (haxis : tubeAxisLine target =
      anisotropicCenteredRescalingMap g c d m center '' tubeAxisLine source) :
    tubeParamsOfTube target =
      anisotropicCenteredTubeParams g c d m center
        (tubeParamsOfTube source) := by
  let sourceHeight : ℝ → ℝ := fun z =>
    c + (d - c) / 2 * (z + 1)
  let imagePoint : ℝ → Point3 := fun z =>
    anisotropicCenteredRescalingMap g c d m center
      (tubeAxisPointAtHeight source (sourceHeight z))
  let params := anisotropicCenteredTubeParams g c d m center
    (tubeParamsOfTube source)
  have himage : ∀ z, imagePoint z ∈ tubeAxisLine target := by
    intro z
    rw [haxis]
    exact ⟨tubeAxisPointAtHeight source (sourceHeight z),
      tubeAxisPointAtHeight_mem source _, rfl⟩
  have hcoords : ∀ z,
      imagePoint z 0 = params.a + params.c * z ∧
      imagePoint z 1 = params.b + params.d * z ∧
      imagePoint z 2 = z := by
    intro z
    exact anisotropicCenteredRescalingMap_axisPointAtHeight
      g hcd center source hsourceVertical z
  have htargetZero : ∀ z,
      imagePoint z 0 = (tubeParamsOfTube target).a +
        (tubeParamsOfTube target).c * imagePoint z 2 :=
    fun z => tubeAxisLine_coord_zero target htargetVertical (himage z)
  have htargetOne : ∀ z,
      imagePoint z 1 = (tubeParamsOfTube target).b +
        (tubeParamsOfTube target).d * imagePoint z 2 :=
    fun z => tubeAxisLine_coord_one target htargetVertical (himage z)
  apply TubeParams.ext
  · have h := htargetZero 0
    rw [(hcoords 0).1, (hcoords 0).2.2] at h
    simpa using h.symm
  · have h := htargetOne 0
    rw [(hcoords 0).2.1, (hcoords 0).2.2] at h
    simpa using h.symm
  · have hzero := htargetZero 0
    have hone := htargetZero 1
    rw [(hcoords 0).1, (hcoords 0).2.2] at hzero
    rw [(hcoords 1).1, (hcoords 1).2.2] at hone
    have ha : (tubeParamsOfTube target).a = params.a := by
      simpa using hzero.symm
    rw [ha] at hone
    linarith
  · have hzero := htargetOne 0
    have hone := htargetOne 1
    rw [(hcoords 0).2.1, (hcoords 0).2.2] at hzero
    rw [(hcoords 1).2.1, (hcoords 1).2.2] at hone
    have hb : (tubeParamsOfTube target).b = params.b := by
      simpa using hzero.symm
    rw [hb] at hone
    linarith

end Kakeya.Assouad

end
