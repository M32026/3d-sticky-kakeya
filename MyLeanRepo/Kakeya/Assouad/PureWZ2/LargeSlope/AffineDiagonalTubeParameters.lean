import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalMap
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeParameters

/-!
# Supporting-line parameters under the fixed-rotation diagonal map

The isotropic factor is fixed to one.  This is the paper-literal map and is
also the factor required by the exact-slope source-height formula used by the
global AD covariance theorem.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Exact four vertical-chart parameters of an affine-diagonal image line. -/
def pureWZ2AffineDiagonalTubeParams
    (frameSlope anchor heightScale transverseScale : ℝ)
    (params : TubeParams) : TubeParams :=
  let horizontalNorm := pureWZ2HorizontalNorm frameSlope
  { a := (params.a + frameSlope * params.b +
      anchor * (params.c + frameSlope * params.d)) / horizontalNorm
    b := transverseScale *
      (-frameSlope * params.a + params.b +
        anchor * (-frameSlope * params.c + params.d)) / horizontalNorm
    c := (params.c + frameSlope * params.d) /
      (horizontalNorm * heightScale)
    d := transverseScale * (-frameSlope * params.c + params.d) /
      (horizontalNorm * heightScale) }

/-- Exact vertical-chart parameters for the fully centered affine map.
The horizontal part of `center` translates both intercepts before the common
fixed rotation; the third coordinate remains the height anchor. -/
def pureWZ2AffineDiagonalCenteredTubeParams
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (params : TubeParams) : TubeParams :=
  pureWZ2AffineDiagonalTubeParams frameSlope (center 2) heightScale
    transverseScale
    { a := params.a - center 0
      b := params.b - center 1
      c := params.c
      d := params.d }

/-- Pairwise parameter differences are insensitive to the common horizontal
translation in the fully centered affine map. -/
theorem pureWZ2AffineDiagonalCenteredTubeParams_sub_eq
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (first second : TubeParams) :
    let centeredFirst := pureWZ2AffineDiagonalCenteredTubeParams frameSlope
      center heightScale transverseScale first
    let centeredSecond := pureWZ2AffineDiagonalCenteredTubeParams frameSlope
      center heightScale transverseScale second
    let anchoredFirst := pureWZ2AffineDiagonalTubeParams frameSlope
      (center 2) heightScale transverseScale first
    let anchoredSecond := pureWZ2AffineDiagonalTubeParams frameSlope
      (center 2) heightScale transverseScale second
    centeredFirst.a - centeredSecond.a = anchoredFirst.a - anchoredSecond.a ∧
      centeredFirst.b - centeredSecond.b = anchoredFirst.b - anchoredSecond.b ∧
      centeredFirst.c - centeredSecond.c = anchoredFirst.c - anchoredSecond.c ∧
      centeredFirst.d - centeredSecond.d = anchoredFirst.d - anchoredSecond.d := by
  dsimp only [pureWZ2AffineDiagonalCenteredTubeParams,
    pureWZ2AffineDiagonalTubeParams]
  have hnorm : pureWZ2HorizontalNorm frameSlope ≠ 0 :=
    (pureWZ2HorizontalNorm_pos frameSlope).ne'
  constructor
  · field_simp [hnorm]
    ring
  constructor
  · field_simp [hnorm]
    ring
  exact ⟨rfl, rfl⟩

/-- The image under the fully centered affine map of a source axis point at
target height `t` has the centered transformed parameters. -/
theorem pureWZ2AffineDiagonalMapCentered_axisPointAtTargetHeight
    {delta : ℝ}
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (source : Kakeya.DeltaTube delta)
    (hvertical : source.direction (2 : Fin 3) ≠ 0)
    (t : ℝ) :
    let sourceHeight := center 2 + t / heightScale
    let point := pureWZ2AffineDiagonalMapCentered frameSlope center
      heightScale transverseScale 1
      (tubeAxisPointAtHeight source sourceHeight)
    let params := pureWZ2AffineDiagonalCenteredTubeParams frameSlope center
      heightScale transverseScale (tubeParamsOfTube source)
    point (0 : Fin 3) = params.a + params.c * t ∧
      point (1 : Fin 3) = params.b + params.d * t ∧
      point (2 : Fin 3) = t := by
  dsimp only
  let sourceHeight := center 2 + t / heightScale
  have hsourceTwo :=
    tubeAxisPointAtHeight_coord_two source hvertical sourceHeight
  have hsourceZero :=
    tubeAxisPointAtHeight_coord_zero source hvertical sourceHeight
  have hsourceOne :=
    tubeAxisPointAtHeight_coord_one source hvertical sourceHeight
  have hnorm : pureWZ2HorizontalNorm frameSlope ≠ 0 :=
    (pureWZ2HorizontalNorm_pos frameSlope).ne'
  constructor
  · rw [pureWZ2AffineDiagonalMapCentered_coord_zero _ _ _ _ _ one_ne_zero,
      hsourceZero,
      hsourceOne]
    dsimp only [pureWZ2AffineDiagonalCenteredTubeParams,
      pureWZ2AffineDiagonalTubeParams, sourceHeight]
    field_simp [hnorm, hheight]
    ring
  constructor
  · rw [pureWZ2AffineDiagonalMapCentered_coord_one _ _ _ _ _
      htransverse one_ne_zero, hsourceZero,
      hsourceOne]
    dsimp only [pureWZ2AffineDiagonalCenteredTubeParams,
      pureWZ2AffineDiagonalTubeParams, sourceHeight]
    field_simp [hnorm, hheight]
    ring
  · rw [pureWZ2AffineDiagonalMapCentered_coord_two, hsourceTwo]
    dsimp only [sourceHeight]
    field_simp [hheight]
    ring

/-- Whole-line provenance for the fully centered affine map. -/
theorem tubeParamsOfTube_eq_pureWZ2AffineDiagonalCentered_of_axis_image
    {sourceDelta targetDelta : ℝ}
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : source.direction (2 : Fin 3) ≠ 0)
    (target : Kakeya.DeltaTube targetDelta)
    (htargetVertical : target.direction (2 : Fin 3) ≠ 0)
    (haxis :
      tubeAxisLine target =
        pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale 1 '' tubeAxisLine source) :
    tubeParamsOfTube target =
      pureWZ2AffineDiagonalCenteredTubeParams frameSlope center
        heightScale transverseScale (tubeParamsOfTube source) := by
  let sourceHeight : ℝ → ℝ := fun t => center 2 + t / heightScale
  let imagePoint : ℝ → Point3 := fun t =>
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
      transverseScale 1 (tubeAxisPointAtHeight source (sourceHeight t))
  let params := pureWZ2AffineDiagonalCenteredTubeParams frameSlope center
    heightScale transverseScale (tubeParamsOfTube source)
  have himage : ∀ t, imagePoint t ∈ tubeAxisLine target := by
    intro t
    rw [haxis]
    exact ⟨tubeAxisPointAtHeight source (sourceHeight t),
      tubeAxisPointAtHeight_mem source (sourceHeight t), rfl⟩
  have hcoords : ∀ t,
      imagePoint t (0 : Fin 3) = params.a + params.c * t ∧
      imagePoint t (1 : Fin 3) = params.b + params.d * t ∧
      imagePoint t (2 : Fin 3) = t := by
    intro t
    exact pureWZ2AffineDiagonalMapCentered_axisPointAtTargetHeight
      frameSlope center heightScale transverseScale hheight htransverse
      source hsourceVertical t
  have htargetZero : ∀ t,
      imagePoint t (0 : Fin 3) =
        (tubeParamsOfTube target).a +
          (tubeParamsOfTube target).c * imagePoint t (2 : Fin 3) :=
    fun t => tubeAxisLine_coord_zero target htargetVertical (himage t)
  have htargetOne : ∀ t,
      imagePoint t (1 : Fin 3) =
        (tubeParamsOfTube target).b +
          (tubeParamsOfTube target).d * imagePoint t (2 : Fin 3) :=
    fun t => tubeAxisLine_coord_one target htargetVertical (himage t)
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

/-- The image of a source axis point at the height corresponding to target
height `t` has the coordinates encoded by the transformed parameters. -/
theorem pureWZ2AffineDiagonalMapAt_axisPointAtTargetHeight
    {delta : ℝ}
    (frameSlope anchor heightScale transverseScale : ℝ)
    (hheight : heightScale ≠ 0)
    (source : Kakeya.DeltaTube delta)
    (hvertical : source.direction (2 : Fin 3) ≠ 0)
    (t : ℝ) :
    let sourceHeight := anchor + t / heightScale
    let point := pureWZ2AffineDiagonalMapAt frameSlope anchor
      heightScale transverseScale 1
      (tubeAxisPointAtHeight source sourceHeight)
    let params := pureWZ2AffineDiagonalTubeParams frameSlope anchor
      heightScale transverseScale (tubeParamsOfTube source)
    point (0 : Fin 3) = params.a + params.c * t ∧
      point (1 : Fin 3) = params.b + params.d * t ∧
      point (2 : Fin 3) = t := by
  dsimp only
  let sourceHeight := anchor + t / heightScale
  have hsourceTwo :=
    tubeAxisPointAtHeight_coord_two source hvertical sourceHeight
  have hsourceZero :=
    tubeAxisPointAtHeight_coord_zero source hvertical sourceHeight
  have hsourceOne :=
    tubeAxisPointAtHeight_coord_one source hvertical sourceHeight
  have hnorm : pureWZ2HorizontalNorm frameSlope ≠ 0 :=
    (pureWZ2HorizontalNorm_pos frameSlope).ne'
  constructor
  · rw [pureWZ2AffineDiagonalMapAt_coord_zero, hsourceZero, hsourceOne]
    dsimp only [pureWZ2AffineDiagonalTubeParams, sourceHeight]
    field_simp [hnorm, hheight]
    ring
  constructor
  · rw [pureWZ2AffineDiagonalMapAt_coord_one, hsourceZero, hsourceOne]
    dsimp only [pureWZ2AffineDiagonalTubeParams, sourceHeight]
    field_simp [hnorm, hheight]
    ring
  · rw [pureWZ2AffineDiagonalMapAt_coord_two, hsourceTwo]
    dsimp only [sourceHeight]
    field_simp [hheight]
    ring

/-- Midpoint-compatible form of the arbitrary-anchor coordinate theorem. -/
theorem pureWZ2AffineDiagonalMap_axisPointAtTargetHeight
    {delta : ℝ}
    (frameSlope left right heightScale transverseScale : ℝ)
    (hheight : heightScale ≠ 0)
    (source : Kakeya.DeltaTube delta)
    (hvertical : source.direction (2 : Fin 3) ≠ 0)
    (t : ℝ) :
    let anchor := (left + right) / 2
    let sourceHeight := anchor + t / heightScale
    let point := pureWZ2AffineDiagonalMap frameSlope left right
      heightScale transverseScale 1
      (tubeAxisPointAtHeight source sourceHeight)
    let params := pureWZ2AffineDiagonalTubeParams frameSlope anchor
      heightScale transverseScale (tubeParamsOfTube source)
    point (0 : Fin 3) = params.a + params.c * t ∧
      point (1 : Fin 3) = params.b + params.d * t ∧
      point (2 : Fin 3) = t := by
  dsimp only
  let anchor := (left + right) / 2
  let sourceHeight := anchor + t / heightScale
  have hsourceTwo :=
    tubeAxisPointAtHeight_coord_two source hvertical sourceHeight
  have hsourceZero :=
    tubeAxisPointAtHeight_coord_zero source hvertical sourceHeight
  have hsourceOne :=
    tubeAxisPointAtHeight_coord_one source hvertical sourceHeight
  have hnorm : pureWZ2HorizontalNorm frameSlope ≠ 0 :=
    (pureWZ2HorizontalNorm_pos frameSlope).ne'
  constructor
  · rw [pureWZ2AffineDiagonalMap_coord_zero, hsourceZero, hsourceOne]
    dsimp only [pureWZ2AffineDiagonalTubeParams, anchor, sourceHeight]
    field_simp [hnorm, hheight]
    ring
  constructor
  · rw [pureWZ2AffineDiagonalMap_coord_one, hsourceZero, hsourceOne]
    dsimp only [pureWZ2AffineDiagonalTubeParams, anchor, sourceHeight]
    field_simp [hnorm, hheight]
    ring
  · rw [pureWZ2AffineDiagonalMap_coord_two, hsourceTwo]
    dsimp only [sourceHeight, anchor]
    field_simp [hheight]
    ring

/-- Whole-line provenance determines the exact target line parameters. -/
theorem tubeParamsOfTube_eq_pureWZ2AffineDiagonalAt_of_axis_image
    {sourceDelta targetDelta : ℝ}
    (frameSlope anchor heightScale transverseScale : ℝ)
    (hheight : heightScale ≠ 0)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : source.direction (2 : Fin 3) ≠ 0)
    (target : Kakeya.DeltaTube targetDelta)
    (htargetVertical : target.direction (2 : Fin 3) ≠ 0)
    (haxis :
      tubeAxisLine target =
        pureWZ2AffineDiagonalMapAt frameSlope anchor heightScale
          transverseScale 1 '' tubeAxisLine source) :
    tubeParamsOfTube target =
      pureWZ2AffineDiagonalTubeParams frameSlope anchor
        heightScale transverseScale (tubeParamsOfTube source) := by
  let sourceHeight : ℝ → ℝ := fun t => anchor + t / heightScale
  let imagePoint : ℝ → Point3 := fun t =>
    pureWZ2AffineDiagonalMapAt frameSlope anchor heightScale
      transverseScale 1 (tubeAxisPointAtHeight source (sourceHeight t))
  let params := pureWZ2AffineDiagonalTubeParams frameSlope anchor
    heightScale transverseScale (tubeParamsOfTube source)
  have himage : ∀ t, imagePoint t ∈ tubeAxisLine target := by
    intro t
    rw [haxis]
    exact ⟨tubeAxisPointAtHeight source (sourceHeight t),
      tubeAxisPointAtHeight_mem source (sourceHeight t), rfl⟩
  have hcoords : ∀ t,
      imagePoint t (0 : Fin 3) = params.a + params.c * t ∧
      imagePoint t (1 : Fin 3) = params.b + params.d * t ∧
      imagePoint t (2 : Fin 3) = t := by
    intro t
    exact pureWZ2AffineDiagonalMapAt_axisPointAtTargetHeight
      frameSlope anchor heightScale transverseScale hheight
      source hsourceVertical t
  have htargetZero : ∀ t,
      imagePoint t (0 : Fin 3) =
        (tubeParamsOfTube target).a +
          (tubeParamsOfTube target).c * imagePoint t (2 : Fin 3) :=
    fun t => tubeAxisLine_coord_zero target htargetVertical (himage t)
  have htargetOne : ∀ t,
      imagePoint t (1 : Fin 3) =
        (tubeParamsOfTube target).b +
          (tubeParamsOfTube target).d * imagePoint t (2 : Fin 3) :=
    fun t => tubeAxisLine_coord_one target htargetVertical (himage t)
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

/-- Midpoint-compatible form of the arbitrary-anchor line theorem. -/
theorem tubeParamsOfTube_eq_pureWZ2AffineDiagonal_of_axis_image
    {sourceDelta targetDelta : ℝ}
    (frameSlope left right heightScale transverseScale : ℝ)
    (hheight : heightScale ≠ 0)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : source.direction (2 : Fin 3) ≠ 0)
    (target : Kakeya.DeltaTube targetDelta)
    (htargetVertical : target.direction (2 : Fin 3) ≠ 0)
    (haxis :
      tubeAxisLine target =
        pureWZ2AffineDiagonalMap frameSlope left right heightScale
          transverseScale 1 '' tubeAxisLine source) :
    tubeParamsOfTube target =
      pureWZ2AffineDiagonalTubeParams frameSlope ((left + right) / 2)
        heightScale transverseScale (tubeParamsOfTube source) := by
  let sourceHeight : ℝ → ℝ := fun t =>
    (left + right) / 2 + t / heightScale
  let imagePoint : ℝ → Point3 := fun t =>
    pureWZ2AffineDiagonalMap frameSlope left right heightScale
      transverseScale 1 (tubeAxisPointAtHeight source (sourceHeight t))
  let params := pureWZ2AffineDiagonalTubeParams frameSlope
    ((left + right) / 2) heightScale transverseScale
      (tubeParamsOfTube source)
  have himage : ∀ t, imagePoint t ∈ tubeAxisLine target := by
    intro t
    rw [haxis]
    exact ⟨tubeAxisPointAtHeight source (sourceHeight t),
      tubeAxisPointAtHeight_mem source (sourceHeight t), rfl⟩
  have hcoords : ∀ t,
      imagePoint t (0 : Fin 3) = params.a + params.c * t ∧
      imagePoint t (1 : Fin 3) = params.b + params.d * t ∧
      imagePoint t (2 : Fin 3) = t := by
    intro t
    exact pureWZ2AffineDiagonalMap_axisPointAtTargetHeight
      frameSlope left right heightScale transverseScale hheight
      source hsourceVertical t
  have htargetZero : ∀ t,
      imagePoint t (0 : Fin 3) =
        (tubeParamsOfTube target).a +
          (tubeParamsOfTube target).c * imagePoint t (2 : Fin 3) :=
    fun t => tubeAxisLine_coord_zero target htargetVertical (himage t)
  have htargetOne : ∀ t,
      imagePoint t (1 : Fin 3) =
        (tubeParamsOfTube target).b +
          (tubeParamsOfTube target).d * imagePoint t (2 : Fin 3) :=
    fun t => tubeAxisLine_coord_one target htargetVertical (himage t)
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

/--
Quantitative inverse of the fixed-rotation diagonal parameter map.

The intentionally coarse common width keeps the four output coordinates in
one box.  It is finite whenever the height and transverse factors are
positive and is the only singular factor later absorbed by the Lemma 8 mild
scale choice.
-/
theorem pureWZ2AffineDiagonalTubeParams_inverse_cluster
    (frameSlope anchor heightScale transverseScale r : ℝ)
    (hframe : |frameSlope| ≤ 1)
    (hanchor : |anchor| ≤ 1)
    (hheight : 0 < heightScale)
    (htransverse : 0 < transverseScale)
    (hr : 0 ≤ r)
    (first second : TubeParams)
    (ha : |(pureWZ2AffineDiagonalTubeParams frameSlope anchor
          heightScale transverseScale first).a -
        (pureWZ2AffineDiagonalTubeParams frameSlope anchor
          heightScale transverseScale second).a| ≤ r)
    (hb : |(pureWZ2AffineDiagonalTubeParams frameSlope anchor
          heightScale transverseScale first).b -
        (pureWZ2AffineDiagonalTubeParams frameSlope anchor
          heightScale transverseScale second).b| ≤ r)
    (hc : |(pureWZ2AffineDiagonalTubeParams frameSlope anchor
          heightScale transverseScale first).c -
        (pureWZ2AffineDiagonalTubeParams frameSlope anchor
          heightScale transverseScale second).c| ≤ r)
    (hd : |(pureWZ2AffineDiagonalTubeParams frameSlope anchor
          heightScale transverseScale first).d -
        (pureWZ2AffineDiagonalTubeParams frameSlope anchor
          heightScale transverseScale second).d| ≤ r) :
    let width :=
      16 * (1 + heightScale) * (1 + transverseScale⁻¹) * r
    |first.a - second.a| ≤ width ∧
      |first.b - second.b| ≤ width ∧
      |first.c - second.c| ≤ width ∧
      |first.d - second.d| ≤ width := by
  dsimp only
  let n := pureWZ2HorizontalNorm frameSlope
  let A :=
    (pureWZ2AffineDiagonalTubeParams frameSlope anchor
      heightScale transverseScale first).a -
      (pureWZ2AffineDiagonalTubeParams frameSlope anchor
        heightScale transverseScale second).a
  let B :=
    (pureWZ2AffineDiagonalTubeParams frameSlope anchor
      heightScale transverseScale first).b -
      (pureWZ2AffineDiagonalTubeParams frameSlope anchor
        heightScale transverseScale second).b
  let C :=
    (pureWZ2AffineDiagonalTubeParams frameSlope anchor
      heightScale transverseScale first).c -
      (pureWZ2AffineDiagonalTubeParams frameSlope anchor
        heightScale transverseScale second).c
  let D :=
    (pureWZ2AffineDiagonalTubeParams frameSlope anchor
      heightScale transverseScale first).d -
      (pureWZ2AffineDiagonalTubeParams frameSlope anchor
        heightScale transverseScale second).d
  let da := first.a - second.a
  let db := first.b - second.b
  let dc := first.c - second.c
  let dd := first.d - second.d
  let U := dc + frameSlope * dd
  let V := -frameSlope * dc + dd
  let X := da + frameSlope * db
  let Y := -frameSlope * da + db
  have hnPos : 0 < n := pureWZ2HorizontalNorm_pos frameSlope
  have hnTwo : n ≤ 2 := by
    have hsquare := pureWZ2HorizontalNorm_sq frameSlope
    have hframeSq : frameSlope ^ 2 ≤ 1 := by
      nlinarith [abs_le.mp hframe]
    nlinarith
  have hA : |A| ≤ r := by simpa [A] using ha
  have hB : |B| ≤ r := by simpa [B] using hb
  have hC : |C| ≤ r := by simpa [C] using hc
  have hD : |D| ≤ r := by simpa [D] using hd
  have htransverseInv : 0 ≤ transverseScale⁻¹ :=
    (inv_pos.mpr htransverse).le
  have hnormNe : pureWZ2HorizontalNorm frameSlope ≠ 0 :=
    (pureWZ2HorizontalNorm_pos frameSlope).ne'
  have hUeq : U = n * heightScale * C := by
    dsimp only [U, C, dc, dd, n]
    simp only [pureWZ2AffineDiagonalTubeParams]
    field_simp [hnormNe, hheight.ne']
    ring
  have hVeq : V = n * heightScale / transverseScale * D := by
    dsimp only [V, D, dc, dd, n]
    simp only [pureWZ2AffineDiagonalTubeParams]
    field_simp [hnormNe, hheight.ne', htransverse.ne']
    ring
  have hXeq : X = n * A - anchor * U := by
    dsimp only [X, A, U, da, db, dc, dd, n]
    simp only [pureWZ2AffineDiagonalTubeParams]
    field_simp [hnormNe]
    ring
  have hYeq : Y = n / transverseScale * B - anchor * V := by
    dsimp only [Y, B, V, da, db, dc, dd, n]
    simp only [pureWZ2AffineDiagonalTubeParams]
    field_simp [hnormNe, htransverse.ne']
    ring
  have hU : |U| ≤ 2 * heightScale * r := by
    rw [hUeq, abs_mul, abs_mul, abs_of_pos hnPos, abs_of_pos hheight]
    gcongr
  have hV : |V| ≤ 2 * heightScale * transverseScale⁻¹ * r := by
    rw [hVeq, abs_mul]
    have hcoefficient : 0 ≤ n * heightScale / transverseScale :=
      (div_pos (mul_pos hnPos hheight) htransverse).le
    rw [abs_of_nonneg hcoefficient]
    calc
      n * heightScale / transverseScale * |D|
          ≤ (2 * heightScale / transverseScale) * r := by gcongr
      _ = 2 * heightScale * transverseScale⁻¹ * r := by
        rw [div_eq_mul_inv]
  have hX : |X| ≤ 2 * r + 2 * heightScale * r := by
    rw [hXeq]
    calc
      |n * A - anchor * U| ≤ |n * A| + |anchor * U| := abs_sub _ _
      _ = n * |A| + |anchor| * |U| := by
        rw [abs_mul, abs_mul, abs_of_pos hnPos]
      _ ≤ 2 * r + 1 * (2 * heightScale * r) := by gcongr
      _ = 2 * r + 2 * heightScale * r := by ring
  have hY : |Y| ≤ 2 * transverseScale⁻¹ * r +
      2 * heightScale * transverseScale⁻¹ * r := by
    have hnInv : n * transverseScale⁻¹ ≤ 2 * transverseScale⁻¹ :=
      mul_le_mul_of_nonneg_right hnTwo htransverseInv
    rw [hYeq]
    calc
      |n / transverseScale * B - anchor * V|
          ≤ |n / transverseScale * B| + |anchor * V| := abs_sub _ _
      _ = (n / transverseScale) * |B| + |anchor| * |V| := by
        rw [abs_mul, abs_mul, abs_of_pos (div_pos hnPos htransverse)]
      _ ≤ (2 * transverseScale⁻¹) * r +
          1 * (2 * heightScale * transverseScale⁻¹ * r) := by
        gcongr
        rw [div_eq_mul_inv]
        exact hnInv
      _ = 2 * transverseScale⁻¹ * r +
          2 * heightScale * transverseScale⁻¹ * r := by ring
  have hrotationCoefficient : 1 ≤ 1 + frameSlope ^ 2 := by
    nlinarith [sq_nonneg frameSlope]
  have hda : |da| ≤
      2 * (1 + heightScale) * (1 + transverseScale⁻¹) * r := by
    have heq : (1 + frameSlope ^ 2) * da = X - frameSlope * Y := by
      dsimp only [X, Y, da, db]
      ring
    have hbound : |(1 + frameSlope ^ 2) * da| ≤
        2 * (1 + heightScale) * (1 + transverseScale⁻¹) * r := by
      rw [heq]
      calc
        |X - frameSlope * Y| ≤ |X| + |frameSlope * Y| := abs_sub _ _
        _ = |X| + |frameSlope| * |Y| := by rw [abs_mul]
        _ ≤ (2 * r + 2 * heightScale * r) +
            1 * (2 * transverseScale⁻¹ * r +
              2 * heightScale * transverseScale⁻¹ * r) := by gcongr
        _ = 2 * (1 + heightScale) * (1 + transverseScale⁻¹) * r := by ring
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + frameSlope ^ 2)] at hbound
    calc
      |da| = 1 * |da| := by ring
      _ ≤ (1 + frameSlope ^ 2) * |da| :=
        mul_le_mul_of_nonneg_right hrotationCoefficient (abs_nonneg da)
      _ ≤ _ := hbound
  have hdb : |db| ≤
      2 * (1 + heightScale) * (1 + transverseScale⁻¹) * r := by
    have heq : (1 + frameSlope ^ 2) * db = frameSlope * X + Y := by
      dsimp only [X, Y, da, db]
      ring
    have hbound : |(1 + frameSlope ^ 2) * db| ≤
        2 * (1 + heightScale) * (1 + transverseScale⁻¹) * r := by
      rw [heq]
      calc
        |frameSlope * X + Y| ≤ |frameSlope * X| + |Y| := abs_add_le _ _
        _ = |frameSlope| * |X| + |Y| := by rw [abs_mul]
        _ ≤ 1 * (2 * r + 2 * heightScale * r) +
            (2 * transverseScale⁻¹ * r +
              2 * heightScale * transverseScale⁻¹ * r) := by gcongr
        _ = 2 * (1 + heightScale) * (1 + transverseScale⁻¹) * r := by ring
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + frameSlope ^ 2)] at hbound
    calc
      |db| = 1 * |db| := by ring
      _ ≤ (1 + frameSlope ^ 2) * |db| :=
        mul_le_mul_of_nonneg_right hrotationCoefficient (abs_nonneg db)
      _ ≤ _ := hbound
  have hdc : |dc| ≤ 2 * heightScale *
      (1 + transverseScale⁻¹) * r := by
    have heq : (1 + frameSlope ^ 2) * dc = U - frameSlope * V := by
      dsimp only [U, V, dc, dd]
      ring
    have hbound : |(1 + frameSlope ^ 2) * dc| ≤
        2 * heightScale * (1 + transverseScale⁻¹) * r := by
      rw [heq]
      calc
        |U - frameSlope * V| ≤ |U| + |frameSlope * V| := abs_sub _ _
        _ = |U| + |frameSlope| * |V| := by rw [abs_mul]
        _ ≤ 2 * heightScale * r +
            1 * (2 * heightScale * transverseScale⁻¹ * r) := by gcongr
        _ = 2 * heightScale * (1 + transverseScale⁻¹) * r := by ring
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + frameSlope ^ 2)] at hbound
    calc
      |dc| = 1 * |dc| := by ring
      _ ≤ (1 + frameSlope ^ 2) * |dc| :=
        mul_le_mul_of_nonneg_right hrotationCoefficient (abs_nonneg dc)
      _ ≤ _ := hbound
  have hdd : |dd| ≤ 2 * heightScale *
      (1 + transverseScale⁻¹) * r := by
    have heq : (1 + frameSlope ^ 2) * dd = frameSlope * U + V := by
      dsimp only [U, V, dc, dd]
      ring
    have hbound : |(1 + frameSlope ^ 2) * dd| ≤
        2 * heightScale * (1 + transverseScale⁻¹) * r := by
      rw [heq]
      calc
        |frameSlope * U + V| ≤ |frameSlope * U| + |V| := abs_add_le _ _
        _ = |frameSlope| * |U| + |V| := by rw [abs_mul]
        _ ≤ 1 * (2 * heightScale * r) +
            2 * heightScale * transverseScale⁻¹ * r := by gcongr
        _ = 2 * heightScale * (1 + transverseScale⁻¹) * r := by ring
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + frameSlope ^ 2)] at hbound
    calc
      |dd| = 1 * |dd| := by ring
      _ ≤ (1 + frameSlope ^ 2) * |dd| :=
        mul_le_mul_of_nonneg_right hrotationCoefficient (abs_nonneg dd)
      _ ≤ _ := hbound
  have hab :
      2 * (1 + heightScale) * (1 + transverseScale⁻¹) * r ≤
        16 * (1 + heightScale) * (1 + transverseScale⁻¹) * r := by
    gcongr
    norm_num
  have hcd :
      2 * heightScale * (1 + transverseScale⁻¹) * r ≤
        16 * (1 + heightScale) * (1 + transverseScale⁻¹) * r := by
    calc
      2 * heightScale * (1 + transverseScale⁻¹) * r
          ≤ 2 * (1 + heightScale) * (1 + transverseScale⁻¹) * r := by
            gcongr
            linarith
      _ ≤ _ := hab
  exact ⟨by simpa [da] using hda.trans hab,
    by simpa [db] using hdb.trans hab,
    by simpa [dc] using hdc.trans hcd,
    by simpa [dd] using hdd.trans hcd⟩

end Kakeya.Assouad
