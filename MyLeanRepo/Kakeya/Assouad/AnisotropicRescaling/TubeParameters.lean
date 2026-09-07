import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.MapInjectivity
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameters

/-!
# Tube parameters under anisotropic rescaling

Whole-line provenance determines the exact four vertical-chart parameters of
the affine image line.  This module keeps the statement at the supporting-line
level and does not infer containment of modeled unit segments.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The image of four vertical-chart line parameters under the affine map. -/
def anisotropicTubeParams
    (g : SlopeFunction) (c d m : ℝ) (params : TubeParams) : TubeParams :=
  let length := d - c
  let midpoint := c + length / 2
  let gmid := g midpoint
  {
    a := params.a + gmid * params.b +
      midpoint * (params.c + gmid * params.d)
    b := (m * length / 2) * (params.b + midpoint * params.d)
    c := (length / 2) * (params.c + gmid * params.d)
    d := (m * length ^ 2 / 4) * params.d
  }

/-- The point on a tube's supporting line with prescribed height. -/
def tubeAxisPointAtHeight {delta : ℝ}
    (T : Kakeya.DeltaTube delta) (z : ℝ) : Point3 :=
  T.base + ((z - T.base (2 : Fin 3)) /
    T.direction (2 : Fin 3)) • T.direction

lemma tubeAxisPointAtHeight_mem {delta : ℝ}
    (T : Kakeya.DeltaTube delta) (z : ℝ) :
    tubeAxisPointAtHeight T z ∈ tubeAxisLine T := by
  exact ⟨(z - T.base (2 : Fin 3)) / T.direction (2 : Fin 3), rfl⟩

lemma tubeAxisPointAtHeight_coord_two {delta : ℝ}
    (T : Kakeya.DeltaTube delta)
    (hvertical : T.direction (2 : Fin 3) ≠ 0)
    (z : ℝ) :
    tubeAxisPointAtHeight T z (2 : Fin 3) = z := by
  simp [tubeAxisPointAtHeight]
  field_simp [hvertical]
  ring

lemma tubeAxisPointAtHeight_coord_zero {delta : ℝ}
    (T : Kakeya.DeltaTube delta)
    (hvertical : T.direction (2 : Fin 3) ≠ 0)
    (z : ℝ) :
    tubeAxisPointAtHeight T z (0 : Fin 3) =
      (tubeParamsOfTube T).a + (tubeParamsOfTube T).c * z := by
  simp [tubeAxisPointAtHeight, tubeParamsOfTube]
  field_simp [hvertical]
  ring

lemma tubeAxisPointAtHeight_coord_one {delta : ℝ}
    (T : Kakeya.DeltaTube delta)
    (hvertical : T.direction (2 : Fin 3) ≠ 0)
    (z : ℝ) :
    tubeAxisPointAtHeight T z (1 : Fin 3) =
      (tubeParamsOfTube T).b + (tubeParamsOfTube T).d * z := by
  simp [tubeAxisPointAtHeight, tubeParamsOfTube]
  field_simp [hvertical]
  ring

lemma tubeAxisLine_coord_zero {delta : ℝ}
    (T : Kakeya.DeltaTube delta)
    (hvertical : T.direction (2 : Fin 3) ≠ 0)
    {point : Point3} (hpoint : point ∈ tubeAxisLine T) :
    point (0 : Fin 3) =
      (tubeParamsOfTube T).a +
        (tubeParamsOfTube T).c * point (2 : Fin 3) := by
  rcases hpoint with ⟨t, rfl⟩
  simp [tubeParamsOfTube]
  field_simp [hvertical]
  ring

lemma tubeAxisLine_coord_one {delta : ℝ}
    (T : Kakeya.DeltaTube delta)
    (hvertical : T.direction (2 : Fin 3) ≠ 0)
    {point : Point3} (hpoint : point ∈ tubeAxisLine T) :
    point (1 : Fin 3) =
      (tubeParamsOfTube T).b +
        (tubeParamsOfTube T).d * point (2 : Fin 3) := by
  rcases hpoint with ⟨t, rfl⟩
  simp [tubeParamsOfTube]
  field_simp [hvertical]
  ring

/--
Two vertical-chart tubes with the same supporting line have the same four
line parameters, independently of their stored unit-segment basepoints or
orientations.
-/
lemma tubeParamsOfTube_eq_of_axis_eq
    {delta rho : ℝ}
    (S : Kakeya.DeltaTube delta)
    (T : Kakeya.DeltaTube rho)
    (hSvertical : S.direction (2 : Fin 3) ≠ 0)
    (hTvertical : T.direction (2 : Fin 3) ≠ 0)
    (haxis : tubeAxisLine T = tubeAxisLine S) :
    tubeParamsOfTube T = tubeParamsOfTube S := by
  have hpointT : ∀ z : ℝ,
      tubeAxisPointAtHeight T z ∈ tubeAxisLine S := by
    intro z
    rw [← haxis]
    exact tubeAxisPointAtHeight_mem T z
  apply TubeParams.ext
  · have h0 :=
      tubeAxisLine_coord_zero S hSvertical
        (hpointT 0)
    have hT0 := tubeAxisPointAtHeight_coord_zero T hTvertical 0
    have hT2 := tubeAxisPointAtHeight_coord_two T hTvertical 0
    rw [hT0, hT2] at h0
    simpa using h0
  · have h0 :=
      tubeAxisLine_coord_one S hSvertical
        (hpointT 0)
    have hT1 := tubeAxisPointAtHeight_coord_one T hTvertical 0
    have hT2 := tubeAxisPointAtHeight_coord_two T hTvertical 0
    rw [hT1, hT2] at h0
    simpa using h0
  · have h0 :=
      tubeAxisLine_coord_zero S hSvertical
        (hpointT 0)
    have h1 :=
      tubeAxisLine_coord_zero S hSvertical
        (hpointT 1)
    have hT00 := tubeAxisPointAtHeight_coord_zero T hTvertical 0
    have hT01 := tubeAxisPointAtHeight_coord_zero T hTvertical 1
    have hT20 := tubeAxisPointAtHeight_coord_two T hTvertical 0
    have hT21 := tubeAxisPointAtHeight_coord_two T hTvertical 1
    rw [hT00, hT20] at h0
    rw [hT01, hT21] at h1
    linarith
  · have h0 :=
      tubeAxisLine_coord_one S hSvertical
        (hpointT 0)
    have h1 :=
      tubeAxisLine_coord_one S hSvertical
        (hpointT 1)
    have hT10 := tubeAxisPointAtHeight_coord_one T hTvertical 0
    have hT11 := tubeAxisPointAtHeight_coord_one T hTvertical 1
    have hT20 := tubeAxisPointAtHeight_coord_two T hTvertical 0
    have hT21 := tubeAxisPointAtHeight_coord_two T hTvertical 1
    rw [hT10, hT20] at h0
    rw [hT11, hT21] at h1
    linarith

/--
The image of the source axis point corresponding to normalized height `z`
has the coordinates encoded by `anisotropicTubeParams`.
-/
lemma anisotropicRescalingMap_axisPointAtHeight
    {delta : ℝ}
    (g : SlopeFunction) {c d m : ℝ} (hcd : c < d)
    (S : Kakeya.DeltaTube delta)
    (hvertical : S.direction (2 : Fin 3) ≠ 0)
    (z : ℝ) :
    let sourceHeight := c + (d - c) / 2 * (z + 1)
    let point :=
      anisotropicRescalingMap g c d m
        (tubeAxisPointAtHeight S sourceHeight)
    let params :=
      anisotropicTubeParams g c d m (tubeParamsOfTube S)
    point (0 : Fin 3) = params.a + params.c * z ∧
      point (1 : Fin 3) = params.b + params.d * z ∧
      point (2 : Fin 3) = z := by
  dsimp only
  have hsource2 :=
    tubeAxisPointAtHeight_coord_two S hvertical
      (c + (d - c) / 2 * (z + 1))
  have hsource0 :=
    tubeAxisPointAtHeight_coord_zero S hvertical
      (c + (d - c) / 2 * (z + 1))
  have hsource1 :=
    tubeAxisPointAtHeight_coord_one S hvertical
      (c + (d - c) / 2 * (z + 1))
  constructor
  · simp only [anisotropicRescalingMap_coord]
    rw [hsource0, hsource1]
    simp [anisotropicTubeParams]
    ring
  constructor
  · simp only [anisotropicRescalingMap_coord]
    rw [hsource1]
    simp [anisotropicTubeParams]
    ring
  · simp only [anisotropicRescalingMap_coord]
    rw [hsource2]
    have hne : d - c ≠ 0 := sub_ne_zero.mpr hcd.ne'
    field_simp [hne]
    ring

/--
Whole-line provenance determines the exact target line parameters.
-/
lemma tubeParamsOfTube_eq_anisotropic_of_axis_image
    {delta rho : ℝ}
    (g : SlopeFunction) {c d m : ℝ} (hcd : c < d)
    (S : Kakeya.DeltaTube delta)
    (hSvertical : S.direction (2 : Fin 3) ≠ 0)
    (A : Kakeya.DeltaTube rho)
    (hAvertical : A.direction (2 : Fin 3) ≠ 0)
    (haxis :
      tubeAxisLine A =
        anisotropicRescalingMap g c d m '' tubeAxisLine S) :
    tubeParamsOfTube A =
      anisotropicTubeParams g c d m (tubeParamsOfTube S) := by
  let sourceHeight : ℝ → ℝ := fun z =>
    c + (d - c) / 2 * (z + 1)
  let imagePoint : ℝ → Point3 := fun z =>
    anisotropicRescalingMap g c d m
      (tubeAxisPointAtHeight S (sourceHeight z))
  let params := anisotropicTubeParams g c d m (tubeParamsOfTube S)
  have himage : ∀ z, imagePoint z ∈ tubeAxisLine A := by
    intro z
    rw [haxis]
    exact ⟨tubeAxisPointAtHeight S (sourceHeight z),
      tubeAxisPointAtHeight_mem S (sourceHeight z), rfl⟩
  have hcoords : ∀ z,
      imagePoint z (0 : Fin 3) = params.a + params.c * z ∧
      imagePoint z (1 : Fin 3) = params.b + params.d * z ∧
      imagePoint z (2 : Fin 3) = z := by
    intro z
    exact anisotropicRescalingMap_axisPointAtHeight
      g hcd S hSvertical z
  have htarget0 : ∀ z,
      imagePoint z (0 : Fin 3) =
        (tubeParamsOfTube A).a +
          (tubeParamsOfTube A).c * imagePoint z (2 : Fin 3) :=
    fun z => tubeAxisLine_coord_zero A hAvertical (himage z)
  have htarget1 : ∀ z,
      imagePoint z (1 : Fin 3) =
        (tubeParamsOfTube A).b +
          (tubeParamsOfTube A).d * imagePoint z (2 : Fin 3) :=
    fun z => tubeAxisLine_coord_one A hAvertical (himage z)
  apply TubeParams.ext
  · have h := htarget0 0
    rw [(hcoords 0).1, (hcoords 0).2.2] at h
    simpa using h.symm
  · have h := htarget1 0
    rw [(hcoords 0).2.1, (hcoords 0).2.2] at h
    simpa using h.symm
  · have hzero := htarget0 0
    have hone := htarget0 1
    rw [(hcoords 0).1, (hcoords 0).2.2] at hzero
    rw [(hcoords 1).1, (hcoords 1).2.2] at hone
    have ha : (tubeParamsOfTube A).a = params.a := by
      simpa using hzero.symm
    rw [ha] at hone
    linarith
  · have hzero := htarget1 0
    have hone := htarget1 1
    rw [(hcoords 0).2.1, (hcoords 0).2.2] at hzero
    rw [(hcoords 1).2.1, (hcoords 1).2.2] at hone
    have hb : (tubeParamsOfTube A).b = params.b := by
      simpa using hzero.symm
    rw [hb] at hone
    linarith

end Kakeya.Assouad
