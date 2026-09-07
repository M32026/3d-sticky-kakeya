import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23FullGrainFubini
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23NormalTiltStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23PlanarProjectionFullness

/-!
# Produce the faithful normal-tilt witness in WZ1 Lemma 23

This is the bridge from one actual almost-full local grain to the planar
normal-tilt witness.  The only supplied proof leaf is the pure planar
projection-fullness dichotomy.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory Set

/-- Measurable coordinate equivalence used by the frozen planar leaf. -/
private def wz1Lemma23Point2Coordinates :
    Point2 ≃ᵐ (Fin 2 → ℝ) :=
  { toFun := WithLp.ofLp
    invFun := WithLp.toLp 2
    left_inv := WithLp.toLp_ofLp (2 : ENNReal)
    right_inv := WithLp.ofLp_toLp (2 : ENNReal)
    measurable_toFun :=
      (PiLp.continuous_ofLp
        (p := 2) (β := fun _ : Fin 2 => ℝ)).measurable
    measurable_invFun :=
      (PiLp.continuous_toLp
        (p := 2) (β := fun _ : Fin 2 => ℝ)).measurable }

/-- Actual almost-full local grain data inside one `sqrt rho` coarse cube. -/
structure WZ1Lemma23FullLocalGrainInput
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ) where
  grain : Set Point3
  grain_measurable : MeasurableSet grain
  grain_finite : volume grain ≠ ⊤
  heightLeft : ℝ
  grain_height :
    ∀ point ∈ grain,
      point (2 : Fin 3) ∈
        Set.Ico heightLeft (heightLeft + Real.sqrt rho)
  grain_volume :
    Kakeya.realRpowENN rho (2 + 2 * eta) ≤
      volume grain
  center : Point3
  normal : Point3
  localProjectionCenter : ℝ
  normal_unit : ‖normal‖ = 1
  normal_vertical : |normal (2 : Fin 3)| ≤ 1 / 2
  grain_square :
    ∀ point ∈ grain,
      |point 0 - center 0| ≤ Real.sqrt rho ∧
        |point 1 - center 1| ≤ Real.sqrt rho
  grain_local_strip :
    ∀ point ∈ grain,
      |inner ℝ point normal - localProjectionCenter| ≤ rho
  slope_small :
    ∀ z ∈ Set.Ico heightLeft
      (heightLeft + Real.sqrt rho),
      |slope z| ≤ 1 / 10
  projected : Set ℝ
  globalAD :
    ∀ z ∈ Set.Ico heightLeft
      (heightLeft + Real.sqrt rho),
      IsADSet1 projected rho (1 - sigma) C
  global_projection_sub :
    ∀ z ∈ Set.Ico heightLeft
        (heightLeft + Real.sqrt rho),
      (fun point : Point2 =>
        point 0 + slope z * point 1) ''
          wz1Lemma23PlanarSlice grain z ⊆
        projected

/-- Full local-grain data with the source-package slope bound `3`. -/
structure WZ1Lemma23FullLocalGrainInputGeneralized
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ) where
  grain : Set Point3
  grain_measurable : MeasurableSet grain
  grain_finite : volume grain ≠ ⊤
  heightLeft : ℝ
  grain_height :
    ∀ point ∈ grain,
      point (2 : Fin 3) ∈
        Set.Ico heightLeft (heightLeft + Real.sqrt rho)
  grain_volume :
    Kakeya.realRpowENN rho (2 + 2 * eta) ≤
      volume grain
  center : Point3
  normal : Point3
  localProjectionCenter : ℝ
  normal_unit : ‖normal‖ = 1
  normal_vertical : |normal (2 : Fin 3)| ≤ 1 / 2
  grain_square :
    ∀ point ∈ grain,
      |point 0 - center 0| ≤ Real.sqrt rho ∧
        |point 1 - center 1| ≤ Real.sqrt rho
  grain_local_strip :
    ∀ point ∈ grain,
      |inner ℝ point normal - localProjectionCenter| ≤ rho
  slope_small :
    ∀ z ∈ Set.Ico heightLeft
      (heightLeft + Real.sqrt rho),
      |slope z| ≤ 3
  projected : ℝ → Set ℝ
  globalAD :
    ∀ z ∈ Set.Ico heightLeft
      (heightLeft + Real.sqrt rho),
      IsADSet1 (projected z) rho (1 - sigma) C
  global_projection_sub :
    ∀ z ∈ Set.Ico heightLeft
        (heightLeft + Real.sqrt rho),
      (fun point : Point2 =>
        point 0 + slope z * point 1) ''
          wz1Lemma23PlanarSlice grain z ⊆
        projected z

/-- The geometric part of a generalized full local grain.  Unlike
`WZ1Lemma23FullLocalGrainInputGeneralized`, this record does not ask for
global AD on every height in the window.  The normal-first proof chooses one
height by Fubini, so a caller may instead provide the global certificate only
at that actual height. -/
structure WZ1Lemma23FullLocalGrainGeometryGeneralized
    (rho eta : ℝ) (slope : ℝ → ℝ) where
  grain : Set Point3
  grain_measurable : MeasurableSet grain
  grain_finite : volume grain ≠ ⊤
  heightLeft : ℝ
  grain_height :
    ∀ point ∈ grain,
      point (2 : Fin 3) ∈
        Set.Ico heightLeft (heightLeft + Real.sqrt rho)
  grain_volume :
    Kakeya.realRpowENN rho (2 + 2 * eta) ≤
      volume grain
  center : Point3
  normal : Point3
  localProjectionCenter : ℝ
  normal_unit : ‖normal‖ = 1
  normal_vertical : |normal (2 : Fin 3)| ≤ 1 / 2
  grain_square :
    ∀ point ∈ grain,
      |point 0 - center 0| ≤ Real.sqrt rho ∧
        |point 1 - center 1| ≤ Real.sqrt rho
  grain_local_strip :
    ∀ point ∈ grain,
      |inner ℝ point normal - localProjectionCenter| ≤ rho
  slope_small :
    ∀ z ∈ Set.Ico heightLeft
      (heightLeft + Real.sqrt rho),
      |slope z| ≤ 3

/-- Forget the all-height global certificate while retaining the exact
geometric data used before the Fubini choice. -/
def WZ1Lemma23FullLocalGrainInputGeneralized.toGeometry
    {rho sigma eta : ℝ} {C : ENNReal} {slope : ℝ → ℝ}
    (input : WZ1Lemma23FullLocalGrainInputGeneralized
      rho sigma eta C slope) :
    WZ1Lemma23FullLocalGrainGeometryGeneralized rho eta slope :=
  { grain := input.grain
    grain_measurable := input.grain_measurable
    grain_finite := input.grain_finite
    heightLeft := input.heightLeft
    grain_height := input.grain_height
    grain_volume := input.grain_volume
    center := input.center
    normal := input.normal
    localProjectionCenter := input.localProjectionCenter
    normal_unit := input.normal_unit
    normal_vertical := input.normal_vertical
    grain_square := input.grain_square
    grain_local_strip := input.grain_local_strip
    slope_small := input.slope_small }

/--
One actual full local grain either already has small tilt at its Fubini slice,
or yields the complete faithful witness consumed by the closed normal-tilt
theorem.
-/
theorem wz1_lemma23_normal_tilt_witness_from_full_grain
    (hPlanar : WZ1Lemma23PlanarProjectionFullnessStatement)
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (heta : 0 < eta)
    (hsmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall : 12 * Real.sqrt rho ≤ 1)
    (input :
      WZ1Lemma23FullLocalGrainInput
        rho sigma eta C slope) :
    (∃ z ∈ Set.Ico input.heightLeft
        (input.heightLeft + Real.sqrt rho),
      |input.normal 1 - slope z * input.normal 0| ≤
        Real.sqrt rho) ∨
    ∃ witness :
      WZ1Lemma23NormalTiltWitness
        rho sigma eta C slope input.normal,
      witness.sliceHeight ∈
        Set.Ico input.heightLeft
          (input.heightLeft + Real.sqrt rho) := by
  rcases
      wz1_lemma23_full_grain_fubini
        input.grain_measurable hrho input.grain_finite
        input.grain_height input.grain_volume with
    ⟨z, hz, hsliceArea⟩
  let slice := wz1Lemma23PlanarSlice input.grain z
  have hsliceMeas : MeasurableSet slice := by
    have hmap :
        Continuous
          (fun point : Point2 =>
            point3 (point 0) (point 1) z) := by
      unfold point3
      fun_prop
    have hpreimage :
        slice =
          (fun point : Point2 =>
            point3 (point 0) (point 1) z) ⁻¹'
            input.grain := by
      ext point
      rw [wz1Lemma23_mem_planarSlice_iff]
      rfl
    rw [hpreimage]
    exact input.grain_measurable.preimage hmap.measurable
  have hsliceSquare :
      ∀ point ∈ slice,
        |point 0 - input.center 0| ≤ Real.sqrt rho ∧
          |point 1 - input.center 1| ≤ Real.sqrt rho := by
    intro point hpoint
    have hlift :
        point3 (point 0) (point 1) z ∈ input.grain :=
      wz1Lemma23_mem_planarSlice_iff.mp hpoint
    simpa [point3] using
      input.grain_square _ hlift
  have hsliceStrip :
      ∀ point ∈ slice,
        |input.normal 0 * point 0 + input.normal 1 * point 1 -
            (input.localProjectionCenter -
              z * input.normal 2)| ≤ rho := by
    intro point hpoint
    have hlift :
        point3 (point 0) (point 1) z ∈ input.grain :=
      wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hstrip := input.grain_local_strip _ hlift
    have hinner :
        inner ℝ (point3 (point 0) (point 1) z)
            input.normal =
          point 0 * input.normal 0 +
            point 1 * input.normal 1 +
              z * input.normal 2 := by
      rw [PiLp.inner_apply]
      simp [point3, Fin.sum_univ_succ, mul_comm]
      <;> ring
    rw [hinner] at hstrip
    convert hstrip using 1 <;> ring_nf
  let globalProjection : Set ℝ :=
    (fun point : Point2 =>
      point 0 + slope z * point 1) '' slice
  let stripCenter :=
    input.localProjectionCenter - z * input.normal 2
  let projectionCenter :=
    ((input.normal 0 + slope z * input.normal 1) *
          stripCenter -
        (input.normal 1 - slope z * input.normal 0) *
          (input.normal 0 * input.center 1 -
            input.normal 1 * input.center 0)) /
      (input.normal 0 ^ 2 + input.normal 1 ^ 2)
  let projectionRadius :=
    4 * rho + 4 * Real.sqrt rho *
      |input.normal 1 - slope z * input.normal 0|
  let planarCenter : Point2 :=
    WithLp.toLp 2 (fun i : Fin 2 =>
      input.center (Fin.castSucc i))
  let coordinateSlice : Set (Fin 2 → ℝ) :=
    wz1Lemma23Point2Coordinates '' slice
  let coordinateCenter : Fin 2 → ℝ :=
    wz1Lemma23Point2Coordinates planarCenter
  have hplanarCenter0 :
      planarCenter 0 = input.center 0 := by
    rfl
  have hplanarCenter1 :
      planarCenter 1 = input.center 1 := by
    rfl
  have hcoordinateSliceMeas :
      MeasurableSet coordinateSlice :=
    wz1Lemma23Point2Coordinates.measurableSet_image.mpr
      hsliceMeas
  have hcoordinateSliceVolume :
      volume coordinateSlice = volume slice := by
    have hmp :
        MeasurePreserving
          wz1Lemma23Point2Coordinates volume volume :=
      PiLp.volume_preserving_ofLp (Fin 2)
    have hpre :
        wz1Lemma23Point2Coordinates ⁻¹' coordinateSlice =
          slice :=
      Set.preimage_image_eq slice
        wz1Lemma23Point2Coordinates.injective
    have hmeasure :
        volume
            (wz1Lemma23Point2Coordinates ⁻¹'
              coordinateSlice) =
          volume coordinateSlice :=
      hmp.measure_preimage_emb
        wz1Lemma23Point2Coordinates.measurableEmbedding
        coordinateSlice
    rw [hpre] at hmeasure
    exact hmeasure.symm
  have hcoordinateSquare :
      ∀ point ∈ coordinateSlice,
        |point 0 - coordinateCenter 0| ≤ Real.sqrt rho ∧
          |point 1 - coordinateCenter 1| ≤ Real.sqrt rho := by
    rintro point ⟨source, hsource, rfl⟩
    simpa [coordinateCenter, planarCenter,
      wz1Lemma23Point2Coordinates] using
      hsliceSquare source hsource
  have hcoordinateStrip :
      ∀ point ∈ coordinateSlice,
        |input.normal 0 * point 0 + input.normal 1 * point 1 -
            stripCenter| ≤ rho := by
    rintro point ⟨source, hsource, rfl⟩
    simpa [wz1Lemma23Point2Coordinates] using
      hsliceStrip source hsource
  have hcoordinateProjection :
      (fun point : Fin 2 → ℝ =>
          point 0 + slope z * point 1) '' coordinateSlice =
        globalProjection := by
    ext value
    simp only [coordinateSlice, globalProjection,
      Set.mem_image]
    constructor
    · rintro ⟨_, ⟨source, hsource, rfl⟩, rfl⟩
      exact ⟨source, hsource, rfl⟩
    · rintro ⟨source, hsource, rfl⟩
      exact
        ⟨wz1Lemma23Point2Coordinates source,
          ⟨source, hsource, rfl⟩, rfl⟩
  have hprojectionSub :
      globalProjection ⊆ input.projected :=
    input.global_projection_sub z hz
  rcases
      hPlanar rho eta hrho hrho_one heta hsmall
        coordinateSlice
        coordinateCenter
        stripCenter
        input.normal (slope z)
        hcoordinateSliceMeas
        input.normal_unit input.normal_vertical
        (input.slope_small z hz)
        hcoordinateSquare hcoordinateStrip
        (by
          rw [hcoordinateSliceVolume]
          exact hsliceArea) with
    htilt | ⟨density, hdensity, hfull⟩
  · exact Or.inl ⟨z, hz, htilt⟩
  · right
    rw [hcoordinateProjection] at hfull
    let witness :
        WZ1Lemma23NormalTiltWitness
          rho sigma eta C slope input.normal :=
      { sliceHeight := z
        slice := slice
        sliceCenter :=
          planarCenter
        stripCenter := stripCenter
        projected := input.projected
        projectionCenter := projectionCenter
        projectionRadius := projectionRadius
        slice_measurable := hsliceMeas
        slice_in_square := by
          intro point hpoint
          rw [hplanarCenter0, hplanarCenter1]
          exact hsliceSquare point hpoint
        slice_in_local_strip := by
          intro point hpoint
          exact hsliceStrip point hpoint
        normal_unit := input.normal_unit
        normal_vertical := input.normal_vertical
        slope_small := input.slope_small z hz
        globalAD := input.globalAD z hz
        tiltedProjection :=
          (fun point : Point2 =>
            point 0 * (-slope z) + point 1) '' slice
        tiltedProjection_eq := rfl
        globalProjection := globalProjection
        globalProjection_eq := rfl
        projectionCenter_eq := rfl
        projectionRadius_eq := rfl
        globalProjection_sub_projected := hprojectionSub
        projectionRadius_upper := by
          dsimp [projectionRadius]
          have h0 : |input.normal 0| ≤ 1 := by
            have h := PiLp.norm_apply_le input.normal 0
            simpa [Real.norm_eq_abs, input.normal_unit] using h
          have h1 : |input.normal 1| ≤ 1 := by
            have h := PiLp.norm_apply_le input.normal 1
            simpa [Real.norm_eq_abs, input.normal_unit] using h
          have hslopeBound := input.slope_small z hz
          have htiltBound :
              |input.normal 1 - slope z * input.normal 0| ≤ 2 := by
            calc
              |input.normal 1 - slope z * input.normal 0|
                  ≤ |input.normal 1| +
                      |slope z * input.normal 0| := abs_sub _ _
              _ = |input.normal 1| +
                  |slope z| * |input.normal 0| := by rw [abs_mul]
              _ ≤ 1 + (1 / 10 : ℝ) * 1 := by gcongr
              _ ≤ 2 := by norm_num
          have hrhoSqrt : rho ≤ Real.sqrt rho := by
            have hsq := Real.sq_sqrt hrho.le
            nlinarith [Real.sqrt_nonneg rho, hrho_one]
          exact
            (by
              calc
                4 * rho +
                      4 * Real.sqrt rho *
                        |input.normal 1 - slope z * input.normal 0|
                    ≤ 4 * Real.sqrt rho +
                        4 * Real.sqrt rho * 2 := by gcongr
                _ = 12 * Real.sqrt rho := by ring
                _ ≤ 1 := hrootSmall)
        density := density
        density_lower := hdensity
        globalProjection_full := hfull }
    exact ⟨witness, hz⟩

/--
The full-grain witness producer for slope bound `3`.  In the witness branch
it records the complementary lower tilt bound and uses `hrootSmall20` to
control the enlarged projection radius.
-/
theorem wz1_lemma23_normal_tilt_witness_from_full_grain_generalized_of_fubini
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (heta : 0 < eta)
    (hsmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (input : WZ1Lemma23FullLocalGrainGeometryGeneralized rho eta slope)
    (hglobalAt :
      ∀ z (_hz : z ∈ Set.Ico input.heightLeft
          (input.heightLeft + Real.sqrt rho)),
        Kakeya.realRpowENN rho (3 / 2 + 2 * eta) ≤
            volume (wz1Lemma23PlanarSlice input.grain z) →
        ∃ projected : Set ℝ,
          IsADSet1 projected rho (1 - sigma) C ∧
          (fun point : Point2 => point 0 + slope z * point 1) ''
              wz1Lemma23PlanarSlice input.grain z ⊆ projected) :
    (∃ z ∈ Set.Ico input.heightLeft
        (input.heightLeft + Real.sqrt rho),
      |input.normal 1 - slope z * input.normal 0| ≤
        Real.sqrt rho) ∨
    ∃ witness :
      WZ1Lemma23NormalTiltWitnessGeneralized
        rho sigma eta C slope input.normal,
      witness.sliceHeight ∈
        Set.Ico input.heightLeft
          (input.heightLeft + Real.sqrt rho) := by
  rcases
      wz1_lemma23_full_grain_fubini
        input.grain_measurable hrho input.grain_finite
        input.grain_height input.grain_volume with
    ⟨z, hz, hsliceArea⟩
  let slice := wz1Lemma23PlanarSlice input.grain z
  rcases hglobalAt z hz (by simpa only [slice] using hsliceArea) with
    ⟨projected, hglobalAD, hprojectionSub⟩
  have hsliceMeas : MeasurableSet slice := by
    have hmap :
        Continuous
          (fun point : Point2 =>
            point3 (point 0) (point 1) z) := by
      unfold point3
      fun_prop
    have hpreimage :
        slice =
          (fun point : Point2 =>
            point3 (point 0) (point 1) z) ⁻¹'
            input.grain := by
      ext point
      rw [wz1Lemma23_mem_planarSlice_iff]
      rfl
    rw [hpreimage]
    exact input.grain_measurable.preimage hmap.measurable
  have hsliceSquare :
      ∀ point ∈ slice,
        |point 0 - input.center 0| ≤ Real.sqrt rho ∧
          |point 1 - input.center 1| ≤ Real.sqrt rho := by
    intro point hpoint
    have hlift :
        point3 (point 0) (point 1) z ∈ input.grain :=
      wz1Lemma23_mem_planarSlice_iff.mp hpoint
    simpa [point3] using
      input.grain_square _ hlift
  have hsliceStrip :
      ∀ point ∈ slice,
        |input.normal 0 * point 0 + input.normal 1 * point 1 -
            (input.localProjectionCenter -
              z * input.normal 2)| ≤ rho := by
    intro point hpoint
    have hlift :
        point3 (point 0) (point 1) z ∈ input.grain :=
      wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hstrip := input.grain_local_strip _ hlift
    have hinner :
        inner ℝ (point3 (point 0) (point 1) z)
            input.normal =
          point 0 * input.normal 0 +
            point 1 * input.normal 1 +
              z * input.normal 2 := by
      rw [PiLp.inner_apply]
      simp [point3, Fin.sum_univ_succ, mul_comm]
      <;> ring
    rw [hinner] at hstrip
    convert hstrip using 1 <;> ring_nf
  let globalProjection : Set ℝ :=
    (fun point : Point2 =>
      point 0 + slope z * point 1) '' slice
  let stripCenter :=
    input.localProjectionCenter - z * input.normal 2
  let tilt := input.normal 1 - slope z * input.normal 0
  let projectionCenter :=
    ((input.normal 0 + slope z * input.normal 1) *
          stripCenter -
        tilt *
          (input.normal 0 * input.center 1 -
            input.normal 1 * input.center 0)) /
      (input.normal 0 ^ 2 + input.normal 1 ^ 2)
  let projectionRadius :=
    4 * rho + 4 * Real.sqrt rho * |tilt|
  let planarCenter : Point2 :=
    WithLp.toLp 2 (fun i : Fin 2 =>
      input.center (Fin.castSucc i))
  let coordinateSlice : Set (Fin 2 → ℝ) :=
    wz1Lemma23Point2Coordinates '' slice
  let coordinateCenter : Fin 2 → ℝ :=
    wz1Lemma23Point2Coordinates planarCenter
  have hplanarCenter0 :
      planarCenter 0 = input.center 0 := by
    rfl
  have hplanarCenter1 :
      planarCenter 1 = input.center 1 := by
    rfl
  have hcoordinateSliceMeas :
      MeasurableSet coordinateSlice :=
    wz1Lemma23Point2Coordinates.measurableSet_image.mpr
      hsliceMeas
  have hcoordinateSliceVolume :
      volume coordinateSlice = volume slice := by
    have hmp :
        MeasurePreserving
          wz1Lemma23Point2Coordinates volume volume :=
      PiLp.volume_preserving_ofLp (Fin 2)
    have hpre :
        wz1Lemma23Point2Coordinates ⁻¹' coordinateSlice =
          slice :=
      Set.preimage_image_eq slice
        wz1Lemma23Point2Coordinates.injective
    have hmeasure :
        volume
            (wz1Lemma23Point2Coordinates ⁻¹'
              coordinateSlice) =
          volume coordinateSlice :=
      hmp.measure_preimage_emb
        wz1Lemma23Point2Coordinates.measurableEmbedding
        coordinateSlice
    rw [hpre] at hmeasure
    exact hmeasure.symm
  have hcoordinateSquare :
      ∀ point ∈ coordinateSlice,
        |point 0 - coordinateCenter 0| ≤ Real.sqrt rho ∧
          |point 1 - coordinateCenter 1| ≤ Real.sqrt rho := by
    rintro point ⟨source, hsource, rfl⟩
    simpa [coordinateCenter, planarCenter,
      wz1Lemma23Point2Coordinates] using
      hsliceSquare source hsource
  have hcoordinateStrip :
      ∀ point ∈ coordinateSlice,
        |input.normal 0 * point 0 + input.normal 1 * point 1 -
            stripCenter| ≤ rho := by
    rintro point ⟨source, hsource, rfl⟩
    simpa [wz1Lemma23Point2Coordinates] using
      hsliceStrip source hsource
  have hcoordinateProjection :
      (fun point : Fin 2 → ℝ =>
          point 0 + slope z * point 1) '' coordinateSlice =
        globalProjection := by
    ext value
    simp only [coordinateSlice, globalProjection,
      Set.mem_image]
    constructor
    · rintro ⟨_, ⟨source, hsource, rfl⟩, rfl⟩
      exact ⟨source, hsource, rfl⟩
    · rintro ⟨source, hsource, rfl⟩
      exact
        ⟨wz1Lemma23Point2Coordinates source,
          ⟨source, hsource, rfl⟩, rfl⟩
  have hprojectionSub' : globalProjection ⊆ projected := by
    simpa only [globalProjection, slice] using hprojectionSub
  by_cases htilt_le : |tilt| ≤ Real.sqrt rho
  · exact Or.inl ⟨z, hz, htilt_le⟩
  · have htilt_gt : |tilt| > Real.sqrt rho :=
      lt_of_not_ge htilt_le
    rcases
        wz1_lemma23_planar_projection_fullness_generalized
          rho eta hrho hrho_one heta hsmall
          coordinateSlice coordinateCenter stripCenter
          input.normal (slope z)
          hcoordinateSliceMeas
          input.normal_unit input.normal_vertical
          (input.slope_small z hz)
          hcoordinateSquare hcoordinateStrip
          (by
            rw [hcoordinateSliceVolume]
            exact hsliceArea) with
      htilt2 | ⟨density, hdensity, hfull⟩
    · exact False.elim (htilt_le (by simpa [tilt] using htilt2))
    · right
      rw [hcoordinateProjection] at hfull
      let witness :
          WZ1Lemma23NormalTiltWitnessGeneralized
            rho sigma eta C slope input.normal :=
        { sliceHeight := z
          slice := slice
          sliceCenter := planarCenter
          stripCenter := stripCenter
          projected := projected
          projectionCenter := projectionCenter
          projectionRadius := projectionRadius
          slice_measurable := hsliceMeas
          slice_in_square := by
            intro point hpoint
            rw [hplanarCenter0, hplanarCenter1]
            exact hsliceSquare point hpoint
          slice_in_local_strip := by
            intro point hpoint
            exact hsliceStrip point hpoint
          normal_unit := input.normal_unit
          normal_vertical := input.normal_vertical
          slope_small := input.slope_small z hz
          tilt_lower := htilt_gt.le
          globalAD := hglobalAD
          tiltedProjection :=
            (fun point : Point2 =>
              point 0 * (-slope z) + point 1) '' slice
          tiltedProjection_eq := rfl
          globalProjection := globalProjection
          globalProjection_eq := rfl
          projectionCenter_eq := rfl
          projectionRadius_eq := rfl
          globalProjection_sub_projected := hprojectionSub'
          projectionRadius_upper := by
            dsimp [projectionRadius, tilt]
            have h0 : |input.normal 0| ≤ 1 := by
              have h := PiLp.norm_apply_le input.normal 0
              simpa [Real.norm_eq_abs, input.normal_unit] using h
            have h1 : |input.normal 1| ≤ 1 := by
              have h := PiLp.norm_apply_le input.normal 1
              simpa [Real.norm_eq_abs, input.normal_unit] using h
            have hslopeBound : |slope z| ≤ 3 :=
              input.slope_small z hz
            have htiltBound : |tilt| ≤ 4 := by
              calc
                |tilt|
                    ≤ |input.normal 1| +
                        |slope z * input.normal 0| := abs_sub _ _
                _ = |input.normal 1| +
                    |slope z| * |input.normal 0| := by rw [abs_mul]
                _ ≤ 1 + (3 : ℝ) * 1 := by gcongr
                _ ≤ 4 := by norm_num
            have hrhoSqrt : rho ≤ Real.sqrt rho := by
              have hsq := Real.sq_sqrt hrho.le
              nlinarith [Real.sqrt_nonneg rho, hrho_one]
            calc
              4 * rho + 4 * Real.sqrt rho * |tilt|
                  ≤ 4 * Real.sqrt rho +
                      4 * Real.sqrt rho * 4 := by gcongr
              _ = 20 * Real.sqrt rho := by ring
              _ ≤ 1 := hrootSmall20
          density := density
          density_lower := hdensity
          globalProjection_full := hfull }
      exact ⟨witness, hz⟩

/-- Compatibility form supplying the selected-height callback from the former
all-window fields. -/
theorem wz1_lemma23_normal_tilt_witness_from_full_grain_generalized
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (heta : 0 < eta)
    (hsmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (input :
      WZ1Lemma23FullLocalGrainInputGeneralized
        rho sigma eta C slope) :
    (∃ z ∈ Set.Ico input.heightLeft
        (input.heightLeft + Real.sqrt rho),
      |input.normal 1 - slope z * input.normal 0| ≤
        Real.sqrt rho) ∨
    ∃ witness :
      WZ1Lemma23NormalTiltWitnessGeneralized
        rho sigma eta C slope input.normal,
      witness.sliceHeight ∈
        Set.Ico input.heightLeft
          (input.heightLeft + Real.sqrt rho) := by
  exact wz1_lemma23_normal_tilt_witness_from_full_grain_generalized_of_fubini
    rho sigma eta C slope hrho hrho_one heta hsmall hrootSmall20
    input.toGeometry (fun z hz _hslice =>
      ⟨input.projected z, input.globalAD z hz,
        input.global_projection_sub z hz⟩)

end

end Kakeya.Assouad
