import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.QuantitativeConfiguration
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperGlobalADVolumeUpper
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectionArea
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GoodHeights

/-!
# Source common-bin spatial-cell slice bound

This file proves the single-side-`s` estimate used for the common-bin
repair.  The scalar coordinate is the genuine height-dependent coordinate

`u_z(x,y) = x + f(z) y`.

The measure-theoretic leaf first turns a cover of the scalar projection by
`delta`-intervals into an area bound inside a strip of `y`-width `s`.  The
paper-grid application then invokes the interval form of the source global
AD estimate on the actual side-`s` cube.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

/-- A planar set of `y`-diameter at most `side` has area at most twice
`side` times the measure of its sheared scalar projection. -/
theorem planar_measure_le_two_side_mul_projection
    {B : Set (ℝ × ℝ)} (hB : MeasurableSet B)
    {lower side slope : ℝ} (hside : 0 < side)
    (hy : ∀ point ∈ B,
      point.2 ∈ Set.Ico lower (lower + side)) :
    volume B ≤
      ENNReal.ofReal (2 * side) *
        volume ((fun point : ℝ × ℝ =>
          point.1 + slope * point.2) '' B) := by
  have hydiam :
      ∀ y₁ y₂ : ℝ,
        (∃ x₁ x₂ : ℝ,
          (x₁, y₁) ∈ B ∧ (x₂, y₂) ∈ B) →
        |y₁ - y₂| ≤ side := by
    rintro y₁ y₂ ⟨x₁, x₂, h₁, h₂⟩
    have hy₁ := hy (x₁, y₁) h₁
    have hy₂ := hy (x₂, y₂) h₂
    rw [abs_le]
    constructor <;> linarith [hy₁.1, hy₁.2, hy₂.1, hy₂.2]
  have hprojection :=
    image_linear_functional_length_lower_general
      (D := side) (c := slope) hside hB hydiam
  let factor : ENNReal := ENNReal.ofReal (2 * side)
  have hfactorPos : 0 < factor := by
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hfactorTop : factor ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    volume B = (volume B / factor) * factor :=
      (ENNReal.div_mul_cancel hfactorPos.ne' hfactorTop).symm
    _ ≤ volume
          ((fun point : ℝ × ℝ =>
            point.1 + slope * point.2) '' B) * factor := by
      gcongr
    _ = factor *
          volume ((fun point : ℝ × ℝ =>
            point.1 + slope * point.2) '' B) := by
      rw [mul_comm]

/-- Construction-independent covering leaf: if the scalar projection is
covered by `N` closed `delta`-intervals and the set has `y`-width `side`,
then its planar area is at most `N * 4 * side * delta`. -/
theorem planar_measure_le_of_projection_finset_cover
    {B : Set (ℝ × ℝ)} (hB : MeasurableSet B)
    {lower side slope delta : ℝ}
    (hside : 0 < side) (_hdelta : 0 < delta)
    (hy : ∀ point ∈ B,
      point.2 ∈ Set.Ico lower (lower + side))
    (centers : Finset ℝ)
    (hcover :
      (fun point : ℝ × ℝ => point.1 + slope * point.2) '' B ⊆
        ⋃ center ∈ centers, Metric.closedBall center delta) :
    volume B ≤
      (centers.card : ENNReal) *
        ENNReal.ofReal (4 * side * delta) := by
  let projection : Set ℝ :=
    (fun point : ℝ × ℝ => point.1 + slope * point.2) '' B
  have hprojection :
      volume projection ≤
        (centers.card : ENNReal) * ENNReal.ofReal (2 * delta) := by
    calc
      volume projection ≤
          volume (⋃ center ∈ centers,
            Metric.closedBall center delta) :=
        measure_mono hcover
      _ ≤ ∑ center ∈ centers,
          volume (Metric.closedBall center delta) :=
        measure_biUnion_finset_le centers _
      _ = ∑ _center ∈ centers, ENNReal.ofReal (2 * delta) := by
        apply Finset.sum_congr rfl
        intro center _
        rw [Real.volume_closedBall]
      _ = (centers.card : ENNReal) *
          ENNReal.ofReal (2 * delta) := by
        simp
  have harea :=
    planar_measure_le_two_side_mul_projection
      hB hside hy (slope := slope)
  calc
    volume B ≤
        ENNReal.ofReal (2 * side) * volume projection := harea
    _ ≤ ENNReal.ofReal (2 * side) *
        ((centers.card : ENNReal) *
          ENNReal.ofReal (2 * delta)) := by
      gcongr
    _ = (centers.card : ENNReal) *
        (ENNReal.ofReal (2 * side) *
          ENNReal.ofReal (2 * delta)) := by
      ring
    _ = (centers.card : ENNReal) *
        ENNReal.ofReal ((2 * side) * (2 * delta)) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * side)]
    _ = (centers.card : ENNReal) *
        ENNReal.ofReal (4 * side * delta) := by
      have hreal : (2 * side) * (2 * delta) =
          4 * side * delta := by ring
      rw [hreal]

private def sourceCommonBinPoint2ProdEquiv :
    Point2 ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

@[simp] private theorem sourceCommonBinPoint2ProdEquiv_apply
    (point : Point2) :
    sourceCommonBinPoint2ProdEquiv point =
      (point 0, point 1) := by
  simp [sourceCommonBinPoint2ProdEquiv, MeasurableEquiv.toLp,
    MeasurableEquiv.piFinTwo]

private theorem sourceCommonBinPoint2ProdEquiv_measurePreserving :
    MeasurePreserving sourceCommonBinPoint2ProdEquiv volume volume :=
  (PiLp.volume_preserving_ofLp (ι := Fin 2)).trans
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))

/-- A single scalar strip of half-width `delta` cuts a horizontal slice of a
side-`side` paper cube in area at most `4 * side * delta`.  Unlike the AD
bound below, this estimate uses the already fixed strip and therefore pays no
factor `(side / delta)^(1 - sigma)`. -/
theorem paperGridCube_planarSlice_volume_le_of_projection_strip
    {S : Set Point3} (hS : MeasurableSet S)
    {side delta slope height center : ℝ}
    (hside : 0 < side) (hdelta : 0 < delta)
    (cell : ℤ × ℤ × ℤ)
    (hstrip : ∀ point ∈
      wz1Lemma23PlanarSlice
        (S ∩ wz1PaperGridCube side cell) height,
      |point 0 + slope * point 1 - center| ≤ delta) :
    volume
        (wz1Lemma23PlanarSlice
          (S ∩ wz1PaperGridCube side cell) height) ≤
      ENNReal.ofReal (4 * side * delta) := by
  let localSlice : Set Point2 :=
    wz1Lemma23PlanarSlice
      (S ∩ wz1PaperGridCube side cell) height
  let B : Set (ℝ × ℝ) :=
    {point |
      point3 point.1 point.2 height ∈
        S ∩ wz1PaperGridCube side cell}
  have hB : MeasurableSet B := by
    have hlift :
        Continuous (fun point : ℝ × ℝ =>
          point3 point.1 point.2 height) := by
      unfold point3
      fun_prop
    exact (hS.inter (wz1PaperGridCube_measurable cell)).preimage
      hlift.measurable
  have hsliceImage :
      sourceCommonBinPoint2ProdEquiv '' localSlice = B := by
    ext point
    constructor
    · rintro ⟨source, hsource, rfl⟩
      change point3 (source 0) (source 1) height ∈
        S ∩ wz1PaperGridCube side cell
      exact wz1Lemma23_mem_planarSlice_iff.mp hsource
    · intro hpoint
      change point3 point.1 point.2 height ∈
        S ∩ wz1PaperGridCube side cell at hpoint
      let source : Point2 := WithLp.toLp 2 ![point.1, point.2]
      refine ⟨source, ?_, ?_⟩
      · rw [wz1Lemma23_mem_planarSlice_iff]
        simpa [source] using hpoint
      · simp [source]
  have hvolumeSlice : volume localSlice = volume B := by
    have hpre :
        sourceCommonBinPoint2ProdEquiv ⁻¹' B = localSlice := by
      rw [← hsliceImage]
      exact Set.preimage_image_eq localSlice
        sourceCommonBinPoint2ProdEquiv.injective
    have hmeasure :=
      sourceCommonBinPoint2ProdEquiv_measurePreserving.measure_preimage_emb
        sourceCommonBinPoint2ProdEquiv.measurableEmbedding B
    rwa [hpre] at hmeasure
  have hy :
      ∀ point ∈ B,
        point.2 ∈ Set.Ico ((cell.2.1 : ℝ) * side)
          ((cell.2.1 : ℝ) * side + side) := by
    intro point hpoint
    have hcube := hpoint.2
    rw [wz1PaperGridCube_eq_Ico hside cell] at hcube
    have hcube' :
      (cell.1 : ℝ) * side ≤ point.1 ∧
      point.1 < ((cell.1 : ℝ) + 1) * side ∧
      (cell.2.1 : ℝ) * side ≤ point.2 ∧
      point.2 < ((cell.2.1 : ℝ) + 1) * side ∧
      (cell.2.2 : ℝ) * side ≤ height ∧
      height < ((cell.2.2 : ℝ) + 1) * side := by
        simpa [point3, PiLp.single_apply] using hcube
    refine ⟨hcube'.2.2.1, ?_⟩
    have hupper := hcube'.2.2.2.1
    calc
      point.2 < ((cell.2.1 : ℝ) + 1) * side := hupper
      _ = (cell.2.1 : ℝ) * side + side := by ring
  have hcover :
      (fun point : ℝ × ℝ => point.1 + slope * point.2) '' B ⊆
        ⋃ value ∈ ({center} : Finset ℝ), Metric.closedBall value delta := by
    rintro value ⟨point, hpoint, rfl⟩
    have hpointSlice :
        (WithLp.toLp 2 ![point.1, point.2] : Point2) ∈ localSlice := by
      rw [wz1Lemma23_mem_planarSlice_iff]
      simpa [B] using hpoint
    have hbound := hstrip _ hpointSlice
    simp only [Finset.set_biUnion_singleton]
    simpa [Metric.mem_closedBall, Real.dist_eq] using hbound
  have harea := planar_measure_le_of_projection_finset_cover
    hB hside hdelta hy ({center} : Finset ℝ) hcover
  rw [Finset.card_singleton, Nat.cast_one, one_mul] at harea
  simpa only [localSlice, hvolumeSlice] using harea

/-- Arithmetic form of the local AD cancellation
`s * (8s/delta)^alpha * delta ≲ delta^(1-alpha) s^(1+alpha)`. -/
private theorem sourceCommonBin_localAD_power_bound
    {delta side alpha : ℝ}
    (hdelta : 0 < delta) (hside : 0 < side)
    (halphaOne : alpha ≤ 1) :
    ENNReal.ofReal (2 * side) *
        (Kakeya.realRpowENN ((8 * side) / delta) alpha *
          ENNReal.ofReal (2 * delta)) ≤
      32 * Kakeya.realRpowENN delta (1 - alpha) *
        Kakeya.realRpowENN side (1 + alpha) := by
  have hratio :
      Real.rpow ((8 * side) / delta) alpha =
        Real.rpow 8 alpha * Real.rpow side alpha /
          Real.rpow delta alpha := by
    calc
      Real.rpow ((8 * side) / delta) alpha =
          Real.rpow (8 * side) alpha /
            Real.rpow delta alpha :=
        Real.div_rpow (by positivity) hdelta.le alpha
      _ = Real.rpow 8 alpha * Real.rpow side alpha /
            Real.rpow delta alpha := by
        have hmul :
            Real.rpow (8 * side) alpha =
              Real.rpow 8 alpha * Real.rpow side alpha :=
          Real.mul_rpow (by norm_num) hside.le
        rw [hmul]
  have hdeltaPower :
      delta / Real.rpow delta alpha =
        Real.rpow delta (1 - alpha) := by
    symm
    calc
      Real.rpow delta (1 - alpha) =
          Real.rpow delta 1 / Real.rpow delta alpha :=
        Real.rpow_sub hdelta 1 alpha
      _ = delta / Real.rpow delta alpha := by
        have hone : Real.rpow delta 1 = delta := by simp
        rw [hone]
  have hsidePower :
      side * Real.rpow side alpha =
        Real.rpow side (1 + alpha) := by
    calc
      side * Real.rpow side alpha =
          Real.rpow side 1 * Real.rpow side alpha := by
        simp
      _ = Real.rpow side (1 + alpha) :=
        (Real.rpow_add hside 1 alpha).symm
  have height :
      Real.rpow 8 alpha ≤ 8 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ 8 by norm_num) halphaOne
    simpa using h
  have hreal :
      (2 * side) *
          (Real.rpow ((8 * side) / delta) alpha *
            (2 * delta)) ≤
        32 * Real.rpow delta (1 - alpha) *
          Real.rpow side (1 + alpha) := by
    rw [hratio]
    have hdeltaRpowPos : 0 < Real.rpow delta alpha :=
      Real.rpow_pos_of_pos hdelta alpha
    calc
      (2 * side) *
            ((Real.rpow 8 alpha * Real.rpow side alpha /
              Real.rpow delta alpha) * (2 * delta)) =
          4 * Real.rpow 8 alpha *
            (delta / Real.rpow delta alpha) *
            (side * Real.rpow side alpha) := by
        field_simp [hdeltaRpowPos.ne']
        ring
      _ = 4 * Real.rpow 8 alpha *
            Real.rpow delta (1 - alpha) *
            Real.rpow side (1 + alpha) := by
        rw [hdeltaPower, hsidePower]
      _ ≤ 4 * 8 *
            Real.rpow delta (1 - alpha) *
            Real.rpow side (1 + alpha) := by
        have hnonneg :
            0 ≤ 4 * Real.rpow delta (1 - alpha) *
              Real.rpow side (1 + alpha) := by
          exact mul_nonneg
            (mul_nonneg (by norm_num)
              (Real.rpow_nonneg hdelta.le _))
            (Real.rpow_nonneg hside.le _)
        nlinarith
      _ = 32 * Real.rpow delta (1 - alpha) *
            Real.rpow side (1 + alpha) := by
        ring
  simp only [Kakeya.realRpowENN]
  have hleft :
      ENNReal.ofReal (2 * side) *
          (ENNReal.ofReal
              (Real.rpow ((8 * side) / delta) alpha) *
            ENNReal.ofReal (2 * delta)) =
        ENNReal.ofReal
          ((2 * side) *
            (Real.rpow ((8 * side) / delta) alpha *
              (2 * delta))) := by
    calc
      ENNReal.ofReal (2 * side) *
            (ENNReal.ofReal
                (Real.rpow ((8 * side) / delta) alpha) *
              ENNReal.ofReal (2 * delta)) =
          (ENNReal.ofReal (2 * side) *
            ENNReal.ofReal
              (Real.rpow ((8 * side) / delta) alpha)) *
            ENNReal.ofReal (2 * delta) := by
        rw [mul_assoc]
      _ = ENNReal.ofReal
            ((2 * side) *
              Real.rpow ((8 * side) / delta) alpha) *
            ENNReal.ofReal (2 * delta) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * side)]
      _ = ENNReal.ofReal
            (((2 * side) *
              Real.rpow ((8 * side) / delta) alpha) *
                (2 * delta)) := by
        have hnonneg :
            0 ≤ (2 * side) *
              Real.rpow ((8 * side) / delta) alpha :=
          mul_nonneg (by positivity)
            (Real.rpow_nonneg (by positivity) _)
        rw [← ENNReal.ofReal_mul hnonneg]
      _ = ENNReal.ofReal
          ((2 * side) *
            (Real.rpow ((8 * side) / delta) alpha *
              (2 * delta))) := by
        congr 1
        ring
  have hright :
      32 * ENNReal.ofReal (Real.rpow delta (1 - alpha)) *
          ENNReal.ofReal (Real.rpow side (1 + alpha)) =
        ENNReal.ofReal
          (32 * Real.rpow delta (1 - alpha) *
            Real.rpow side (1 + alpha)) := by
    calc
      32 * ENNReal.ofReal (Real.rpow delta (1 - alpha)) *
            ENNReal.ofReal (Real.rpow side (1 + alpha)) =
          ENNReal.ofReal
              (32 * Real.rpow delta (1 - alpha)) *
            ENNReal.ofReal (Real.rpow side (1 + alpha)) := by
        rw [← ENNReal.ofReal_ofNat 32,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32)]
      _ = ENNReal.ofReal
          ((32 * Real.rpow delta (1 - alpha)) *
            Real.rpow side (1 + alpha)) := by
        have hnonneg :
            0 ≤ 32 * Real.rpow delta (1 - alpha) :=
          mul_nonneg (by norm_num)
            (Real.rpow_nonneg hdelta.le _)
        rw [← ENNReal.ofReal_mul hnonneg]
      _ = ENNReal.ofReal
          (32 * Real.rpow delta (1 - alpha) *
            Real.rpow side (1 + alpha)) := by
        rfl
  rw [hleft, hright]
  exact ENNReal.ofReal_mono hreal

/-- Local paper-grid form of the `a₀` estimate.  The AD coordinate is the
height-dependent `x + slope * y`; no fixed line is used. -/
theorem paperGridCube_planarSlice_volume_le_of_paperAD
    {S : Set Point3} (hS : MeasurableSet S)
    {delta sigma side slope height : ℝ} {C : ENNReal}
    (hside : 0 < side) (hdeltaSide : delta ≤ side)
    (hSlope : |slope| ≤ 3)
    (cell : ℤ × ℤ × ℤ)
    (hAD :
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection slope)
          (horizontalSlice S height))
        delta (1 - sigma) C) :
    volume
        (wz1Lemma23PlanarSlice
          (S ∩ wz1PaperGridCube side cell) height) ≤
      32 * C *
        Kakeya.realRpowENN delta sigma *
        Kakeya.realRpowENN side (2 - sigma) := by
  let localSlice : Set Point2 :=
    wz1Lemma23PlanarSlice
      (S ∩ wz1PaperGridCube side cell) height
  let B : Set (ℝ × ℝ) :=
    {point |
      point3 point.1 point.2 height ∈
        S ∩ wz1PaperGridCube side cell}
  have hB : MeasurableSet B := by
    have hlift :
        Continuous (fun point : ℝ × ℝ =>
          point3 point.1 point.2 height) := by
      unfold point3
      fun_prop
    exact (hS.inter (wz1PaperGridCube_measurable cell)).preimage
      hlift.measurable
  have hsliceImage :
      sourceCommonBinPoint2ProdEquiv '' localSlice = B := by
    ext point
    constructor
    · rintro ⟨source, hsource, rfl⟩
      change point3 (source 0) (source 1) height ∈
        S ∩ wz1PaperGridCube side cell
      exact wz1Lemma23_mem_planarSlice_iff.mp hsource
    · intro hpoint
      change point3 point.1 point.2 height ∈
        S ∩ wz1PaperGridCube side cell at hpoint
      let source : Point2 :=
        WithLp.toLp 2 ![point.1, point.2]
      refine ⟨source, ?_, ?_⟩
      · rw [wz1Lemma23_mem_planarSlice_iff]
        simpa [source] using hpoint
      · simp [source]
  have hvolumeSlice :
      volume localSlice = volume B := by
    have hpre :
        sourceCommonBinPoint2ProdEquiv ⁻¹' B = localSlice := by
      rw [← hsliceImage]
      exact Set.preimage_image_eq localSlice
        sourceCommonBinPoint2ProdEquiv.injective
    have hmeasure :=
      sourceCommonBinPoint2ProdEquiv_measurePreserving.measure_preimage_emb
        sourceCommonBinPoint2ProdEquiv.measurableEmbedding B
    rwa [hpre] at hmeasure
  let projection : Set ℝ :=
    (fun point : ℝ × ℝ =>
      point.1 + slope * point.2) '' B
  let projectionCenter : ℝ :=
    (cell.1 : ℝ) * side +
      slope * ((cell.2.1 : ℝ) * side)
  let intervalLeft : ℝ := projectionCenter - 4 * side
  have hprojectionSubset :
      projection ⊆
        scalarProjection (globalGrainDirection slope)
            (horizontalSlice S height) ∩
          Set.Icc intervalLeft (intervalLeft + 8 * side) := by
    rintro value ⟨point, hpoint, rfl⟩
    have hpointS :
        point3 point.1 point.2 height ∈ S := hpoint.1
    have hpointCube :
        point3 point.1 point.2 height ∈
          wz1PaperGridCube side cell := hpoint.2
    have hcube := hpointCube
    rw [wz1PaperGridCube_eq_Ico hside cell] at hcube
    have hcube' :
      (cell.1 : ℝ) * side ≤ point.1 ∧
      point.1 < ((cell.1 : ℝ) + 1) * side ∧
      (cell.2.1 : ℝ) * side ≤ point.2 ∧
      point.2 < ((cell.2.1 : ℝ) + 1) * side ∧
      (cell.2.2 : ℝ) * side ≤ height ∧
      height < ((cell.2.2 : ℝ) + 1) * side := by
        simpa [point3, PiLp.single_apply] using hcube
    constructor
    · refine ⟨point3 point.1 point.2 height,
          ⟨hpointS, by simp [point3]⟩, ?_⟩
      simp [globalGrainDirection, PiLp.inner_apply,
        Fin.sum_univ_succ, point3]
    · have hx :
          |point.1 - (cell.1 : ℝ) * side| ≤ side := by
        rw [abs_le]
        constructor <;> linarith [hcube'.1, hcube'.2.1]
      have hy :
          |point.2 - (cell.2.1 : ℝ) * side| ≤ side := by
        rw [abs_le]
        constructor <;>
          linarith [hcube'.2.2.1, hcube'.2.2.2.1]
      have hclose :
          |(point.1 + slope * point.2) -
              projectionCenter| ≤ 4 * side := by
        have hslopeNonneg : 0 ≤ |slope| := abs_nonneg slope
        calc
          |(point.1 + slope * point.2) -
              projectionCenter| =
              |(point.1 - (cell.1 : ℝ) * side) +
                slope *
                  (point.2 - (cell.2.1 : ℝ) * side)| := by
            congr 1
            simp [projectionCenter]
            ring
          _ ≤ |point.1 - (cell.1 : ℝ) * side| +
              |slope| *
                |point.2 - (cell.2.1 : ℝ) * side| := by
            simpa [abs_mul] using
              abs_add_le
                (point.1 - (cell.1 : ℝ) * side)
                (slope *
                  (point.2 - (cell.2.1 : ℝ) * side))
          _ ≤ side + 3 * side := by
            gcongr
          _ = 4 * side := by ring
      rw [abs_le] at hclose
      change intervalLeft ≤ point.1 + slope * point.2 ∧
        point.1 + slope * point.2 ≤ intervalLeft + 8 * side
      constructor <;> simp [intervalLeft] <;> linarith
  rcases hAD with
    ⟨hdelta, _halpha, halphaOne, _hCone, hCtop, hcover⟩
  have hdeltaLength : delta ≤ 8 * side := by
    nlinarith
  have hcoverAD :
      (↑(Metric.externalCoveringNumber
          ⟨delta, hdelta.le⟩
          (scalarProjection (globalGrainDirection slope)
              (horizontalSlice S height) ∩
            Set.Icc intervalLeft (intervalLeft + 8 * side))) :
        ENNReal) ≤
      C * Kakeya.realRpowENN ((8 * side) / delta)
        (1 - sigma) := by
    exact hcover delta hdelta.le le_rfl intervalLeft
      (8 * side) hdeltaLength
  have hcoverMono :
      Metric.externalCoveringNumber ⟨delta, hdelta.le⟩ projection ≤
        Metric.externalCoveringNumber ⟨delta, hdelta.le⟩
          (scalarProjection (globalGrainDirection slope)
              (horizontalSlice S height) ∩
            Set.Icc intervalLeft (intervalLeft + 8 * side)) :=
    Metric.externalCoveringNumber_mono_set hprojectionSubset
  have hcoverProjection :
      (↑(Metric.externalCoveringNumber
          ⟨delta, hdelta.le⟩ projection) : ENNReal) ≤
        C * Kakeya.realRpowENN ((8 * side) / delta)
          (1 - sigma) := by
    have hcoverMonoENN :
        (↑(Metric.externalCoveringNumber
          ⟨delta, hdelta.le⟩ projection) : ENNReal) ≤
        (↑(Metric.externalCoveringNumber
          ⟨delta, hdelta.le⟩
            (scalarProjection (globalGrainDirection slope)
                (horizontalSlice S height) ∩
              Set.Icc intervalLeft
                (intervalLeft + 8 * side))) : ENNReal) := by
      exact_mod_cast hcoverMono
    exact hcoverMonoENN.trans hcoverAD
  have hprojectionVolume :
      volume projection ≤
        (C * Kakeya.realRpowENN ((8 * side) / delta)
          (1 - sigma)) * ENNReal.ofReal (2 * delta) := by
    exact volume_le_externalCoveringNumber_mul_two_delta
      hdelta
      (ENNReal.mul_ne_top hCtop
        (by simp [Kakeya.realRpowENN]))
      hcoverProjection
  have hy :
      ∀ point ∈ B,
        point.2 ∈
          Set.Ico ((cell.2.1 : ℝ) * side)
            ((cell.2.1 : ℝ) * side + side) := by
    intro point hpoint
    have hcube := hpoint.2
    rw [wz1PaperGridCube_eq_Ico hside cell] at hcube
    have hcube' :
      (cell.1 : ℝ) * side ≤ point.1 ∧
      point.1 < ((cell.1 : ℝ) + 1) * side ∧
      (cell.2.1 : ℝ) * side ≤ point.2 ∧
      point.2 < ((cell.2.1 : ℝ) + 1) * side ∧
      (cell.2.2 : ℝ) * side ≤ height ∧
      height < ((cell.2.2 : ℝ) + 1) * side := by
        simpa [point3, PiLp.single_apply] using hcube
    refine ⟨hcube'.2.2.1, ?_⟩
    have hupper := hcube'.2.2.2.1
    have heq :
        ((cell.2.1 : ℝ) + 1) * side =
          (cell.2.1 : ℝ) * side + side := by
      ring
    rwa [heq] at hupper
  have harea :=
    planar_measure_le_two_side_mul_projection
      hB hside hy (slope := slope)
  have hpower :=
    sourceCommonBin_localAD_power_bound
      hdelta hside halphaOne
  calc
    volume
        (wz1Lemma23PlanarSlice
          (S ∩ wz1PaperGridCube side cell) height) =
        volume B := hvolumeSlice
    _ ≤ ENNReal.ofReal (2 * side) * volume projection := harea
    _ ≤ ENNReal.ofReal (2 * side) *
        ((C * Kakeya.realRpowENN ((8 * side) / delta)
          (1 - sigma)) * ENNReal.ofReal (2 * delta)) := by
      gcongr
    _ = C *
        (ENNReal.ofReal (2 * side) *
          (Kakeya.realRpowENN ((8 * side) / delta)
            (1 - sigma) * ENNReal.ofReal (2 * delta))) := by
      ring
    _ ≤ C *
        (32 * Kakeya.realRpowENN delta (1 - (1 - sigma)) *
          Kakeya.realRpowENN side (1 + (1 - sigma))) := by
      gcongr
    _ = 32 * C *
        Kakeya.realRpowENN delta sigma *
        Kakeya.realRpowENN side (2 - sigma) := by
      rw [show 1 - (1 - sigma) = sigma by ring,
        show 1 + (1 - sigma) = 2 - sigma by ring]
      ring

/-- Source-shading `a₀` for one side-`sqrt rho` paper-grid cube.  The
projection direction is exactly
`globalGrainDirection (source.globalGrains.slope height)`, hence depends on
the queried height. -/
theorem PureWZ2QuantitativeGrainConfiguration.sourceCommonBinSpatialCellSliceBound
    {sigma inputLoss delta rho : ℝ}
    (source :
      PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (hrho : 0 < rho)
    (hdeltaRoot : delta ≤ Real.sqrt rho)
    (cell : ℤ × ℤ × ℤ)
    (height : ℝ) (hheight : height ∈ Set.Icc (-1 : ℝ) 1) :
    volume
        (wz1Lemma23PlanarSlice
          (source.shading.union ∩
            wz1PaperGridCube (Real.sqrt rho) cell)
          height) ≤
      32 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN delta sigma *
        Kakeya.realRpowENN rho (1 - sigma / 2) := by
  have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hAD :
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (source.globalGrains.slope height))
          (horizontalSlice source.shading.union height))
        delta (1 - sigma)
        (Kakeya.realRpowENN delta (-inputLoss)) :=
    source.globalGrains.global_ad height hheight
  have hraw :=
    paperGridCube_planarSlice_volume_le_of_paperAD
      (S := source.shading.union)
      (measurableSet_shading_union source.shading)
      hroot hdeltaRoot
      (source.globalGrains.slope_bound height hheight)
      cell hAD
  have hrootPower :
      Kakeya.realRpowENN (Real.sqrt rho) (2 - sigma) =
        Kakeya.realRpowENN rho (1 - sigma / 2) := by
    simp only [Kakeya.realRpowENN, Real.sqrt_eq_rpow]
    congr 1
    calc
      (Real.rpow rho (1 / 2 : ℝ)).rpow (2 - sigma) =
          Real.rpow rho ((1 / 2 : ℝ) * (2 - sigma)) :=
        (Real.rpow_mul hrho.le _ _).symm
      _ = Real.rpow rho (1 - sigma / 2) := by
        congr 1
        ring
  rwa [hrootPower] at hraw

end Kakeya.Assouad

end
