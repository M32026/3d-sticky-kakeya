import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoverCarrierContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics

/-!
# Geometric helpers for common paper unit rescaling

This module isolates three source-independent facts used by both the strict
and doubled-anchor carrier-transfer arguments:

* the paper-oriented parametrization of a tube axis;
* the orthogonal closest point on an affine line;
* a uniform bound on the source-axis parameter from the image height.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

theorem wz2PaperTubeAxisLine_eq_range
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    tubeAxisLine tube =
      Set.range (fun parameter : ℝ =>
        wz1TubeAxisZeroPoint tube +
          parameter • wz1PaperDirection tube) := by
  ext point
  simp only [tubeAxisLine, Set.mem_range]
  constructor
  · rintro ⟨parameter, rfl⟩
    rcases wz1TubeAxisZeroPoint_mem_axis tube with
      ⟨zeroParameter, hzeroParameter⟩
    dsimp only [wz1PaperDirection]
    split_ifs with hsign
    · refine ⟨parameter - zeroParameter, ?_⟩
      rw [hzeroParameter]
      module
    · refine ⟨zeroParameter - parameter, ?_⟩
      rw [hzeroParameter]
      module
  · rintro ⟨parameter, rfl⟩
    exact
      wz1TubeAxisZeroPoint_add_smul_paperDirection_mem_axis
        tube parameter

theorem wz2PaperAffineLine_closest_point
    {base direction point : Point3}
    (hdirection : direction ≠ 0) :
    ∃ (closest : Point3) (parameter : ℝ),
      closest = base + parameter • direction ∧
      inner ℝ (point - closest) direction = 0 ∧
      ∀ candidate : ℝ,
        ‖point - closest‖ ≤
          ‖point - (base + candidate • direction)‖ := by
  let parameter : ℝ :=
    inner ℝ (point - base) direction / ‖direction‖ ^ 2
  let closest : Point3 := base + parameter • direction
  have hnormPos : 0 < ‖direction‖ ^ 2 := by
    have hdirectionNorm : 0 < ‖direction‖ :=
      norm_pos_iff.mpr hdirection
    positivity
  have hnormNe : ‖direction‖ ^ 2 ≠ 0 := hnormPos.ne'
  have hinner :
      inner ℝ (point - closest) direction = 0 := by
    have hdifference :
        point - closest =
          (point - base) - parameter • direction := by
      dsimp only [closest]
      module
    rw [hdifference, inner_sub_left, inner_smul_left]
    simp only [RCLike.star_def, RCLike.conj_to_real]
    have hself :
        inner ℝ direction direction = ‖direction‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [hself]
    dsimp only [parameter]
    field_simp [hnormNe]
    ring
  refine ⟨closest, parameter, rfl, hinner, ?_⟩
  intro candidate
  have hdifference :
      point - (base + candidate • direction) =
        (point - closest) +
          (parameter - candidate) • direction := by
    dsimp only [closest]
    module
  have horthogonal :
      inner ℝ (point - closest)
          ((parameter - candidate) • direction) = 0 := by
    rw [inner_smul_right, hinner]
    ring
  have hnormSquare :
      ‖point - (base + candidate • direction)‖ ^ 2 =
        ‖point - closest‖ ^ 2 +
          ‖(parameter - candidate) • direction‖ ^ 2 := by
    rw [hdifference]
    have hidentity :=
      norm_add_sq (𝕜 := ℝ)
        (point - closest)
        ((parameter - candidate) • direction)
    have hre :
        RCLike.re
            (inner ℝ (point - closest)
              ((parameter - candidate) • direction)) =
          inner ℝ (point - closest)
            ((parameter - candidate) • direction) := by
      simp
    rw [hre, horthogonal] at hidentity
    linarith
  have hsquare :
      ‖point - closest‖ ^ 2 ≤
        ‖point - (base + candidate • direction)‖ ^ 2 := by
    rw [hnormSquare]
    exact le_add_of_nonneg_right (sq_nonneg _)
  nlinarith [
    norm_nonneg (point - closest),
    norm_nonneg (point - (base + candidate • direction))]

theorem wz2PaperUnitRescalingMap_image_range
    {rho : ℝ}
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (zero direction : Point3) :
    wz1PaperUnitRescalingMap anchor hrho ''
        Set.range (fun parameter : ℝ =>
          zero + parameter • direction) =
      Set.range (fun parameter : ℝ =>
        wz1PaperUnitRescalingMap anchor hrho zero +
          parameter •
            wz1PaperUnitRescalingLinear anchor direction) := by
  ext point
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨sourcePoint, ⟨parameter, rfl⟩, rfl⟩
    refine ⟨parameter, ?_⟩
    rw [wz1PaperUnitRescalingMap_add,
      map_smul]
  · rintro ⟨parameter, rfl⟩
    refine
      ⟨zero + parameter • direction,
        ⟨parameter, rfl⟩, ?_⟩
    rw [wz1PaperUnitRescalingMap_add,
      map_smul]

theorem wz2PaperAffineLine_closest_dist_le_of_mem_cthickening
    {base direction point closest : Point3}
    {closestParameter radius : ℝ}
    (hclosest :
      closest = base + closestParameter • direction)
    (hminimal :
      ∀ candidate : ℝ,
        ‖point - closest‖ ≤
          ‖point - (base + candidate • direction)‖)
    (hradius : 0 ≤ radius)
    (hpoint :
      point ∈
        Metric.cthickening radius
          (Set.range fun parameter : ℝ =>
            base + parameter • direction)) :
    dist point closest ≤ radius := by
  let axis : Set Point3 :=
    Set.range fun parameter : ℝ =>
      base + parameter • direction
  have haxisNonempty : axis.Nonempty :=
    ⟨base, ⟨0, by simp [axis]⟩⟩
  have hclosestMem : closest ∈ axis := by
    exact ⟨closestParameter, hclosest.symm⟩
  have hinfUpper :
      Metric.infDist point axis ≤ dist point closest :=
    Metric.infDist_le_dist_of_mem hclosestMem
  have hinfLower :
      dist point closest ≤ Metric.infDist point axis := by
    rw [Metric.infDist_eq_iInf]
    apply le_ciInf
    intro candidate
    rcases candidate.property with ⟨parameter, hparameter⟩
    rw [← hparameter]
    simpa [dist_eq_norm] using hminimal parameter
  have hinfEq :
      dist point closest = Metric.infDist point axis := by
    linarith
  have hmembership :
      Metric.infEDist point axis ≤ ENNReal.ofReal radius := by
    simpa only [axis, Metric.mem_cthickening_iff] using hpoint
  have hinfNotTop :
      Metric.infEDist point axis ≠ ⊤ :=
    Metric.infEDist_ne_top haxisNonempty
  have htoReal :
      Metric.infDist point axis ≤ radius := by
    have hcomparison :
        (Metric.infEDist point axis).toReal ≤
          (ENNReal.ofReal radius).toReal :=
      (ENNReal.toReal_le_toReal
        hinfNotTop ENNReal.ofReal_ne_top).mpr hmembership
    rw [ENNReal.toReal_ofReal hradius] at hcomparison
    exact hcomparison
  rw [hinfEq]
  exact htoReal

theorem wz2PaperParameter_bound_from_image_height
    {delta sigma : ℝ}
    (hdelta : 0 < delta)
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1)
    (hmargin : 100 * delta ≤ sigma)
    {fineZero anchorZero fineDirection anchorDirection : Point3}
    (hfineDirectionUnit : ‖fineDirection‖ = 1)
    (hanchorDirectionUnit : ‖anchorDirection‖ = 1)
    (hzeroDistance : dist fineZero anchorZero ≤ sigma / 2)
    (hdirectionAngle :
      InnerProductGeometry.angle
          fineDirection anchorDirection ≤
        sigma / 2)
    {parameter height : ℝ}
    (hheight :
      height =
        inner ℝ
          (fineZero + parameter • fineDirection - anchorZero)
          anchorDirection)
    (hheightBound :
      |height| ≤ 1 + 6 * delta / sigma) :
    |parameter| ≤ 2 := by
  have hchord :
      ‖fineDirection - anchorDirection‖ ≤ sigma / 2 :=
    (unit_norm_sub_le_angle
      hfineDirectionUnit hanchorDirectionUnit).trans
      hdirectionAngle
  have hinnerLower :
      7 / 8 ≤ inner ℝ fineDirection anchorDirection := by
    have hidentity :
        inner ℝ fineDirection anchorDirection =
          (‖fineDirection‖ ^ 2 +
              ‖anchorDirection‖ ^ 2 -
                ‖fineDirection - anchorDirection‖ ^ 2) / 2 := by
      have hnormSub :=
        norm_sub_sq_real fineDirection anchorDirection
      linarith
    rw [hidentity, hfineDirectionUnit, hanchorDirectionUnit]
    have hchordSquare :
        ‖fineDirection - anchorDirection‖ ^ 2 ≤
          (sigma / 2) ^ 2 := by
      nlinarith [
        norm_nonneg (fineDirection - anchorDirection),
        show 0 ≤ sigma / 2 by linarith]
    nlinarith
  have hinnerPos :
      0 < inner ℝ fineDirection anchorDirection := by
    linarith
  have hbaseInner :
      |inner ℝ (fineZero - anchorZero) anchorDirection| ≤
        sigma / 2 := by
    calc
      |inner ℝ (fineZero - anchorZero) anchorDirection|
          ≤ ‖fineZero - anchorZero‖ *
              ‖anchorDirection‖ :=
        abs_real_inner_le_norm _ _
      _ = dist fineZero anchorZero := by
        rw [hanchorDirectionUnit, mul_one, dist_eq_norm]
      _ ≤ sigma / 2 := hzeroDistance
  let baseInner :=
    inner ℝ (fineZero - anchorZero) anchorDirection
  let directionInner :=
    inner ℝ fineDirection anchorDirection
  have hdirectionInnerPos : 0 < directionInner := hinnerPos
  have hexpand :
      height = baseInner + parameter * directionInner := by
    rw [hheight]
    dsimp only [baseInner, directionInner]
    have hvector :
        fineZero + parameter • fineDirection - anchorZero =
          (fineZero - anchorZero) +
            parameter • fineDirection := by
      module
    rw [hvector, inner_add_left, inner_smul_left]
    rfl
  have hparameterFormula :
      parameter = (height - baseInner) / directionInner := by
    have hdifference :
        height - baseInner =
          parameter * directionInner := by
      rw [hexpand]
      ring
    rw [hdifference]
    field_simp [hdirectionInnerPos.ne']
  have hnumerator :
      |height - baseInner| ≤
        (1 + 6 * delta / sigma) + sigma / 2 := by
    calc
      |height - baseInner| ≤ |height| + |baseInner| :=
        abs_sub height baseInner
      _ ≤ (1 + 6 * delta / sigma) + sigma / 2 := by
        dsimp only [baseInner]
        gcongr
  have hparameterBound :
      |parameter| ≤
        ((1 + 6 * delta / sigma) + sigma / 2) /
          directionInner := by
    rw [hparameterFormula, abs_div,
      abs_of_pos hdirectionInnerPos]
    exact
      div_le_div_of_nonneg_right hnumerator
        hdirectionInnerPos.le
  have hdeltaRatio : delta / sigma ≤ 1 / 100 := by
    have hdeltaLe : delta ≤ sigma / 100 := by
      linarith
    calc
      delta / sigma ≤ (sigma / 100) / sigma := by
        gcongr
      _ = 1 / 100 := by
        field_simp [hsigma.ne']
  have hsixRatio : 6 * delta / sigma ≤ 6 / 100 := by
    calc
      6 * delta / sigma = 6 * (delta / sigma) := by ring
      _ ≤ 6 * (1 / 100 : ℝ) := by gcongr
      _ = 6 / 100 := by norm_num
  have hnumeratorUniform :
      (1 + 6 * delta / sigma) + sigma / 2 ≤
        1 + 6 / 100 + 1 / 2 := by
    linarith
  have hfinal :
      ((1 + 6 * delta / sigma) + sigma / 2) /
          directionInner ≤
        2 := by
    calc
      ((1 + 6 * delta / sigma) + sigma / 2) /
            directionInner
          ≤ (1 + 6 / 100 + 1 / 2 : ℝ) /
              directionInner := by
        exact
          div_le_div_of_nonneg_right hnumeratorUniform
            hdirectionInnerPos.le
      _ ≤ (1 + 6 / 100 + 1 / 2 : ℝ) / (7 / 8 : ℝ) := by
        gcongr
      _ ≤ 2 := by norm_num
  exact hparameterBound.trans hfinal

/--
Generalized parameter bound: given an arbitrary height bound, bound the
source-axis parameter. Used by the literal-map carrier proof where the
image height is compressed by `1 / 100`.
-/
theorem wz2PaperParameter_bound_from_arbitrary_height
    {sigma : ℝ}
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1)
    {fineZero anchorZero fineDirection anchorDirection : Point3}
    (hfineDirectionUnit : ‖fineDirection‖ = 1)
    (hanchorDirectionUnit : ‖anchorDirection‖ = 1)
    (hzeroDistance : dist fineZero anchorZero ≤ sigma / 2)
    (hdirectionAngle :
      InnerProductGeometry.angle
          fineDirection anchorDirection ≤
        sigma / 2)
    {parameter height : ℝ}
    (hheight :
      height =
        inner ℝ
          (fineZero + parameter • fineDirection - anchorZero)
          anchorDirection)
    {heightBound : ℝ}
    (hheightBoundNonneg : 0 ≤ heightBound)
    (hheightBound : |height| ≤ heightBound) :
    |parameter| ≤ (heightBound + sigma / 2) / (7 / 8 : ℝ) := by
  have hchord :
      ‖fineDirection - anchorDirection‖ ≤ sigma / 2 :=
    (unit_norm_sub_le_angle
      hfineDirectionUnit hanchorDirectionUnit).trans
      hdirectionAngle
  have hinnerLower :
      7 / 8 ≤ inner ℝ fineDirection anchorDirection := by
    have hidentity :
        inner ℝ fineDirection anchorDirection =
          (‖fineDirection‖ ^ 2 +
              ‖anchorDirection‖ ^ 2 -
                ‖fineDirection - anchorDirection‖ ^ 2) / 2 := by
      have hnormSub :=
        norm_sub_sq_real fineDirection anchorDirection
      linarith
    rw [hidentity, hfineDirectionUnit, hanchorDirectionUnit]
    have hchordSquare :
        ‖fineDirection - anchorDirection‖ ^ 2 ≤
          (sigma / 2) ^ 2 := by
      nlinarith [
        norm_nonneg (fineDirection - anchorDirection),
        show 0 ≤ sigma / 2 by linarith]
    nlinarith
  have hinnerPos :
      0 < inner ℝ fineDirection anchorDirection := by
    linarith
  have hbaseInner :
      |inner ℝ (fineZero - anchorZero) anchorDirection| ≤
        sigma / 2 := by
    calc
      |inner ℝ (fineZero - anchorZero) anchorDirection|
          ≤ ‖fineZero - anchorZero‖ *
              ‖anchorDirection‖ :=
        abs_real_inner_le_norm _ _
      _ = dist fineZero anchorZero := by
        rw [hanchorDirectionUnit, mul_one, dist_eq_norm]
      _ ≤ sigma / 2 := hzeroDistance
  let baseInner :=
    inner ℝ (fineZero - anchorZero) anchorDirection
  let directionInner :=
    inner ℝ fineDirection anchorDirection
  have hdirectionInnerPos : 0 < directionInner := hinnerPos
  have hexpand :
      height = baseInner + parameter * directionInner := by
    rw [hheight]
    dsimp only [baseInner, directionInner]
    have hvector :
        fineZero + parameter • fineDirection - anchorZero =
          (fineZero - anchorZero) +
            parameter • fineDirection := by
      module
    rw [hvector, inner_add_left, inner_smul_left]
    rfl
  have hparameterFormula :
      parameter = (height - baseInner) / directionInner := by
    have hdifference :
        height - baseInner =
          parameter * directionInner := by
      rw [hexpand]
      ring
    rw [hdifference]
    field_simp [hdirectionInnerPos.ne']
  have hnumerator :
      |height - baseInner| ≤ heightBound + sigma / 2 := by
    calc
      |height - baseInner| ≤ |height| + |baseInner| :=
        abs_sub height baseInner
      _ ≤ heightBound + sigma / 2 := by
        dsimp only [baseInner]
        gcongr
  have hparameterBound :
      |parameter| ≤
        (heightBound + sigma / 2) / directionInner := by
    rw [hparameterFormula, abs_div,
      abs_of_pos hdirectionInnerPos]
    exact
      div_le_div_of_nonneg_right hnumerator
        hdirectionInnerPos.le
  have hfinal :
      (heightBound + sigma / 2) / directionInner ≤
        (heightBound + sigma / 2) / (7 / 8 : ℝ) := by
    gcongr
    <;> linarith
  exact hparameterBound.trans hfinal

/--
Concrete bound for the literal-map height scaling.

The literal image z-coordinate is `1 / 100` of the unscaled inner product,
so the unscaled height bound is `100 * (1 + 6 * delta / sigma)`.
-/
theorem wz2PaperParameter_bound_from_literal_height
    {delta sigma : ℝ}
    (hdelta : 0 < delta)
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1)
    (hmargin : 100 * delta ≤ sigma)
    {fineZero anchorZero fineDirection anchorDirection : Point3}
    (hfineDirectionUnit : ‖fineDirection‖ = 1)
    (hanchorDirectionUnit : ‖anchorDirection‖ = 1)
    (hzeroDistance : dist fineZero anchorZero ≤ sigma / 2)
    (hdirectionAngle :
      InnerProductGeometry.angle
          fineDirection anchorDirection ≤
        sigma / 2)
    {parameter height : ℝ}
    (hheight :
      height =
        inner ℝ
          (fineZero + parameter • fineDirection - anchorZero)
          anchorDirection)
    (hheightBound :
      |height| ≤ 100 * (1 + 6 * delta / sigma)) :
    |parameter| ≤ 852 / 7 := by
  have hdeltaRatio : delta / sigma ≤ 1 / 100 := by
    have hdeltaLe : delta ≤ sigma / 100 := by linarith
    calc
      delta / sigma ≤ (sigma / 100) / sigma := by gcongr
      _ = 1 / 100 := by field_simp [hsigma.ne']
  have hbound :
      100 * (1 + 6 * delta / sigma) + sigma / 2 ≤
        100 * (1 + 6 / 100) + 1 / 2 := by
    have hsix : 6 * delta / sigma ≤ 6 / 100 := by
      calc
        6 * delta / sigma = 6 * (delta / sigma) := by ring
        _ ≤ 6 * (1 / 100 : ℝ) := by gcongr
        _ = 6 / 100 := by norm_num
    linarith
  have hmain :=
    wz2PaperParameter_bound_from_arbitrary_height
      hsigma hsigmaOne
      hfineDirectionUnit hanchorDirectionUnit
      hzeroDistance hdirectionAngle
      hheight
      (by positivity) hheightBound
  have hfinal :
      (100 * (1 + 6 * delta / sigma) + sigma / 2) /
          (7 / 8 : ℝ) ≤
        852 / 7 := by
    calc
      (100 * (1 + 6 * delta / sigma) + sigma / 2) /
            (7 / 8 : ℝ)
          ≤ (100 * (1 + 6 / 100) + 1 / 2) /
              (7 / 8 : ℝ) := by
        gcongr
      _ = 852 / 7 := by norm_num
  exact hmain.trans hfinal

end Kakeya.Assouad

end
