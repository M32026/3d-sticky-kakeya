import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeReversal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.DilatedClosestPoint
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.LargeScaleConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ShiftedCopyCellPack

/-!
# Complete-fiber parent overlap

At one sufficiently small GWZ scale, an essentially-distinct coarse family
has uniformly bounded complete fixed-dilation incidence multiplicity: one
fine source tube belongs to only finitely many complete containment fibers,
with a bound depending on the fixed dilation and the scale but not on the
source-family cardinality.

This is a direct statement about `PureWZ2GWZScaleData.fullFiberIndices`.
No assigned parent map appears.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas
open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem pureWZ2_perp_norm_le
    (direction vector : Point3)
    (hdirection : ‖direction‖ = 1) :
    ‖vector - inner ℝ vector direction • direction‖ ≤ ‖vector‖ := by
  let coefficient := inner ℝ vector direction
  have hnorm :
      ‖vector - coefficient • direction‖ ^ 2 =
        ‖vector‖ ^ 2 - coefficient ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right,
      norm_smul, hdirection]
    simp [coefficient, Real.norm_eq_abs, sq_abs]
    ring
  have hsquared :
      ‖vector - coefficient • direction‖ ^ 2 ≤
        ‖vector‖ ^ 2 := by
    rw [hnorm]
    exact sub_le_self _ (sq_nonneg coefficient)
  nlinarith [
    norm_nonneg vector,
    norm_nonneg (vector - coefficient • direction)]

theorem pureWZ2_projective_parent_direction
    {delta rho A : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hA : 1 ≤ A)
    (hsmall : rho ≤ 1 / (200 * A))
    (hscale : delta ≤ A * rho)
    (source : Kakeya.DeltaTube delta)
    (parent : Kakeya.DeltaTube rho)
    (hcontainment :
      source.carrier ⊆
        wz2PaperCenteredDilatedCarrier A parent) :
    ‖parent.direction -
        inner ℝ parent.direction source.direction •
          source.direction‖ ≤
      2 * A * rho ∧
    |inner ℝ parent.direction source.direction| ≥ 1 / 2 := by
  have htransverseSource :
      ‖source.direction -
          inner ℝ source.direction parent.direction •
            parent.direction‖ ≤
        2 * (A * rho - delta) :=
    gwz_direction_constraint
      hdelta hrho hA hscale source parent hcontainment
  let coefficient :=
    inner ℝ parent.direction source.direction
  have hcoefficient :
      inner ℝ source.direction parent.direction = coefficient :=
    real_inner_comm parent.direction source.direction
  have hsourceSq :
      ‖source.direction -
          coefficient • parent.direction‖ ^ 2 =
        1 - coefficient ^ 2 := by
    rw [norm_sub_sq_real, source.direction_unit,
      norm_smul, parent.direction_unit,
      inner_smul_right, hcoefficient]
    simp [Real.norm_eq_abs, sq_abs]
    ring
  have hparentSq :
      ‖parent.direction -
          coefficient • source.direction‖ ^ 2 =
        1 - coefficient ^ 2 := by
    rw [norm_sub_sq_real, parent.direction_unit,
      norm_smul, source.direction_unit,
      inner_smul_right]
    simp [coefficient, Real.norm_eq_abs, sq_abs]
    ring
  have hnormEquality :
      ‖parent.direction -
          coefficient • source.direction‖ =
        ‖source.direction -
          coefficient • parent.direction‖ := by
    nlinarith [
      norm_nonneg
        (parent.direction -
          coefficient • source.direction),
      norm_nonneg
        (source.direction -
          coefficient • parent.direction)]
  have hparentTransverse :
      ‖parent.direction -
          coefficient • source.direction‖ ≤
        2 * A * rho := by
    rw [hnormEquality, ← hcoefficient]
    exact htransverseSource.trans (by linarith)
  have hcoefficientSq :
      coefficient ^ 2 ≥
        1 - (2 * A * rho) ^ 2 := by
    have hscaleNonnegative : 0 ≤ 2 * A * rho := by positivity
    have hnormSquared :
        ‖parent.direction -
            coefficient • source.direction‖ ^ 2 ≤
          (2 * A * rho) ^ 2 := by
      exact
        (sq_le_sq₀ (norm_nonneg _) hscaleNonnegative).mpr
          hparentTransverse
    linarith [hparentSq]
  have hArho :
      A * rho ≤ 1 / 200 := by
    have hApos : 0 < A := by linarith
    calc
      A * rho ≤ A * (1 / (200 * A)) := by gcongr
      _ = 1 / 200 := by
        field_simp [hApos.ne']
  have habs : |coefficient| ≥ 1 / 2 := by
    have hsq : coefficient ^ 2 ≥ (1 / 2 : ℝ) ^ 2 := by
      nlinarith
    nlinarith [sq_abs coefficient, abs_nonneg coefficient]
  exact ⟨hparentTransverse, habs⟩

def pureWZ2OrientedParent
    {rho : ℝ}
    (sourceDirection : Point3)
    (parent : Kakeya.DeltaTube rho) :
    Kakeya.DeltaTube rho :=
  if 0 ≤ inner ℝ parent.direction sourceDirection then
    parent
  else
    reverseTube parent

@[simp] theorem pureWZ2OrientedParent_carrier
    {rho : ℝ}
    (sourceDirection : Point3)
    (parent : Kakeya.DeltaTube rho) :
    (pureWZ2OrientedParent sourceDirection parent).carrier =
      parent.carrier := by
  unfold pureWZ2OrientedParent
  split_ifs <;> simp

@[simp] theorem pureWZ2OrientedParent_midpoint
    {rho : ℝ}
    (sourceDirection : Point3)
    (parent : Kakeya.DeltaTube rho) :
    wz2PaperTubeMidpoint
        (pureWZ2OrientedParent sourceDirection parent) =
      wz2PaperTubeMidpoint parent := by
  unfold pureWZ2OrientedParent
  split_ifs
  · rfl
  · simp only [reverseTube, wz2PaperTubeMidpoint]
    module

theorem pureWZ2OrientedParent_inner_nonnegative
    {rho : ℝ}
    (sourceDirection : Point3)
    (parent : Kakeya.DeltaTube rho) :
    0 ≤ inner ℝ
      (pureWZ2OrientedParent sourceDirection parent).direction
      sourceDirection := by
  unfold pureWZ2OrientedParent
  split_ifs with h
  · exact h
  · simp only [reverseTube, inner_neg_left]
    linarith

theorem pureWZ2OrientedParent_inner_eq_abs
    {rho : ℝ}
    (sourceDirection : Point3)
    (parent : Kakeya.DeltaTube rho) :
    inner ℝ
        (pureWZ2OrientedParent
          sourceDirection parent).direction
        sourceDirection =
      |inner ℝ parent.direction sourceDirection| := by
  unfold pureWZ2OrientedParent
  split_ifs with h
  · rw [abs_of_nonneg h]
  · have hnegative :
        inner ℝ parent.direction sourceDirection < 0 :=
      lt_of_not_ge h
    simp only [reverseTube, inner_neg_left]
    rw [abs_of_neg hnegative]

theorem pureWZ2OrientedParent_transverse
    {rho : ℝ}
    (sourceDirection : Point3)
    (parent : Kakeya.DeltaTube rho) :
    ‖(pureWZ2OrientedParent sourceDirection parent).direction -
        inner ℝ
            (pureWZ2OrientedParent
              sourceDirection parent).direction
            sourceDirection • sourceDirection‖ =
      ‖parent.direction -
        inner ℝ parent.direction sourceDirection •
          sourceDirection‖ := by
  unfold pureWZ2OrientedParent
  split_ifs
  · rfl
  · simp only [reverseTube, inner_neg_left]
    have hvector :
        -parent.direction -
            (-inner ℝ parent.direction sourceDirection) •
              sourceDirection =
          -(parent.direction -
            inner ℝ parent.direction sourceDirection •
              sourceDirection) := by
      module
    rw [hvector, norm_neg]

theorem pureWZ2OrientedParent_distinct
    {rho : ℝ}
    {sourceDirection : Point3}
    {first second : Kakeya.DeltaTube rho}
    (hdistinct : first.EssentiallyDistinct second) :
    (pureWZ2OrientedParent sourceDirection first).EssentiallyDistinct
      (pureWZ2OrientedParent sourceDirection second) := by
  unfold pureWZ2OrientedParent
  split_ifs
  · exact hdistinct
  · exact reverseTube_essentiallyDistinct_right first second hdistinct
  · exact reverseTube_essentiallyDistinct_left first second hdistinct
  · exact
      reverseTube_essentiallyDistinct_right
        (reverseTube first) second
        (reverseTube_essentiallyDistinct_left first second hdistinct)

/-- A scale-independent bound for complete fixed-dilation parent incidence. -/
def pureWZ2CompleteFiberOverlapBound (A : ℝ) : ℕ :=
  (2 * Nat.ceil (200 * A * (A + 1)) + 1) ^ 2 *
    (2 * Nat.ceil
      ((400 * max (2 * A) 16) * (3 * A / 2)) + 1) *
    (2 * Nat.ceil (400 * A) + 1) ^ 2

/--
At one small exact GWZ scale, every source tube lies in only a bounded number
of complete fixed-dilation containment fibers.
-/
theorem pureWZ2_complete_fiber_parent_overlap
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    (scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant)
    (hscaleSmall : scale.1 ≤ 1 / (200 * A)) :
    ∀ index : Fin source.card,
      (Finset.univ.filter fun parent :
        Fin scaleData.coarse.card =>
          index ∈ scaleData.fullFiberIndices parent).card ≤
        pureWZ2CompleteFiberOverlapBound A := by
  let rho := scale.1
  have hrho : 0 < rho := by
    have := scale.property.1
    linarith
  intro index
  let sourceTube := source.tube index
  let parents : Finset (Fin scaleData.coarse.card) :=
    Finset.univ.filter fun parent =>
      index ∈ scaleData.fullFiberIndices parent
  let oriented : Fin scaleData.coarse.card →
      Kakeya.DeltaTube rho := fun parent =>
    pureWZ2OrientedParent sourceTube.direction
      (scaleData.coarse.tube parent)
  let sourceMidpoint :=
    wz2PaperTubeMidpoint sourceTube
  have hcontains :
      ∀ parent ∈ parents,
        sourceTube.carrier ⊆
          wz2PaperCenteredDilatedCarrier A
            (scaleData.coarse.tube parent) := by
    intro parent hparent
    have hmember :=
      (Finset.mem_filter.mp hparent).2
    rw [scaleData.fullFiberIndices_eq] at hmember
    exact (Finset.mem_filter.mp hmember).2
  have htransverseMidpoint :
      ∀ parent ∈ parents,
        ‖(wz2PaperTubeMidpoint (oriented parent) -
              sourceMidpoint) -
            inner ℝ
                (wz2PaperTubeMidpoint (oriented parent) -
                  sourceMidpoint)
                sourceTube.direction •
              sourceTube.direction‖ ≤
          A * (A + 1) * rho := by
    intro parent hparent
    let parentTube := scaleData.coarse.tube parent
    have hsourceMidpoint :
        sourceMidpoint ∈
          wz2PaperCenteredDilatedCarrier A parentTube := by
      exact hcontains parent hparent
        (wz2_paper_tubeMidpoint_mem_carrier
          sourceTube hdelta.le)
    rcases
        pureWZ2_general_dilation_closest_point
          hrho.le (by linarith) parentTube
          sourceMidpoint hsourceMidpoint with
      ⟨parameter, hparameter, hdistance⟩
    let axisPoint :=
      parentTube.base + parameter • parentTube.direction
    have hmidpointDecomposition :
        wz2PaperTubeMidpoint parentTube - sourceMidpoint =
          (axisPoint - sourceMidpoint) +
            (1 / 2 - parameter) •
              parentTube.direction := by
      dsimp only [axisPoint, wz2PaperTubeMidpoint]
      module
    have haxisTransverse :
        ‖(axisPoint - sourceMidpoint) -
            inner ℝ (axisPoint - sourceMidpoint)
              sourceTube.direction •
              sourceTube.direction‖ ≤
          A * rho := by
      exact
        (pureWZ2_perp_norm_le
          sourceTube.direction
          (axisPoint - sourceMidpoint)
          sourceTube.direction_unit).trans
          (by
            simpa [dist_eq_norm, norm_sub_rev] using hdistance)
    have hdirection :=
      (pureWZ2_projective_parent_direction
        hdelta hrho hA hscaleSmall
        (show delta ≤ A * rho by
          have := scale.property.1
          have hArho : rho ≤ A * rho := by nlinarith
          linarith)
        sourceTube parentTube
        (hcontains parent hparent)).1
    have hparameterBound :
        |1 / 2 - parameter| ≤ A / 2 := by
      rw [abs_le]
      constructor <;>
        linarith [hparameter.1, hparameter.2]
    have hdecomposition :
        (wz2PaperTubeMidpoint parentTube - sourceMidpoint) -
            inner ℝ
                (wz2PaperTubeMidpoint parentTube - sourceMidpoint)
                sourceTube.direction •
              sourceTube.direction =
          ((axisPoint - sourceMidpoint) -
            inner ℝ (axisPoint - sourceMidpoint)
                sourceTube.direction •
              sourceTube.direction) +
            (1 / 2 - parameter) •
              (parentTube.direction -
                inner ℝ parentTube.direction
                    sourceTube.direction •
                  sourceTube.direction) := by
      rw [hmidpointDecomposition, inner_add_left,
        real_inner_smul_left]
      module
    rw [pureWZ2OrientedParent_midpoint]
    rw [hdecomposition]
    calc
      ‖((axisPoint - sourceMidpoint) -
            inner ℝ (axisPoint - sourceMidpoint)
                sourceTube.direction •
              sourceTube.direction) +
          (1 / 2 - parameter) •
            (parentTube.direction -
              inner ℝ parentTube.direction
                  sourceTube.direction •
                sourceTube.direction)‖
          ≤
        ‖(axisPoint - sourceMidpoint) -
            inner ℝ (axisPoint - sourceMidpoint)
                sourceTube.direction •
              sourceTube.direction‖ +
          ‖(1 / 2 - parameter) •
            (parentTube.direction -
              inner ℝ parentTube.direction
                  sourceTube.direction •
                sourceTube.direction)‖ :=
        norm_add_le _ _
      _ ≤
          A * rho +
            (A / 2) * (2 * A * rho) := by
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
      _ = A * (A + 1) * rho := by ring
  have hlongitudinalMidpoint :
      ∀ parent ∈ parents,
        |inner ℝ
            (wz2PaperTubeMidpoint (oriented parent) -
              sourceMidpoint)
            sourceTube.direction| ≤
          A * rho + A / 2 := by
    intro parent hparent
    let parentTube := scaleData.coarse.tube parent
    have hsourceMidpoint :
        sourceMidpoint ∈
          wz2PaperCenteredDilatedCarrier A parentTube := by
      exact hcontains parent hparent
        (wz2_paper_tubeMidpoint_mem_carrier
          sourceTube hdelta.le)
    rcases
        pureWZ2_general_dilation_closest_point
          hrho.le (by linarith) parentTube
          sourceMidpoint hsourceMidpoint with
      ⟨parameter, hparameter, hdistance⟩
    let axisPoint :=
      parentTube.base + parameter • parentTube.direction
    have hdecomposition :
        wz2PaperTubeMidpoint parentTube - sourceMidpoint =
          (axisPoint - sourceMidpoint) +
            (1 / 2 - parameter) •
              parentTube.direction := by
      dsimp only [axisPoint, wz2PaperTubeMidpoint]
      module
    have haxisInner :
        |inner ℝ (axisPoint - sourceMidpoint)
            sourceTube.direction| ≤
          A * rho := by
      exact
        (abs_real_inner_le_norm
          (axisPoint - sourceMidpoint)
          sourceTube.direction).trans
          (by
            rw [sourceTube.direction_unit, mul_one]
            simpa [dist_eq_norm, norm_sub_rev] using hdistance)
    have hparameterBound :
        |1 / 2 - parameter| ≤ A / 2 := by
      rw [abs_le]
      constructor <;>
        linarith [hparameter.1, hparameter.2]
    rw [pureWZ2OrientedParent_midpoint, hdecomposition,
      inner_add_left, inner_smul_left]
    calc
      |inner ℝ (axisPoint - sourceMidpoint)
            sourceTube.direction +
          (1 / 2 - parameter) *
            inner ℝ parentTube.direction
              sourceTube.direction|
          ≤
        |inner ℝ (axisPoint - sourceMidpoint)
            sourceTube.direction| +
          |1 / 2 - parameter| *
            |inner ℝ parentTube.direction
              sourceTube.direction| := by
        simpa [abs_mul] using abs_add_le
          (inner ℝ (axisPoint - sourceMidpoint)
            sourceTube.direction)
          ((1 / 2 - parameter) *
            inner ℝ parentTube.direction
              sourceTube.direction)
      _ ≤ A * rho + (A / 2) * 1 := by
        gcongr
        exact
          (abs_real_inner_le_norm
            parentTube.direction sourceTube.direction).trans
            (by
              rw [parentTube.direction_unit,
                sourceTube.direction_unit]
              norm_num)
      _ = A * rho + A / 2 := by ring
  have hdirection :
      ∀ parent ∈ parents,
        ‖(oriented parent).direction -
            inner ℝ (oriented parent).direction
                sourceTube.direction •
              sourceTube.direction‖ ≤
          (2 * A) * rho := by
    intro parent hparent
    rw [pureWZ2OrientedParent_transverse]
    simpa [mul_assoc] using
      (pureWZ2_projective_parent_direction
        hdelta hrho hA hscaleSmall
        (show delta ≤ A * rho by
          have := scale.property.1
          have hArho : rho ≤ A * rho := by nlinarith
          linarith)
        sourceTube (scaleData.coarse.tube parent)
        (hcontains parent hparent)).1
  have hpositiveInner :
      ∀ parent ∈ parents,
        inner ℝ (oriented parent).direction
            sourceTube.direction ≥
          1 / 2 := by
    intro parent hparent
    have hprojective :=
      (pureWZ2_projective_parent_direction
        hdelta hrho hA hscaleSmall
        (show delta ≤ A * rho by
          have := scale.property.1
          have hArho : rho ≤ A * rho := by nlinarith
          linarith)
        sourceTube (scaleData.coarse.tube parent)
        (hcontains parent hparent)).2
    change
      inner ℝ
          (pureWZ2OrientedParent sourceTube.direction
            (scaleData.coarse.tube parent)).direction
          sourceTube.direction ≥
        1 / 2
    unfold pureWZ2OrientedParent
    split_ifs with hsign
    · rw [abs_of_nonneg hsign] at hprojective
      exact hprojective
    · have hnegative :
          inner ℝ
              (scaleData.coarse.tube parent).direction
              sourceTube.direction < 0 := lt_of_not_ge hsign
      rw [abs_of_neg hnegative] at hprojective
      simp only [reverseTube, inner_neg_left]
      linarith
  have horientedDistinct :
      ∀ first second,
        first ∈ parents → second ∈ parents →
        first ≠ second →
        (oriented first).EssentiallyDistinct
          (oriented second) := by
    intro first second _ _ hne
    exact
      pureWZ2OrientedParent_distinct
        (scaleData.coarse_distinct first second hne)
  have hcapsuleLower : CapsuleLowerBound :=
    capsule_lower_bound_instantiation
  have hcapsuleUpper : CapsuleUpperBound :=
    capsule_upper_bound_instantiation
  have hbound :=
    large_scale_packing_bound
      hrho scale.property.2
      (show 0 ≤ A * (A + 1) * rho by positivity)
      (show 0 ≤ A * rho + A / 2 by positivity)
      (show 0 ≤ 2 * A by positivity)
      parents sourceMidpoint sourceTube.direction
      sourceTube.direction_unit
      htransverseMidpoint hlongitudinalMidpoint
      hdirection hpositiveInner horientedDistinct
      hcapsuleLower hcapsuleUpper
  have htransverseRatio :
      200 * (A * (A + 1) * rho) / rho =
        200 * A * (A + 1) := by
    field_simp [hrho.ne']
  rw [htransverseRatio] at hbound
  have hlongitudinal :
      A * rho + A / 2 ≤ 3 * A / 2 := by
    have hrhoOne := scale.property.2
    nlinarith
  have hceilLong :
      Nat.ceil
          ((400 * max (2 * A) 16) *
            (A * rho + A / 2)) ≤
        Nat.ceil
          ((400 * max (2 * A) 16) *
            (3 * A / 2)) := by
    apply Nat.ceil_mono
    gcongr
  have hsecond :
      2 * Nat.ceil
            ((400 * max (2 * A) 16) *
              (A * rho + A / 2)) + 1 ≤
        2 * Nat.ceil
            ((400 * max (2 * A) 16) *
              (3 * A / 2)) + 1 := by
    omega
  exact hbound.trans <| by
    dsimp only [pureWZ2CompleteFiberOverlapBound]
    have hleft :=
      Nat.mul_le_mul_left
        ((2 * Nat.ceil (200 * A * (A + 1)) + 1) ^ 2)
        hsecond
    have hproduct :=
      Nat.mul_le_mul_right
        ((2 * Nat.ceil (400 * A) + 1) ^ 2)
        hleft
    simpa [show 200 * (2 * A) = 400 * A by ring,
      Nat.mul_assoc] using hproduct

end Kakeya.Assouad

end
