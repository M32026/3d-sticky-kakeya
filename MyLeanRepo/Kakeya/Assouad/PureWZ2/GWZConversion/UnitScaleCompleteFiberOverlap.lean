import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.CompleteFiberOverlap

/-!
# Complete-fiber overlap at exact scale one

At the top GWZ scale the parent directions need not be close to a fixed
source direction.  Split the unit sphere into six signed coordinate charts.
Inside one chart, all parent directions have positive inner product at least
`1 / 2` with a fixed coordinate axis, so the existing five-dimensional
large-scale packing theorem applies.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas

attribute [local instance] Classical.propDecidable

/-- One exact scale-one complete-incidence overlap constant. -/
def pureWZ2UnitScaleCompleteFiberOverlapBound (A : ℝ) : ℕ :=
  6 *
    ((2 * Nat.ceil (300 * A) + 1) ^ 2 *
      (2 * Nat.ceil (9600 * A) + 1) *
      (2 * Nat.ceil (200 : ℝ) + 1) ^ 2)

private theorem pureWZ2_unit_vector_signed_coordinate
    (direction : Point3)
    (hdirection : ‖direction‖ = 1) :
    ∃ coordinate : Fin 3,
      ∃ positive : Bool,
        inner ℝ direction
            (if positive then
              EuclideanSpace.single coordinate (1 : ℝ)
            else
              -EuclideanSpace.single coordinate (1 : ℝ)) ≥
          1 / 2 := by
  have hcoordinate :
      ∃ coordinate : Fin 3, 1 / 2 ≤ |direction coordinate| := by
    by_contra hnot
    have hzero : |direction 0| < 1 / 2 :=
      lt_of_not_ge fun h => hnot ⟨0, h⟩
    have hone : |direction 1| < 1 / 2 :=
      lt_of_not_ge fun h => hnot ⟨1, h⟩
    have htwo : |direction 2| < 1 / 2 :=
      lt_of_not_ge fun h => hnot ⟨2, h⟩
    have hnormSq :
        ‖direction‖ ^ 2 =
          direction 0 ^ 2 + direction 1 ^ 2 + direction 2 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_succ]
      ring
    have hzeroSq : direction 0 ^ 2 < 1 / 4 := by
      nlinarith [sq_abs (direction 0), abs_nonneg (direction 0)]
    have honeSq : direction 1 ^ 2 < 1 / 4 := by
      nlinarith [sq_abs (direction 1), abs_nonneg (direction 1)]
    have htwoSq : direction 2 ^ 2 < 1 / 4 := by
      nlinarith [sq_abs (direction 2), abs_nonneg (direction 2)]
    rw [hdirection] at hnormSq
    nlinarith
  rcases hcoordinate with ⟨coordinate, hcoordinate⟩
  by_cases hpositive : 0 ≤ direction coordinate
  · refine ⟨coordinate, true, ?_⟩
    change inner ℝ direction
        (EuclideanSpace.single coordinate (1 : ℝ)) ≥ 1 / 2
    rw [EuclideanSpace.inner_single_right]
    simp only [RCLike.star_def, starRingEnd_apply, star_id_of_comm]
    rw [abs_of_nonneg hpositive] at hcoordinate
    simpa using hcoordinate
  · refine ⟨coordinate, false, ?_⟩
    have hnegative : direction coordinate < 0 :=
      lt_of_not_ge hpositive
    change inner ℝ direction
        (-EuclideanSpace.single coordinate (1 : ℝ)) ≥ 1 / 2
    rw [inner_neg_right]
    rw [EuclideanSpace.inner_single_right]
    simp only [RCLike.star_def, starRingEnd_apply, star_id_of_comm]
    rw [abs_of_neg hnegative] at hcoordinate
    simpa using hcoordinate

/--
At exact GWZ scale one, each source tube belongs to only a fixed number of
complete fixed-dilation fibers.
-/
theorem pureWZ2_unit_scale_complete_fiber_overlap
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    (scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant)
    (hscale : scale.1 = 1) :
    ∀ index : Fin source.card,
      (Finset.univ.filter fun parent :
        Fin scaleData.coarse.card =>
          index ∈ scaleData.fullFiberIndices parent).card ≤
        pureWZ2UnitScaleCompleteFiberOverlapBound A := by
  intro index
  let sourceTube := source.tube index
  let sourceMidpoint := wz2PaperTubeMidpoint sourceTube
  let parents : Finset (Fin scaleData.coarse.card) :=
    Finset.univ.filter fun parent =>
      index ∈ scaleData.fullFiberIndices parent
  let Axis := Fin 3 × Bool
  let axis : Axis → Point3 := fun label =>
    if label.2 then
      EuclideanSpace.single label.1 (1 : ℝ)
    else
      -EuclideanSpace.single label.1 (1 : ℝ)
  let chart : Axis → Finset (Fin scaleData.coarse.card) :=
    fun label =>
      parents.filter fun parent =>
        inner ℝ (scaleData.coarse.tube parent).direction
          (axis label) ≥ 1 / 2
  have hcontains :
      ∀ parent ∈ parents,
        sourceTube.carrier ⊆
          wz2PaperCenteredDilatedCarrier A
            (scaleData.coarse.tube parent) := by
    intro parent hparent
    have hmember := (Finset.mem_filter.mp hparent).2
    rw [scaleData.fullFiberIndices_eq] at hmember
    exact (Finset.mem_filter.mp hmember).2
  have hmidpoint :
      ∀ parent ∈ parents,
        dist
            (wz2PaperTubeMidpoint
              (scaleData.coarse.tube parent))
            sourceMidpoint ≤
          3 * A / 2 := by
    intro parent hparent
    let parentTube := scaleData.coarse.tube parent
    have hsourceMidpoint :
        sourceMidpoint ∈
          wz2PaperCenteredDilatedCarrier A parentTube :=
      hcontains parent hparent
        (wz2_paper_tubeMidpoint_mem_carrier
          sourceTube hdelta.le)
    rcases
        pureWZ2_general_dilation_closest_point
          (by simpa [hscale] using scale.property.1.le)
          (by linarith) parentTube sourceMidpoint
          hsourceMidpoint with
      ⟨parameter, hparameter, hdistance⟩
    let axisPoint :=
      parentTube.base + parameter • parentTube.direction
    have hdecomposition :
        wz2PaperTubeMidpoint parentTube - sourceMidpoint =
          (axisPoint - sourceMidpoint) +
            (1 / 2 - parameter) • parentTube.direction := by
      dsimp only [axisPoint, wz2PaperTubeMidpoint]
      module
    have hparameterBound :
        |1 / 2 - parameter| ≤ A / 2 := by
      rw [abs_le]
      constructor <;> linarith [hparameter.1, hparameter.2]
    have hdistance' :
        dist sourceMidpoint axisPoint ≤ A := by
      calc
        dist sourceMidpoint axisPoint ≤ A * scale.1 := by
          simpa [axisPoint] using hdistance
        _ = A := by rw [hscale, mul_one]
    rw [dist_eq_norm, hdecomposition]
    calc
      ‖(axisPoint - sourceMidpoint) +
          (1 / 2 - parameter) • parentTube.direction‖ ≤
          ‖axisPoint - sourceMidpoint‖ +
            ‖(1 / 2 - parameter) • parentTube.direction‖ :=
        norm_add_le _ _
      _ ≤ A + A / 2 := by
        rw [norm_smul, Real.norm_eq_abs,
          parentTube.direction_unit, mul_one]
        gcongr
        simpa [dist_eq_norm, norm_sub_rev] using hdistance'
      _ = 3 * A / 2 := by ring
  have haxisNorm :
      ∀ label : Axis, ‖axis label‖ = 1 := by
    rintro ⟨coordinate, positive⟩
    fin_cases coordinate <;> cases positive <;>
      simp [axis, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
  have hcover :
      parents ⊆
        (Finset.univ : Finset Axis).biUnion chart := by
    intro parent hparent
    rcases
        pureWZ2_unit_vector_signed_coordinate
          (scaleData.coarse.tube parent).direction
          (scaleData.coarse.tube parent).direction_unit with
      ⟨coordinate, positive, hdirection⟩
    rw [Finset.mem_biUnion]
    refine ⟨(coordinate, positive), Finset.mem_univ _, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hparent, hdirection⟩
  have hchart :
      ∀ label : Axis,
        (chart label).card ≤
          (2 * Nat.ceil (300 * A) + 1) ^ 2 *
            (2 * Nat.ceil (9600 * A) + 1) *
            (2 * Nat.ceil (200 : ℝ) + 1) ^ 2 := by
    intro label
    have hmidTrans :
        ∀ parent ∈ chart label,
          ‖((wz2PaperTubeMidpoint
                (scaleData.coarse.tube parent) -
              sourceMidpoint) -
            inner ℝ
                (wz2PaperTubeMidpoint
                    (scaleData.coarse.tube parent) -
                  sourceMidpoint)
                (axis label) • axis label)‖ ≤
            3 * A / 2 := by
      intro parent hparent
      exact
        (pureWZ2_perp_norm_le
          (axis label)
          (wz2PaperTubeMidpoint
              (scaleData.coarse.tube parent) -
            sourceMidpoint)
          (haxisNorm label)).trans <| by
            rw [← dist_eq_norm]
            exact hmidpoint parent (Finset.mem_filter.mp hparent).1
    have hmidLong :
        ∀ parent ∈ chart label,
          |inner ℝ
              (wz2PaperTubeMidpoint
                  (scaleData.coarse.tube parent) -
                sourceMidpoint)
              (axis label)| ≤
            3 * A / 2 := by
      intro parent hparent
      exact
        (abs_real_inner_le_norm
          (wz2PaperTubeMidpoint
              (scaleData.coarse.tube parent) -
            sourceMidpoint)
          (axis label)).trans <| by
            rw [haxisNorm label, mul_one, ← dist_eq_norm]
            exact hmidpoint parent (Finset.mem_filter.mp hparent).1
    have hdirection :
        ∀ parent ∈ chart label,
          ‖(scaleData.coarse.tube parent).direction -
              inner ℝ
                  (scaleData.coarse.tube parent).direction
                  (axis label) • axis label‖ ≤
            (1 : ℝ) * scale.1 := by
      intro parent _
      calc
        ‖(scaleData.coarse.tube parent).direction -
            inner ℝ
                (scaleData.coarse.tube parent).direction
                (axis label) • axis label‖ ≤
            ‖(scaleData.coarse.tube parent).direction‖ :=
          pureWZ2_perp_norm_le
            (axis label)
            (scaleData.coarse.tube parent).direction
            (haxisNorm label)
        _ = (1 : ℝ) * scale.1 := by
          rw [(scaleData.coarse.tube parent).direction_unit,
            hscale, mul_one]
    have hlong :
        ∀ parent ∈ chart label,
          inner ℝ
              (scaleData.coarse.tube parent).direction
              (axis label) ≥ 1 / 2 := by
      intro parent hparent
      exact (Finset.mem_filter.mp hparent).2
    have hdistinct :
        ∀ first second,
          first ∈ chart label →
          second ∈ chart label →
          first ≠ second →
          (scaleData.coarse.tube first).EssentiallyDistinct
            (scaleData.coarse.tube second) := by
      intro first second _ _ hne
      exact scaleData.coarse_distinct first second hne
    have hbound :=
      large_scale_packing_bound
        (show 0 < scale.1 by simpa [hscale])
        (show scale.1 ≤ 1 by simp [hscale])
        (show 0 ≤ 3 * A / 2 by positivity)
        (show 0 ≤ 3 * A / 2 by positivity)
        (show (0 : ℝ) ≤ 1 by norm_num)
        (chart label) sourceMidpoint (axis label)
        (haxisNorm label)
        hmidTrans hmidLong hdirection hlong hdistinct
        capsule_lower_bound_instantiation
        capsule_upper_bound_instantiation
    have htransverse :
        200 * (3 * A / 2) / scale.1 = 300 * A := by
      rw [hscale]
      ring
    have hlongitudinal :
        (400 * max (1 : ℝ) 16) * (3 * A / 2) =
          9600 * A := by
      norm_num
      ring
    rw [htransverse, hlongitudinal,
      show 200 * (1 : ℝ) = 200 by ring] at hbound
    exact hbound
  calc
    parents.card ≤
        ((Finset.univ : Finset Axis).biUnion chart).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ label : Axis, (chart label).card := by
      simpa using
        (Finset.card_biUnion_le :
          ((Finset.univ : Finset Axis).biUnion chart).card ≤
            ∑ label ∈ (Finset.univ : Finset Axis),
              (chart label).card)
    _ ≤
        ∑ _label : Axis,
          ((2 * Nat.ceil (300 * A) + 1) ^ 2 *
            (2 * Nat.ceil (9600 * A) + 1) *
            (2 * Nat.ceil (200 : ℝ) + 1) ^ 2) := by
      exact Finset.sum_le_sum fun label _ => hchart label
    _ = pureWZ2UnitScaleCompleteFiberOverlapBound A := by
      rw [Finset.sum_const]
      simp only [Finset.card_univ, nsmul_eq_mul]
      rw [show Fintype.card Axis = 6 by simp [Axis]]
      rfl

end Kakeya.Assouad

end
