import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterNearbyCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.DilatedClosestPoint

/-!
# Caller-center envelope conflict degree

The scheduled raw parents are only known to be essentially distinct in the
literal centered-containment sense.  We therefore pack their ordinary
midpoint and direction parameters directly, rather than passing through the
measure-overlap notion of essential distinctness.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

attribute [local instance] Classical.propDecidable

/--
Two positive-radius ordinary tubes with sufficiently close midpoint and
direction parameters cannot be paper-essentially-distinct: the first carrier
is contained in the centered double of the second.
-/
theorem wz2PaperOrdinary_carrier_subset_centeredDilatedTwo_of_close
    {rho : ℝ}
    (hrho : 0 < rho)
    {first second : Kakeya.DeltaTube rho}
    (hmidpoint :
      ‖wz2PaperTubeMidpoint first -
          wz2PaperTubeMidpoint second‖ ≤
        rho / 16)
    (hdirection :
      ‖first.direction - second.direction‖ ≤
        rho / 16) :
    first.carrier ⊆
      wz2PaperCenteredDilatedCarrier 2 second := by
  intro point hpoint
  have hsegmentCompact :
      IsCompact
        (Kakeya.unitSegment first.base first.direction) := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  change
    point ∈
      Metric.cthickening rho
        (Kakeya.unitSegment first.base first.direction) at hpoint
  rw [hsegmentCompact.cthickening_eq_biUnion_closedBall hrho.le] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨axisPoint, haxisPoint, hpointAxis⟩
  rcases haxisPoint with ⟨parameter, hparameter, rfl⟩
  let firstMidpoint := wz2PaperTubeMidpoint first
  let secondMidpoint := wz2PaperTubeMidpoint second
  let secondParameter : ℝ := parameter / 2 + 1 / 4
  let sourcePoint : Point3 :=
    secondMidpoint +
      (1 / 2 : ℝ) • (point - secondMidpoint)
  have hsecondParameter :
      secondParameter ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [secondParameter]
    constructor <;> linarith [hparameter.1, hparameter.2]
  have hparameterCentered :
      |parameter - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hparameter.1, hparameter.2]
  have haxisIdentity :
      sourcePoint -
          (second.base +
            secondParameter • second.direction) =
        (1 / 2 : ℝ) •
            (point -
              (first.base +
                parameter • first.direction)) +
          (1 / 2 : ℝ) •
            (firstMidpoint - secondMidpoint) +
          ((1 / 2 : ℝ) * (parameter - 1 / 2)) •
            (first.direction - second.direction) := by
    dsimp only [sourcePoint, secondParameter,
      firstMidpoint, secondMidpoint, wz2PaperTubeMidpoint]
    module
  have hpointAxisNorm :
      ‖point -
          (first.base +
            parameter • first.direction)‖ ≤ rho := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hpointAxis
  have hcoefficient :
      |(1 / 2 : ℝ) * (parameter - 1 / 2)| ≤
        1 / 4 := by
    rw [abs_mul]
    norm_num
    linarith
  have hsourceDistance :
      dist sourcePoint
          (second.base +
            secondParameter • second.direction) ≤ rho := by
    rw [dist_eq_norm, haxisIdentity]
    calc
      ‖(1 / 2 : ℝ) •
            (point -
              (first.base +
                parameter • first.direction)) +
          (1 / 2 : ℝ) •
            (firstMidpoint - secondMidpoint) +
          ((1 / 2 : ℝ) * (parameter - 1 / 2)) •
            (first.direction - second.direction)‖
          ≤
        ‖(1 / 2 : ℝ) •
            (point -
              (first.base +
                parameter • first.direction))‖ +
          ‖(1 / 2 : ℝ) •
            (firstMidpoint - secondMidpoint)‖ +
          ‖((1 / 2 : ℝ) * (parameter - 1 / 2)) •
            (first.direction - second.direction)‖ := by
              calc
                _ ≤
                    ‖(1 / 2 : ℝ) •
                        (point -
                          (first.base +
                            parameter • first.direction)) +
                      (1 / 2 : ℝ) •
                        (firstMidpoint - secondMidpoint)‖ +
                      ‖((1 / 2 : ℝ) *
                          (parameter - 1 / 2)) •
                        (first.direction - second.direction)‖ :=
                  norm_add_le _ _
                _ ≤ _ := by
                  gcongr
                  exact norm_add_le _ _
      _ ≤
          (1 / 2 : ℝ) * rho +
            (1 / 2 : ℝ) * (rho / 16) +
            (1 / 4 : ℝ) * (rho / 16) := by
              repeat' rw [norm_smul, Real.norm_eq_abs]
              have hhalf :
                  |(1 / 2 : ℝ)| = 1 / 2 := by
                norm_num
              have hfirstTerm :
                  (1 / 2 : ℝ) *
                      ‖point -
                        (first.base +
                          parameter • first.direction)‖ ≤
                    (1 / 2 : ℝ) * rho :=
                mul_le_mul_of_nonneg_left
                  hpointAxisNorm (by norm_num)
              have hsecondTerm :
                  (1 / 2 : ℝ) *
                      ‖firstMidpoint - secondMidpoint‖ ≤
                    (1 / 2 : ℝ) * (rho / 16) :=
                mul_le_mul_of_nonneg_left
                  hmidpoint (by norm_num)
              have hthirdTerm :
                  |(1 / 2 : ℝ) * (parameter - 1 / 2)| *
                      ‖first.direction - second.direction‖ ≤
                    (1 / 4 : ℝ) * (rho / 16) := by
                calc
                  |(1 / 2 : ℝ) * (parameter - 1 / 2)| *
                        ‖first.direction - second.direction‖
                      ≤ (1 / 4 : ℝ) *
                          ‖first.direction - second.direction‖ :=
                    mul_le_mul_of_nonneg_right
                      hcoefficient (norm_nonneg _)
                  _ ≤ (1 / 4 : ℝ) * (rho / 16) :=
                    mul_le_mul_of_nonneg_left
                      hdirection (by norm_num)
              simpa [hhalf] using
                add_le_add
                  (add_le_add hfirstTerm hsecondTerm)
                  hthirdTerm
      _ ≤ rho := by
        linarith
  have hsourceCarrier :
      sourcePoint ∈ second.carrier := by
    exact
      Metric.mem_cthickening_of_dist_le
        sourcePoint
        (second.base +
          secondParameter • second.direction)
        rho
        (Kakeya.unitSegment second.base second.direction)
        ⟨secondParameter, hsecondParameter, rfl⟩
        hsourceDistance
  refine ⟨sourcePoint, hsourceCarrier, ?_⟩
  ext coordinate
  simp [sourcePoint, secondMidpoint,
    AffineMap.homothety_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply]

/--
A point in the centered double of an ordinary tube lies within
`1 + 2 * rho` of its midpoint.  This bound is uniform at all positive
scales and does not use a line-class chart.
-/
theorem wz2PaperOrdinary_dist_midpoint_le_of_mem_centeredDilatedTwo
    {rho : ℝ}
    (hrho : 0 < rho)
    (tube : Kakeya.DeltaTube rho)
    (point : Point3)
    (hpoint :
      point ∈ wz2PaperCenteredDilatedCarrier 2 tube) :
    dist point (wz2PaperTubeMidpoint tube) ≤
      1 + 2 * rho := by
  rcases
      pureWZ2_general_dilation_closest_point
        hrho.le (by norm_num : (0 : ℝ) < 2)
        tube point hpoint with
    ⟨parameter, hparameter, hdistance⟩
  let axisPoint :=
    tube.base + parameter • tube.direction
  have hparameterBound :
      |parameter - 1 / 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hparameter.1, hparameter.2]
  have haxisMidpoint :
      dist axisPoint (wz2PaperTubeMidpoint tube) =
        |parameter - 1 / 2| := by
    rw [dist_eq_norm]
    have hdifference :
        axisPoint - wz2PaperTubeMidpoint tube =
          (parameter - 1 / 2 : ℝ) • tube.direction := by
      dsimp only [axisPoint, wz2PaperTubeMidpoint]
      module
    rw [hdifference, norm_smul, tube.direction_unit,
      Real.norm_eq_abs, mul_one]
  calc
    dist point (wz2PaperTubeMidpoint tube)
        ≤ dist point axisPoint +
            dist axisPoint (wz2PaperTubeMidpoint tube) :=
      dist_triangle _ _ _
    _ ≤ 2 * rho + 1 := by
      rw [haxisMidpoint]
      exact add_le_add hdistance hparameterBound
    _ = 1 + 2 * rho := by ring

/--
Six-parameter packing for the literal paper notion of essential
distinctness.  Midpoints occupy one Euclidean ball and directions occupy the
unit ball.  At mesh `rho / 64`, equal midpoint and direction cells force
centered-double containment.
-/
theorem wz2PaperOrdinary_local_six_grid_card_bound
    {rho midpointRadius : ℝ}
    (hrho : 0 < rho)
    (hmidpointRadius : 0 ≤ midpointRadius)
    {family : Kakeya.Streamlined.TubeFamily rho}
    (familyDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct family)
    (indices : Finset (Fin family.card))
    (center : Point3)
    (hmidpoint :
      ∀ index ∈ indices,
        ‖wz2PaperTubeMidpoint (family.tube index) -
            center‖ ≤ midpointRadius) :
    indices.card ≤
      (2 * Nat.ceil
          (midpointRadius / (rho / 64)) + 1) ^ 3 *
        (2 * Nat.ceil (1 / (rho / 64)) + 1) ^ 3 := by
  let mesh : ℝ := rho / 64
  have hmesh : 0 < mesh := by
    positivity
  let midpointCellCount :=
    Nat.ceil (midpointRadius / mesh)
  let directionCellCount :=
    Nat.ceil (1 / mesh)
  have hmidpointCellCount :
      midpointRadius / mesh ≤
        (midpointCellCount : ℝ) :=
    Nat.le_ceil _
  have hdirectionCellCount :
      1 / mesh ≤
        (directionCellCount : ℝ) :=
    Nat.le_ceil _
  rcases
      grid3_finset
        midpointCellCount hmidpointRadius hmesh
        hmidpointCellCount with
    ⟨midpointCells, hmidpointCells,
      hmidpointCellsCard⟩
  rcases
      grid3_finset
        directionCellCount (by norm_num : (0 : ℝ) ≤ 1)
        hmesh hdirectionCellCount with
    ⟨directionCells, hdirectionCells,
      hdirectionCellsCard⟩
  let cellRange : Finset (Grid3 × Grid3) :=
    midpointCells ×ˢ directionCells
  let midpointOffset (index : Fin family.card) : Point3 :=
    wz2PaperTubeMidpoint (family.tube index) - center
  let cell (index : Fin family.card) : Grid3 × Grid3 :=
    (grid3 mesh (midpointOffset index),
      grid3 mesh (family.tube index).direction)
  have hcellMem :
      ∀ index ∈ indices, cell index ∈ cellRange := by
    intro index hindex
    rw [Finset.mem_product]
    constructor
    · exact
        hmidpointCells
          (midpointOffset index)
          (hmidpoint index hindex)
    · exact
        hdirectionCells
          (family.tube index).direction
          (by rw [(family.tube index).direction_unit])
  have hsqrt :
      Real.sqrt 3 * mesh < rho / 16 := by
    have hsqrtThree : Real.sqrt 3 < 4 := by
      have hsqrtThreeTwo : Real.sqrt 3 < 2 := by
        have h :=
          Real.sqrt_lt_sqrt
            (show (0 : ℝ) ≤ 3 by norm_num)
            (show (3 : ℝ) < 4 by norm_num)
        norm_num at h
        exact h
      linarith
    dsimp only [mesh]
    nlinarith
  have hcellInjective :
      Set.InjOn cell indices := by
    intro first hfirst second hsecond hcell
    by_contra hne
    have hmidpointCell :
        grid3 mesh (midpointOffset first) =
          grid3 mesh (midpointOffset second) :=
      congrArg Prod.fst hcell
    have hdirectionCell :
        grid3 mesh (family.tube first).direction =
          grid3 mesh (family.tube second).direction :=
      congrArg Prod.snd hcell
    have hmidpointClose :
        ‖wz2PaperTubeMidpoint (family.tube first) -
            wz2PaperTubeMidpoint (family.tube second)‖ ≤
          rho / 16 := by
      have hoffsetClose :=
        grid3_close hmesh hmidpointCell
      have hoffsetDifference :
          midpointOffset first - midpointOffset second =
            wz2PaperTubeMidpoint (family.tube first) -
              wz2PaperTubeMidpoint (family.tube second) := by
        dsimp only [midpointOffset]
        module
      rw [hoffsetDifference] at hoffsetClose
      exact hoffsetClose.le.trans hsqrt.le
    have hdirectionClose :
        ‖(family.tube first).direction -
            (family.tube second).direction‖ ≤
          rho / 16 :=
      (grid3_close hmesh hdirectionCell).le.trans hsqrt.le
    have hcontainment :=
      wz2PaperOrdinary_carrier_subset_centeredDilatedTwo_of_close
        hrho hmidpointClose hdirectionClose
    exact
      (familyDistinct first second hne).1 hcontainment
  have himageCard :
      (Finset.image cell indices).card = indices.card :=
    Finset.card_image_of_injOn hcellInjective
  have himageSubset :
      Finset.image cell indices ⊆ cellRange := by
    intro imageIndex himageIndex
    rcases Finset.mem_image.mp himageIndex with
      ⟨index, hindex, rfl⟩
    exact hcellMem index hindex
  have hcard :
      indices.card ≤ cellRange.card := by
    rw [← himageCard]
    exact Finset.card_le_card himageSubset
  have hcellRangeCard :
      cellRange.card =
        (2 * midpointCellCount + 1) ^ 3 *
          (2 * directionCellCount + 1) ^ 3 := by
    rw [Finset.card_product,
      hmidpointCellsCard, hdirectionCellsCard]
  rw [hcellRangeCard] at hcard
  simpa [mesh, midpointCellCount,
    directionCellCount] using hcard

/--
The explicit six-dimensional grid bound for one scheduled raw-parent
envelope conflict graph.
-/
def pureWZ2CallerCenterEnvelopeConflictDegree
    (rho : ℝ) : ℕ :=
  (2 * Nat.ceil
      ((2 + 76 * rho) / (rho / 64)) + 1) ^ 3 *
    (2 * Nat.ceil (1 / (rho / 64)) + 1) ^ 3

/--
Every raw scheduled envelope has uniformly bounded conflict degree relative
to a fixed caller subfamily.  A conflicting caller midpoint lies in both
centered doubled envelopes, so the two raw parent midpoints are within
`2 + 76 * rho`.  Literal essential distinctness of the raw scheduled cover
then makes the six-parameter grid map injective.
-/
theorem pureWZ2_caller_center_envelope_conflict_degree
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    {scheduledRequested : WZ2PaperRequestedScale delta}
    (scheduled :
      WZ2PaperPureNearbyScaleCoverData
        fine scheduledRequested ambientConstant)
    (callerBase :
      WZ2PaperPureTubeSubfamily quotient.callerCoarse)
    (fineNonempty : fine.Nonempty) :
    ∀ fixed : Fin scheduled.scaleData.coarse.card,
      (Finset.univ.filter fun other =>
        other ≠ fixed ∧
          (wz2PaperOrdinaryDilatedFiberIndices
              2 callerBase.family
              (wz2PaperOrdinaryEnvelopeFamily
                scheduled.scaleData.coarse) fixed ∩
            wz2PaperOrdinaryDilatedFiberIndices
              2 callerBase.family
              (wz2PaperOrdinaryEnvelopeFamily
                scheduled.scaleData.coarse) other).Nonempty).card ≤
        pureWZ2CallerCenterEnvelopeConflictDegree scheduled.rho := by
  intro fixed
  let conflicts :
      Finset (Fin scheduled.scaleData.coarse.card) :=
    Finset.univ.filter fun other =>
      other ≠ fixed ∧
        (wz2PaperOrdinaryDilatedFiberIndices
            2 callerBase.family
            (wz2PaperOrdinaryEnvelopeFamily
              scheduled.scaleData.coarse) fixed ∩
          wz2PaperOrdinaryDilatedFiberIndices
            2 callerBase.family
            (wz2PaperOrdinaryEnvelopeFamily
              scheduled.scaleData.coarse) other).Nonempty
  have rawDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct
        scheduled.scaleData.coarse :=
    scheduled.scaleData.cover.coarse_essentiallyDistinct_of_uniform
      scheduled.scaleData.rho_pos.le
      fineNonempty
      scheduled.scaleData.full_fiber_uniform
  have hmidpoint :
      ∀ other ∈ conflicts,
        ‖wz2PaperTubeMidpoint
              (scheduled.scaleData.coarse.tube other) -
            wz2PaperTubeMidpoint
              (scheduled.scaleData.coarse.tube fixed)‖ ≤
          2 + 76 * scheduled.rho := by
    intro other hother
    have hoverlap :=
      (Finset.mem_filter.mp hother).2.2
    rcases hoverlap with
      ⟨callerIndex, hcallerIndex⟩
    rcases Finset.mem_inter.mp hcallerIndex with
      ⟨hfixed, hother'⟩
    rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
      at hfixed hother'
    let callerTube := callerBase.family.tube callerIndex
    let callerMidpoint := wz2PaperTubeMidpoint callerTube
    have hcallerPos :
        0 < callerRequested.1 :=
      scheduled.scaleData.delta_pos.trans_le
        callerRequested.2.1
    have hcallerMidpoint :
        callerMidpoint ∈ callerTube.carrier :=
      wz2_paper_tubeMidpoint_mem_carrier
        callerTube hcallerPos.le
    have hfixedPoint :
        callerMidpoint ∈
          wz2PaperCenteredDilatedCarrier 2
            ((wz2PaperOrdinaryEnvelopeFamily
              scheduled.scaleData.coarse).tube fixed) :=
      hfixed hcallerMidpoint
    have hotherPoint :
        callerMidpoint ∈
          wz2PaperCenteredDilatedCarrier 2
            ((wz2PaperOrdinaryEnvelopeFamily
              scheduled.scaleData.coarse).tube other) :=
      hother' hcallerMidpoint
    have henvelopePos :
        0 < 19 * scheduled.rho := by
      exact mul_pos (by norm_num) scheduled.scaleData.rho_pos
    have hfixedDistance :=
      wz2PaperOrdinary_dist_midpoint_le_of_mem_centeredDilatedTwo
        henvelopePos
        ((wz2PaperOrdinaryEnvelopeFamily
          scheduled.scaleData.coarse).tube fixed)
        callerMidpoint hfixedPoint
    have hotherDistance :=
      wz2PaperOrdinary_dist_midpoint_le_of_mem_centeredDilatedTwo
        henvelopePos
        ((wz2PaperOrdinaryEnvelopeFamily
          scheduled.scaleData.coarse).tube other)
        callerMidpoint hotherPoint
    have hfixedDistance' :
        dist callerMidpoint
            (wz2PaperTubeMidpoint
              (scheduled.scaleData.coarse.tube fixed)) ≤
          1 + 38 * scheduled.rho := by
      convert hfixedDistance using 1 <;>
        simp [wz2PaperTubeMidpoint] <;> ring
    have hotherDistance' :
        dist
            (wz2PaperTubeMidpoint
              (scheduled.scaleData.coarse.tube other))
            callerMidpoint ≤
          1 + 38 * scheduled.rho := by
      rw [dist_comm]
      convert hotherDistance using 1 <;>
        simp [wz2PaperTubeMidpoint] <;> ring
    rw [← dist_eq_norm]
    calc
      dist
          (wz2PaperTubeMidpoint
            (scheduled.scaleData.coarse.tube other))
          (wz2PaperTubeMidpoint
            (scheduled.scaleData.coarse.tube fixed))
          ≤
        dist
            (wz2PaperTubeMidpoint
              (scheduled.scaleData.coarse.tube other))
            callerMidpoint +
          dist callerMidpoint
            (wz2PaperTubeMidpoint
              (scheduled.scaleData.coarse.tube fixed)) :=
        dist_triangle _ _ _
      _ ≤
          (1 + 38 * scheduled.rho) +
            (1 + 38 * scheduled.rho) :=
        add_le_add hotherDistance' hfixedDistance'
      _ = 2 + 76 * scheduled.rho := by ring
  have hbound :=
    wz2PaperOrdinary_local_six_grid_card_bound
      scheduled.scaleData.rho_pos
      (by
        have := scheduled.scaleData.rho_pos.le
        linarith : 0 ≤ 2 + 76 * scheduled.rho)
      rawDistinct conflicts
      (wz2PaperTubeMidpoint
        (scheduled.scaleData.coarse.tube fixed))
      hmidpoint
  simpa [conflicts,
    pureWZ2CallerCenterEnvelopeConflictDegree] using hbound

/--
The geometric conflict bound supplies the proper coloring consumed by the
simultaneous finite caller-center selection.
-/
theorem pureWZ2_caller_center_envelope_coloring_of_geometry
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    {scheduledRequested : WZ2PaperRequestedScale delta}
    (scheduled :
      WZ2PaperPureNearbyScaleCoverData
        fine scheduledRequested ambientConstant)
    (callerBase :
      WZ2PaperPureTubeSubfamily quotient.callerCoarse)
    (fineNonempty : fine.Nonempty) :
    Nonempty
      (PureWZ2CallerCenterEnvelopeColoringData
        quotient scheduled callerBase
        (Fin
          (pureWZ2CallerCenterEnvelopeConflictDegree
              scheduled.rho + 1))) :=
  pureWZ2_caller_center_envelope_coloring
    quotient scheduled callerBase
    (pureWZ2CallerCenterEnvelopeConflictDegree scheduled.rho)
    (pureWZ2_caller_center_envelope_conflict_degree
      quotient scheduled callerBase fineNonempty)

end Kakeya.Assouad

end
