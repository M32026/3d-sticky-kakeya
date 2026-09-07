import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4BoundedSupport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperMetricFiberEnvelope
import Mathlib.Tactic

/-!
# Upper metric-fiber envelopes from bounded support

The original upper common-envelope lemma assumes that every fine ordinary
carrier lies in `axisBox 2 2 2`.  A normalized Proposition 6.2 source instead
naturally supplies `HasBoundedBase fine 4`, which places its small ordinary
carriers in `axisBox 12 12 12`.

This module repeats only the geometric containment step at that larger fixed
box.  At heights of absolute value at most six, paper line distance controls
same-height axis points with factor `36`.  The existing factor-`100`
homothety around a centered metric parent still absorbs this loss, so the
outer-John common-envelope constant remains `212776173`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- On the height window supplied by `axisBox 12 12 12`, paper line distance
controls corresponding points on two paper-oriented axes with factor `36`. -/
theorem wz1PaperAxisPointAtHeight_dist_le_of_abs_le_six
    {delta rho : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (fineLine : WZ1PaperTubeInLineClass fine)
    (coarseLine : WZ1PaperTubeInLineClass coarse)
    {height : ℝ}
    (heightBound : |height| ≤ 6) :
    dist
        (wz1PaperAxisPointAtHeight fine height)
        (wz1PaperAxisPointAtHeight coarse height) ≤
      36 * wz1PaperLineDistance fine coarse := by
  let fineZero := wz1TubeAxisZeroPoint fine
  let coarseZero := wz1TubeAxisZeroPoint coarse
  let fineDirection := wz1PaperDirection fine
  let coarseDirection := wz1PaperDirection coarse
  let fineVertical := fineDirection (2 : Fin 3)
  let coarseVertical := coarseDirection (2 : Fin 3)
  have fineVerticalLower : 1 / 2 ≤ fineVertical := fineLine.1
  have coarseVerticalLower : 1 / 2 ≤ coarseVertical := coarseLine.1
  have fineVerticalPos : 0 < fineVertical := by linarith
  have coarseVerticalPos : 0 < coarseVertical := by linarith
  have fineVerticalInv : fineVertical⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ fineVerticalPos).mpr (by linarith)
  have verticalDifference :
      |fineVertical - coarseVertical| ≤
        ‖fineDirection - coarseDirection‖ :=
    abs_coord_two_le_norm (fineDirection - coarseDirection)
      |>.trans_eq (by rfl)
  have inverseDifference :
      |fineVertical⁻¹ - coarseVertical⁻¹| ≤
        4 * |fineVertical - coarseVertical| := by
    have algebra :
        fineVertical⁻¹ - coarseVertical⁻¹ =
          (coarseVertical - fineVertical) /
            (fineVertical * coarseVertical) := by
      field_simp [fineVerticalPos.ne', coarseVerticalPos.ne']
    rw [algebra, abs_div, abs_mul,
      abs_of_pos fineVerticalPos, abs_of_pos coarseVerticalPos,
      abs_sub_comm]
    have denominatorLower :
        1 / 4 ≤ fineVertical * coarseVertical := by
      nlinarith
    have denominatorPos :
        0 < fineVertical * coarseVertical := by positivity
    exact
      (div_le_iff₀ denominatorPos).mpr <| by
        nlinarith [abs_nonneg (fineVertical - coarseVertical)]
  have parameterDifference :
      |height / fineVertical - height / coarseVertical| ≤
        24 * ‖fineDirection - coarseDirection‖ := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, abs_mul]
    calc
      |height| * |fineVertical⁻¹ - coarseVertical⁻¹| ≤
          6 * (4 * |fineVertical - coarseVertical|) := by
        exact
          mul_le_mul heightBound inverseDifference
            (abs_nonneg _) (by norm_num)
      _ = 24 * |fineVertical - coarseVertical| := by ring
      _ ≤ 24 * ‖fineDirection - coarseDirection‖ := by
        gcongr
  have pointDifference :
      wz1PaperAxisPointAtHeight fine height -
          wz1PaperAxisPointAtHeight coarse height =
        (fineZero - coarseZero) +
          (height / fineVertical) •
            (fineDirection - coarseDirection) +
          (height / fineVertical -
            height / coarseVertical) • coarseDirection := by
    dsimp only [wz1PaperAxisPointAtHeight, fineZero, coarseZero,
      fineDirection, coarseDirection, fineVertical, coarseVertical]
    module
  rw [dist_eq_norm, pointDifference]
  calc
    ‖(fineZero - coarseZero) +
        (height / fineVertical) •
          (fineDirection - coarseDirection) +
        (height / fineVertical -
          height / coarseVertical) • coarseDirection‖ ≤
        ‖fineZero - coarseZero‖ +
          ‖(height / fineVertical) •
            (fineDirection - coarseDirection)‖ +
          ‖(height / fineVertical -
            height / coarseVertical) • coarseDirection‖ := by
      exact (norm_add_le _ _).trans <| by
        gcongr
        exact norm_add_le _ _
    _ = dist fineZero coarseZero +
          |height / fineVertical| *
            ‖fineDirection - coarseDirection‖ +
          |height / fineVertical -
            height / coarseVertical| := by
      rw [norm_smul, norm_smul,
        wz1PaperDirection_norm coarse, mul_one, dist_eq_norm]
      simp only [Real.norm_eq_abs]
    _ ≤ dist fineZero coarseZero +
          12 * ‖fineDirection - coarseDirection‖ +
          24 * ‖fineDirection - coarseDirection‖ := by
      gcongr
      rw [abs_div, abs_of_pos fineVerticalPos]
      exact
        (div_le_iff₀ fineVerticalPos).mpr <| by
          nlinarith [abs_nonneg height]
    _ ≤ dist fineZero coarseZero +
          36 * InnerProductGeometry.angle
            fineDirection coarseDirection := by
      have chord :=
        unit_norm_sub_le_angle
          (wz1PaperDirection_norm fine)
          (wz1PaperDirection_norm coarse)
      nlinarith
    _ ≤ 36 * wz1PaperLineDistance fine coarse := by
      dsimp only [wz1PaperLineDistance, fineZero, coarseZero,
        fineDirection, coarseDirection]
      have distanceNonnegative :
          0 ≤
            dist
              (wz1TubeAxisZeroPoint fine)
              (wz1TubeAxisZeroPoint coarse) :=
        dist_nonneg
      have angleNonnegative :
          0 ≤
            InnerProductGeometry.angle
              (wz1PaperDirection fine)
              (wz1PaperDirection coarse) :=
        InnerProductGeometry.angle_nonneg _ _
      nlinarith

/--
An ordinary fine carrier in `axisBox 12 12 12` that is line-covered by a
centered coarse tube lies in the same factor-`100` parent homothety used by
the original upper-envelope proof.
-/
theorem pureWZ2_prop62_carrier_subset_centered_parent_homothety_of_axisBox_twelve
    {delta rho : ℝ}
    (deltaPos : 0 < delta)
    (rhoPos : 0 < rho)
    (scaleGap : 4 * delta ≤ rho)
    (fine : Kakeya.DeltaTube delta)
    (coarse : Kakeya.DeltaTube rho)
    (fineLine : WZ1PaperTubeInLineClass fine)
    (coarseLine : WZ1PaperTubeInLineClass coarse)
    (lineCover : WZ1PaperTubeCovers fine coarse)
    (fineAxisBox :
      fine.carrier ⊆
        Kakeya.Streamlined.axisBox 12 12 12)
    (coarseCentered :
      wz2PaperCenteredLineTube (targetScale := rho) coarse =
        coarse) :
    fine.carrier ⊆
      AffineMap.homothety
          (wz2PaperTubeMidpoint coarse) (100 : ℝ) ''
        coarse.carrier := by
  intro point pointMem
  rcases exists_closest_on_axis deltaPos.le fine point pointMem with
    ⟨sourceParameter, _sourceParameterMem, sourceAxisDistance⟩
  let sourceAxisPoint :=
    fine.base + sourceParameter • fine.direction
  have sourceAxisMem :
      sourceAxisPoint ∈ tubeAxisLine fine := by
    exact ⟨sourceParameter, rfl⟩
  let height := point (2 : Fin 3)
  let fineAtHeight :=
    wz1PaperAxisPointAtHeight fine height
  let coarseAtHeight :=
    wz1PaperAxisPointAtHeight coarse height
  have pointFineAtHeight :
      dist point fineAtHeight ≤ 2 * delta := by
    have sameHeight :=
      wz1Paper_axisPointAtHeight_dist_point_le_two_mul
        fineLine point sourceAxisPoint sourceAxisMem
    calc
      dist point fineAtHeight =
          dist fineAtHeight point := dist_comm _ _
      _ ≤ 2 * dist point sourceAxisPoint := sameHeight
      _ ≤ 2 * delta := by gcongr
  have heightBound : |height| ≤ 6 := by
    have support := fineAxisBox pointMem
    have verticalBound := support.2.2
    norm_num at verticalBound
    simpa [height] using verticalBound
  have fineCoarseAtHeight :
      dist fineAtHeight coarseAtHeight ≤ 18 * rho := by
    have lineDistance :=
      wz1PaperAxisPointAtHeight_dist_le_of_abs_le_six
        fineLine coarseLine heightBound
    unfold WZ1PaperTubeCovers at lineCover
    exact lineDistance.trans <| by nlinarith
  have pointCoarseAtHeight :
      dist point coarseAtHeight ≤ 19 * rho := by
    calc
      dist point coarseAtHeight ≤
          dist point fineAtHeight +
            dist fineAtHeight coarseAtHeight :=
        dist_triangle _ _ _
      _ ≤ 2 * delta + 18 * rho := by gcongr
      _ ≤ 19 * rho := by nlinarith
  let midpoint := wz2PaperTubeMidpoint coarse
  let direction := wz1PaperDirection coarse
  let vertical := direction (2 : Fin 3)
  let parameter := height / vertical
  let contractedParameter := 1 / 2 + parameter / 100
  let contractedAxisPoint :=
    coarse.base + contractedParameter • coarse.direction
  let contractedPoint :=
    AffineMap.homothety midpoint (1 / 100 : ℝ) point
  have verticalLower : 1 / 2 ≤ vertical := coarseLine.1
  have verticalPos : 0 < vertical := by linarith
  have parameterBound : |parameter| ≤ 12 := by
    dsimp only [parameter]
    rw [abs_div, abs_of_pos verticalPos]
    exact
      (div_le_iff₀ verticalPos).mpr <| by
        nlinarith [abs_nonneg height]
  have contractedParameterMem :
      contractedParameter ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [contractedParameter]
    rw [Set.mem_Icc]
    have bounds := abs_le.mp parameterBound
    constructor <;> linarith
  have coarseDirection :
      coarse.direction = direction := by
    have directionEq :
        (wz2PaperCenteredLineTube
          (targetScale := rho) coarse).direction =
          wz1PaperDirection coarse := rfl
    rwa [coarseCentered] at directionEq
  have coarseBase :
      coarse.base =
        midpoint - (1 / 2 : ℝ) • direction := by
    have midpointEq :
        midpoint =
          coarse.base + (1 / 2 : ℝ) • coarse.direction := by
      rfl
    rw [coarseDirection] at midpointEq
    rw [midpointEq]
    abel
  have coarseZero :
      wz1TubeAxisZeroPoint coarse = midpoint := by
    have midpointEq :
        wz2PaperTubeMidpoint
            (wz2PaperCenteredLineTube
              (targetScale := rho) coarse) =
          wz1TubeAxisZeroPoint coarse :=
      wz2PaperCenteredLineTube_midpoint coarse
    rw [coarseCentered] at midpointEq
    exact midpointEq.symm
  have coarseAtHeightEq :
      coarseAtHeight =
        midpoint + parameter • direction := by
    dsimp only [coarseAtHeight, parameter, direction]
    rw [wz1PaperAxisPointAtHeight, coarseZero]
  have contractedAxisEq :
      contractedAxisPoint =
        AffineMap.homothety midpoint (1 / 100 : ℝ)
          coarseAtHeight := by
    rw [coarseAtHeightEq, AffineMap.homothety_apply]
    dsimp only [contractedAxisPoint, contractedParameter]
    rw [coarseDirection, coarseBase]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  have contractedDistance :
      dist contractedPoint contractedAxisPoint ≤ rho := by
    rw [contractedAxisEq]
    have scaledDistance :
        dist
            (AffineMap.homothety midpoint (1 / 100 : ℝ) point)
            (AffineMap.homothety midpoint (1 / 100 : ℝ)
              coarseAtHeight) =
          (1 / 100 : ℝ) * dist point coarseAtHeight :=
      homothety_dist (by norm_num) point coarseAtHeight
    rw [scaledDistance]
    calc
      (1 / 100 : ℝ) * dist point coarseAtHeight ≤
          (1 / 100 : ℝ) * (19 * rho) := by gcongr
      _ ≤ rho := by nlinarith
  have contractedAxisMem :
      contractedAxisPoint ∈
        Kakeya.unitSegment coarse.base coarse.direction :=
    ⟨contractedParameter, contractedParameterMem, rfl⟩
  have contractedCarrier :
      contractedPoint ∈ coarse.carrier :=
    Metric.mem_cthickening_of_dist_le
      contractedPoint contractedAxisPoint rho
      (Kakeya.unitSegment coarse.base coarse.direction)
      contractedAxisMem contractedDistance
  refine ⟨contractedPoint, contractedCarrier, ?_⟩
  dsimp only [contractedPoint, midpoint]
  rw [AffineMap.homothety_apply,
    AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  module

/--
The upper metric-child common envelope remains valid for fine carriers in
`axisBox 12 12 12`.  The factor-`100` parent homothety is unchanged, so the
outer-John volume loss is still exactly `212776173`.
-/
theorem pureWZ2_prop62_metric_children_common_envelope_of_axisBox_twelve
    {delta rho : ℝ}
    (deltaPos : 0 < delta)
    (rhoPos : 0 < rho)
    (scaleGap : 4 * delta ≤ rho)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineAxisBox :
      ∀ source,
        (fine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 12 12 12)
    (coarseCentered :
      ∀ parent,
        wz2PaperCenteredLineTube (targetScale := rho)
            (coarse.tube parent) =
          coarse.tube parent)
    (selected : Finset (Fin coarse.card))
    (selectedNonempty : selected.Nonempty)
    (convexSet : Set Point3)
    (convexSetConvex : Convex ℝ convexSet)
    (selectedContained :
      ∀ parent ∈ selected,
        (coarse.tube parent).carrier ⊆ convexSet) :
    ∃ envelope : Set Point3,
      Convex ℝ envelope ∧
      volume envelope ≤
        (212776173 : ENNReal) * volume convexSet ∧
      ∀ source,
        cover.toWZ1PaperTubeCover.parent source ∈ selected →
          (fine.tube source).carrier ⊆ envelope := by
  let selectedUnion : Set Point3 :=
    ⋃ parent ∈ selected, (coarse.tube parent).carrier
  let convexBody : Set Point3 :=
    convexHull ℝ selectedUnion
  have convexBodyCompact : IsCompact convexBody := by
    exact
      Kakeya.Streamlined.RandomTranslation.isCompact_convexHull_finite_union
        selected
        (fun parent => (coarse.tube parent).carrier)
        (by
          intro parent _parentMem
          exact
            ⟨wz2_paper_ordinary_tube_carrier_compact
                (coarse.tube parent) rhoPos,
              wz2_paper_ordinary_tube_carrier_convex
                (coarse.tube parent)⟩)
  have convexBodyConvex : Convex ℝ convexBody :=
    convex_convexHull ℝ selectedUnion
  have convexBodySubset : convexBody ⊆ convexSet := by
    apply convexHull_min
    · intro point pointMem
      simp only [selectedUnion, Set.mem_iUnion] at pointMem
      rcases pointMem with ⟨parent, pointMem⟩
      rcases pointMem with ⟨parentMem, pointMem⟩
      exact selectedContained parent parentMem pointMem
    · exact convexSetConvex
  rcases selectedNonempty with ⟨reference, referenceMem⟩
  have referenceCarrierSubset :
      (coarse.tube reference).carrier ⊆ convexBody := by
    intro point pointMem
    apply subset_convexHull ℝ selectedUnion
    exact
      Set.mem_iUnion.mpr
        ⟨reference,
          Set.mem_iUnion.mpr ⟨referenceMem, pointMem⟩⟩
  have convexBodyInterior :
      (interior convexBody).Nonempty := by
    exact
      (Kakeya.Streamlined.RandomTranslation.deltaTube_nonempty_interior
        rhoPos (coarse.tube reference)).mono
          (interior_mono referenceCarrierSubset)
  have convexBodyIsBody :
      JohnEllipsoid.IsConvexBody convexBody :=
    ⟨convexBodyConvex, convexBodyCompact, convexBodyInterior⟩
  rcases
      wz2_paper_john_homothetic_envelope
        convexBody convexBodyIsBody
    with
    ⟨envelope, envelopeConvex, envelopeVolume,
      envelopeContains⟩
  refine
    ⟨envelope, envelopeConvex,
      envelopeVolume.trans ?_, ?_⟩
  · exact
      mul_le_mul_left'
        (measure_mono convexBodySubset)
        (212776173 : ENNReal)
  · intro source sourceOwnerMem
    let parent :=
      cover.toWZ1PaperTubeCover.parent source
    have parentCarrierSubset :
        (coarse.tube parent).carrier ⊆ convexBody := by
      intro point pointMem
      apply subset_convexHull ℝ selectedUnion
      exact
        Set.mem_iUnion.mpr
          ⟨parent,
            Set.mem_iUnion.mpr
              ⟨sourceOwnerMem, pointMem⟩⟩
    have parentMidpointMem :
        wz2PaperTubeMidpoint (coarse.tube parent) ∈ convexBody :=
      parentCarrierSubset
        (wz2_paper_tubeMidpoint_mem_carrier
          (coarse.tube parent) rhoPos.le)
    have sourceToParentHomothety :
        (fine.tube source).carrier ⊆
          AffineMap.homothety
              (wz2PaperTubeMidpoint (coarse.tube parent))
              (100 : ℝ) ''
            (coarse.tube parent).carrier :=
      pureWZ2_prop62_carrier_subset_centered_parent_homothety_of_axisBox_twelve
        deltaPos rhoPos scaleGap
        (fine.tube source) (coarse.tube parent)
        (cover.fine_line_class source)
        (cover.coarse_line_class parent)
        (cover.toWZ1PaperTubeCover.parent_covers source)
        (fineAxisBox source) (coarseCentered parent)
    exact
      sourceToParentHomothety.trans <|
        (Set.image_mono parentCarrierSubset).trans <|
          envelopeContains
            (wz2PaperTubeMidpoint (coarse.tube parent))
            parentMidpointMem

/--
Pipeline-facing wrapper: bounded base at radius four and
`delta ≤ 1 / 100` provide the `axisBox 12` input required above.
-/
theorem pureWZ2_prop62_metric_children_common_envelope_of_boundedBase_four
    {delta rho : ℝ}
    (deltaPos : 0 < delta)
    (deltaLe : delta ≤ 1 / 100)
    (rhoPos : 0 < rho)
    (scaleGap : 4 * delta ≤ rho)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineBoundedBase : HasBoundedBase fine 4)
    (coarseCentered :
      ∀ parent,
        wz2PaperCenteredLineTube (targetScale := rho)
            (coarse.tube parent) =
          coarse.tube parent)
    (selected : Finset (Fin coarse.card))
    (selectedNonempty : selected.Nonempty)
    (convexSet : Set Point3)
    (convexSetConvex : Convex ℝ convexSet)
    (selectedContained :
      ∀ parent ∈ selected,
        (coarse.tube parent).carrier ⊆ convexSet) :
    ∃ envelope : Set Point3,
      Convex ℝ envelope ∧
      volume envelope ≤
        (212776173 : ENNReal) * volume convexSet ∧
      ∀ source,
        cover.toWZ1PaperTubeCover.parent source ∈ selected →
          (fine.tube source).carrier ⊆ envelope := by
  exact
    pureWZ2_prop62_metric_children_common_envelope_of_axisBox_twelve
      deltaPos rhoPos scaleGap cover
      (pureWZ2Prop62_family_carrier_subset_axisBox_twelve
        deltaPos.le deltaLe cover.fine_line_class fineBoundedBase)
      coarseCentered selected selectedNonempty
      convexSet convexSetConvex selectedContained

end Kakeya.Assouad

end
