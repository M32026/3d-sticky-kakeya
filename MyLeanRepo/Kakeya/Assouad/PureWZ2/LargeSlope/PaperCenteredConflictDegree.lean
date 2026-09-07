import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalTubeParameters
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperCenteredWeightedSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedDoubledFiber

/-!
# Public centered-conflict degree after affine-diagonal retubing

The argument stays in the public Definition 2.12 relation.  Centered
containment gives a paper line-distance bound; vertical-chart algebra gives a
target parameter box; exact affine-line provenance and the inverse parameter
formula pull that box back to the source.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Vertical-chart parameters are independent of the orientation chosen for
the supporting line. -/
lemma tubeParamsOfTube_eq_paper_zero_and_direction_ratio
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    (tubeParamsOfTube tube).a = wz1TubeAxisZeroPoint tube 0 ∧
      (tubeParamsOfTube tube).b = wz1TubeAxisZeroPoint tube 1 ∧
      (tubeParamsOfTube tube).c =
        wz1PaperDirection tube 0 / wz1PaperDirection tube 2 ∧
      (tubeParamsOfTube tube).d =
        wz1PaperDirection tube 1 / wz1PaperDirection tube 2 := by
  have hvertical : tube.direction (2 : Fin 3) ≠ 0 :=
    fun hzero => by
      have h := hline.vertical
      rw [hzero, abs_zero] at h
      norm_num at h
  constructor
  · simp only [tubeParamsOfTube, wz1TubeAxisZeroPoint, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]
    ring
  constructor
  · simp only [tubeParamsOfTube, wz1TubeAxisZeroPoint, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]
    ring
  unfold wz1PaperDirection
  split_ifs with horientation
  · exact ⟨rfl, rfl⟩
  · constructor <;> simp only [PiLp.neg_apply, tubeParamsOfTube] <;>
      field_simp [hvertical] <;> ring

/-- A small paper line distance gives a common four-parameter box in the
positive vertical chart. -/
theorem tubeParamsOfTube_cluster_of_paperLineDistance
    {firstDelta secondDelta radius : ℝ}
    {first : Kakeya.DeltaTube firstDelta}
    {second : Kakeya.DeltaTube secondDelta}
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second)
    (hdistance : wz1PaperLineDistance first second ≤ radius) :
    |(tubeParamsOfTube first).a - (tubeParamsOfTube second).a| ≤ radius ∧
      |(tubeParamsOfTube first).b - (tubeParamsOfTube second).b| ≤ radius ∧
      |(tubeParamsOfTube first).c - (tubeParamsOfTube second).c| ≤
        6 * radius ∧
      |(tubeParamsOfTube first).d - (tubeParamsOfTube second).d| ≤
        6 * radius := by
  let firstZero := wz1TubeAxisZeroPoint first
  let secondZero := wz1TubeAxisZeroPoint second
  let firstDirection := wz1PaperDirection first
  let secondDirection := wz1PaperDirection second
  have hzero : dist firstZero secondZero ≤ radius := by
    dsimp only [wz1PaperLineDistance] at hdistance
    linarith [InnerProductGeometry.angle_nonneg firstDirection secondDirection]
  have hangle : InnerProductGeometry.angle firstDirection secondDirection ≤ radius := by
    dsimp only [wz1PaperLineDistance] at hdistance
    linarith [dist_nonneg (x := firstZero) (y := secondZero)]
  have hdirection : ‖firstDirection - secondDirection‖ ≤ radius :=
    (unit_norm_sub_le_angle
      (wz1PaperDirection_norm first)
      (wz1PaperDirection_norm second)).trans hangle
  have hcoordinate : ∀ coordinate : Fin 3,
      |firstDirection coordinate - secondDirection coordinate| ≤ radius := by
    intro coordinate
    exact (PiLp.norm_apply_le (firstDirection - secondDirection) coordinate).trans
      hdirection
  have hzeroCoordinate : ∀ coordinate : Fin 3,
      |firstZero coordinate - secondZero coordinate| ≤ radius := by
    intro coordinate
    have h := PiLp.dist_apply_le firstZero secondZero coordinate
    simpa [Real.dist_eq] using h.trans hzero
  have hfirstVertical : 1 / 2 ≤ firstDirection 2 := hfirst.1
  have hsecondVertical : 1 / 2 ≤ secondDirection 2 := hsecond.1
  have hfirstVerticalPos : 0 < firstDirection 2 := by linarith
  have hsecondVerticalPos : 0 < secondDirection 2 := by linarith
  have hsecondHorizontal : ∀ coordinate : Fin 2,
      |secondDirection coordinate.castSucc| ≤ 1 := by
    intro coordinate
    have h := PiLp.norm_apply_le secondDirection coordinate.castSucc
    rw [wz1PaperDirection_norm second] at h
    exact h
  have hslope : ∀ coordinate : Fin 2,
      |firstDirection coordinate.castSucc / firstDirection 2 -
        secondDirection coordinate.castSucc / secondDirection 2| ≤
          6 * radius := by
    intro coordinate
    have heq :
        firstDirection coordinate.castSucc / firstDirection 2 -
            secondDirection coordinate.castSucc / secondDirection 2 =
          (firstDirection coordinate.castSucc -
              secondDirection coordinate.castSucc) / firstDirection 2 +
            secondDirection coordinate.castSucc *
              (secondDirection 2 - firstDirection 2) /
                (firstDirection 2 * secondDirection 2) := by
      field_simp [hfirstVerticalPos.ne', hsecondVerticalPos.ne']
      ring
    rw [heq]
    have hfirstTerm :
        |firstDirection coordinate.castSucc -
              secondDirection coordinate.castSucc| / firstDirection 2 ≤
          2 * radius := by
      apply (div_le_iff₀ hfirstVerticalPos).2
      calc
        |firstDirection coordinate.castSucc -
              secondDirection coordinate.castSucc|
            ≤ radius := hcoordinate coordinate.castSucc
        _ ≤ 2 * radius * firstDirection 2 := by
          have hradius : 0 ≤ radius := by
            exact (InnerProductGeometry.angle_nonneg
              firstDirection secondDirection).trans hangle
          nlinarith
    have hsecondTerm :
        |secondDirection coordinate.castSucc| *
            |secondDirection 2 - firstDirection 2| /
              (firstDirection 2 * secondDirection 2) ≤
          4 * radius := by
      apply (div_le_iff₀ (mul_pos hfirstVerticalPos hsecondVerticalPos)).2
      have hhorizontal := hsecondHorizontal coordinate
      have hverticalDiff :
          |secondDirection 2 - firstDirection 2| ≤ radius := by
        simpa [abs_sub_comm] using hcoordinate (2 : Fin 3)
      have hproduct :
          |secondDirection coordinate.castSucc| *
              |secondDirection 2 - firstDirection 2| ≤ radius := by
        calc
          |secondDirection coordinate.castSucc| *
                |secondDirection 2 - firstDirection 2|
              ≤ 1 * |secondDirection 2 - firstDirection 2| := by gcongr
          _ ≤ radius := by simpa using hverticalDiff
      have hdenLower :
          (1 / 4 : ℝ) ≤ firstDirection 2 * secondDirection 2 := by
        nlinarith
      have hradius : 0 ≤ radius := by
        exact (InnerProductGeometry.angle_nonneg
          firstDirection secondDirection).trans hangle
      calc
        |secondDirection coordinate.castSucc| *
              |secondDirection 2 - firstDirection 2|
            ≤ radius := hproduct
        _ ≤ 4 * radius * (firstDirection 2 * secondDirection 2) := by
          nlinarith
    calc
      |(firstDirection coordinate.castSucc -
              secondDirection coordinate.castSucc) / firstDirection 2 +
          secondDirection coordinate.castSucc *
            (secondDirection 2 - firstDirection 2) /
              (firstDirection 2 * secondDirection 2)|
          ≤ |(firstDirection coordinate.castSucc -
              secondDirection coordinate.castSucc) / firstDirection 2| +
            |secondDirection coordinate.castSucc *
              (secondDirection 2 - firstDirection 2) /
                (firstDirection 2 * secondDirection 2)| := abs_add_le _ _
      _ = |firstDirection coordinate.castSucc -
              secondDirection coordinate.castSucc| / firstDirection 2 +
            |secondDirection coordinate.castSucc| *
              |secondDirection 2 - firstDirection 2| /
                (firstDirection 2 * secondDirection 2) := by
          rw [abs_div, abs_div, abs_mul,
            abs_of_pos hfirstVerticalPos,
            abs_of_pos (mul_pos hfirstVerticalPos hsecondVerticalPos)]
      _ ≤ 2 * radius + 4 * radius := add_le_add hfirstTerm hsecondTerm
      _ = 6 * radius := by ring
  have hfirstParams :=
    tubeParamsOfTube_eq_paper_zero_and_direction_ratio first hfirst
  have hsecondParams :=
    tubeParamsOfTube_eq_paper_zero_and_direction_ratio second hsecond
  rw [hfirstParams.1, hsecondParams.1, hfirstParams.2.1,
    hsecondParams.2.1, hfirstParams.2.2.1, hsecondParams.2.2.1,
    hfirstParams.2.2.2, hsecondParams.2.2.2]
  exact ⟨hzeroCoordinate 0, hzeroCoordinate 1, hslope 0, hslope 1⟩

/-- One directed centered containment pulls back to a source parameter
cluster in the same direction. -/
private theorem source_parameter_cluster_of_affine_centered_containment
    {sourceDelta targetDelta : ℝ}
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hframe : |frameSlope| ≤ 1)
    (hanchor : |center 2| ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (hheight : 0 < heightScale)
    (htransverse : 0 < transverseScale)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (targetFamily : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceParent : Fin targetFamily.card → Fin sourceFamily.card)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (htargetLine : WZ1PaperIsLineClass targetFamily)
    (htargetLocal : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFamily.tube target)‖ ≤ 3)
    (haxis : ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale 1 ''
            tubeAxisLine (sourceFamily.tube (sourceParent target)))
    (hsourceVertical : ∀ source,
      (sourceFamily.tube source).direction (2 : Fin 3) ≠ 0)
    (htargetVertical : ∀ target,
      (targetFamily.tube target).direction (2 : Fin 3) ≠ 0)
    (reference other : Fin targetFamily.card)
    (hcontain : (targetFamily.tube reference).carrier ⊆
      wz2PaperCenteredDilatedCarrier 2 (targetFamily.tube other)) :
    let width := 16 * (1 + heightScale) *
      (1 + transverseScale⁻¹) * (600 * targetDelta)
    |(tubeParams (F := sourceFamily) (sourceParent reference)).a -
        (tubeParams (F := sourceFamily) (sourceParent other)).a| ≤ width ∧
      |(tubeParams (F := sourceFamily) (sourceParent reference)).b -
        (tubeParams (F := sourceFamily) (sourceParent other)).b| ≤ width ∧
      |(tubeParams (F := sourceFamily) (sourceParent reference)).c -
        (tubeParams (F := sourceFamily) (sourceParent other)).c| ≤ width ∧
      |(tubeParams (F := sourceFamily) (sourceParent reference)).d -
        (tubeParams (F := sourceFamily) (sourceParent other)).d| ≤ width := by
  dsimp only
  have hlineDistance :=
      wz2_paper_localized_centered_doubled_containment_lineDistance_le
        htargetDelta htargetDelta
        (htargetLine reference) (htargetLine other)
        (htargetLocal reference) hcontain
  have htargetCluster := tubeParamsOfTube_cluster_of_paperLineDistance
      (htargetLine reference) (htargetLine other) hlineDistance
  have htargetBound :
        |(tubeParamsOfTube (targetFamily.tube reference)).a -
            (tubeParamsOfTube (targetFamily.tube other)).a| ≤
              600 * targetDelta ∧
          |(tubeParamsOfTube (targetFamily.tube reference)).b -
            (tubeParamsOfTube (targetFamily.tube other)).b| ≤
              600 * targetDelta ∧
          |(tubeParamsOfTube (targetFamily.tube reference)).c -
            (tubeParamsOfTube (targetFamily.tube other)).c| ≤
              600 * targetDelta ∧
          |(tubeParamsOfTube (targetFamily.tube reference)).d -
            (tubeParamsOfTube (targetFamily.tube other)).d| ≤
              600 * targetDelta := by
    dsimp only [wz2PaperLocalizedDoubledFiberLineDistanceConstant] at htargetCluster
    exact ⟨htargetCluster.1.trans (by nlinarith),
      htargetCluster.2.1.trans (by nlinarith),
      by convert htargetCluster.2.2.1 using 1 <;> ring,
      by convert htargetCluster.2.2.2 using 1 <;> ring⟩
  rw [tubeParamsOfTube_eq_pureWZ2AffineDiagonalCentered_of_axis_image
      frameSlope center heightScale transverseScale hheight.ne'
      htransverse.ne'
      (sourceFamily.tube (sourceParent reference))
      (hsourceVertical _) (targetFamily.tube reference)
      (htargetVertical _) (haxis reference),
      tubeParamsOfTube_eq_pureWZ2AffineDiagonalCentered_of_axis_image
      frameSlope center heightScale transverseScale hheight.ne'
      htransverse.ne'
      (sourceFamily.tube (sourceParent other))
      (hsourceVertical _) (targetFamily.tube other)
    (htargetVertical _) (haxis other)] at htargetBound
  have hdiff := pureWZ2AffineDiagonalCenteredTubeParams_sub_eq
    frameSlope center heightScale transverseScale
    (tubeParamsOfTube (sourceFamily.tube (sourceParent reference)))
    (tubeParamsOfTube (sourceFamily.tube (sourceParent other)))
  have htargetAnchored :
      |(pureWZ2AffineDiagonalTubeParams frameSlope (center 2) heightScale
            transverseScale
            (tubeParamsOfTube (sourceFamily.tube (sourceParent reference)))).a -
          (pureWZ2AffineDiagonalTubeParams frameSlope (center 2) heightScale
            transverseScale
            (tubeParamsOfTube (sourceFamily.tube (sourceParent other)))).a| ≤
            600 * targetDelta ∧
        |(pureWZ2AffineDiagonalTubeParams frameSlope (center 2) heightScale
            transverseScale
            (tubeParamsOfTube (sourceFamily.tube (sourceParent reference)))).b -
          (pureWZ2AffineDiagonalTubeParams frameSlope (center 2) heightScale
            transverseScale
            (tubeParamsOfTube (sourceFamily.tube (sourceParent other)))).b| ≤
            600 * targetDelta ∧
        |(pureWZ2AffineDiagonalTubeParams frameSlope (center 2) heightScale
            transverseScale
            (tubeParamsOfTube (sourceFamily.tube (sourceParent reference)))).c -
          (pureWZ2AffineDiagonalTubeParams frameSlope (center 2) heightScale
            transverseScale
            (tubeParamsOfTube (sourceFamily.tube (sourceParent other)))).c| ≤
            600 * targetDelta ∧
        |(pureWZ2AffineDiagonalTubeParams frameSlope (center 2) heightScale
            transverseScale
            (tubeParamsOfTube (sourceFamily.tube (sourceParent reference)))).d -
          (pureWZ2AffineDiagonalTubeParams frameSlope (center 2) heightScale
            transverseScale
            (tubeParamsOfTube (sourceFamily.tube (sourceParent other)))).d| ≤
            600 * targetDelta := by
    exact ⟨by rw [← hdiff.1]; exact htargetBound.1,
      by rw [← hdiff.2.1]; exact htargetBound.2.1,
      by rw [← hdiff.2.2.1]; exact htargetBound.2.2.1,
      by rw [← hdiff.2.2.2]; exact htargetBound.2.2.2⟩
  have hinverse := pureWZ2AffineDiagonalTubeParams_inverse_cluster
      frameSlope (center 2) heightScale transverseScale
      (600 * targetDelta) hframe hanchor hheight htransverse
      (by positivity) _ _ htargetAnchored.1 htargetAnchored.2.1
      htargetAnchored.2.2.1 htargetAnchored.2.2.2
  simpa only [tubeParams] using hinverse

/-- One public centered conflict pulls back to a source parameter cluster. -/
theorem source_parameter_cluster_of_affine_centered_conflict
    {sourceDelta targetDelta : ℝ}
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hframe : |frameSlope| ≤ 1)
    (hanchor : |center 2| ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (hheight : 0 < heightScale)
    (htransverse : 0 < transverseScale)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (targetFamily : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceParent : Fin targetFamily.card → Fin sourceFamily.card)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (htargetLine : WZ1PaperIsLineClass targetFamily)
    (htargetLocal : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFamily.tube target)‖ ≤ 3)
    (haxis : ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale 1 ''
            tubeAxisLine (sourceFamily.tube (sourceParent target)))
    (hsourceVertical : ∀ source,
      (sourceFamily.tube source).direction (2 : Fin 3) ≠ 0)
    (htargetVertical : ∀ target,
      (targetFamily.tube target).direction (2 : Fin 3) ≠ 0)
    (reference other : Fin targetFamily.card)
    (hconflict : pureWZ2PaperCenteredConflict
      targetFamily reference other) :
    let width := 16 * (1 + heightScale) *
      (1 + transverseScale⁻¹) * (600 * targetDelta)
    |(tubeParams (F := sourceFamily) (sourceParent reference)).a -
        (tubeParams (F := sourceFamily) (sourceParent other)).a| ≤ width ∧
      |(tubeParams (F := sourceFamily) (sourceParent reference)).b -
        (tubeParams (F := sourceFamily) (sourceParent other)).b| ≤ width ∧
      |(tubeParams (F := sourceFamily) (sourceParent reference)).c -
        (tubeParams (F := sourceFamily) (sourceParent other)).c| ≤ width ∧
      |(tubeParams (F := sourceFamily) (sourceParent reference)).d -
        (tubeParams (F := sourceFamily) (sourceParent other)).d| ≤ width := by
  dsimp only
  rcases hconflict with ⟨hne, hcontain | hcontain⟩
  · exact source_parameter_cluster_of_affine_centered_containment
      frameSlope center heightScale transverseScale hframe hanchor
      htargetDelta hheight htransverse sourceFamily targetFamily
      sourceParent hsourceLine htargetLine htargetLocal haxis
      hsourceVertical htargetVertical reference other hcontain
  · have hresult := source_parameter_cluster_of_affine_centered_containment
      frameSlope center heightScale transverseScale hframe hanchor
      htargetDelta hheight htransverse sourceFamily targetFamily sourceParent
      hsourceLine htargetLine htargetLocal haxis hsourceVertical
      htargetVertical other reference hcontain
    exact ⟨by simpa [abs_sub_comm] using hresult.1,
      by simpa [abs_sub_comm] using hresult.2.1,
      by simpa [abs_sub_comm] using hresult.2.2.1,
      by simpa [abs_sub_comm] using hresult.2.2.2⟩

/--
Source parameter Frostman control and a finite source-parent fiber cap bound
the public centered-conflict degree of the target family.
-/
theorem affine_centered_conflict_degree_le
    {sourceDelta targetDelta : ℝ}
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hframe : |frameSlope| ≤ 1)
    (hanchor : |center 2| ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (hheight : 0 < heightScale)
    (htransverse : 0 < transverseScale)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (targetFamily : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceParent : Fin targetFamily.card → Fin sourceFamily.card)
    (fiberCap : ℕ)
    (hfiber : ∀ source,
      ((Finset.univ : Finset (Fin targetFamily.card)).filter fun target =>
        sourceParent target = source).card ≤ fiberCap)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (htargetLine : WZ1PaperIsLineClass targetFamily)
    (htargetLocal : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFamily.tube target)‖ ≤ 3)
    (haxis : ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale 1 ''
            tubeAxisLine (sourceFamily.tube (sourceParent target)))
    (hsourceVertical : ∀ source,
      (sourceFamily.tube source).direction (2 : Fin 3) ≠ 0)
    (htargetVertical : ∀ target,
      (targetFamily.tube target).direction (2 : Fin 3) ≠ 0)
    (sourceConstant normalization : ENNReal)
    (hFrostman : ∀ r : ℝ, sourceDelta ≤ r → r ≤ 1 →
      ∀ reference : Fin sourceFamily.card,
        (((Finset.univ : Finset (Fin sourceFamily.card)).filter fun source =>
          |(tubeParams (F := sourceFamily) source).a -
              (tubeParams (F := sourceFamily) reference).a| ≤ r ∧
          |(tubeParams (F := sourceFamily) source).b -
              (tubeParams (F := sourceFamily) reference).b| ≤ r ∧
          |(tubeParams (F := sourceFamily) source).c -
              (tubeParams (F := sourceFamily) reference).c| ≤ r ∧
          |(tubeParams (F := sourceFamily) source).d -
              (tubeParams (F := sourceFamily) reference).d| ≤ r).card :
            ENNReal) ≤
          sourceConstant * Kakeya.realRpowENN r 2 * normalization)
    (width : ℝ)
    (hwidth : width = 16 * (1 + heightScale) *
      (1 + transverseScale⁻¹) * (600 * targetDelta))
    (hsourceWidth : sourceDelta ≤ width)
    (hwidthOne : width ≤ 1) :
    ∀ reference : Fin targetFamily.card,
      (((Finset.univ : Finset (Fin targetFamily.card)).filter
        (pureWZ2PaperCenteredConflict targetFamily reference)).card :
          ENNReal) ≤
        (fiberCap : ENNReal) *
          (sourceConstant * Kakeya.realRpowENN width 2 *
            normalization) := by
  intro reference
  let conflicts : Finset (Fin targetFamily.card) :=
    (Finset.univ : Finset (Fin targetFamily.card)).filter
      (pureWZ2PaperCenteredConflict targetFamily reference)
  let sourceConflicts : Finset (Fin sourceFamily.card) :=
    conflicts.image sourceParent
  let sourceCluster : Finset (Fin sourceFamily.card) :=
    (Finset.univ : Finset (Fin sourceFamily.card)).filter fun source =>
      |(tubeParams source).a -
          (tubeParams (sourceParent reference)).a| ≤ width ∧
      |(tubeParams source).b -
          (tubeParams (sourceParent reference)).b| ≤ width ∧
      |(tubeParams source).c -
          (tubeParams (sourceParent reference)).c| ≤ width ∧
      |(tubeParams source).d -
          (tubeParams (sourceParent reference)).d| ≤ width
  have hsourceSubset : sourceConflicts ⊆ sourceCluster := by
    intro source hsource
    rcases Finset.mem_image.mp hsource with ⟨target, htarget, rfl⟩
    have hconflict := (Finset.mem_filter.mp htarget).2
    have hcluster := source_parameter_cluster_of_affine_centered_conflict
      frameSlope center heightScale transverseScale hframe hanchor
      htargetDelta hheight htransverse sourceFamily targetFamily
      sourceParent hsourceLine htargetLine htargetLocal haxis
      hsourceVertical htargetVertical reference target hconflict
    have hcluster' :
        |(tubeParams (F := sourceFamily) (sourceParent target)).a -
            (tubeParams (F := sourceFamily) (sourceParent reference)).a| ≤ width ∧
          |(tubeParams (F := sourceFamily) (sourceParent target)).b -
            (tubeParams (F := sourceFamily) (sourceParent reference)).b| ≤ width ∧
          |(tubeParams (F := sourceFamily) (sourceParent target)).c -
            (tubeParams (F := sourceFamily) (sourceParent reference)).c| ≤ width ∧
          |(tubeParams (F := sourceFamily) (sourceParent target)).d -
            (tubeParams (F := sourceFamily) (sourceParent reference)).d| ≤ width := by
      rw [hwidth]
      exact ⟨by simpa [abs_sub_comm] using hcluster.1,
        by simpa [abs_sub_comm] using hcluster.2.1,
        by simpa [abs_sub_comm] using hcluster.2.2.1,
        by simpa [abs_sub_comm] using hcluster.2.2.2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcluster'⟩
  have hsourceCard :
      (sourceConflicts.card : ENNReal) ≤
        sourceConstant * Kakeya.realRpowENN width 2 *
          normalization := by
    calc
      (sourceConflicts.card : ENNReal) ≤
          (sourceCluster.card : ENNReal) := by
        exact_mod_cast Finset.card_le_card hsourceSubset
      _ ≤ sourceConstant * Kakeya.realRpowENN width 2 *
          normalization := by
        simpa [TubeParameterFrostmanBound, sourceCluster] using
          hFrostman width hsourceWidth hwidthOne
            (sourceParent reference)
  have htargetCard : conflicts.card ≤ fiberCap * sourceConflicts.card := by
    let targetFiber : Fin sourceFamily.card →
        Finset (Fin targetFamily.card) := fun source =>
      conflicts.filter fun target => sourceParent target = source
    have hunion : conflicts = sourceConflicts.biUnion targetFiber := by
      ext target
      constructor
      · intro htarget
        exact Finset.mem_biUnion.mpr
          ⟨sourceParent target, Finset.mem_image.mpr
            ⟨target, htarget, rfl⟩,
            Finset.mem_filter.mpr ⟨htarget, rfl⟩⟩
      · intro htarget
        rcases Finset.mem_biUnion.mp htarget with
          ⟨_source, _hsource, htargetFiber⟩
        exact (Finset.mem_filter.mp htargetFiber).1
    have hfiberCard : ∀ source ∈ sourceConflicts,
        (targetFiber source).card ≤ fiberCap := by
      intro source _
      calc
        (targetFiber source).card ≤
            ((Finset.univ : Finset (Fin targetFamily.card)).filter
              fun target => sourceParent target = source).card := by
          apply Finset.card_le_card
          intro target htarget
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp htarget).2⟩
        _ ≤ fiberCap := hfiber source
    rw [hunion]
    calc
      (sourceConflicts.biUnion targetFiber).card ≤
          ∑ source ∈ sourceConflicts, (targetFiber source).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _source ∈ sourceConflicts, fiberCap := by
        exact Finset.sum_le_sum hfiberCard
      _ = fiberCap * sourceConflicts.card := by
        simp [Finset.sum_const, Nat.mul_comm]
  have htargetCardENN :
      (conflicts.card : ENNReal) ≤
        (fiberCap : ENNReal) * (sourceConflicts.card : ENNReal) := by
    exact_mod_cast htargetCard
  exact htargetCardENN.trans (by gcongr)

end Kakeya.Assouad
