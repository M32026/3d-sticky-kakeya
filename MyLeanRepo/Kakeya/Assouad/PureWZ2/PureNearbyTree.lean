import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureNearbyTreeGeometryCore

/-!
# Pure nearby-scale full-fiber tree

Independently selected Definition 2.12 covers at sufficiently separated
scales form a nested tree.  The proof uses only ordinary carrier containment
and centered doubled-fiber disjointness.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/--
If one fine tube lies in ordinary parents at two sufficiently separated
scales, the smaller parent lies in the centered double of the larger parent.
-/
lemma wz2_pure_tree_geometric_step
    {delta fineScale coarseScale : ℝ}
    {source : Kakeya.DeltaTube delta}
    {fineParent : Kakeya.DeltaTube fineScale}
    {coarseParent : Kakeya.DeltaTube coarseScale}
    (hdelta : 0 ≤ delta)
    (hfineScale : 0 < fineScale)
    (hcoarseScale : 0 < coarseScale)
    (hdeltaFine : delta ≤ fineScale)
    (hdeltaCoarse : delta ≤ coarseScale)
    (hseparation :
      4 * (fineScale - delta) ≤ coarseScale)
    (hsourceFine :
      source.carrier ⊆ fineParent.carrier)
    (hsourceCoarse :
      source.carrier ⊆ coarseParent.carrier) :
    fineParent.carrier ⊆
      wz2PaperCenteredDilatedCarrier 2 coarseParent := by
  let sourceSegment :=
    Kakeya.unitSegment source.base source.direction
  let fineSegment :=
    Kakeya.unitSegment fineParent.base fineParent.direction
  let coarseSegment :=
    Kakeya.unitSegment coarseParent.base coarseParent.direction
  have fineSegmentEq :
      fineSegment =
        segment ℝ fineParent.base
          (fineParent.base + fineParent.direction) := by
    unfold fineSegment Kakeya.unitSegment
    rw [segment_eq_image]
    congr with parameter
    simp [add_smul, sub_smul]
    abel
  have coarseSegmentEq :
      coarseSegment =
        segment ℝ coarseParent.base
          (coarseParent.base + coarseParent.direction) := by
    unfold coarseSegment Kakeya.unitSegment
    rw [segment_eq_image]
    congr with parameter
    simp [add_smul, sub_smul]
    abel
  have sourceSegmentEq :
      sourceSegment =
        segment ℝ source.base
          (source.base + source.direction) := by
    unfold sourceSegment Kakeya.unitSegment
    rw [segment_eq_image]
    congr with parameter
    simp [add_smul, sub_smul]
    abel
  have fineCompact : IsCompact fineSegment := by
    rw [fineSegmentEq, segment_eq_image]
    have hcontinuous :
        Continuous
          (fun parameter : ℝ =>
            (1 - parameter) • fineParent.base +
              parameter •
                (fineParent.base + fineParent.direction)) := by
      continuity
    exact
      (show IsCompact (Set.Icc (0 : ℝ) 1) from
          isCompact_Icc).image hcontinuous
  have coarseCompact : IsCompact coarseSegment := by
    rw [coarseSegmentEq, segment_eq_image]
    have hcontinuous :
        Continuous
          (fun parameter : ℝ =>
            (1 - parameter) • coarseParent.base +
              parameter •
                (coarseParent.base + coarseParent.direction)) := by
      continuity
    exact
      (show IsCompact (Set.Icc (0 : ℝ) 1) from
          isCompact_Icc).image hcontinuous
  have sourceCompact : IsCompact sourceSegment := by
    rw [sourceSegmentEq, segment_eq_image]
    have hcontinuous :
        Continuous
          (fun parameter : ℝ =>
            (1 - parameter) • source.base +
              parameter •
                (source.base + source.direction)) := by
      continuity
    exact
      (show IsCompact (Set.Icc (0 : ℝ) 1) from
          isCompact_Icc).image hcontinuous
  have fineNonempty : fineSegment.Nonempty := by
    rw [fineSegmentEq, segment_eq_image]
    exact ⟨fineParent.base, 0, by norm_num, by simp⟩
  have coarseNonempty : coarseSegment.Nonempty := by
    rw [coarseSegmentEq, segment_eq_image]
    exact ⟨coarseParent.base, 0, by norm_num, by simp⟩
  have sourceNonempty : sourceSegment.Nonempty := by
    rw [sourceSegmentEq, segment_eq_image]
    exact ⟨source.base, 0, by norm_num, by simp⟩
  have coarseConvex : Convex ℝ coarseSegment := by
    rw [coarseSegmentEq]
    exact convex_segment _ _
  have forwardFine :
      ∀ point ∈ sourceSegment,
        infDist point fineSegment ≤ fineScale - delta :=
    wz2_pure_segment_hausdorff_from_containment
      hdelta hfineScale.le hdeltaFine hsourceFine
  have reverseFine :
      ∀ point ∈ fineSegment,
        infDist point sourceSegment ≤
          3 * (fineScale - delta) :=
    wz2_pure_unit_segment_reverse_hausdorff
      (fineScale - delta)
      source.direction_unit fineParent.direction_unit
      (by linarith) forwardFine
  have forwardCoarse :
      ∀ point ∈ sourceSegment,
        infDist point coarseSegment ≤ coarseScale - delta :=
    wz2_pure_segment_hausdorff_from_containment
      hdelta hcoarseScale.le hdeltaCoarse hsourceCoarse
  intro point hpoint
  have pointInf :
      infEDist point fineSegment ≤
        ENNReal.ofReal fineScale := by
    simpa [Kakeya.DeltaTube.carrier,
      Metric.mem_cthickening_iff] using hpoint
  rcases
      fineCompact.exists_infEDist_eq_edist
        fineNonempty point with
    ⟨fineAxisPoint, hfineAxisPoint, hfineAxisEq⟩
  have pointFineDistance :
      dist point fineAxisPoint ≤ fineScale := by
    have hedistance :
        edist point fineAxisPoint ≤
          ENNReal.ofReal fineScale := by
      rw [← hfineAxisEq]
      exact pointInf
    have hofReal :
        ENNReal.ofReal (dist point fineAxisPoint) ≤
          ENNReal.ofReal fineScale := by
      simpa [edist_dist] using hedistance
    exact
      (ENNReal.ofReal_le_ofReal_iff
        (by positivity)).mp hofReal
  have fineSourceInf :
      infDist fineAxisPoint sourceSegment ≤
        3 * (fineScale - delta) :=
    reverseFine fineAxisPoint hfineAxisPoint
  have fineSourceEDist :
      infEDist fineAxisPoint sourceSegment ≤
        ENNReal.ofReal (3 * (fineScale - delta)) := by
    have hfinite :
        infEDist fineAxisPoint sourceSegment ≠ ⊤ :=
      Metric.infEDist_ne_top sourceNonempty
    have heq :
        infEDist fineAxisPoint sourceSegment =
          ENNReal.ofReal
            (infDist fineAxisPoint sourceSegment) := by
      have htoReal :
          (infEDist fineAxisPoint sourceSegment).toReal =
            infDist fineAxisPoint sourceSegment := by
        rfl
      rw [← htoReal, ENNReal.ofReal_toReal hfinite]
    rw [heq]
    exact ENNReal.ofReal_le_ofReal fineSourceInf
  rcases
      sourceCompact.exists_infEDist_eq_edist
        sourceNonempty fineAxisPoint with
    ⟨sourceAxisPoint, hsourceAxisPoint, hsourceAxisEq⟩
  have fineSourceDistance :
      dist fineAxisPoint sourceAxisPoint ≤
        3 * (fineScale - delta) := by
    have hedistance :
        edist fineAxisPoint sourceAxisPoint ≤
          ENNReal.ofReal (3 * (fineScale - delta)) := by
      rw [← hsourceAxisEq]
      exact fineSourceEDist
    have hofReal :
        ENNReal.ofReal
            (dist fineAxisPoint sourceAxisPoint) ≤
          ENNReal.ofReal (3 * (fineScale - delta)) := by
      simpa [edist_dist] using hedistance
    exact
      (ENNReal.ofReal_le_ofReal_iff
        (by positivity)).mp hofReal
  have sourceCoarseInf :
      infDist sourceAxisPoint coarseSegment ≤
        coarseScale - delta :=
    forwardCoarse sourceAxisPoint hsourceAxisPoint
  have sourceCoarseEDist :
      infEDist sourceAxisPoint coarseSegment ≤
        ENNReal.ofReal (coarseScale - delta) := by
    have hfinite :
        infEDist sourceAxisPoint coarseSegment ≠ ⊤ :=
      Metric.infEDist_ne_top coarseNonempty
    have heq :
        infEDist sourceAxisPoint coarseSegment =
          ENNReal.ofReal
            (infDist sourceAxisPoint coarseSegment) := by
      have htoReal :
          (infEDist sourceAxisPoint coarseSegment).toReal =
            infDist sourceAxisPoint coarseSegment := by
        rfl
      rw [← htoReal, ENNReal.ofReal_toReal hfinite]
    rw [heq]
    exact ENNReal.ofReal_le_ofReal sourceCoarseInf
  rcases
      coarseCompact.exists_infEDist_eq_edist
        coarseNonempty sourceAxisPoint with
    ⟨coarseAxisPoint, hcoarseAxisPoint, hcoarseAxisEq⟩
  have sourceCoarseDistance :
      dist sourceAxisPoint coarseAxisPoint ≤
        coarseScale - delta := by
    have hedistance :
        edist sourceAxisPoint coarseAxisPoint ≤
          ENNReal.ofReal (coarseScale - delta) := by
      rw [← hcoarseAxisEq]
      exact sourceCoarseEDist
    have hofReal :
        ENNReal.ofReal
            (dist sourceAxisPoint coarseAxisPoint) ≤
          ENNReal.ofReal (coarseScale - delta) := by
      simpa [edist_dist] using hedistance
    exact
      (ENNReal.ofReal_le_ofReal_iff
        (by positivity)).mp hofReal
  have pointCoarseDistance :
      dist point coarseAxisPoint ≤
        4 * fineScale + coarseScale - 4 * delta := by
    have hfirst :
        dist point coarseAxisPoint ≤
          dist point fineAxisPoint +
            dist fineAxisPoint coarseAxisPoint :=
      dist_triangle _ _ _
    have hsecond :
        dist fineAxisPoint coarseAxisPoint ≤
          dist fineAxisPoint sourceAxisPoint +
            dist sourceAxisPoint coarseAxisPoint :=
      dist_triangle _ _ _
    linarith
  let midpoint := wz2PaperTubeMidpoint coarseParent
  have midpointMem : midpoint ∈ coarseSegment := by
    rw [coarseSegmentEq, segment_eq_image]
    refine ⟨1 / 2, by norm_num, ?_⟩
    simp [midpoint, wz2PaperTubeMidpoint,
      sub_smul, add_smul]
    abel
  let halfPoint :=
    midpoint + (1 / 2 : ℝ) • (point - midpoint)
  let halfAxisPoint :=
    midpoint +
      (1 / 2 : ℝ) • (coarseAxisPoint - midpoint)
  have halfAxisPointMem :
      halfAxisPoint ∈ coarseSegment := by
    have heq :
        halfAxisPoint =
          (1 - (1 / 2 : ℝ)) • midpoint +
            (1 / 2 : ℝ) • coarseAxisPoint := by
      dsimp only [halfAxisPoint]
      rw [smul_sub]
      simp [sub_smul, add_smul]
      abel
    rw [heq]
    exact coarseConvex midpointMem hcoarseAxisPoint
      (by norm_num) (by norm_num) (by norm_num)
  have halfDistance :
      dist halfPoint halfAxisPoint =
        (1 / 2 : ℝ) * dist point coarseAxisPoint := by
    have heq :
        halfPoint - halfAxisPoint =
          (1 / 2 : ℝ) •
            (point - coarseAxisPoint) := by
      simp [halfPoint, halfAxisPoint, sub_smul,
        smul_sub]
    rw [dist_eq_norm, heq, norm_smul,
      Real.norm_eq_abs, abs_of_pos
        (by norm_num : (0 : ℝ) < 1 / 2),
      dist_eq_norm]
  have halfDistanceBound :
      dist halfPoint halfAxisPoint ≤ coarseScale := by
    rw [halfDistance]
    have hmul :
        (1 / 2 : ℝ) * dist point coarseAxisPoint ≤
          (1 / 2 : ℝ) *
            (4 * fineScale + coarseScale - 4 * delta) :=
      mul_le_mul_of_nonneg_left pointCoarseDistance
        (by norm_num)
    linarith
  have halfPointCarrier :
      halfPoint ∈ coarseParent.carrier := by
    exact
      Metric.mem_cthickening_of_dist_le
        halfPoint halfAxisPoint coarseScale
        coarseSegment halfAxisPointMem halfDistanceBound
  refine ⟨halfPoint, halfPointCarrier, ?_⟩
  simp [midpoint, halfPoint,
    AffineMap.homothety_apply, smul_smul]

/--
Pure Definition 2.12 parent maps at geometrically separated scales are
nested.
-/
theorem WZ2PaperPurePartitioningCover.parent_maps_nested_of_gap
    {delta fineScale coarseScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineCoarse :
      Kakeya.Streamlined.TubeFamily fineScale}
    {coarseCoarse :
      Kakeya.Streamlined.TubeFamily coarseScale}
    (fineCover :
      WZ2PaperPurePartitioningCover fine fineCoarse)
    (coarseCover :
      WZ2PaperPurePartitioningCover fine coarseCoarse)
    (hdelta : 0 ≤ delta)
    (hfineScale : 0 < fineScale)
    (hcoarseScale : 0 < coarseScale)
    (hdeltaFine : delta ≤ fineScale)
    (hdeltaCoarse : delta ≤ coarseScale)
    (hseparation :
      4 * (fineScale - delta) ≤ coarseScale) :
    ∀ first second : Fin fine.card,
      fineCover.parent first =
          fineCover.parent second →
        coarseCover.parent first =
          coarseCover.parent second := by
  intro first second hfineParent
  let fineParent := fineCover.parent first
  let coarseParent := coarseCover.parent first
  have hfirstFine :
      first ∈
        wz2PaperOrdinaryFullFiberIndices
          fine fineCoarse fineParent :=
    fineCover.parent_mem_fullFiber first
  have hfirstCoarse :
      first ∈
        wz2PaperOrdinaryFullFiberIndices
          fine coarseCoarse coarseParent :=
    coarseCover.parent_mem_fullFiber first
  have hsecondFine :
      second ∈
        wz2PaperOrdinaryFullFiberIndices
          fine fineCoarse fineParent := by
    apply
      (fineCover.mem_fullFiber_iff_parent_eq
        hfineScale.le fineParent second).mpr
    exact hfineParent.symm
  have hparentContainment :
      (fineCoarse.tube fineParent).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2
          (coarseCoarse.tube coarseParent) :=
    wz2_pure_tree_geometric_step
      hdelta hfineScale hcoarseScale
      hdeltaFine hdeltaCoarse hseparation
      ((mem_wz2PaperOrdinaryFullFiberIndices_iff
        fineParent first).mp hfirstFine)
      ((mem_wz2PaperOrdinaryFullFiberIndices_iff
        coarseParent first).mp hfirstCoarse)
  have hsecondInCoarseDouble :
      second ∈
        wz2PaperOrdinaryDilatedFiberIndices
          2 fine coarseCoarse coarseParent := by
    rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
    exact
      ((mem_wz2PaperOrdinaryFullFiberIndices_iff
        fineParent second).mp hsecondFine).trans
        hparentContainment
  let secondParent := coarseCover.parent second
  have hsecondOwn :
      second ∈
        wz2PaperOrdinaryFullFiberIndices
          fine coarseCoarse secondParent :=
    coarseCover.parent_mem_fullFiber second
  have hsecondOwnDouble :
      second ∈
        wz2PaperOrdinaryDilatedFiberIndices
          2 fine coarseCoarse secondParent :=
    WZ2PaperPurePartitioningCover.mem_doubledFiber_of_mem_fullFiber
      hcoarseScale.le hsecondOwn
  by_contra hne
  exact
    Finset.disjoint_left.mp
      (coarseCover.doubled_fibers_disjoint
        coarseParent secondParent hne)
      hsecondInCoarseDouble hsecondOwnDouble

end Kakeya.Assouad

end
