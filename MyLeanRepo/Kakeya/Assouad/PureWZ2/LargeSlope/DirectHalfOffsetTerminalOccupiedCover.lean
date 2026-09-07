import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalExactLocalAD

/-!
# Occupied finite source covers for direct half-offset terminals

The sharp ambient finite cover is pared down to precisely those source balls
which meet the genuine exact-terminal source set.  Choosing one occupied
source point in each retained ball gives both the source-ball containment
needed for source local AD and the target-ball containment needed for normal
recentering.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalGeometry

/-- The complete occupied finite-cover certificate at one exact terminal
anchor and radius. -/
structure ExactLocalOccupiedCoverData
    (terminal : commonSource.TerminalGeometry)
    (anchor0 : {point : Point3 // point ∈ terminal.exactShading.union})
    (radius : ℝ) where
  centers : Finset Point3
  card_le : (centers.card : ℝ) ≤ 9 *
    (commonSource.halfOffsetAssembly.horizontalSource.m *
      (commonSource.halfOffsetAssembly.horizontalSource.d -
        commonSource.halfOffsetAssembly.horizontalSource.c) / 2)⁻¹
  sourcePieces : Point3 → Set Point3
  sourceAnchor : Point3 → {point : Point3 // point ∈
    exactTerminalSourceSet commonSource terminal}
  cover : exactLocalSet commonSource terminal anchor0 radius ⊆
    ⋃ center ∈ centers,
      totalAffineMap commonSource terminal '' sourcePieces center
  source_subset : ∀ center ∈ centers, sourcePieces center ⊆
    exactTerminalSourceSet commonSource terminal
  anchor_ball : ∀ center ∈ centers,
    totalAffineMap commonSource terminal (sourceAnchor center : Point3) ∈
      Metric.closedBall (anchor0 : Point3) radius
  image_ball : ∀ center ∈ centers,
    totalAffineMap commonSource terminal '' sourcePieces center ⊆
      Metric.closedBall
        (totalAffineMap commonSource terminal (sourceAnchor center : Point3))
        (2 * radius)
  source_ball : ∀ center ∈ centers, sourcePieces center ⊆
    Metric.closedBall (sourceAnchor center : Point3) (7 * radius / 2)

/-- A sharp finite preimage-ball cover can be restricted to its occupied
balls.  The retained source pieces have genuine exact-terminal source anchors,
cover the localized exact terminal after applying the total affine map.  Each
source piece lies in the ball of radius `7 * radius / 2` about its genuine
source anchor, while each target image lies in the ball of radius `2 * radius`
about the corresponding target anchor. -/
theorem exactLocalSet_finite_occupied_source_cover
    (terminal : commonSource.TerminalGeometry)
    (anchor0 : {point : Point3 // point ∈ terminal.exactShading.union})
    {radius : ℝ} (hradius : 0 < radius) :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    let b := source.m * (source.d - source.c) / 2
    ∃ centers : Finset Point3,
      (centers.card : ℝ) ≤ 9 * b⁻¹ ∧
      ∃ sourcePieces : Point3 → Set Point3,
        ∃ sourceAnchor : Point3 → {point : Point3 // point ∈
          exactTerminalSourceSet commonSource terminal},
          exactLocalSet commonSource terminal anchor0 radius ⊆
            ⋃ center ∈ centers,
              totalAffineMap commonSource terminal '' sourcePieces center ∧
          (∀ center ∈ centers, sourcePieces center ⊆
            exactTerminalSourceSet commonSource terminal) ∧
          (∀ center ∈ centers,
            totalAffineMap commonSource terminal
                (sourceAnchor center : Point3) ∈
              Metric.closedBall (anchor0 : Point3) radius) ∧
          (∀ center ∈ centers,
            totalAffineMap commonSource terminal '' sourcePieces center ⊆
              Metric.closedBall
                (totalAffineMap commonSource terminal
                  (sourceAnchor center : Point3)) (2 * radius)) ∧
          (∀ center ∈ centers,
            sourcePieces center ⊆
              Metric.closedBall (sourceAnchor center : Point3)
                (7 * radius / 2)) := by
  classical
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let exactSource := exactTerminalSourceSet commonSource terminal
  let ambientRadius := 7 * radius / 4
  obtain ⟨rawCenters, hrawCard, hrawCover⟩ :=
    totalAffineMap_exact_preimage_closedBall_sharp_finite_cover
      commonSource terminal anchor0 hradius
  let sourcePieces : Point3 → Set Point3 := fun center =>
    exactSource ∩
      (totalAffineMap commonSource terminal ⁻¹'
        Metric.closedBall (anchor0 : Point3) radius ∩
          Metric.closedBall center ambientRadius)
  let occupied : Finset Point3 := rawCenters.filter (fun center =>
    (sourcePieces center).Nonempty)
  let anchorSource : {point : Point3 // point ∈ exactSource} :=
    ⟨commonSource.halfOffsetTerminalSourcePoint terminal.retubing terminal.box
      pureWZ2DirectHalfOffsetTerminalLambda_pos
      (exactSetPoint commonSource terminal anchor0), by
        refine ⟨?_, ?_⟩
        · exact (commonSource.halfOffsetTerminalSourcePoint terminal.retubing
            terminal.box pureWZ2DirectHalfOffsetTerminalLambda_pos
            (exactSetPoint commonSource terminal anchor0)).property
        · change totalAffineMap commonSource terminal
              (commonSource.halfOffsetTerminalSourcePoint terminal.retubing terminal.box
                pureWZ2DirectHalfOffsetTerminalLambda_pos
                (exactSetPoint commonSource terminal anchor0)) ∈
              terminal.exactShading.union
          rw [totalAffineMap_halfOffsetTerminalSourcePoint commonSource
            terminal anchor0]
          exact anchor0.property⟩
  let sourceAnchor : Point3 → {point : Point3 // point ∈ exactSource} :=
    fun center => if hoccupied : (sourcePieces center).Nonempty then
      ⟨Classical.choose hoccupied, (Classical.choose_spec hoccupied).1⟩
    else anchorSource
  refine ⟨occupied, ?_, sourcePieces, sourceAnchor, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (by exact_mod_cast Finset.card_filter_le _ _) hrawCard
  · intro target htarget
    unfold exactLocalSet at htarget
    rw [exactShading_union_inter_closedBall_eq_totalAffineMap_image
      commonSource terminal (anchor0 : Point3) radius] at htarget
    rcases htarget with ⟨sourcePoint, ⟨hsourcePoint, hpointBall⟩, rfl⟩
    rcases Set.mem_iUnion.mp (hrawCover hpointBall) with ⟨center, hcenter⟩
    rcases Set.mem_iUnion.mp hcenter with ⟨hcenterRaw, hsourceBall⟩
    have hoccupied : (sourcePieces center).Nonempty :=
      ⟨sourcePoint, ⟨hsourcePoint, hpointBall, hsourceBall⟩⟩
    have hcenterOccupied : center ∈ occupied := by
      simp only [occupied, Finset.mem_filter, hcenterRaw, true_and]
      exact hoccupied
    refine Set.mem_iUnion.2 ⟨center, Set.mem_iUnion.2 ⟨hcenterOccupied, ?_⟩⟩
    exact ⟨sourcePoint, ⟨hsourcePoint, hpointBall, hsourceBall⟩, rfl⟩
  · intro center _ sourcePoint hsourcePoint
    exact hsourcePoint.1
  · intro center hcenter
    have hoccupied : (sourcePieces center).Nonempty :=
      (Finset.mem_filter.mp hcenter).2
    dsimp only [sourceAnchor]
    rw [dif_pos hoccupied]
    exact (Classical.choose_spec hoccupied).2.1
  · intro center hcenter target htarget
    have hoccupied : (sourcePieces center).Nonempty :=
      (Finset.mem_filter.mp hcenter).2
    rw [Set.mem_image] at htarget
    rcases htarget with ⟨sourcePoint, hsourcePoint, rfl⟩
    have hsourceTargetBall : totalAffineMap commonSource terminal sourcePoint ∈
        Metric.closedBall (anchor0 : Point3) radius := hsourcePoint.2.1
    have hanchorTargetBall : totalAffineMap commonSource terminal
        (sourceAnchor center : Point3) ∈
        Metric.closedBall (anchor0 : Point3) radius := by
      dsimp only [sourceAnchor]
      rw [dif_pos hoccupied]
      exact (Classical.choose_spec hoccupied).2.1
    calc
      dist (totalAffineMap commonSource terminal sourcePoint)
          (totalAffineMap commonSource terminal (sourceAnchor center : Point3)) ≤
          radius + radius := by
            calc
              _ ≤ dist (totalAffineMap commonSource terminal sourcePoint)
                    (anchor0 : Point3) +
                  dist (anchor0 : Point3)
                    (totalAffineMap commonSource terminal (sourceAnchor center : Point3)) :=
                      dist_triangle _ _ _
              _ ≤ radius + radius := by
                rw [dist_comm (anchor0 : Point3)]
                exact add_le_add (Metric.mem_closedBall.mp hsourceTargetBall)
                  (Metric.mem_closedBall.mp hanchorTargetBall)
      _ = 2 * radius := by ring
  · intro center hcenter sourcePoint hsourcePoint
    have hoccupied : (sourcePieces center).Nonempty :=
      (Finset.mem_filter.mp hcenter).2
    have hsourceBall : sourcePoint ∈
        Metric.closedBall center ambientRadius := hsourcePoint.2.2
    have hanchorBall : (sourceAnchor center : Point3) ∈
        Metric.closedBall center ambientRadius := by
      dsimp only [sourceAnchor]
      rw [dif_pos hoccupied]
      exact (Classical.choose_spec hoccupied).2.2
    calc
      dist sourcePoint (sourceAnchor center : Point3) ≤
          dist sourcePoint center +
            dist center (sourceAnchor center : Point3) := dist_triangle _ _ _
      _ ≤ ambientRadius + ambientRadius := by
        rw [dist_comm center]
        exact add_le_add (Metric.mem_closedBall.mp hsourceBall)
          (Metric.mem_closedBall.mp hanchorBall)
      _ = 7 * radius / 2 := by
        dsimp only [ambientRadius]
        ring

/-- Record-valued form of `exactLocalSet_finite_occupied_source_cover`. -/
theorem toExactLocalOccupiedCoverData
    (terminal : commonSource.TerminalGeometry)
    (anchor0 : {point : Point3 // point ∈ terminal.exactShading.union})
    {radius : ℝ} (hradius : 0 < radius) :
    Nonempty (ExactLocalOccupiedCoverData commonSource terminal anchor0 radius) := by
  obtain ⟨centers, hcard, sourcePieces, sourceAnchor, hcover, hsourceSubset,
      hanchorBall, himageBall, hsourceBall⟩ :=
    exactLocalSet_finite_occupied_source_cover commonSource terminal anchor0
      hradius
  exact ⟨{
    centers := centers
    card_le := hcard
    sourcePieces := sourcePieces
    sourceAnchor := sourceAnchor
    cover := hcover
    source_subset := hsourceSubset
    anchor_ball := hanchorBall
    image_ball := himageBall
    source_ball := hsourceBall
  }⟩

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
