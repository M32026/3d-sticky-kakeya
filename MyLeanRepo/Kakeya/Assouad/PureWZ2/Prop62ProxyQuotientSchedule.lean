import MyLeanRepo.Kakeya.Assouad.PureWZ2.FiniteMaximalQuotientNet
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyMetricMeshProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.WeightedGraphSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement

/-!
# Proposition 6.2 proxy-line quotient schedule

Definition 2.12 parents are ordinary finite segments and may repeat one
supporting line at different longitudinal positions.  The paper works in the
four-dimensional space of affine lines, so each scheduled level is first
quotiented by a maximal separated net of the complete-packet proxy axes.

No fine tube or complete actual packet is deleted.  Every actual parent maps
surjectively to one proxy-line center.  Only the quotient centers are colored.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Absolute degree for the `12000000 * r` graph on an `r / 4` line net. -/
def pureWZ2Prop62ProxyCenterConflictDegree : ℕ :=
  (2 * 384000000 + 1) ^ 5

structure PureWZ2Prop62ProxyQuotientLevelData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount) where
  net :
    WZ2FiniteMaximalQuotientNetData
      (schedule.scaleData coordinate).coarse.card
      (fun first second =>
        wz1PaperLineDistance
          (schedule.coordinateProxyTube
            fineNonempty coordinate first)
          (schedule.coordinateProxyTube
            fineNonempty coordinate second))
      (schedule.actualScale coordinate / 4)

namespace PureWZ2Prop62ProxyQuotientLevelData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {coordinate : Fin schedule.levelCount}
    (level :
      PureWZ2Prop62ProxyQuotientLevelData
        schedule fineNonempty coordinate)

/-- Radius-`r/4` centered representatives of the quotient line classes. -/
noncomputable def centerFamily :
    Kakeya.Streamlined.TubeFamily
      (schedule.actualScale coordinate / 4) where
  card := level.net.centers.card
  tube center :=
    wz2PaperCenteredLineTube
      (targetScale := schedule.actualScale coordinate / 4)
      (schedule.coordinateProxyTube
        fineNonempty coordinate
        (level.net.centerEmbedding center))

theorem centerFamily_lineClass
    (fineLine : WZ1PaperIsLineClass fine) :
    WZ1PaperIsLineClass level.centerFamily := by
  intro center
  exact
    wz2PaperCenteredLineTube_lineClass <|
      schedule.coordinateProxyTube_lineClass
        fineNonempty fineLine coordinate
        (level.net.centerEmbedding center)

theorem centerFamily_lineDistance
    (fineLine : WZ1PaperIsLineClass fine)
    (first second : Fin level.centerFamily.card) :
    wz1PaperLineDistance
        (level.centerFamily.tube first)
        (level.centerFamily.tube second) =
      wz1PaperLineDistance
        (schedule.coordinateProxyTube
          fineNonempty coordinate
          (level.net.centerEmbedding first))
        (schedule.coordinateProxyTube
          fineNonempty coordinate
          (level.net.centerEmbedding second)) := by
  exact
    wz1PaperLineDistance_centeredLineTube_both
      (schedule.coordinateProxyTube_lineClass
        fineNonempty fineLine coordinate
        (level.net.centerEmbedding first))
      (schedule.coordinateProxyTube_lineClass
        fineNonempty fineLine coordinate
        (level.net.centerEmbedding second))

theorem centerFamily_distinct
    (fineLine : WZ1PaperIsLineClass fine) :
    WZ1PaperIsEssentiallyDistinct level.centerFamily := by
  intro first second hne
  rw [level.centerFamily_lineDistance fineLine]
  exact level.net.centers_separated first second hne

theorem actualProxy_center_lineDistance_le
    (fineLine : WZ1PaperIsLineClass fine)
    (parent : Fin (schedule.scaleData coordinate).coarse.card) :
    wz1PaperLineDistance
        (schedule.coordinateProxyTube
          fineNonempty coordinate parent)
        (level.centerFamily.tube (level.net.center parent)) ≤
      schedule.actualScale coordinate / 4 := by
  change
    wz1PaperLineDistance
        (schedule.coordinateProxyTube
          fineNonempty coordinate parent)
        (wz2PaperCenteredLineTube
          (targetScale := schedule.actualScale coordinate / 4)
          (schedule.coordinateProxyTube
            fineNonempty coordinate
            (level.net.centerEmbedding
              (level.net.center parent)))) ≤
      schedule.actualScale coordinate / 4
  rw [wz1PaperLineDistance_centeredLineTube_right
    (schedule.coordinateProxyTube_lineClass
      fineNonempty fineLine coordinate parent)
    (schedule.coordinateProxyTube_lineClass
      fineNonempty fineLine coordinate
      (level.net.centerEmbedding (level.net.center parent)))]
  exact level.net.center_close parent

theorem center_conflict_degree
    (fineLine : WZ1PaperIsLineClass fine)
    (fixed : Fin level.centerFamily.card) :
    (Finset.univ.filter fun other =>
      wz1PaperLineDistance
          (level.centerFamily.tube other)
          (level.centerFamily.tube fixed) ≤
        wz2PaperLiteralSourceSeparationFactor *
          schedule.actualScale coordinate).card ≤
      pureWZ2Prop62ProxyCenterConflictDegree := by
  have actualPos :
      0 < schedule.actualScale coordinate :=
    (schedule.scaleData coordinate).rho_pos
  have packing :=
    tube_packing_bound_general
      (level.centerFamily_distinct fineLine)
      (level.centerFamily_lineClass fineLine)
      (by positivity :
        0 < schedule.actualScale coordinate / 4)
      (wz2PaperLiteralSourceSeparationFactor *
        schedule.actualScale coordinate)
      (mul_pos
        (by
          norm_num [wz2PaperLiteralSourceSeparationFactor])
        actualPos)
      fixed
  have quotient :
      8 *
          (wz2PaperLiteralSourceSeparationFactor *
            schedule.actualScale coordinate) /
          (schedule.actualScale coordinate / 4) =
        (384000000 : ℝ) := by
    rw [show
      (wz2PaperLiteralSourceSeparationFactor : ℝ) =
        12000000 by
      norm_num [wz2PaperLiteralSourceSeparationFactor]]
    field_simp [actualPos.ne']
    norm_num
  have ceiling :
      Nat.ceil
          (8 *
            (wz2PaperLiteralSourceSeparationFactor *
              schedule.actualScale coordinate) /
            (schedule.actualScale coordinate / 4)) =
        384000000 := by
    rw [quotient]
    norm_num
  rw [ceiling] at packing
  simpa [pureWZ2Prop62ProxyCenterConflictDegree] using packing

end PureWZ2Prop62ProxyQuotientLevelData

theorem exists_pureWZ2Prop62ProxyQuotientLevelData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount) :
    Nonempty
      (PureWZ2Prop62ProxyQuotientLevelData
        schedule fineNonempty coordinate) := by
  let distance :
      Fin (schedule.scaleData coordinate).coarse.card →
        Fin (schedule.scaleData coordinate).coarse.card → ℝ :=
    fun first second =>
      wz1PaperLineDistance
        (schedule.coordinateProxyTube
          fineNonempty coordinate first)
        (schedule.coordinateProxyTube
          fineNonempty coordinate second)
  have distanceSymmetric :
      ∀ first second,
        distance first second = distance second first :=
    fun first second => wz1PaperLineDistance_symm _ _
  have distanceSelf :
      ∀ parent, distance parent parent = 0 := by
    intro parent
    have directionNe :
        wz1PaperDirection
            (schedule.coordinateProxyTube
              fineNonempty coordinate parent) ≠ 0 := by
      intro hzero
      have hnorm :=
        wz1PaperDirection_norm
          (schedule.coordinateProxyTube
            fineNonempty coordinate parent)
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    simp [distance, wz1PaperLineDistance,
      InnerProductGeometry.angle_self directionNe]
  have parentCountPos :
      0 < (schedule.scaleData coordinate).coarse.card := by
    rcases
        (schedule.scaleData coordinate).cover.covers
          ⟨0, fineNonempty⟩
      with
      ⟨parent, _⟩
    exact lt_of_le_of_lt (Nat.zero_le parent.val) parent.isLt
  rcases
      wz2_finite_maximal_quotient_net
        (schedule.scaleData coordinate).coarse.card
        parentCountPos distance distanceSymmetric distanceSelf
        (schedule.actualScale coordinate / 4)
        (by
          have := (schedule.scaleData coordinate).rho_pos
          positivity)
    with
    ⟨net⟩
  exact ⟨{ net := net }⟩

structure PureWZ2Prop62ProxyCenterColoringData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {coordinate : Fin schedule.levelCount}
    (level :
      PureWZ2Prop62ProxyQuotientLevelData
        schedule fineNonempty coordinate) where
  color :
    Fin level.centerFamily.card →
      Fin (pureWZ2Prop62ProxyCenterConflictDegree + 1)
  proper :
    ∀ first second, first ≠ second →
      wz1PaperLineDistance
          (level.centerFamily.tube first)
          (level.centerFamily.tube second) ≤
        wz2PaperLiteralSourceSeparationFactor *
          schedule.actualScale coordinate →
      color first ≠ color second

theorem pureWZ2_prop62_proxy_center_coloring
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {coordinate : Fin schedule.levelCount}
    (fineLine : WZ1PaperIsLineClass fine)
    (level :
      PureWZ2Prop62ProxyQuotientLevelData
        schedule fineNonempty coordinate) :
    Nonempty (PureWZ2Prop62ProxyCenterColoringData level) := by
  let conflict :
      Fin level.centerFamily.card →
        Fin level.centerFamily.card → Prop :=
    fun first second =>
      second ≠ first ∧
        wz1PaperLineDistance
            (level.centerFamily.tube second)
            (level.centerFamily.tube first) ≤
          wz2PaperLiteralSourceSeparationFactor *
            schedule.actualScale coordinate
  have symmetric :
      ∀ first second, conflict first second →
        conflict second first := by
    intro first second hconflict
    refine ⟨hconflict.1.symm, ?_⟩
    rw [wz1PaperLineDistance_symm]
    exact hconflict.2
  have irreflexive :
      ∀ center, ¬conflict center center := by
    intro center hconflict
    exact hconflict.1 rfl
  rcases
      pureWZ2_greedy_proper_coloring
        (D := pureWZ2Prop62ProxyCenterConflictDegree)
        symmetric irreflexive
        (fun fixed => by
          dsimp only [conflict]
          rw [Finset.filter_congr_decidable]
          have subset :
              (Finset.univ.filter fun other =>
                other ≠ fixed ∧
                  wz1PaperLineDistance
                      (level.centerFamily.tube other)
                      (level.centerFamily.tube fixed) ≤
                    wz2PaperLiteralSourceSeparationFactor *
                      schedule.actualScale coordinate) ⊆
                Finset.univ.filter fun other =>
                  wz1PaperLineDistance
                      (level.centerFamily.tube other)
                      (level.centerFamily.tube fixed) ≤
                    wz2PaperLiteralSourceSeparationFactor *
                      schedule.actualScale coordinate := by
            intro other hother
            exact
              Finset.mem_filter.mpr
                ⟨Finset.mem_univ other,
                  (Finset.mem_filter.mp hother).2.2⟩
          exact
            (Finset.card_le_card subset).trans
              (level.center_conflict_degree fineLine fixed))
    with
    ⟨color, proper⟩
  exact
    ⟨{
      color := color
      proper := by
        intro first second hne hclose
        exact
          proper first second
            ⟨hne.symm, by
              rw [wz1PaperLineDistance_symm]
              exact hclose⟩
    }⟩

structure PureWZ2Prop62ProxyQuotientScheduleData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty) where
  level :
    ∀ coordinate,
      PureWZ2Prop62ProxyQuotientLevelData
        schedule fineNonempty coordinate
  coloring :
    ∀ coordinate,
      PureWZ2Prop62ProxyCenterColoringData
        (level coordinate)

theorem exists_pureWZ2Prop62ProxyQuotientScheduleData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine) :
    Nonempty
      (PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty) := by
  let level :
      ∀ coordinate,
        PureWZ2Prop62ProxyQuotientLevelData
          schedule fineNonempty coordinate :=
    fun coordinate =>
      Classical.choice <|
        exists_pureWZ2Prop62ProxyQuotientLevelData
          schedule fineNonempty coordinate
  let coloring :
      ∀ coordinate,
        PureWZ2Prop62ProxyCenterColoringData
          (level coordinate) :=
    fun coordinate =>
      Classical.choice <|
        pureWZ2_prop62_proxy_center_coloring
          fineLine (level coordinate)
  exact ⟨{ level := level, coloring := coloring }⟩

namespace PureWZ2Prop62ProxyQuotientScheduleData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)

/-- Quotient-center parent of one actual complete packet. -/
def actualCenter
    (coordinate : Fin schedule.levelCount)
    (parent : Fin (schedule.scaleData coordinate).coarse.card) :
    Fin (quotient.level coordinate).centerFamily.card :=
  (quotient.level coordinate).net.center parent

theorem actualCenter_surjective
    (coordinate : Fin schedule.levelCount) :
    Function.Surjective (quotient.actualCenter coordinate) :=
  (quotient.level coordinate).net.center_surjective

/-- Actual Definition 2.12 parents merged into one proxy-line center. -/
def centerActualParents
    (coordinate : Fin schedule.levelCount)
    (center : Fin (quotient.level coordinate).centerFamily.card) :
    Finset (Fin (schedule.scaleData coordinate).coarse.card) :=
  Finset.univ.filter fun parent =>
    quotient.actualCenter coordinate parent = center

theorem centerActualParents_nonempty
    (coordinate : Fin schedule.levelCount)
    (center : Fin (quotient.level coordinate).centerFamily.card) :
    (quotient.centerActualParents coordinate center).Nonempty := by
  rcases quotient.actualCenter_surjective coordinate center with
    ⟨parent, hparent⟩
  exact
    ⟨parent,
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ parent, hparent⟩⟩

/-- Quotient-center ancestry label of one fine leaf. -/
def leafCenter
    (coordinate : Fin schedule.levelCount)
    (source : Fin fine.card) :
    Fin (quotient.level coordinate).centerFamily.card :=
  quotient.actualCenter coordinate
    ((schedule.scaleData coordinate).cover.parent source)

/-- Fine leaves grouped by one quotient-center label. -/
def centerPacketIndices
    (coordinate : Fin schedule.levelCount)
    (center : Fin (quotient.level coordinate).centerFamily.card) :
    Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    quotient.leafCenter coordinate source = center

/--
No complete packet is lost in the line quotient: one center class is exactly
the union of all complete actual strict fibers mapping to that center.
-/
theorem centerPacketIndices_eq_actual_biUnion
    (coordinate : Fin schedule.levelCount)
    (center : Fin (quotient.level coordinate).centerFamily.card) :
    quotient.centerPacketIndices coordinate center =
      Finset.biUnion
        (quotient.centerActualParents coordinate center)
        (wz2PaperOrdinaryFullFiberIndices
          fine (schedule.scaleData coordinate).coarse) := by
  ext source
  simp only [centerPacketIndices, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_biUnion]
  constructor
  · intro hcenter
    let parent :=
      (schedule.scaleData coordinate).cover.parent source
    refine
      ⟨parent, ?_,
        (schedule.scaleData coordinate).cover
          |>.parent_mem_fullFiber source⟩
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ parent, hcenter⟩
  · rintro ⟨parent, hparent, hsource⟩
    have sourceParent :
        (schedule.scaleData coordinate).cover.parent source =
          parent :=
      ((schedule.scaleData coordinate).cover
        |>.mem_fullFiber_iff_parent_eq
          (schedule.scaleData coordinate).rho_pos.le
          parent source).mp hsource
    have parentCenter :
        quotient.actualCenter coordinate parent = center :=
      (Finset.mem_filter.mp hparent).2
    unfold leafCenter
    rwa [sourceParent]

/-- Color of the quotient-center ancestor of one fine leaf. -/
def leafCenterColor
    (coordinate : Fin schedule.levelCount)
    (source : Fin fine.card) :
    Fin (pureWZ2Prop62ProxyCenterConflictDegree + 1) :=
  (quotient.coloring coordinate).color
    (quotient.leafCenter coordinate source)

theorem leafCenter_eq_of_color_eq_of_lineDistance_le
    (coordinate : Fin schedule.levelCount)
    (first second : Fin fine.card)
    (colorEq :
      quotient.leafCenterColor coordinate first =
        quotient.leafCenterColor coordinate second)
    (distanceClose :
      wz1PaperLineDistance
          ((quotient.level coordinate).centerFamily.tube
            (quotient.leafCenter coordinate first))
          ((quotient.level coordinate).centerFamily.tube
            (quotient.leafCenter coordinate second)) ≤
        wz2PaperLiteralSourceSeparationFactor *
          schedule.actualScale coordinate) :
    quotient.leafCenter coordinate first =
      quotient.leafCenter coordinate second := by
  by_contra hne
  exact
    ((quotient.coloring coordinate).proper
      (quotient.leafCenter coordinate first)
      (quotient.leafCenter coordinate second)
      hne distanceClose) colorEq

end PureWZ2Prop62ProxyQuotientScheduleData

end Kakeya.Assouad

end
