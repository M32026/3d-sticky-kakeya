import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperCenteredConflictDegree
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeParameters
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicCenteredMap

/-!
# Public centered-conflict degree for the exact triangular map

This is the target-side cleanup used in Proposition 6.5.  A centered
containment between two localized target tubes first gives a target paper
line-distance bound.  Exact supporting-line provenance identifies their
four target parameters with `anisotropicTubeParams`; the quantitative inverse
formula then pulls the conflict back to one source parameter box.

The final degree estimate is deliberately independent of any choice of
coarse parents.  It is therefore safe to use before constructing the public
nearby-scale covers.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- One directed public centered containment in the target pulls back to a
source four-parameter box for the exact triangular affine map. -/
theorem source_parameter_cluster_of_anisotropic_centered_containment
    (hInverse : AnisotropicTubeParamsInverseClusterStatement)
    {sourceDelta targetDelta c d m : ℝ}
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (g : SlopeFunction)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (targetFamily : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceParent : Fin targetFamily.card → Fin sourceFamily.card)
    (htargetLine : WZ1PaperIsLineClass targetFamily)
    (htargetLocal : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFamily.tube target)‖ ≤ 3)
    (hsourceVertical : ∀ source,
      (sourceFamily.tube source).direction (2 : Fin 3) ≠ 0)
    (htargetVertical : ∀ target,
      (targetFamily.tube target).direction (2 : Fin 3) ≠ 0)
    (haxis : ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        anisotropicRescalingMap g c d m ''
          tubeAxisLine (sourceFamily.tube (sourceParent target)))
    (reference other : Fin targetFamily.card)
    (hcontain : (targetFamily.tube reference).carrier ⊆
      wz2PaperCenteredDilatedCarrier 2 (targetFamily.tube other)) :
    let width := 100 * (600 * targetDelta) / (m * (d - c) ^ 2)
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
  have htargetCluster :=
    tubeParamsOfTube_cluster_of_paperLineDistance
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
    dsimp only [wz2PaperLocalizedDoubledFiberLineDistanceConstant]
      at hlineDistance htargetCluster
    exact ⟨htargetCluster.1.trans (by nlinarith),
      htargetCluster.2.1.trans (by nlinarith),
      by convert htargetCluster.2.2.1 using 1 <;> ring,
      by convert htargetCluster.2.2.2 using 1 <;> ring⟩
  have hrefParams :=
    tubeParamsOfTube_eq_anisotropic_of_axis_image
      g hcd (sourceFamily.tube (sourceParent reference))
      (hsourceVertical _) (targetFamily.tube reference)
      (htargetVertical _) (haxis reference)
  have hotherParams :=
    tubeParamsOfTube_eq_anisotropic_of_axis_image
      g hcd (sourceFamily.tube (sourceParent other))
      (hsourceVertical _) (targetFamily.tube other)
      (htargetVertical _) (haxis other)
  rw [hrefParams, hotherParams] at htargetBound
  simpa only [tubeParams] using
    hInverse g c d m (600 * targetDelta)
      hcd hdc hsub hm hmOne hgmid (by positivity)
      (tubeParamsOfTube (sourceFamily.tube (sourceParent reference)))
      (tubeParamsOfTube (sourceFamily.tube (sourceParent other)))
      htargetBound.1 htargetBound.2.1
      htargetBound.2.2.1 htargetBound.2.2.2

/-- A symmetric public centered conflict in the target pulls back to the same
source four-parameter box. -/
theorem source_parameter_cluster_of_anisotropic_centered_conflict
    (hInverse : AnisotropicTubeParamsInverseClusterStatement)
    {sourceDelta targetDelta c d m : ℝ}
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (g : SlopeFunction)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (targetFamily : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceParent : Fin targetFamily.card → Fin sourceFamily.card)
    (htargetLine : WZ1PaperIsLineClass targetFamily)
    (htargetLocal : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFamily.tube target)‖ ≤ 3)
    (hsourceVertical : ∀ source,
      (sourceFamily.tube source).direction (2 : Fin 3) ≠ 0)
    (htargetVertical : ∀ target,
      (targetFamily.tube target).direction (2 : Fin 3) ≠ 0)
    (haxis : ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        anisotropicRescalingMap g c d m ''
          tubeAxisLine (sourceFamily.tube (sourceParent target)))
    (reference other : Fin targetFamily.card)
    (hconflict : pureWZ2PaperCenteredConflict
      targetFamily reference other) :
    let width := 100 * (600 * targetDelta) / (m * (d - c) ^ 2)
    |(tubeParams (F := sourceFamily) (sourceParent reference)).a -
        (tubeParams (F := sourceFamily) (sourceParent other)).a| ≤ width ∧
      |(tubeParams (F := sourceFamily) (sourceParent reference)).b -
        (tubeParams (F := sourceFamily) (sourceParent other)).b| ≤ width ∧
      |(tubeParams (F := sourceFamily) (sourceParent reference)).c -
        (tubeParams (F := sourceFamily) (sourceParent other)).c| ≤ width ∧
      |(tubeParams (F := sourceFamily) (sourceParent reference)).d -
        (tubeParams (F := sourceFamily) (sourceParent other)).d| ≤ width := by
  dsimp only
  rcases hconflict with ⟨_hne, hcontain | hcontain⟩
  · exact source_parameter_cluster_of_anisotropic_centered_containment
      hInverse hcd hdc hsub hm hmOne g hgmid htargetDelta
      sourceFamily targetFamily sourceParent htargetLine htargetLocal
      hsourceVertical htargetVertical haxis reference other hcontain
  · have hresult :=
      source_parameter_cluster_of_anisotropic_centered_containment
        hInverse hcd hdc hsub hm hmOne g hgmid htargetDelta
        sourceFamily targetFamily sourceParent htargetLine htargetLocal
        hsourceVertical htargetVertical haxis other reference hcontain
    exact ⟨by simpa [abs_sub_comm] using hresult.1,
      by simpa [abs_sub_comm] using hresult.2.1,
      by simpa [abs_sub_comm] using hresult.2.2.1,
      by simpa [abs_sub_comm] using hresult.2.2.2⟩

/-- Source parameter Frostman control and a bounded source-index fiber bound
control the actual public centered-conflict degree of the triangular target. -/
theorem anisotropic_centered_conflict_degree_le
    (hInverse : AnisotropicTubeParamsInverseClusterStatement)
    {sourceDelta targetDelta c d m : ℝ}
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (g : SlopeFunction)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (targetFamily : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceParent : Fin targetFamily.card → Fin sourceFamily.card)
    (fiberCap : ℕ)
    (hfiber : ∀ source,
      ((Finset.univ : Finset (Fin targetFamily.card)).filter fun target =>
        sourceParent target = source).card ≤ fiberCap)
    (htargetLine : WZ1PaperIsLineClass targetFamily)
    (htargetLocal : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFamily.tube target)‖ ≤ 3)
    (hsourceVertical : ∀ source,
      (sourceFamily.tube source).direction (2 : Fin 3) ≠ 0)
    (htargetVertical : ∀ target,
      (targetFamily.tube target).direction (2 : Fin 3) ≠ 0)
    (haxis : ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        anisotropicRescalingMap g c d m ''
          tubeAxisLine (sourceFamily.tube (sourceParent target)))
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
    (hwidth : width =
      100 * (600 * targetDelta) / (m * (d - c) ^ 2))
    (hsourceWidth : sourceDelta ≤ width)
    (hwidthOne : width ≤ 1) :
    ∀ reference : Fin targetFamily.card,
      (((Finset.univ : Finset (Fin targetFamily.card)).filter
        (pureWZ2PaperCenteredConflict targetFamily reference)).card :
          ENNReal) ≤
        (fiberCap : ENNReal) *
          (sourceConstant * Kakeya.realRpowENN width 2 * normalization) := by
  intro reference
  let conflicts : Finset (Fin targetFamily.card) :=
    Finset.univ.filter
      (pureWZ2PaperCenteredConflict targetFamily reference)
  let sourceConflicts : Finset (Fin sourceFamily.card) :=
    conflicts.image sourceParent
  let sourceCluster : Finset (Fin sourceFamily.card) :=
    Finset.univ.filter fun source =>
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
    have hcluster :=
      source_parameter_cluster_of_anisotropic_centered_conflict
        hInverse hcd hdc hsub hm hmOne g hgmid htargetDelta
        sourceFamily targetFamily sourceParent htargetLine htargetLocal
        hsourceVertical htargetVertical haxis reference target hconflict
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hwidth]
    exact ⟨by simpa [abs_sub_comm] using hcluster.1,
      by simpa [abs_sub_comm] using hcluster.2.1,
      by simpa [abs_sub_comm] using hcluster.2.2.1,
      by simpa [abs_sub_comm] using hcluster.2.2.2⟩
  have hsourceCard :
      (sourceConflicts.card : ENNReal) ≤
        sourceConstant * Kakeya.realRpowENN width 2 * normalization := by
    calc
      (sourceConflicts.card : ENNReal) ≤
          (sourceCluster.card : ENNReal) := by
        exact_mod_cast Finset.card_le_card hsourceSubset
      _ ≤ sourceConstant * Kakeya.realRpowENN width 2 * normalization := by
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

/-! ## Common horizontal recentering -/

/-- A centered target line keeps the uncentered triangular parameter
differences, so one centered containment pulls back to the same source box. -/
theorem source_parameter_cluster_of_anisotropic_recentered_containment
    (hInverse : AnisotropicTubeParamsInverseClusterStatement)
    {sourceDelta targetDelta c d m : ℝ}
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (g : SlopeFunction) (center : Point3)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (targetFamily : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceParent : Fin targetFamily.card → Fin sourceFamily.card)
    (htargetLine : WZ1PaperIsLineClass targetFamily)
    (htargetLocal : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFamily.tube target)‖ ≤ 3)
    (hsourceVertical : ∀ source,
      (sourceFamily.tube source).direction 2 ≠ 0)
    (htargetVertical : ∀ target,
      (targetFamily.tube target).direction 2 ≠ 0)
    (haxis : ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        anisotropicCenteredRescalingMap g c d m center ''
          tubeAxisLine (sourceFamily.tube (sourceParent target)))
    (reference other : Fin targetFamily.card)
    (hcontain : (targetFamily.tube reference).carrier ⊆
      wz2PaperCenteredDilatedCarrier 2 (targetFamily.tube other)) :
    let width := 100 * (600 * targetDelta) / (m * (d - c) ^ 2)
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
  have htargetCluster :=
    tubeParamsOfTube_cluster_of_paperLineDistance
      (htargetLine reference) (htargetLine other) hlineDistance
  have htargetBound :
      |(tubeParamsOfTube (targetFamily.tube reference)).a -
          (tubeParamsOfTube (targetFamily.tube other)).a| ≤ 600 * targetDelta ∧
        |(tubeParamsOfTube (targetFamily.tube reference)).b -
          (tubeParamsOfTube (targetFamily.tube other)).b| ≤ 600 * targetDelta ∧
        |(tubeParamsOfTube (targetFamily.tube reference)).c -
          (tubeParamsOfTube (targetFamily.tube other)).c| ≤ 600 * targetDelta ∧
        |(tubeParamsOfTube (targetFamily.tube reference)).d -
          (tubeParamsOfTube (targetFamily.tube other)).d| ≤ 600 * targetDelta := by
    dsimp only [wz2PaperLocalizedDoubledFiberLineDistanceConstant]
      at hlineDistance htargetCluster
    exact ⟨htargetCluster.1.trans (by nlinarith),
      htargetCluster.2.1.trans (by nlinarith),
      by convert htargetCluster.2.2.1 using 1 <;> ring,
      by convert htargetCluster.2.2.2 using 1 <;> ring⟩
  have hrefParams := tubeParamsOfTube_eq_anisotropicCentered_of_axis_image
    g hcd center (sourceFamily.tube (sourceParent reference))
      (hsourceVertical _) (targetFamily.tube reference)
      (htargetVertical _) (haxis reference)
  have hotherParams := tubeParamsOfTube_eq_anisotropicCentered_of_axis_image
    g hcd center (sourceFamily.tube (sourceParent other))
      (hsourceVertical _) (targetFamily.tube other)
      (htargetVertical _) (haxis other)
  rw [hrefParams, hotherParams] at htargetBound
  have hdiff := anisotropicCenteredTubeParams_sub_eq
    g c d m center
      (tubeParamsOfTube (sourceFamily.tube (sourceParent reference)))
      (tubeParamsOfTube (sourceFamily.tube (sourceParent other)))
  have hrawBound :
      |(anisotropicTubeParams g c d m
          (tubeParamsOfTube (sourceFamily.tube (sourceParent reference)))).a -
          (anisotropicTubeParams g c d m
            (tubeParamsOfTube (sourceFamily.tube (sourceParent other)))).a| ≤
            600 * targetDelta ∧
        |(anisotropicTubeParams g c d m
          (tubeParamsOfTube (sourceFamily.tube (sourceParent reference)))).b -
          (anisotropicTubeParams g c d m
            (tubeParamsOfTube (sourceFamily.tube (sourceParent other)))).b| ≤
            600 * targetDelta ∧
        |(anisotropicTubeParams g c d m
          (tubeParamsOfTube (sourceFamily.tube (sourceParent reference)))).c -
          (anisotropicTubeParams g c d m
            (tubeParamsOfTube (sourceFamily.tube (sourceParent other)))).c| ≤
            600 * targetDelta ∧
        |(anisotropicTubeParams g c d m
          (tubeParamsOfTube (sourceFamily.tube (sourceParent reference)))).d -
          (anisotropicTubeParams g c d m
            (tubeParamsOfTube (sourceFamily.tube (sourceParent other)))).d| ≤
            600 * targetDelta := by
    exact ⟨by rw [← hdiff.1]; exact htargetBound.1,
      by rw [← hdiff.2.1]; exact htargetBound.2.1,
      by rw [← hdiff.2.2.1]; exact htargetBound.2.2.1,
      by rw [← hdiff.2.2.2]; exact htargetBound.2.2.2⟩
  simpa only [tubeParams] using
    hInverse g c d m (600 * targetDelta)
      hcd hdc hsub hm hmOne hgmid (by positivity)
      (tubeParamsOfTube (sourceFamily.tube (sourceParent reference)))
      (tubeParamsOfTube (sourceFamily.tube (sourceParent other)))
      hrawBound.1 hrawBound.2.1 hrawBound.2.2.1 hrawBound.2.2.2

/-- The symmetric centered-conflict version of the recentered pullback. -/
theorem source_parameter_cluster_of_anisotropic_recentered_conflict
    (hInverse : AnisotropicTubeParamsInverseClusterStatement)
    {sourceDelta targetDelta c d m : ℝ}
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (g : SlopeFunction) (center : Point3)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (targetFamily : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceParent : Fin targetFamily.card → Fin sourceFamily.card)
    (htargetLine : WZ1PaperIsLineClass targetFamily)
    (htargetLocal : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFamily.tube target)‖ ≤ 3)
    (hsourceVertical : ∀ source,
      (sourceFamily.tube source).direction 2 ≠ 0)
    (htargetVertical : ∀ target,
      (targetFamily.tube target).direction 2 ≠ 0)
    (haxis : ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        anisotropicCenteredRescalingMap g c d m center ''
          tubeAxisLine (sourceFamily.tube (sourceParent target)))
    (reference other : Fin targetFamily.card)
    (hconflict : pureWZ2PaperCenteredConflict
      targetFamily reference other) :
    let width := 100 * (600 * targetDelta) / (m * (d - c) ^ 2)
    |(tubeParams (F := sourceFamily) (sourceParent reference)).a -
        (tubeParams (F := sourceFamily) (sourceParent other)).a| ≤ width ∧
      |(tubeParams (F := sourceFamily) (sourceParent reference)).b -
        (tubeParams (F := sourceFamily) (sourceParent other)).b| ≤ width ∧
      |(tubeParams (F := sourceFamily) (sourceParent reference)).c -
        (tubeParams (F := sourceFamily) (sourceParent other)).c| ≤ width ∧
      |(tubeParams (F := sourceFamily) (sourceParent reference)).d -
        (tubeParams (F := sourceFamily) (sourceParent other)).d| ≤ width := by
  dsimp only
  rcases hconflict with ⟨_hne, hcontain | hcontain⟩
  · exact source_parameter_cluster_of_anisotropic_recentered_containment
      hInverse hcd hdc hsub hm hmOne g center hgmid htargetDelta
      sourceFamily targetFamily sourceParent htargetLine htargetLocal
      hsourceVertical htargetVertical haxis reference other hcontain
  · have hresult :=
      source_parameter_cluster_of_anisotropic_recentered_containment
        hInverse hcd hdc hsub hm hmOne g center hgmid htargetDelta
        sourceFamily targetFamily sourceParent htargetLine htargetLocal
        hsourceVertical htargetVertical haxis other reference hcontain
    exact ⟨by simpa [abs_sub_comm] using hresult.1,
      by simpa [abs_sub_comm] using hresult.2.1,
      by simpa [abs_sub_comm] using hresult.2.2.1,
      by simpa [abs_sub_comm] using hresult.2.2.2⟩

/-- Source parameter Frostman control bounds the public centered-conflict
degree after the common horizontal recentering used by the paper retubing.
The proof counts source indices first and then uses the stated fiber cap; in
the one-to-one paper family this cap is exactly one. -/
theorem anisotropic_recentered_conflict_degree_le
    (hInverse : AnisotropicTubeParamsInverseClusterStatement)
    {sourceDelta targetDelta c d m : ℝ}
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (g : SlopeFunction) (center : Point3)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (targetFamily : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceParent : Fin targetFamily.card → Fin sourceFamily.card)
    (fiberCap : ℕ)
    (hfiber : ∀ source,
      ((Finset.univ : Finset (Fin targetFamily.card)).filter fun target =>
        sourceParent target = source).card ≤ fiberCap)
    (htargetLine : WZ1PaperIsLineClass targetFamily)
    (htargetLocal : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFamily.tube target)‖ ≤ 3)
    (hsourceVertical : ∀ source,
      (sourceFamily.tube source).direction 2 ≠ 0)
    (htargetVertical : ∀ target,
      (targetFamily.tube target).direction 2 ≠ 0)
    (haxis : ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        anisotropicCenteredRescalingMap g c d m center ''
          tubeAxisLine (sourceFamily.tube (sourceParent target)))
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
    (hwidth : width =
      100 * (600 * targetDelta) / (m * (d - c) ^ 2))
    (hsourceWidth : sourceDelta ≤ width)
    (hwidthOne : width ≤ 1) :
    ∀ reference : Fin targetFamily.card,
      (((Finset.univ : Finset (Fin targetFamily.card)).filter
        (pureWZ2PaperCenteredConflict targetFamily reference)).card :
          ENNReal) ≤
        (fiberCap : ENNReal) *
          (sourceConstant * Kakeya.realRpowENN width 2 * normalization) := by
  intro reference
  let conflicts : Finset (Fin targetFamily.card) :=
    Finset.univ.filter
      (pureWZ2PaperCenteredConflict targetFamily reference)
  let sourceConflicts : Finset (Fin sourceFamily.card) :=
    conflicts.image sourceParent
  let sourceCluster : Finset (Fin sourceFamily.card) :=
    Finset.univ.filter fun source =>
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
    have hcluster :=
      source_parameter_cluster_of_anisotropic_recentered_conflict
        hInverse hcd hdc hsub hm hmOne g center hgmid htargetDelta
        sourceFamily targetFamily sourceParent htargetLine htargetLocal
        hsourceVertical htargetVertical haxis reference target hconflict
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hwidth]
    exact ⟨by simpa [abs_sub_comm] using hcluster.1,
      by simpa [abs_sub_comm] using hcluster.2.1,
      by simpa [abs_sub_comm] using hcluster.2.2.1,
      by simpa [abs_sub_comm] using hcluster.2.2.2⟩
  have hsourceCard :
      (sourceConflicts.card : ENNReal) ≤
        sourceConstant * Kakeya.realRpowENN width 2 * normalization := by
    calc
      (sourceConflicts.card : ENNReal) ≤
          (sourceCluster.card : ENNReal) := by
        exact_mod_cast Finset.card_le_card hsourceSubset
      _ ≤ sourceConstant * Kakeya.realRpowENN width 2 * normalization := by
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

end
