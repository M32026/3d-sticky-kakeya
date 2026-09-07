import MyLeanRepo.Kakeya.Assouad.PureWZ2.CanonicalLineTube
import MyLeanRepo.Kakeya.Assouad.PureWZ2.TubeParameterLineDistance
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDoubledParentCarrierCover
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CommonContainerTargetTubeParameterClusterBaseFive

/-!
# Localized actual fibers lie in prescribed line balls

After the concrete final shading removes empty tubes, the retained ordinary
tubes live in a fixed spatial window.  Two retained tubes in one complete
actual Definition 2.12 fiber therefore have nearby vertical-chart
parameters.  If the actual scale is sufficiently smaller than the prescribed
caller scale, the entire actual fiber is covered by the caller-scale
enlargement of any representative.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The common-container parameter cluster gives a paper line-distance bound. -/
theorem wz1PaperLineDistance_le_of_common_actual_parent
    {delta actual : ℝ}
    {first second : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube actual}
    (hdelta : 0 < delta)
    (hdeltaActual : delta ≤ actual)
    (hactualSmall : actual ≤ 1 / 10000)
    (hfirstLine : WZ1PaperTubeInLineClass first)
    (hsecondLine : WZ1PaperTubeInLineClass second)
    (hfirstBase : ‖first.base‖ ≤ 5)
    (hsecondBase : ‖second.base‖ ≤ 5)
    (hfirstParent : first.carrier ⊆ parent.carrier)
    (hsecondParent : second.carrier ⊆ parent.carrier) :
    wz1PaperLineDistance first second ≤
      600000 * actual := by
  have hactual : 0 < actual :=
    hdelta.trans_le hdeltaActual
  have hparameters :=
    common_container_target_tube_parameter_cluster_base_five
      delta actual hdelta hdeltaActual hactualSmall
      first second
      hfirstLine.vertical hsecondLine.vertical
      hfirstBase hsecondBase parent
      hfirstParent hsecondParent
  have hdistance :=
    wz1PaperLineDistance_le_of_tubeParams_close
      hfirstLine hsecondLine
      (mul_nonneg (by norm_num) hactual.le)
      hparameters.1 hparameters.2.1
      hparameters.2.2.1 hparameters.2.2.2
  convert hdistance using 1 <;> ring

/--
Every member of one complete actual fiber is covered by the prescribed-scale
enlargement of a representative from that same complete fiber.
-/
theorem wz2_pure_actual_fullFiber_lineCoveredBy_representative
    {delta actual caller : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily actual}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hdelta : 0 < delta)
    (hdeltaActual : delta ≤ actual)
    (hactualSmall : actual ≤ 1 / 10000)
    (hactualCaller : 1200000 * actual ≤ caller)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (parent : Fin coarse.card)
    (representative : Fin fine.card)
    (hrepresentative :
      representative ∈
        wz2PaperOrdinaryFullFiberIndices fine coarse parent) :
    ∀ source,
      source ∈
          wz2PaperOrdinaryFullFiberIndices fine coarse parent →
        WZ1PaperTubeCovers
          (fine.tube source)
          (wz2PaperRelabelTube (targetScale := caller)
            (wz2PaperCanonicalLineTube
              (fine.tube representative))) := by
  intro source hsource
  have hsourceContainment :
      (fine.tube source).carrier ⊆
        (coarse.tube parent).carrier :=
    (mem_wz2PaperOrdinaryFullFiberIndices_iff
      parent source).mp hsource
  have hrepresentativeContainment :
      (fine.tube representative).carrier ⊆
        (coarse.tube parent).carrier :=
    (mem_wz2PaperOrdinaryFullFiberIndices_iff
      parent representative).mp hrepresentative
  have hdistance :
      wz1PaperLineDistance
          (fine.tube source)
          (fine.tube representative) ≤
        600000 * actual :=
    wz1PaperLineDistance_le_of_common_actual_parent
      hdelta hdeltaActual hactualSmall
      (fineLine source) (fineLine representative)
      (fineBase source) (fineBase representative)
      hsourceContainment hrepresentativeContainment
  have hcanonical :
      wz1PaperLineDistance
          (fine.tube source)
          (wz2PaperCanonicalLineTube
            (fine.tube representative)) =
        wz1PaperLineDistance
          (fine.tube source)
          (fine.tube representative) := by
    unfold wz1PaperLineDistance
    rw [
      wz2PaperCanonicalLineTube_axisZero
        (fineLine representative),
      wz2PaperCanonicalLineTube_paperDirection
        (fineLine representative)
    ]
  unfold WZ1PaperTubeCovers
  rw [wz2PaperRelabelTube_lineDistance_right]
  rw [hcanonical]
  linarith

end Kakeya.Assouad

end
