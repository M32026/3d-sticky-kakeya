import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientInsertedCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricFiberRescaling
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricCoreRescaledPhysicalCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BoundedOrdinaryRescaledLocality

/-!
# Proposition 6.2 quotient final-fiber CWA

This module constructs the public nearby-scale CWA on every final genuine
metric fiber of one fixed quotient metric-core output.  The lower requested
routes are explicit inputs, but their source family is definitionally the
same final metric fiber.  No new family selection is performed.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62ProxyQuotientFiberRouteData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (sourceConstant : ENNReal) where
  rho_le_one : rho ≤ 1
  delta_pos : 0 < delta
  scale_separation : 100 * delta ≤ rho
  source_constant_finite :
    WZ2PaperFiniteErrorConstant sourceConstant
  requested_route :
    ∀ parent :
        Fin metricCore.restriction.coarseSelected.family.card,
      ∀ requested : WZ2PaperRequestedScale (delta / rho),
        (∃ (actual : ℝ)
          (scaleData :
            WZ2PaperPureScaleCoverData
              (metricCore.restriction.metricFiberSource parent).family
              actual sourceConstant),
            100 * delta ≤ actual ∧
            actual ≤ rho ∧
            requested.1 ≤ actual / rho ∧
            ENNReal.ofReal (actual / rho) <
              ((81000000 : ENNReal) * sourceConstant) *
                ENNReal.ofReal requested.1 ∧
            WZ1PaperIsLineClass scaleData.coarse ∧
            (∀ source,
              WZ1PaperTubeCovers
                ((metricCore.restriction.metricFiberSource parent).family.tube
                  source)
                (scaleData.coarse.tube
                  (scaleData.cover.parent source))) ∧
            (∀ middle,
              WZ2PaperDilatedTubeCovers 2
                (scaleData.coarse.tube middle)
                (metricCore.restriction.coarseSelected.family.tube parent)) ∧
            (∀ first second, first ≠ second →
              wz2PaperLiteralSourceSeparationFactor * actual <
                wz1PaperLineDistance
                  (scaleData.coarse.tube first)
                  (scaleData.coarse.tube second)) ∧
            WZ2PaperOrdinaryNestedTargetLocalization
              (metricCore.restriction.metricFiberSource parent).family
              scaleData.coarse
              (metricCore.restriction.coarseSelected.family.tube parent)
              metricCore.metric.metricInput.rho_pos) ∨
        (4 : ENNReal) <
          ((81000000 : ENNReal) * sourceConstant) *
            ENNReal.ofReal requested.1

structure PureWZ2Prop62ProxyQuotientFiberCWAData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (sourceConstant : ENNReal) where
  input :
    ∀ parent :
        Fin metricCore.restriction.coarseSelected.family.card,
      PureWZ2Prop62MetricFiberRescalingInput
        metricCore.restriction.section6Cover parent sourceConstant
  sourceIndices_eq :
    ∀ parent,
      (input parent).sourceIndices =
        wz2PaperFullFiberIndices
          metricCore.restriction.fineSelected.family
          metricCore.restriction.coarseSelected.family parent
  sourceFamily_eq :
    ∀ parent,
      (input parent).sourceFamily =
        (metricCore.restriction.metricFiberSource parent).family
  public_cwa :
    ∀ parent,
      WZ2PaperPureCWAAtNearbyScales
        (input parent).certificate.publicFamily
        ((81000000 : ENNReal) * sourceConstant)

noncomputable def pureWZ2_prop62_proxy_quotient_fiber_cwa
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 4)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (rhoLeOne : rho ≤ 1)
    (deltaPos : 0 < delta)
    (scaleSeparation : 100 * delta ≤ rho)
    (sourceConstant : ENNReal)
    (sourceConstantFinite :
      WZ2PaperFiniteErrorConstant sourceConstant)
    (insertedConstantLe :
      pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        metricCore.quotientDensityLoss ≤ sourceConstant)
    (sourceStronglySeparated :
      ∀ parent :
          Fin metricCore.restriction.coarseSelected.family.card,
        ∀ first second :
            Fin
              (metricCore.restriction.metricFiberSource parent).family.card,
          first ≠ second →
            wz2PaperLiteralSourceSeparationFactor * delta <
              wz1PaperLineDistance
                ((metricCore.restriction.metricFiberSource parent).family.tube
                  first)
                ((metricCore.restriction.metricFiberSource parent).family.tube
                  second))
    (route :
      PureWZ2Prop62ProxyQuotientFiberRouteData
        metricCore sourceConstant) :
    PureWZ2Prop62ProxyQuotientFiberCWAData
      metricCore sourceConstant := by
  let input :
      ∀ parent :
          Fin metricCore.restriction.coarseSelected.family.card,
        PureWZ2Prop62MetricFiberRescalingInput
          metricCore.restriction.section6Cover parent sourceConstant :=
    fun parent => by
      let sourceIndices :=
        wz2PaperFullFiberIndices
          metricCore.restriction.fineSelected.family
          metricCore.restriction.coarseSelected.family parent
      let source :=
        metricCore.restriction.metricFiberSource parent
      let sourceEquiv :
          Fin source.family.card ≃ sourceIndices :=
        (sourceIndices.orderIsoOfFin rfl).toEquiv
      have sourceLine :
          WZ1PaperIsLineClass source.family :=
        metricCore.restriction.section6Cover.fine_line_class.subfamily
          source.toTubeSubfamily
      have sourceCovered :
          ∀ index,
            WZ1PaperTubeCovers
              (source.family.tube index)
              (metricCore.restriction.coarseSelected.family.tube parent) := by
        intro index
        rw [source.tube_eq]
        exact
          (mem_wz2PaperFullFiberIndices_iff parent
            (source.embedding index)).mp
            (Finset.orderEmbOfFin_mem sourceIndices rfl index)
      have targetLocality :
          ∀ index,
            ‖wz2PaperTubeMidpoint
              ((wz2PaperLiteralOrdinaryRescaledFamily
                source.family
                (metricCore.restriction.coarseSelected.family.tube parent)
                rhoPos).tube index)‖ ≤ 3 := by
        intro index
        exact
          wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_three_of_boundedBase
            rhoPos rhoLeOne
            (source.family.tube index)
            (metricCore.restriction.coarseSelected.family.tube parent)
            (sourceLine index)
            (by
              rw [source.tube_eq,
                metricCore.restriction.fineSelected.tube_eq,
                metricCore.metric.mesh.complete.selectedFine.tube_eq]
              exact fineBase _)
            (sourceCovered index)
      have physicalCWA :
          WZ2PaperBodyConvexWolffBound
            (wz2PaperLiteralOrdinaryRescaledFamily
              source.family
              (metricCore.restriction.coarseSelected.family.tube parent)
              rhoPos).toBodyFamily
            sourceConstant := by
        let fiber :=
          wz2PaperFullFiberIndices
            metricCore.restriction.fineSelected.family
            metricCore.restriction.coarseSelected.family parent
        let literalBodies :=
          metricCore.restriction.metricFiberLiteralImageBodies
            rhoPos parent
        have literalCWA :
            WZ2PaperBodyConvexWolffBound
              literalBodies sourceConstant := by
          intro convexSet convex
          let ambientPredicate :
              Fin metricCore.restriction.fineSelected.family.card → Prop :=
            fun sourceIndex =>
              wz2PaperLiteralUnitRescalingMap
                  (metricCore.restriction.coarseSelected.family.tube parent)
                  rhoPos ''
                (metricCore.restriction.fineSelected.family.tube
                  sourceIndex).carrier ⊆ convexSet
          let localPredicate : Fin source.family.card → Prop :=
            fun sourceIndex =>
              (literalBodies.body sourceIndex).carrier ⊆ convexSet
          have filteredImage :
              Finset.image source.embedding
                  (Finset.univ.filter localPredicate) =
                fiber.filter ambientPredicate := by
            ext ambientSource
            constructor
            · intro ambientMem
              rcases Finset.mem_image.mp ambientMem with
                ⟨sourceIndex, sourceMem, rfl⟩
              have sourceData := Finset.mem_filter.mp sourceMem
              apply Finset.mem_filter.mpr
              constructor
              · exact
                  Finset.orderEmbOfFin_mem fiber rfl sourceIndex
              · change
                  wz2PaperLiteralUnitRescalingMap
                      (metricCore.restriction.coarseSelected.family.tube parent)
                      rhoPos ''
                    (metricCore.restriction.fineSelected.family.tube
                      (source.embedding sourceIndex)).carrier ⊆
                    convexSet
                dsimp only [localPredicate, literalBodies,
                  PureWZ2Prop62MetricCoreRestrictionData.metricFiberLiteralImageBodies]
                  at sourceData
                exact sourceData.2
            · intro ambientMem
              have ambientData := Finset.mem_filter.mp ambientMem
              let equivalence : Fin fiber.card ≃ fiber :=
                (fiber.orderIsoOfFin rfl).toEquiv
              let sourceIndex : Fin source.family.card :=
                equivalence.symm ⟨ambientSource, ambientData.1⟩
              have sourceEq :
                  source.embedding sourceIndex = ambientSource := by
                exact congrArg Subtype.val
                  (equivalence.apply_symm_apply
                    ⟨ambientSource, ambientData.1⟩)
              apply Finset.mem_image.mpr
              refine
                ⟨sourceIndex,
                  Finset.mem_filter.mpr
                    ⟨Finset.mem_univ sourceIndex, ?_⟩,
                  sourceEq⟩
              change
                wz2PaperLiteralUnitRescalingMap
                    (metricCore.restriction.coarseSelected.family.tube parent)
                    rhoPos ''
                  (source.family.tube sourceIndex).carrier ⊆
                  convexSet
              rw [source.tube_eq, sourceEq]
              exact ambientData.2
          have filteredCard :
              (Finset.univ.filter localPredicate).card =
                (fiber.filter ambientPredicate).card := by
            rw [← filteredImage]
            exact
              (Finset.card_image_of_injective _
                source.embedding.injective).symm
          have sourceCard :
              source.family.card = fiber.card := rfl
          have raw :=
            metricCore.restrictedInsertedFiberCWA
              fineLine
              (fun ambientSource =>
                (fineBase ambientSource).trans (by norm_num))
              rhoPos widthPos packetScaleLeRho
              sixWidthLe parent
          change
            ((Finset.univ.filter localPredicate).card : ENNReal) ≤
              sourceConstant * volume convexSet *
                (source.family.card : ENNReal)
          rw [filteredCard, sourceCard]
          exact (raw convexSet convex).trans <| by
            gcongr
        let target :=
          (wz2PaperLiteralOrdinaryRescaledFamily
            source.family
            (metricCore.restriction.coarseSelected.family.tube parent)
            rhoPos).toBodyFamily
        apply WZ2PaperBodyConvexWolffBound.of_pointwise_subset
          (source := literalBodies) (target := target) rfl
        · intro index
          change
            wz2PaperLiteralUnitRescalingMap
                (metricCore.restriction.coarseSelected.family.tube parent)
                rhoPos ''
              (source.family.tube index).carrier ⊆
            (wz2PaperLiteralOrdinaryRescaledTube
              (source.family.tube index)
              (metricCore.restriction.coarseSelected.family.tube parent)
              rhoPos).carrier
          exact
            wz2PaperLiteral_image_carrier_subset_ordinary
              deltaPos
              (source.family.tube index)
              (metricCore.restriction.coarseSelected.family.tube parent)
              rhoPos rhoLeOne (sourceCovered index)
        · exact literalCWA
      exact
        {
          rho_pos := rhoPos
          rho_le_one := rhoLeOne
          delta_pos := deltaPos
          scale_separation := scaleSeparation
          sourceIndices := sourceIndices
          sourceIndices_eq := rfl
          sourceIndices_nonempty := by
            rcases
                metricCore.restriction.section6Cover.parent_hit parent
              with ⟨sourceIndex, sourceCovered⟩
            exact
              ⟨sourceIndex,
                (mem_wz2PaperFullFiberIndices_iff
                  parent sourceIndex).mpr sourceCovered⟩
          sourceFamily := source.family
          sourceEquiv := sourceEquiv
          source_tube_eq := by
            intro index
            rfl
          source_line_class := sourceLine
          anchor_line_class :=
            metricCore.restriction.section6Cover.coarse_line_class parent
          source_covered := sourceCovered
          source_strongly_separated :=
            sourceStronglySeparated parent
          source_constant_finite := sourceConstantFinite
          target_locality := targetLocality
          rescaled_physical_cwa := physicalCWA
          requested_route := route.requested_route parent
        }
  exact
    {
      input := input
      sourceIndices_eq := by
        intro parent
        rfl
      sourceFamily_eq := by
        intro parent
        rfl
      public_cwa := by
        intro parent
        exact (input parent).publicPureCWA
    }

end Kakeya.Assouad

end
