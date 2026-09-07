import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricCoreInsertedCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricFiberRescaling

/-!
# Proposition 6.2 metric-fiber physical CWA after literal rescaling

The inserted estimate counts literal affine images of the exact final metric
fiber.  The canonical ordinary public tube contains the corresponding literal
image pointwise.  Therefore ordinary public containment in a convex set
implies literal-image containment in that set, and the inserted estimate gives
physical body CWA on the canonical public family without changing the
constant.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62MetricCoreRestrictionData

noncomputable def metricFiberSource
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambient : PureWZ2Section6Cover fine coarse}
    {core : Finset (Fin fine.card)}
    (restriction :
      PureWZ2Prop62MetricCoreRestrictionData ambient core)
    (parent : Fin restriction.coarseSelected.family.card) :
    WZ2PaperPureTubeSubfamily restriction.fineSelected.family :=
  WZ2PaperPureTubeSubfamily.fromFinset
    restriction.fineSelected.family
    (wz2PaperFullFiberIndices
      restriction.fineSelected.family
      restriction.coarseSelected.family parent)

noncomputable def metricFiberLiteralImageBodies
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambient : PureWZ2Section6Cover fine coarse}
    {core : Finset (Fin fine.card)}
    (rhoPos : 0 < rho)
    (restriction :
      PureWZ2Prop62MetricCoreRestrictionData ambient core)
    (parent : Fin restriction.coarseSelected.family.card) :
    Kakeya.Streamlined.BodyFamily where
  card := (restriction.metricFiberSource parent).family.card
  body index :=
    ⟨wz2PaperLiteralUnitRescalingMap
        (restriction.coarseSelected.family.tube parent) rhoPos ''
      ((restriction.metricFiberSource parent).family.tube index).carrier⟩

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {width M : ℝ}
    (metric :
      PureWZ2Prop62MetricPacketOutput
        (rho := rho) oldData width M)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        metric.selectedFine ambientConstant scaleWindow}
    (auxiliary :
      PureWZ2Prop62AuxiliaryLevel
        schedule (Fin metric.metricParents.card))
    (label_eq :
      ∀ source,
        auxiliary.label source =
          metric.metricInput.packetParent
            (metric.mesh.restrictedOldData.cover.parent source))
    (selected : Finset (Fin metric.selectedFine.card))
    (restriction :
      PureWZ2Prop62MetricCoreRestrictionData
        metric.section6Cover
        (auxiliary.coreIndices selected))

theorem metricFiberLiteralImageCWA
    (label_eq :
      ∀ source,
        auxiliary.label source =
          metric.metricInput.packetParent
            (metric.mesh.restrictedOldData.cover.parent source))
    (parent : Fin restriction.coarseSelected.family.card) :
    WZ2PaperBodyConvexWolffBound
      (restriction.metricFiberLiteralImageBodies
        metric.metricInput.rho_pos parent)
      (pureWZ2Prop62InsertedCWALoss rho scale C *
        auxiliary.densityLoss selected) := by
  intro convexSet convex
  let fiber :=
    wz2PaperFullFiberIndices
      restriction.fineSelected.family
      restriction.coarseSelected.family parent
  let sourceFamily := restriction.metricFiberSource parent
  let literalBodies :=
    restriction.metricFiberLiteralImageBodies
      metric.metricInput.rho_pos parent
  let ambientPredicate :
      Fin restriction.fineSelected.family.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (restriction.coarseSelected.family.tube parent)
          metric.metricInput.rho_pos ''
        (restriction.fineSelected.family.tube source).carrier ⊆ convexSet
  let localPredicate : Fin sourceFamily.family.card → Prop :=
    fun source =>
      (literalBodies.body source).carrier ⊆ convexSet
  have filteredImage :
      Finset.image sourceFamily.embedding
          (Finset.univ.filter localPredicate) =
        fiber.filter ambientPredicate := by
    ext ambientSource
    constructor
    · intro ambientMem
      rcases Finset.mem_image.mp ambientMem with
        ⟨source, sourceMem, rfl⟩
      have sourceData := Finset.mem_filter.mp sourceMem
      apply Finset.mem_filter.mpr
      constructor
      · exact
          Finset.orderEmbOfFin_mem fiber rfl source
      · change
          wz2PaperLiteralUnitRescalingMap
              (restriction.coarseSelected.family.tube parent)
              metric.metricInput.rho_pos ''
            (restriction.fineSelected.family.tube
              (sourceFamily.embedding source)).carrier ⊆ convexSet
        dsimp only [localPredicate, literalBodies,
          metricFiberLiteralImageBodies] at sourceData
        have sourcePredicate := sourceData.2
        change
          wz2PaperLiteralUnitRescalingMap
              (restriction.coarseSelected.family.tube parent)
              metric.metricInput.rho_pos ''
            (restriction.fineSelected.family.tube
              (sourceFamily.embedding source)).carrier ⊆ convexSet
          at sourcePredicate
        exact sourcePredicate
    · intro ambientMem
      have ambientData := Finset.mem_filter.mp ambientMem
      let equivalence : Fin fiber.card ≃ fiber :=
        (fiber.orderIsoOfFin rfl).toEquiv
      let source : Fin sourceFamily.family.card :=
        equivalence.symm ⟨ambientSource, ambientData.1⟩
      have sourceEq :
          sourceFamily.embedding source = ambientSource := by
        exact congrArg Subtype.val
          (equivalence.apply_symm_apply
            ⟨ambientSource, ambientData.1⟩)
      apply Finset.mem_image.mpr
      refine ⟨source, Finset.mem_filter.mpr
        ⟨Finset.mem_univ source, ?_⟩, sourceEq⟩
      change
        wz2PaperLiteralUnitRescalingMap
            (restriction.coarseSelected.family.tube parent)
            metric.metricInput.rho_pos ''
          (sourceFamily.family.tube source).carrier ⊆ convexSet
      rw [sourceFamily.tube_eq, sourceEq]
      exact ambientData.2
  have filteredCard :
      (Finset.univ.filter localPredicate).card =
        (fiber.filter ambientPredicate).card := by
    rw [← filteredImage]
    exact
      (Finset.card_image_of_injective _
        sourceFamily.embedding.injective).symm
  have sourceCard :
      sourceFamily.family.card = fiber.card := rfl
  have inserted :=
    restriction.insertedFiberCWA
      metric auxiliary label_eq selected parent convexSet convex
  change
    ((Finset.univ.filter localPredicate).card : ENNReal) ≤
      (pureWZ2Prop62InsertedCWALoss rho scale C *
        auxiliary.densityLoss selected) *
        volume convexSet * (sourceFamily.family.card : ENNReal)
  rw [filteredCard, sourceCard]
  exact inserted

theorem metricFiberRescaledPhysicalCWA
    (label_eq :
      ∀ source,
        auxiliary.label source =
          metric.metricInput.packetParent
            (metric.mesh.restrictedOldData.cover.parent source))
    (parent : Fin restriction.coarseSelected.family.card)
    (rho_le_one : rho ≤ 1) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperLiteralOrdinaryRescaledFamily
        (restriction.metricFiberSource parent).family
        (restriction.coarseSelected.family.tube parent)
        metric.metricInput.rho_pos).toBodyFamily
      (pureWZ2Prop62InsertedCWALoss rho scale C *
        auxiliary.densityLoss selected) := by
  let source :=
    restriction.metricFiberLiteralImageBodies
      metric.metricInput.rho_pos parent
  let target :=
    (wz2PaperLiteralOrdinaryRescaledFamily
      (restriction.metricFiberSource parent).family
      (restriction.coarseSelected.family.tube parent)
      metric.metricInput.rho_pos).toBodyFamily
  apply WZ2PaperBodyConvexWolffBound.of_pointwise_subset
    (source := source) (target := target) rfl
  · intro index
    change
      wz2PaperLiteralUnitRescalingMap
          (restriction.coarseSelected.family.tube parent)
          metric.metricInput.rho_pos ''
        ((restriction.metricFiberSource parent).family.tube index).carrier ⊆
      (wz2PaperLiteralOrdinaryRescaledTube
        ((restriction.metricFiberSource parent).family.tube index)
        (restriction.coarseSelected.family.tube parent)
        metric.metricInput.rho_pos).carrier
    exact
      wz2PaperLiteral_image_carrier_subset_ordinary
        oldData.delta_pos
        ((restriction.metricFiberSource parent).family.tube index)
        (restriction.coarseSelected.family.tube parent)
        metric.metricInput.rho_pos rho_le_one
        (by
          rw [(restriction.metricFiberSource parent).tube_eq]
          exact
            (mem_wz2PaperFullFiberIndices_iff parent
              ((restriction.metricFiberSource parent).embedding index)).mp <|
              Finset.orderEmbOfFin_mem
                (wz2PaperFullFiberIndices
                  restriction.fineSelected.family
                  restriction.coarseSelected.family parent)
                rfl index)
  · exact metricFiberLiteralImageCWA
      (metric := metric)
      (auxiliary := auxiliary)
      (selected := selected)
      (restriction := restriction)
      label_eq parent

end PureWZ2Prop62MetricCoreRestrictionData

end Kakeya.Assouad

end
