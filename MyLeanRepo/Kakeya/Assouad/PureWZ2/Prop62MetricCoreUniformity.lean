import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperSchedule

/-!
# Proposition 6.2 metric parents: final-core fiber uniformity

The preliminary metric fibers are globally cardinality-comparable.  The
inserted auxiliary level is exactly the metric-fiber partition, so one-pass
node density gives a lower bound for every surviving core fiber.  Combining
that lower bound with the trivial upper bound transfers uniformity to the
final core with one factor `densityLoss`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem PureWZ2Prop62AuxiliaryLevel.ambientAuxiliaryFiber_le_densityLoss_core
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule fine ambientConstant scaleWindow}
    {Aux : Type}
    [Fintype Aux] [DecidableEq Aux]
    (auxiliary : PureWZ2Prop62AuxiliaryLevel schedule Aux)
    {selected : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty)
    (label : Aux)
    (coreFiberNonempty :
      (auxiliary.coreIndices selected ∩
        auxiliary.auxiliaryFiber label).Nonempty) :
    ((auxiliary.auxiliaryFiber label).card : ENNReal) ≤
      auxiliary.densityLoss selected *
        ((auxiliary.coreIndices selected ∩
          auxiliary.auxiliaryFiber label).card : ENNReal) := by
  have selectedPos : 0 < (selected.card : ENNReal) := by
    exact_mod_cast Finset.card_pos.mpr selectedNonempty
  have selectedTop : (selected.card : ENNReal) ≠ ⊤ := by
    simp
  have densityNat :=
    (auxiliary.coreOutput selected).auxiliary_density
      label <| by
        simpa only [
          PureWZ2Prop62AuxiliaryLevel.coreIndices
        ] using coreFiberNonempty
  have densityENN :
      (selected.card : ENNReal) *
          ((auxiliary.auxiliaryFiber label).card : ENNReal) ≤
        (2 ^ (schedule.levelCount + 1) : ENNReal) *
          ((auxiliary.coreIndices selected ∩
            auxiliary.auxiliaryFiber label).card : ENNReal) *
          fine.enncard := by
    have densityCast :
        ((selected.card *
          (auxiliary.auxiliaryFiber label).card : ℕ) : ENNReal) ≤
          ((2 ^ (schedule.levelCount + 1) *
            ((auxiliary.coreOutput selected).core ∩
              auxiliary.auxiliaryFiber label).card *
            fine.card : ℕ) : ENNReal) := by
      exact_mod_cast densityNat
    simpa only [
      PureWZ2Prop62AuxiliaryLevel.coreIndices,
      Kakeya.Streamlined.TubeFamily.enncard,
      Nat.cast_mul,
      Nat.cast_pow,
      Nat.cast_ofNat
    ] using densityCast
  calc
    ((auxiliary.auxiliaryFiber label).card : ENNReal) =
        (selected.card : ENNReal)⁻¹ *
          ((selected.card : ENNReal) *
            ((auxiliary.auxiliaryFiber label).card : ENNReal)) := by
      rw [← mul_assoc,
        ENNReal.inv_mul_cancel selectedPos.ne' selectedTop, one_mul]
    _ ≤
        (selected.card : ENNReal)⁻¹ *
          ((2 ^ (schedule.levelCount + 1) : ENNReal) *
          ((auxiliary.coreIndices selected ∩
            auxiliary.auxiliaryFiber label).card : ENNReal) *
          fine.enncard) := by
      gcongr
    _ =
        auxiliary.densityLoss selected *
          ((auxiliary.coreIndices selected ∩
            auxiliary.auxiliaryFiber label).card : ENNReal) := by
      simp only [PureWZ2Prop62AuxiliaryLevel.densityLoss]
      ring

theorem PureWZ2Prop62MetricPacketOutput.core_metricFiber_uniform
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
    {selected : Finset (Fin metric.selectedFine.card)}
    (selectedNonempty : selected.Nonempty)
    (baseConstant : ENNReal)
    (ambientUniform :
      ∀ first second,
        ((wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents first).card :
          ENNReal) ≤
          baseConstant *
            ((wz2PaperFullFiberIndices
              metric.selectedFine metric.metricParents second).card :
              ENNReal))
    (first second : Fin metric.metricParents.card)
    (secondCoreNonempty :
      (auxiliary.coreIndices selected ∩
        wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents second).Nonempty) :
    ((auxiliary.coreIndices selected ∩
        wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents first).card :
        ENNReal) ≤
      (baseConstant * auxiliary.densityLoss selected) *
        ((auxiliary.coreIndices selected ∩
          wz2PaperFullFiberIndices
            metric.selectedFine metric.metricParents second).card :
          ENNReal) := by
  have firstSubset :
      auxiliary.coreIndices selected ∩
          wz2PaperFullFiberIndices
            metric.selectedFine metric.metricParents first ⊆
        wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents first :=
    Finset.inter_subset_right
  have firstLe :
      ((auxiliary.coreIndices selected ∩
        wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents first).card :
          ENNReal) ≤
        ((wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents first).card :
          ENNReal) := by
    exact_mod_cast Finset.card_le_card firstSubset
  have secondAuxiliary :
      auxiliary.auxiliaryFiber second =
        wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents second :=
    auxiliary.auxiliaryFiber_eq_metricFiber metric label_eq second
  have secondLower :=
    auxiliary.ambientAuxiliaryFiber_le_densityLoss_core
      selectedNonempty second <| by
        simpa only [secondAuxiliary] using secondCoreNonempty
  rw [secondAuxiliary] at secondLower
  calc
    ((auxiliary.coreIndices selected ∩
        wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents first).card :
        ENNReal) ≤
      ((wz2PaperFullFiberIndices
        metric.selectedFine metric.metricParents first).card :
        ENNReal) := firstLe
    _ ≤
      baseConstant *
        ((wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents second).card :
          ENNReal) :=
      ambientUniform first second
    _ ≤
      baseConstant *
        (auxiliary.densityLoss selected *
          ((auxiliary.coreIndices selected ∩
            wz2PaperFullFiberIndices
              metric.selectedFine metric.metricParents second).card :
            ENNReal)) := by
      gcongr
    _ =
      (baseConstant * auxiliary.densityLoss selected) *
        ((auxiliary.coreIndices selected ∩
          wz2PaperFullFiberIndices
            metric.selectedFine metric.metricParents second).card :
          ENNReal) := by ring

theorem PureWZ2Prop62MetricCoreRestrictionData.fullFiber_uniform
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
    {selected : Finset (Fin metric.selectedFine.card)}
    (selectedNonempty : selected.Nonempty)
    (restriction :
      PureWZ2Prop62MetricCoreRestrictionData
        metric.section6Cover
        (auxiliary.coreIndices selected))
    (baseConstant : ENNReal)
    (ambientUniform :
      ∀ first second,
        ((wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents first).card :
          ENNReal) ≤
          baseConstant *
            ((wz2PaperFullFiberIndices
              metric.selectedFine metric.metricParents second).card :
              ENNReal)) :
    ∀ first second,
      ((wz2PaperFullFiberIndices
        restriction.fineSelected.family
        restriction.coarseSelected.family first).card :
        ENNReal) ≤
        (baseConstant * auxiliary.densityLoss selected) *
          ((wz2PaperFullFiberIndices
            restriction.fineSelected.family
            restriction.coarseSelected.family second).card :
            ENNReal) := by
  intro first second
  have firstCard :
      (wz2PaperFullFiberIndices
        restriction.fineSelected.family
        restriction.coarseSelected.family first).card =
        (auxiliary.coreIndices selected ∩
          wz2PaperFullFiberIndices
            metric.selectedFine metric.metricParents
              (restriction.coarseSelected.embedding first)).card := by
    rw [← restriction.fiber_image_eq first]
    exact
      (Finset.card_image_of_injective _
        restriction.fineSelected.embedding.injective).symm
  have secondCard :
      (wz2PaperFullFiberIndices
        restriction.fineSelected.family
        restriction.coarseSelected.family second).card =
        (auxiliary.coreIndices selected ∩
          wz2PaperFullFiberIndices
            metric.selectedFine metric.metricParents
              (restriction.coarseSelected.embedding second)).card := by
    rw [← restriction.fiber_image_eq second]
    exact
      (Finset.card_image_of_injective _
        restriction.fineSelected.embedding.injective).symm
  have secondNonempty :
      (auxiliary.coreIndices selected ∩
        wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents
            (restriction.coarseSelected.embedding second)).Nonempty := by
    rcases restriction.lineCover.parent_surjective second with
      ⟨source, parentEq⟩
    have sourceFiber :
        source ∈
          wz2PaperFullFiberIndices
            restriction.fineSelected.family
            restriction.coarseSelected.family second :=
      (mem_wz2PaperFullFiberIndices_iff second source).mpr <| by
        rw [← parentEq]
        exact restriction.lineCover.parent_covers source
    rw [← restriction.fiber_image_eq second]
    exact
      ⟨restriction.fineSelected.embedding source,
        Finset.mem_image.mpr ⟨source, sourceFiber, rfl⟩⟩
  rw [firstCard, secondCard]
  exact
    metric.core_metricFiber_uniform
      auxiliary label_eq selectedNonempty baseConstant ambientUniform
      (restriction.coarseSelected.embedding first)
      (restriction.coarseSelected.embedding second)
      secondNonempty

end Kakeya.Assouad

end
