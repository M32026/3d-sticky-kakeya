import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalRequestedCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCentered
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SameCarrierGrainRetype
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GrainSubfamilyRestriction

/-!
# Analytic restriction to the direct half-offset final target

The requested-scale CWA construction ends with a genuine subfamily of the
cleanup-selected terminal family.  This file attaches the inherited cubical,
line-class, carrier-containment, and grain certificates to that literal final
family and to the literal restriction of its pre-target shading.

No density assertion is made here.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry
namespace PureWZ2ExternalWeightRegularizationData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- The same-carrier witness used to retype terminal local grains to the
canonical centered representatives. -/
private def finalCenteredCubicalGrainRetype
    (terminal : commonSource.TerminalGeometry) :
    PureWZ2SameCarrierGrainRetype terminal.family terminal.centeredFamily
      terminal.cubicalShading terminal.centeredCubicalShading where
  indexEquiv := Equiv.refl _
  carrier_eq := fun _ => rfl
  direction_eq_or_neg := by
    intro index
    change wz1PaperDirection (terminal.family.tube index) =
        (terminal.family.tube index).direction ∨
      wz1PaperDirection (terminal.family.tube index) =
        -(terminal.family.tube index).direction
    unfold wz1PaperDirection
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The literal cubical shading on the final jointly regularized target. -/
noncomputable def DirectHalfOffsetTerminalRequestedCWAData.finalShading
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant) :
    WZ1PaperTubeShading data.finalTarget :=
  restrictPaperShading data.finalTargetSubfamily
    (halfOffsetTerminalCleanupTargetShading
      (commonSource := commonSource) regularization)

/-- Cubicality survives the last two finite regularizations. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.finalShading_cubical
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant) :
    WZ1PaperIsCubicalShading data.finalShading :=
  restrictPaperShading_cubical data.finalTargetSubfamily
    (halfOffsetTerminalCleanupTargetSubfamily_cubical
      (commonSource := commonSource) regularization)

/-- The literal final target remains in the paper line class. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.finalTarget_line_class
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant) :
    WZ1PaperIsLineClass data.finalTarget :=
  ((TerminalGeometry.line_class_subfamily commonSource terminal cleanup.family).subfamily
    (halfOffsetTerminalCleanupTargetSubfamily
      (commonSource := commonSource) regularization)).subfamily
        data.finalTargetSubfamily

/-- Every ordinary carrier of the final centered target is contained in its
paper carrier. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.finalTarget_ordinary_carrier_subset_paper
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant)
    (index : Fin data.finalTarget.card) :
    (data.finalTarget.tube index).carrier ⊆
      wz1PaperTubeCarrier (data.finalTarget.tube index) := by
  rw [data.finalTargetSubfamily.tube_eq,
    (halfOffsetTerminalCleanupTargetSubfamily
      (commonSource := commonSource) regularization).tube_eq,
    cleanup.family.tube_eq]
  exact centeredFamily_ordinary_carrier_subset_paper commonSource terminal _

/-- The literal final shading is contained in the ambient terminal cubical
shading through the cleanup, source-regularization, and final selections. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.finalShading_union_subset_terminal
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant) :
    data.finalShading.union ⊆ terminal.cubicalShading.union := by
  intro point hpoint
  have hpreTarget : point ∈
      (halfOffsetTerminalCleanupTargetShading
        (commonSource := commonSource) regularization).union :=
    restrictPaperShading_union_subset data.finalTargetSubfamily _ hpoint
  have hcleanup : point ∈ cleanup.shading.union :=
    restrictPaperShading_union_subset
      (halfOffsetTerminalCleanupTargetSubfamily
        (commonSource := commonSource) regularization) cleanup.shading hpreTarget
  have hcentered : point ∈ terminal.centeredCubicalShading.union :=
    restrictPaperShading_union_subset cleanup.family
      terminal.centeredCubicalShading hcleanup
  rw [centeredCubicalShading_union commonSource terminal] at hcentered
  exact hcentered

/-- Any ambient terminal finite-slice global-AD certificate, in particular
one carrying the final absorbed constant, restricts to the literal final
shading without changing its slope or constant. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.finalShading_global_ad
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant C : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant)
    (slope : ℝ → ℝ)
    (ambientGlobalAD : ∀ z : ℝ, ∀ _ : z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice terminal.cubicalShading.union z))
        terminal.targetDelta (1 - sigma) C) :
    ∀ z : ℝ, ∀ _ : z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice data.finalShading.union z))
        terminal.targetDelta (1 - sigma) C := by
  intro z hz
  exact (ambientGlobalAD z hz).weaken_subset <| by
    apply Set.image_mono
    intro point hpoint
    exact ⟨data.finalShading_union_subset_terminal hpoint.1, hpoint.2⟩

/-- Restrict an ambient terminal global-grain certificate to the literal
final target.  In particular, an ambient finite-slice proof with its final
constant is inherited solely by subset restriction. -/
noncomputable def DirectHalfOffsetTerminalRequestedCWAData.finalGlobalGrains
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant C : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant)
    (ambient : PureWZ2C2GlobalGrainData terminal.cubicalShading sigma C) :
    PureWZ2C2GlobalGrainData data.finalShading sigma C :=
  (((retypeCubicalGlobalGrains commonSource terminal ambient).subfamily
    cleanup.family).subfamily
    (halfOffsetTerminalCleanupTargetSubfamily
      (commonSource := commonSource) regularization)).subfamily
        data.finalTargetSubfamily

/-- Restrict terminal local grains along the exact carrier-provenance chain:
first retype the terminal family to its centered representatives, then pass
through the cleanup, source-regularization, and final requested-CWA
subfamilies. -/
noncomputable def DirectHalfOffsetTerminalRequestedCWAData.finalLocalGrains
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant C : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant)
    (ambient : PureWZ2LocalGrainData terminal.cubicalShading sigma C) :
    PureWZ2LocalGrainData data.finalShading sigma C :=
  (((ambient.retypeSameCarrier
    (finalCenteredCubicalGrainRetype terminal)).subfamily cleanup.family).subfamily
    (halfOffsetTerminalCleanupTargetSubfamily
      (commonSource := commonSource) regularization)).subfamily
        data.finalTargetSubfamily

end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
