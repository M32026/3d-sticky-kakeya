import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalCapAbsorption
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFiberDensityAbsorption
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFiberQuantitativeAbsorption
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalLossHierarchy
import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentUniformAbsorption

/-!
# Joint paper parameter selection for the final `prop: sticky` argument

The Assouad paper fixes the requested output error first.  It then invokes
the critical-volume principle with a much smaller structural budget, chooses
the source preparation losses after the returned structural loss is known,
and finally takes the physical scale sufficiently small to absorb all fixed
and polylogarithmic losses.

This record packages that quantifier order.  In particular, the component,
cap, and final-fiber absorption hypotheses used by the closed downstream
modules are simultaneously satisfiable; they are not independent
assumptions on the input family.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFinalParameterSelectionData
    (sigma outputLoss : ℝ)
    (totalExponent globalBalancingExponent : ℕ) where
  critical :
    WZ2PaperCriticalFloorSelectionData
      sigma
      (wz2PaperCriticalFloorLoss outputLoss)
      (wz2PaperInternalStrongLoss outputLoss)
  hierarchy :
    WZ2PaperFinalLossHierarchyData
      outputLoss critical.structuralLoss
  oneParent :
    WZ2PaperPreparedOneParentUniformAbsorptionData
      hierarchy.sourceLoss hierarchy.stableLoss
      (wz2PaperCriticalFloorLoss outputLoss)
      (wz2PaperInternalStrongLoss outputLoss)
      outputLoss critical
  component :
    WZ2PaperFinalComponentAbsorptionData
      hierarchy.sourceLoss critical.structuralLoss
      hierarchy.capLoss hierarchy.componentLoss outputLoss
      totalExponent
  density :
    WZ2PaperFinalFiberDensityAbsorptionData
      hierarchy.sourceLoss critical.structuralLoss hierarchy.capLoss
      hierarchy.componentLoss hierarchy.fiberDensityLoss outputLoss
      totalExponent
  cap :
    WZ2PaperFinalCapAbsorptionData
      hierarchy.internalStrongLoss hierarchy.capLoss
      globalBalancingExponent
  fiber :
    WZ2PaperFinalFiberGeometricAbsorptionData
      hierarchy.fiberDensityLoss hierarchy.finalStrongLoss

theorem wz2_paper_final_parameter_selection
    (sigma outputLoss : ℝ)
    (totalExponent globalBalancingExponent : ℕ)
    (hOutputPos : 0 < outputLoss)
    (hOutputOne : outputLoss ≤ 1)
    (criticalFloor : HasWZ2PaperCriticalVolumeFloor sigma) :
    Nonempty
      (WZ2PaperFinalParameterSelectionData
        sigma outputLoss totalExponent globalBalancingExponent) := by
  have hCriticalFloorPos :
      0 < wz2PaperCriticalFloorLoss outputLoss := by
    dsimp only [wz2PaperCriticalFloorLoss]
    positivity
  have hInternalPos :
      0 < wz2PaperInternalStrongLoss outputLoss := by
    dsimp only [wz2PaperInternalStrongLoss]
    positivity
  rcases
      wz2_paper_critical_floor_selection
        sigma
        (wz2PaperCriticalFloorLoss outputLoss)
        (wz2PaperInternalStrongLoss outputLoss)
        hCriticalFloorPos hInternalPos criticalFloor
    with ⟨critical⟩
  rcases
      wz2_paper_final_loss_hierarchy
        outputLoss critical.structuralLoss
        hOutputPos hOutputOne critical.structuralLoss_pos
        critical.structuralLoss_le
    with ⟨hierarchy⟩
  have hCriticalFloorEq :
      hierarchy.criticalFloorLoss =
        wz2PaperCriticalFloorLoss outputLoss :=
    hierarchy.criticalFloorLoss_eq
  have hInternalEq :
      hierarchy.internalStrongLoss =
        wz2PaperInternalStrongLoss outputLoss :=
    hierarchy.internalStrongLoss_eq
  have hCriticalInternal :
      wz2PaperCriticalFloorLoss outputLoss <
        wz2PaperInternalStrongLoss outputLoss := by
    simpa [hCriticalFloorEq, hInternalEq] using
      hierarchy.critical_internal
  have hInternalBudget :
      3 * wz2PaperInternalStrongLoss outputLoss ≤ outputLoss := by
    simpa [hInternalEq] using hierarchy.internal_output_budget
  rcases
      wz2_prop_sticky_prepared_one_parent_uniform_absorption
        critical
        hCriticalFloorPos
        hCriticalInternal
        hInternalBudget
        hierarchy.sourceLoss hierarchy.stableLoss
        hierarchy.sourceLoss_pos hierarchy.source_stable
        hierarchy.stable_structural_square
    with ⟨oneParent⟩
  rcases
      wz2_paper_final_component_absorption
        hierarchy.sourceLoss critical.structuralLoss
        hierarchy.capLoss hierarchy.componentLoss outputLoss
        totalExponent hierarchy.component_gap_pos
    with ⟨component⟩
  rcases
      wz2_paper_final_fiber_density_absorption
        hierarchy.sourceLoss critical.structuralLoss
        hierarchy.capLoss hierarchy.componentLoss
        hierarchy.fiberDensityLoss outputLoss
        totalExponent
        (by
          simpa [wz2PaperFinalFiberDensityGap] using
            hierarchy.density_gap_pos)
    with ⟨density⟩
  rcases
      wz2_paper_final_cap_absorption
        hierarchy.internalStrongLoss hierarchy.capLoss
        globalBalancingExponent hierarchy.internal_cap
        hierarchy.capLoss_pos
    with ⟨cap⟩
  rcases
      wz2_paper_final_fiber_geometric_absorption
        hierarchy.fiberDensityLoss hierarchy.finalStrongLoss
        hierarchy.density_final
    with ⟨fiber⟩
  exact
    ⟨{
      critical := critical
      hierarchy := hierarchy
      oneParent := oneParent
      component := component
      density := density
      cap := cap
      fiber := fiber
    }⟩

end Kakeya.Assouad

end
