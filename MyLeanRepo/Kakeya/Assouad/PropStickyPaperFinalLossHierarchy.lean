import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalComponentAbsorption

/-!
# A paper-feasible hierarchy for the final `prop: sticky` losses

The final multiplicity comparison uses two different loss scales.  The
nearby-CWA and normalized-cap estimates are first proved with a quadratic
loss in the requested output error.  The two component floors are then
proved with a linear loss and weakened to the public output error.

The source preparation losses are chosen only after the critical-volume
principle returns its structural loss.  Taking them quadratic in that
structural loss simultaneously closes the one-parent envelope condition and
leaves a positive exponent gap in the final component absorption.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperInternalStrongLoss (outputLoss : ℝ) : ℝ :=
  outputLoss ^ 2 / 1000

def wz2PaperCriticalFloorLoss (outputLoss : ℝ) : ℝ :=
  outputLoss ^ 2 / 2000

def wz2PaperFinalCapLoss (outputLoss : ℝ) : ℝ :=
  outputLoss ^ 2 / 500

def wz2PaperFinalComponentLoss (outputLoss : ℝ) : ℝ :=
  outputLoss / 5

def wz2PaperFinalFiberDensityLoss (outputLoss : ℝ) : ℝ :=
  9 * outputLoss / 40

def wz2PaperFinalStrongLoss (outputLoss : ℝ) : ℝ :=
  outputLoss / 4

def wz2PaperFinalSourceLoss (structuralLoss : ℝ) : ℝ :=
  structuralLoss ^ 2 / 20

def wz2PaperFinalStableLoss (structuralLoss : ℝ) : ℝ :=
  structuralLoss ^ 2 / 10

structure WZ2PaperFinalLossHierarchyData
    (outputLoss structuralLoss : ℝ) where
  sourceLoss : ℝ
  sourceLoss_eq :
    sourceLoss = wz2PaperFinalSourceLoss structuralLoss
  stableLoss : ℝ
  stableLoss_eq :
    stableLoss = wz2PaperFinalStableLoss structuralLoss
  criticalFloorLoss : ℝ
  criticalFloorLoss_eq :
    criticalFloorLoss = wz2PaperCriticalFloorLoss outputLoss
  internalStrongLoss : ℝ
  internalStrongLoss_eq :
    internalStrongLoss = wz2PaperInternalStrongLoss outputLoss
  capLoss : ℝ
  capLoss_eq :
    capLoss = wz2PaperFinalCapLoss outputLoss
  capLoss_pos : 0 < capLoss
  componentLoss : ℝ
  componentLoss_eq :
    componentLoss = wz2PaperFinalComponentLoss outputLoss
  componentLoss_pos : 0 < componentLoss
  fiberDensityLoss : ℝ
  fiberDensityLoss_eq :
    fiberDensityLoss = wz2PaperFinalFiberDensityLoss outputLoss
  fiberDensityLoss_pos : 0 < fiberDensityLoss
  finalStrongLoss : ℝ
  finalStrongLoss_eq :
    finalStrongLoss = wz2PaperFinalStrongLoss outputLoss
  finalStrongLoss_pos : 0 < finalStrongLoss
  sourceLoss_pos : 0 < sourceLoss
  source_stable : sourceLoss < stableLoss
  stable_structural_square :
    5 * stableLoss < structuralLoss ^ 2
  criticalFloorLoss_pos : 0 < criticalFloorLoss
  critical_internal :
    criticalFloorLoss < internalStrongLoss
  internal_output_budget :
    3 * internalStrongLoss ≤ outputLoss
  internal_cap : internalStrongLoss < capLoss
  cap_component : capLoss < componentLoss
  density_final : fiberDensityLoss < finalStrongLoss
  final_output_budget : 3 * finalStrongLoss ≤ outputLoss
  component_gap_pos :
    0 <
      wz2PaperFinalComponentGap
        sourceLoss structuralLoss capLoss componentLoss outputLoss
  density_gap_pos :
    0 <
      outputLoss *
          (fiberDensityLoss - componentLoss - capLoss) -
        2 * sourceLoss - structuralLoss

theorem wz2_paper_final_loss_hierarchy
    (outputLoss structuralLoss : ℝ)
    (hOutputPos : 0 < outputLoss)
    (hOutputOne : outputLoss ≤ 1)
    (hStructuralPos : 0 < structuralLoss)
    (hStructuralInternal :
      structuralLoss ≤ wz2PaperInternalStrongLoss outputLoss) :
    Nonempty
      (WZ2PaperFinalLossHierarchyData outputLoss structuralLoss) := by
  let sourceLoss := wz2PaperFinalSourceLoss structuralLoss
  let stableLoss := wz2PaperFinalStableLoss structuralLoss
  let criticalFloorLoss := wz2PaperCriticalFloorLoss outputLoss
  let internalStrongLoss := wz2PaperInternalStrongLoss outputLoss
  let capLoss := wz2PaperFinalCapLoss outputLoss
  let componentLoss := wz2PaperFinalComponentLoss outputLoss
  let fiberDensityLoss := wz2PaperFinalFiberDensityLoss outputLoss
  let finalStrongLoss := wz2PaperFinalStrongLoss outputLoss
  have hOutputSquarePos : 0 < outputLoss ^ 2 := sq_pos_of_pos hOutputPos
  have hOutputSquareLe : outputLoss ^ 2 ≤ outputLoss := by
    nlinarith
  have hStructuralSquarePos : 0 < structuralLoss ^ 2 :=
    sq_pos_of_pos hStructuralPos
  have hSourcePos : 0 < sourceLoss := by
    dsimp only [sourceLoss, wz2PaperFinalSourceLoss]
    positivity
  have hSourceStable : sourceLoss < stableLoss := by
    dsimp only [sourceLoss, stableLoss, wz2PaperFinalSourceLoss,
      wz2PaperFinalStableLoss]
    nlinarith
  have hStableEnvelope :
      5 * stableLoss < structuralLoss ^ 2 := by
    dsimp only [stableLoss, wz2PaperFinalStableLoss]
    nlinarith
  have hCriticalPos : 0 < criticalFloorLoss := by
    dsimp only [criticalFloorLoss, wz2PaperCriticalFloorLoss]
    positivity
  have hCriticalInternal :
      criticalFloorLoss < internalStrongLoss := by
    dsimp only [criticalFloorLoss, internalStrongLoss,
      wz2PaperCriticalFloorLoss, wz2PaperInternalStrongLoss]
    nlinarith
  have hInternalBudget :
      3 * internalStrongLoss ≤ outputLoss := by
    dsimp only [internalStrongLoss, wz2PaperInternalStrongLoss]
    nlinarith
  have hInternalCap : internalStrongLoss < capLoss := by
    dsimp only [capLoss, internalStrongLoss, wz2PaperFinalCapLoss,
      wz2PaperInternalStrongLoss]
    nlinarith
  have hCapPos : 0 < capLoss := by
    dsimp only [capLoss, wz2PaperFinalCapLoss]
    positivity
  have hComponentPos : 0 < componentLoss := by
    dsimp only [componentLoss, wz2PaperFinalComponentLoss]
    positivity
  have hFiberDensityPos : 0 < fiberDensityLoss := by
    dsimp only [fiberDensityLoss, wz2PaperFinalFiberDensityLoss]
    positivity
  have hFinalPos : 0 < finalStrongLoss := by
    dsimp only [finalStrongLoss, wz2PaperFinalStrongLoss]
    positivity
  have hCapComponent : capLoss < componentLoss := by
    dsimp only [capLoss, componentLoss, wz2PaperFinalCapLoss,
      wz2PaperFinalComponentLoss]
    nlinarith
  have hDensityFinal : fiberDensityLoss < finalStrongLoss := by
    dsimp only [fiberDensityLoss, finalStrongLoss,
      wz2PaperFinalFiberDensityLoss, wz2PaperFinalStrongLoss]
    linarith
  have hFinalBudget : 3 * finalStrongLoss ≤ outputLoss := by
    dsimp only [finalStrongLoss, wz2PaperFinalStrongLoss]
    linarith
  have hStructuralBound :
      structuralLoss ≤ outputLoss ^ 2 / 1000 := by
    simpa [wz2PaperInternalStrongLoss] using hStructuralInternal
  have hSourceBound :
      3 * sourceLoss ≤ outputLoss ^ 2 / 1000 := by
    have hStructuralOne : structuralLoss ≤ 1 := by
      calc
        structuralLoss ≤ outputLoss ^ 2 / 1000 := hStructuralBound
        _ ≤ 1 := by nlinarith
    have hStructuralSquareLe :
        structuralLoss ^ 2 ≤ structuralLoss := by
      nlinarith
    dsimp only [sourceLoss, wz2PaperFinalSourceLoss]
    nlinarith
  have hGap :
      0 <
        wz2PaperFinalComponentGap
          sourceLoss structuralLoss capLoss componentLoss outputLoss := by
    dsimp only [wz2PaperFinalComponentGap, capLoss, componentLoss,
      wz2PaperFinalCapLoss, wz2PaperFinalComponentLoss]
    nlinarith
  have hDensityGap :
      0 <
        outputLoss *
            (fiberDensityLoss - componentLoss - capLoss) -
          2 * sourceLoss - structuralLoss := by
    dsimp only [fiberDensityLoss, componentLoss, capLoss,
      wz2PaperFinalFiberDensityLoss, wz2PaperFinalComponentLoss,
      wz2PaperFinalCapLoss]
    nlinarith
  exact
    ⟨{
      sourceLoss := sourceLoss
      sourceLoss_eq := rfl
      stableLoss := stableLoss
      stableLoss_eq := rfl
      criticalFloorLoss := criticalFloorLoss
      criticalFloorLoss_eq := rfl
      internalStrongLoss := internalStrongLoss
      internalStrongLoss_eq := rfl
      capLoss := capLoss
      capLoss_eq := rfl
      capLoss_pos := hCapPos
      componentLoss := componentLoss
      componentLoss_eq := rfl
      componentLoss_pos := hComponentPos
      fiberDensityLoss := fiberDensityLoss
      fiberDensityLoss_eq := rfl
      fiberDensityLoss_pos := hFiberDensityPos
      finalStrongLoss := finalStrongLoss
      finalStrongLoss_eq := rfl
      finalStrongLoss_pos := hFinalPos
      sourceLoss_pos := hSourcePos
      source_stable := hSourceStable
      stable_structural_square := hStableEnvelope
      criticalFloorLoss_pos := hCriticalPos
      critical_internal := hCriticalInternal
      internal_output_budget := hInternalBudget
      internal_cap := hInternalCap
      cap_component := hCapComponent
      density_final := hDensityFinal
      final_output_budget := hFinalBudget
      component_gap_pos := hGap
      density_gap_pos := hDensityGap
    }⟩

end Kakeya.Assouad

end
