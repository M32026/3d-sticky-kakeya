import MyLeanRepo.Kakeya.Assouad.WZ1.MainChainStatements

/-!
# Paper-level WZ1 Corollary 26 boundaries

These statements separate:

1. the locally-linear producer on one scale;
2. its dependent finite iteration on one final shading;
3. the conversion from the genuine parent-child trapezoid hierarchy to the
   segment-correction format consumed by Proposition 27.
-/

namespace Kakeya.Assouad

/--
Direct one-scale locally-linear conclusion.

The input source loss is selected strictly inside the requested output budget.
The producer returns a family of separated active intervals on one retained
same-configuration shading, not a single global affine segment.
-/
def WZ1LocallyLinearOneScaleConclusion : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      HasWZ1CriticalVolumeFloor sigma →
      ∃ sourceLossCeiling delta₀ : ℝ,
        0 < sourceLossCeiling ∧
        sourceLossCeiling ≤ outputLoss / 100 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ inputLoss : ℝ,
          0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ source :
                WZ1PlaninessGraininessPackage
                  sigma inputLoss delta,
              ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
                Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                rho.1 ≤ Real.rpow delta outputLoss →
                  Nonempty
                    (WZ1LocallyLinearOneScaleData
                      source outputLoss rho)

/--
WZ1 Lemmas 23--24: the proved projection dichotomy supplies the one-scale
locally-linear producer.
-/
def WZ1LocallyLinearOneScaleStatement : Prop :=
  WZ1ProjectionDichotomyConclusion →
    WZ1LocallyLinearOneScaleConclusion

/--
Direct locally-linear conclusion at the terminal paper scale `rho = delta`.

This endpoint is deliberately separate from
`WZ1LocallyLinearOneScaleConclusion`: WZ1 Lemma 24 only states the window
`rho ∈ [delta^(1-outputLoss), delta^outputLoss]`, whereas Lemma 25 also uses
`rho_N = delta`.  The output is the same genuine separated trapezoid family,
not a Lipschitz-only surrogate.
-/
def WZ1LocallyLinearTerminalScaleConclusion : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      HasWZ1CriticalVolumeFloor sigma →
      ∃ sourceLossCeiling delta₀ : ℝ,
        0 < sourceLossCeiling ∧
        sourceLossCeiling ≤ outputLoss / 100 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ inputLoss : ℝ,
          0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ source :
                WZ1PlaninessGraininessPackage
                  sigma inputLoss delta,
              ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
                rho.1 = delta →
                  Nonempty
                    (WZ1LocallyLinearOneScaleData
                      source outputLoss rho)

/--
The projection dichotomy supplies the missing exact-`delta` endpoint used by
WZ1 Lemma 25.
-/
def WZ1LocallyLinearTerminalScaleStatement : Prop :=
  WZ1ProjectionDichotomyConclusion →
    WZ1LocallyLinearTerminalScaleConclusion

/--
Direct finite many-scale conclusion.

The caller chooses every `levelCount ≥ 2`; the theorem must therefore build
the full `rho_j = delta^((j+1)/levelCount)` hierarchy rather than selecting a
convenient two-level surrogate.
-/
def WZ1LocallyLinearHierarchyConclusion : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      HasWZ1CriticalVolumeFloor sigma →
      ∀ levelCount : ℕ, 2 ≤ levelCount →
        ∃ sourceLossCeiling delta₀ : ℝ,
          0 < sourceLossCeiling ∧
          sourceLossCeiling ≤ outputLoss / 100 ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ inputLoss : ℝ,
            0 < inputLoss → inputLoss ≤ sourceLossCeiling →
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∀ source :
                  WZ1PlaninessGraininessPackage
                    sigma inputLoss delta,
                ∃ package :
                    WZ1LocallyLinearHierarchyPackage
                      source outputLoss,
                  package.hierarchy.levelCount = levelCount

/--
WZ1 Lemma 25 / Corollary 26: dependently iterate the one-scale producer,
retain one final shading, enforce popularity/separation at every level, and
record the unique actual parent trapezoid at adjacent levels.
-/
def WZ1LocallyLinearHierarchyStatement : Prop :=
  WZ1LocallyLinearOneScaleConclusion →
    WZ1LocallyLinearTerminalScaleConclusion →
      WZ1LocallyLinearHierarchyConclusion

/--
Convert the genuine Corollary 26 hierarchy to the level-indexed segment
corrections consumed by the closed Proposition 27 proof.

The conversion must use parent-child trapezoid differences and within-level
separation to establish the active value and derivative costs.  Its global
slab AD output is transported from the source slope using the final-level
approximation on the same retained shading.
-/
def WZ1Corollary26SegmentConversionStatement : Prop :=
  ∀ {sigma inputLoss outputLoss delta : ℝ},
    0 < outputLoss →
    ∀ {source :
        WZ1PlaninessGraininessPackage
          sigma inputLoss delta},
      ∀ hierarchy :
          WZ1LocallyLinearHierarchyPackage source outputLoss,
        ∃ package :
            WZ1MultiscaleSlopeCorrectionPackage
              source outputLoss,
          package.shading = hierarchy.shading ∧
            ∃ levelCount_eq :
                package.corrections.levelCount =
                  hierarchy.hierarchy.levelCount,
              ∃ segmentFor :
                  ∀ level :
                      Fin hierarchy.hierarchy.levelCount,
                    ∀ trapezoid ∈
                        hierarchy.hierarchy.trapezoids level,
                      WZ1SegmentCorrection,
                (∀ level trapezoid htrapezoid,
                  segmentFor level trapezoid htrapezoid ∈
                    package.corrections.segments
                      (Fin.cast levelCount_eq.symm level)) ∧
                (∀ level trapezoid htrapezoid,
                  Nonempty
                    (WZ1TrapezoidSegmentSource
                      hierarchy.hierarchy level
                      (segmentFor level trapezoid htrapezoid))) ∧
                (∀ level,
                  ∀ segment ∈
                      package.corrections.segments level,
                    ∃ trapezoid htrapezoid,
                      segment =
                        segmentFor
                          (Fin.cast levelCount_eq level)
                          trapezoid htrapezoid)

/--
Assemble the legacy broad Corollary 26 boundary from the three repaired
mathematical leaves.
-/
def WZ1NestedSlopeCorrectionsFromHierarchyStatement : Prop :=
  WZ1CriticalFloorNormalizationStatement →
    WZ1LocallyLinearOneScaleStatement →
    WZ1LocallyLinearTerminalScaleStatement →
      WZ1LocallyLinearHierarchyStatement →
        WZ1Corollary26SegmentConversionStatement →
          WZ1NestedSlopeCorrectionsStatement

end Kakeya.Assouad
