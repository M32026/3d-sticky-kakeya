import MyLeanRepo.Kakeya.Assouad.WZ1.GridCellPartition
import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling
import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# Unit-rescaled fibers from WZ1 Proposition 5

The ordinary `WZ1BalancedCoverData` records the extremal coarse family and
the fine-to-coarse multiplicity bounds used by WZ1 Lemmas 12--20.  Proposition
5 has one additional output needed specifically by Proposition 9: inside
each retained coarse tube, a refinement of the fine fiber becomes extremal
after unit rescaling to radius `delta / rho`.

This module freezes that missing scale-changing boundary.  The target family
is not allowed to be an unrelated existential extremal family: the indexed
source shading is supported on the selected parent fiber, and the two shaded
carriers are related in both directions by the fixed unit-rescaling map, up
to one target-radius thickening.
-/

noncomputable section

namespace Kakeya.Assouad

/--
One selected fine fiber and its unit-rescaled extremal realization.

The source shading may be a refinement of the complete parent fiber, as in
the paper's `rescaledCoveredTube` lemma.  The distinguished source tube is
an anchor for this particular rediscretization; it is not yet the later
Property-(P) tube from Proposition 9.  A source tube can produce finitely many
coaxial target tubes after rediscretizing its affine image into unit segments,
so `sourceIndex` is intentionally not injective.  The measurable sets
`sourcePiece k` record the part assigned to target index `k`; they cover the
retained source shading and satisfy two-sided image control.
-/
structure WZ1UnitRescaledFiberData
    {delta sigma inputLoss outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := inputLoss) U Y rho)
    (parent : Fin (U.coarse rho).card)
    (hrho : 0 < rho.1) where
  sourceShading : Kakeya.Streamlined.TubeShading F
  source_subshading :
    IsSubshading sourceShading balanced.refined
  source_supported_on_parent :
    ∀ i p, p ∈ sourceShading.carrier i →
      (U.cover rho).parent i = parent
  distinguished : Fin F.card
  distinguished_parent :
    (U.cover rho).parent distinguished = parent
  distinguished_nonempty :
    (sourceShading.carrier distinguished).Nonempty
  targetFamily :
    Kakeya.Streamlined.TubeFamily (delta / rho.1)
  targetUniform :
    Kakeya.Streamlined.UniformTubeStructure targetFamily
  targetShading :
    Kakeya.Streamlined.TubeShading targetFamily
  target_extremal :
    WZ1ExtremalPair sigma outputLoss
      targetFamily targetUniform targetShading
  target_vertical :
    IsInVerticalChart targetFamily
  target_uniform_vertical :
    ∀ scale,
      IsInVerticalChart (targetUniform.coarse scale)
  sourceIndex : Fin targetFamily.card → Fin F.card
  sourceIndex_parent :
    ∀ k, (U.cover rho).parent (sourceIndex k) = parent
  sourcePiece : Fin targetFamily.card → Set Point3
  sourcePiece_measurable :
    ∀ k, MeasurableSet (sourcePiece k)
  sourcePiece_subset :
    ∀ k,
      sourcePiece k ⊆
        sourceShading.carrier (sourceIndex k)
  sourcePiece_cover :
    ∀ i,
      sourceShading.carrier i ⊆
        ⋃ k : Fin targetFamily.card,
          if sourceIndex k = i then sourcePiece k else ∅
  target_axis :
    ∀ k,
      tubeAxisLine (targetFamily.tube k) =
        wz1AnchoredUnitRescalingMap
            (F.tube distinguished) rho.1 hrho ''
          tubeAxisLine (F.tube (sourceIndex k))
  source_image_subset :
    ∀ k,
      wz1AnchoredUnitRescalingMap
          (F.tube distinguished) rho.1 hrho ''
        sourcePiece k ⊆
          targetShading.carrier k
  target_near_source_image :
    ∀ k,
      targetShading.carrier k ⊆
        Metric.cthickening (delta / rho.1)
          (wz1AnchoredUnitRescalingMap
              (F.tube distinguished) rho.1 hrho ''
            sourcePiece k)

/--
The later Property-(P) selection on one concrete rescaled parent fiber.

The paper performs this selection only after Proposition 5 has supplied an
extremal unit-rescaled fiber.  It may refine the supplied fiber and choose a
new distinguished source tube before rebuilding the anchored
rediscretization.  The explicit subshading field prevents this second
selection from replacing the supplied Proposition 5 fiber by an unrelated
configuration.
-/
structure WZ1PropertyPRescaledFiberData
    {delta sigma inputLoss baseOutputLoss propertyOutputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := inputLoss) U Y rho}
    {parent : Fin (U.coarse rho).card}
    {hrho : 0 < rho.1}
    (base :
      WZ1UnitRescaledFiberData
        (inputLoss := inputLoss) (outputLoss := baseOutputLoss)
        balanced parent hrho) where
  fiber :
    WZ1UnitRescaledFiberData
      (inputLoss := inputLoss) (outputLoss := propertyOutputLoss)
      balanced parent hrho
  source_subshading_base :
    IsSubshading fiber.sourceShading base.sourceShading
  propertyP :
    ∀ p ∈ fiber.sourceShading.union,
      ∃ q ∈ fiber.sourceShading.carrier fiber.distinguished,
        rhoGridIndex rho.1 p = rhoGridIndex rho.1 q

/--
Select the paper's Property-(P) refinement on one supplied unit-rescaled
fiber.

The caller requests the final loss `propertyOutputLoss`; the theorem chooses a
strictly stronger `baseOutputLoss` for the Proposition 5 fiber.  For a
sufficiently small target radius `delta / rho`, the selection keeps a
same-parent source refinement, re-anchors the unit rescaling on its
distinguished tube, and returns an extremal target at the requested weaker
loss.
-/
def WZ1PropertyPSelectionStatement : Prop :=
  ∀ sigma propertyOutputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < propertyOutputLoss →
      ∃ baseOutputLoss targetDelta₀ : ℝ,
        0 < baseOutputLoss ∧
        baseOutputLoss < propertyOutputLoss ∧
        0 < targetDelta₀ ∧ targetDelta₀ ≤ 1 ∧
        ∀ {delta inputLoss : ℝ},
          ∀ {F : Kakeya.Streamlined.TubeFamily delta},
            ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
              ∀ {Y : Kakeya.Streamlined.TubeShading F},
                ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
                  ∀ {balanced :
                      WZ1BalancedCoverData
                        (sigma := sigma) (epsilon := inputLoss) U Y rho},
                    ∀ {parent : Fin (U.coarse rho).card},
                      ∀ {hrho : 0 < rho.1},
                        ∀ base :
                            WZ1UnitRescaledFiberData
                              (inputLoss := inputLoss)
                              (outputLoss := baseOutputLoss)
                              balanced parent hrho,
                          0 < delta / rho.1 →
                          delta / rho.1 ≤ targetDelta₀ →
                            Nonempty
                              (WZ1PropertyPRescaledFiberData
                                (propertyOutputLoss := propertyOutputLoss)
                                base)

/--
The full Proposition 5 package needed by Proposition 9.

Besides the ordinary balanced cover, every coarse tube carrying nonempty
coarse shading has a nonempty fine refinement whose unit rescaling is
extremal at the genuine target radius `delta / rho`.
-/
structure WZ1BalancedCoverRescaledFiberData
    {delta sigma inputLoss outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) where
  balanced :
    WZ1BalancedCoverData
      (sigma := sigma) (epsilon := inputLoss) U Y rho
  rescaledFiber :
    ∀ parent : Fin (U.coarse rho).card,
      balanced.coarseShading.carrier parent ≠ ∅ →
        Nonempty
          (WZ1UnitRescaledFiberData
            (inputLoss := inputLoss)
            (outputLoss := outputLoss)
            balanced parent
            (lt_of_lt_of_le balanced.refined_extremal.1 rho.2.1))

/--
Repackage the one-parent Lemma 6 output when it was applied to the exact final
balanced refinement.
-/
def WZ1RescaledCoveredParentFiberData.toUnitRescaledFiberData
    {delta sigma inputLoss outputLoss retentionLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := inputLoss) U Y rho}
    {parent : Fin (U.coarse rho).card}
    {hrho : 0 < rho.1}
    (covered :
      WZ1RescaledCoveredParentFiberData
        (sigma := sigma)
        (outputLoss := outputLoss)
        (retentionLoss := retentionLoss)
        U balanced.refined rho parent hrho) :
    WZ1UnitRescaledFiberData
      (inputLoss := inputLoss) (outputLoss := outputLoss)
      balanced parent hrho :=
  { sourceShading := covered.sourceShading
    source_subshading := covered.source_subshading
    source_supported_on_parent := covered.source_supported_on_parent
    distinguished := covered.distinguished
    distinguished_parent := covered.distinguished_parent
    distinguished_nonempty := covered.distinguished_nonempty
    targetFamily := covered.targetFamily
    targetUniform := covered.targetUniform
    targetShading := covered.targetShading
    target_extremal := covered.target_extremal
    target_vertical := covered.target_vertical
    target_uniform_vertical := covered.target_uniform_vertical
    sourceIndex := covered.sourceIndex
    sourceIndex_parent := covered.sourceIndex_parent
    sourcePiece := covered.sourcePiece
    sourcePiece_measurable := covered.sourcePiece_measurable
    sourcePiece_subset := covered.sourcePiece_subset
    sourcePiece_cover := covered.sourcePiece_cover
    target_axis := covered.target_axis
    source_image_subset := covered.source_image_subset
    target_near_source_image := covered.target_near_source_image }

/--
WZ1 Proposition 5 with its unit-rescaled-fiber conclusion restored.

The balanced cover and the rescaled fibers must be produced jointly.  In the
paper, Lemma 6 is applied inside each retained parent before the subsequent
global refinements are frozen.  An independently quantified
`WZ1BalancedCoverStatement` cannot be combined with independently chosen
one-parent outputs while preserving source-shading provenance.
-/
def WZ1BalancedCoverRescaledFiberConclusion : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
    HasCriticalVolumeFloor sigma →
      ∀ rescaledLoss scaleLoss : ℝ,
        0 < rescaledLoss →
        0 < scaleLoss →
        ∃ balancedLoss eta delta₀ : ℝ,
          0 < balancedLoss ∧ balancedLoss < rescaledLoss ∧
          0 < eta ∧ eta < balancedLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  WZ1ExtremalPair sigma eta F U Y →
                  ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
                    Real.rpow delta (1 - scaleLoss) ≤ rho.1 →
                    rho.1 ≤ Real.rpow delta scaleLoss →
                      Nonempty
                        (WZ1BalancedCoverRescaledFiberData
                          (sigma := sigma)
                          (inputLoss := balancedLoss)
                          (outputLoss := rescaledLoss)
                          U Y rho)

/--
The full Proposition 5 producer, conditional on the one-parent unit-rescaled
Lemma 6.

This is not propositional glue with an independently chosen balanced cover:
the proof must construct the balanced cover around the retained one-parent
outputs so every exported source shading refines that exact cover.
-/
def WZ1BalancedCoverRescaledFiberStatement : Prop :=
  WZ1CriticalFloorNormalizationStatement →
    WZ1RescaledCoveredParentFiberStatement →
      WZ1BalancedCoverCoreStatement →
        WZ1AssociatedCellRefinementStatement →
          WZ1BalancedCoverRescaledFiberConclusion

end Kakeya.Assouad
