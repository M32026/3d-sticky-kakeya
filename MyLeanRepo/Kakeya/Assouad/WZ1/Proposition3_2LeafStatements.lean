import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2Statements

/-!
# Leaf boundaries for WZ1 Proposition 3.2

The decomposition follows the quantifier order of the paper.

1. The exact one-parent rescaling theorem chooses the internal parent loss.
2. The core constructor uses that concrete loss to build one final balanced
   refinement and the density premise needed in every final parent.
3. The assembly applies the same one-parent theorem to every parent of that
   concrete core.

This prevents independently chosen existential refinements from being glued
together after the fact.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The reusable output already present in the historical one-parent rescaling
development.

It records the retained same-parent source shading, the extremal rescaled
target, and the source-piece provenance.  It deliberately leaves the anchor
map abstract: the historical code uses a distinguished fine tube, while the
frozen Proposition 3.2 interface uses the coarse parent tube.
-/
structure WZ1Proposition3_2ParentRescalingCandidate
    {delta rho sigma retentionLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : Kakeya.Streamlined.TubeCover fine coarse)
    (source : Kakeya.Streamlined.TubeShading fine)
    (parent : Fin coarse.card) where
  rho_pos : 0 < rho
  retained : Kakeya.Streamlined.TubeShading fine
  retained_subshading : IsSubshading retained source
  retained_supported :
    ∀ index point, point ∈ retained.carrier index →
      cover.parent index = parent
  retained_mass :
    Kakeya.realRpowENN delta retentionLoss *
        cover.toFactoring.fiberShadedMass source parent ≤
      retained.mass
  source_fiber_cap :
    ∀ point,
      (cover.toFactoring.fiberPointMultiplicity
          retained parent point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
          (-sigma - outputLoss)
  target :
    WZ1UnitRescaledTargetData
      (delta / rho) sigma outputLoss
  distinguished : Fin fine.card
  distinguished_parent :
    cover.parent distinguished = parent
  distinguished_nonempty :
    (retained.carrier distinguished).Nonempty
  targetMultiplicity : ℕ
  targetMultiplicity_pos : 0 < targetMultiplicity
  target_constant_multiplicity :
    target.shading.HasConstantMultiplicity
      targetMultiplicity (2 * targetMultiplicity)
  target_multiplicity_upper :
    (targetMultiplicity : ENNReal) ≤
      Kakeya.realRpowENN (delta / rho)
        (-sigma - outputLoss)
  sourceIndex : Fin target.family.card → Fin fine.card
  sourceIndex_parent :
    ∀ targetIndex,
      cover.parent (sourceIndex targetIndex) = parent
  sourcePiece : Fin target.family.card → Set Point3
  sourcePiece_measurable :
    ∀ targetIndex, MeasurableSet (sourcePiece targetIndex)
  sourcePiece_subset :
    ∀ targetIndex,
      sourcePiece targetIndex ⊆
        retained.carrier (sourceIndex targetIndex)
  sourcePiece_cover :
    ∀ sourceIndex',
      retained.carrier sourceIndex' ⊆
        ⋃ targetIndex : Fin target.family.card,
          if sourceIndex targetIndex = sourceIndex' then
            sourcePiece targetIndex
          else ∅
  target_axis :
    ∀ targetIndex,
      tubeAxisLine (target.family.tube targetIndex) =
        wz1AnchoredUnitRescalingMap
            (fine.tube distinguished) rho rho_pos ''
          tubeAxisLine (fine.tube (sourceIndex targetIndex))
  pullback_multiplicity_le :
    ∀ point,
      (retained.pointMultiplicity point : ENNReal) ≤
        (target.shading.pointMultiplicity
          (wz1AnchoredUnitRescalingMap
            (fine.tube distinguished) rho rho_pos
            point) : ENNReal)
  source_image_subset :
    ∀ targetIndex,
      wz1AnchoredUnitRescalingMap
          (fine.tube distinguished) rho rho_pos ''
        sourcePiece targetIndex ⊆
          target.shading.carrier targetIndex
  target_near_source_image :
    ∀ targetIndex,
      target.shading.carrier targetIndex ⊆
        Metric.cthickening (delta / rho)
          (wz1AnchoredUnitRescalingMap
              (fine.tube distinguished) rho rho_pos ''
            sourcePiece targetIndex)

/--
The paper-aligned strengthening of the historical one-parent candidate.

The only additional field is cubicality of the retained source shading.  This
cannot be recovered propositionally from the legacy output, whose type permits
an arbitrary measurable subshading, but the existing dyadic-band construction
can preserve it when the input shading is cubical.
-/
structure WZ1Proposition3_2CubicalParentCandidate
    {delta rho sigma retentionLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : Kakeya.Streamlined.TubeCover fine coarse)
    (source : Kakeya.Streamlined.TubeShading fine)
    (parent : Fin coarse.card)
    extends
      WZ1Proposition3_2ParentRescalingCandidate
        (sigma := sigma)
        (retentionLoss := retentionLoss)
        (outputLoss := outputLoss)
        cover source parent where
  retained_cubical :
    WZ1IsCubicalShading toWZ1Proposition3_2ParentRescalingCandidate.retained
/--
Convert a historical one-parent candidate to the frozen exact item-(ii)
package once the three genuinely missing provenance facts are supplied.
-/
def WZ1Proposition3_2ParentRescalingExactificationStatement : Prop :=
  ∀ {delta rho sigma retentionLoss outputLoss : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ {cover : Kakeya.Streamlined.TubeCover fine coarse},
          ∀ {source : Kakeya.Streamlined.TubeShading fine},
            ∀ {parent : Fin coarse.card},
              ∀ {hrho : 0 < rho},
                ∀ {coarseVertical : IsInVerticalChart coarse},
                  ∀ candidate :
                      WZ1Proposition3_2ParentRescalingCandidate
                        (sigma := sigma)
                        (retentionLoss := retentionLoss)
                        (outputLoss := outputLoss)
                        cover source parent,
                    (∀ targetIndex,
                      tubeAxisLine
                          (candidate.target.family.tube
                            targetIndex) =
                        wz1CoarseUnitRescalingMap
                            (coarse.tube parent) hrho
                            (coarseVertical parent) ''
                          tubeAxisLine
                            (fine.tube
                              (candidate.sourceIndex
                                targetIndex))) →
                    (∀ targetIndex,
                      candidate.target.shading.carrier
                          targetIndex =
                        wz1CubicalSaturation (delta / rho)
                          (wz1CoarseUnitRescalingMap
                              (coarse.tube parent) hrho
                              (coarseVertical parent) ''
                            candidate.sourcePiece targetIndex)) →
                      Nonempty
                        (WZ1UnitRescaledParentFiberData
                          (sigma := sigma)
                          (epsilon := outputLoss)
                          cover candidate.retained parent
                          hrho coarseVertical)

/--
The final Proposition 3.2 package except for item (ii).

`parent_density` is the exact input needed to apply the one-parent rescaling
leaf to every parent of this same final balanced refinement.
-/
structure WZ1Proposition3_2CoreData
    {delta sigma inputLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) where
  selected : Kakeya.Streamlined.TubeSubfamily source
  refined :
    Kakeya.Streamlined.TubeShading selected.family
  subshading :
    ∀ index,
      refined.carrier index ⊆
        shading.carrier (selected.embedding index)
  refined_cubical :
    WZ1IsCubicalShading refined
  retained_mass :
    Kakeya.realRpowENN delta outputLoss * shading.mass ≤
      refined.mass
  fineUniform :
    Kakeya.Streamlined.UniformTubeStructure selected.family
  refined_extremal :
    WZ1ExtremalPair sigma inputLoss
      selected.family fineUniform refined
  fine_vertical :
    WZ1VerticalUniformTubeStructure fineUniform
  coarse :
    WZ1Proposition3_2CoarseExtremalData
      fineUniform rho sigma outputLoss
  balanced :
    WZ1Proposition3_2BalancedCoverData
      (fineUniform.cover rho) refined coarse.shading
  multiplicity :
    WZ1Proposition3_2MultiplicityData
      (sigma := sigma) (epsilon := outputLoss)
      (fineUniform.cover rho) refined coarse.shading
  parent_density :
    ∀ parent : Fin (fineUniform.coarse rho).card,
      coarse.shading.carrier parent ≠ ∅ →
      Kakeya.realRpowENN delta inputLoss *
          (fineUniform.cover rho).toFactoring.fiberMass parent ≤
        (fineUniform.cover rho).toFactoring.fiberShadedMass
          refined parent

/--
The part of the Proposition 3.2 core already supplied by the root-relative
single-scale package.

The candidate deliberately omits exactly the fields that historical arbitrary
cell partitions cannot provide: cubicality of the final fine shading, the
standard-cell balanced cover, and active-parent density on that same final
shading.
-/
structure WZ1Proposition3_2CoreCandidate
    {delta sigma inputLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) where
  selected : Kakeya.Streamlined.TubeSubfamily source
  refined :
    Kakeya.Streamlined.TubeShading selected.family
  subshading :
    ∀ index,
      refined.carrier index ⊆
        shading.carrier (selected.embedding index)
  retained_mass :
    Kakeya.realRpowENN delta outputLoss * shading.mass ≤
      refined.mass
  fineUniform :
    Kakeya.Streamlined.UniformTubeStructure selected.family
  refined_extremal :
    WZ1ExtremalPair sigma inputLoss
      selected.family fineUniform refined
  fine_vertical :
    WZ1VerticalUniformTubeStructure fineUniform
  coarse :
    WZ1Proposition3_2CoarseExtremalData
      fineUniform rho sigma outputLoss
  point_compatibility :
    ∀ sourceIndex point,
      point ∈ refined.carrier sourceIndex →
        point ∈ coarse.shading.carrier
          ((fineUniform.cover rho).parent sourceIndex)
  multiplicity :
    WZ1Proposition3_2MultiplicityData
      (sigma := sigma) (epsilon := outputLoss)
      (fineUniform.cover rho) refined coarse.shading

/--
Certificate that a historical finite cell map is exactly the standard grid
partition used by the frozen Proposition 3.2 interface.
-/
structure WZ1Proposition3_2StandardCellRealizationData
    {rho : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (coarseShading : Kakeya.Streamlined.TubeShading coarse)
    {cellCount : ℕ}
    (cell : Point3 → Fin cellCount) where
  coarse_cubical :
    WZ1IsCubicalShading coarseShading
  gridIndexOfCell : Fin cellCount → ℤ × ℤ × ℤ
  gridIndexOfCell_injective :
    Function.Injective gridIndexOfCell
  cell_eq_standard :
    ∀ point ∈ coarseShading.union,
      wz1StandardGridIndex rho point =
        gridIndexOfCell (cell point)
  standard_eq_cell :
    ∀ point ∈ coarseShading.union,
      ∀ index : Fin cellCount,
        wz1StandardGridIndex rho point =
            gridIndexOfCell index →
          cell point = index

/--
Complete a reusable core candidate once the three genuinely missing
same-configuration facts have been supplied.
-/
def WZ1Proposition3_2CoreExactificationStatement : Prop :=
  ∀ {delta sigma inputLoss outputLoss : ℝ},
    ∀ {source : Kakeya.Streamlined.TubeFamily delta},
      ∀ {shading : Kakeya.Streamlined.TubeShading source},
        ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
          ∀ candidate :
              WZ1Proposition3_2CoreCandidate
                (sigma := sigma)
                (inputLoss := inputLoss)
                (outputLoss := outputLoss)
                shading rho,
            WZ1IsCubicalShading candidate.refined →
            WZ1Proposition3_2BalancedCoverData
                (candidate.fineUniform.cover rho)
                candidate.refined candidate.coarse.shading →
            (∀ parent :
                Fin (candidate.fineUniform.coarse rho).card,
              candidate.coarse.shading.carrier parent ≠ ∅ →
              Kakeya.realRpowENN delta inputLoss *
                  (candidate.fineUniform.cover rho).toFactoring.fiberMass
                    parent ≤
                (candidate.fineUniform.cover rho).toFactoring.fiberShadedMass
                  candidate.refined parent) →
              Nonempty
                (WZ1Proposition3_2CoreData
                  (sigma := sigma)
                  (inputLoss := inputLoss)
                  (outputLoss := outputLoss)
                  shading rho)

/--
The WZ1 Lemma 3.3 boundary aligned with the historical producer.

This is the paper's one-parent refinement.  It returns the reusable candidate,
not the final item-(ii) package on the later global refinement.
-/
def WZ1Proposition3_2LegacyParentCandidateStatement : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
    HasWZ1CriticalVolumeFloor sigma →
      ∀ outputLoss retentionLoss scaleLoss : ℝ,
        0 < outputLoss →
        0 < retentionLoss → retentionLoss < outputLoss →
        0 < scaleLoss →
          ∃ inputLoss delta₀ : ℝ,
            0 < inputLoss ∧ inputLoss < retentionLoss ∧
            0 < delta₀ ∧ delta₀ ≤ 1 ∧
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∀ fine : Kakeya.Streamlined.TubeFamily delta,
                ∀ fineUniform :
                    Kakeya.Streamlined.UniformTubeStructure fine,
                  ∀ source : Kakeya.Streamlined.TubeShading fine,
                    WZ1ExtremalPair sigma inputLoss
                      fine fineUniform source →
                    ∀ rho :
                        Kakeya.Streamlined.AdmissibleScale delta,
                      Real.rpow delta (1 - scaleLoss) ≤ rho.1 →
                      rho.1 ≤ Real.rpow delta scaleLoss →
                      ∀ parent :
                          Fin (fineUniform.coarse rho).card,
                        Kakeya.realRpowENN delta inputLoss *
                            (fineUniform.cover rho).toFactoring.fiberMass
                              parent ≤
                          (fineUniform.cover rho).toFactoring.fiberShadedMass
                            source parent →
                          Nonempty
                            (WZ1Proposition3_2ParentRescalingCandidate
                              (sigma := sigma)
                              (retentionLoss := retentionLoss)
                              (outputLoss := outputLoss)
                              (fineUniform.cover rho) source parent)

/--
The paper-aligned Lemma 3.3 producer used by the global synchronization.

It has the same quantifier order and quantitative bounds as the historical
one-parent theorem, but additionally preserves standard-cell cubicality.
-/
def WZ1Proposition3_2ParentCandidateStatement : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
    HasWZ1CriticalVolumeFloor sigma →
      ∀ outputLoss retentionLoss scaleLoss : ℝ,
        0 < outputLoss →
        0 < retentionLoss → retentionLoss < outputLoss →
        0 < scaleLoss →
          ∃ inputLoss delta₀ : ℝ,
            0 < inputLoss ∧ inputLoss < retentionLoss ∧
            0 < delta₀ ∧ delta₀ ≤ 1 ∧
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∀ fine : Kakeya.Streamlined.TubeFamily delta,
                ∀ fineUniform :
                    Kakeya.Streamlined.UniformTubeStructure fine,
                  ∀ source : Kakeya.Streamlined.TubeShading fine,
                    WZ1ExtremalPair sigma inputLoss
                      fine fineUniform source →
                    WZ1IsCubicalShading source →
                    ∀ rho :
                        Kakeya.Streamlined.AdmissibleScale delta,
                      Real.rpow delta (1 - scaleLoss) ≤ rho.1 →
                      rho.1 ≤ Real.rpow delta scaleLoss →
                      ∀ parent :
                          Fin (fineUniform.coarse rho).card,
                        Kakeya.realRpowENN delta inputLoss *
                            (fineUniform.cover rho).toFactoring.fiberMass
                              parent ≤
                          (fineUniform.cover rho).toFactoring.fiberShadedMass
                            source parent →
                          Nonempty
                            (WZ1Proposition3_2CubicalParentCandidate
                              (sigma := sigma)
                              (retentionLoss := retentionLoss)
                              (outputLoss := outputLoss)
                              (fineUniform.cover rho) source parent)

/--
The stronger exact one-parent boundary used by the mechanical exact-core
assembly below.

It is stated on one already-final fine configuration.  The caller supplies
the parent-density premise; the output is the coarse-relative whole-parent
unit rescaling from the frozen Proposition 3.2 interface.
-/
def WZ1Proposition3_2ExactParentRescalingStatement : Prop :=
  ∀ sigma outputLoss scaleLoss : ℝ,
    0 < sigma → sigma < 1 →
    0 < outputLoss → 0 < scaleLoss →
    HasWZ1CriticalVolumeFloor sigma →
      ∃ inputLoss delta₀ : ℝ,
        0 < inputLoss ∧ inputLoss < outputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ fine : Kakeya.Streamlined.TubeFamily delta,
            ∀ fineUniform :
                Kakeya.Streamlined.UniformTubeStructure fine,
              ∀ refined : Kakeya.Streamlined.TubeShading fine,
                ∀ hExt :
                    WZ1ExtremalPair sigma inputLoss
                      fine fineUniform refined,
                ∀ hVertical :
                    WZ1VerticalUniformTubeStructure fineUniform,
                WZ1IsCubicalShading refined →
                ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
                  Real.rpow delta (1 - scaleLoss) ≤ rho.1 →
                  rho.1 ≤ Real.rpow delta scaleLoss →
                  ∀ parent : Fin (fineUniform.coarse rho).card,
                    Kakeya.realRpowENN delta inputLoss *
                        (fineUniform.cover rho).toFactoring.fiberMass
                          parent ≤
                      (fineUniform.cover rho).toFactoring.fiberShadedMass
                        refined parent →
                      Nonempty
                        (WZ1UnitRescaledParentFiberData
                          (sigma := sigma) (epsilon := outputLoss)
                          (fineUniform.cover rho) refined parent
                          (lt_of_lt_of_le
                            hExt.1 rho.2.1)
                          (hVertical.2 rho))

/--
Steps 1 and 3 of Proposition 3.2, including final cleanup.

The internal loss is supplied by Lemma 3.3.  The core constructor must return
one final subfamily whose standard-cell balanced cover, coarse extremality,
two multiplicity bounds, and per-parent density all hold simultaneously.
-/
def WZ1Proposition3_2ExactCoreStatement : Prop :=
  ∀ sigma inputLoss outputLoss scaleLoss : ℝ,
    0 < sigma → sigma < 1 →
    0 < inputLoss → inputLoss < outputLoss →
    0 < outputLoss → 0 < scaleLoss →
    HasWZ1CriticalVolumeFloor sigma →
      ∃ eta delta₀ : ℝ,
        0 < eta ∧ eta < inputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ source : Kakeya.Streamlined.TubeFamily delta,
            ∀ sourceUniform :
                Kakeya.Streamlined.UniformTubeStructure source,
              ∀ shading : Kakeya.Streamlined.TubeShading source,
                WZ1ExtremalPair sigma eta
                  source sourceUniform shading →
                WZ1VerticalUniformTubeStructure sourceUniform →
                WZ1IsCubicalShading shading →
                ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
                  Real.rpow delta (1 - scaleLoss) ≤ rho.1 →
                  rho.1 ≤ Real.rpow delta scaleLoss →
                    Nonempty
                      (WZ1Proposition3_2CoreData
                        (sigma := sigma)
                        (inputLoss := inputLoss)
                        (outputLoss := outputLoss)
                        shading rho)

/-- Mechanical assembly of the two strong exact leaves. -/
def WZ1Proposition3_2ExactAssemblyStatement : Prop :=
  WZ1Proposition3_2ExactParentRescalingStatement →
    WZ1Proposition3_2ExactCoreStatement →
      WZ1Proposition3_2Statement

/--
The remaining global Proposition 3.2 synchronization after the paper-aligned
Lemma 3.3 candidate theorem is available.

This leaf contains Steps 1--3: choose the coarse cover, apply the candidate to
all retained parents, synchronize their source refinements, perform the
standard-cell balance and active-parent cleanup, and restore the final
extremality conclusions.
-/
def WZ1Proposition3_2GlobalSynchronizationStatement : Prop :=
  WZ1Proposition3_2ParentCandidateStatement →
    WZ1Proposition3_2Statement

end Kakeya.Assouad
