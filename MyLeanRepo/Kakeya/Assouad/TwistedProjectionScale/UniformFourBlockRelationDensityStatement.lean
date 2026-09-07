import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedScaleStatements

/-!
# Fubini density for a uniform relation-valued four-block cover

The original selected-scale density theorem assumed an injective parent map.
For an OS-uniform parameter cell decomposition the parent fibers are instead
all comparable: every occupied cell contains between `m` and `2m` indexed
tubes.

Summing the same tube-piece Fubini inequality now costs the upper factor
`2m`, while the total fine cardinality gains the lower factor `m` per coarse
block.  These factors cancel, leaving the explicit coarse density
`lambda / 800`.
-/

noncomputable section

namespace Kakeya.Assouad

/--
A finite relation-valued cover by one four-tube block per parent, with
factor-two uniform indexed parent fibers.
-/
structure UniformFourBlockRelationData
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (shading : Kakeya.Streamlined.TubeShading fine) where
  parentCount : ℕ
  parentCount_pos : 0 < parentCount
  parent : Fin fine.card → Fin parentCount
  parent_surjective : Function.Surjective parent
  block : Fin parentCount → Kakeya.Streamlined.TubeFamily rho
  block_card : ∀ parentIndex, (block parentIndex).card = 4
  shading_cover :
    ∀ fineIndex,
      shading.carrier fineIndex ⊆
        (block (parent fineIndex)).toBodyFamily.union
  fiberMultiplicity : ℕ
  fiberMultiplicity_pos : 0 < fiberMultiplicity
  fiber_lower :
    ∀ parentIndex : Fin parentCount,
      fiberMultiplicity ≤
        (Finset.univ.filter fun fineIndex =>
          parent fineIndex = parentIndex).card
  fiber_upper :
    ∀ parentIndex : Fin parentCount,
      (Finset.univ.filter fun fineIndex =>
        parent fineIndex = parentIndex).card <
          2 * fiberMultiplicity

namespace UniformFourBlockRelationData

/-- Flatten the four-member parent blocks. -/
def coarse
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading fine}
    (data : UniformFourBlockRelationData (rho := rho) fine shading) :
    Kakeya.Streamlined.TubeFamily rho :=
  flattenFixedBlocks data.block data.block_card

/-- Relate a fine index to every member of its assigned four-tube block. -/
def relation
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading fine}
    (data : UniformFourBlockRelationData (rho := rho) fine shading)
    (fineIndex : Fin fine.card)
    (coarseIndex : Fin data.coarse.card) : Prop :=
  fixedBlockIndex coarseIndex = data.parent fineIndex

/-- Unwindowed exact relation-induced shading used by the Fubini estimate. -/
def exactShading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading fine}
    (data : UniformFourBlockRelationData (rho := rho) fine shading)
    (r : ℝ) :
    Kakeya.Streamlined.TubeShading data.coarse where
  carrier coarseIndex :=
    (data.coarse.tube coarseIndex).carrier ∩
      Metric.cthickening r
        {point | ∃ fineIndex : Fin fine.card,
          data.relation fineIndex coarseIndex ∧
            point ∈ shading.carrier fineIndex}
  measurable_carrier coarseIndex :=
    Metric.isClosed_cthickening.measurableSet.inter
      Metric.isClosed_cthickening.measurableSet
  subset_body coarseIndex := Set.inter_subset_left

end UniformFourBlockRelationData

/--
Direct callable density transfer for one uniform four-block relation.
-/
def UniformFourBlockRelationDensityInput : Prop :=
  ∀ {delta rho : ℝ},
        0 < delta →
        delta ≤ rho →
        rho ≤ 1 →
        ∀ fine : Kakeya.Streamlined.TubeFamily delta,
          ∀ shading : Kakeya.Streamlined.TubeShading fine,
            ∀ data :
                UniformFourBlockRelationData
                  (rho := rho) fine shading,
              ∀ lambda : ENNReal,
                shading.IsLambdaDense lambda →
                  (ENNReal.ofReal (1 / 800 : ℝ) * lambda) *
                      data.coarse.toBodyFamily.mass ≤
                    (data.exactShading rho).mass

/--
Uniform parent-fiber counts replace parent injectivity in the selected-scale
tube-piece Fubini argument.
-/
def UniformFourBlockRelationDensityStatement : Prop :=
  TubeVolumeScalingStatement →
    TubePieceThickeningDensityStatement →
      UniformFourBlockRelationDensityInput

end Kakeya.Assouad
