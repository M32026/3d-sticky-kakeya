import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropStickyReentry

/-!
# Node 5 post-refinement receipts for Proposition 6.2 outputs

The public Node 3 result is exactly `PureWZ2PropStickyData`.  Lemma 24 then
further refines the fine, intermediate, and coarse collections before using
constant multiplicity and balanced indexed incidence mass.  Consequently the
Node 5 object below is not an enrichment of an unchanged public output.  It
stores the exact Node 3 seed, explicit fine/coarse refinement provenance, and
the final public-shaped sticky data on which the extra receipts hold.

This distinction prevents a downstream proof from attaching the later
Lemma-24 conclusions to an arbitrary Node 3 output without performing the
paper's simultaneous refinement.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Node 5's extra receipts on one exact public balanced cover. -/
structure PureWZ2Node5BalancedCoverData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    (base : PureWZ2BalancedCoverData cover fineShading coarseShading) where
  incidenceMass : ENNReal
  incidenceMass_pos : 0 < incidenceMass
  incidenceMass_ne_top : incidenceMass ≠ ⊤
  fine_cell_incidence_mass :
    ∀ cell ∈ base.activeCells,
      (∑ source : Fin fine.card,
        volume
          (fineShading.carrier source ∩
            wz1PaperGridCube rho cell)) =
        incidenceMass
  fine_cell_nested :
    ∀ source point, point ∈ fineShading.carrier source →
      ∃ cell ∈ base.activeCells,
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          wz1PaperGridCube rho cell

namespace PureWZ2Node5BalancedCoverData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    {base : PureWZ2BalancedCoverData cover fineShading coarseShading}

abbrev activeCells (data : PureWZ2Node5BalancedCoverData base) :=
  base.activeCells

abbrev cellMass (data : PureWZ2Node5BalancedCoverData base) :=
  base.cellMass

abbrev point_compatibility (data : PureWZ2Node5BalancedCoverData base) :=
  base.point_compatibility

abbrev coarse_cubical (data : PureWZ2Node5BalancedCoverData base) :=
  base.coarse_cubical

abbrev coarse_union_eq (data : PureWZ2Node5BalancedCoverData base) :=
  base.coarse_union_eq

abbrev cellMass_pos (data : PureWZ2Node5BalancedCoverData base) :=
  base.cellMass_pos

abbrev cellMass_ne_top (data : PureWZ2Node5BalancedCoverData base) :=
  base.cellMass_ne_top

abbrev fine_cell_mass (data : PureWZ2Node5BalancedCoverData base) :=
  base.fine_cell_mass

end PureWZ2Node5BalancedCoverData

/--
One post-Node-3 sticky configuration used by Node 5.

`seed` is the exact output of the Node 3 call.  The two `WZ1PaperRefinement`
fields certify that the final fine and coarse configurations are genuine
refinements of that output.  `data` repackages the final configuration in the
public sticky shape; the extra Node 5 receipts below all refer to this final
configuration.
-/
structure PureWZ2Node5StickyData
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading source)
    (rho : WZ2PaperRequestedScale delta)
    (logExponent : ℕ) where
  seedLoss : ℝ
  seedNormalizationExponent : ℕ
  seedLogExponent : ℕ
  seed :
    PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
  fineRefinementExponent : ℕ
  fineRefinement :
    WZ1PaperRefinement seed.data.refined fineRefinementExponent
  coarseRefinementExponent : ℕ
  coarseRefinement :
    WZ1PaperRefinement
      seed.data.croppedCoarseShading coarseRefinementExponent
  data : PureWZ2PropStickyData
    (sigma := sigma) (outputLoss := outputLoss)
    sourceShading rho logExponent
  logExponent_eq :
    logExponent = seedLogExponent + fineRefinementExponent
  selected_eq :
    data.selected =
      seed.data.selected.comp fineRefinement.selected
  refined_eq :
    HEq data.refined fineRefinement.refined
  coarse_eq :
    data.coarse = coarseRefinement.selected.family
  croppedCoarseShading_eq :
    HEq data.croppedCoarseShading coarseRefinement.refined
  balanced : PureWZ2Node5BalancedCoverData data.balanced
  fineMultiplicity : ℕ
  fineMultiplicity_pos : 0 < fineMultiplicity
  refined_multiplicity_band :
    data.refined.HasConstantMultiplicity
      fineMultiplicity (2 * fineMultiplicity)
  refined_extremal :
    WZ2PaperCroppedIsExtremal
      sigma outputLoss data.selected.family data.refined
  refined_volume_lower :
    Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      volume data.refined.union
  full_fiber_uniform :
    ∀ first second : Fin data.coarse.card,
      ((wz2PaperFullFiberIndices
          data.selected.family data.coarse first).card : ENNReal) ≤
        Kakeya.realRpowENN rho.1 (-outputLoss) *
          ((wz2PaperFullFiberIndices
            data.selected.family data.coarse second).card : ENNReal)
  coarse_volume_lower :
    Kakeya.realRpowENN rho.1 (sigma + outputLoss) ≤
      volume data.croppedCoarseShading.union

/-- The exact subset of the historical Node-5 wrapper used by the terminal
Corollary-5.6 geometry.  In particular, terminal geometry does not inspect
the seed or the refinement-equality bookkeeping. -/
structure PureWZ2TerminalStickyCore
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading source)
    (rho : WZ2PaperRequestedScale delta)
    (logExponent : ℕ) where
  selected : Kakeya.Streamlined.TubeSubfamily source
  selected_nonempty : selected.family.Nonempty
  refined : WZ1PaperTubeShading selected.family
  subshading : ∀ index,
    refined.carrier index ⊆ sourceShading.carrier (selected.embedding index)
  retained_mass :
    wz2PaperPureRefinementFraction delta logExponent * sourceShading.mass ≤
      refined.mass
  refined_cubical : WZ1PaperIsCubicalShading refined
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  cover : PureWZ2Section6Cover selected.family coarse
  croppedCoarseShading : WZ1PaperTubeShading coarse
  balancedBase : PureWZ2BalancedCoverData cover refined croppedCoarseShading
  balanced : PureWZ2Node5BalancedCoverData
    (show PureWZ2BalancedCoverData cover refined croppedCoarseShading from
      balancedBase)
  coarse_extremal : WZ2PaperCroppedIsExtremal
    sigma outputLoss coarse croppedCoarseShading
  fineMultiplicity : ℕ
  fineMultiplicity_pos : 0 < fineMultiplicity
  refined_multiplicity_band :
    refined.HasConstantMultiplicity fineMultiplicity (2 * fineMultiplicity)
  refined_volume_lower :
    Kakeya.realRpowENN delta (sigma + outputLoss) ≤ volume refined.union

namespace PureWZ2Node5StickyData

/-- Forget the historical seed and equality bookkeeping at the exact point
where only terminal geometry remains. -/
noncomputable def toTerminalStickyCore
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) :
    PureWZ2TerminalStickyCore
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent where
  selected := data.data.selected
  selected_nonempty := data.data.selected_nonempty
  refined := data.data.refined
  subshading := data.data.subshading
  retained_mass := data.data.retained_mass
  refined_cubical := data.data.refined_cubical
  coarse := data.data.coarse
  cover := data.data.cover
  croppedCoarseShading := data.data.croppedCoarseShading
  balancedBase := data.data.balanced
  balanced := data.balanced
  coarse_extremal := data.data.coarse_extremal
  fineMultiplicity := data.fineMultiplicity
  fineMultiplicity_pos := data.fineMultiplicity_pos
  refined_multiplicity_band := data.refined_multiplicity_band
  refined_volume_lower := data.refined_volume_lower

variable
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}

abbrev selected (output : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := outputLoss)
    (sourceShading := sourceShading) (rho := rho)
    (logExponent := logExponent)) :=
  output.data.selected

abbrev selected_nonempty (output : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := outputLoss)
    (sourceShading := sourceShading) (rho := rho)
    (logExponent := logExponent)) :=
  output.data.selected_nonempty

abbrev refined (output : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := outputLoss)
    (sourceShading := sourceShading) (rho := rho)
    (logExponent := logExponent)) :=
  output.data.refined

abbrev subshading (output : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := outputLoss)
    (sourceShading := sourceShading) (rho := rho)
    (logExponent := logExponent)) :=
  output.data.subshading

abbrev retained_mass (output : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := outputLoss)
    (sourceShading := sourceShading) (rho := rho)
    (logExponent := logExponent)) :=
  output.data.retained_mass

abbrev refined_cubical (output : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := outputLoss)
    (sourceShading := sourceShading) (rho := rho)
    (logExponent := logExponent)) :=
  output.data.refined_cubical

abbrev coarse (output : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := outputLoss)
    (sourceShading := sourceShading) (rho := rho)
    (logExponent := logExponent)) :=
  output.data.coarse

abbrev cover (output : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := outputLoss)
    (sourceShading := sourceShading) (rho := rho)
    (logExponent := logExponent)) :=
  output.data.cover

abbrev croppedCoarseShading (output : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := outputLoss)
    (sourceShading := sourceShading) (rho := rho)
    (logExponent := logExponent)) :=
  output.data.croppedCoarseShading

abbrev coarse_extremal (output : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := outputLoss)
    (sourceShading := sourceShading) (rho := rho)
    (logExponent := logExponent)) :=
  output.data.coarse_extremal

abbrev rescaledFiber (output : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := outputLoss)
    (sourceShading := sourceShading) (rho := rho)
    (logExponent := logExponent)) :=
  output.data.rescaledFiber

abbrev coarse_multiplicity_upper (output : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := outputLoss)
    (sourceShading := sourceShading) (rho := rho)
    (logExponent := logExponent)) :=
  output.data.coarse_multiplicity_upper

abbrev fiber_multiplicity_upper (output : PureWZ2Node5StickyData
    (sigma := sigma) (outputLoss := outputLoss)
    (sourceShading := sourceShading) (rho := rho)
    (logExponent := logExponent)) :=
  output.data.fiber_multiplicity_upper

end PureWZ2Node5StickyData

/-- The Node 5 post-sticky output is attached to the exact rich output supplied
by the preceding Node 4 construction.  The heterogeneous equality records the
same dependent re-entry witness after identifying its stored indices. -/
structure PureWZ2Node5StickyRefinesReentrantSeed
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {seedNormalizationExponent seedLogExponent logExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent)
    (output : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) : Prop where
  seedLoss_eq : output.seedLoss = seedLoss
  seedNormalizationExponent_eq :
    output.seedNormalizationExponent = seedNormalizationExponent
  seedLogExponent_eq : output.seedLogExponent = seedLogExponent
  seed_eq : HEq output.seed seed

/--
The paper's post-sticky simultaneous refinement, stated as a separate Node 5
capability.  The preceding Node 4 construction supplies a rich `seed` which
retains the exact coarse re-entry certificate; this capability must refine
that very output and preserve the equality in its result.  In particular it
cannot quantify over a public `PureWZ2PropStickyData` which has already
forgotten the ordinary normalization and then manufacture the missing
receipts.
-/
def PureWZ2Node5StickyRefinementCapability : Prop :=
  ∀ sigma : ℝ, PureWZ2CriticalPackage sigma →
    ∀ seedLoss outputLoss : ℝ,
      0 < seedLoss → seedLoss < outputLoss →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ {source : Kakeya.Streamlined.TubeFamily delta},
              ∀ (sourceShading : WZ1PaperTubeShading source),
                WZ1PaperIsLineClass source →
                WZ2PaperCroppedIsExtremal
                  sigma seedLoss source sourceShading →
                ∀ (rho : WZ2PaperRequestedScale delta),
                  18 * delta ≤ rho.1 →
                  ∀ (seedNormalizationExponent seedLogExponent : ℕ),
                    ∀ seed : PureWZ2ReentrantPropStickyData
                        (sigma := sigma) (outputLoss := seedLoss)
                        sourceShading rho seedNormalizationExponent
                          seedLogExponent,
                      Nonempty
                        (Σ logExponent : ℕ,
                          {output : PureWZ2Node5StickyData
                              (sigma := sigma) (outputLoss := outputLoss)
                              sourceShading rho logExponent //
                            PureWZ2Node5StickyRefinesReentrantSeed
                              seed output})

end Kakeya.Assouad
