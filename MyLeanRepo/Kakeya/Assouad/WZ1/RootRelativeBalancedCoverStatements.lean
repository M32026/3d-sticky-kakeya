import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeConditionalRefinementStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# Root-relative Proposition 5 balanced covers

This module freezes the replacement for the retired recursive
`WZ1BalancedCoverData.coarseUniform` interface.

All coarse families remain independent covers of one original root family.
The output keeps one common root subshading, one paper-scale coarse package
at each requested schedule coordinate, and finite conditional-cell
uniformity.  Cross-scale geometry is relational: parents with a common active
root child satisfy a fixed dilated containment theorem.  No
`UniformTubeStructure (U.coarse rho)` is constructed.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/--
Homothetic dilation of one formal tube carrier about the midpoint of its
unit axis segment.

This is the Assouad-side statement boundary for the shared independent-cover
geometry.  The validated Streamlined theorem uses dilation factor `13`.
-/
def wz1DilatedTubeCarrier
    {rho : ℝ} (factor : ℝ) (tube : Kakeya.DeltaTube rho) :
    Set Point3 :=
  let midpoint :=
    tube.base + (1 / 2 : ℝ) • tube.direction
  AffineMap.homothety midpoint factor '' tube.carrier

/--
Shared geometric input for two independently selected root covers.

If a `rho`-parent and a larger `sigma`-parent have one common active root
child, the smaller parent lies in the `13`-dilation of the larger one.  Strict
containment in the undilated parent is deliberately not asserted.
-/
def WZ1IndependentParentContainmentInput : Prop :=
  ∀ {delta : ℝ}, 0 < delta →
    ∀ {F : Kakeya.Streamlined.TubeFamily delta},
      F.IsInUnitBall →
      ∀ (U : Kakeya.Streamlined.UniformTubeStructure F),
        ∀ (Y : Kakeya.Streamlined.TubeShading F),
          ∀ rho sigma :
              Kakeya.Streamlined.AdmissibleScale delta,
            rho.1 ≤ sigma.1 →
            ∀ j : Fin (U.coarse rho).card,
              ∀ k : Fin (U.coarse sigma).card,
                WZ1RootParentRelation
                    U Y rho sigma j k →
                  ((U.coarse rho).tube j).carrier ⊆
                    wz1DilatedTubeCarrier 13
                      ((U.coarse sigma).tube k)

/--
The scale-local part of WZ1 extremality.

The all-scale cover information is stored once on the original root family
and its finite schedule.  A selected coarse family therefore records only
the properties literally used at that scale: essential distinctness,
density, the cropped support window, and the two-sided volume window.
-/
def WZ1ScaleLocalExtremalPair
    {rho : ℝ} (sigma epsilon : ℝ)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (shading : Kakeya.Streamlined.TubeShading coarse) : Prop :=
  0 < rho ∧ rho ≤ 1 ∧
    coarse.Nonempty ∧
    shading.union ⊆ Metric.closedBall (0 : Point3) 1 ∧
    coarse.IsEssentiallyDistinct ∧
    shading.IsLambdaDense
      (Kakeya.realRpowENN rho epsilon) ∧
    volume shading.union ≤
      Kakeya.realRpowENN rho (sigma - epsilon) ∧
    Kakeya.realRpowENN rho (sigma + epsilon) ≤
      volume shading.union

/--
One paper-scale Proposition 5 package on the original root family.

This contains the scale-local part of the former associated balanced cover,
but no recursive uniform structure on the coarse family.
-/
structure WZ1RootRelativeScaleCoverData
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (refined : Kakeya.Streamlined.TubeShading F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) where
  fiberMultiplicity : ℕ
  fiberMultiplicity_pos : 0 < fiberMultiplicity
  fiber_constant_multiplicity :
    ∀ j,
      (U.cover rho).toFactoring.FiberHasConstantMultiplicity
        refined j fiberMultiplicity (2 * fiberMultiplicity)
  coarseShading :
    Kakeya.Streamlined.TubeShading (U.coarse rho)
  coarseUniform :
    Kakeya.Streamlined.UniformTubeStructure (U.coarse rho)
  coarse_uniformity_bound :
    coarseUniform.uniformity ≤
      Kakeya.realRpowENN rho.1 (-epsilon)
  coarse_frostman_bound :
    coarseUniform.IsFrostmanAtEveryScale
      (Kakeya.realRpowENN rho.1 (-epsilon))
  coarse_extremal :
    WZ1ScaleLocalExtremalPair sigma epsilon
      (U.coarse rho) coarseShading
  induced_subshading :
    (U.cover rho).toFactoring.IsInducedSubshading
      refined coarseShading rho.1
  coarse_nonempty : coarseShading.union.Nonempty
  coarseMultiplicity : ℕ
  coarseMultiplicity_pos : 0 < coarseMultiplicity
  coarse_constant_multiplicity :
    coarseShading.HasConstantMultiplicity
      coarseMultiplicity (2 * coarseMultiplicity)
  point_compatibility :
    ∀ i p, p ∈ refined.carrier i →
      p ∈ coarseShading.carrier ((U.cover rho).parent i)
  direction_alignment :
    ∀ i,
      ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
        ‖((U.coarse rho).tube
              ((U.cover rho).parent i)).direction -
            sign • (F.tube i).direction‖ ≤
          4 * rho.1
  coarse_multiplicity_upper :
    ∀ p,
      (coarseShading.pointMultiplicity p : ENNReal) ≤
        Kakeya.realRpowENN rho.1 (-sigma - epsilon)
  fiber_multiplicity_upper :
    ∀ j p,
      ((U.cover rho).toFactoring.fiberPointMultiplicity
          refined j p : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1)
          (-sigma - epsilon)
  cellCount : ℕ
  cell : Point3 → Fin cellCount
  cell_measurable : Measurable cell
  same_cell_induced_subshading :
    ∀ j c,
      {p | p ∈ coarseShading.carrier j ∧ cell p = c} ⊆
        ((U.coarse rho).tube j).carrier ∩
          Metric.cthickening rho.1
            {q |
              ∃ i,
                (U.cover rho).parent i = j ∧
                q ∈ refined.carrier i ∧
                cell q = c}
  cellMass : ENNReal
  cellMass_pos : 0 < cellMass
  cellMass_ne_top : cellMass ≠ ⊤
  fiberCellMass : ENNReal
  fiberCellMass_pos : 0 < fiberCellMass
  fiberCellMass_ne_top : fiberCellMass ≠ ⊤
  cell_diameter :
    ∀ p ∈ coarseShading.union,
      ∀ q ∈ coarseShading.union,
        cell p = cell q →
          dist p q ≤ 2 * rho.1
  coarse_cell_volume_lower :
    ∀ c : Fin cellCount,
      {p | p ∈ coarseShading.union ∧
        cell p = c}.Nonempty →
      Kakeya.realRpowENN rho.1 3 / 1000000 ≤
        volume
          {p | p ∈ coarseShading.union ∧ cell p = c}
  coarse_cell_saturation :
    ∀ j c,
      {p | p ∈ coarseShading.carrier j ∧
        cell p = c}.Nonempty →
      {p | p ∈ coarseShading.union ∧ cell p = c} ⊆
        coarseShading.carrier j
  cell_balance :
    ∀ c : Fin cellCount,
      {p | p ∈ coarseShading.union ∧
        cell p = c}.Nonempty →
      cellMass ≤
          volume
            (refined.union ∩ {p | cell p = c}) ∧
        volume
            (refined.union ∩ {p | cell p = c}) ≤
          2 * cellMass
  fiber_cell_balance :
    ∀ j c,
      {p | p ∈ coarseShading.carrier j ∧
        cell p = c}.Nonempty →
      fiberCellMass ≤
          volume
            ((U.cover rho).toFactoring.fiberShadedUnion
                refined j ∩ {p | cell p = c}) ∧
        volume
            ((U.cover rho).toFactoring.fiberShadedUnion
                refined j ∩ {p | cell p = c}) ≤
          2 * fiberCellMass
  representative : Fin cellCount → Point3
  cell_fine_witness :
    ∀ p ∈ coarseShading.union,
      representative (cell p) ∈ refined.union ∧
        cell (representative (cell p)) = cell p
  representative_associated :
    ∀ j p, p ∈ coarseShading.carrier j →
      ∃ i,
        (U.cover rho).parent i = j ∧
          representative (cell p) ∈ refined.carrier i
  neighborBound : ℕ
  neighborBound_pos : 0 < neighborBound
  neighborBound_le : neighborBound ≤ 10000
  nearby_active_cells :
    ∀ c : Fin cellCount,
      {p | p ∈ coarseShading.union ∧
        cell p = c}.Nonempty →
      wz1NearbyActiveCellCount
        coarseShading cell representative c ≤ neighborBound

namespace WZ1RootRelativeScaleCoverData

/--
Recover the full intermediate extremality certificate on one selected coarse
family.

The coarse uniform structure is an independent paper-level good-cover choice.
It is not inherited from the root structure and carries no transition maps to
the root cover or to another schedule coordinate.
-/
lemma coarse_wz1_extremal
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {refined : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (data :
      WZ1RootRelativeScaleCoverData
        (sigma := sigma) (epsilon := epsilon)
        U refined rho) :
    WZ1ExtremalPair sigma epsilon
      (U.coarse rho) data.coarseUniform data.coarseShading := by
  rcases data.coarse_extremal with
    ⟨hrho, hrhoOne, hnonempty, hwindow, hdistinct,
      hdense, hupper, hlower⟩
  exact
    ⟨hrho, hrhoOne, hnonempty, hwindow, hdistinct,
      data.coarse_uniformity_bound, data.coarse_frostman_bound,
      hdense, hupper, hlower⟩

end WZ1RootRelativeScaleCoverData

/--
One finite schedule of independent Proposition 5 covers on a common root
refinement.

The same fine shading is used at every schedule coordinate.  Conditional
parent-cell uniformity supplies the finite recursive closure, while the
related-parent field supplies only the paper's fixed-dilation geometry.
-/
structure WZ1RootRelativeBalancedCoverData
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    {scaleCount : ℕ}
    (schedule :
      Fin scaleCount →
        Kakeya.Streamlined.AdmissibleScale delta)
    (depth : ℕ) where
  refined : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading refined Y
  refined_extremal :
    WZ1ExtremalPair sigma epsilon F U refined
  fineMultiplicity : ℕ
  fineMultiplicity_pos : 0 < fineMultiplicity
  fine_constant_multiplicity :
    refined.HasConstantMultiplicity
      fineMultiplicity (2 * fineMultiplicity)
  fine_multiplicity_lower :
    Kakeya.realRpowENN delta (-sigma + epsilon) ≤
      (fineMultiplicity : ENNReal)
  retained_mass :
    Kakeya.realRpowENN delta epsilon * Y.mass ≤
      refined.mass
  conditionalConstant : ENNReal
  conditionalConstant_one : 1 ≤ conditionalConstant
  conditionalConstant_ne_top : conditionalConstant ≠ ⊤
  conditionalConstant_power :
    conditionalConstant ^ (2 * depth) ≤
      Kakeya.realRpowENN delta (-epsilon)
  conditional_uniformity :
    WZ1RootScheduledConditionalUniformity
      depth U refined schedule conditionalConstant
  atScale :
    ∀ s,
      WZ1RootRelativeScaleCoverData
        (sigma := sigma) (epsilon := epsilon)
        U refined (schedule s)
  related_parent_containment :
    ∀ s t, (schedule s).1 ≤ (schedule t).1 →
      ∀ j : Fin (U.coarse (schedule s)).card,
        ∀ k : Fin (U.coarse (schedule t)).card,
          WZ1RootParentRelation
              U refined (schedule s) (schedule t) j k →
            ((U.coarse (schedule s)).tube j).carrier ⊆
              wz1DilatedTubeCarrier 13
                ((U.coarse (schedule t)).tube k)

namespace WZ1RootRelativeBalancedCoverData

/--
Expose one schedule coordinate as the ordinary single-scale balanced-cover
package consumed by WZ1 Lemmas 12--15.

The returned coarse uniform structure is the independent certificate stored
at this coordinate.  This adapter adds no transition maps and does not claim
that the root structure recursively induces the coarse one.
-/
noncomputable def toBalancedCoverData
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {scaleCount : ℕ}
    {schedule :
      Fin scaleCount →
        Kakeya.Streamlined.AdmissibleScale delta}
    {depth : ℕ}
    (cover :
      WZ1RootRelativeBalancedCoverData
        (sigma := sigma) (epsilon := epsilon)
        U Y schedule depth)
    (coordinate : Fin scaleCount) :
    WZ1BalancedCoverData
      (sigma := sigma) (epsilon := epsilon)
      U Y (schedule coordinate) where
  refined := cover.refined
  subshading := cover.subshading
  refined_extremal := cover.refined_extremal
  fineMultiplicity := cover.fineMultiplicity
  fineMultiplicity_pos := cover.fineMultiplicity_pos
  fine_constant_multiplicity := cover.fine_constant_multiplicity
  fine_multiplicity_lower := cover.fine_multiplicity_lower
  fiberMultiplicity := (cover.atScale coordinate).fiberMultiplicity
  fiberMultiplicity_pos :=
    (cover.atScale coordinate).fiberMultiplicity_pos
  fiber_constant_multiplicity :=
    (cover.atScale coordinate).fiber_constant_multiplicity
  coarseShading := (cover.atScale coordinate).coarseShading
  coarseUniform := (cover.atScale coordinate).coarseUniform
  coarse_extremal :=
    (cover.atScale coordinate).coarse_wz1_extremal
  induced_subshading :=
    (cover.atScale coordinate).induced_subshading
  coarse_nonempty := (cover.atScale coordinate).coarse_nonempty
  coarseMultiplicity := (cover.atScale coordinate).coarseMultiplicity
  coarseMultiplicity_pos :=
    (cover.atScale coordinate).coarseMultiplicity_pos
  coarse_constant_multiplicity :=
    (cover.atScale coordinate).coarse_constant_multiplicity
  point_compatibility :=
    (cover.atScale coordinate).point_compatibility
  direction_alignment :=
    (cover.atScale coordinate).direction_alignment
  coarse_multiplicity_upper :=
    (cover.atScale coordinate).coarse_multiplicity_upper
  fiber_multiplicity_upper :=
    (cover.atScale coordinate).fiber_multiplicity_upper
  cellCount := (cover.atScale coordinate).cellCount
  cell := (cover.atScale coordinate).cell
  cell_measurable := (cover.atScale coordinate).cell_measurable
  same_cell_induced_subshading :=
    (cover.atScale coordinate).same_cell_induced_subshading
  cellMass := (cover.atScale coordinate).cellMass
  cellMass_pos := (cover.atScale coordinate).cellMass_pos
  cellMass_ne_top := (cover.atScale coordinate).cellMass_ne_top
  fiberCellMass := (cover.atScale coordinate).fiberCellMass
  fiberCellMass_pos := (cover.atScale coordinate).fiberCellMass_pos
  fiberCellMass_ne_top :=
    (cover.atScale coordinate).fiberCellMass_ne_top
  cell_diameter := (cover.atScale coordinate).cell_diameter
  coarse_cell_volume_lower :=
    (cover.atScale coordinate).coarse_cell_volume_lower
  coarse_cell_saturation :=
    (cover.atScale coordinate).coarse_cell_saturation
  cell_balance := (cover.atScale coordinate).cell_balance
  fiber_cell_balance :=
    (cover.atScale coordinate).fiber_cell_balance
  representative := (cover.atScale coordinate).representative
  cell_fine_witness :=
    (cover.atScale coordinate).cell_fine_witness
  representative_associated :=
    (cover.atScale coordinate).representative_associated
  neighborBound := (cover.atScale coordinate).neighborBound
  neighborBound_pos :=
    (cover.atScale coordinate).neighborBound_pos
  neighborBound_le := (cover.atScale coordinate).neighborBound_le
  nearby_active_cells :=
    (cover.atScale coordinate).nearby_active_cells

end WZ1RootRelativeBalancedCoverData

/--
Finite-schedule Proposition 5 conclusion parameterized by the critical-floor
interface used to restore extremality after the common fine refinement.
-/
def WZ1RootRelativeBalancedCoverConclusionWith
    (criticalFloor : ℝ → Prop) : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
    criticalFloor sigma →
    ∀ depth scaleCount : ℕ,
      1 ≤ depth → 0 < scaleCount →
      ∀ outputLoss scaleLoss : ℝ,
        0 < outputLoss → 0 < scaleLoss →
        ∃ inputLoss delta₀ : ℝ,
          0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  WZ1ExtremalPair sigma inputLoss F U Y →
                  ∀ schedule :
                      Fin scaleCount →
                        Kakeya.Streamlined.AdmissibleScale delta,
                    (∀ s,
                      Real.rpow delta (1 - scaleLoss) ≤
                          (schedule s).1 ∧
                        (schedule s).1 ≤
                          Real.rpow delta scaleLoss) →
                    Nonempty
                      (WZ1RootRelativeBalancedCoverData
                        (sigma := sigma)
                        (epsilon := outputLoss)
                        U Y schedule depth)

/--
Forensic ordinary-floor interface.

The former normalization
`HasCriticalVolumeFloor sigma → HasWZ1CriticalVolumeFloor sigma` used a
coherent transition hierarchy that is no longer part of the paper-level
`UniformTubeStructure`.  This proposition is retained only so historical
branches remain readable; canonical producers must not consume it.
-/
def WZ1RootRelativeBalancedCoverLegacyConclusion : Prop :=
  WZ1RootRelativeBalancedCoverConclusionWith
    HasCriticalVolumeFloor

/--
Paper-faithful finite-schedule Proposition 5 conclusion.

The caller supplies the cropped critical-volume floor actually used by the
WZ1 refinement.  This avoids smuggling the retired coherent critical-floor
normalization into the root-relative Proposition 5 theorem.
-/
def WZ1RootRelativeBalancedCoverConclusion : Prop :=
  WZ1RootRelativeBalancedCoverConclusionWith
    HasWZ1CriticalVolumeFloor

/-- Forensic producer retaining the invalid ordinary-floor dependency. -/
def WZ1RootRelativeBalancedCoverLegacyStatement : Prop :=
  WZ1IndependentParentContainmentInput →
    WZ1RootRelativeBalancedCoverLegacyConclusion

/--
Replacement producer for the retired recursive balanced-cover theorem.

The shared geometric containment theorem is an explicit input owned by the
Streamlined cover infrastructure.  All remaining construction is WZ1-owned.
-/
def WZ1RootRelativeBalancedCoverStatement : Prop :=
  WZ1IndependentParentContainmentInput →
    WZ1RootRelativeBalancedCoverConclusion

end Kakeya.Assouad
