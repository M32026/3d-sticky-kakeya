import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarsePlaneMap
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume

/-!
# Mass comparison for source-witness coarse shadings

The source-witness reconstruction deletes only parent-cell memberships.  It
does not delete spatial cells: its union is exactly the original balanced
coarse union.  Hence the loss from the original indexed shading mass to the
source-witness mass is bounded by any pointwise multiplicity cap for the
original coarse shading.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- Reconstructing parent-specific honest source witnesses preserves the full
balanced coarse union. -/
lemma source_witness_coarse_shading_union_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced) :
    sourceWitness.shading.union = coarseShading.union := by
  rw [sourceWitness.balanced.coarse_union_eq,
    sourceWitness.balanced_activeCells_eq, balanced.coarse_union_eq]

/-- A pointwise multiplicity cap is the exact indexed-mass price of deleting
unsupported parent-cell memberships. -/
theorem source_witness_coarse_shading_mass_lower
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced)
    (multiplicityCap : ENNReal)
    (hcapZero : multiplicityCap ≠ 0)
    (hcapTop : multiplicityCap ≠ ⊤)
    (hcap : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤
        multiplicityCap) :
    multiplicityCap⁻¹ * coarseShading.mass ≤
      sourceWitness.shading.mass := by
  have horiginalMass : coarseShading.mass ≤
      multiplicityCap * volume coarseShading.union :=
    mass_le_of_pointMultiplicity_le fun point _ => hcap point
  have hwitnessVolume : volume sourceWitness.shading.union ≤
      sourceWitness.shading.mass := by
    simpa using multiplicity_floor_le_mass
      (one_le_pointMultiplicity_on_union sourceWitness.shading)
  calc
    multiplicityCap⁻¹ * coarseShading.mass ≤
        multiplicityCap⁻¹ *
          (multiplicityCap * volume coarseShading.union) := by gcongr
    _ = volume coarseShading.union := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hcapZero hcapTop, one_mul]
    _ = volume sourceWitness.shading.union := by
      rw [source_witness_coarse_shading_union_eq sourceWitness]
    _ ≤ sourceWitness.shading.mass := hwitnessVolume

/-- Specialization to the public Node-3 coarse multiplicity cap. -/
theorem source_witness_coarse_shading_mass_lower_of_sticky
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent}
    (sourceWitness :
      PureWZ2SourceWitnessCoarseShadingData sticky.balanced) :
    (Kakeya.realRpowENN rho.1 (2 - sigma - outputLoss) *
        sticky.coarse.enncard)⁻¹ *
          sticky.croppedCoarseShading.mass ≤
      sourceWitness.shading.mass := by
  let cap : ENNReal :=
    Kakeya.realRpowENN rho.1 (2 - sigma - outputLoss) *
      sticky.coarse.enncard
  have hrho : 0 < rho.1 := sticky.coarse_extremal.delta_pos
  have hcoarseNonempty : sticky.coarse.Nonempty :=
    sticky.coarse_extremal.nonempty
  have hpowerZero :
      Kakeya.realRpowENN rho.1 (2 - sigma - outputLoss) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hrho (2 - sigma - outputLoss))).ne'
  have hcardZero : sticky.coarse.enncard ≠ 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using
      hcoarseNonempty.ne'
  have hcapZero : cap ≠ 0 := mul_ne_zero hpowerZero hcardZero
  have hcapTop : cap ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (by simp [Kakeya.Streamlined.TubeFamily.enncard])
  simpa [cap] using source_witness_coarse_shading_mass_lower
    sourceWitness cap hcapZero hcapTop sticky.coarse_multiplicity_upper

/-- Compose the honest-membership loss with a subsequent common-spatial
refinement of fixed cost `refinementCost`. -/
theorem source_witness_coarse_refinement_mass_lower
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading selected : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced)
    (multiplicityCap refinementCost : ENNReal)
    (hcapZero : multiplicityCap ≠ 0)
    (hcapTop : multiplicityCap ≠ ⊤)
    (hcostZero : refinementCost ≠ 0)
    (hcostTop : refinementCost ≠ ⊤)
    (hcap : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤
        multiplicityCap)
    (hrefinement : sourceWitness.shading.mass ≤
      refinementCost * selected.mass) :
    (multiplicityCap * refinementCost)⁻¹ * coarseShading.mass ≤
      selected.mass := by
  have hwitness := source_witness_coarse_shading_mass_lower
    sourceWitness multiplicityCap hcapZero hcapTop hcap
  have hinv : (multiplicityCap * refinementCost)⁻¹ =
      refinementCost⁻¹ * multiplicityCap⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hcapZero) (Or.inl hcapTop)]
    ac_rfl
  rw [hinv]
  calc
    refinementCost⁻¹ * multiplicityCap⁻¹ * coarseShading.mass =
        refinementCost⁻¹ *
          (multiplicityCap⁻¹ * coarseShading.mass) := by ring
    _ ≤ refinementCost⁻¹ * sourceWitness.shading.mass := by gcongr
    _ ≤ refinementCost⁻¹ * (refinementCost * selected.mass) := by gcongr
    _ = selected.mass := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hcostZero hcostTop, one_mul]

/-- A fine multiplicity floor and a uniform full-fiber cap give a coarse
multiplicity floor on the honest source-witness shading.  The fine lower
bound is used at the stored shaded witness in the same coarse cell; coarse
cubicality then transports the coarse multiplicity back to the query point.
This avoids the invalid same-point comparison at unshaded coarse points. -/
theorem source_witness_coarse_multiplicity_floor
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced : PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced)
    (fineFloor fiberCap : ENNReal)
    (hfiberPos : 0 < fiberCap)
    (hfiberTop : fiberCap ≠ ⊤)
    (hfineFloor : ∀ point ∈ fineShading.union,
      fineFloor ≤ (fineShading.pointMultiplicity point : ENNReal))
    (hfiberCap : ∀ parent point,
      (cover.toPaperTubeCover.fiberPointMultiplicity
          fineShading parent point : ENNReal) ≤ fiberCap) :
    ∀ point ∈ sourceWitness.shading.union,
      fineFloor * fiberCap⁻¹ ≤
        (sourceWitness.shading.pointMultiplicity point : ENNReal) := by
  intro point hpoint
  rcases hpoint with ⟨parent, hpointParent⟩
  rw [sourceWitness.shading_carrier_eq parent] at hpointParent
  rcases Set.mem_iUnion.mp hpointParent with ⟨cell, hpointParent⟩
  rcases Set.mem_iUnion.mp hpointParent with ⟨hcell, hpointCell⟩
  rcases sourceWitness.source_witness parent cell hcell with
    ⟨source, witness, hsourceParent, hwitnessFine, hwitnessCell⟩
  have hwitnessUnion : witness ∈ fineShading.union :=
    ⟨source, hwitnessFine⟩
  have hpointwise :=
    cover.toPaperTubeCover.pointMultiplicity_le_coarseMultiplicity_mul_fiber
      fineShading sourceWitness.shading
      (fun source point hpoint =>
        sourceWitness.balanced.point_compatibility source
          (cover.toPaperTubeCover.parent source)
          (cover.toPaperTubeCover.parent_covers source) point hpoint)
      hfiberCap witness
  have hraw : fineFloor ≤
      (sourceWitness.shading.pointMultiplicity witness : ENNReal) *
        fiberCap :=
    (hfineFloor witness hwitnessUnion).trans hpointwise
  have hsameCell : wz1PaperGridIndex rho witness =
      wz1PaperGridIndex rho point := by
    exact ((mem_wz1PaperGridCube rho cell witness).mp hwitnessCell).trans
      ((mem_wz1PaperGridCube rho cell point).mp hpointCell).symm
  have hmultiplicityEq :
      sourceWitness.shading.pointMultiplicity witness =
        sourceWitness.shading.pointMultiplicity point :=
    sourceWitness.balanced.coarse_cubical
      |>.pointMultiplicity_eq_of_same_cell hsameCell
  have hscaled := mul_le_mul_left' hraw fiberCap⁻¹
  have hcancel : fiberCap * fiberCap⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hfiberPos.ne' hfiberTop
  calc
    fineFloor * fiberCap⁻¹ = fiberCap⁻¹ * fineFloor := by ring
    _ ≤ fiberCap⁻¹ *
        ((sourceWitness.shading.pointMultiplicity point : ENNReal) *
          fiberCap) := by
      simpa [hmultiplicityEq] using hscaled
    _ = (sourceWitness.shading.pointMultiplicity point : ENNReal) := by
      rw [show fiberCap⁻¹ *
          ((sourceWitness.shading.pointMultiplicity point : ENNReal) *
            fiberCap) =
        (sourceWitness.shading.pointMultiplicity point : ENNReal) *
          (fiberCap * fiberCap⁻¹) by ring, hcancel, mul_one]

end Kakeya.Assouad.PureWZ2

end
