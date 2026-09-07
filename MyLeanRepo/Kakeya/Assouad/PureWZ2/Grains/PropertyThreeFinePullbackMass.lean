import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellMassConversion
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume

/-! Quantitative whole-cell mass retention for the Property-P fine pullback. -/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- Active coarse cells touched by a retained Property-P shading. -/
def propertyThreeGoodCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (propertyThree : WZ1PaperTubeShading coarse) :
    Finset (ℤ × ℤ × ℤ) :=
  balanced.activeCells.filter fun cell =>
    (propertyThree.union ∩ wz1PaperGridCube rho cell).Nonempty

@[simp] lemma mem_propertyThreeGoodCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (propertyThree : WZ1PaperTubeShading coarse)
    (cell : ℤ × ℤ × ℤ) :
    cell ∈ propertyThreeGoodCells balanced propertyThree ↔
      cell ∈ balanced.activeCells ∧
        (propertyThree.union ∩ wz1PaperGridCube rho cell).Nonempty := by
  simp [propertyThreeGoodCells]

/-- A cubical Property-P subshading is precisely the union of its good active
coarse cells. -/
lemma propertyThree_union_eq_goodCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading propertyThree : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hsub : PaperIsSubshading propertyThree coarseShading)
    (hcubical : WZ1PaperIsCubicalShading propertyThree) :
    propertyThree.union =
      ⋃ cell ∈ propertyThreeGoodCells balanced propertyThree,
        wz1PaperGridCube rho cell := by
  apply Set.Subset.antisymm
  · intro point hpoint
    have hcoarse : point ∈ coarseShading.union := by
      rcases hpoint with ⟨parent, hparent⟩
      exact ⟨parent, hsub parent hparent⟩
    rw [balanced.coarse_union_eq] at hcoarse
    rcases Set.mem_iUnion₂.mp hcoarse with ⟨cell, hcell, hpointCell⟩
    have hgood : cell ∈ propertyThreeGoodCells balanced propertyThree := by
      apply (mem_propertyThreeGoodCells balanced propertyThree cell).mpr
      exact ⟨hcell, ⟨point, hpoint, hpointCell⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨cell, hgood, hpointCell⟩
  · intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hgood, hpointCell⟩
    rcases (mem_propertyThreeGoodCells balanced propertyThree cell).mp hgood with
      ⟨_, witness, hwitness, hwitnessCell⟩
    rcases hwitness with ⟨parent, hparent⟩
    refine ⟨parent, hcubical parent witness hparent ?_⟩
    have hindex : wz1PaperGridIndex rho witness = cell :=
      (mem_wz1PaperGridCube rho cell witness).mp hwitnessCell
    apply (mem_wz1PaperGridCube rho
      (wz1PaperGridIndex rho witness) point).mpr
    exact ((mem_wz1PaperGridCube rho cell point).mp hpointCell).trans hindex.symm

lemma propertyThree_volume_eq_goodCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading propertyThree : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hsub : PaperIsSubshading propertyThree coarseShading)
    (hcubical : WZ1PaperIsCubicalShading propertyThree)
    (hrho : 0 < rho) :
    volume propertyThree.union =
      ((propertyThreeGoodCells balanced propertyThree).card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  rw [propertyThree_union_eq_goodCells balanced hsub hcubical]
  exact wz1PaperGridCube_volume_biUnion hrho
    (propertyThreeGoodCells balanced propertyThree)

/-- The fine pullback union is the balanced fine union restricted to the same
good spatial cells. -/
lemma propertyThreeFinePullback_union_eq_goodCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading propertyThree : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hsub : PaperIsSubshading propertyThree coarseShading) :
    (propertyThreeFinePullbackShading cover fineShading propertyThree).union =
      ⋃ cell ∈ propertyThreeGoodCells balanced propertyThree,
        (fineShading.union ∩ wz1PaperGridCube rho cell) := by
  apply Set.Subset.antisymm
  · rintro point ⟨source, hsource⟩
    rcases propertyThreeFinePullbackShading_support
        cover fineShading propertyThree source point hsource with
      ⟨witness, hwitness, hgrid⟩
    have hcoarse : witness ∈ coarseShading.union := by
      rcases hwitness with ⟨parent, hparent⟩
      exact ⟨parent, hsub parent hparent⟩
    rw [balanced.coarse_union_eq] at hcoarse
    rcases Set.mem_iUnion₂.mp hcoarse with ⟨cell, hcell, hwitnessCell⟩
    have hgood : cell ∈ propertyThreeGoodCells balanced propertyThree := by
      apply (mem_propertyThreeGoodCells balanced propertyThree cell).mpr
      exact ⟨hcell, ⟨witness, hwitness, hwitnessCell⟩⟩
    have hpointCell : point ∈ wz1PaperGridCube rho cell := by
      apply (mem_wz1PaperGridCube rho cell point).mpr
      have hw : wz1PaperGridIndex rho witness = cell :=
        (mem_wz1PaperGridCube rho cell witness).mp hwitnessCell
      exact hgrid.symm.trans hw
    exact Set.mem_iUnion₂.mpr ⟨cell, hgood, ⟨⟨source, hsource.1⟩, hpointCell⟩⟩
  · intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hgood, hfine, hpointCell⟩
    rcases hfine with ⟨source, hsource⟩
    rcases (mem_propertyThreeGoodCells balanced propertyThree cell).mp hgood with
      ⟨_, witness, hwitness, hwitnessCell⟩
    refine ⟨source, hsource, ?_⟩
    refine ⟨witness, hwitness, ?_⟩
    exact ((mem_wz1PaperGridCube rho cell witness).mp hwitnessCell).trans
      ((mem_wz1PaperGridCube rho cell point).mp hpointCell).symm

lemma propertyThreeFinePullback_volume_eq_goodCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading propertyThree : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hsub : PaperIsSubshading propertyThree coarseShading) :
    volume (propertyThreeFinePullbackShading cover fineShading propertyThree).union =
      ((propertyThreeGoodCells balanced propertyThree).card : ENNReal) *
        balanced.cellMass := by
  rw [propertyThreeFinePullback_union_eq_goodCells balanced hsub]
  have hdisjoint : Set.PairwiseDisjoint
      (↑(propertyThreeGoodCells balanced propertyThree))
      (fun cell => fineShading.union ∩ wz1PaperGridCube rho cell) := by
    intro first _ second _ hne
    exact (wz1PaperGridCube_disjoint hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ cell ∈ propertyThreeGoodCells balanced propertyThree,
      MeasurableSet (fineShading.union ∩ wz1PaperGridCube rho cell) := by
    intro cell _
    exact (measurableSet_shading_union fineShading).inter
      (wz1PaperGridCube_measurable cell)
  rw [MeasureTheory.measure_biUnion_finset hdisjoint hmeas]
  calc
    (∑ cell ∈ propertyThreeGoodCells balanced propertyThree,
        volume (fineShading.union ∩ wz1PaperGridCube rho cell)) =
        ∑ _cell ∈ propertyThreeGoodCells balanced propertyThree,
          balanced.cellMass := by
      apply Finset.sum_congr rfl
      intro cell hcell
      exact balanced.fine_cell_mass cell
        ((mem_propertyThreeGoodCells balanced propertyThree cell).mp hcell).1
    _ = ((propertyThreeGoodCells balanced propertyThree).card : ENNReal) *
        balanced.cellMass := by simp [Finset.sum_const]

/-- A pointwise coarse multiplicity cap bounds the coarse shaded mass by the
number of balanced cells times one cube volume. -/
lemma coarse_mass_le_activeCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hrho : 0 < rho)
    (coarseCap : ENNReal)
    (hcoarse : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ coarseCap) :
    coarseShading.mass ≤
      coarseCap * (balanced.activeCells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  calc
    coarseShading.mass ≤ coarseCap * volume coarseShading.union :=
      mass_le_of_pointMultiplicity_le (fun point _ => hcoarse point)
    _ = coarseCap * ((balanced.activeCells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0))) := by
      rw [balanced_cover_coarse_volume balanced hrho]
    _ = coarseCap * (balanced.activeCells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by ring

/-- The selected unique-parent cover converts the Node-3 coarse/fiber caps
into one pointwise fine multiplicity cap. -/
lemma fine_pointMultiplicity_le_coarse_mul_fiber
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (coarseCap fiberCap : ENNReal)
    (hcoarse : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ coarseCap)
    (hfiber : ∀ parent point,
      (wz2PaperFullFiberPointMultiplicity coarse fineShading parent point : ENNReal) ≤
        fiberCap) :
    ∀ point,
      (fineShading.pointMultiplicity point : ENNReal) ≤
        coarseCap * fiberCap := by
  have hcompat : ∀ source point,
      point ∈ fineShading.carrier source →
        point ∈ coarseShading.carrier
          (cover.toPaperTubeCover.parent source) := by
    intro source point hpoint
    exact balanced.point_compatibility source
      (PureWZ2.selectParent cover source)
      (PureWZ2.selectedParent_covers cover source) point hpoint
  have hfiber' : ∀ parent point,
      (cover.toPaperTubeCover.fiberPointMultiplicity
          fineShading parent point : ENNReal) ≤ fiberCap := by
    intro parent point
    rw [← cover.fullFiberPointMultiplicity_eq fineShading parent point]
    exact hfiber parent point
  exact cover.toPaperTubeCover.pointMultiplicity_le_coarse_mul_fiber
    fineShading coarseShading hcompat hcoarse hfiber'

lemma fine_mass_le_activeCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hrho : 0 < rho)
    (coarseCap fiberCap : ENNReal)
    (hcoarse : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ coarseCap)
    (hfiber : ∀ parent point,
      (wz2PaperFullFiberPointMultiplicity coarse fineShading parent point : ENNReal) ≤
        fiberCap) :
    fineShading.mass ≤
      (coarseCap * fiberCap) *
        ((balanced.activeCells.card : ENNReal) * balanced.cellMass) := by
  calc
    fineShading.mass ≤ (coarseCap * fiberCap) * volume fineShading.union :=
      mass_le_of_pointMultiplicity_le
        (fun point _ => fine_pointMultiplicity_le_coarse_mul_fiber
          balanced coarseCap fiberCap hcoarse hfiber point)
    _ = (coarseCap * fiberCap) *
        ((balanced.activeCells.card : ENNReal) * balanced.cellMass) := by
      rw [balanced_cover_fine_union_volume balanced hrho]

/-- The uniform coarse multiplicity cap carried by one Node-3 sticky output. -/
def stickyCoarseMultiplicityCap
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) : ENNReal :=
  Kakeya.realRpowENN rho.1 (2 - sigma - outputLoss) *
    sticky.coarse.enncard

/-- A parent-independent full-fiber cap obtained from the Node-3 fiber bound
by bounding every full fiber by the entire selected fine family. -/
def stickyFiberMultiplicityCap
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) : ENNReal :=
  Kakeya.realRpowENN (delta / rho.1) (2 - sigma - outputLoss) *
    sticky.selected.family.enncard

/-- Quantitative whole-cell pullback for an arbitrary two-sided coarse mass
comparison.  This is the form needed after the dependent full-grain step,
whose right-hand loss must remain visible rather than be cancelled in
`ENNReal`. -/
lemma propertyThreeFinePullback_mass_lower_of_comparison
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading propertyThree : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hsub : PaperIsSubshading propertyThree coarseShading)
    (hcubical : WZ1PaperIsCubicalShading propertyThree)
    (hrho : 0 < rho)
    (coarseCap fiberCap : ENNReal)
    (hcoarseCap_zero : coarseCap ≠ 0)
    (hcoarseCap_top : coarseCap ≠ ⊤)
    (hfiberCap_zero : fiberCap ≠ 0)
    (hfiberCap_top : fiberCap ≠ ⊤)
    (hcoarse : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ coarseCap)
    (hfiber : ∀ parent point,
      (wz2PaperFullFiberPointMultiplicity coarse fineShading parent point : ENNReal) ≤
        fiberCap)
    (leftFactor rightFactor : ENNReal)
    (hretained : leftFactor * coarseShading.mass ≤
      rightFactor * propertyThree.mass) :
    (leftFactor *
        (coarseCap * coarseCap * fiberCap : ENNReal)⁻¹) * fineShading.mass ≤
      rightFactor *
        (propertyThreeFinePullbackShading cover fineShading propertyThree).mass := by
  let active : ENNReal := balanced.activeCells.card
  let good : ENNReal := (propertyThreeGoodCells balanced propertyThree).card
  let cubeVolume : ENNReal := volume (wz1PaperGridCube rho (0, 0, 0))
  let cellMass : ENNReal := balanced.cellMass
  have hproperty_mass_upper :
      propertyThree.mass ≤ coarseCap * (good * cubeVolume) := by
    calc
      propertyThree.mass ≤ coarseCap * volume propertyThree.union :=
        mass_le_of_pointMultiplicity_le (fun point hpoint => by
          have hnat := paperSubshading_pointMultiplicity_le
            propertyThree coarseShading hsub point
          have henn : (propertyThree.pointMultiplicity point : ENNReal) ≤
              (coarseShading.pointMultiplicity point : ENNReal) := by
            exact_mod_cast hnat
          exact henn.trans (hcoarse point))
      _ = coarseCap * (good * cubeVolume) := by
        rw [propertyThree_volume_eq_goodCells balanced hsub hcubical hrho]
  have hgood_scaled :
      leftFactor * coarseShading.mass ≤
        rightFactor * (coarseCap * (good * cubeVolume)) :=
    hretained.trans (mul_le_mul_left' hproperty_mass_upper rightFactor)
  have hvolume_le_mass :
      volume coarseShading.union ≤ coarseShading.mass := by
    simpa using multiplicity_floor_le_mass
      (one_le_pointMultiplicity_on_union coarseShading)
  have hactive_with_cube :
      (leftFactor * active) * cubeVolume ≤
        (rightFactor * (coarseCap * good)) * cubeVolume := by
    calc
      (leftFactor * active) * cubeVolume =
          leftFactor * volume coarseShading.union := by
        dsimp only [active, cubeVolume]
        rw [balanced_cover_coarse_volume balanced hrho]
        ring
      _ ≤ leftFactor * coarseShading.mass := by gcongr
      _ ≤ rightFactor * (coarseCap * (good * cubeVolume)) := hgood_scaled
      _ = (rightFactor * (coarseCap * good)) * cubeVolume := by ring
  have hcube_zero : cubeVolume ≠ 0 := by
    exact (wz1PaperGridCube_volume_pos hrho (0, 0, 0)).ne'
  have hcube_top : cubeVolume ≠ ⊤ := by
    exact wz1PaperGridCube_volume_ne_top hrho (0, 0, 0)
  have hactive_count :
      leftFactor * active ≤ rightFactor * (coarseCap * good) :=
    (ENNReal.mul_le_mul_iff_right hcube_zero hcube_top).mp <| by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hactive_with_cube
  have hgood_count :
      coarseCap⁻¹ * (leftFactor * active) ≤ rightFactor * good := by
    calc
      coarseCap⁻¹ * (leftFactor * active) ≤
          coarseCap⁻¹ * (rightFactor * (coarseCap * good)) := by gcongr
      _ = rightFactor * good := by
        calc
          coarseCap⁻¹ * (rightFactor * (coarseCap * good)) =
              rightFactor * (coarseCap⁻¹ * coarseCap) * good := by ac_rfl
          _ = rightFactor * good := by
            rw [ENNReal.inv_mul_cancel hcoarseCap_zero hcoarseCap_top]
            simp
  have hfine_mass :
      fineShading.mass ≤
        (coarseCap * fiberCap) * (active * cellMass) := by
    simpa [active, cellMass] using
      fine_mass_le_activeCells balanced hrho coarseCap fiberCap hcoarse hfiber
  have hscaled_fine :
      (leftFactor *
          (coarseCap * coarseCap * fiberCap : ENNReal)⁻¹) *
          fineShading.mass ≤
        leftFactor * coarseCap⁻¹ * active * cellMass := by
    calc
      (leftFactor *
          (coarseCap * coarseCap * fiberCap : ENNReal)⁻¹) *
          fineShading.mass ≤
          (leftFactor *
            (coarseCap * coarseCap * fiberCap : ENNReal)⁻¹) *
            ((coarseCap * fiberCap) * (active * cellMass)) := by gcongr
      _ = leftFactor * coarseCap⁻¹ * active * cellMass := by
        have hCinv : coarseCap⁻¹ * coarseCap = 1 :=
          ENNReal.inv_mul_cancel hcoarseCap_zero hcoarseCap_top
        have hFinv : fiberCap⁻¹ * fiberCap = 1 :=
          ENNReal.inv_mul_cancel hfiberCap_zero hfiberCap_top
        have hinv :
            (coarseCap * coarseCap * fiberCap : ENNReal)⁻¹ =
              coarseCap⁻¹ * coarseCap⁻¹ * fiberCap⁻¹ := by
          rw [ENNReal.mul_inv
            (Or.inr hfiberCap_top) (Or.inr hfiberCap_zero)]
          rw [ENNReal.mul_inv
            (Or.inr hcoarseCap_top) (Or.inr hcoarseCap_zero)]
        rw [hinv]
        calc
          (leftFactor *
                (coarseCap⁻¹ * coarseCap⁻¹ * fiberCap⁻¹)) *
                (coarseCap * fiberCap * (active * cellMass)) =
              leftFactor * (coarseCap⁻¹ * coarseCap) *
                (coarseCap⁻¹ * (fiberCap⁻¹ * fiberCap)) *
                (active * cellMass) := by ac_rfl
          _ = leftFactor * coarseCap⁻¹ * active * cellMass := by
            rw [hCinv, hFinv]
            simp
            ac_rfl
  have hscaled_good :
      leftFactor * coarseCap⁻¹ * active * cellMass ≤
        rightFactor * (good * cellMass) := by
    have hrewrite :
        leftFactor * coarseCap⁻¹ * active =
          coarseCap⁻¹ * (leftFactor * active) := by ac_rfl
    rw [hrewrite]
    simpa only [mul_assoc] using mul_le_mul_right' hgood_count cellMass
  have hpull_volume :
      volume (propertyThreeFinePullbackShading cover fineShading propertyThree).union =
        good * cellMass := by
    simpa [good, cellMass] using
      propertyThreeFinePullback_volume_eq_goodCells balanced hsub
  have hpull_volume_le_mass :
      volume (propertyThreeFinePullbackShading cover fineShading propertyThree).union ≤
        (propertyThreeFinePullbackShading cover fineShading propertyThree).mass := by
    simpa using multiplicity_floor_le_mass
      (one_le_pointMultiplicity_on_union
        (propertyThreeFinePullbackShading cover fineShading propertyThree))
  calc
    (leftFactor *
        (coarseCap * coarseCap * fiberCap : ENNReal)⁻¹) * fineShading.mass ≤
        leftFactor * coarseCap⁻¹ * active * cellMass := hscaled_fine
    _ ≤ rightFactor * (good * cellMass) := hscaled_good
    _ = rightFactor *
        volume (propertyThreeFinePullbackShading cover fineShading propertyThree).union := by
      rw [hpull_volume]
    _ ≤ rightFactor *
        (propertyThreeFinePullbackShading cover fineShading propertyThree).mass := by
      gcongr

/-- One-sided specialization of the general comparison ledger. -/
lemma propertyThreeFinePullback_mass_lower_of_retention
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading propertyThree : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hsub : PaperIsSubshading propertyThree coarseShading)
    (hcubical : WZ1PaperIsCubicalShading propertyThree)
    (hrho : 0 < rho)
    (coarseCap fiberCap : ENNReal)
    (hcoarseCap_zero : coarseCap ≠ 0)
    (hcoarseCap_top : coarseCap ≠ ⊤)
    (hfiberCap_zero : fiberCap ≠ 0)
    (hfiberCap_top : fiberCap ≠ ⊤)
    (hcoarse : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ coarseCap)
    (hfiber : ∀ parent point,
      (wz2PaperFullFiberPointMultiplicity coarse fineShading parent point : ENNReal) ≤
        fiberCap)
    (retainedFactor : ENNReal)
    (hretained : retainedFactor * coarseShading.mass ≤ propertyThree.mass) :
    (retainedFactor *
        (coarseCap * coarseCap * fiberCap : ENNReal)⁻¹) * fineShading.mass ≤
      (propertyThreeFinePullbackShading cover fineShading propertyThree).mass := by
  simpa using propertyThreeFinePullback_mass_lower_of_comparison
    balanced hsub hcubical hrho coarseCap fiberCap hcoarseCap_zero
    hcoarseCap_top hfiberCap_zero hfiberCap_top hcoarse hfiber
    retainedFactor 1 (by simpa using hretained)

/-- Property-(P) specialization of the general retained-factor pullback. -/
lemma propertyThreeFinePullback_mass_lower
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading propertyThree : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hsub : PaperIsSubshading propertyThree coarseShading)
    (hcubical : WZ1PaperIsCubicalShading propertyThree)
    (hrho : 0 < rho)
    (coarseCap fiberCap : ENNReal)
    (hcoarseCap_zero : coarseCap ≠ 0)
    (hcoarseCap_top : coarseCap ≠ ⊤)
    (hfiberCap_zero : fiberCap ≠ 0)
    (hfiberCap_top : fiberCap ≠ ⊤)
    (hcoarse : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ coarseCap)
    (hfiber : ∀ parent point,
      (wz2PaperFullFiberPointMultiplicity coarse fineShading parent point : ENNReal) ≤
        fiberCap)
    (hhalf : (1 / 2 : ENNReal) * coarseShading.mass ≤ propertyThree.mass) :
    ((2 * coarseCap * coarseCap * fiberCap : ENNReal)⁻¹) * fineShading.mass ≤
      (propertyThreeFinePullbackShading cover fineShading propertyThree).mass := by
  have hgeneral := propertyThreeFinePullback_mass_lower_of_retention
    balanced hsub hcubical hrho coarseCap fiberCap hcoarseCap_zero
    hcoarseCap_top hfiberCap_zero hfiberCap_top hcoarse hfiber
    (1 / 2 : ENNReal) hhalf
  have hproductZero : coarseCap * coarseCap * fiberCap ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcoarseCap_zero hcoarseCap_zero)
      hfiberCap_zero
  have hproductTop : coarseCap * coarseCap * fiberCap ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hcoarseCap_top hcoarseCap_top) hfiberCap_top
  have hinverse :
      (2 * coarseCap * coarseCap * fiberCap : ENNReal)⁻¹ =
        (1 / 2 : ENNReal) *
          (coarseCap * coarseCap * fiberCap : ENNReal)⁻¹ := by
    rw [show (2 * coarseCap * coarseCap * fiberCap : ENNReal) =
      2 * (coarseCap * coarseCap * fiberCap) by ring]
    rw [ENNReal.mul_inv (Or.inr hproductTop) (Or.inr hproductZero)]
    norm_num [one_div]
  rw [hinverse]
  exact hgeneral

/-- Specialization of the two-sided comparison lemma to the explicit
multiplicity powers supplied by one Node-3 sticky output. -/
lemma propertyThreeFinePullback_mass_lower_of_sticky_comparison
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (hdelta : 0 < delta)
    (hsub : PaperIsSubshading propertyThree sticky.croppedCoarseShading)
    (hcubical : WZ1PaperIsCubicalShading propertyThree)
    (leftFactor rightFactor : ENNReal)
    (hcomparison : leftFactor * sticky.croppedCoarseShading.mass ≤
      rightFactor * propertyThree.mass) :
    (leftFactor *
        (stickyCoarseMultiplicityCap sticky *
          stickyCoarseMultiplicityCap sticky *
          stickyFiberMultiplicityCap sticky : ENNReal)⁻¹) *
        sticky.refined.mass ≤
      rightFactor * (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propertyThree).mass := by
  have hrho : 0 < rho.1 := sticky.coarse_extremal.delta_pos
  have hratio : 0 < delta / rho.1 := div_pos hdelta hrho
  have hcoarse_nonempty : sticky.coarse.Nonempty := by
    let sourceIndex : Fin sticky.selected.family.card :=
      ⟨0, sticky.selected_nonempty⟩
    rcases sticky.cover.covers sourceIndex with ⟨parent, _⟩
    exact Nat.zero_lt_of_lt parent.isLt
  have hcoarse_card_zero : sticky.coarse.enncard ≠ 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using hcoarse_nonempty.ne'
  have hfine_card_zero : sticky.selected.family.enncard ≠ 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using
      sticky.selected_nonempty.ne'
  have hcoarse_power_zero :
      Kakeya.realRpowENN rho.1 (2 - sigma - outputLoss) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hrho (2 - sigma - outputLoss))).ne'
  have hfiber_power_zero :
      Kakeya.realRpowENN (delta / rho.1) (2 - sigma - outputLoss) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hratio (2 - sigma - outputLoss))).ne'
  have hcoarseCap_zero : stickyCoarseMultiplicityCap sticky ≠ 0 := by
    exact mul_ne_zero hcoarse_power_zero hcoarse_card_zero
  have hfiberCap_zero : stickyFiberMultiplicityCap sticky ≠ 0 := by
    exact mul_ne_zero hfiber_power_zero hfine_card_zero
  have hcoarseCap_top : stickyCoarseMultiplicityCap sticky ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp [Kakeya.realRpowENN]
    · simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hfiberCap_top : stickyFiberMultiplicityCap sticky ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp [Kakeya.realRpowENN]
    · simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hcoarse : ∀ point,
      (sticky.croppedCoarseShading.pointMultiplicity point : ENNReal) ≤
        stickyCoarseMultiplicityCap sticky := by
    intro point
    exact sticky.coarse_multiplicity_upper point
  have hfiber : ∀ parent point,
      (wz2PaperFullFiberPointMultiplicity
          sticky.coarse sticky.refined parent point : ENNReal) ≤
        stickyFiberMultiplicityCap sticky := by
    intro parent point
    calc
      (wz2PaperFullFiberPointMultiplicity
          sticky.coarse sticky.refined parent point : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho.1)
              (2 - sigma - outputLoss) *
            ((wz2PaperFullFiberIndices
              sticky.selected.family sticky.coarse parent).card : ENNReal) :=
        sticky.fiber_multiplicity_upper parent point
      _ ≤ Kakeya.realRpowENN (delta / rho.1)
              (2 - sigma - outputLoss) *
            sticky.selected.family.enncard := by
        gcongr
        have hcard :
            (wz2PaperFullFiberIndices
              sticky.selected.family sticky.coarse parent).card ≤
              sticky.selected.family.card := by
          simpa using (Finset.card_le_univ
            (s := wz2PaperFullFiberIndices
              sticky.selected.family sticky.coarse parent))
        simpa [Kakeya.Streamlined.TubeFamily.enncard] using hcard
  exact propertyThreeFinePullback_mass_lower_of_comparison
    sticky.balanced hsub hcubical hrho
    (stickyCoarseMultiplicityCap sticky)
    (stickyFiberMultiplicityCap sticky)
    hcoarseCap_zero hcoarseCap_top hfiberCap_zero hfiberCap_top
    hcoarse hfiber leftFactor rightFactor hcomparison

/-- Property-(P) specialization with its fixed half-mass retention.  The
resulting constant is uniform in the parent: the cardinality of an individual
full fiber is bounded by the cardinality of the selected fine family. -/
lemma propertyThreeFinePullback_mass_lower_of_sticky
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (hdelta : 0 < delta)
    (hsub : PaperIsSubshading propertyThree sticky.croppedCoarseShading)
    (hcubical : WZ1PaperIsCubicalShading propertyThree)
    (hhalf :
      (1 / 2 : ENNReal) * sticky.croppedCoarseShading.mass ≤
        propertyThree.mass) :
    ((2 * stickyCoarseMultiplicityCap sticky *
        stickyCoarseMultiplicityCap sticky *
        stickyFiberMultiplicityCap sticky : ENNReal)⁻¹) *
        sticky.refined.mass ≤
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propertyThree).mass := by
  have hgeneral := propertyThreeFinePullback_mass_lower_of_sticky_comparison
    sticky propertyThree hdelta hsub hcubical (1 / 2 : ENNReal) 1
    (by simpa using hhalf)
  have hproductZero :
      stickyCoarseMultiplicityCap sticky *
          stickyCoarseMultiplicityCap sticky *
          stickyFiberMultiplicityCap sticky ≠ 0 := by
    have hrho : 0 < rho.1 := sticky.coarse_extremal.delta_pos
    have hratio : 0 < delta / rho.1 := div_pos hdelta hrho
    have hcoarseNonempty : sticky.coarse.Nonempty := by
      let sourceIndex : Fin sticky.selected.family.card :=
        ⟨0, sticky.selected_nonempty⟩
      rcases sticky.cover.covers sourceIndex with ⟨parent, _⟩
      exact Nat.zero_lt_of_lt parent.isLt
    have hcoarseCapZero : stickyCoarseMultiplicityCap sticky ≠ 0 :=
      mul_ne_zero
        (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos hrho (2 - sigma - outputLoss))).ne'
        (by simpa [Kakeya.Streamlined.TubeFamily.enncard] using
          hcoarseNonempty.ne')
    have hfiberCapZero : stickyFiberMultiplicityCap sticky ≠ 0 :=
      mul_ne_zero
        (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos hratio (2 - sigma - outputLoss))).ne'
        (by simpa [Kakeya.Streamlined.TubeFamily.enncard] using
          sticky.selected_nonempty.ne')
    exact mul_ne_zero (mul_ne_zero hcoarseCapZero hcoarseCapZero)
      hfiberCapZero
  have hproductTop :
      stickyCoarseMultiplicityCap sticky *
          stickyCoarseMultiplicityCap sticky *
          stickyFiberMultiplicityCap sticky ≠ ⊤ := by
    have hcoarseCapTop : stickyCoarseMultiplicityCap sticky ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · simp [Kakeya.realRpowENN]
      · simp [Kakeya.Streamlined.TubeFamily.enncard]
    have hfiberCapTop : stickyFiberMultiplicityCap sticky ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · simp [Kakeya.realRpowENN]
      · simp [Kakeya.Streamlined.TubeFamily.enncard]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hcoarseCapTop hcoarseCapTop) hfiberCapTop
  have hinverse :
      (2 * stickyCoarseMultiplicityCap sticky *
          stickyCoarseMultiplicityCap sticky *
          stickyFiberMultiplicityCap sticky : ENNReal)⁻¹ =
        (1 / 2 : ENNReal) *
          (stickyCoarseMultiplicityCap sticky *
            stickyCoarseMultiplicityCap sticky *
            stickyFiberMultiplicityCap sticky : ENNReal)⁻¹ := by
    rw [show (2 * stickyCoarseMultiplicityCap sticky *
        stickyCoarseMultiplicityCap sticky *
        stickyFiberMultiplicityCap sticky : ENNReal) =
      2 * (stickyCoarseMultiplicityCap sticky *
        stickyCoarseMultiplicityCap sticky *
        stickyFiberMultiplicityCap sticky) by ring]
    rw [ENNReal.mul_inv (Or.inr hproductTop) (Or.inr hproductZero)]
    norm_num [one_div]
  rw [hinverse]
  simpa using hgeneral

end Kakeya.Assouad.PureWZ2

end
