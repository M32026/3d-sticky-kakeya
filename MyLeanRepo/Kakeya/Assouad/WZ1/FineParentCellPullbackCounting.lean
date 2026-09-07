import MyLeanRepo.Kakeya.Assouad.WZ1.FineParentCellPullbackInfrastructure
import MyLeanRepo.Kakeya.Assouad.WZ1.CubeCountGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCovering

/-!
# Quantitative parent-cell counting for WZ1 Lemma 17

This module compares the actual parent-cell pairs touched by a coarse
subshading with all active parent-cell pairs in a balanced cover.  The
comparison uses the coarse extremal density, the balanced coarse-cell volume
floor, and the literal diameter bound on each cell.
-/

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Kakeya.Assouad

/-- Coarse shaded mass carried by one actual parent-cell pair. -/
def coarseParentCellMass
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho))
    (parent : Fin (U.coarse rho).card)
    (cell : Fin balanced.cellCount) : ENNReal :=
  MeasureTheory.volume
    (coarse.carrier parent ∩ {point | balanced.cell point = cell})

private lemma coarse_carrier_volume_cell_decomposition
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho))
    (parent : Fin (U.coarse rho).card) :
    MeasureTheory.volume (coarse.carrier parent) =
      ∑ cell : Fin balanced.cellCount,
        coarseParentCellMass balanced coarse parent cell := by
  let pieces : Fin balanced.cellCount → Set Point3 :=
    fun cell =>
      coarse.carrier parent ∩
        {point | balanced.cell point = cell}
  have hdisjoint :
      Set.PairwiseDisjoint
        (↑(Finset.univ : Finset (Fin balanced.cellCount)))
        pieces := by
    intro first _ second _ hne
    change Disjoint (pieces first) (pieces second)
    rw [Set.disjoint_left]
    intro point hfirst hsecond
    exact hne (hfirst.2.symm.trans hsecond.2)
  have hmeasurable :
      ∀ cell ∈ (Finset.univ : Finset (Fin balanced.cellCount)),
        MeasurableSet (pieces cell) := by
    intro cell _
    exact
      (coarse.measurable_carrier parent).inter
        (balanced.cell_measurable (MeasurableSet.singleton cell))
  have hcover :
      coarse.carrier parent =
        ⋃ cell : Fin balanced.cellCount, pieces cell := by
    ext point
    simp only [pieces, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    exact
      ⟨fun hpoint => ⟨balanced.cell point, hpoint, rfl⟩,
        fun hpoint => hpoint.choose_spec.1⟩
  have hmeasure :
      MeasureTheory.volume
          (⋃ cell : Fin balanced.cellCount, pieces cell) =
        ∑ cell : Fin balanced.cellCount,
          MeasureTheory.volume (pieces cell) := by
    have hfinite :
        MeasureTheory.volume
            (⋃ cell ∈
              (Finset.univ : Finset (Fin balanced.cellCount)),
                pieces cell) =
          ∑ cell ∈
              (Finset.univ : Finset (Fin balanced.cellCount)),
            MeasureTheory.volume (pieces cell) :=
      MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable
    simpa [Set.biUnion_univ, Finset.mem_univ] using hfinite
  calc
    MeasureTheory.volume (coarse.carrier parent) =
        MeasureTheory.volume
          (⋃ cell : Fin balanced.cellCount, pieces cell) := by
          rw [hcover]
    _ = ∑ cell : Fin balanced.cellCount,
          MeasureTheory.volume (pieces cell) := hmeasure
    _ = ∑ cell : Fin balanced.cellCount,
          coarseParentCellMass balanced coarse parent cell := by
          rfl

/-- A coarse shading's mass is the sum of its occupied parent-cell masses. -/
lemma coarse_mass_eq_sum_touchedParentCells
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho)) :
    coarse.mass =
      ∑ pair ∈ touchedParentCells balanced coarse,
        coarseParentCellMass balanced coarse pair.1 pair.2 := by
  have hall :
      coarse.mass =
        ∑ pair :
            Fin (U.coarse rho).card × Fin balanced.cellCount,
          coarseParentCellMass balanced coarse pair.1 pair.2 := by
    have hproduct :
        (∑ pair :
            Fin (U.coarse rho).card × Fin balanced.cellCount,
          coarseParentCellMass balanced coarse pair.1 pair.2) =
          ∑ parent : Fin (U.coarse rho).card,
            ∑ cell : Fin balanced.cellCount,
              coarseParentCellMass balanced coarse parent cell := by
      calc
        (∑ pair :
            Fin (U.coarse rho).card × Fin balanced.cellCount,
          coarseParentCellMass balanced coarse pair.1 pair.2) =
            ∑ pair ∈
                (Finset.univ :
                  Finset (Fin (U.coarse rho).card)) ×ˢ
                    (Finset.univ :
                      Finset (Fin balanced.cellCount)),
              coarseParentCellMass balanced coarse pair.1 pair.2 := by
                rw [Finset.univ_product_univ]
        _ = ∑ parent : Fin (U.coarse rho).card,
              ∑ cell : Fin balanced.cellCount,
                coarseParentCellMass balanced coarse parent cell := by
              rw [Finset.sum_product]
    rw [hproduct]
    change
      (∑ parent : Fin (U.coarse rho).card,
        MeasureTheory.volume (coarse.carrier parent)) =
        ∑ parent : Fin (U.coarse rho).card,
          ∑ cell : Fin balanced.cellCount,
            coarseParentCellMass balanced coarse parent cell
    apply Finset.sum_congr rfl
    intro parent _
    exact coarse_carrier_volume_cell_decomposition
      balanced coarse parent
  have hzero :
      ∀ pair :
          Fin (U.coarse rho).card × Fin balanced.cellCount,
        pair ∉ touchedParentCells balanced coarse →
          coarseParentCellMass balanced coarse pair.1 pair.2 = 0 := by
    intro pair hpair
    have hempty :
        coarse.carrier pair.1 ∩
            {point | balanced.cell point = pair.2} =
          ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hnonempty
      apply hpair
      rw [mem_touchedParentCells]
      exact hnonempty
    simp [coarseParentCellMass, hempty]
  rw [hall]
  symm
  exact
    Finset.sum_subset
      (Finset.subset_univ (touchedParentCells balanced coarse))
      (fun pair _ hpair => hzero pair hpair)

/-- Every active pair contains the full balanced coarse-cell slice. -/
lemma active_coarseParentCellMass_lower
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (pair :
      Fin (U.coarse rho).card × Fin balanced.cellCount)
    (hpair : pair ∈ activeParentCells balanced) :
    Kakeya.realRpowENN rho.1 3 / 1000000 ≤
      coarseParentCellMass
        balanced balanced.coarseShading pair.1 pair.2 := by
  have hactive :
      {point |
        point ∈ balanced.coarseShading.carrier pair.1 ∧
          balanced.cell point = pair.2}.Nonempty :=
    (mem_activeParentCells balanced pair).mp hpair
  have hcell :
      {point |
        point ∈ balanced.coarseShading.union ∧
          balanced.cell point = pair.2}.Nonempty := by
    rcases hactive with ⟨point, hpoint, hpointCell⟩
    exact ⟨point, ⟨pair.1, hpoint⟩, hpointCell⟩
  have heq :
      balanced.coarseShading.carrier pair.1 ∩
          {point | balanced.cell point = pair.2} =
        {point |
          point ∈ balanced.coarseShading.union ∧
            balanced.cell point = pair.2} := by
    ext point
    constructor
    · intro hpoint
      exact ⟨⟨pair.1, hpoint.1⟩, hpoint.2⟩
    · intro hpoint
      exact
        ⟨balanced.coarse_cell_saturation
            pair.1 pair.2 hactive hpoint,
          hpoint.2⟩
  rw [coarseParentCellMass, heq]
  exact balanced.coarse_cell_volume_lower pair.2 hcell

/-- Every touched parent-cell piece lies in one diameter-`2 * rho` cell. -/
lemma touched_coarseParentCellMass_upper
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho))
    (hcoarse : IsSubshading coarse balanced.coarseShading)
    (hrho : 0 < rho.1)
    (pair :
      Fin (U.coarse rho).card × Fin balanced.cellCount)
    (hpair : pair ∈ touchedParentCells balanced coarse) :
    coarseParentCellMass balanced coarse pair.1 pair.2 ≤
      ENNReal.ofReal (8 * rho.1 ^ 3) := by
  let piece : Set Point3 :=
    coarse.carrier pair.1 ∩
      {point | balanced.cell point = pair.2}
  have hpieceMeasurable : MeasurableSet piece :=
    (coarse.measurable_carrier pair.1).inter
      (balanced.cell_measurable
        (MeasurableSet.singleton pair.2))
  have hnonempty : piece.Nonempty := by
    rcases (mem_touchedParentCells balanced coarse pair).mp hpair with
      ⟨point, hpoint, hpointCell⟩
    exact ⟨point, hpoint, hpointCell⟩
  rcases hnonempty with ⟨anchor, hanchor⟩
  have hcoordinate :
      ∀ coordinate : Fin 3,
        ∀ first ∈ piece, ∀ second ∈ piece,
          |first coordinate - second coordinate| ≤ 2 * rho.1 := by
    intro coordinate first hfirst second hsecond
    have hfirstCoarse :
        first ∈ balanced.coarseShading.carrier pair.1 :=
      hcoarse pair.1 hfirst.1
    have hsecondCoarse :
        second ∈ balanced.coarseShading.carrier pair.1 :=
      hcoarse pair.1 hsecond.1
    have hdistance :
        dist first second ≤ 2 * rho.1 := by
      exact
        balanced.cell_diameter first
          ⟨pair.1, hfirstCoarse⟩ second
          ⟨pair.1, hsecondCoarse⟩
          (hfirst.2.trans hsecond.2.symm)
    have hcoord : |(first - second) coordinate| ≤ ‖first - second‖ :=
      coord_bound (first - second) coordinate
    simpa [dist_eq_norm] using hcoord.trans hdistance
  have hdiameter :=
    volume_by_three_diameters_public
      hpieceMeasurable
      (LinearIsometryEquiv.refl ℝ Point3)
      (2 * rho.1) (2 * rho.1) (2 * rho.1)
      (by positivity) (by positivity) (by positivity)
      (fun first second hfirst hsecond =>
        hcoordinate 0 first hfirst second hsecond)
      (fun first second hfirst hsecond =>
        hcoordinate 1 first hfirst second hsecond)
      (fun first second hfirst hsecond =>
        hcoordinate 2 first hfirst second hsecond)
  have hconstant :
      (2 * rho.1) * (2 * rho.1) * (2 * rho.1) =
        8 * rho.1 ^ 3 := by ring
  simpa [coarseParentCellMass, piece, hconstant] using hdiameter

/-- The active pair count is controlled by balanced coarse mass. -/
lemma activeParentCells_card_lower_from_coarse_mass
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho) :
    ((activeParentCells balanced).card : ENNReal) *
          (Kakeya.realRpowENN rho.1 3 / 1000000) ≤
      balanced.coarseShading.mass := by
  rw [coarse_mass_eq_sum_touchedParentCells
    balanced balanced.coarseShading]
  have heq :
      touchedParentCells balanced balanced.coarseShading =
        activeParentCells balanced := by
    ext pair
    simp
  rw [heq]
  calc
    ((activeParentCells balanced).card : ENNReal) *
          (Kakeya.realRpowENN rho.1 3 / 1000000) =
        ∑ _pair ∈ activeParentCells balanced,
          Kakeya.realRpowENN rho.1 3 / 1000000 := by
            simp [Finset.sum_const]
    _ ≤
        ∑ pair ∈ activeParentCells balanced,
          coarseParentCellMass
            balanced balanced.coarseShading pair.1 pair.2 := by
          exact Finset.sum_le_sum
            (active_coarseParentCellMass_lower balanced)

/-- The mass of a coarse subshading is controlled by its touched pair count. -/
lemma coarse_mass_le_touchedParentCells_card
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho))
    (hcoarse : IsSubshading coarse balanced.coarseShading)
    (hrho : 0 < rho.1) :
    coarse.mass ≤
      ((touchedParentCells balanced coarse).card : ENNReal) *
        ENNReal.ofReal (8 * rho.1 ^ 3) := by
  rw [coarse_mass_eq_sum_touchedParentCells balanced coarse]
  calc
    (∑ pair ∈ touchedParentCells balanced coarse,
        coarseParentCellMass balanced coarse pair.1 pair.2) ≤
        ∑ _pair ∈ touchedParentCells balanced coarse,
          ENNReal.ofReal (8 * rho.1 ^ 3) := by
            exact Finset.sum_le_sum
              (touched_coarseParentCellMass_upper
                balanced coarse hcoarse hrho)
    _ =
        ((touchedParentCells balanced coarse).card : ENNReal) *
          ENNReal.ofReal (8 * rho.1 ^ 3) := by
            simp [Finset.sum_const]

/--
The coarse `epsilon₂`-density forces enough actual parent-cell pairs to be
touched.  Converting that cardinality proportion through the balanced fine
pair masses retains the factor `rho^epsilon₂ / 32,000,000` of fine mass.
-/
lemma fineParentCellPullback_mass_retention
    {delta sigma epsilon₁ epsilon₂ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon₁) U Y rho)
    (coarse : Kakeya.Streamlined.TubeShading (U.coarse rho))
    (hcoarse : IsSubshading coarse balanced.coarseShading)
    (hcoarseExtremal :
      WZ1ExtremalPair sigma epsilon₂
        (U.coarse rho) balanced.coarseUniform coarse)
    (hrho : 0 < rho.1) :
    (Kakeya.realRpowENN rho.1 epsilon₂ / 32000000) *
        balanced.refined.mass ≤
      (fineParentCellPullbackShading balanced coarse).mass := by
  let rhoPower : ENNReal :=
    Kakeya.realRpowENN rho.1 epsilon₂
  let cellVolume : ENNReal :=
    Kakeya.realRpowENN rho.1 3
  let activeCount : ENNReal :=
    ((activeParentCells balanced).card : ENNReal)
  let touchedCount : ENNReal :=
    ((touchedParentCells balanced coarse).card : ENNReal)
  have hbalancedMassFamily :
      balanced.coarseShading.mass ≤
        (U.coarse rho).toBodyFamily.mass := by
    simp only [Kakeya.Streamlined.Shading.mass,
      Kakeya.Streamlined.BodyFamily.mass]
    apply Finset.sum_le_sum
    intro parent _
    exact
      MeasureTheory.measure_mono
        (balanced.coarseShading.subset_body parent)
  have hcoarseDensity :
      rhoPower * (U.coarse rho).toBodyFamily.mass ≤
        coarse.mass := by
    exact hcoarseExtremal.2.2.2.2.2.2.2.1
  have hrelativeCoarseMass :
      rhoPower * balanced.coarseShading.mass ≤ coarse.mass := by
    exact (mul_le_mul_left' hbalancedMassFamily rhoPower).trans
      hcoarseDensity
  have hactiveLower :
      activeCount * (cellVolume / 1000000) ≤
        balanced.coarseShading.mass := by
    simpa [activeCount, cellVolume] using
      activeParentCells_card_lower_from_coarse_mass balanced
  have htouchedUpper :
      coarse.mass ≤ touchedCount * (8 * cellVolume) := by
    have hraw :=
      coarse_mass_le_touchedParentCells_card
        balanced coarse hcoarse hrho
    have hcellVolume :
        ENNReal.ofReal (8 * rho.1 ^ 3) =
          8 * cellVolume := by
      simp only [cellVolume, Kakeya.realRpowENN]
      have hrho3 : 0 ≤ rho.1 ^ 3 := by positivity
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    simpa [touchedCount, hcellVolume] using hraw
  have hcountScaled :
      rhoPower *
          (activeCount * (cellVolume / 1000000)) ≤
        touchedCount * (8 * cellVolume) :=
    (mul_le_mul_left' hactiveLower rhoPower).trans
      (hrelativeCoarseMass.trans htouchedUpper)
  have hrhoPowerTop : rhoPower ≠ ⊤ := by
    simp [rhoPower, Kakeya.realRpowENN]
  have hcellVolumeTop : cellVolume ≠ ⊤ := by
    simp [cellVolume, Kakeya.realRpowENN]
  have hcellVolumePos : 0 < cellVolume := by
    simp [cellVolume, Kakeya.realRpowENN,
      ENNReal.ofReal_pos, hrho]
  have hactiveTop : activeCount ≠ ⊤ := by
    simp [activeCount]
  have htouchedTop : touchedCount ≠ ⊤ := by
    simp [touchedCount]
  have hcardEight :
      (rhoPower / 8000000) * activeCount ≤
        touchedCount := by
    have hrightTop :
        touchedCount * (8 * cellVolume) ≠ ⊤ :=
      ENNReal.mul_ne_top htouchedTop
        (ENNReal.mul_ne_top (by norm_num) hcellVolumeTop)
    have hreal := ENNReal.toReal_mono hrightTop hcountScaled
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_ofNat] at hreal
    have hcellVolumeReal : 0 < cellVolume.toReal :=
      ENNReal.toReal_pos hcellVolumePos.ne' hcellVolumeTop
    have hlhsTop :
        (rhoPower / 8000000) * activeCount ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.div_ne_top hrhoPowerTop (by norm_num))
        hactiveTop
    apply
      (ENNReal.toReal_le_toReal hlhsTop htouchedTop).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_ofNat]
    nlinarith
  have hcardThirtyTwo :
      (rhoPower / 32000000) * (4 * activeCount) ≤
        touchedCount := by
    have hreal := ENNReal.toReal_mono htouchedTop hcardEight
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_ofNat] at hreal
    have hlhsTop :
        (rhoPower / 32000000) * (4 * activeCount) ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.div_ne_top hrhoPowerTop (by norm_num))
        (ENNReal.mul_ne_top (by norm_num) hactiveTop)
    apply
      (ENNReal.toReal_le_toReal hlhsTop htouchedTop).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_ofNat]
    nlinarith
  apply fineParentCellPullback_mass_retention_of_cardinality
    balanced coarse hcoarse
      (rhoPower / 32000000)
  simpa [activeCount, touchedCount] using hcardThirtyTwo

end Kakeya.Assouad
