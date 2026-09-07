import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderGlobalBinFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperCubeSliceArea

/-!
# Aggregate retained volume over ordinary global bins

The exact source slice is partitioned into all of its global-bin fibres before
the parent and residue selections.  Summing the fixed-bin estimates removes
the maximal-bin `globalBins.card` loss.  This module deliberately stops at the
full retained source carriers; comparison with their outer-popular graph
shadows is the next, separate height-retention step.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Geometric cost of the ordinary all-global-bin retained-source
construction.  In contrast with `pureWZ2SourceHorizontalVolumeCost`, it has no
global-bin cardinality factor. -/
def pureWZ2OrdinaryAllBinRetainedVolumeCost
    (rho delta : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
    (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) *
    (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) *
    23040

/-- Geometric cost for the corresponding genuine first-sticky coarse
carriers.  It is the same all-bin cost, with no global-bin cardinality loss. -/
def pureWZ2OrdinaryAllBinCoarseVolumeCost
    (rho delta : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
    (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) *
    (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) *
    23040

/-- Absolute constant in the product of the ordinary global-bin count and
the all-bin genuine-coarse geometric cost. -/
def pureWZ2OrdinaryAllBinCoarseVolumeConstant : ENNReal :=
  (132 * 10) * 3 * 4 * 12 * 23040

private theorem ordinaryAllBin_parentFiberBound_ennreal_le
    {delta rho : ℝ}
    (hdelta : 0 < delta) (hdeltaRho : delta ≤ rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1) :
    (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) ≤
      12 * Kakeya.realRpowENN rho (1 / 2 : ℝ) *
        Kakeya.realRpowENN delta (-1) := by
  let root := Real.sqrt rho
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  have hrootOne : root ≤ 1 := Real.sqrt_le_one.mpr hrhoOne
  have hrhoRoot : rho ≤ root := by
    nlinarith [Real.sqrt_nonneg rho, Real.sq_sqrt hrho.le]
  have hdeltaRoot : delta ≤ root := hdeltaRho.trans hrhoRoot
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  let x := (root + delta) / (delta / Real.sqrt 3)
  have hxNonneg : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hx : x ≤ 4 * root / delta := by
    have hsqrtThreePos : 0 < Real.sqrt 3 := by positivity
    have hxEq : x = (root + delta) * Real.sqrt 3 / delta := by
      dsimp only [x]
      field_simp [hdelta.ne', hsqrtThreePos.ne'] <;> ring
    have hlhs : (root + delta) * Real.sqrt 3 ≤
        2 * (root + delta) := by
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left hsqrtThree
          (show 0 ≤ root + delta by positivity))
    have hbound : (root + delta) * Real.sqrt 3 ≤ 4 * root := by
      exact hlhs.trans (by linarith)
    rw [hxEq, div_le_div_iff_of_pos_right hdelta]
    exact hbound
  have hceil : (Nat.ceil x : ℝ) ≤ x + 1 :=
    (Nat.ceil_lt_add_one hxNonneg).le
  have htwo : 2 ≤ 2 * root / delta := by
    rw [le_div_iff₀ hdelta]
    nlinarith
  have hy : (pureWZ2SourceFixedLineParentYBound delta rho : ℝ) ≤
      6 * root / delta := by
    dsimp only [pureWZ2SourceFixedLineParentYBound]
    rw [show Real.sqrt rho = root by rfl]
    norm_num only [Nat.cast_add, Nat.cast_one]
    change (Nat.ceil x : ℝ) + 1 ≤ 6 * root / delta
    calc
      (Nat.ceil x : ℝ) + 1 ≤ x + 2 := by linarith
      _ ≤ 4 * root / delta + 2 := by linarith
      _ ≤ 4 * root / delta + 2 * root / delta := by linarith
      _ = 6 * root / delta := by ring
  have hreal : (pureWZ2SourceFixedLineParentFiberBound delta rho : ℝ) ≤
      12 * Real.sqrt rho / delta := by
    calc
      (pureWZ2SourceFixedLineParentFiberBound delta rho : ℝ) =
          2 * (pureWZ2SourceFixedLineParentYBound delta rho : ℝ) := by
        simp [pureWZ2SourceFixedLineParentFiberBound]
      _ ≤ 2 * (6 * root / delta) := by gcongr
      _ = 12 * Real.sqrt rho / delta := by simp [root]; ring
  have hrpowRho : Real.rpow rho (1 / 2 : ℝ) = Real.sqrt rho :=
    (Real.sqrt_eq_rpow rho).symm
  have hrpowDelta : Real.rpow delta (-1 : ℝ) = 1 / delta := by
    simpa [one_div] using Real.rpow_neg_one delta
  simp only [Kakeya.realRpowENN, hrpowRho, hrpowDelta]
  have hcast :
      (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) =
        ENNReal.ofReal
          (pureWZ2SourceFixedLineParentFiberBound delta rho : ℝ) := by
    norm_cast
  rw [hcast, ← ENNReal.ofReal_ofNat 12,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12),
    ← ENNReal.ofReal_mul (show 0 ≤ 12 * Real.sqrt rho by positivity)]
  apply ENNReal.ofReal_mono
  simpa [div_eq_mul_inv, mul_assoc] using hreal

/-- Rewrite the source fixed-bin count as one power of the original scale. -/
theorem PureWZ2SourceHorizontalFixedBinData.global_bin_count_power_bound
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedBinData window) :
    (line.globalBins.card : ENNReal) ≤
      (132 * 10 : ENNReal) *
        Kakeya.realRpowENN delta (sigma - inputLoss - 1) := by
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hinverse :
      Kakeya.realRpowENN (1 / delta) (1 - sigma) =
        Kakeya.realRpowENN delta (-(1 - sigma)) := by
    simp only [Kakeya.realRpowENN]
    congr 1
    calc
      Real.rpow (1 / delta) (1 - sigma) =
          Real.rpow 1 (1 - sigma) / Real.rpow delta (1 - sigma) :=
        Real.div_rpow (by norm_num) hdelta.le _
      _ = (Real.rpow delta (1 - sigma))⁻¹ := by simp
      _ = Real.rpow delta (-(1 - sigma)) :=
        (Real.rpow_neg hdelta.le _).symm
  calc
    (line.globalBins.card : ENNReal) ≤
        132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
          Kakeya.realRpowENN (1 / delta) (1 - sigma) :=
      line.global_bin_count
    _ = (132 * 10 : ENNReal) *
        (Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta (-(1 - sigma))) := by
      rw [hinverse]
      ring
    _ = (132 * 10 : ENNReal) *
        Kakeya.realRpowENN delta
          ((-inputLoss) + (-(1 - sigma))) := by
      rw [realRpowENN_add hdelta]
    _ = (132 * 10 : ENNReal) *
        Kakeya.realRpowENN delta (sigma - inputLoss - 1) := by
      congr 2
      ring

/-- The all-bin coarse geometric cost has exactly one remaining power of
`delta` and one of `rho` after the slice thickness, disk area, and parent
fibre count are combined. -/
theorem pureWZ2OrdinaryAllBinCoarseVolumeCost_upper
    {delta rho : ℝ}
    (hdelta : 0 < delta) (hdeltaRho : delta ≤ rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1) :
    pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤
      (3 * 4 * 12 * 23040 : ENNReal) *
        Kakeya.realRpowENN delta 1 *
        Kakeya.realRpowENN rho 1 := by
  have hrhoRoot : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sqrt_nonneg rho, Real.sq_sqrt hrho.le, hrhoOne]
  have hthicknessReal : Real.sqrt rho + 2 * rho ≤
      3 * Real.sqrt rho := by linarith
  have hthickness : ENNReal.ofReal (Real.sqrt rho + 2 * rho) ≤
      3 * Kakeya.realRpowENN rho (1 / 2 : ℝ) := by
    rw [show Kakeya.realRpowENN rho (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt rho) by
        simp [Kakeya.realRpowENN, Real.sqrt_eq_rpow]]
    calc
      ENNReal.ofReal (Real.sqrt rho + 2 * rho) ≤
          ENNReal.ofReal (3 * Real.sqrt rho) :=
        ENNReal.ofReal_mono hthicknessReal
      _ = 3 * ENNReal.ofReal (Real.sqrt rho) := by
        rw [← ENNReal.ofReal_ofNat 3,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hdisk : ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi ≤
      4 * Kakeya.realRpowENN delta 2 := by
    have hpow : ENNReal.ofReal delta ^ 2 =
        Kakeya.realRpowENN delta 2 := by
      simp [Kakeya.realRpowENN, Real.rpow_two,
        ← ENNReal.ofReal_mul hdelta.le, pow_two]
    have hpi : ENNReal.ofReal Real.pi ≤ 4 := by
      simpa using ENNReal.ofReal_le_ofReal Real.pi_le_four
    calc
      ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi =
          Kakeya.realRpowENN delta 2 * ENNReal.ofReal Real.pi := by rw [hpow]
      _ ≤ Kakeya.realRpowENN delta 2 * 4 := by gcongr
      _ = 4 * Kakeya.realRpowENN delta 2 := by ring
  have hparent := ordinaryAllBin_parentFiberBound_ennreal_le
    hdelta hdeltaRho hrho hrhoOne
  have hdeltaPowers :
      Kakeya.realRpowENN delta 2 * Kakeya.realRpowENN delta (-1) =
        Kakeya.realRpowENN delta 1 := by
    rw [← realRpowENN_add hdelta]
    congr 1
    ring
  have hrhoPowers :
      Kakeya.realRpowENN rho (1 / 2 : ℝ) *
          Kakeya.realRpowENN rho (1 / 2 : ℝ) =
        Kakeya.realRpowENN rho 1 := by
    rw [← realRpowENN_add hrho]
    congr 1
    ring
  rw [pureWZ2OrdinaryAllBinCoarseVolumeCost]
  calc
    ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
          (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) *
          (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) *
          23040 ≤
        (3 * Kakeya.realRpowENN rho (1 / 2 : ℝ)) *
          (4 * Kakeya.realRpowENN delta 2) *
          (12 * Kakeya.realRpowENN rho (1 / 2 : ℝ) *
            Kakeya.realRpowENN delta (-1)) * 23040 := by
      gcongr
    _ = (3 * 4 * 12 * 23040 : ENNReal) *
        Kakeya.realRpowENN delta 1 *
        Kakeya.realRpowENN rho 1 := by
      rw [← hdeltaPowers, ← hrhoPowers]
      ring

/-- Combined fixed-bin-count and all-bin coarse-volume bound. -/
theorem PureWZ2SourceHorizontalFixedBinData.global_bin_count_mul_coarseCost_upper
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedBinData window)
    (hrhoOne : rho ≤ 1) :
    (line.globalBins.card : ENNReal) *
        pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤
      pureWZ2OrdinaryAllBinCoarseVolumeConstant *
        Kakeya.realRpowENN delta (sigma - inputLoss) *
        Kakeya.realRpowENN rho 1 := by
  have hdelta := source.extremal.delta_pos
  have hrho := line.rho_pos
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hcount := line.global_bin_count_power_bound
  have hcost := pureWZ2OrdinaryAllBinCoarseVolumeCost_upper
    hdelta hdeltaRho hrho hrhoOne
  have hdeltaPowers :
      Kakeya.realRpowENN delta (sigma - inputLoss - 1) *
          Kakeya.realRpowENN delta 1 =
        Kakeya.realRpowENN delta (sigma - inputLoss) := by
    rw [← realRpowENN_add hdelta]
    congr 1
    ring
  calc
    (line.globalBins.card : ENNReal) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤
        ((132 * 10 : ENNReal) *
            Kakeya.realRpowENN delta (sigma - inputLoss - 1)) *
          ((3 * 4 * 12 * 23040 : ENNReal) *
            Kakeya.realRpowENN delta 1 *
            Kakeya.realRpowENN rho 1) := by
      gcongr
    _ = pureWZ2OrdinaryAllBinCoarseVolumeConstant *
        Kakeya.realRpowENN delta (sigma - inputLoss) *
        Kakeya.realRpowENN rho 1 := by
      rw [← hdeltaPowers]
      simp only [pureWZ2OrdinaryAllBinCoarseVolumeConstant]
      ring

/-- The common source-window supply is controlled by the sum of the full
retained source carriers over every global-bin fibre.  The two balanced cell
masses are kept explicit, exactly as in the former one-bin estimate. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData.aggregate_retained_volume_supply_le
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    (family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers) :
    carriers.outerPopular.popularWindow.volumeSupply *
          twoScale.coarse.balanced.cellMass *
        twoScale.fine.balanced.cellMass ≤
      (pureWZ2OrdinaryAllBinRetainedVolumeCost rho delta *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          volume (family.sourceRetained bin).shading.union := by
  let sliceThickness : ENNReal :=
    ENNReal.ofReal (Real.sqrt rho + 2 * rho)
  let sliceDisk : ENNReal :=
    ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi
  let parentBound : ENNReal :=
    (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal)
  let thinning : ENNReal := 23040
  let window := carriers.outerPopular.windowed
  have hpopularWindowSupply :
      carriers.outerPopular.popularWindow.volumeSupply ≤
        window.volumeSupply := by
    dsimp only [window]
    rw [carriers.outerPopular.popularWindow_supply,
      carriers.outerPopular.windowed_supply]
    exact carriers.outerPopular.volume_lower
  have hwindowSupply : window.volumeSupply ≤ volume window.shading.union :=
    window.volume_lower
  have hball : window.shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared : point ∈ prepared.shadow.union :=
      window.subshading.union_subset hpoint
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hsource := pullback.subshading.union_subset hpull
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hsliceAreaUpper :
      volume (wz1Lemma23PlanarSlice window.shading.union
          family.line.lineHeight) ≤
        (family.line.sliceCells.card : ENNReal) * sliceDisk := by
    have hraw := wz1_lemma23_exactSlice_area_le_two
      window.shading source.extremal.delta_pos hball family.line.lineHeight
    simpa [family.line.sliceCells_eq, sliceDisk] using hraw
  have hsliceThicknessPos : 0 < sliceThickness := by
    apply ENNReal.ofReal_pos.mpr
    have hrho : 0 < rho := family.line.rho_pos
    have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
    linarith
  have hsliceThicknessTop : sliceThickness ≠ ⊤ := ENNReal.ofReal_ne_top
  have hwindowToSlice :
      volume window.shading.union ≤
        volume (wz1Lemma23PlanarSlice window.shading.union
          family.line.lineHeight) * sliceThickness := by
    apply (ENNReal.div_le_iff
      hsliceThicknessPos.ne' hsliceThicknessTop).mp
    simpa [sliceThickness] using family.line.slice_area_lower
  have hbinMass : ∀ bin : {bin // bin ∈ family.line.globalBins},
      ((family.core bin).heavyCells.card : ENNReal) *
            twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass ≤
        parentBound * thinning *
          (volume (family.sourceRetained bin).shading.union *
            volume (wz1PaperGridCube rho (0, 0, 0))) := by
    intro bin
    have hheavy : ((family.core bin).heavyCells.card : ENNReal) ≤
        parentBound * ((family.parents bin).parents.card : ENNReal) := by
      dsimp only [parentBound]
      exact_mod_cast (family.parents bin).heavy_card
    have hparentNat : (family.parents bin).parents.card ≤
        23040 * (family.residue bin).selected.card := by
      calc
        (family.parents bin).parents.card ≤
            45 * (family.selection bin).selected.card :=
          (family.selection bin).parent_card
        _ ≤ 45 * (512 * (family.residue bin).selected.card) := by
          gcongr
          exact (family.residue bin).card_fraction
        _ = 23040 * (family.residue bin).selected.card := by ring
    have hparent : ((family.parents bin).parents.card : ENNReal) ≤
        thinning * ((family.residue bin).selected.card : ENNReal) := by
      dsimp only [thinning]
      exact_mod_cast hparentNat
    calc
      ((family.core bin).heavyCells.card : ENNReal) *
            twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass ≤
        (parentBound * ((family.parents bin).parents.card : ENNReal)) *
            twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass := by gcongr
      _ ≤ (parentBound *
            (thinning * ((family.residue bin).selected.card : ENNReal))) *
            twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass := by gcongr
      _ = parentBound * thinning *
          (((family.residue bin).selected.card : ENNReal) *
              twoScale.fine.balanced.cellMass *
            twoScale.coarse.balanced.cellMass) := by ring
      _ = parentBound * thinning *
          (volume (family.sourceRetained bin).shading.union *
            volume (wz1PaperGridCube rho (0, 0, 0))) := by
        rw [(family.sourceRetained bin).volume_mul_cube]
  have hsliceMass : (family.line.sliceCells.card : ENNReal) *
          twoScale.coarse.balanced.cellMass *
        twoScale.fine.balanced.cellMass ≤
      parentBound * thinning *
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          (volume (family.sourceRetained bin).shading.union *
            volume (wz1PaperGridCube rho (0, 0, 0))) := by
    rw [show (family.line.sliceCells.card : ENNReal) =
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          ((family.core bin).heavyCells.card : ENNReal) by
      exact_mod_cast family.slice_card]
    rw [Finset.sum_mul, Finset.sum_mul]
    calc
      (∑ bin : {bin // bin ∈ family.line.globalBins},
          ((family.core bin).heavyCells.card : ENNReal) *
              twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) ≤
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          parentBound * thinning *
            (volume (family.sourceRetained bin).shading.union *
              volume (wz1PaperGridCube rho (0, 0, 0))) := by
        exact Finset.sum_le_sum fun bin _ => hbinMass bin
      _ = parentBound * thinning *
          ∑ bin : {bin // bin ∈ family.line.globalBins},
            (volume (family.sourceRetained bin).shading.union *
              volume (wz1PaperGridCube rho (0, 0, 0))) := by
        rw [Finset.mul_sum]
  calc
    carriers.outerPopular.popularWindow.volumeSupply *
          twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass ≤
        window.volumeSupply * twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass := by gcongr
    _ ≤ volume window.shading.union * twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass := by gcongr
    _ ≤ (volume (wz1Lemma23PlanarSlice window.shading.union
          family.line.lineHeight) * sliceThickness) *
            twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass := by gcongr
    _ ≤ (((family.line.sliceCells.card : ENNReal) * sliceDisk) *
          sliceThickness) * twoScale.coarse.balanced.cellMass *
        twoScale.fine.balanced.cellMass := by gcongr
    _ = sliceThickness * sliceDisk *
        ((family.line.sliceCells.card : ENNReal) *
            twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass) := by ring
    _ ≤ sliceThickness * sliceDisk *
        (parentBound * thinning *
          ∑ bin : {bin // bin ∈ family.line.globalBins},
            (volume (family.sourceRetained bin).shading.union *
              volume (wz1PaperGridCube rho (0, 0, 0)))) := by gcongr
    _ = (pureWZ2OrdinaryAllBinRetainedVolumeCost rho delta *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          volume (family.sourceRetained bin).shading.union := by
      simp [pureWZ2OrdinaryAllBinRetainedVolumeCost, sliceThickness,
        sliceDisk, parentBound, thinning]
      rw [← Finset.sum_mul]
      ring

/-- The same lossless all-bin count controls the sum of the genuine
first-sticky coarse carriers.  This is the ordinary counterpart of the
terminal all-bin volume theorem, before any per-bin ready-graph threshold is
imposed. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData.aggregate_coarse_volume_supply_le
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    (family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers) :
    carriers.outerPopular.popularWindow.volumeSupply *
        twoScale.fine.balanced.cellMass ≤
      pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta *
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          volume (family.coarseCarrier bin).shading.union := by
  let sliceThickness : ENNReal :=
    ENNReal.ofReal (Real.sqrt rho + 2 * rho)
  let sliceDisk : ENNReal :=
    ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi
  let parentBound : ENNReal :=
    (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal)
  let thinning : ENNReal := 23040
  let window := carriers.outerPopular.windowed
  have hpopularWindowSupply :
      carriers.outerPopular.popularWindow.volumeSupply ≤
        window.volumeSupply := by
    dsimp only [window]
    rw [carriers.outerPopular.popularWindow_supply,
      carriers.outerPopular.windowed_supply]
    exact carriers.outerPopular.volume_lower
  have hwindowSupply : window.volumeSupply ≤ volume window.shading.union :=
    window.volume_lower
  have hball : window.shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared : point ∈ prepared.shadow.union :=
      window.subshading.union_subset hpoint
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hsource := pullback.subshading.union_subset hpull
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hsliceAreaUpper :
      volume (wz1Lemma23PlanarSlice window.shading.union
          family.line.lineHeight) ≤
        (family.line.sliceCells.card : ENNReal) * sliceDisk := by
    have hraw := wz1_lemma23_exactSlice_area_le_two
      window.shading source.extremal.delta_pos hball family.line.lineHeight
    simpa [family.line.sliceCells_eq, sliceDisk] using hraw
  have hsliceThicknessPos : 0 < sliceThickness := by
    apply ENNReal.ofReal_pos.mpr
    have hrho : 0 < rho := family.line.rho_pos
    have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
    linarith
  have hsliceThicknessTop : sliceThickness ≠ ⊤ := ENNReal.ofReal_ne_top
  have hwindowToSlice :
      volume window.shading.union ≤
        volume (wz1Lemma23PlanarSlice window.shading.union
          family.line.lineHeight) * sliceThickness := by
    apply (ENNReal.div_le_iff
      hsliceThicknessPos.ne' hsliceThicknessTop).mp
    simpa [sliceThickness] using family.line.slice_area_lower
  have hbinMass : ∀ bin : {bin // bin ∈ family.line.globalBins},
      ((family.core bin).heavyCells.card : ENNReal) *
          twoScale.fine.balanced.cellMass ≤
        parentBound * thinning *
          volume (family.coarseCarrier bin).shading.union := by
    intro bin
    have hheavy : ((family.core bin).heavyCells.card : ENNReal) ≤
        parentBound * ((family.parents bin).parents.card : ENNReal) := by
      dsimp only [parentBound]
      exact_mod_cast (family.parents bin).heavy_card
    have hparentNat : (family.parents bin).parents.card ≤
        23040 * (family.residue bin).selected.card := by
      calc
        (family.parents bin).parents.card ≤
            45 * (family.selection bin).selected.card :=
          (family.selection bin).parent_card
        _ ≤ 45 * (512 * (family.residue bin).selected.card) := by
          gcongr
          exact (family.residue bin).card_fraction
        _ = 23040 * (family.residue bin).selected.card := by ring
    have hparent : ((family.parents bin).parents.card : ENNReal) ≤
        thinning * ((family.residue bin).selected.card : ENNReal) := by
      dsimp only [thinning]
      exact_mod_cast hparentNat
    calc
      ((family.core bin).heavyCells.card : ENNReal) *
          twoScale.fine.balanced.cellMass ≤
        (parentBound * ((family.parents bin).parents.card : ENNReal)) *
          twoScale.fine.balanced.cellMass := by gcongr
      _ ≤ (parentBound *
            (thinning * ((family.residue bin).selected.card : ENNReal))) *
          twoScale.fine.balanced.cellMass := by gcongr
      _ = parentBound * thinning *
          (((family.residue bin).selected.card : ENNReal) *
            twoScale.fine.balanced.cellMass) := by ring
      _ = parentBound * thinning *
          volume (family.coarseCarrier bin).shading.union := by
        rw [(family.coarseCarrier bin).volume_eq]
  have hsliceMass : (family.line.sliceCells.card : ENNReal) *
        twoScale.fine.balanced.cellMass ≤
      parentBound * thinning *
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          volume (family.coarseCarrier bin).shading.union := by
    rw [show (family.line.sliceCells.card : ENNReal) =
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          ((family.core bin).heavyCells.card : ENNReal) by
      exact_mod_cast family.slice_card]
    rw [Finset.sum_mul]
    calc
      (∑ bin : {bin // bin ∈ family.line.globalBins},
          ((family.core bin).heavyCells.card : ENNReal) *
            twoScale.fine.balanced.cellMass) ≤
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          parentBound * thinning *
            volume (family.coarseCarrier bin).shading.union := by
        exact Finset.sum_le_sum fun bin _ => hbinMass bin
      _ = parentBound * thinning *
          ∑ bin : {bin // bin ∈ family.line.globalBins},
            volume (family.coarseCarrier bin).shading.union := by
        rw [Finset.mul_sum]
  calc
    carriers.outerPopular.popularWindow.volumeSupply *
          twoScale.fine.balanced.cellMass ≤
        window.volumeSupply * twoScale.fine.balanced.cellMass := by gcongr
    _ ≤
        volume window.shading.union *
          twoScale.fine.balanced.cellMass := by gcongr
    _ ≤ (volume (wz1Lemma23PlanarSlice window.shading.union
          family.line.lineHeight) * sliceThickness) *
        twoScale.fine.balanced.cellMass := by gcongr
    _ ≤ (((family.line.sliceCells.card : ENNReal) * sliceDisk) *
          sliceThickness) * twoScale.fine.balanced.cellMass := by gcongr
    _ = sliceThickness * sliceDisk *
        ((family.line.sliceCells.card : ENNReal) *
          twoScale.fine.balanced.cellMass) := by ring
    _ ≤ sliceThickness * sliceDisk *
        (parentBound * thinning *
          ∑ bin : {bin // bin ∈ family.line.globalBins},
            volume (family.coarseCarrier bin).shading.union) := by gcongr
    _ = pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta *
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          volume (family.coarseCarrier bin).shading.union := by
      simp [pureWZ2OrdinaryAllBinCoarseVolumeCost, sliceThickness,
        sliceDisk, parentBound, thinning]
      ring

/-- The source and genuine-coarse outputs of every fixed global bin obey the
same exact balanced-cover cross identity.  Summing before any bin is selected
preserves that identity for the complete all-bin family. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData.aggregate_coarse_source_mass_cross
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    (family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers) :
    (∑ bin : {bin // bin ∈ family.line.globalBins},
        volume (family.coarseCarrier bin).shading.union) *
          twoScale.coarse.balanced.incidenceMass =
      (∑ bin : {bin // bin ∈ family.line.globalBins},
        (family.sourceRetained bin).shading.mass) *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro bin _
  exact (family.sourceRetained bin).coarse_volume_mass_cross
    (family.coarseCarrier bin)

/-- All-bin Fubini bookkeeping in indexed source mass.  The second balanced
cell mass and first balanced incidence mass remain coupled on the left, while
the physical side-`rho` cube remains a common factor on the right. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData.aggregate_source_mass_supply_le
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    (family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers) :
    carriers.outerPopular.popularWindow.volumeSupply *
          twoScale.fine.balanced.cellMass *
          twoScale.coarse.balanced.incidenceMass ≤
      pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta *
        (∑ bin : {bin // bin ∈ family.line.globalBins},
          (family.sourceRetained bin).shading.mass) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  calc
    carriers.outerPopular.popularWindow.volumeSupply *
          twoScale.fine.balanced.cellMass *
          twoScale.coarse.balanced.incidenceMass ≤
        (pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta *
          ∑ bin : {bin // bin ∈ family.line.globalBins},
            volume (family.coarseCarrier bin).shading.union) *
          twoScale.coarse.balanced.incidenceMass := by
      exact mul_le_mul_right' family.aggregate_coarse_volume_supply_le _
    _ = pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta *
        ((∑ bin : {bin // bin ∈ family.line.globalBins},
          volume (family.coarseCarrier bin).shading.union) *
            twoScale.coarse.balanced.incidenceMass) := by ring
    _ = pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta *
        ((∑ bin : {bin // bin ∈ family.line.globalBins},
          (family.sourceRetained bin).shading.mass) *
            volume (wz1PaperGridCube rho (0, 0, 0))) := by
      rw [family.aggregate_coarse_source_mass_cross]
    _ = _ := by ring

end Kakeya.Assouad

end
