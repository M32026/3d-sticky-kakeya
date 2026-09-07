import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseCellWitness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DenseCubicalImageContainment
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage

/-!
# Original-slope Lemma-23 preparation on a genuine coarse carrier

In the paper proof of Lemma 24, Lemma 23 is applied to a subset of the
first-sticky coarse shading, while its slope function is the original source
function.  These two roles must not be identified.

The balanced cover gives every occupied coarse `rho`-cell a genuine point of
the original fine shading in the same cell.  For the global slice certificate,
the fixed-line localization puts the projection of every point into one
interval of length `28 * sqrt rho`.  A direct diameter-covering argument then
gives the paper AD estimate for the original interval slope; no equality with
the slope produced by the second grain refinement is needed.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- A bounded subset of the line has paper AD once its endpoint covering cost
is absorbed.  The proof combines the two elementary bounds
`N_r(E ∩ I) <= 2D/r + 2` and `N_r(E ∩ I) <= 2|I|/r + 2`, then interpolates
between them by concavity. -/
lemma pureWZ2_paperAD_of_bounded_diameter
    {delta sigma loss D : ℝ} {E : Set ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hD_pos : 0 < D)
    (hE_diam : ∀ x y, x ∈ E → y ∈ E → |x - y| ≤ D)
    (hC_ge : (4 : ENNReal) ≤ Kakeya.realRpowENN delta (-loss))
    (h_endpoint :
      ENNReal.ofReal
          ((2 * D / delta + 2) ^ sigma *
            4 ^ (1 - sigma)) ≤
        Kakeya.realRpowENN delta (-loss)) :
    PureWZ2PaperADSet1 E delta (1 - sigma)
      (Kakeya.realRpowENN delta (-loss)) := by
  let alpha : ℝ := 1 - sigma
  let A : ℝ := 2 * D / delta + 2
  let C : ℝ := Real.rpow delta (-loss)
  have halpha_pos : 0 < alpha := by
    dsimp only [alpha]
    linarith
  have halpha_lt_one : alpha < 1 := by
    dsimp only [alpha]
    linarith
  have hA_pos : 0 < A := by
    dsimp only [A]
    positivity
  have hC_pos : 0 < C := by
    dsimp only [C]
    exact Real.rpow_pos_of_pos hdelta_pos _
  have hC_eq :
      Kakeya.realRpowENN delta (-loss) = ENNReal.ofReal C := by
    rfl
  have hC_one :
      (1 : ENNReal) ≤ Kakeya.realRpowENN delta (-loss) :=
    le_trans (by norm_num) hC_ge
  have hC_ne_top : Kakeya.realRpowENN delta (-loss) ≠ ⊤ := by
    rw [hC_eq]
    exact ENNReal.ofReal_ne_top
  have h_endpoint_real : A ^ (1 - alpha) * 4 ^ alpha ≤ C := by
    rw [hC_eq] at h_endpoint
    have hreal :
        (2 * D / delta + 2) ^ sigma * 4 ^ (1 - sigma) ≤ C :=
      (ENNReal.ofReal_le_ofReal_iff hC_pos.le).mp h_endpoint
    simpa only [A, alpha, sub_sub_cancel] using hreal
  refine ⟨hdelta_pos, halpha_pos, halpha_lt_one.le, hC_one,
    hC_ne_top, ?_⟩
  intro r hr_nonneg hdelta_r left length hlength_r
  have hr_pos : 0 < r := hdelta_pos.trans_le hdelta_r
  have hlength_pos : 0 < length := hr_pos.trans_le hlength_r
  let T : Set ℝ := E ∩ Set.Icc left (left + length)
  let u : ℝ := length / r
  have hu_pos : 0 < u := by
    dsimp only [u]
    positivity
  have hu_one : 1 ≤ u := by
    dsimp only [u]
    calc
      (1 : ℝ) = r / r := by field_simp [hr_pos.ne']
      _ ≤ length / r := by gcongr
  have hT_diam_D :
      ∀ x y, x ∈ T → y ∈ T → dist x y ≤ D := by
    intro x y hx hy
    simpa only [Real.dist_eq] using hE_diam x y hx.1 hy.1
  have hT_diam_length :
      ∀ x y, x ∈ T → y ∈ T → dist x y ≤ length := by
    intro x y hx hy
    rw [Real.dist_eq, abs_le]
    exact ⟨by linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2],
      by linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]⟩
  have hcover_D :
      (Metric.externalCoveringNumber ⟨r, hr_nonneg⟩ T : ENNReal) ≤
        ENNReal.ofReal (2 * D / r + 2) :=
    covering_by_diameter hr_pos hD_pos.le hT_diam_D
  have hcover_length :
      (Metric.externalCoveringNumber ⟨r, hr_nonneg⟩ T : ENNReal) ≤
        ENNReal.ofReal (2 * length / r + 2) :=
    covering_by_diameter hr_pos hlength_pos.le hT_diam_length
  have hD_div : 2 * D / r + 2 ≤ A := by
    dsimp only [A]
    have hD_nonneg : 0 ≤ 2 * D := by positivity
    have hdiv : 2 * D / r ≤ 2 * D / delta := by
      exact div_le_div_of_nonneg_left hD_nonneg hdelta_pos hdelta_r
    linarith
  have hlength_div : 2 * length / r + 2 ≤ 4 * u := by
    calc
      2 * length / r + 2 = 2 * u + 2 := by
        dsimp only [u]
        ring
      _ ≤ 4 * u := by linarith [hu_one]
  have hcover_A :
      (Metric.externalCoveringNumber ⟨r, hr_nonneg⟩ T : ENNReal) ≤
        ENNReal.ofReal A :=
    hcover_D.trans (ENNReal.ofReal_le_ofReal hD_div)
  have hcover_4u :
      (Metric.externalCoveringNumber ⟨r, hr_nonneg⟩ T : ENNReal) ≤
        ENNReal.ofReal (4 * u) :=
    hcover_length.trans (ENNReal.ofReal_le_ofReal hlength_div)
  have hcover_min :
      (Metric.externalCoveringNumber ⟨r, hr_nonneg⟩ T : ENNReal) ≤
        ENNReal.ofReal (min A (4 * u)) := by
    rw [ENNReal.ofReal_min]
    exact le_min hcover_A hcover_4u
  have hcrossover : min A (4 * u) ≤ C * u ^ alpha :=
    crossover_lemma A 4 C u alpha hA_pos (by norm_num) hC_pos
      hu_pos halpha_pos halpha_lt_one h_endpoint_real
  have hreal :
      ENNReal.ofReal (min A (4 * u)) ≤
        ENNReal.ofReal (C * u ^ alpha) :=
    ENNReal.ofReal_le_ofReal hcrossover
  calc
    (Metric.externalCoveringNumber ⟨r, hr_nonneg⟩
        (E ∩ Set.Icc left (left + length)) : ENNReal)
        ≤ ENNReal.ofReal (min A (4 * u)) := hcover_min
    _ ≤ ENNReal.ofReal (C * u ^ alpha) := hreal
    _ = Kakeya.realRpowENN delta (-loss) *
          Kakeya.realRpowENN (length / r) (1 - sigma) := by
      rw [hC_eq]
      change ENNReal.ofReal (C * u ^ alpha) =
        ENNReal.ofReal C * ENNReal.ofReal ((length / r) ^ (1 - sigma))
      rw [← ENNReal.ofReal_mul hC_pos.le]

/-- The exact mixed carrier needed immediately before the paper's Lemma 23:
the set is the genuine first-sticky coarse shading, while `f` and the local
normal witnesses retain the original source provenance. -/
structure PureWZ2SourceFixedBinCoarseOriginalSlopeData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (carrier : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (fineWitnesses : PureWZ2CoarseCellWitnessData twoScale) : Type where
  original_interval_slope_exactAD :
    ∀ z : PureWZ2UnitInterval,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.f z))
          (horizontalSlice carrier.shading.union z.1))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss))

abbrev PureWZ2SourceFixedLineCoarseOriginalSlopeData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (carrier : PureWZ2SourceFixedLineCoarseCarrierData residue)
    (fineWitnesses : PureWZ2CoarseCellWitnessData twoScale) : Type :=
  PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses

/-- Ambient compatibility view used only by the existing WZ1 Lemma-23
machinery.  The stored mathematical witness remains the interval function
`source.globalGrains.f`. -/
theorem PureWZ2SourceFixedBinCoarseOriginalSlopeData.original_slope_exactADFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2CoarseCellWitnessData twoScale}
    (data : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice carrier.shading.union z))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss)) := by
  intro z hz
  rw [source.globalGrains.slope_eq_f z hz]
  exact data.original_interval_slope_exactAD ⟨z, hz⟩

/-- A point of the genuine first-sticky coarse carrier has an original fine
witness in the same side-`rho` paper cell. -/
lemma PureWZ2SourceFixedBinCoarseCarrierData.point_has_source_cell_witnessFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (data : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (witnesses : PureWZ2CoarseCellWitnessData twoScale)
    {point : Point3} (hpoint : point ∈ data.shading.union) :
    ∃ cell ∈ witnesses.activeCells,
      point ∈ wz1PaperGridCube rho cell ∧
        witnesses.witness cell ∈ source.shading.union ∧
          witnesses.witness cell ∈ wz1PaperGridCube rho cell := by
  have hcoarseGrains : point ∈ twoScale.coarseGrains.shading.union :=
    data.subshading.union_subset hpoint
  have hcoarse : point ∈ twoScale.coarse.croppedCoarseShading.union :=
    twoScale.coarseGrains.subshading.union_subset hcoarseGrains
  rw [twoScale.coarse.balanced.coarse_union_eq] at hcoarse
  rcases Set.mem_iUnion₂.mp hcoarse with ⟨cell, hcell, hpointCell⟩
  have hcell' : cell ∈ witnesses.activeCells := by
    rw [witnesses.activeCells_eq]
    exact hcell
  refine ⟨cell, hcell', ?_, ?_, ?_⟩
  · simpa only [twoScale.rhoRequested_eq] using hpointCell
  · exact ⟨witnesses.sourceIndex cell,
      witnesses.witness_mem_source cell hcell'⟩
  · exact witnesses.witness_mem_cell cell hcell'

/-- Backwards-compatible maximal-bin specialization of the same-cell source
witness. -/
lemma PureWZ2SourceFixedLineCoarseCarrierData.point_has_source_cell_witness
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (data : PureWZ2SourceFixedLineCoarseCarrierData residue)
    (witnesses : PureWZ2CoarseCellWitnessData twoScale)
    {point : Point3} (hpoint : point ∈ data.shading.union) :
    ∃ cell ∈ witnesses.activeCells,
      point ∈ wz1PaperGridCube rho cell ∧
        witnesses.witness cell ∈ source.shading.union ∧
          witnesses.witness cell ∈ wz1PaperGridCube rho cell :=
  data.point_has_source_cell_witnessFixedBin witnesses hpoint

/-- Every original-slope projection value on an exact slice of the fixed-line
genuine-coarse carrier is within `5 * rho` of an original-source projection
from the corresponding side-`rho` height slab.  The source point is the
balanced-cover witness in the same literal side-`rho` cell. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.originalSlope_exactSlice_subset_sourceRhoSlab_thickening
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (data : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (witnesses : PureWZ2CoarseCellWitnessData twoScale) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice data.shading.union z) ⊆
        Metric.cthickening (5 * rho)
          (globalGrainProjection source.globalGrains.slope
            (globalGrainSlab source.shading.union z rho)) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  intro z hz value hvalue
  rcases hvalue with ⟨point, hpoint, rfl⟩
  rcases data.point_has_source_cell_witnessFixedBin witnesses hpoint.1 with
    ⟨cell, _hcell, hpointCell, hsource, hsourceCell⟩
  let sourcePoint := witnesses.witness cell
  have hx : |point 0 - sourcePoint 0| ≤ rho :=
    (pureWZ2_same_grid_cell_coord_lt hrho hsourceCell hpointCell 0).le
  have hy : |point 1 - sourcePoint 1| ≤ rho :=
    (pureWZ2_same_grid_cell_coord_lt hrho hsourceCell hpointCell 1).le
  have hzclose : |point 2 - sourcePoint 2| ≤ rho :=
    (pureWZ2_same_grid_cell_coord_lt hrho hsourceCell hpointCell 2).le
  have hsourceBox := shading_union_subset_axisBox hsource
  have hsourceHeight : sourcePoint 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hsourceBox.2.2
  have hsourceY : |sourcePoint 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hsourceBox.2.1
  have hsourceSlab : sourcePoint ∈
      globalGrainSlab source.shading.union z rho := by
    refine ⟨⟨hsource, ?_⟩, hsourceHeight⟩
    rw [hpoint.2] at hzclose
    exact ⟨by linarith [abs_le.mp hzclose],
      by linarith [abs_le.mp hzclose]⟩
  let sourceValue := inner ℝ sourcePoint
    (globalGrainDirection (source.globalGrains.slope (sourcePoint 2)))
  have hsourceValue : sourceValue ∈
      globalGrainProjection source.globalGrains.slope
        (globalGrainSlab source.shading.union z rho) :=
    ⟨sourcePoint, hsourceSlab, rfl⟩
  have hslopeClose :
      |source.globalGrains.slope z -
          source.globalGrains.slope (sourcePoint 2)| ≤ rho := by
    have hlip := source.globalGrains.slope_lipschitz.dist_le_mul
      z hz (sourcePoint 2) hsourceHeight
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    have hheight : |z - sourcePoint 2| ≤ rho := by
      rw [hpoint.2] at hzclose
      exact hzclose
    exact hlip.trans hheight
  have hslope : |source.globalGrains.slope z| ≤ 3 :=
    source.globalGrains.slope_bound z hz
  have hformula :
      inner ℝ point (globalGrainDirection (source.globalGrains.slope z)) -
          sourceValue =
        (point 0 - sourcePoint 0) +
          source.globalGrains.slope z * (point 1 - sourcePoint 1) +
          (source.globalGrains.slope z -
            source.globalGrains.slope (sourcePoint 2)) * sourcePoint 1 := by
    dsimp only [sourceValue]
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    ring
  have hclose :
      |inner ℝ point (globalGrainDirection (source.globalGrains.slope z)) -
          sourceValue| ≤ 5 * rho := by
    rw [hformula]
    calc
      |(point 0 - sourcePoint 0) +
          source.globalGrains.slope z * (point 1 - sourcePoint 1) +
          (source.globalGrains.slope z -
            source.globalGrains.slope (sourcePoint 2)) * sourcePoint 1| ≤
        |point 0 - sourcePoint 0| +
          |source.globalGrains.slope z| * |point 1 - sourcePoint 1| +
          |source.globalGrains.slope z -
            source.globalGrains.slope (sourcePoint 2)| * |sourcePoint 1| := by
          calc
            _ ≤ |(point 0 - sourcePoint 0) +
                  source.globalGrains.slope z *
                    (point 1 - sourcePoint 1)| +
                |(source.globalGrains.slope z -
                  source.globalGrains.slope (sourcePoint 2)) *
                    sourcePoint 1| := abs_add_le _ _
            _ ≤ (|point 0 - sourcePoint 0| +
                  |source.globalGrains.slope z *
                    (point 1 - sourcePoint 1)|) +
                |(source.globalGrains.slope z -
                  source.globalGrains.slope (sourcePoint 2)) *
                    sourcePoint 1| := by
              gcongr
              exact abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ rho + 3 * rho + rho * 1 := by gcongr
      _ = 5 * rho := by ring
  exact Metric.mem_cthickening_of_dist_le _ sourceValue (5 * rho) _
    hsourceValue (by simpa [Real.dist_eq] using hclose)

/-- Transport one explicit source `rho`-slab AD receipt to exact slices of the
fixed-line genuine-coarse carrier.  This is the paper-faithful replacement for
the bounded-diameter endpoint estimate. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.originalSlope_exactAD_of_sourceRhoSlabAD
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (data : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (witnesses : PureWZ2CoarseCellWitnessData twoScale)
    {C : ENNReal}
    (hsourceRhoSlabAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (globalGrainProjection source.globalGrains.slope
          (globalGrainSlab source.shading.union z rho))
        rho (1 - sigma) C)
    (hconstant :
      144 * C ≤ 10 * Kakeya.realRpowENN rho (-middleLoss)) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice data.shading.union z))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss)) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  intro z hz
  have hbounded :
      scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice data.shading.union z) ⊆
        Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hbox := shading_union_subset_axisBox
      (data.subshading.union_subset hpoint.1)
    have hzero : |point 0| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have hone : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hslope := source.globalGrains.slope_bound z hz
    have hformula :
        inner ℝ point (globalGrainDirection (source.globalGrains.slope z)) =
          point 0 + source.globalGrains.slope z * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    change inner ℝ point
        (globalGrainDirection (source.globalGrains.slope z)) ∈
      Set.Icc (-4 : ℝ) 4
    rw [hformula]
    apply abs_le.mp
    calc
      |point 0 + source.globalGrains.slope z * point 1| ≤
          |point 0| + |source.globalGrains.slope z| * |point 1| := by
        calc
          _ ≤ |point 0| +
              |source.globalGrains.slope z * point 1| := abs_add_le _ _
          _ = _ := by rw [abs_mul]
      _ ≤ 1 + 3 * 1 := by gcongr
      _ = 4 := by norm_num
  have hsubset :=
    data.originalSlope_exactSlice_subset_sourceRhoSlab_thickening
      witnesses z hz
  have hthick := IsADSet1.generalized_thickening
    (ε := 5 * rho) (hsourceRhoSlabAD z hz) hsubset hbounded hrho
      (by positivity)
  have hratio : (5 * rho) / rho = (5 : ℝ) := by
    field_simp [hrho.ne']
  rw [hratio] at hthick
  norm_num at hthick
  exact hthick.mono_constant hconstant

/-- Package the mixed fixed-line carrier from an explicit original-source
`rho`-slab AD certificate, with no bounded-diameter endpoint premise. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.withSourceRhoSlabADFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (data : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (witnesses : PureWZ2CoarseCellWitnessData twoScale)
    {C : ENNReal}
    (hsourceRhoSlabAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (globalGrainProjection source.globalGrains.slope
          (globalGrainSlab source.shading.union z rho))
        rho (1 - sigma) C)
    (hconstant :
      144 * C ≤ 10 * Kakeya.realRpowENN rho (-middleLoss)) :
    Nonempty (PureWZ2SourceFixedBinCoarseOriginalSlopeData
      data witnesses) := by
  refine ⟨{ original_interval_slope_exactAD := ?_ }⟩
  intro z
  have h := data.originalSlope_exactAD_of_sourceRhoSlabAD witnesses
    hsourceRhoSlabAD hconstant z.1 z.2
  rwa [source.globalGrains.slope_eq_f z.1 z.2] at h

/-- Exact-slice global AD for the genuine coarse carrier, measured using the
original interval slope.  The fixed-line localization bounds every projected
slice by diameter `28 * sqrt rho`; the endpoint hypothesis absorbs the
corresponding elementary covering cost. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.original_interval_slope_exactADFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (data : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCge :
      (4 : ENNReal) ≤ Kakeya.realRpowENN rho (-middleLoss))
    (hendpoint :
      ENNReal.ofReal
          ((2 * (28 * twoScale.sqrtRequested.1) / rho + 2) ^ sigma *
            4 ^ (1 - sigma)) ≤
        Kakeya.realRpowENN rho (-middleLoss))
    (hbridge : PureWZ2PaperADBridgeStatement) :
    ∀ z : PureWZ2UnitInterval,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.f z))
          (horizontalSlice data.shading.union z.1))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss)) := by
  intro z
  let E :=
    scalarProjection
      (globalGrainDirection (source.globalGrains.f z))
      (horizontalSlice data.shading.union z.1)
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hroot : 0 < twoScale.sqrtRequested.1 :=
    twoScale.fine.coarse_extremal.delta_pos
  have hdiam :
      ∀ x y, x ∈ E → y ∈ E →
        |x - y| ≤ 28 * twoScale.sqrtRequested.1 := by
    rintro x y ⟨pointX, hpointX, rfl⟩ ⟨pointY, hpointY, rfl⟩
    have hx := data.fixed_line_localizationFixedBin pointX hpointX.1
    have hy := data.fixed_line_localizationFixedBin pointY hpointY.1
    rw [hpointX.2, source.globalGrains.slope_eq_f z.1 z.2] at hx
    rw [hpointY.2, source.globalGrains.slope_eq_f z.1 z.2] at hy
    calc
      |inner ℝ pointX (globalGrainDirection (source.globalGrains.f z)) -
          inner ℝ pointY (globalGrainDirection (source.globalGrains.f z))|
          ≤ |inner ℝ pointX
                (globalGrainDirection (source.globalGrains.f z)) -
              line.lineLevel| +
            |line.lineLevel - inner ℝ pointY
                (globalGrainDirection (source.globalGrains.f z))| :=
            abs_sub_le _ _ _
      _ = |inner ℝ pointX
                (globalGrainDirection (source.globalGrains.f z)) -
              line.lineLevel| +
            |inner ℝ pointY
                (globalGrainDirection (source.globalGrains.f z)) -
              line.lineLevel| := by rw [abs_sub_comm line.lineLevel]
      _ ≤ 14 * twoScale.sqrtRequested.1 +
            14 * twoScale.sqrtRequested.1 := add_le_add hx hy
      _ = 28 * twoScale.sqrtRequested.1 := by ring
  have hbounded :
      E ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hbox := shading_union_subset_axisBox
      (data.subshading.union_subset hpoint.1)
    have h0 : |point 0| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have h1 : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hslope := source.globalGrains.f_bound z
    have hformula :
        inner ℝ point
            (globalGrainDirection (source.globalGrains.f z)) =
          point 0 + source.globalGrains.f z * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    change inner ℝ point
        (globalGrainDirection (source.globalGrains.f z)) ∈
      Set.Icc (-4 : ℝ) 4
    rw [hformula]
    apply abs_le.mp
    calc
      |point 0 + source.globalGrains.f z * point 1| ≤
          |point 0| + |source.globalGrains.f z| * |point 1| := by
        calc
          _ ≤ |point 0| +
              |source.globalGrains.f z * point 1| := abs_add_le _ _
          _ = _ := by rw [abs_mul]
      _ ≤ 1 + 3 * 1 := by gcongr
      _ = 4 := by norm_num
  have hpaper : PureWZ2PaperADSet1 E rho (1 - sigma)
      (Kakeya.realRpowENN rho (-middleLoss)) :=
    pureWZ2_paperAD_of_bounded_diameter
      line.rho_pos hrhoOne hsigma hsigmaOne
      (by positivity) hdiam hCge hendpoint
  exact hbridge.1 E rho (1 - sigma)
    (Kakeya.realRpowENN rho (-middleLoss)) hbounded hpaper

/-- Package the mixed coarse/fine Lemma-23 boundary from a direct
original-slope exact-slice certificate.  Fine normal witnesses are selected
canonically from the first balanced cover. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.withOriginalSlopeFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (carrier : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (fineWitnesses : PureWZ2CoarseCellWitnessData twoScale)
    (hexact : ∀ z : PureWZ2UnitInterval,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.f z))
          (horizontalSlice carrier.shading.union z.1))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty (PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses) :=
  ⟨{ original_interval_slope_exactAD := hexact }⟩

/-- Production original-slope certificate obtained by restricting the exact
global AD data of the intermediate coarse grain refinement.  The carrier is a
literal subshading of that refinement, and `coarse_slope_eq` identifies its
slope with the original source slope.  The paper-to-internal bridge pays only
its fixed factor ten; no diameter endpoint estimate is used. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.withCoarseGlobalGrainsFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (carrier : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (fineWitnesses : PureWZ2CoarseCellWitnessData twoScale)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses) := by
  apply carrier.withOriginalSlopeFixedBin fineWitnesses
  intro z
  let E :=
    scalarProjection
      (globalGrainDirection (source.globalGrains.f z))
      (horizontalSlice carrier.shading.union z.1)
  have hpaper :
      PureWZ2PaperADSet1 E rho (1 - sigma)
        (Kakeya.realRpowENN rho (-middleLoss)) := by
    have hambient :=
      twoScale.coarseGrains.globalGrains.global_ad z.1 z.2
    rw [twoScale.coarse_slope_eq,
      source.globalGrains.slope_eq_f z.1 z.2] at hambient
    have hsub :
        E ⊆ scalarProjection
          (globalGrainDirection (source.globalGrains.f z))
          (horizontalSlice twoScale.coarseGrains.shading.union z.1) := by
      rintro value ⟨point, hpoint, rfl⟩
      exact ⟨point,
        ⟨carrier.subshading.union_subset hpoint.1, hpoint.2⟩, rfl⟩
    simpa only [twoScale.rhoRequested_eq] using hambient.mono hsub
  have hbounded : E ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hbox := shading_union_subset_axisBox
      (carrier.subshading.union_subset hpoint.1)
    have h0 : |point 0| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have h1 : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hslope := source.globalGrains.f_bound z
    have hformula :
        inner ℝ point
            (globalGrainDirection (source.globalGrains.f z)) =
          point 0 + source.globalGrains.f z * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    change inner ℝ point
        (globalGrainDirection (source.globalGrains.f z)) ∈
      Set.Icc (-4 : ℝ) 4
    rw [hformula]
    apply abs_le.mp
    calc
      |point 0 + source.globalGrains.f z * point 1| ≤
          |point 0| + |source.globalGrains.f z| * |point 1| := by
        calc
          _ ≤ |point 0| +
              |source.globalGrains.f z * point 1| := abs_add_le _ _
          _ = _ := by rw [abs_mul]
      _ ≤ 1 + 3 * 1 := by gcongr
      _ = 4 := by norm_num
  exact hbridge.1 E rho (1 - sigma)
    (Kakeya.realRpowENN rho (-middleLoss)) hbounded hpaper

/-- Canonical paper-order constructor for the mixed carrier.  It uses only the
original interval slope and the endpoint budget for the fixed-line diameter;
there is no slope-equality premise from the second grain refinement. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.withEndpointBudgetFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (carrier : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (fineWitnesses : PureWZ2CoarseCellWitnessData twoScale)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCge :
      (4 : ENNReal) ≤ Kakeya.realRpowENN rho (-middleLoss))
    (hendpoint :
      ENNReal.ofReal
          ((2 * (28 * twoScale.sqrtRequested.1) / rho + 2) ^ sigma *
            4 ^ (1 - sigma)) ≤
        Kakeya.realRpowENN rho (-middleLoss))
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses) :=
  carrier.withOriginalSlopeFixedBin fineWitnesses
    (carrier.original_interval_slope_exactADFixedBin hsigma hsigmaOne
      hCge hendpoint hbridge)

/-- Lemma-23 preparation on the genuine first-sticky carrier, while retaining
the original source slope.  The graph grid has side `256 * rho`; the carrier
itself remains the side-`rho` coarse shading selected before Lemma 23. -/
structure PureWZ2SourceFixedBinCoarsePreparationData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2CoarseCellWitnessData twoScale}
    (original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses) : Type where
  graphScale : ℝ := 256 * rho
  graphScale_eq : graphScale = 256 * rho
  graphScale_pos : 0 < graphScale
  graphScale_one : graphScale ≤ 1
  graphScale_sqrt :
    Real.sqrt graphScale = 16 * twoScale.sqrtRequested.1
  graphScale_two_root_bound :
    graphScale + 2 * twoScale.sqrtRequested.1 ≤
      16 * twoScale.sqrtRequested.1
  rho_le_graphScale : rho ≤ graphScale
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily carrier.shading
      twoScale.coarseGrains.extremal.delta_pos) :=
    pureWZ2ActiveCellShading carrier.shading
      twoScale.coarseGrains.extremal.delta_pos
  shadow_union_subset : shadow.union ⊆ carrier.shading.union
  windowed : WZ1Lemma23WindowedGlobalSlicePackage
    (delta := twoScale.rhoRequested.1) (rho := graphScale)
    (sigma := sigma) shadow
    (10 * Kakeya.realRpowENN rho (-middleLoss))
  sourceSlope_eq :
    windowed.global.sourceSlope = source.globalGrains.slope
  exactAD :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (windowed.global.sourceSlope z))
          (horizontalSlice shadow.union z))
        graphScale (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss))
  fixed_line_localization :
    ∀ point ∈ shadow.union,
      |inner ℝ point
          (globalGrainDirection
            (windowed.global.sourceSlope (point (2 : Fin 3)))) -
        line.lineLevel| ≤ 14 * twoScale.sqrtRequested.1
  localization : WZ1Lemma23GlobalLocalizationInput windowed.global

abbrev PureWZ2SourceFixedLineCoarsePreparationData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {carrier : PureWZ2SourceFixedLineCoarseCarrierData residue}
    {fineWitnesses : PureWZ2CoarseCellWitnessData twoScale}
    (original : PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carrier fineWitnesses) : Type :=
  PureWZ2SourceFixedBinCoarsePreparationData original

/-- A literal side-`rho` cell restriction of an existing fixed-bin coarse
carrier, represented on the carrier's ordinary active-cell family. -/
structure PureWZ2SourceFixedBinCoarseCellRestrictionPreparationData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2CoarseCellWitnessData twoScale}
    (original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses)
    (cells : Finset (ℤ × ℤ × ℤ)) where
  cells_subset : cells ⊆ wz1PaperActiveCells carrier.shading
    twoScale.coarseGrains.extremal.delta_pos
  cells_nonempty : cells.Nonempty
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily carrier.shading
      twoScale.coarseGrains.extremal.delta_pos)
  subshading : IsSubshading shadow
    (pureWZ2ActiveCellShading carrier.shading
      twoScale.coarseGrains.extremal.delta_pos)
  union_eq : shadow.union = wz2RetainedCellsUnion rho cells
  volume_eq : volume shadow.union =
    (cells.card : ENNReal) * volume (wz1PaperGridCube rho (0, 0, 0))
  prep : PureWZ2SourceFixedBinCoarsePreparationData original
  prep_shadow : prep.shadow = shadow

/-- Build the common original-slope preparation on any ordinary subshadow of
the genuine fixed-bin coarse carrier.  This is the reusable restriction
principle behind both exact height cuts and whole-cell envelopes. -/
theorem PureWZ2SourceFixedBinCoarseOriginalSlopeData.prepareSubshadowFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2CoarseCellWitnessData twoScale}
    (original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses)
    (shadow : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily carrier.shading
        twoScale.coarseGrains.extremal.delta_pos))
    (hshadowSub : shadow.union ⊆ carrier.shading.union)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    ∃ prep : PureWZ2SourceFixedBinCoarsePreparationData original,
      prep.shadow = shadow := by
  let root := twoScale.sqrtRequested.1
  let graphScale := 256 * rho
  let C : ENNReal := 10 * Kakeya.realRpowENN rho (-middleLoss)
  have hrho : 0 < rho := line.rho_pos
  have hroot : 0 < root := twoScale.fine.coarse_extremal.delta_pos
  have hgraph : 0 < graphScale := by positivity
  have hrhoGraph : rho ≤ graphScale := by
    dsimp only [graphScale]
    nlinarith
  have hsqrtRho : root = Real.sqrt rho := twoScale.sqrtRequested_eq
  have hsqrtGraph : Real.sqrt graphScale = 16 * root := by
    rw [show graphScale = 256 * rho by rfl,
      Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt (256 : ℝ) = 16 by norm_num, ← hsqrtRho]
  have hball : shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hcoarse := carrier.subshading.union_subset (hshadowSub hpoint)
    have hnorm := norm_le_two_of_mem_paperShading hcoarse
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord : ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hbox := shading_union_subset_axisBox
      (carrier.subshading.union_subset (hshadowSub hpoint))
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hexactBase :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          twoScale.rhoRequested.1 (1 - sigma) C := by
    intro z hz
    have hmono :
        scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice shadow.union z) ⊆
          scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice carrier.shading.union z) := by
      rintro value ⟨point, hpoint, rfl⟩
      exact ⟨point, ⟨hshadowSub hpoint.1, hpoint.2⟩, rfl⟩
    have h := (original.original_slope_exactADFixedBin z hz).mono hmono
    simpa only [twoScale.rhoRequested_eq, C] using h
  have hCtop : C ≠ ⊤ := by
    dsimp only [C]
    exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      shadow hgraph
      (by simpa [twoScale.rhoRequested_eq] using hrhoGraph)
      hgraphOne hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound C hCtop hexactBase with
    ⟨global, hsourceSlope⟩
  let left := (carrier.commonParentHeight : ℝ) * root - graphScale / 2
  have hactiveWindow : WZ1Lemma23ActiveCellHeightWindow shadow global.rho_pos := by
    refine ⟨left, ?_⟩
    intro cell hcell
    have hactive := (wz1Lemma23_mem_active_iff shadow hgraph cell).mp hcell
    rcases hactive.2 with ⟨point, hpoint, hpointCell⟩
    have hheight := carrier.union_height point (hshadowSub hpoint)
    have hcenter := ((wz1_lemma23_snapped_cell_geometry
      graphScale hgraph hgraphOne).2.1 cell point hpointCell).1
        (2 : Fin 3)
    rw [abs_le] at hcenter
    constructor
    · dsimp only [left]
      linarith [hheight.1, hcenter.2]
    · dsimp only [left]
      rw [hsqrtGraph]
      have hshort : graphScale + root ≤ 16 * root := by
        linarith [hheightAbsorb]
      linarith [hheight.2, hcenter.1]
  let windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := twoScale.rhoRequested.1) (rho := graphScale)
      (sigma := sigma) shadow C :=
    { global := global
      active_height_window := hactiveWindow }
  have hexactGraph :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (global.sourceSlope z))
            (horizontalSlice shadow.union z))
          graphScale (1 - sigma) C := by
    intro z hz
    rw [hsourceSlope]
    exact (hexactBase z hz).coarsen_scale hgraph
      (by simpa [twoScale.rhoRequested_eq] using hrhoGraph) hgraphOne
  have hfixedLine :
      ∀ point ∈ shadow.union,
        |inner ℝ point
            (globalGrainDirection
              (global.sourceSlope (point (2 : Fin 3)))) -
          line.lineLevel| ≤ 14 * root := by
    intro point hpoint
    rw [hsourceSlope]
    exact carrier.fixed_line_localizationFixedBin point (hshadowSub hpoint)
  have hlocalization : WZ1Lemma23GlobalLocalizationInput windowed.global := by
    refine ⟨fun _ => line.lineLevel, ?_⟩
    intro heightIndex hheightIndex
    rintro value ⟨point, hpoint, rfl⟩
    have hbound := hfixedLine point hpoint.1
    rw [hpoint.2] at hbound
    rw [Metric.mem_closedBall, Real.dist_eq, hsqrtGraph]
    exact hbound.trans (by nlinarith [hroot])
  exact ⟨{
    graphScale := graphScale
    graphScale_eq := rfl
    graphScale_pos := hgraph
    graphScale_one := hgraphOne
    graphScale_sqrt := hsqrtGraph
    graphScale_two_root_bound := by
      simpa [graphScale, root] using hheightAbsorb
    rho_le_graphScale := hrhoGraph
    shadow := shadow
    shadow_union_subset := hshadowSub
    windowed := windowed
    sourceSlope_eq := hsourceSlope
    exactAD := hexactGraph
    fixed_line_localization := hfixedLine
    localization := hlocalization
  }, rfl⟩

/-- Prepare the original-slope graph on an arbitrary nonempty literal subset
of the fixed-bin carrier's active side-`rho` cells.  The ordinary shadow is
indexed by the ambient active-cell family, but its union is exactly the chosen
cell union. -/
theorem PureWZ2SourceFixedBinCoarseOriginalSlopeData.prepareCellRestrictionFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2CoarseCellWitnessData twoScale}
    (original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses)
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : cells ⊆ wz1PaperActiveCells carrier.shading
      twoScale.coarseGrains.extremal.delta_pos)
    (hnonempty : cells.Nonempty)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2SourceFixedBinCoarseCellRestrictionPreparationData
      original cells) := by
  let hbase : 0 < twoScale.rhoRequested.1 :=
    twoScale.coarseGrains.extremal.delta_pos
  let ambient := pureWZ2ActiveCellShading carrier.shading hbase
  let region := wz2RetainedCellsUnion rho cells
  let shadow : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily carrier.shading hbase) :=
    { carrier := fun index => ambient.carrier index ∩ region
      measurable_carrier := fun index =>
        (ambient.measurable_carrier index).inter
          (MeasurableSet.biUnion cells.finite_toSet.countable
            (fun cell _ => wz1PaperGridCube_measurable cell))
      subset_body := fun index => Set.inter_subset_left.trans
        (ambient.subset_body index) }
  have hambientUnion : ambient.union = carrier.shading.union :=
    pureWZ2ActiveCellShading_union carrier.shading hbase carrier.whole_cells
  have hregionCarrier : region ⊆ carrier.shading.union := by
    intro point hpoint
    change point ∈ ⋃ cell ∈ cells, wz1PaperGridCube rho cell at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    have hactive := hcells hcell
    have hinter := carrier.whole_cells.inter_activeCell_eq hbase hactive
    have hpointCell' : point ∈
        wz1PaperGridCube twoScale.rhoRequested.1 cell := by
      simpa only [twoScale.rhoRequested_eq] using hpointCell
    have hintersection : point ∈ carrier.shading.union ∩
        wz1PaperGridCube twoScale.rhoRequested.1 cell := by
      rw [hinter]
      exact hpointCell'
    exact hintersection.1
  have hunion : shadow.union = region := by
    ext point
    constructor
    · rintro ⟨_index, _hambient, hregion⟩
      exact hregion
    · intro hregion
      have hcarrier := hregionCarrier hregion
      have hambient : point ∈ ambient.union := by
        rwa [hambientUnion]
      rcases hambient with ⟨index, hindex⟩
      exact ⟨index, hindex, hregion⟩
  have hsub : IsSubshading shadow ambient :=
    fun _ => Set.inter_subset_left
  have hshadowSub : shadow.union ⊆ carrier.shading.union := by
    rw [hunion]
    exact hregionCarrier
  have hvolume : volume shadow.union =
      (cells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [hunion]
    exact wz1PaperGridCube_volume_biUnion
      (by simpa only [twoScale.rhoRequested_eq] using hbase) cells
  rcases original.prepareSubshadowFixedBin shadow hshadowSub hgraphOne
      hheightAbsorb with ⟨prep, hprep⟩
  exact ⟨{
    cells_subset := hcells
    cells_nonempty := hnonempty
    shadow := shadow
    subshading := hsub
    union_eq := hunion
    volume_eq := hvolume
    prep := prep
    prep_shadow := hprep
  }⟩

/-- Build the genuine-coarse, original-slope preparation from the interval
certificate.  This is the paper's input `N_{sqrt rho}(L) ∩ E_{T_tilde}` for
Lemma 23. -/
theorem PureWZ2SourceFixedBinCoarseOriginalSlopeData.prepareFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2CoarseCellWitnessData twoScale}
    (original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    ∃ prep : PureWZ2SourceFixedBinCoarsePreparationData original,
      prep.shadow.union = carrier.shading.union := by
  let root := twoScale.sqrtRequested.1
  let graphScale := 256 * rho
  let C : ENNReal := 10 * Kakeya.realRpowENN rho (-middleLoss)
  have hrho : 0 < rho := line.rho_pos
  have hroot : 0 < root := twoScale.fine.coarse_extremal.delta_pos
  have hbase : 0 < twoScale.rhoRequested.1 :=
    twoScale.coarseGrains.extremal.delta_pos
  have hgraph : 0 < graphScale := by positivity
  have hrhoGraph : rho ≤ graphScale := by
    dsimp only [graphScale]
    nlinarith
  have hsqrtRho : root = Real.sqrt rho := twoScale.sqrtRequested_eq
  have hsqrtGraph : Real.sqrt graphScale = 16 * root := by
    rw [show graphScale = 256 * rho by rfl, Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt (256 : ℝ) = 16 by norm_num, ← hsqrtRho]
  let shadow := pureWZ2ActiveCellShading carrier.shading hbase
  have hunion : shadow.union = carrier.shading.union :=
    pureWZ2ActiveCellShading_union carrier.shading hbase carrier.whole_cells
  have hball : shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hcarrier : point ∈ carrier.shading.union := by
      simpa [hunion] using hpoint
    have hcoarse := carrier.subshading.union_subset hcarrier
    have hnorm := norm_le_two_of_mem_paperShading hcoarse
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord :
      ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hcarrier : point ∈ carrier.shading.union := by
      simpa [hunion] using hpoint
    have hbox := shading_union_subset_axisBox
      (carrier.subshading.union_subset hcarrier)
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hexactBase :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          twoScale.rhoRequested.1 (1 - sigma) C := by
    intro z hz
    rw [hunion]
    simpa only [C, twoScale.rhoRequested_eq] using
      original.original_slope_exactADFixedBin z hz
  have hCtop : C ≠ ⊤ := by
    dsimp only [C]
    exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      shadow hgraph (by simpa [twoScale.rhoRequested_eq] using hrhoGraph)
      hgraphOne hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound C hCtop hexactBase with
    ⟨global, hsourceSlope⟩
  let left :=
    (carrier.commonParentHeight : ℝ) * root - graphScale / 2
  have hactiveWindow :
      WZ1Lemma23ActiveCellHeightWindow shadow global.rho_pos := by
    refine ⟨left, ?_⟩
    intro cell hcell
    have hactive :=
      (wz1Lemma23_mem_active_iff shadow hgraph cell).mp hcell
    rcases hactive.2 with ⟨point, hpoint, hpointCell⟩
    have hcarrier : point ∈ carrier.shading.union := by
      simpa [hunion] using hpoint
    have hheight := carrier.union_height point hcarrier
    have hcenter :=
      ((wz1_lemma23_snapped_cell_geometry
        graphScale hgraph hgraphOne).2.1 cell point hpointCell).1
        (2 : Fin 3)
    rw [abs_le] at hcenter
    have hcenterLower :
        point (2 : Fin 3) - graphScale / 2 ≤
          (wz1Lemma23SnappedPoint graphScale cell) (2 : Fin 3) := by
      linarith [hcenter.2]
    have hcenterUpper :
        (wz1Lemma23SnappedPoint graphScale cell) (2 : Fin 3) ≤
          point (2 : Fin 3) + graphScale / 2 := by
      linarith [hcenter.1]
    constructor
    · dsimp only [left]
      linarith [hheight.1, hcenterLower]
    · dsimp only [left]
      rw [hsqrtGraph]
      have hshort : graphScale + root ≤ 16 * root := by
        have hstrong : graphScale + 2 * root ≤ 16 * root := by
          simpa [graphScale, root] using hheightAbsorb
        linarith
      linarith [hheight.2, hcenterUpper]
  let windowedPackage : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := twoScale.rhoRequested.1) (rho := graphScale)
      (sigma := sigma) shadow C :=
    { global := global
      active_height_window := hactiveWindow }
  have hexactGraph :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (global.sourceSlope z))
            (horizontalSlice shadow.union z))
          graphScale (1 - sigma) C := by
    intro z hz
    rw [hsourceSlope]
    exact (hexactBase z hz).coarsen_scale hgraph
      (by simpa [twoScale.rhoRequested_eq] using hrhoGraph) hgraphOne
  have hfixedLine :
      ∀ point ∈ shadow.union,
        |inner ℝ point
            (globalGrainDirection
              (global.sourceSlope (point (2 : Fin 3)))) -
          line.lineLevel| ≤ 14 * root := by
    intro point hpoint
    have hcarrier : point ∈ carrier.shading.union := by
      simpa [hunion] using hpoint
    rw [hsourceSlope]
    exact carrier.fixed_line_localizationFixedBin point hcarrier
  have hlocalization :
      WZ1Lemma23GlobalLocalizationInput windowedPackage.global := by
    refine ⟨fun _ => line.lineLevel, ?_⟩
    intro heightIndex hheightIndex
    rintro value ⟨point, hpoint, rfl⟩
    have hbound := hfixedLine point hpoint.1
    rw [hpoint.2] at hbound
    rw [Metric.mem_closedBall, Real.dist_eq, hsqrtGraph]
    exact hbound.trans (by nlinarith [hroot])
  refine ⟨{
    graphScale := graphScale
    graphScale_eq := rfl
    graphScale_pos := hgraph
    graphScale_one := hgraphOne
    graphScale_sqrt := hsqrtGraph
    graphScale_two_root_bound := by
      simpa [graphScale, root] using hheightAbsorb
    rho_le_graphScale := hrhoGraph
    shadow := shadow
    shadow_union_subset := by rw [hunion]
    windowed := windowedPackage
    sourceSlope_eq := hsourceSlope
    exactAD := hexactGraph
    fixed_line_localization := hfixedLine
    localization := hlocalization
  }, ?_⟩
  exact hunion

theorem PureWZ2SourceFixedLineCoarseOriginalSlopeData.original_slope_exactAD
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {carrier : PureWZ2SourceFixedLineCoarseCarrierData residue}
    {fineWitnesses : PureWZ2CoarseCellWitnessData twoScale}
    (data : PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carrier fineWitnesses) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice carrier.shading.union z))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss)) :=
  data.original_slope_exactADFixedBin

theorem PureWZ2SourceFixedLineCoarseCarrierData.original_interval_slope_exactAD
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (data : PureWZ2SourceFixedLineCoarseCarrierData residue)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCge :
      (4 : ENNReal) ≤ Kakeya.realRpowENN rho (-middleLoss))
    (hendpoint :
      ENNReal.ofReal
          ((2 * (28 * twoScale.sqrtRequested.1) / rho + 2) ^ sigma *
            4 ^ (1 - sigma)) ≤
        Kakeya.realRpowENN rho (-middleLoss))
    (hbridge : PureWZ2PaperADBridgeStatement) :
    ∀ z : PureWZ2UnitInterval,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.f z))
          (horizontalSlice data.shading.union z.1))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss)) :=
  data.original_interval_slope_exactADFixedBin hsigma hsigmaOne hCge hendpoint hbridge

theorem PureWZ2SourceFixedLineCoarseCarrierData.withOriginalSlope
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (carrier : PureWZ2SourceFixedLineCoarseCarrierData residue)
    (fineWitnesses : PureWZ2CoarseCellWitnessData twoScale)
    (hexact : ∀ z : PureWZ2UnitInterval,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.f z))
          (horizontalSlice carrier.shading.union z.1))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty (PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carrier fineWitnesses) :=
  carrier.withOriginalSlopeFixedBin fineWitnesses hexact

theorem PureWZ2SourceFixedLineCoarseCarrierData.withEndpointBudget
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (carrier : PureWZ2SourceFixedLineCoarseCarrierData residue)
    (fineWitnesses : PureWZ2CoarseCellWitnessData twoScale)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCge :
      (4 : ENNReal) ≤ Kakeya.realRpowENN rho (-middleLoss))
    (hendpoint :
      ENNReal.ofReal
          ((2 * (28 * twoScale.sqrtRequested.1) / rho + 2) ^ sigma *
            4 ^ (1 - sigma)) ≤
        Kakeya.realRpowENN rho (-middleLoss))
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carrier fineWitnesses) :=
  carrier.withEndpointBudgetFixedBin fineWitnesses hsigma hsigmaOne hCge hendpoint hbridge

theorem PureWZ2SourceFixedLineCoarseOriginalSlopeData.prepare
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {carrier : PureWZ2SourceFixedLineCoarseCarrierData residue}
    {fineWitnesses : PureWZ2CoarseCellWitnessData twoScale}
    (original : PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carrier fineWitnesses)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2SourceFixedLineCoarsePreparationData original) := by
  rcases original.prepareFixedBin hgraphOne hheightAbsorb with ⟨prep, _⟩
  exact ⟨prep⟩

end Kakeya.Assouad

end
