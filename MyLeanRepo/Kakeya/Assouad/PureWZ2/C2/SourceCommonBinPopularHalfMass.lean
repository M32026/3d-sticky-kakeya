import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderBlockRegularization
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GoodHeights

/-!
# Half-mass popular heights for source-heavy common-bin slabs

For a nonnegative measurable height mass `m` on an interval of length
`side`, put

`m_* = (∫ m) / (2 * side)`

and retain the heights where `m ≥ m_*`.  The complementary low-height part
has mass at most one half, so the retained heights carry at least one half
of the original mass.  The final theorems apply this literal integral
statement to the planar slices of a balanced safe source block.  No graph
budget or coarse-envelope density is used.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The threshold `total / (2 * side)`, written in a form convenient for
cancelling the positive finite interval length. -/
def pureWZ2CommonBinPopularThreshold
    (total : ENNReal) (side : ℝ) : ENNReal :=
  total / 2 / ENNReal.ofReal side

theorem pureWZ2CommonBinPopularThreshold_eq
    (total : ENNReal) (side : ℝ) :
    pureWZ2CommonBinPopularThreshold total side =
      total / (2 * ENNReal.ofReal side) := by
  simp only [pureWZ2CommonBinPopularThreshold, div_eq_mul_inv]
  rw [ENNReal.mul_inv (by simp) (by simp)]
  ac_rfl

/-- Heights in the interval where the slice mass is at least the half-mass
threshold. -/
def pureWZ2CommonBinPopularHeights
    (m : ℝ → ENNReal) (left side : ℝ) : Set ℝ :=
  Set.Ico left (left + side) ∩
    {z | pureWZ2CommonBinPopularThreshold
      (∫⁻ w in Set.Ico left (left + side), m w) side ≤ m z}

theorem measurableSet_pureWZ2CommonBinPopularHeights
    {m : ℝ → ENNReal} (hm : Measurable m) (left side : ℝ) :
    MeasurableSet (pureWZ2CommonBinPopularHeights m left side) := by
  exact measurableSet_Ico.inter <|
    measurableSet_le measurable_const hm

/-- The part below `total / (2 * side)` carries at most half of the total
mass.  This is the quantitative fact that a mere lower bound for the measure
of popular heights cannot replace. -/
theorem pureWZ2CommonBin_lowHeightMass_le_half
    {m : ℝ → ENNReal} (hm : Measurable m)
    {left side : ℝ} (hside : 0 < side) :
    (∫⁻ z in Set.Ico left (left + side) \
        pureWZ2CommonBinPopularHeights m left side, m z) ≤
      (∫⁻ z in Set.Ico left (left + side), m z) / 2 := by
  let interval : Set ℝ := Set.Ico left (left + side)
  let total : ENNReal := ∫⁻ z in interval, m z
  let threshold : ENNReal :=
    pureWZ2CommonBinPopularThreshold total side
  let popular : Set ℝ :=
    pureWZ2CommonBinPopularHeights m left side
  have hpopularMeas : MeasurableSet popular :=
    measurableSet_pureWZ2CommonBinPopularHeights hm left side
  have hlowMeas : MeasurableSet (interval \ popular) :=
    measurableSet_Ico.diff hpopularMeas
  have hpoint :
      ∀ z ∈ interval \ popular, m z ≤ threshold := by
    intro z hz
    have hzNot : ¬ threshold ≤ m z := by
      intro hzHigh
      apply hz.2
      exact ⟨hz.1, hzHigh⟩
    exact le_of_lt (lt_of_not_ge hzNot)
  calc
    (∫⁻ z in Set.Ico left (left + side) \
        pureWZ2CommonBinPopularHeights m left side, m z) =
        ∫⁻ z in interval \ popular, m z := rfl
    _ ≤ ∫⁻ _z in interval \ popular, threshold :=
      setLIntegral_mono' hlowMeas hpoint
    _ = threshold * volume (interval \ popular) :=
      setLIntegral_const (interval \ popular) threshold
    _ ≤ threshold * volume interval := by
      gcongr
      exact Set.sdiff_subset
    _ = total / 2 := by
      rw [Real.volume_Ico]
      have hlength : left + side - left = side := by ring
      rw [hlength]
      exact ENNReal.div_mul_cancel
        (ENNReal.ofReal_pos.mpr hside).ne'
        ENNReal.ofReal_ne_top
    _ = (∫⁻ z in Set.Ico left (left + side), m z) / 2 := rfl

/-- Threshold popularity retains at least half of the integral, not merely a
large set of heights. -/
theorem pureWZ2CommonBin_popularHeightMass_ge_half
    {m : ℝ → ENNReal} (hm : Measurable m)
    {left side : ℝ} (hside : 0 < side)
    (htotal : (∫⁻ z in Set.Ico left (left + side), m z) ≠ ⊤) :
    (∫⁻ z in Set.Ico left (left + side), m z) / 2 ≤
      ∫⁻ z in pureWZ2CommonBinPopularHeights m left side, m z := by
  let interval : Set ℝ := Set.Ico left (left + side)
  let popular : Set ℝ :=
    pureWZ2CommonBinPopularHeights m left side
  let low : Set ℝ := interval \ popular
  let total : ENNReal := ∫⁻ z in interval, m z
  let popularMass : ENNReal := ∫⁻ z in popular, m z
  let lowMass : ENNReal := ∫⁻ z in low, m z
  have hpopularMeas : MeasurableSet popular :=
    measurableSet_pureWZ2CommonBinPopularHeights hm left side
  have hpopularSubset : popular ⊆ interval := by
    intro z hz
    exact hz.1
  have hsum : popularMass + lowMass = total := by
    have hsplit :=
      lintegral_inter_add_sdiff (μ := (volume : Measure ℝ))
        m interval hpopularMeas
    have hinter : interval ∩ popular = popular :=
      Set.inter_eq_right.mpr hpopularSubset
    simpa [popularMass, lowMass, total, low, hinter] using hsplit
  have hlow : lowMass ≤ total / 2 := by
    simpa [lowMass, total, low, interval, popular] using
      pureWZ2CommonBin_lowHeightMass_le_half hm hside
  have hhalfTop : total / 2 ≠ ⊤ :=
    ENNReal.div_ne_top htotal (by norm_num)
  have hadd :
      total / 2 + total / 2 ≤ total / 2 + popularMass := by
    calc
      total / 2 + total / 2 = total := ENNReal.add_halves total
      _ = popularMass + lowMass := hsum.symm
      _ ≤ popularMass + total / 2 := by gcongr
      _ = total / 2 + popularMass := add_comm _ _
  exact (ENNReal.add_le_add_iff_left hhalfTop).mp hadd

/-- Genuine planar-slice area is a measurable function of height.  This
public lemma complements the existing Fubini identity for
`wz1Lemma23PlanarSlice`. -/
theorem measurable_volume_wz1Lemma23PlanarSlice
    (E : Set Point3) (hE : MeasurableSet E) :
    Measurable (fun z : ℝ => volume (wz1Lemma23PlanarSlice E z)) := by
  let coordinateSet : Set (ℝ × (Fin 2 → ℝ)) :=
    {p | point3 (p.2 0) (p.2 1) p.1 ∈ E}
  have hcoordinateSet : MeasurableSet coordinateSet := by
    apply hE.preimage
    apply Continuous.measurable
    unfold point3
    fun_prop
  let toPoint2 : (Fin 2 → ℝ) ≃ᵐ Point2 :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toHomeomorph.toMeasurableEquiv
  have htoPoint2 :
      MeasurePreserving toPoint2 volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 2)
  have hsection :
      ∀ z : ℝ,
        volume (Prod.mk z ⁻¹' coordinateSet) =
          volume (wz1Lemma23PlanarSlice E z) := by
    intro z
    let fiber : Set (Fin 2 → ℝ) := Prod.mk z ⁻¹' coordinateSet
    have himage :
        toPoint2 '' fiber = wz1Lemma23PlanarSlice E z := by
      ext point
      rw [wz1Lemma23_mem_planarSlice_iff]
      constructor
      · rintro ⟨coordinates, hcoordinates, rfl⟩
        simpa [fiber, coordinateSet, toPoint2] using hcoordinates
      · intro hpoint
        refine ⟨toPoint2.symm point, ?_, by simp⟩
        simpa [fiber, coordinateSet, toPoint2] using hpoint
    have hpreimage :
        toPoint2 ⁻¹' (toPoint2 '' fiber) = fiber :=
      Set.preimage_image_eq fiber toPoint2.injective
    have hvolume := htoPoint2.measure_preimage_emb
      toPoint2.measurableEmbedding (toPoint2 '' fiber)
    rw [hpreimage, himage] at hvolume
    exact hvolume
  have hcoordinateMeasurable :
      Measurable (fun z : ℝ => volume (Prod.mk z ⁻¹' coordinateSet)) :=
    measurable_measure_prodMk_left hcoordinateSet
  convert hcoordinateMeasurable using 1
  funext z
  exact (hsection z).symm

/-- The planar slice mass used by the common-bin construction. -/
def pureWZ2SourceCommonBinSliceMass
    (E : Set Point3) (z : ℝ) : ENNReal :=
  volume (wz1Lemma23PlanarSlice E z)

/-- The source-slab threshold `m_*`. -/
def pureWZ2SourceCommonBinPopularThreshold
    (E : Set Point3) (side : ℝ) : ENNReal :=
  pureWZ2CommonBinPopularThreshold (volume E) side

/-- The source-slab popular height set `Z_S`. -/
def pureWZ2SourceCommonBinPopularHeights
    (E : Set Point3) (left side : ℝ) : Set ℝ :=
  Set.Ico left (left + side) ∩
    {z | pureWZ2SourceCommonBinPopularThreshold E side ≤
      pureWZ2SourceCommonBinSliceMass E z}

theorem measurableSet_pureWZ2SourceCommonBinPopularHeights
    (E : Set Point3) (hE : MeasurableSet E) (left side : ℝ) :
    MeasurableSet
      (pureWZ2SourceCommonBinPopularHeights E left side) := by
  exact measurableSet_Ico.inter <|
    measurableSet_le measurable_const <|
      measurable_volume_wz1Lemma23PlanarSlice E hE

theorem pureWZ2SourceCommonBinPopularThreshold_eq
    (E : Set Point3) (side : ℝ) :
    pureWZ2SourceCommonBinPopularThreshold E side =
      volume E / (2 * ENNReal.ofReal side) := by
  exact pureWZ2CommonBinPopularThreshold_eq (volume E) side

/-- Construction-independent planar-slice form of the half-mass threshold
lemma. -/
theorem pureWZ2SourceCommonBinPopularHalfMass
    (E : Set Point3) (hE : MeasurableSet E)
    (hE_finite : volume E ≠ ⊤)
    {left side : ℝ} (hside : 0 < side)
    (hheight : ∀ point ∈ E,
      point (2 : Fin 3) ∈ Set.Ico left (left + side)) :
    volume E / 2 ≤
      ∫⁻ z in pureWZ2SourceCommonBinPopularHeights E left side,
        pureWZ2SourceCommonBinSliceMass E z := by
  let m : ℝ → ENNReal := pureWZ2SourceCommonBinSliceMass E
  have hm : Measurable m := by
    exact measurable_volume_wz1Lemma23PlanarSlice E hE
  have hout :
      ∀ z ∉ Set.Ico left (left + side), m z = 0 := by
    intro z hz
    have hempty : wz1Lemma23PlanarSlice E z = ∅ := by
      ext point
      simp only [Set.notMem_empty, iff_false]
      rw [wz1Lemma23_mem_planarSlice_iff]
      intro hpoint
      exact hz (by simpa [point3] using hheight _ hpoint)
    simp [m, pureWZ2SourceCommonBinSliceMass, hempty]
  have htotal :
      volume E =
        ∫⁻ z in Set.Ico left (left + side), m z := by
    rw [wz1_lemma23_volume_eq_lintegral_planarSlice E hE]
    change (∫⁻ z : ℝ, m z) =
      ∫⁻ z in Set.Ico left (left + side), m z
    rw [← lintegral_indicator measurableSet_Ico]
    apply lintegral_congr
    intro z
    by_cases hz : z ∈ Set.Ico left (left + side)
    · simp [hz]
    · simp [hz, hout z hz]
  have htotalFinite :
      (∫⁻ z in Set.Ico left (left + side), m z) ≠ ⊤ := by
    rw [← htotal]
    exact hE_finite
  have hpopular :=
    pureWZ2CommonBin_popularHeightMass_ge_half hm hside htotalFinite
  have hpopularSet :
      pureWZ2CommonBinPopularHeights m left side =
        pureWZ2SourceCommonBinPopularHeights E left side := by
    ext z
    simp only [pureWZ2CommonBinPopularHeights,
      pureWZ2SourceCommonBinPopularHeights, m]
    rw [← htotal]
    rfl
  rw [← htotal, hpopularSet] at hpopular
  exact hpopular

/-- A balanced safe source window lies in its literal side-`sqrt rho`
height slab, rather than merely having its snapped cell centers there. -/
theorem PureWZ2BalancedSafeWindowData.union_height_mem_source_slab
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {left : ℝ}
    (data : PureWZ2BalancedSafeWindowData prepared left) :
    ∀ point ∈ data.shading.union,
      point (2 : Fin 3) ∈ Set.Ico left (left + Real.sqrt rho) := by
  intro point hpoint
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  rw [data.union_eq] at hpoint
  rw [data.region_eq] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint.2 with
    ⟨cell, hcell, hpointCell⟩
  have hcell' : cell ∈ data.cells := hcell
  rw [data.cells_eq] at hcell'
  have hsafe := (Finset.mem_filter.mp hcell').2
  rw [wz1PaperGridCube_eq_Ico hrho cell] at hpointCell
  have hcenter :
      pureWZ2PaperCellCenterHeight rho cell =
        (cell.2.2 : ℝ) * rho + rho / 2 := by
    simp [pureWZ2PaperCellCenterHeight]
    ring
  rw [hcenter] at hsafe
  constructor <;> linarith [hrho, hpointCell.2.2.2.2.1,
    hpointCell.2.2.2.2.2.le, hsafe.1, hsafe.2]

/-- Exact half-mass popular-height theorem on one balanced source slab. -/
theorem PureWZ2BalancedSafeWindowData.commonBinPopularHalfMass
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {left : ℝ}
    (data : PureWZ2BalancedSafeWindowData prepared left) :
    volume data.shading.union / 2 ≤
      ∫⁻ z in pureWZ2SourceCommonBinPopularHeights
          data.shading.union left (Real.sqrt rho),
        pureWZ2SourceCommonBinSliceMass data.shading.union z := by
  apply pureWZ2SourceCommonBinPopularHalfMass
      data.shading.union (measurableSet_shading_union data.shading)
  · rw [data.volume_eq]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      twoScale.coarse.balanced.cellMass_ne_top
  · exact Real.sqrt_pos.mpr <| by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.coarseGrains.extremal.delta_pos
  · exact data.union_height_mem_source_slab

/-- Source-heavy (regularized) block form used by the ordinary paper-order
common-bin construction.  Its conclusion retains half of the literal block
mass before any fixed-line or graph selection. -/
theorem PureWZ2BalancedSafeBlockFamilyData.regularizedBlock_commonBinPopularHalfMass
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
    (block : {block // block ∈
      pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}) :
    let slab := safe.blockWindow block.1
    volume slab.shading.union / 2 ≤
      ∫⁻ z in pureWZ2SourceCommonBinPopularHeights
          slab.shading.union
          (pureWZ2BalancedWindowPhaseLeftAt rho safe.phase block.1.1)
          (Real.sqrt rho),
        pureWZ2SourceCommonBinSliceMass slab.shading.union z := by
  dsimp only
  exact (safe.blockWindow block.1).commonBinPopularHalfMass

end Kakeya.Assouad
