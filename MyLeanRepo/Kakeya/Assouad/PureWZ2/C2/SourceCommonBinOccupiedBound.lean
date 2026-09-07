import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalFixedLine

/-!
# Height-independent common-bin bounds on a source slice

Fix a reference height `zStar` and use the coordinate

`uStar(point) = point 0 + slope zStar * point 1`.

The corresponding side-`side` integer-bin lattice is independent of the
height `z` of the slice being counted.  When `|z - zStar| ≤ side`, the
one-Lipschitz slope and `|point 1| ≤ 1` move `uStar` by at most `side` from
the height-dependent AD coordinate `u_z`.  The existing perturbed AD-bin
bound then controls all occupied fixed bins.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The common-bin label based at one fixed reference height.  In particular,
the label contains no varying slice-height argument. -/
def pureWZ2FixedCommonBinLabel
    (slope : ℝ → ℝ) (referenceHeight side : ℝ) (point : Point3) : ℤ :=
  Int.floor
    (inner ℝ point (globalGrainDirection (slope referenceHeight)) / side)

/-- All occupied common bins of a set in the paper coordinate window.

Under the hypotheses of `pureWZ2_fixed_common_bin_mem`, every occupied label
lies in the displayed finite ambient range.  The filter therefore records
the literal occupied bins, rather than a choice of representatives. -/
def pureWZ2OccupiedCommonBins
    (E : Set Point3) (slope : ℝ → ℝ)
    (referenceHeight side : ℝ) : Finset ℤ := by
  classical
  exact
    (Finset.Icc
      (Int.floor ((-5 : ℝ) / side))
      (Int.floor ((5 : ℝ) / side))).filter fun bin =>
        ∃ point ∈ E,
          pureWZ2FixedCommonBinLabel slope referenceHeight side point = bin

private lemma pureWZ2_fixed_common_coordinate_close
    {side : ℝ} {E : Set Point3}
    (slope : ℝ → ℝ)
    (hslope : LipschitzOnWith 1 slope (Set.Icc (-1 : ℝ) 1))
    (z referenceHeight : ℝ)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : |z - referenceHeight| ≤ side)
    (hy : ∀ point ∈ E, |point (1 : Fin 3)| ≤ 1)
    {point : Point3} (hpoint : point ∈ E) :
    |inner ℝ point (globalGrainDirection (slope referenceHeight)) -
        inner ℝ point (globalGrainDirection (slope z))| ≤ side := by
  have hslopeClose :
      |slope referenceHeight - slope z| ≤ side := by
    have hlip := hslope.dist_le_mul referenceHeight hreference z hz
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    exact hlip.trans (by simpa [abs_sub_comm] using hheight)
  have hformula :
      inner ℝ point (globalGrainDirection (slope referenceHeight)) -
          inner ℝ point (globalGrainDirection (slope z)) =
        (slope referenceHeight - slope z) * point (1 : Fin 3) := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    ring
  rw [hformula, abs_mul]
  calc
    |slope referenceHeight - slope z| * |point (1 : Fin 3)|
        ≤ side * 1 :=
      mul_le_mul hslopeClose (hy point hpoint)
        (abs_nonneg _) (le_trans (abs_nonneg _) hslopeClose)
    _ = side := mul_one side

/-- Every fixed label occupied by `E` belongs to
`pureWZ2OccupiedCommonBins`.  Thus the finite definition does not discard any
occupied bin under the same assumptions used by the cardinality theorem. -/
theorem pureWZ2_fixed_common_bin_mem
    {side alpha : ℝ} (E : Set Point3)
    (slope : ℝ → ℝ)
    (hslope : LipschitzOnWith 1 slope (Set.Icc (-1 : ℝ) 1))
    (z referenceHeight : ℝ)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : |z - referenceHeight| ≤ side)
    (hy : ∀ point ∈ E, |point (1 : Fin 3)| ≤ 1)
    {C : ENNReal}
    (hAD : IsADSet1
      (scalarProjection (globalGrainDirection (slope z)) E)
      side alpha C)
    (hside_one : side ≤ 1)
    {point : Point3} (hpoint : point ∈ E) :
    pureWZ2FixedCommonBinLabel slope referenceHeight side point ∈
      pureWZ2OccupiedCommonBins E slope referenceHeight side := by
  classical
  have hside : 0 < side := hAD.1
  let sourceValue : ℝ :=
    inner ℝ point (globalGrainDirection (slope z))
  let targetValue : ℝ :=
    inner ℝ point (globalGrainDirection (slope referenceHeight))
  have hsourceMem :
      sourceValue ∈
        scalarProjection (globalGrainDirection (slope z)) E :=
    ⟨point, hpoint, rfl⟩
  have hsourceBounds : sourceValue ∈ Set.Icc (-4 : ℝ) 4 :=
    hAD.2.2.2.2.1 hsourceMem
  have hclose : |targetValue - sourceValue| ≤ side := by
    exact pureWZ2_fixed_common_coordinate_close
      slope hslope z referenceHeight hz hreference hheight hy hpoint
  have htargetBounds : targetValue ∈ Set.Icc (-5 : ℝ) 5 := by
    rcases abs_le.mp hclose with ⟨hlower, hupper⟩
    exact ⟨by
      dsimp only [targetValue, sourceValue] at *
      linarith [hsourceBounds.1, hside_one], by
      dsimp only [targetValue, sourceValue] at *
      linarith [hsourceBounds.2, hside_one]⟩
  rw [pureWZ2OccupiedCommonBins, Finset.mem_filter]
  refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ⟨point, hpoint, rfl⟩⟩
  · apply Int.floor_mono
    exact (div_le_div_iff_of_pos_right hside).2 htargetBounds.1
  · apply Int.floor_mono
    exact (div_le_div_iff_of_pos_right hside).2 htargetBounds.2

/-- Fixed common-bin occupied-count bound.

The set `E` may be a genuine horizontal slice.  The source AD coordinate is
evaluated at that slice's height `z`, while every target label uses the one
fixed `referenceHeight`.  The absolute constant `132` is the repository's
existing `4 * side` perturbation constant; here the actual perturbation is
only `side`. -/
theorem pureWZ2_fixed_common_bin_occupied_bound
    {side alpha : ℝ} (E : Set Point3)
    (slope : ℝ → ℝ)
    (hslope : LipschitzOnWith 1 slope (Set.Icc (-1 : ℝ) 1))
    (z referenceHeight : ℝ)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : |z - referenceHeight| ≤ side)
    (hy : ∀ point ∈ E, |point (1 : Fin 3)| ≤ 1)
    {C : ENNReal}
    (hAD : IsADSet1
      (scalarProjection (globalGrainDirection (slope z)) E)
      side alpha C)
    (hside_one : side ≤ 1) :
    ((pureWZ2OccupiedCommonBins
      E slope referenceHeight side).card : ENNReal) ≤
        132 * C * Kakeya.realRpowENN (1 / side) alpha := by
  classical
  let bins :=
    pureWZ2OccupiedCommonBins E slope referenceHeight side
  have hexists :
      ∀ bin ∈ bins,
        ∃ point ∈ E,
          pureWZ2FixedCommonBinLabel slope referenceHeight side point = bin := by
    intro bin hbin
    have hbin' :
        bin ∈ pureWZ2OccupiedCommonBins E slope referenceHeight side := by
      simpa [bins] using hbin
    rw [pureWZ2OccupiedCommonBins, Finset.mem_filter] at hbin'
    exact hbin'.2
  choose point hpointMem hpointLabel using hexists
  let pointOf : {bin // bin ∈ bins} → Point3 :=
    fun bin => point bin.1 bin.property
  let values : Finset ℝ :=
    bins.attach.image fun bin =>
      inner ℝ (pointOf bin)
        (globalGrainDirection (slope referenceHeight))
  have hclose :
      ∀ value ∈ values,
        ∃ sourceValue ∈
            scalarProjection (globalGrainDirection (slope z)) E,
          |value - sourceValue| ≤ 4 * side := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨bin, _hbinAttach, hvalueEq⟩
    let sourceValue : ℝ :=
      inner ℝ (pointOf bin) (globalGrainDirection (slope z))
    have hsourceMem :
        sourceValue ∈
          scalarProjection (globalGrainDirection (slope z)) E :=
      ⟨pointOf bin, hpointMem bin.1 bin.property, rfl⟩
    refine ⟨sourceValue, hsourceMem, ?_⟩
    rw [← hvalueEq]
    have hone :=
      pureWZ2_fixed_common_coordinate_close
        slope hslope z referenceHeight hz hreference hheight hy
        (hpointMem bin.1 bin.property)
    exact hone.trans (by
      have hside : 0 < side := hAD.1
      nlinarith)
  have hbins :
      wz1Lemma23ScalarBins side values = bins := by
    ext bin
    constructor
    · intro hbin
      rcases Finset.mem_image.mp hbin with
        ⟨value, hvalue, hvalueBin⟩
      rcases Finset.mem_image.mp hvalue with
        ⟨sourceBin, _hsourceBinAttach, hsourceValue⟩
      have hsourceLabel :
          Int.floor
              (inner ℝ (pointOf sourceBin)
                (globalGrainDirection (slope referenceHeight)) / side) =
            sourceBin.1 := by
        simpa [pureWZ2FixedCommonBinLabel] using
          hpointLabel sourceBin.1 sourceBin.property
      have hbinEq : bin = sourceBin.1 := by
        calc
          bin = Int.floor (value / side) := hvalueBin.symm
          _ = Int.floor
              (inner ℝ (pointOf sourceBin)
                (globalGrainDirection (slope referenceHeight)) / side) := by
                  rw [hsourceValue]
          _ = sourceBin.1 := hsourceLabel
      rw [hbinEq]
      exact sourceBin.property
    · intro hbin
      let sourceBin : {bin // bin ∈ bins} := ⟨bin, hbin⟩
      let value : ℝ :=
        inner ℝ (pointOf sourceBin)
          (globalGrainDirection (slope referenceHeight))
      have hvalue : value ∈ values := by
        exact Finset.mem_image.mpr
          ⟨sourceBin, by simp, rfl⟩
      refine Finset.mem_image.mpr ⟨value, hvalue, ?_⟩
      simpa [value, sourceBin, pureWZ2FixedCommonBinLabel] using
        hpointLabel bin hbin
  have hcount :=
    wz1_lemma23_perturbed_ad_bin_count
      side alpha C
      (scalarProjection (globalGrainDirection (slope z)) E)
      values hAD hside_one hclose
  simpa [bins, hbins] using hcount

namespace PureWZ2SourceHorizontalFixedLineData

/-- Literal common bins occupied by the current source-heavy horizontal
slice.  All labels use `referenceHeight`; no per-height bin lattice is
selected. -/
def occupiedCommonBins
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    (referenceHeight : ℝ) : Finset ℤ :=
  pureWZ2OccupiedCommonBins
    (horizontalSlice window.shading.union line.lineHeight)
    source.globalGrains.slope referenceHeight (Real.sqrt rho)

/-- The source-heavy slice occupies at most
`132 * C_AD * (1 / sqrt rho)^(1-sigma)` fixed common bins, with
`C_AD = 10 * delta^(-inputLoss)`. -/
theorem occupiedCommonBins_bound
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight :
      |line.lineHeight - referenceHeight| ≤ Real.sqrt rho) :
    ((line.occupiedCommonBins referenceHeight).card : ENNReal) ≤
      132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
        Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) := by
  have hrho_one : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hroot_pos : 0 < Real.sqrt rho :=
    Real.sqrt_pos.mpr line.rho_pos
  have hrho_root : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sq_sqrt line.rho_pos.le, Real.sqrt_nonneg rho]
  have hroot_one : Real.sqrt rho ≤ 1 :=
    Real.sqrt_le_one.mpr hrho_one
  let slice :=
    horizontalSlice window.shading.union line.lineHeight
  have hADrho :
      IsADSet1
        (scalarProjection
          (globalGrainDirection
            (source.globalGrains.slope line.lineHeight))
          slice)
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    apply (prepared.exactAD line.lineHeight line.lineHeight_mem).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact
      ⟨point,
        ⟨window.subshading.union_subset hpoint.1, hpoint.2⟩,
        rfl⟩
  have hADroot :
      IsADSet1
        (scalarProjection
          (globalGrainDirection
            (source.globalGrains.slope line.lineHeight))
          slice)
        (Real.sqrt rho) (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss)) :=
    hADrho.coarsen_scale hroot_pos hrho_root hroot_one
  have hy :
      ∀ point ∈ slice, |point (1 : Fin 3)| ≤ 1 := by
    intro point hpoint
    have hshadow : point ∈ prepared.shadow.union :=
      window.subshading.union_subset hpoint.1
    have hpullback : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hshadow
    have hsource : point ∈ source.shading.union :=
      pullback.subshading.union_subset hpullback
    have hbox := shading_union_subset_axisBox hsource
    simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
  simpa [occupiedCommonBins, slice] using
    pureWZ2_fixed_common_bin_occupied_bound
      slice source.globalGrains.slope
      source.globalGrains.slope_lipschitz
      line.lineHeight referenceHeight
      line.lineHeight_mem hreference hheight hy
      hADroot hroot_one

end PureWZ2SourceHorizontalFixedLineData

end Kakeya.Assouad
