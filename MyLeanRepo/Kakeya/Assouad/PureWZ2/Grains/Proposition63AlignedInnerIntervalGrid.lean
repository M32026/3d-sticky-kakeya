import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteIntervalCoveringIteration
import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes

/-!
# Integer-aligned surrogates for the inner interval grid

The geometric grid used by Lemma 4.11 consists of real powers and is not, in
general, aligned with the fine `delta` grid.  This file constructs the honest
upward-rounded surrogate of each grid scale and records the exact comparison
needed by the four-call runtime.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Upward rounding of an arbitrary positive scale to the fine integer grid. -/
structure Proposition63AlignedInnerScaleData (delta scale : ℝ) where
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  aligned : ℝ
  aligned_eq : aligned = (multiplicity : ℝ) * delta
  requested : WZ2PaperRequestedScale delta
  requested_eq : requested.1 = aligned
  scale_le : scale ≤ aligned
  aligned_lt_add : aligned < scale + delta

/-- Every inner-grid scale has an upward integer-grid surrogate.  The
`scale + delta ≤ 1` hypothesis is precisely what makes the rounded value a
legal requested scale; no false exact alignment of `scale` is assumed. -/
theorem proposition63_aligned_inner_scale
    {delta scale : ℝ}
    (hdelta : 0 < delta)
    (hdeltaScale : delta ≤ scale)
    (hscaleOne : scale + delta ≤ 1) :
    Nonempty (Proposition63AlignedInnerScaleData delta scale) := by
  let multiplicity : ℕ := Nat.ceil (scale / delta)
  have hscale : 0 < scale := hdelta.trans_le hdeltaScale
  have hmultiplicity : 0 < multiplicity := by
    dsimp only [multiplicity]
    exact Nat.ceil_pos.mpr (div_pos hscale hdelta)
  let aligned : ℝ := (multiplicity : ℝ) * delta
  have hceilLower : scale / delta ≤ (multiplicity : ℝ) := by
    dsimp only [multiplicity]
    exact Nat.le_ceil _
  have hscaleAligned : scale ≤ aligned := by
    dsimp only [aligned]
    have hscaled := mul_le_mul_of_nonneg_right hceilLower hdelta.le
    simpa [div_mul_cancel₀ scale hdelta.ne'] using hscaled
  have hceilUpper : (multiplicity : ℝ) < scale / delta + 1 := by
    dsimp only [multiplicity]
    exact Nat.ceil_lt_add_one (div_nonneg hscale.le hdelta.le)
  have halignedAdd : aligned < scale + delta := by
    dsimp only [aligned]
    have hscaled := mul_lt_mul_of_pos_right hceilUpper hdelta
    simpa [div_mul_cancel₀ scale hdelta.ne', add_mul] using hscaled
  have hdeltaAligned : delta ≤ aligned := hdeltaScale.trans hscaleAligned
  have halignedOne : aligned ≤ 1 := halignedAdd.le.trans hscaleOne
  let requested : WZ2PaperRequestedScale delta :=
    ⟨aligned, hdeltaAligned, halignedOne⟩
  exact ⟨{
    multiplicity := multiplicity
    multiplicity_pos := hmultiplicity
    aligned := aligned
    aligned_eq := rfl
    requested := requested
    requested_eq := rfl
    scale_le := hscaleAligned
    aligned_lt_add := halignedAdd
  }⟩

/-- In the small-scale regime used by Proposition 6.3, every coordinate of
the inner grid admits a legal aligned surrogate, uniformly in the index. -/
theorem Proposition63InnerIntervalGridData.alignedSurrogate
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (hdelta : 0 < delta)
    (hdeltaQuery : delta ≤ queryScale)
    (hsqrtSmall : 2 * Real.sqrt queryScale ≤ 1)
    (index : ℕ) (hindex : index ≤ gridN) :
    Nonempty (Proposition63AlignedInnerScaleData delta (grid.scale index)) := by
  apply proposition63_aligned_inner_scale hdelta
  · exact hdeltaQuery.trans (grid.query_le_scale index hindex)
  · have hscaleTop : (grid.scale index : ℝ) ≤ Real.sqrt queryScale := by
      rw [← grid.scale_top]
      have hmono : ∀ offset : ℕ, index + offset ≤ gridN →
          (grid.scale index : ℝ) ≤ grid.scale (index + offset) := by
        intro offset
        induction offset with
        | zero => simp
        | succ offset ih =>
            intro hsum
            exact (ih (by omega)).trans (grid.scale_mono (index + offset) (by omega))
      simpa only [Nat.add_sub_of_le hindex] using
        hmono (gridN - index) (by omega)
    have hdeltaSqrt : delta ≤ Real.sqrt queryScale := by
      exact (hdeltaQuery.trans (grid.query_le_scale gridN le_rfl)).trans_eq
        grid.scale_top
    linarith

/-- The canonical aligned scale attached to an inner-grid coordinate. -/
noncomputable def Proposition63InnerIntervalGridData.alignedScale
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (hdelta : 0 < delta)
    (index : ℕ) : NNReal :=
  ⟨(Nat.ceil ((grid.scale index : ℝ) / delta) : ℝ) * delta, by positivity⟩

/-- On its valid index range, the aligned scale is exactly the scale packaged
by `alignedSurrogate`. -/
theorem Proposition63InnerIntervalGridData.alignedScale_spec
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (hdelta : 0 < delta)
    (hdeltaQuery : delta ≤ queryScale)
    (hsqrtSmall : 2 * Real.sqrt queryScale ≤ 1)
    (index : ℕ) (hindex : index ≤ gridN) :
    ∃ K : ℕ, 0 < K ∧
      (grid.alignedScale hdelta index : ℝ) = (K : ℝ) * delta ∧
      (grid.scale index : ℝ) ≤ grid.alignedScale hdelta index ∧
      (grid.alignedScale hdelta index : ℝ) < (grid.scale index : ℝ) + delta ∧
      delta ≤ (grid.alignedScale hdelta index : ℝ) ∧
      (grid.alignedScale hdelta index : ℝ) ≤ 1 := by
  let K : ℕ := Nat.ceil ((grid.scale index : ℝ) / delta)
  have hscale : 0 < (grid.scale index : ℝ) := grid.scale_pos index hindex
  have hK : 0 < K := Nat.ceil_pos.mpr (div_pos hscale hdelta)
  have hlower : (grid.scale index : ℝ) ≤ (K : ℝ) * delta := by
    have hceil : (grid.scale index : ℝ) / delta ≤ (K : ℝ) := Nat.le_ceil _
    have hscaled := mul_le_mul_of_nonneg_right hceil hdelta.le
    simpa [div_mul_cancel₀ (grid.scale index : ℝ) hdelta.ne'] using hscaled
  have hupper : (K : ℝ) * delta < (grid.scale index : ℝ) + delta := by
    have hceil : (K : ℝ) < (grid.scale index : ℝ) / delta + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hscaled := mul_lt_mul_of_pos_right hceil hdelta
    simpa [div_mul_cancel₀ (grid.scale index : ℝ) hdelta.ne', add_mul] using hscaled
  have hdeltaAligned : delta ≤ (K : ℝ) * delta := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  have hscaleTop : (grid.scale index : ℝ) ≤ Real.sqrt queryScale := by
    have hmono : ∀ offset : ℕ, index + offset ≤ gridN →
        (grid.scale index : ℝ) ≤ grid.scale (index + offset) := by
      intro offset
      induction offset with
      | zero => simp
      | succ offset ih =>
          intro hsum
          exact (ih (by omega)).trans (grid.scale_mono (index + offset) (by omega))
    rw [← grid.scale_top]
    simpa only [Nat.add_sub_of_le hindex] using hmono (gridN - index) (by omega)
  have hdeltaSqrt : delta ≤ Real.sqrt queryScale := by
    calc
      delta ≤ queryScale := hdeltaQuery
      _ ≤ (grid.scale gridN : ℝ) := grid.query_le_scale gridN le_rfl
      _ = Real.sqrt queryScale := grid.scale_top
  have hsumOne : (grid.scale index : ℝ) + delta ≤ 1 := by
    linarith
  have halignedOne : (K : ℝ) * delta ≤ 1 := hupper.le.trans hsumOne
  refine ⟨K, hK, rfl, ?_, ?_, ?_, ?_⟩
  · change (grid.scale index : ℝ) ≤ (K : ℝ) * delta
    exact hlower
  · change (K : ℝ) * delta < (grid.scale index : ℝ) + delta
    exact hupper
  · change delta ≤ (K : ℝ) * delta
    exact hdeltaAligned
  · change (K : ℝ) * delta ≤ 1
    exact halignedOne

/-- Upward rounding preserves the order of the inner grid. -/
theorem Proposition63InnerIntervalGridData.alignedScale_mono
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (hdelta : 0 < delta)
    {first second : ℕ}
    (hfirstSecond : first ≤ second)
    (hsecond : second ≤ gridN) :
    grid.alignedScale hdelta first ≤ grid.alignedScale hdelta second := by
  have hscale : (grid.scale first : ℝ) ≤ grid.scale second := by
    have hmono : ∀ offset : ℕ, first + offset ≤ gridN →
        (grid.scale first : ℝ) ≤ grid.scale (first + offset) := by
      intro offset
      induction offset with
      | zero => simp
      | succ offset ih =>
          intro hsum
          exact (ih (by omega)).trans (grid.scale_mono (first + offset) (by omega))
    simpa only [Nat.add_sub_of_le hfirstSecond] using
      hmono (second - first) (by omega)
  change (Nat.ceil ((grid.scale first : ℝ) / delta) : ℝ) * delta ≤
    (Nat.ceil ((grid.scale second : ℝ) / delta) : ℝ) * delta
  gcongr

/-- Query and interval-window enlargement is harmless when the resolution is
kept fixed.  This isolates the transport supplied by set inclusion; changing
the resolution requires a separate one-dimensional covering refinement. -/
theorem pureWZ2IntervalCoveringAt_mono_query_window
    {delta smallQuery largeQuery : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {resolutionScale smallWindow largeWindow : NNReal}
    {constant : ENNReal}
    (hquery : smallQuery ≤ largeQuery)
    (hwindow : smallWindow ≤ largeWindow)
    (hcover : PureWZ2IntervalCoveringAt shading planeMap largeQuery
      resolutionScale largeWindow constant) :
    PureWZ2IntervalCoveringAt shading planeMap smallQuery
      resolutionScale smallWindow constant := by
  intro point center
  have hqueryBall : Metric.closedBall (point : Point3)
      (Real.sqrt smallQuery) ⊆
      Metric.closedBall (point : Point3) (Real.sqrt largeQuery) :=
    Metric.closedBall_subset_closedBall (Real.sqrt_le_sqrt hquery)
  have hwindowBall : Metric.closedBall center (smallWindow : ℝ) ⊆
      Metric.closedBall center (largeWindow : ℝ) :=
    Metric.closedBall_subset_closedBall (by exact_mod_cast hwindow)
  have hset :
      scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt smallQuery)) ∩
          Metric.closedBall center (smallWindow : ℝ) ⊆
        scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt largeQuery)) ∩
          Metric.closedBall center (largeWindow : ℝ) := by
    exact Set.inter_subset_inter
      (Set.image_mono (Set.inter_subset_inter_right _ hqueryBall))
      hwindowBall
  have hmono :
      (Metric.externalCoveringNumber resolutionScale
        (scalarProjection (planeMap point)
              (shading.union ∩ Metric.closedBall (point : Point3)
                (Real.sqrt smallQuery)) ∩
            Metric.closedBall center (smallWindow : ℝ)) : ENNReal) ≤
      (Metric.externalCoveringNumber resolutionScale
        (scalarProjection (planeMap point)
              (shading.union ∩ Metric.closedBall (point : Point3)
                (Real.sqrt largeQuery)) ∩
            Metric.closedBall center (largeWindow : ℝ)) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hset
  exact hmono.trans (hcover point center)

/-- A covering bound at a resolution between `r` and `2 * r` refines to
resolution `r` at the fixed one-dimensional doubling cost `2`. -/
theorem pureWZ2IntervalCoveringAt_refine_resolution_two
    {delta queryScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {r rHat windowScale : NNReal}
    {constant : ENNReal}
    (hr : 0 < r)
    (hr_le : r ≤ rHat)
    (hrHat_le : rHat ≤ 2 * r)
    (hcover : PureWZ2IntervalCoveringAt shading planeMap queryScale
      rHat windowScale constant) :
    PureWZ2IntervalCoveringAt shading planeMap queryScale
      r windowScale (2 * constant) := by
  intro point center
  let projectedSet : Set ℝ :=
    scalarProjection (planeMap point)
          (shading.union ∩ Metric.closedBall (point : Point3)
            (Real.sqrt queryScale)) ∩
        Metric.closedBall center (windowScale : ℝ)
  have hrHat : 0 < rHat := hr.trans_le hr_le
  have hhalf : 0 < rHat / 2 := div_pos hrHat (by norm_num)
  have hhalf_le : rHat / 2 ≤ r := by
    rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)]
    simpa [mul_comm] using hrHat_le
  have hanti :
      (Metric.externalCoveringNumber r projectedSet : ENNReal) ≤
        (Metric.externalCoveringNumber (rHat / 2) projectedSet : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_anti hhalf_le
  have hdoubling :
      (Metric.externalCoveringNumber (rHat / 2) projectedSet : ENNReal) ≤
        2 * (Metric.externalCoveringNumber rHat projectedSet : ENNReal) := by
    have h := TubesAndSlopes.real_covering_doubling
      (S := projectedSet) hhalf
    have hcast :
      (Metric.externalCoveringNumber (rHat / 2) projectedSet : ENNReal) ≤
        2 * (Metric.externalCoveringNumber (2 * (rHat / 2)) projectedSet : ENNReal) := by
      exact_mod_cast h
    have htwo : (2 : NNReal) * (rHat / 2) = rHat := by
      apply NNReal.coe_injective
      push_cast
      ring
    simpa only [htwo] using hcast
  change (Metric.externalCoveringNumber r projectedSet : ENNReal) ≤
    2 * constant
  have hconstant :
      2 * (Metric.externalCoveringNumber rHat projectedSet : ENNReal) ≤
        2 * constant := by
    gcongr
    exact hcover point center
  exact hanti.trans (hdoubling.trans hconstant)

/-- First shrink the query ball, then refine an aligned resolution back to
the original resolution.  The interval window is unchanged throughout. -/
theorem pureWZ2IntervalCoveringAt_mono_query_refine_resolution_two
    {delta smallQuery largeQuery : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {r rHat windowScale : NNReal}
    {constant : ENNReal}
    (hquery : smallQuery ≤ largeQuery)
    (hr : 0 < r)
    (hr_le : r ≤ rHat)
    (hrHat_le : rHat ≤ 2 * r)
    (hcover : PureWZ2IntervalCoveringAt shading planeMap largeQuery
      rHat windowScale constant) :
    PureWZ2IntervalCoveringAt shading planeMap smallQuery
      r windowScale (2 * constant) := by
  have hqueryCover := pureWZ2IntervalCoveringAt_mono_query_window
    hquery (le_refl windowScale) hcover
  exact pureWZ2IntervalCoveringAt_refine_resolution_two
    hr hr_le hrHat_le hqueryCover

/-- The upward-rounded grid scale can be used by an aligned-scale caller and
then transported back to the exact inner-grid resolution. -/
theorem Proposition63InnerIntervalGridData.coveringAt_of_alignedScale
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (hdelta : 0 < delta)
    (hdeltaQuery : delta ≤ queryScale)
    (hsqrtSmall : 2 * Real.sqrt queryScale ≤ 1)
    {smallQuery largeQuery : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {windowScale : NNReal}
    {constant : ENNReal}
    (index : ℕ) (hindex : index ≤ gridN)
    (hquery : smallQuery ≤ largeQuery)
    (hcover : PureWZ2IntervalCoveringAt shading planeMap largeQuery
      (grid.alignedScale hdelta index) windowScale constant) :
    PureWZ2IntervalCoveringAt shading planeMap smallQuery
      (grid.scale index) windowScale (2 * constant) := by
  rcases grid.alignedScale_spec hdelta hdeltaQuery hsqrtSmall index hindex with
    ⟨_, _, _, hscaleAligned, halignedAdd, _, _⟩
  have hresolution : grid.scale index ≤ grid.alignedScale hdelta index := by
    exact_mod_cast hscaleAligned
  have halignedTwoReal :
      (grid.alignedScale hdelta index : ℝ) ≤
        2 * (grid.scale index : ℝ) := by
    have hdeltaScale : delta ≤ (grid.scale index : ℝ) :=
      hdeltaQuery.trans (grid.query_le_scale index hindex)
    linarith
  have halignedTwo :
      grid.alignedScale hdelta index ≤ 2 * grid.scale index := by
    exact_mod_cast halignedTwoReal
  exact pureWZ2IntervalCoveringAt_mono_query_refine_resolution_two
    hquery (grid.scale_pos index hindex) hresolution halignedTwo hcover

end Kakeya.Assouad.PureWZ2
