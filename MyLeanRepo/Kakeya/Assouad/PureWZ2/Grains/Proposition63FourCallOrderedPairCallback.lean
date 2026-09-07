import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63AlignedInnerIntervalGrid
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairActual

/-!
# Index-owned scales for the Proposition 6.3 ordered-pair callback

This module packages the scale data which the M5 callback can derive from its
ordered-pair index.  In particular, the aligned lower scale is constructed
from the frozen inner grid rather than accepted as callback-local geometric
data.  The interval scale is the second coordinate of the same ordered pair.

The package deliberately does not contain the prefix mass ledger.  That ledger
is an input to the iterator only and has no role in any geometric construction.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Scalar core of the global-smallness argument used by every ordered pair. -/
theorem proposition63_aligned_lower_scale_le_interval_of_query_small
    {delta queryScale discreteLoss x rhoHat tau : ℝ}
    (hqueryPos : 0 < queryScale)
    (hx : 0 < x)
    (hxTop : x ≤ Real.sqrt queryScale)
    (hdeltaQuery : delta ≤ queryScale)
    (hqueryX : queryScale ≤ x)
    (hdiscreteLoss : 0 ≤ discreteLoss)
    (hquerySmall :
      2 * Real.rpow queryScale (discreteLoss / 2) ≤ 1)
    (hrhoHat : rhoHat < x + delta)
    (hpairLower : Real.rpow x (1 - discreteLoss) ≤ tau) :
    rhoHat ≤ tau := by
  have hqueryRpow : Real.rpow x discreteLoss ≤
      Real.rpow queryScale (discreteLoss / 2) := by
    calc
      Real.rpow x discreteLoss ≤
          Real.rpow (Real.sqrt queryScale) discreteLoss :=
        Real.rpow_le_rpow hx.le hxTop hdiscreteLoss
      _ = Real.rpow queryScale (discreteLoss / 2) := by
        rw [Real.sqrt_eq_rpow]
        calc
          Real.rpow (Real.rpow queryScale (1 / 2)) discreteLoss =
              Real.rpow queryScale ((1 / 2) * discreteLoss) :=
            (Real.rpow_mul hqueryPos.le (1 / 2) discreteLoss).symm
          _ = Real.rpow queryScale (discreteLoss / 2) := by ring_nf
  have hxSmall : 2 * Real.rpow x discreteLoss ≤ 1 :=
    (mul_le_mul_of_nonneg_left hqueryRpow (by norm_num)).trans hquerySmall
  have htwoX : 2 * x ≤ Real.rpow x (1 - discreteLoss) := by
    have hmul : (2 * x) * Real.rpow x discreteLoss ≤
        Real.rpow x (1 - discreteLoss) * Real.rpow x discreteLoss := by
      calc
        (2 * x) * Real.rpow x discreteLoss =
            x * (2 * Real.rpow x discreteLoss) := by ring
        _ ≤ x * 1 := mul_le_mul_of_nonneg_left hxSmall hx.le
        _ = Real.rpow x (1 - discreteLoss) *
            Real.rpow x discreteLoss := by
          calc
            x * 1 = Real.rpow x 1 := by simp
            _ = Real.rpow x ((1 - discreteLoss) + discreteLoss) := by
              congr 1
              ring
            _ = Real.rpow x (1 - discreteLoss) *
                Real.rpow x discreteLoss := Real.rpow_add hx _ _
    exact le_of_mul_le_mul_right hmul
      (Real.rpow_pos_of_pos hx discreteLoss)
  have hdeltaX : delta ≤ x := hdeltaQuery.trans hqueryX
  calc
    rhoHat ≤ x + delta := hrhoHat.le
    _ ≤ 2 * x := by linarith
    _ ≤ Real.rpow x (1 - discreteLoss) := htwoX
    _ ≤ tau := hpairLower

/-- All scale data for one valid ordered pair which follows from the frozen
inner grid, the pair index, and the single global query-scale smallness
receipt.  In particular, `rhoHat ≤ tau` is produced without a pair-local
spacing assumption. -/
structure Proposition63FourCallOrderedPairIndexScales
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (index : ℕ) where
  index_lt : index < (finiteIntervalOrderedPairs gridN).length
  first_lt_second :
    (finiteIntervalOrderedPair gridN index).1 <
      (finiteIntervalOrderedPair gridN index).2
  second_le_gridN : (finiteIntervalOrderedPair gridN index).2 ≤ gridN
  rhoHat : WZ2PaperRequestedScale delta
  scaleFactor : ℕ
  scaleFactor_pos : 0 < scaleFactor
  rhoHat_aligned : rhoHat.1 = (scaleFactor : ℝ) * delta
  logicalR_le_rhoHat :
    (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) ≤ rhoHat.1
  rhoHat_lt_logicalR_add_delta : rhoHat.1 <
    (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) + delta
  rhoHat_le_two_logicalR : rhoHat.1 ≤
    2 * (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
  tau : ℝ
  tau_eq : tau =
    (grid.scale (finiteIntervalOrderedPair gridN index).2 : ℝ)
  tau_pos : 0 < tau
  tau_le_one : tau ≤ 1
  pair_lower_window :
    Real.rpow
        (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
        (1 - discreteLoss) ≤ tau
  tau_le_sqrt_logicalR : tau ≤ Real.sqrt
    (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
  rhoHat_le_tau : rhoHat.1 ≤ tau

/-- Produce the complete index-owned part of the M5 scale package.  No current
shading, prefix ledger, plane map, or runtime-selected witness occurs in the
construction. -/
theorem Proposition63InnerIntervalGridData.orderedPairIndexScales
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN index : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (hdelta : 0 < delta)
    (hdiscreteLoss : 0 < discreteLoss)
    (hquerySmall :
      2 * Real.rpow queryScale (discreteLoss / 2) ≤ 1)
    (hdeltaQuery : delta ≤ queryScale)
    (hsqrtSmall : 2 * Real.sqrt queryScale ≤ 1)
    (hindex : index < (finiteIntervalOrderedPairs gridN).length) :
    Nonempty (Proposition63FourCallOrderedPairIndexScales grid index) := by
  have hpair := finiteIntervalOrderedPair_valid hindex
  have hk : (finiteIntervalOrderedPair gridN index).1 ≤ gridN :=
    hpair.1.le.trans hpair.2
  rcases grid.alignedScale_spec hdelta hdeltaQuery hsqrtSmall
      (finiteIntervalOrderedPair gridN index).1 hk with
    ⟨scaleFactor, hscaleFactor, hrhoAligned, hlogicalRho, hrhoAdd,
      hdeltaRho, hrhoOne⟩
  let rhoHat : WZ2PaperRequestedScale delta :=
    ⟨grid.alignedScale hdelta
        (finiteIntervalOrderedPair gridN index).1, hdeltaRho, hrhoOne⟩
  let tau : ℝ :=
    (grid.scale (finiteIntervalOrderedPair gridN index).2 : ℝ)
  have hlogicalPos : 0 <
      (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) :=
    grid.scale_pos _ hk
  have hlogicalTop :
      (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) ≤
        Real.sqrt queryScale := by
    rw [← grid.scale_top]
    have hmono : ∀ offset : ℕ,
        (finiteIntervalOrderedPair gridN index).1 + offset ≤ gridN →
        (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) ≤
          grid.scale ((finiteIntervalOrderedPair gridN index).1 + offset) := by
      intro offset
      induction offset with
      | zero => simp
      | succ offset ih =>
          intro hsum
          exact (ih (by omega)).trans (grid.scale_mono _ (by omega))
    simpa only [Nat.add_sub_of_le hk] using
      hmono (gridN - (finiteIntervalOrderedPair gridN index).1) (by omega)
  have hrhoTwo : (grid.alignedScale hdelta
        (finiteIntervalOrderedPair gridN index).1 : ℝ) ≤
      2 * (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) := by
    have hdeltaLogical : delta ≤
        (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) :=
      hdeltaQuery.trans (grid.query_le_scale _ hk)
    linarith
  have hpairWindow := grid.pair_window discreteLoss
    hdiscreteLoss (le_refl discreteLoss) index hindex
  exact ⟨{
    index_lt := hindex
    first_lt_second := hpair.1
    second_le_gridN := hpair.2
    rhoHat := rhoHat
    scaleFactor := scaleFactor
    scaleFactor_pos := hscaleFactor
    rhoHat_aligned := by
      change (grid.alignedScale hdelta
        (finiteIntervalOrderedPair gridN index).1 : ℝ) =
          (scaleFactor : ℝ) * delta
      exact hrhoAligned
    logicalR_le_rhoHat := hlogicalRho
    rhoHat_lt_logicalR_add_delta := hrhoAdd
    rhoHat_le_two_logicalR := hrhoTwo
    tau := tau
    tau_eq := rfl
    tau_pos := grid.scale_pos _ hpair.2
    tau_le_one := grid.scale_le_one _ hpair.2
    pair_lower_window := hpairWindow.1
    tau_le_sqrt_logicalR := hpairWindow.2
    rhoHat_le_tau :=
      proposition63_aligned_lower_scale_le_interval_of_query_small
        grid.query_pos hlogicalPos hlogicalTop
        hdeltaQuery (grid.query_le_scale _ hk) hdiscreteLoss.le hquerySmall
        hrhoAdd hpairWindow.1
  }⟩

/-- The exact one-pair transition type accepted by
`Proposition63InnerIntervalGridData.runIteration`.  The two ledger hypotheses
are intentionally arguments of the transition but are not available to any
frozen geometric package. -/
def Proposition63FourCallOrderedPairStep
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN : ℕ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (source : WZ1PaperTubeShading family)
    (planeMap : Point3 → Point3)
    (loss : ℕ → ℝ) (leftFactor rightFactor : ℕ → ENNReal) : Prop :=
  ∀ index : ℕ,
    index < (finiteIntervalOrderedPairs gridN).length →
    ∀ current : WZ1PaperTubeShading family,
      PaperIsSubshading current source →
      WZ1PaperIsCubicalShading current →
      (∀ point ∈ current.union,
        current.pointMultiplicity point = source.pointMultiplicity point) →
      WZ2PaperCroppedIsExtremal sigma (loss index) family current →
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-(loss index))) →
      (∏ prior ∈ Finset.range index, leftFactor prior) * source.mass ≤
        (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass →
      0 < current.mass →
      ∃ next : WZ1PaperTubeShading family,
        PaperIsSubshading next current ∧
        WZ1PaperIsCubicalShading next ∧
        (∀ point ∈ next.union,
          next.pointMultiplicity point = current.pointMultiplicity point) ∧
        WZ2PaperCroppedIsExtremal sigma (loss (index + 1)) family next ∧
        WZ2PaperConvexWolffBound family
          (Kakeya.realRpowENN delta (-(loss (index + 1)))) ∧
        PureWZ2IntervalCoveringAt next planeMap
          (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
          (grid.scale (finiteIntervalOrderedPair gridN index).1)
          (grid.scale (finiteIntervalOrderedPair gridN index).2)
          (proposition63FourCallOrderedPairConstant grid index) ∧
        leftFactor index * current.mass ≤ rightFactor index * next.mass

/-- Frozen index-local entrance to the four-call producer.  Its only
pair-specific geometric data is constructed by `orderedPairIndexScales`; in
particular, no current shading, extremality/CWA witness, runtime object, mass,
or prefix ledger can occur in this package. -/
structure Proposition63FourCallOrderedPairIndexFrozenAt
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (index : ℕ) where
  scales : Proposition63FourCallOrderedPairIndexScales grid index

/-- Construct the frozen pair entrance solely from global grid receipts and
the enumeration index. -/
theorem Proposition63InnerIntervalGridData.orderedPairIndexFrozenAt
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN index : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (hdelta : 0 < delta)
    (hdiscreteLoss : 0 < discreteLoss)
    (hquerySmall :
      2 * Real.rpow queryScale (discreteLoss / 2) ≤ 1)
    (hdeltaQuery : delta ≤ queryScale)
    (hsqrtSmall : 2 * Real.sqrt queryScale ≤ 1)
    (hindex : index < (finiteIntervalOrderedPairs gridN).length) :
    Nonempty (Proposition63FourCallOrderedPairIndexFrozenAt grid index) := by
  rcases grid.orderedPairIndexScales hdelta hdiscreteLoss hquerySmall
      hdeltaQuery hsqrtSmall hindex with ⟨scales⟩
  exact ⟨⟨scales⟩⟩

end Kakeya.Assouad.PureWZ2
