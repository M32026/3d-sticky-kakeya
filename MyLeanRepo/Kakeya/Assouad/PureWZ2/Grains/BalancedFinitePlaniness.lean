import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighMultiplicityBalancedFiniteLipschitz
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakLipschitzPlaneMapRefinement

/-!
# Branch-independent balanced finite planiness data

Dense and sparse planiness use different geometric inputs and quantitative
losses.  Exact rebalancing only needs their common output: a genuine cubical
subshading, a weak plane map with a recorded finite Lipschitz coefficient, and
an explicit two-sided shaded-mass inequality.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The branch-independent data consumed after finite planiness. -/
structure BalancedFinitePlaninessData
    {delta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family) where
  incidence : ℝ
  leftFactor : ENNReal
  rightFactor : ENNReal
  leftFactor_pos : 0 < leftFactor
  leftFactor_ne_top : leftFactor ≠ ⊤
  rightFactor_ne_top : rightFactor ≠ ⊤
  refinement : QuantitativeWeakLipschitzPlaneMapRefinement source incidence
    (Real.toNNReal coefficient) leftFactor rightFactor

/-- Finite planiness together with the branch-independent incidence budget
needed by coarse source-witness sampling. -/
structure BoundedBalancedFinitePlaninessData
    {delta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family) (incidenceBudget : ℝ) where
  data : BalancedFinitePlaninessData (coefficient := coefficient) source
  incidence_le : data.incidence ≤ incidenceBudget

/-- The one-sided mass-loss constant extracted from the two-sided finite
planiness mass account.  The added `1` keeps the constant positive even when
the recorded right factor vanishes. -/
def BalancedFinitePlaninessData.massLoss
    {delta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (data : BalancedFinitePlaninessData
      (coefficient := coefficient) source) : ENNReal :=
  1 + data.leftFactor⁻¹ * data.rightFactor

lemma BalancedFinitePlaninessData.massLoss_pos
    {delta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (data : BalancedFinitePlaninessData
      (coefficient := coefficient) source) :
    0 < data.massLoss := by
  exact zero_lt_one.trans_le (le_add_right le_rfl)

lemma BalancedFinitePlaninessData.massLoss_ne_top
    {delta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (data : BalancedFinitePlaninessData
      (coefficient := coefficient) source) :
    data.massLoss ≠ ⊤ := by
  rw [BalancedFinitePlaninessData.massLoss, ENNReal.add_ne_top]
  constructor
  · norm_num
  · exact ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr data.leftFactor_pos.ne')
      data.rightFactor_ne_top

/-- Normalize the finite-planiness mass certificate into the form consumed
by cropped-extremality transfer. -/
lemma BalancedFinitePlaninessData.massLoss_inv_mul_source_mass_le
    {delta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (data : BalancedFinitePlaninessData
      (coefficient := coefficient) source) :
    data.massLoss⁻¹ * source.mass ≤ data.refinement.shading.mass := by
  apply (ENNReal.inv_mul_le_iff data.massLoss_pos.ne'
    data.massLoss_ne_top).2
  calc
    source.mass = data.leftFactor⁻¹ *
        (data.leftFactor * source.mass) := by
      rw [ENNReal.inv_mul_cancel_left data.leftFactor_pos.ne'
        data.leftFactor_ne_top]
    _ ≤ data.leftFactor⁻¹ *
        (data.rightFactor * data.refinement.shading.mass) := by
      exact mul_le_mul_left' data.refinement.mass_retention _
    _ = (data.leftFactor⁻¹ * data.rightFactor) *
        data.refinement.shading.mass := by ring
    _ ≤ data.massLoss * data.refinement.shading.mass := by
      gcongr
      exact le_add_left le_rfl

/-- Rebase finite planiness across a quantitatively retained subshading.

This is the bookkeeping operation needed for non-commensurable scales: first
delete boundary-crossing whole fine cells, run finite planiness there, and
then record the same final shading as a refinement of the pre-pruning source.
No plane map or final carrier is changed. -/
def BalancedFinitePlaninessData.rebaseOfRetained
    {delta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source selected : WZ1PaperTubeShading family}
    (data : BalancedFinitePlaninessData
      (coefficient := coefficient) selected)
    (hsub : PaperIsSubshading selected source)
    (retainedFactor : ENNReal)
    (hretainedFactorPos : 0 < retainedFactor)
    (hretainedFactorTop : retainedFactor ≠ ⊤)
    (hretained : retainedFactor * source.mass ≤ selected.mass) :
    BalancedFinitePlaninessData
      (coefficient := coefficient) source where
  incidence := data.incidence
  leftFactor := retainedFactor * data.leftFactor
  rightFactor := data.rightFactor
  leftFactor_pos :=
    ENNReal.mul_pos hretainedFactorPos.ne' data.leftFactor_pos.ne'
  leftFactor_ne_top :=
    ENNReal.mul_ne_top hretainedFactorTop data.leftFactor_ne_top
  rightFactor_ne_top := data.rightFactor_ne_top
  refinement :=
    { shading := data.refinement.shading
      subshading := fun index =>
        (data.refinement.subshading index).trans (hsub index)
      cubical := data.refinement.cubical
      planeMap := data.refinement.planeMap
      planeMap_cellwise := data.refinement.planeMap_cellwise
      lipschitz := data.refinement.lipschitz
      mass_retention := by
        calc
          (retainedFactor * data.leftFactor) * source.mass =
              data.leftFactor * (retainedFactor * source.mass) := by ring
          _ ≤ data.leftFactor * selected.mass := by gcongr
          _ ≤ data.rightFactor * data.refinement.shading.mass :=
            data.refinement.mass_retention }

/-- The bounded incidence budget is unchanged by quantitative rebasing. -/
def BoundedBalancedFinitePlaninessData.rebaseOfRetained
    {delta coefficient incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source selected : WZ1PaperTubeShading family}
    (data : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) selected incidenceBudget)
    (hsub : PaperIsSubshading selected source)
    (retainedFactor : ENNReal)
    (hretainedFactorPos : 0 < retainedFactor)
    (hretainedFactorTop : retainedFactor ≠ ⊤)
    (hretained : retainedFactor * source.mass ≤ selected.mass) :
    BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) source incidenceBudget where
  data := data.data.rebaseOfRetained hsub retainedFactor
    hretainedFactorPos hretainedFactorTop hretained
  incidence_le := data.incidence_le

/-- Forget the dense/sparse formula after its quantitative values have been
recorded. -/
def HighMultiplicityBalancedFiniteLipschitzOutput.toPlaniness
    {delta sigma loss kappa eta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {nearbyConstant : ENNReal}
    {hcwa : WZ2PaperPureCWAAtNearbyScales family nearbyConstant}
    {N : ℕ}
    {requested : ℕ → WZ2PaperRequestedScale delta}
    {variationScale : ℕ → ℝ}
    (finite : HighMultiplicityBalancedFiniteLipschitzOutput
      (sigma := sigma) (loss := loss) (kappa := kappa) (eta := eta)
      (coefficient := coefficient) source hcwa N requested variationScale)
    (hdelta : 0 < delta) :
    BalancedFinitePlaninessData (coefficient := coefficient) source where
  incidence := finite.incidence
  leftFactor := finite.leftFactor
  rightFactor := finite.rightFactor
  leftFactor_pos := finite.leftFactor_pos hdelta
  leftFactor_ne_top := finite.leftFactor_ne_top
  rightFactor_ne_top := finite.rightFactor_ne_top
  refinement := finite.refinement

/-- A finite planiness refinement of a zero-extension restricts back to the
selected fine family with exactly the same quantitative mass account. -/
def BalancedFinitePlaninessData.restrictZeroExtension
    {delta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {source : WZ1PaperTubeShading selected.family}
    (data : BalancedFinitePlaninessData (coefficient := coefficient)
      (extendShading selected source)) :
    BalancedFinitePlaninessData (coefficient := coefficient) source where
  incidence := data.incidence
  leftFactor := data.leftFactor
  rightFactor := data.rightFactor
  leftFactor_pos := data.leftFactor_pos
  leftFactor_ne_top := data.leftFactor_ne_top
  rightFactor_ne_top := data.rightFactor_ne_top
  refinement := data.refinement.restrictZeroExtension selected

/-- Incidence bounds are unchanged by restricting a zero-extension back to
its genuine selected tube family. -/
def BoundedBalancedFinitePlaninessData.restrictZeroExtension
    {delta coefficient incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {source : WZ1PaperTubeShading selected.family}
    (data : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) (extendShading selected source)
      incidenceBudget) :
    BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) source incidenceBudget where
  data := data.data.restrictZeroExtension selected
  incidence_le := data.incidence_le

end Kakeya.Assouad.PureWZ2

end
