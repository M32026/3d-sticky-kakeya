import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentLocalVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SubfamilyShadingExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyPBase
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CordobaSlabLower
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaProjectionCoveringGeometry

/-!
# Dependent HIGH covering bound for Proposition 6.3

This is the quantitative core of the non-endpoint HIGH branch in the paper's
Lemma 4.11.  The second Proposition 6.2 output is zero-extended to its actual
`rho`-family.  A Property-(P) refinement on that same shading supplies the
full-grain slab lower bound, while the dependent `tau`-cover supplies the
local total-volume upper bound.  The two estimates are combined on the same
set inside the same `3 * tau` ball.

No all-scale AD conclusion or Fubini good-line selection is asserted here.
Those are later steps of Lemma 4.11/4.12.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/-- Slab width produced by the incidence-aware Córdoba argument at coarse
scale `rho`, local radius `tau`, and the actual plane-map Lipschitz constant. -/
def proposition63DependentSlabWidth
    (rho tau incidenceBound : ℝ) (coefficient : NNReal) : ℝ :=
  (tau + 12 * rho) *
      (2 * incidenceBound + 3 * (coefficient : ℝ) * tau) + 24 * rho

/-- Zero-extend the dependent second cover's selected `rho`-tube shading back
to the exact normalized outer coarse family. -/
noncomputable def Proposition63DependentTwoLevelCoverData.ambientRefined
    {delta sigma outerLoss reentryLoss innerLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau) :
    WZ1PaperTubeShading reentry.normalization.croppedFamily :=
  extendShading data.inner.selected data.inner.refined

@[simp] theorem Proposition63DependentTwoLevelCoverData.ambientRefined_union
    {delta sigma outerLoss reentryLoss innerLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau) :
    data.ambientRefined.union = data.inner.refined.union :=
  extendShading_union data.inner.selected data.inner.refined

@[simp] theorem Proposition63DependentTwoLevelCoverData.ambientRefined_mass
    {delta sigma outerLoss reentryLoss innerLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau) :
    data.ambientRefined.mass = data.inner.refined.mass :=
  extendShading_mass data.inner.selected data.inner.refined

/-- Property (P) on the actual second-cover refinement retains half of that
refinement's mass.  The equality is the zero-extension identity, not an
unrelated-family comparison. -/
theorem Proposition63DependentTwoLevelCoverData.propertyThree_mass_from_inner
    {delta sigma outerLoss reentryLoss innerLoss epsilon₁ epsilon₃ : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃) :
    (1 / 2 : ENNReal) * data.inner.refined.mass ≤
      propP.propertyThree.mass := by
  simpa using propP.propertyThree_mass

/-- The Property-(P) shading retains a quantified fraction of the outer
coarse shading through the genuine dependent re-entry ledger. -/
theorem Proposition63DependentTwoLevelCoverData.propertyThree_mass_from_outer_coarse
    {delta sigma outerLoss reentryLoss innerLoss epsilon₁ epsilon₃ : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃) :
    (1 / 2 : ENNReal) *
        (wz2PaperPureRefinementFraction rho.1 innerLogExponent *
          (reentry.retentionFactor⁻¹ *
            outer.croppedCoarseShading.mass)) ≤
      propP.propertyThree.mass := by
  calc
    (1 / 2 : ENNReal) *
          (wz2PaperPureRefinementFraction rho.1 innerLogExponent *
            (reentry.retentionFactor⁻¹ *
              outer.croppedCoarseShading.mass)) ≤
        (1 / 2 : ENNReal) * data.inner.refined.mass := by
      gcongr
      exact data.inner_refined_mass_from_outer_coarse
    _ ≤ propP.propertyThree.mass :=
      data.propertyThree_mass_from_inner propP

/-- Córdoba projection covering from the exact local-volume input used in
the proof.  This separates the analytic Córdoba argument from the particular
producer of the local total-volume upper bound. -/
theorem pureWZ2_cordoba_projection_covering_of_local_volume
    {sigma L tau epsilon₁ epsilon₃ : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (propP : PureWZ2CordobaPropertyPData
      (sigma := sigma) (coarseShading := coarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ propP.propertyThree.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      ∀ hpoint : point ∈ propP.propertyOne.carrier index,
        |@Inner.inner ℝ Point3 _
          (coarse.tube index).direction (planeMap point)| ≤ incidenceBound)
    (q : Point3) (hq : q ∈ propP.propertyThree.union)
    (hLPos : 0 < L) (hLSmall : L ≤ 1 / 1000)
    (htauPos : 0 < tau) (hLTau : L ≤ tau)
    (htauSq : tau ^ 2 ≤ 4 * L) (htauOne : tau ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hLLog : L ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hpropertyThreeFull :
      ∀ index point, point ∈ propP.propertyThree.carrier index →
        Kakeya.realRpowENN L (2 + 2 * epsilon₁) *
            ENNReal.ofReal tau ≤
          volume (propP.propertyThree.carrier index ∩
            Metric.closedBall point tau))
    (haxis : 4 * (6 * L) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃)) ^ 2)
    (totalVolume : ℝ)
    (hTotal : volume (coarseShading.union ∩
        Metric.closedBall q (3 * tau)) ≤ ENNReal.ofReal totalVolume) :
    (↑(Metric.externalCoveringNumber (Real.toNNReal L)
      (scalarProjection (planeMap q)
        (propP.propertyThree.union ∩ Metric.closedBall q tau))) :
        ENNReal) ≤
      ENNReal.ofReal
        ((totalVolume /
            (Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200)) *
          (2 * proposition63DependentSlabWidth L tau incidenceBound
            coefficient / L + 2)) := by
  let E := scalarProjection (planeMap q)
    (propP.propertyThree.union ∩ Metric.closedBall q tau)
  let S := coarseShading.union ∩ Metric.closedBall q (3 * tau)
  let proj : Point3 → ℝ := fun point =>
    @Inner.inner ℝ Point3 _ point (planeMap q)
  let W : ℝ := proposition63DependentSlabWidth L tau incidenceBound
    coefficient
  let Vmin : ℝ :=
    Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200
  have hincidenceNonnegative : 0 ≤ incidenceBound := by
    rcases hq with ⟨index, hpoint⟩
    exact (abs_nonneg _).trans <|
      hplaneIncidence index q (propP.propertyThree_sub index hpoint)
  have hWPos : 0 < W := by
    have hfirst : 0 ≤
        (tau + 12 * L) *
          (2 * incidenceBound + 3 * (coefficient : ℝ) * tau) := by
      positivity
    dsimp only [W, proposition63DependentSlabWidth]
    nlinarith
  have hVminPos : 0 < Vmin := by
    dsimp only [Vmin]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hLPos _) (sq_pos_of_pos htauPos))
      (by norm_num)
  have hSMeasurable : MeasurableSet S :=
    (measurableSet_shading_union coarseShading).inter
      Metric.isClosed_closedBall.measurableSet
  have hprojMeasurable : Measurable proj := by fun_prop
  have hEsub : E ⊆ proj '' S := by
    rintro value ⟨point, hpoint, rfl⟩
    refine ⟨point, ?_, by simp [proj]⟩
    refine ⟨?_, show dist point q ≤ 3 * tau from ?_⟩
    · rcases hpoint.1 with ⟨index, hindex⟩
      exact ⟨index, propP.propertyOne_sub index
        (propP.propertyThree_sub index hindex)⟩
    · calc
        dist point q ≤ tau := hpoint.2
        _ ≤ 3 * tau := by nlinarith
  have hSlab : ∀ level ∈ E,
      volume (S ∩ {point | |proj point - level| ≤ W}) ≥
        ENNReal.ofReal Vmin := by
    intro level hlevel
    let restrictedPlaneMap :
        {point : Point3 // point ∈ propP.propertyThree.union} → Point3 :=
      fun point => planeMap point
    have hrestrictedUnit : ∀ point, ‖restrictedPlaneMap point‖ = 1 := by
      intro point
      exact hplaneUnit point point.prop
    have hrestrictedLipschitz :
        LipschitzWith coefficient restrictedPlaneMap := by
      intro first second
      exact hplaneLipschitz first.val second.val
    have hraw := pureWz2_cordoba_slab_lower_with_hypotheses
      epsilon₁ epsilon₃ propP coefficient incidenceBound restrictedPlaneMap
      hrestrictedUnit hrestrictedLipschitz
      (fun index point _hpointUnion hpoint => by
        simpa only [restrictedPlaneMap] using
          hplaneIncidence index point hpoint)
      hpropertyThreeFull (hlog hepsilon₁ L hLPos hLLog) haxis
      hLPos hLSmall htauPos hLTau htauSq htauOne
      hsigma hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum q hq level hlevel
    change volume (S ∩ {point : Point3 |
        |proj point - level| ≤ W}) ≥
      Kakeya.realRpowENN L (1 + 7 * epsilon₁ + epsilon₃) *
        ENNReal.ofReal (tau ^ 2 / 200) at hraw
    have hbound :
        Kakeya.realRpowENN L (1 + 7 * epsilon₁ + epsilon₃) *
            ENNReal.ofReal (tau ^ 2 / 200) =
          ENNReal.ofReal Vmin := by
      have hpow : 0 ≤ Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) :=
        Real.rpow_nonneg hLPos.le _
      dsimp only [Vmin, Kakeya.realRpowENN]
      rw [← ENNReal.ofReal_mul hpow]
      congr 1
      ring
    rwa [hbound] at hraw
  have hDisjoint : ∀ first second, |first - second| > 2 * W →
      Disjoint {point : Point3 | |proj point - first| ≤ W}
        {point : Point3 | |proj point - second| ≤ W} := by
    intro first second hseparated
    rw [Set.disjoint_left]
    intro point hfirst hsecond
    change |proj point - first| ≤ W at hfirst
    change |proj point - second| ≤ W at hsecond
    have htriangle : |first - second| ≤
        |proj point - first| + |proj point - second| := by
      have heq : first - second =
          (proj point - second) - (proj point - first) := by ring
      rw [heq]
      linarith [abs_sub (proj point - second) (proj point - first)]
    exact (not_lt_of_ge (by linarith : |first - second| ≤ 2 * W))
      hseparated
  exact covering_number_from_slab_volumes_subset proj
    hLPos hWPos hVminPos hSMeasurable hprojMeasurable hEsub
    hSlab (by simpa only [S] using hTotal) hDisjoint

/-- Exact dependent Lemma 4.11 HIGH covering estimate.  The Córdoba lower
bound and the second cover's local-volume upper bound are both taken inside
`ambientRefined.union ∩ closedBall q (3 * tau)`. -/
theorem Proposition63DependentTwoLevelCoverData.inner_propertyThree_projection_covering
    {delta sigma outerLoss reentryLoss innerLoss epsilon₁ epsilon₃ : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau)
    (propP : PureWZ2CordobaPropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ propP.propertyThree.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      ∀ hpoint : point ∈ propP.propertyOne.carrier index,
        |@Inner.inner ℝ Point3 _
          (reentry.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (q : Point3) (hq : q ∈ propP.propertyThree.union)
    (htauSmall : tau.1 ≤ 1 / 12)
    (hrhoSmall : rho.1 ≤ 1 / 1000)
    (hrhoTau : rho.1 ≤ tau.1)
    (htauSq : tau.1 ^ 2 ≤ 4 * rho.1)
    (htauOne : tau.1 ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hpropertyThreeFull :
      ∀ index point, point ∈ propP.propertyThree.carrier index →
        Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
            ENNReal.ofReal tau.1 ≤
          volume (propP.propertyThree.carrier index ∩
            Metric.closedBall point tau.1))
    (haxis : 4 * (6 * rho.1) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2) :
    let projected := scalarProjection (planeMap q)
      (propP.propertyThree.union ∩ Metric.closedBall q tau.1)
    let totalVolume := 5832 *
      Real.rpow rho.1 (sigma - outerLoss) *
      Real.rpow tau.1 (3 - sigma - 2 * innerLoss)
    let slabVolume :=
      Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
        tau.1 ^ 2 / 200
    (↑(Metric.externalCoveringNumber (Real.toNNReal rho.1) projected) :
        ENNReal) ≤
      ENNReal.ofReal
        ((totalVolume / slabVolume) *
          (2 * proposition63DependentSlabWidth rho.1 tau.1 incidenceBound
            coefficient /
            rho.1 + 2)) := by
  dsimp only
  let source := data.ambientRefined
  let E := scalarProjection (planeMap q)
    (propP.propertyThree.union ∩ Metric.closedBall q tau.1)
  let S := source.union ∩ Metric.closedBall q (3 * tau.1)
  let proj : Point3 → ℝ := fun point =>
    @Inner.inner ℝ Point3 _ point (planeMap q)
  let W : ℝ := proposition63DependentSlabWidth rho.1 tau.1 incidenceBound
    coefficient
  let Vmin : ℝ :=
    Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
      tau.1 ^ 2 / 200
  let Vtotal : ℝ := 5832 *
    Real.rpow rho.1 (sigma - outerLoss) *
      Real.rpow tau.1 (3 - sigma - 2 * innerLoss)
  have hrhoPos : 0 < rho.1 :=
    reentry.normalization.final_extremal.delta_pos
  have htauPos : 0 < tau.1 := data.inner.coarse_extremal.delta_pos
  have hincidenceNonnegative : 0 ≤ incidenceBound := by
    rcases hq with ⟨index, hpoint⟩
    exact (abs_nonneg _).trans <|
      hplaneIncidence index q (propP.propertyThree_sub index hpoint)
  have hWPos : 0 < W := by
    have hfirst : 0 ≤
        (tau.1 + 12 * rho.1) *
          (2 * incidenceBound + 3 * (coefficient : ℝ) * tau.1) := by
      positivity
    dsimp only [W, proposition63DependentSlabWidth]
    nlinarith
  have hVminPos : 0 < Vmin := by
    dsimp only [Vmin]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hrhoPos _) (sq_pos_of_pos htauPos))
      (by norm_num)
  have hSMeasurable : MeasurableSet S :=
    (measurableSet_shading_union source).inter
      Metric.isClosed_closedBall.measurableSet
  have hprojMeasurable : Measurable proj := by
    fun_prop
  have hEsub : E ⊆ proj '' S := by
    rintro value ⟨point, hpoint, rfl⟩
    refine ⟨point, ?_, by simp [proj]⟩
    refine ⟨?_, show dist point q ≤ 3 * tau.1 from ?_⟩
    · rcases hpoint.1 with ⟨index, hindex⟩
      exact ⟨index, propP.propertyOne_sub index
        (propP.propertyThree_sub index hindex)⟩
    · calc
        dist point q ≤ tau.1 := hpoint.2
        _ ≤ 3 * tau.1 := by nlinarith [htauPos]
  have hSlab : ∀ level ∈ E,
      volume (S ∩ {point | |proj point - level| ≤ W}) ≥
        ENNReal.ofReal Vmin := by
    intro level hlevel
    let restrictedPlaneMap :
        {point : Point3 // point ∈ propP.propertyThree.union} → Point3 :=
      fun point => planeMap point
    have hrestrictedUnit : ∀ point, ‖restrictedPlaneMap point‖ = 1 := by
      intro point
      exact hplaneUnit point point.prop
    have hrestrictedLipschitz :
        LipschitzWith coefficient restrictedPlaneMap := by
      intro first second
      exact hplaneLipschitz first.val second.val
    have hraw := pureWz2_cordoba_slab_lower_with_hypotheses
      epsilon₁ epsilon₃ propP coefficient incidenceBound restrictedPlaneMap
      hrestrictedUnit
      hrestrictedLipschitz (fun index point _hpointUnion hpoint => by
        simpa only [restrictedPlaneMap] using
          hplaneIncidence index point hpoint)
      hpropertyThreeFull (hlog hepsilon₁ rho.1 hrhoPos hrhoLog) haxis
      hrhoPos hrhoSmall htauPos hrhoTau htauSq htauOne
      hsigma hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum q hq level hlevel
    change volume (S ∩ {point : Point3 |
        |proj point - level| ≤ W}) ≥
      Kakeya.realRpowENN rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
        ENNReal.ofReal (tau.1 ^ 2 / 200) at hraw
    have hbound :
        Kakeya.realRpowENN rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
            ENNReal.ofReal (tau.1 ^ 2 / 200) =
          ENNReal.ofReal Vmin := by
      have hpow :
          0 ≤ Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) :=
        Real.rpow_nonneg hrhoPos.le _
      have hquotient : 0 ≤ tau.1 ^ 2 / 200 := by positivity
      dsimp only [Vmin, Kakeya.realRpowENN]
      rw [← ENNReal.ofReal_mul hpow]
      congr 1
      ring
    rwa [hbound] at hraw
  have hVtotalPos : 0 < Vtotal := by
    dsimp only [Vtotal]
    exact mul_pos
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos hrhoPos _))
      (Real.rpow_pos_of_pos htauPos _)
  have hTotal : volume S ≤ ENNReal.ofReal Vtotal := by
    have hlocal := data.inner_three_tau_volume_upper htauSmall q
    have hset : S = data.inner.refined.union ∩
        Metric.closedBall q (3 * tau.1) := by
      dsimp only [S, source]
      rw [data.ambientRefined_union]
    rw [hset]
    apply hlocal.trans_eq
    have hrhoPower :
        0 ≤ Real.rpow rho.1 (sigma - outerLoss) :=
      Real.rpow_nonneg hrhoPos.le _
    have htauPower :
        0 ≤ Real.rpow tau.1 (3 - sigma - 2 * innerLoss) :=
      Real.rpow_nonneg htauPos.le _
    dsimp only [Vtotal, Kakeya.realRpowENN]
    rw [ENNReal.ofReal_mul (by positivity :
      0 ≤ 5832 * Real.rpow rho.1 (sigma - outerLoss))]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5832)]
    norm_num [mul_assoc]
  have hDisjoint : ∀ first second, |first - second| > 2 * W →
      Disjoint {point : Point3 | |proj point - first| ≤ W}
        {point : Point3 | |proj point - second| ≤ W} := by
    intro first second hseparated
    rw [Set.disjoint_left]
    intro point hfirst hsecond
    change |proj point - first| ≤ W at hfirst
    change |proj point - second| ≤ W at hsecond
    have htriangle : |first - second| ≤
        |proj point - first| + |proj point - second| := by
      have heq : first - second =
          (proj point - second) - (proj point - first) := by ring
      rw [heq]
      linarith [abs_sub (proj point - second) (proj point - first)]
    have hupper : |first - second| ≤ 2 * W := by linarith
    exact (not_lt_of_ge hupper) hseparated
  exact covering_number_from_slab_volumes_subset proj
    hrhoPos hWPos hVminPos hSMeasurable hprojMeasurable hEsub
    hSlab hTotal hDisjoint

/-- Arithmetic-facing form of the dependent HIGH bound.  Once the explicit
volume ratio is absorbed into the requested loss, the local Property-(P)
projection has the paper's one-scale covering estimate. -/
theorem Proposition63DependentTwoLevelCoverData.inner_propertyThree_projection_covering_of_arithmetic
    {delta sigma outerLoss reentryLoss innerLoss epsilon₁ epsilon₃ : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau)
    (propP : PureWZ2CordobaPropertyPData
      (sigma := sigma) (coarseShading := data.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ propP.propertyThree.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      ∀ hpoint : point ∈ propP.propertyOne.carrier index,
        |@Inner.inner ℝ Point3 _
          (reentry.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (q : Point3) (hq : q ∈ propP.propertyThree.union)
    (htauSmall : tau.1 ≤ 1 / 12)
    (hrhoSmall : rho.1 ≤ 1 / 1000)
    (hrhoTau : rho.1 ≤ tau.1)
    (htauSq : tau.1 ^ 2 ≤ 4 * rho.1)
    (htauOne : tau.1 ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hpropertyThreeFull :
      ∀ index point, point ∈ propP.propertyThree.carrier index →
        Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
            ENNReal.ofReal tau.1 ≤
          volume (propP.propertyThree.carrier index ∩
            Metric.closedBall point tau.1))
    (haxis : 4 * (6 * rho.1) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          (((5832 * Real.rpow rho.1 (sigma - outerLoss) *
              Real.rpow tau.1 (3 - sigma - 2 * innerLoss)) /
              (Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
                tau.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth rho.1 tau.1 incidenceBound
              coefficient /
              rho.1 + 2)) ≤
        C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)) :
    (↑(Metric.externalCoveringNumber (Real.toNNReal rho.1)
      (scalarProjection (planeMap q)
        (propP.propertyThree.union ∩ Metric.closedBall q tau.1))) :
        ENNReal) ≤
      C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma) := by
  exact (data.inner_propertyThree_projection_covering propP planeMap
    incidenceBound
    hplaneUnit hplaneLipschitz hplaneIncidence q hq
    htauSmall hrhoSmall hrhoTau htauSq htauOne hsigma
    hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hrhoLog hlog
    hpropertyThreeFull haxis).trans harithmetic

end Kakeya.Assouad.PureWZ2

end
