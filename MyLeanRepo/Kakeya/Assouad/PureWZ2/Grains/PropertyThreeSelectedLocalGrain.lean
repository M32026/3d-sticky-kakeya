import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullbackAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SingleCriticalEveryScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AlignedCoarseScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RelaxedLocalGrainData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TransversePairPaper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinitePlaninessInitial
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SubfamilyShadingExtension

/-!
# Local grains on the genuine selected fine family

The ambient zero-extension is useful for extremality bookkeeping, but the
metric-fibre continuation must remain on the fine family selected by the
same Node 3 output.  This module places the finite plane map and every-scale
local AD estimate on a refinement of that genuine selected-family pullback.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- The same sticky/Property-Three loss used for the ambient common hull also
controls the genuine selected-family fine pullback, before zero-extension. -/
lemma propertyThreeFinePullback_massLoss_inv_mul_source_mass_le
    {delta sigma stickyLoss tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (hdelta : 0 < delta) :
    (propertyThreeCommonHullMassLoss sticky)⁻¹ * sourceShading.mass ≤
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree).mass := by
  have hretained : propertyThreeCommonHullRetainedFactor sticky *
      sourceShading.mass ≤
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree).mass := by
    let cap : ENNReal :=
      (2 * stickyCoarseMultiplicityCap sticky *
        stickyCoarseMultiplicityCap sticky *
        stickyFiberMultiplicityCap sticky)⁻¹
    calc
      propertyThreeCommonHullRetainedFactor sticky *
          sourceShading.mass =
        cap * (wz2PaperPureRefinementFraction delta logExponent *
          sourceShading.mass) := by
            simp [propertyThreeCommonHullRetainedFactor, cap]
            ring
      _ ≤ cap * sticky.refined.mass := by
        exact mul_le_mul_left' sticky.retained_mass cap
      _ ≤ (propertyThreeFinePullbackShading
          sticky.cover sticky.refined propP.propertyThree).mass := by
        simpa [cap] using
          propertyThreeFinePullback_mass_lower_of_sticky
            sticky propP.propertyThree hdelta
            (fun index => (propP.propertyThree_sub index).trans
              (propP.propertyOne_sub index))
            propP.propertyThree_cubical propP.propertyThree_mass
  have hinvLe : (propertyThreeCommonHullMassLoss sticky)⁻¹ ≤
      propertyThreeCommonHullRetainedFactor sticky := by
    rw [ENNReal.inv_le_iff_inv_le]
    exact le_add_left le_rfl
  exact (mul_le_mul_right' hinvLe sourceShading.mass).trans hretained

/-- The first-half local-grain package before the final mild rescaling.  Its
incidence scale is the one actually produced by the dense/sparse planiness
dichotomy; it is not prematurely identified with the fine tube scale. -/
structure Proposition63InitialWeakLocalGrainData
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (sigma : ℝ) (C : ENNReal) (L : NNReal) where
  planeMap : {point : Point3 // point ∈ shading.union} → Point3
  planeMap_lipschitz : LipschitzWith L planeMap
  planeMap_unit : ∀ point, ‖planeMap point‖ = 1
  planeMap_incidence : ∀ index point,
    ∀ hpoint : point ∈ shading.carrier index,
      |inner ℝ (family.tube index).direction
        (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ incidence
  local_ad : ∀ queryScale : ℝ, delta ≤ queryScale → queryScale ≤ 1 →
    ∀ point : {point : Point3 // point ∈ shading.union},
      PureWZ2PaperADSet1
        (scalarProjection (planeMap point)
          (shading.union ∩ Metric.closedBall (point : Point3)
            (Real.sqrt queryScale)))
        queryScale (1 - sigma) C

namespace Proposition63InitialWeakLocalGrainData

/-- Regard a relaxed local-grain package as the weak package used before the
first Proposition 6.2 call. No estimate is changed. -/
noncomputable def ofRelaxed
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal} {L : NNReal}
    (data : PureWZ2RelaxedLocalGrainData shading sigma C L) :
    Proposition63InitialWeakLocalGrainData
      (incidence := delta) shading sigma C L where
  planeMap := data.planeMap
  planeMap_lipschitz := data.planeMap_lipschitz
  planeMap_unit := data.planeMap_unit
  planeMap_incidence := data.planeMap_incidence
  local_ad := data.local_ad

/-- Regard a strict local-grain package as the weak package used before the
first Proposition 6.2 call.  This changes no map or estimate; it only exposes
the incidence and Lipschitz constants as explicit parameters. -/
noncomputable def ofStrict
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2LocalGrainData shading sigma C) :
    Proposition63InitialWeakLocalGrainData
      (incidence := delta) shading sigma C 1 :=
  ofRelaxed
    { planeMap := data.planeMap
      planeMap_lipschitz := data.planeMap_lipschitz
      planeMap_unit := data.planeMap_unit
      planeMap_incidence := data.planeMap_incidence
      local_ad := data.local_ad }

/-- Enlarge only the recorded Lipschitz coefficient. -/
noncomputable def weakenLipschitz
    {delta incidence sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal} {sourceL targetL : NNReal}
    (data : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) shading sigma C sourceL)
    (hL : sourceL ≤ targetL) :
    Proposition63InitialWeakLocalGrainData
      (incidence := incidence) shading sigma C targetL where
  planeMap := data.planeMap
  planeMap_lipschitz := data.planeMap_lipschitz.weaken hL
  planeMap_unit := data.planeMap_unit
  planeMap_incidence := data.planeMap_incidence
  local_ad := data.local_ad

/-- Enlarge only the recorded incidence tolerance.  The plane map, its
Lipschitz certificate, and every local AD estimate are left definitionally
unchanged.  This is the bookkeeping step needed when the plane map was
constructed before a later finite-planiness refinement. -/
noncomputable def weakenIncidence
    {delta sourceIncidence targetIncidence sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal} {L : NNReal}
    (data : Proposition63InitialWeakLocalGrainData
      (incidence := sourceIncidence) shading sigma C L)
    (hincidence : sourceIncidence ≤ targetIncidence) :
    Proposition63InitialWeakLocalGrainData
      (incidence := targetIncidence) shading sigma C L where
  planeMap := data.planeMap
  planeMap_lipschitz := data.planeMap_lipschitz
  planeMap_unit := data.planeMap_unit
  planeMap_incidence := by
    intro index point hpoint
    exact (data.planeMap_incidence index point hpoint).trans hincidence
  local_ad := data.local_ad

/-- Enlarge the AD constant by spending a loss gap, without changing the
plane map, its Lipschitz constant, or its incidence tolerance. -/
noncomputable def weakenLoss
    {delta incidence sigma sourceLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {L : NNReal}
    (data : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) shading sigma
      (Kakeya.realRpowENN delta (-sourceLoss)) L)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hloss : sourceLoss ≤ targetLoss) :
    Proposition63InitialWeakLocalGrainData
      (incidence := incidence) shading sigma
      (Kakeya.realRpowENN delta (-targetLoss)) L where
  planeMap := data.planeMap
  planeMap_lipschitz := data.planeMap_lipschitz
  planeMap_unit := data.planeMap_unit
  planeMap_incidence := data.planeMap_incidence
  local_ad := by
    intro queryScale hdeltaQuery hqueryOne point
    apply (data.local_ad queryScale hdeltaQuery hqueryOne point).mono_const
    · apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
    · simp [Kakeya.realRpowENN]

/-- Restrict the genuine first-stage weak plane map and its local AD bounds
to a carrierwise subshading. -/
noncomputable def restrict
    {delta incidence sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source selected : WZ1PaperTubeShading family}
    {C : ENNReal} {L : NNReal}
    (data : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) source sigma C L)
    (hsub : PaperIsSubshading selected source) :
    Proposition63InitialWeakLocalGrainData
      (incidence := incidence) selected sigma C L := by
  have hunion : selected.union ⊆ source.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hsub index hpoint⟩
  let planeMap : {point : Point3 // point ∈ selected.union} → Point3 :=
    fun point => data.planeMap ⟨point, hunion point.prop⟩
  exact
    { planeMap := planeMap
      planeMap_lipschitz := by
        intro first second
        exact data.planeMap_lipschitz
          ⟨first, hunion first.prop⟩ ⟨second, hunion second.prop⟩
      planeMap_unit := fun point =>
        data.planeMap_unit ⟨point, hunion point.prop⟩
      planeMap_incidence := by
        intro index point hpoint
        exact data.planeMap_incidence index point (hsub index hpoint)
      local_ad := by
        intro queryScale hdeltaQuery hqueryOne point
        apply (data.local_ad queryScale hdeltaQuery hqueryOne
          ⟨point, hunion point.prop⟩).mono_set
        rintro value ⟨other, hother, rfl⟩
        exact ⟨other, ⟨hunion hother.1, hother.2⟩, rfl⟩ }

/-- Reindex the earlier local-grain package along a genuine tube subfamily.
The plane map and its AD estimates are restricted through the literal
subfamily embedding. -/
noncomputable def restrictSubfamily
    {delta incidence sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal} {L : NNReal}
    (data : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) source sigma C L)
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    Proposition63InitialWeakLocalGrainData
      (incidence := incidence)
      (restrictPaperShading selected source) sigma C L := by
  have hunion : (restrictPaperShading selected source).union ⊆
      source.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨selected.embedding index, hpoint⟩
  let planeMap :
      {point : Point3 //
        point ∈ (restrictPaperShading selected source).union} → Point3 :=
    fun point => data.planeMap ⟨point, hunion point.prop⟩
  exact
    { planeMap := planeMap
      planeMap_lipschitz := by
        intro first second
        exact data.planeMap_lipschitz
          ⟨first, hunion first.prop⟩ ⟨second, hunion second.prop⟩
      planeMap_unit := fun point =>
        data.planeMap_unit ⟨point, hunion point.prop⟩
      planeMap_incidence := by
        intro index point hpoint
        have hraw := data.planeMap_incidence
          (selected.embedding index) point hpoint
        simpa only [selected.tube_eq] using hraw
      local_ad := by
        intro queryScale hdeltaQuery hqueryOne point
        apply (data.local_ad queryScale hdeltaQuery hqueryOne
          ⟨point, hunion point.prop⟩).mono_set
        rintro value ⟨other, hother, rfl⟩
        exact ⟨other, ⟨hunion hother.1, hother.2⟩, rfl⟩ }

/-- Reindex preliminary weak local grains back to the ambient tube family by
empty carriers. The union and every local AD set are unchanged. -/
noncomputable def extendSubfamily
    {delta incidence sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {source : WZ1PaperTubeShading selected.family}
    {C : ENNReal} {L : NNReal}
    (data : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) source sigma C L) :
    Proposition63InitialWeakLocalGrainData
      (incidence := incidence) (extendShading selected source) sigma C L := by
  let hunion : (extendShading selected source).union = source.union :=
    extendShading_union selected source
  let planeMap :
      {point : Point3 // point ∈ (extendShading selected source).union} →
        Point3 :=
    fun point => data.planeMap ⟨point, hunion ▸ point.prop⟩
  exact
    { planeMap := planeMap
      planeMap_lipschitz := by
        intro first second
        exact data.planeMap_lipschitz
          ⟨first, hunion ▸ first.prop⟩ ⟨second, hunion ▸ second.prop⟩
      planeMap_unit := fun point =>
        data.planeMap_unit ⟨point, hunion ▸ point.prop⟩
      planeMap_incidence := by
        intro ambientIndex point hpoint
        by_cases himage : ∃ sourceIndex,
            selected.embedding sourceIndex = ambientIndex
        · rcases himage with ⟨sourceIndex, rfl⟩
          rw [extendShading_carrier_mem] at hpoint
          simpa only [selected.tube_eq] using
            data.planeMap_incidence sourceIndex point hpoint
        · rw [extendShading_carrier_empty himage] at hpoint
          exact False.elim hpoint
      local_ad := by
        intro queryScale hdeltaQuery hqueryOne point
        have hsource := data.local_ad queryScale hdeltaQuery hqueryOne
          ⟨point, hunion ▸ point.prop⟩
        simpa only [hunion] using hsource }

end Proposition63InitialWeakLocalGrainData

/-- One finite-planiness refinement on the genuine selected fine family,
carrying local AD on exactly the same shading. -/
structure PropertyThreeSelectedInitialLocalData
    {delta sigma outputLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading fine) where
  planiness : BalancedFinitePlaninessData
    (coefficient := coefficient) source
  planiness_mass_pos : 0 < planiness.refinement.shading.mass
  /-- A common incidence budget for the earlier local-grain map and the
  later finite-planiness map. -/
  incidence : ℝ
  planiness_incidence_le : planiness.incidence ≤ incidence
  incidence_nonnegative : 0 ≤ incidence
  localGrains : Proposition63InitialWeakLocalGrainData
    (incidence := incidence) planiness.refinement.shading sigma
    (Kakeya.realRpowENN delta (-outputLoss)) (Real.toNNReal coefficient)

/-- A positive final planiness shading forces its incidence tolerance to be
nonnegative, since some retained point has a nonnegative absolute inner
product bounded by that tolerance. -/
lemma BalancedFinitePlaninessData.incidence_nonnegative_of_mass_pos
    {delta coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading fine}
    (planiness : BalancedFinitePlaninessData
      (coefficient := coefficient) source)
    (hmass : 0 < planiness.refinement.shading.mass) :
    0 ≤ planiness.incidence := by
  by_contra hnot
  have hnegative : planiness.incidence < 0 := lt_of_not_ge hnot
  have hunion : planiness.refinement.shading.union.Nonempty := by
    by_contra hempty
    have hunionEmpty : planiness.refinement.shading.union = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hempty
    have hcarrierEmpty : ∀ index,
        planiness.refinement.shading.carrier index = ∅ := by
      intro index
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hcarrier
      rcases hcarrier with ⟨point, hpoint⟩
      have : point ∈ planiness.refinement.shading.union := ⟨index, hpoint⟩
      rw [hunionEmpty] at this
      exact this
    have hmassZero : planiness.refinement.shading.mass = 0 := by
      change (∑ index,
        volume (planiness.refinement.shading.carrier index)) = 0
      simp [hcarrierEmpty]
    rw [hmassZero] at hmass
    exact (lt_irrefl 0) hmass
  rcases hunion with ⟨point, index, hpoint⟩
  have hinc := planiness.refinement.planeMap.incidence index point hpoint
  exact (not_le_of_gt hnegative) ((abs_nonneg _).trans hinc)

/-- Combine a finite-planiness refinement with local grains that were
constructed earlier in the paper.  The old local-grain plane map is merely
restricted to the final shading; the planiness map is retained separately in
`planiness.refinement.planeMap`.  The explicit incidence comparison is the
only bridge between their two budgets. -/
noncomputable def PropertyThreeSelectedInitialLocalData.ofPriorLocalGrains
    {delta sigma outputLoss coefficient sourceIncidence : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading fine}
    (planiness : BalancedFinitePlaninessData
      (coefficient := coefficient) source)
    (hplaninessMass : 0 < planiness.refinement.shading.mass)
    {priorShading : WZ1PaperTubeShading fine}
    {priorL : NNReal}
    (prior : Proposition63InitialWeakLocalGrainData
      (incidence := sourceIncidence) priorShading sigma
      (Kakeya.realRpowENN delta (-outputLoss))
      priorL)
    (hfinalPrior : PaperIsSubshading
      planiness.refinement.shading priorShading)
    (hpriorL : priorL ≤ Real.toNNReal coefficient)
    (commonIncidence : ℝ)
    (hpriorIncidence : sourceIncidence ≤ commonIncidence)
    (hplaninessIncidence : planiness.incidence ≤ commonIncidence)
    (hcommonIncidence : 0 ≤ commonIncidence) :
    PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := outputLoss)
      (coefficient := coefficient) source where
  planiness := planiness
  planiness_mass_pos := hplaninessMass
  incidence := commonIncidence
  planiness_incidence_le := hplaninessIncidence
  incidence_nonnegative := hcommonIncidence
  localGrains :=
    ((prior.restrict hfinalPrior).weakenLipschitz hpriorL).weakenIncidence
      hpriorIncidence

theorem propertyThree_selected_subshading_every_scale_relaxed_local_grain
    {delta incidence sigma stickyLoss sourceADLoss targetLoss tau epsilon₁
      epsilon₃ : ℝ}
    {L : NNReal}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    {final : WZ1PaperTubeShading sticky.selected.family}
    (planeMap : PaperWZ1WeakPlaneMapData final incidence)
    (hplaneLipschitz : LipschitzWith L
      (fun point : {point : Point3 // point ∈ final.union} =>
        planeMap.planeMap point))
    (hfinalSub : PaperIsSubshading final
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree))
    (hdelta : 0 < delta)
    (hdeltaOne : delta < 1)
    (htargetLoss : 0 < targetLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (htau_def : tau = rho.1 * Real.sqrt 3)
    (htau_pos : 0 < tau)
    (htau_le_20L : tau ≤ 20 * rho.1)
    (hL_le_tau : rho.1 ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * rho.1)
    (htau_le_one : tau ≤ 1)
    (hL_small : rho.1 ≤ 1 / 1000)
    (hL_pos : 0 < rho.1)
    (hL_half : rho.1 ≤ 1 / 2)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (heps₁_pos : 0 < epsilon₁)
    (heps₁_lt : epsilon₁ < 1 / 20)
    (heps₃_pos : 0 < epsilon₃)
    (heps₃_def : epsilon₃ = 1 - 2 * epsilon₁)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (L₀_log : ℝ)
    (hL_le_L0_log : rho.1 ≤ L₀_log)
    (h_log_main : 0 < epsilon₁ → ∀ L' : ℝ, 0 < L' → L' ≤ L₀_log →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ parent : Fin sticky.coarse.card, ∀ point : Point3,
        point ∈ propP.propertyThree.carrier parent →
          Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
              ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier parent ∩
              Metric.closedBall point tau))
    (h_ax_condition :
      4 * (6 * rho.1) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (hL_lower : Real.rpow delta stickyLoss ≤ rho.1)
    (hL_bound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyLoss_le_sourceAD : 3 * stickyLoss ≤ sourceADLoss)
    (hsmallCost :
      let criticalScale := 48 * rho.1 ^ 2
      let sourceConstant := Kakeya.realRpowENN delta (-sourceADLoss)
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * criticalScale / delta)) ≤
        Kakeya.realRpowENN delta (-targetLoss))
    (hlargeEndpoint :
      let criticalScale := 48 * rho.1 ^ 2
      3 * (2 / Real.sqrt criticalScale) ^ sigma ≤
        delta ^ (-targetLoss)) :
    Nonempty (Proposition63InitialWeakLocalGrainData
      (incidence := incidence) final sigma
      (Kakeya.realRpowENN delta (-targetLoss)) L) := by
  let finalPlaneMap : {point : Point3 // point ∈ final.union} → Point3 :=
    fun point => planeMap.planeMap point
  have hfinalUnit : ∀ point, ‖finalPlaneMap point‖ = 1 := by
    intro point
    exact planeMap.unit point point.prop
  let criticalScale : ℝ := 48 * rho.1 ^ 2
  let sourceConstant : ENNReal :=
    Kakeya.realRpowENN delta (-sourceADLoss)
  have hcriticalPos : 0 < criticalScale := by
    dsimp only [criticalScale]
    positivity
  have hcriticalOne : criticalScale ≤ 1 := by
    dsimp only [criticalScale]
    nlinarith [sq_nonneg (rho.1 : ℝ)]
  have hcritical : ∀ point : {point : Point3 // point ∈ final.union},
      PureWZ2PaperADSet1
        (scalarProjection (finalPlaneMap point)
          (final.union ∩ Metric.closedBall (point : Point3)
            (Real.sqrt criticalScale)))
        criticalScale (1 - sigma) sourceConstant := by
    intro point
    have hpullback : (point : Point3) ∈
        (propertyThreeFinePullbackShading
          sticky.cover sticky.refined propP.propertyThree).union := by
      rcases point.prop with ⟨index, hindex⟩
      exact ⟨index, hfinalSub index hindex⟩
    let S : Set Point3 := sticky.croppedCoarseShading.union ∩
      Metric.closedBall (point : Point3) (4 * tau)
    have hinvCube : Real.rpow rho.1 (-3 : ℝ) ≤
        Real.rpow delta (-sourceADLoss) :=
      aligned_scale_inv_cube_bound hdelta hdeltaOne hL_lower
        hstickyLoss_le_sourceAD
    have hAD :=
      propertyThreeFinePullback_high_local_ad_at_critical_scale_of_inv_cube_bound
        sticky.balanced epsilon₁ epsilon₃ propP
        (finalPlaneMap point) (hfinalUnit point) point hpullback
        S rfl
        (sticky.croppedCoarseShading.union_measurable.inter
          Metric.isClosed_closedBall.measurableSet)
        (by intro other hother; exact hother.2)
        htau_def htau_pos htau_le_20L hL_le_tau htau_sq htau_le_one
        hL_small hL_pos hL_half hsigma_pos hsigma_lt_one heps₁_pos
        heps₁_lt heps₃_pos heps₃_def heps_sum L₀_log hL_le_L0_log
        h_log_main h_propertyThree_full h_ax_condition hdelta hdeltaOne
        hsourceADLoss hL_bound hinvCube
    apply hAD.mono_set
    rintro value ⟨other, hother, rfl⟩
    exact ⟨other, ⟨by
      rcases hother.1 with ⟨index, hindex⟩
      exact ⟨index, hfinalSub index hindex⟩, hother.2⟩, rfl⟩
  exact ⟨{
    planeMap := finalPlaneMap
    planeMap_lipschitz := hplaneLipschitz
    planeMap_unit := hfinalUnit
    planeMap_incidence := fun index point hpoint =>
      planeMap.incidence index point hpoint
    local_ad := local_projection_ad_all_scales_of_critical
      finalPlaneMap hfinalUnit hdelta hdeltaOne.le hsigma_pos
      hsigma_lt_one htargetLoss hcriticalPos hcriticalOne sourceConstant
      hcritical hsmallCost hlargeEndpoint
  }⟩

/-- Attach every-scale local AD to an already-produced finite-planiness
refinement of the selected Property-Three pullback. -/
theorem propertyThree_selected_initial_local_data
    {delta sigma stickyLoss sourceADLoss outputLoss tau epsilon₁ epsilon₃
      coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (bounded : BalancedFinitePlaninessData
      (coefficient := coefficient)
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree))
    (hboundedMass : 0 < bounded.refinement.shading.mass)
    (hdelta : 0 < delta)
    (hdeltaOne : delta < 1)
    (houtputLoss : 0 < outputLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (htau_def : tau = rho.1 * Real.sqrt 3)
    (htau_pos : 0 < tau)
    (htau_le_20L : tau ≤ 20 * rho.1)
    (hL_le_tau : rho.1 ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * rho.1)
    (htau_le_one : tau ≤ 1)
    (hL_small : rho.1 ≤ 1 / 1000)
    (hL_pos : 0 < rho.1)
    (hL_half : rho.1 ≤ 1 / 2)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (heps₁_pos : 0 < epsilon₁)
    (heps₁_lt : epsilon₁ < 1 / 20)
    (heps₃_pos : 0 < epsilon₃)
    (heps₃_def : epsilon₃ = 1 - 2 * epsilon₁)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (L₀_log : ℝ)
    (hL_le_L0_log : rho.1 ≤ L₀_log)
    (h_log_main : 0 < epsilon₁ → ∀ L' : ℝ, 0 < L' → L' ≤ L₀_log →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ parent : Fin sticky.coarse.card, ∀ point : Point3,
        point ∈ propP.propertyThree.carrier parent →
          Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
              ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier parent ∩
              Metric.closedBall point tau))
    (h_ax_condition :
      4 * (6 * rho.1) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (hL_lower : Real.rpow delta stickyLoss ≤ rho.1)
    (hL_bound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyLoss_le_sourceAD : 3 * stickyLoss ≤ sourceADLoss)
    (hsmallCost :
      let criticalScale := 48 * rho.1 ^ 2
      let sourceConstant := Kakeya.realRpowENN delta (-sourceADLoss)
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * criticalScale / delta)) ≤
        Kakeya.realRpowENN delta (-outputLoss))
    (hlargeEndpoint :
      let criticalScale := 48 * rho.1 ^ 2
      3 * (2 / Real.sqrt criticalScale) ^ sigma ≤
        delta ^ (-outputLoss)) :
    ∃ initial : PropertyThreeSelectedInitialLocalData
        (sigma := sigma) (outputLoss := outputLoss)
        (coefficient := coefficient)
        (propertyThreeFinePullbackShading
          sticky.cover sticky.refined propP.propertyThree),
      initial.incidence = bounded.incidence := by
  let source := propertyThreeFinePullbackShading
    sticky.cover sticky.refined propP.propertyThree
  let final := bounded.refinement.shading
  let sourceMap := bounded.refinement.planeMap
  rcases propertyThree_selected_subshading_every_scale_relaxed_local_grain
      sticky propP sourceMap bounded.refinement.lipschitz
      bounded.refinement.subshading hdelta hdeltaOne houtputLoss
      hsourceADLoss htau_def htau_pos htau_le_20L hL_le_tau htau_sq
      htau_le_one hL_small hL_pos hL_half hsigma_pos hsigma_lt_one
      heps₁_pos heps₁_lt heps₃_pos heps₃_def heps_sum L₀_log
      hL_le_L0_log h_log_main h_propertyThree_full h_ax_condition
      hL_lower hL_bound hstickyLoss_le_sourceAD hsmallCost
      hlargeEndpoint with ⟨localGrains⟩
  have hincidenceNonnegative : 0 ≤ bounded.incidence :=
    bounded.incidence_nonnegative_of_mass_pos hboundedMass
  refine ⟨{
    planiness := bounded
    planiness_mass_pos := hboundedMass
    incidence := bounded.incidence
    planiness_incidence_le := le_rfl
    incidence_nonnegative := hincidenceNonnegative
    localGrains := localGrains
  }, rfl⟩

/-- Rebase the initial local-grain package on the actual fine shading in the
Node-3 sticky output.

The construction is the literal composition used in Proposition 6.3.  The
first factor is the mass retained when Property Three is pulled back from the
coarse family, and the second factor is the finite-planiness refinement.  No
family or shading is replaced: the final shading and its plane map are exactly
those of `initial`, while its source is recorded as `sticky.refined`, whose
complete metric fibres carry the frozen Node-3 rescaling certificates. -/
noncomputable def PropertyThreeSelectedInitialLocalData.onStickyRefined
    {delta sigma stickyLoss outputLoss tau epsilon₁ epsilon₃ coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := outputLoss)
      (coefficient := coefficient)
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree))
    (hdelta : 0 < delta) :
    PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := outputLoss)
      (coefficient := coefficient) sticky.refined := by
  let coarseCap := stickyCoarseMultiplicityCap sticky
  let fiberCap := stickyFiberMultiplicityCap sticky
  let pullbackFactor : ENNReal :=
    (2 * coarseCap * coarseCap * fiberCap)⁻¹
  have hrho : 0 < rho.1 := sticky.coarse_extremal.delta_pos
  have hratio : 0 < delta / rho.1 := div_pos hdelta hrho
  have hcoarseNonempty : sticky.coarse.Nonempty := by
    let sourceIndex : Fin sticky.selected.family.card :=
      ⟨0, sticky.selected_nonempty⟩
    rcases sticky.cover.covers sourceIndex with ⟨parent, _⟩
    exact Nat.zero_lt_of_lt parent.isLt
  have hcoarseCard : sticky.coarse.enncard ≠ 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using
      hcoarseNonempty.ne'
  have hfineCard : sticky.selected.family.enncard ≠ 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using
      sticky.selected_nonempty.ne'
  have hcoarsePower :
      Kakeya.realRpowENN rho.1 (2 - sigma - stickyLoss) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hrho (2 - sigma - stickyLoss))).ne'
  have hfiberPower :
      Kakeya.realRpowENN (delta / rho.1)
          (2 - sigma - stickyLoss) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hratio (2 - sigma - stickyLoss))).ne'
  have hcoarseCapZero : coarseCap ≠ 0 :=
    mul_ne_zero hcoarsePower hcoarseCard
  have hfiberCapZero : fiberCap ≠ 0 :=
    mul_ne_zero hfiberPower hfineCard
  have hcoarseCapTop : coarseCap ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp [coarseCap,
      stickyCoarseMultiplicityCap, Kakeya.realRpowENN])
      (by simp [coarseCap, stickyCoarseMultiplicityCap,
        Kakeya.Streamlined.TubeFamily.enncard])
  have hfiberCapTop : fiberCap ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp [fiberCap,
      stickyFiberMultiplicityCap, Kakeya.realRpowENN])
      (by simp [fiberCap, stickyFiberMultiplicityCap,
        Kakeya.Streamlined.TubeFamily.enncard])
  have hcapZero : 2 * coarseCap * coarseCap * fiberCap ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hcoarseCapZero)
      hcoarseCapZero) hfiberCapZero
  have hcapTop : 2 * coarseCap * coarseCap * fiberCap ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hcoarseCapTop)
        hcoarseCapTop) hfiberCapTop
  have hpullbackFactorPos : 0 < pullbackFactor :=
    ENNReal.inv_pos.mpr hcapTop
  have hpullbackFactorTop : pullbackFactor ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr hcapZero
  have hpullbackMass : pullbackFactor * sticky.refined.mass ≤
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree).mass := by
    simpa [pullbackFactor, coarseCap, fiberCap] using
      propertyThreeFinePullback_mass_lower_of_sticky
        sticky propP.propertyThree hdelta
        (fun index => (propP.propertyThree_sub index).trans
          (propP.propertyOne_sub index))
        propP.propertyThree_cubical propP.propertyThree_mass
  let combined : BalancedFinitePlaninessData
      (coefficient := coefficient) sticky.refined :=
    { incidence := initial.planiness.incidence
      leftFactor := pullbackFactor * initial.planiness.leftFactor
      rightFactor := initial.planiness.rightFactor
      leftFactor_pos :=
        ENNReal.mul_pos hpullbackFactorPos.ne'
          initial.planiness.leftFactor_pos.ne'
      leftFactor_ne_top :=
        ENNReal.mul_ne_top hpullbackFactorTop
          initial.planiness.leftFactor_ne_top
      rightFactor_ne_top := initial.planiness.rightFactor_ne_top
      refinement :=
        { shading := initial.planiness.refinement.shading
          subshading := fun index =>
            (initial.planiness.refinement.subshading index).trans
              (propertyThreeFinePullbackShading_subshading
                sticky.cover sticky.refined propP.propertyThree index)
          cubical := initial.planiness.refinement.cubical
          planeMap := initial.planiness.refinement.planeMap
          planeMap_cellwise :=
            initial.planiness.refinement.planeMap_cellwise
          lipschitz := initial.planiness.refinement.lipschitz
          mass_retention := by
            calc
              (pullbackFactor * initial.planiness.leftFactor) *
                    sticky.refined.mass =
                  initial.planiness.leftFactor *
                    (pullbackFactor * sticky.refined.mass) := by ring
              _ ≤ initial.planiness.leftFactor *
                  (propertyThreeFinePullbackShading
                    sticky.cover sticky.refined
                    propP.propertyThree).mass := by gcongr
              _ ≤ initial.planiness.rightFactor *
                  initial.planiness.refinement.shading.mass :=
                initial.planiness.refinement.mass_retention } }
  exact
    { planiness := combined
      planiness_mass_pos := initial.planiness_mass_pos
      incidence := initial.incidence
      planiness_incidence_le := initial.planiness_incidence_le
      incidence_nonnegative := initial.incidence_nonnegative
      localGrains := initial.localGrains }

end Kakeya.Assouad.PureWZ2

end
