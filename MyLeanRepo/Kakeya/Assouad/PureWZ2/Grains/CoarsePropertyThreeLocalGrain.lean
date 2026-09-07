import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CoarsePropertyThreeExactLipschitzPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullbackAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SingleCriticalEveryScaleLocalAD

/-!
# Same-family local grains on coarse Property Three

This is the coarse-family analogue of the fine-pullback local-grain
assembler.  The Córdoba estimate is proved on the whole Property-Three set
in the direction of the genuine final plane map, and then restricted to the
same final shading.  All endpoint arithmetic remains explicit.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- Relaxed-Lipschitz form of the coarse Property-Three local-grain
assembler.  It is the literal Lemma 4.12 interface used before the final
normalizing dilation in Proposition 6.3. -/
theorem coarse_property_three_subshading_relaxed_local_grain
    {sigma L targetLoss tau epsilon₁ epsilon₃ : ℝ}
    {coefficient : NNReal}
    {family : Kakeya.Streamlined.TubeFamily L}
    {coarseShading final : WZ1PaperTubeShading family}
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (L := L) (tau := tau)
      (coarseShading := coarseShading) epsilon₁ epsilon₃)
    (planeMap : PaperWZ1WeakPlaneMapData final L)
    (hplaneLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ final.union} =>
        planeMap.planeMap point))
    (hfinalSub : PaperIsSubshading final propP.propertyThree)
    (hL : 0 < L) (hLOne : L ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (htargetLoss : 0 < targetLoss)
    (htau_def : tau = L * Real.sqrt 3)
    (htau_pos : 0 < tau)
    (htau_le_20L : tau ≤ 20 * L)
    (hL_le_tau : L ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L)
    (htau_le_one : tau ≤ 1)
    (hL_small : L ≤ 1 / 1000)
    (heps₁_pos : 0 < epsilon₁)
    (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (L₀_log : ℝ)
    (hL_le_L0_log : L ≤ L₀_log)
    (h_log_main : 0 < epsilon₁ → ∀ L' : ℝ, 0 < L' → L' ≤ L₀_log →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ parent : Fin family.card, ∀ point : Point3,
        point ∈ propP.propertyThree.carrier parent →
          Kakeya.realRpowENN L (2 + 2 * epsilon₁) *
              ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier parent ∩
              Metric.closedBall point tau))
    (h_ax_condition :
      4 * (6 * L) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃)) ^ 2)
    (W0 Vmin Vtotal : ℝ)
    (hW0 : W0 = 40 * L) (hW0Pos : 0 < W0)
    (hVmin : Vmin =
      Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200)
    (hVminPos : 0 < Vmin)
    (hVtotalPos : 0 < Vtotal)
    (hVtotal : volume coarseShading.union ≤ ENNReal.ofReal Vtotal)
    (sourceConstant : ENNReal)
    (hsourceOne : 1 ≤ sourceConstant)
    (hsourceTop : sourceConstant ≠ ⊤)
    (hcriticalArithmetic :
      let criticalScale := 48 * L ^ 2
      ENNReal.ofReal
        ((Vtotal / Vmin) *
          (2 * (2 * W0) / criticalScale + 2)) ≤ sourceConstant)
    (hsmallCost :
      let criticalScale := 48 * L ^ 2
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * criticalScale / L)) ≤
        Kakeya.realRpowENN L (-targetLoss))
    (hlargeEndpoint :
      let criticalScale := 48 * L ^ 2
      3 * (2 / Real.sqrt criticalScale) ^ sigma ≤
        L ^ (-targetLoss)) :
    ∃ localGrains : PureWZ2RelaxedLocalGrainData final sigma
        (Kakeya.realRpowENN L (-targetLoss)) coefficient,
      localGrains.planeMap =
        (fun point : {point : Point3 // point ∈ final.union} =>
          planeMap.planeMap point) := by
  let finalPlaneMap : {point : Point3 // point ∈ final.union} → Point3 :=
    fun point => planeMap.planeMap point
  have hfinalUnit : ∀ point, ‖finalPlaneMap point‖ = 1 := by
    intro point
    exact planeMap.unit point point.prop
  have hfinalIncidence : ∀ index point,
      ∀ hpoint : point ∈ final.carrier index,
        |inner ℝ (family.tube index).direction
          (finalPlaneMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ L := by
    intro index point hpoint
    exact planeMap.incidence index point hpoint
  let criticalScale : ℝ := 48 * L ^ 2
  have hcriticalPos : 0 < criticalScale := by
    dsimp only [criticalScale]
    positivity
  have hcriticalOne : criticalScale ≤ 1 := by
    dsimp only [criticalScale]
    nlinarith [sq_nonneg L]
  have hcritical : ∀ point : {point : Point3 // point ∈ final.union},
      PureWZ2PaperADSet1
        (scalarProjection (finalPlaneMap point)
          (final.union ∩ Metric.closedBall (point : Point3)
            (Real.sqrt criticalScale)))
        criticalScale (1 - sigma) sourceConstant := by
    intro point
    have hpointProperty : (point : Point3) ∈ propP.propertyThree.union := by
      rcases point.prop with ⟨index, hindex⟩
      exact ⟨index, hfinalSub index hindex⟩
    rcases hpointProperty with ⟨queryIndex, hqueryIndex⟩
    have hpointCoarse : (point : Point3) ∈ coarseShading.union :=
      ⟨queryIndex, propP.propertyOne_sub queryIndex
        (propP.propertyThree_sub queryIndex hqueryIndex)⟩
    have hnear :
        (propP.propertyThree.union ∩
          Metric.closedBall (point : Point3) tau).Nonempty := by
      refine ⟨point, ⟨queryIndex, hqueryIndex⟩, ?_⟩
      simpa [Metric.mem_closedBall] using htau_pos.le
    let S : Set Point3 := coarseShading.union ∩
      Metric.closedBall (point : Point3) (4 * tau)
    have hSVolume : volume S ≤ ENNReal.ofReal Vtotal :=
      (measure_mono Set.inter_subset_left).trans hVtotal
    have hsqrt : Real.sqrt criticalScale ≤ 4 * tau :=
      sqrt_rho_le_4tau hL hcriticalPos.le htau_def (le_refl _)
    exact high_case_cordoba_ad_of_nearby
      epsilon₁ epsilon₃ propP
      (finalPlaneMap point) (hfinalUnit point)
      (point : Point3) hpointCoarse hnear
      S rfl
      (coarseShading.union_measurable.inter
        Metric.isClosed_closedBall.measurableSet)
      (by intro other hother; exact hother.2)
      W0 Vmin Vtotal hW0Pos hW0 hVminPos hVmin
      hVtotalPos hSVolume htau_def htau_pos htau_le_20L
      hL_le_tau htau_sq htau_le_one hL_small hL hsigma hsigmaOne
      heps₁_pos heps₃_pos heps_sum L₀_log hL_le_L0_log h_log_main
      h_propertyThree_full h_ax_condition
      (final.union ∩ Metric.closedBall (point : Point3)
        (Real.sqrt criticalScale))
      (by
        intro other hother
        rcases hother.1 with ⟨index, hindex⟩
        exact ⟨⟨index, propP.propertyOne_sub index
          (propP.propertyThree_sub index (hfinalSub index hindex))⟩,
          hother.2⟩)
      hsqrt hcriticalPos sourceConstant hsourceOne hsourceTop
      hcriticalArithmetic
  exact ⟨relaxedLocalGrainData_of_critical finalPlaneMap hplaneLipschitz
    hfinalUnit hfinalIncidence hL hLOne hsigma hsigmaOne
    htargetLoss hcriticalPos hcriticalOne sourceConstant hcritical
    hsmallCost hlargeEndpoint, rfl⟩

/-- Package a Property-Three subshading carrying a Lip-1 exact-scale plane
map into strict every-scale local grains. -/
theorem coarse_property_three_subshading_local_grain
    {sigma L targetLoss tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily L}
    {coarseShading final : WZ1PaperTubeShading family}
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (L := L) (tau := tau)
      (coarseShading := coarseShading) epsilon₁ epsilon₃)
    (planeMap : PaperWZ1WeakPlaneMapData final L)
    (hplaneLipschitz : LipschitzWith 1
      (fun point : {point : Point3 // point ∈ final.union} =>
        planeMap.planeMap point))
    (hfinalSub : PaperIsSubshading final propP.propertyThree)
    (hL : 0 < L) (hLOne : L ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (htargetLoss : 0 < targetLoss)
    (htau_def : tau = L * Real.sqrt 3)
    (htau_pos : 0 < tau)
    (htau_le_20L : tau ≤ 20 * L)
    (hL_le_tau : L ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L)
    (htau_le_one : tau ≤ 1)
    (hL_small : L ≤ 1 / 1000)
    (heps₁_pos : 0 < epsilon₁)
    (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (L₀_log : ℝ)
    (hL_le_L0_log : L ≤ L₀_log)
    (h_log_main : 0 < epsilon₁ → ∀ L' : ℝ, 0 < L' → L' ≤ L₀_log →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ parent : Fin family.card, ∀ point : Point3,
        point ∈ propP.propertyThree.carrier parent →
          Kakeya.realRpowENN L (2 + 2 * epsilon₁) *
              ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier parent ∩
              Metric.closedBall point tau))
    (h_ax_condition :
      4 * (6 * L) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃)) ^ 2)
    (W0 Vmin Vtotal : ℝ)
    (hW0 : W0 = 40 * L) (hW0Pos : 0 < W0)
    (hVmin : Vmin =
      Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200)
    (hVminPos : 0 < Vmin)
    (hVtotalPos : 0 < Vtotal)
    (hVtotal : volume coarseShading.union ≤ ENNReal.ofReal Vtotal)
    (sourceConstant : ENNReal)
    (hsourceOne : 1 ≤ sourceConstant)
    (hsourceTop : sourceConstant ≠ ⊤)
    (hcriticalArithmetic :
      let criticalScale := 48 * L ^ 2
      ENNReal.ofReal
        ((Vtotal / Vmin) *
          (2 * (2 * W0) / criticalScale + 2)) ≤ sourceConstant)
    (hsmallCost :
      let criticalScale := 48 * L ^ 2
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * criticalScale / L)) ≤
        Kakeya.realRpowENN L (-targetLoss))
    (hlargeEndpoint :
      let criticalScale := 48 * L ^ 2
      3 * (2 / Real.sqrt criticalScale) ^ sigma ≤
        L ^ (-targetLoss)) :
    Nonempty (PureWZ2LocalGrainData final sigma
      (Kakeya.realRpowENN L (-targetLoss))) := by
  let finalPlaneMap : {point : Point3 // point ∈ final.union} → Point3 :=
    fun point => planeMap.planeMap point
  have hfinalUnit : ∀ point, ‖finalPlaneMap point‖ = 1 := by
    intro point
    exact planeMap.unit point point.prop
  have hfinalIncidence : ∀ index point,
      ∀ hpoint : point ∈ final.carrier index,
        |inner ℝ (family.tube index).direction
          (finalPlaneMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ L := by
    intro index point hpoint
    exact planeMap.incidence index point hpoint
  let criticalScale : ℝ := 48 * L ^ 2
  have hcriticalPos : 0 < criticalScale := by
    dsimp only [criticalScale]
    positivity
  have hcriticalOne : criticalScale ≤ 1 := by
    dsimp only [criticalScale]
    nlinarith [sq_nonneg L]
  have hcritical : ∀ point : {point : Point3 // point ∈ final.union},
      PureWZ2PaperADSet1
        (scalarProjection (finalPlaneMap point)
          (final.union ∩ Metric.closedBall (point : Point3)
            (Real.sqrt criticalScale)))
        criticalScale (1 - sigma) sourceConstant := by
    intro point
    have hpointProperty : (point : Point3) ∈ propP.propertyThree.union := by
      rcases point.prop with ⟨index, hindex⟩
      exact ⟨index, hfinalSub index hindex⟩
    rcases hpointProperty with ⟨queryIndex, hqueryIndex⟩
    have hpointCoarse : (point : Point3) ∈ coarseShading.union :=
      ⟨queryIndex, propP.propertyOne_sub queryIndex
        (propP.propertyThree_sub queryIndex hqueryIndex)⟩
    have hnear :
        (propP.propertyThree.union ∩
          Metric.closedBall (point : Point3) tau).Nonempty := by
      refine ⟨point, ⟨queryIndex, hqueryIndex⟩, ?_⟩
      simpa [Metric.mem_closedBall] using htau_pos.le
    let S : Set Point3 := coarseShading.union ∩
      Metric.closedBall (point : Point3) (4 * tau)
    have hSVolume : volume S ≤ ENNReal.ofReal Vtotal :=
      (measure_mono (Set.inter_subset_left)).trans hVtotal
    have hsqrt : Real.sqrt criticalScale ≤ 4 * tau :=
      sqrt_rho_le_4tau hL hcriticalPos.le htau_def (le_refl _)
    exact high_case_cordoba_ad_of_nearby
      epsilon₁ epsilon₃ propP
      (finalPlaneMap point) (hfinalUnit point)
      (point : Point3) hpointCoarse hnear
      S rfl
      (coarseShading.union_measurable.inter
        Metric.isClosed_closedBall.measurableSet)
      (by intro other hother; exact hother.2)
      W0 Vmin Vtotal hW0Pos hW0 hVminPos hVmin
      hVtotalPos hSVolume htau_def htau_pos htau_le_20L
      hL_le_tau htau_sq htau_le_one hL_small hL hsigma hsigmaOne
      heps₁_pos heps₃_pos heps_sum L₀_log hL_le_L0_log h_log_main
      h_propertyThree_full h_ax_condition
      (final.union ∩ Metric.closedBall (point : Point3)
        (Real.sqrt criticalScale))
      (by
        intro other hother
        rcases hother.1 with ⟨index, hindex⟩
        exact ⟨⟨index, propP.propertyOne_sub index
          (propP.propertyThree_sub index (hfinalSub index hindex))⟩,
          hother.2⟩)
      hsqrt hcriticalPos sourceConstant hsourceOne hsourceTop
      hcriticalArithmetic
  let localGrains : PureWZ2LocalGrainData final sigma
      (Kakeya.realRpowENN L (-targetLoss)) :=
    localGrainData_of_critical finalPlaneMap hplaneLipschitz
      hfinalUnit hfinalIncidence hL hLOne hsigma hsigmaOne
      htargetLoss hcriticalPos hcriticalOne sourceConstant hcritical
      hsmallCost hlargeEndpoint
  exact ⟨localGrains⟩

end Kakeya.Assouad.PureWZ2

end
