import MyLeanRepo.Kakeya.Assouad.WZ1.HorizontalChartNormalization.Basic
import MyLeanRepo.Kakeya.Assouad.WZ1.HorizontalChartNormalization.Frostman

/-!
# Horizontal chart normalization for WZ1 Proposition 9 (main construction)

Extremal pair, plane map, global grains transport, and the main
normalization construction.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined MeasureTheory Set Metric

-- ============================================================================
-- 6. Extremal pair transport
-- ============================================================================

lemma transportFamily_isInVerticalChart
    (chart : WZ1HorizontalChart)
    {delta : ℝ}
    (F : Streamlined.TubeFamily delta)
    (hF : IsInVerticalChart F) :
    IsInVerticalChart
      (transportFamily chart.isometry F) := by
  intro i
  change
    (1 / 2 : ℝ) ≤
      |(chart.isometry (F.tube i).direction) (2 : Fin 3)|
  rw [chart.isometry_preserves_coord2]
  exact hF i

lemma transportExtremalPair (e : Point3 ≃ₗᵢ[ℝ] Point3)
    (e_invol : ∀ x, e (e x) = x)
    (hvol : ∀ s, volume (e '' s) = volume s)
    {δ sigma epsilon : ℝ}
    {F : Streamlined.TubeFamily δ}
    {U : Streamlined.UniformTubeStructure F}
    {Y : Streamlined.TubeShading F}
    (h : WZ1ExtremalPair sigma epsilon F U Y) :
    WZ1ExtremalPair sigma epsilon
      (transportFamily e F)
      (transportUniform e hvol U)
      (transportShading e Y) := by
  rcases h with ⟨hδ, hδ1, hFne, hball, hdist, hunif, hfrost, hdense, hupper, hlower⟩
  have hball' : (transportShading e Y).union ⊆ Metric.closedBall (0 : Point3) 1 := by
    rw [transportShading_union e]
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have h9 : y ∈ Metric.closedBall (0 : Point3) 1 := hball hy
    have h10 : dist (e y) 0 = dist y 0 := by
      simpa [dist_zero_right] using e.norm_map y
    rw [Metric.mem_closedBall] at h9 ⊢
    rw [h10]; exact h9
  have hdist' : (transportFamily e F).IsEssentiallyDistinct := by
    intro i j hne
    have h := hdist i j hne
    simp only [Kakeya.DeltaTube.EssentiallyDistinct] at h ⊢
    have hcar1 : ((transportFamily e F).tube i).carrier =
        e '' (F.tube i).carrier := transportFamily_carrier e F i
    have hcar2 : ((transportFamily e F).tube j).carrier =
        e '' (F.tube j).carrier := transportFamily_carrier e F j
    have hvol1 : ((transportFamily e F).tube i).volume = (F.tube i).volume :=
      transportTube_volume e hvol (F.tube i)
    have hvol2 : ((transportFamily e F).tube j).volume = (F.tube j).volume :=
      transportTube_volume e hvol (F.tube j)
    have h_inter : volume (((transportFamily e F).tube i).carrier ∩ ((transportFamily e F).tube j).carrier) =
        volume ((F.tube i).carrier ∩ (F.tube j).carrier) := by
      have h_set : ((transportFamily e F).tube i).carrier ∩ ((transportFamily e F).tube j).carrier =
          e '' ((F.tube i).carrier ∩ (F.tube j).carrier) := by
        rw [hcar1, hcar2, Set.image_inter e.injective]
      rw [h_set]
      exact hvol ((F.tube i).carrier ∩ (F.tube j).carrier)
    rw [h_inter, hvol1, hvol2]
    exact h
  have hfrost' := transportUniform_frostman e e_invol hvol hfrost
  have hFmass : (transportFamily e F).toBodyFamily.mass = F.toBodyFamily.mass :=
    transportFamily_mass e hvol F
  have hYmass : (transportShading e Y).mass = Y.mass := transportShading_mass e hvol
  have hdense' : (transportShading e Y).IsLambdaDense (Kakeya.realRpowENN δ epsilon) := by
    have h_goal : Kakeya.realRpowENN δ epsilon * (transportFamily e F).toBodyFamily.mass ≤
        (transportShading e Y).mass := by
      rw [hFmass, hYmass]
      exact hdense
    exact h_goal
  have hupper' : volume (transportShading e Y).union ≤
      Kakeya.realRpowENN δ (sigma - epsilon) := by
    rw [transportShading_union e, hvol Y.union]
    exact hupper
  have hlower' : Kakeya.realRpowENN δ (sigma + epsilon) ≤
      volume (transportShading e Y).union := by
    rw [transportShading_union e, hvol Y.union]
    exact hlower
  exact ⟨hδ, hδ1, hFne, hball', hdist', hunif, hfrost', hdense', hupper', hlower'⟩

-- ============================================================================
-- 7. Plane map transport
-- ============================================================================

def transportPlaneMap (e : Point3 ≃ₗᵢ[ℝ] Point3) {δ : ℝ}
    {F : Streamlined.TubeFamily δ}
    {Y : Streamlined.TubeShading F}
    (pm : WZ1PlaneMapData Y) :
    WZ1PlaneMapData (transportShading e Y) where
  planeMap p := e (pm.planeMap (e.symm p))
  measurable := by
    have h1 : Measurable (e : Point3 → Point3) := e.continuous.measurable
    have h2 : Measurable (fun p : Point3 => pm.planeMap (e.symm p)) :=
      pm.measurable.comp e.symm.continuous.measurable
    exact h1.comp h2
  lipschitzConstant := pm.lipschitzConstant
  lipschitz := by
    have h_union : (transportShading e Y).union = e '' Y.union := transportShading_union e
    rw [h_union]
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro x hx y hy
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    have hsx : e.symm (e x') = x' := e.left_inv x'
    have hsy : e.symm (e y') = y' := e.left_inv y'
    have hlip : ∀ (a : Point3), a ∈ Y.union → ∀ (b : Point3), b ∈ Y.union →
        dist (pm.planeMap a) (pm.planeMap b) ≤ (pm.lipschitzConstant : ℝ) * dist a b :=
      lipschitzOnWith_iff_dist_le_mul.mp pm.lipschitz
    have h := hlip x' hx' y' hy'
    have h_goal : dist (e (pm.planeMap (e.symm (e x')))) (e (pm.planeMap (e.symm (e y')))) =
        dist (pm.planeMap x') (pm.planeMap y') := by
      rw [hsx, hsy]
      exact e.dist_map _ _
    rw [h_goal]
    have h2 : dist (e x') (e y') = dist x' y' := e.dist_map _ _
    rw [h2]
    exact h
  unit p hp := by
    have h_union : (transportShading e Y).union = e '' Y.union := transportShading_union e
    rw [h_union] at hp
    rcases hp with ⟨x, hx, rfl⟩
    have h1 : e.symm (e x) = x := e.left_inv x
    have h2 : ‖e (pm.planeMap (e.symm (e x)))‖ = ‖pm.planeMap x‖ := by
      rw [h1]
      exact e.norm_map (pm.planeMap x)
    rw [h2]
    exact pm.unit x hx
  incidence i p hp := by
    have hcar : (transportShading e Y).carrier i = e '' Y.carrier i := by rfl
    rw [hcar] at hp
    rcases hp with ⟨x, hx, rfl⟩
    have h1 : e.symm (e x) = x := e.left_inv x
    have h_card : (transportFamily e F).card = F.card := by
      dsimp only [transportFamily] <;> rfl
    let i' : Fin F.card := Fin.cast h_card i
    have hdir : ((transportFamily e F).tube i).direction = e (F.tube i').direction := by
      dsimp only [transportFamily, transportTube] <;> rfl
    have hinner : inner ℝ (e (F.tube i').direction) (e (pm.planeMap x)) =
        inner ℝ (F.tube i').direction (pm.planeMap x) := by
      exact e.toLinearIsometry.inner_map_map (F.tube i').direction (pm.planeMap x)
    rw [hdir, h1]
    rw [hinner]
    exact pm.incidence i' x hx

-- ============================================================================
-- 8. Global grains transport
-- ============================================================================

lemma transportProjection_eq
    (chart : WZ1HorizontalChart) (slope : ℝ → ℝ) (E : Set Point3) :
    globalGrainProjection slope (chart.isometry '' E) =
    wz1ChartedGlobalGrainProjection chart slope E := by
  let e := chart.isometry
  have hmain : ∀ (p : Point3), inner ℝ (e p) (globalGrainDirection (slope ((e p) (2 : Fin 3)))) =
      inner ℝ p (chart.direction (slope (p (2 : Fin 3)))) := by
    intro p
    have h1 : (e p) (2 : Fin 3) = p (2 : Fin 3) := chart.isometry_preserves_coord2 p
    let v := e (globalGrainDirection (slope (p (2 : Fin 3))))
    have h4 : inner ℝ (e p) (e v) = inner ℝ p v := e.toLinearIsometry.inner_map_map p v
    have h5 : e v = globalGrainDirection (slope (p (2 : Fin 3))) := by
      dsimp only [v]
      exact chart.isometry_involutive _
    have h2 : inner ℝ (e p) (globalGrainDirection (slope (p (2 : Fin 3)))) = inner ℝ p v := by
      rw [h5] at h4
      exact h4
    rw [h1] at *
    rw [h2]
    dsimp only [v]
    rw [chart.isometry_globalGrainDirection (slope (p (2 : Fin 3)))]
  have h_img : (fun x : Point3 => inner ℝ (e x) (globalGrainDirection (slope ((e x) (2 : Fin 3))))) '' E =
      (fun p : Point3 => inner ℝ p (chart.direction (slope (p (2 : Fin 3))))) '' E := by
    apply Set.image_congr
    intro p _
    exact hmain p
  have h1 : globalGrainProjection slope (e '' E) =
      (fun x : Point3 => inner ℝ (e x) (globalGrainDirection (slope ((e x) (2 : Fin 3))))) '' E := by
    have h2 : globalGrainProjection slope (e '' E) =
        (fun p : Point3 => inner ℝ p (globalGrainDirection (slope (p (2 : Fin 3))))) '' (e '' E) := by rfl
    rw [h2, Set.image_image]
    <;> rfl
  rw [h1]
  exact h_img

lemma transportSlab_eq
    (chart : WZ1HorizontalChart) (E : Set Point3) (z δ : ℝ) :
    globalGrainSlab (chart.isometry '' E) z δ =
    chart.isometry '' (globalGrainSlab E z δ) := by
  let e := chart.isometry
  have h_coord : ∀ p, (e p) (2 : Fin 3) = p (2 : Fin 3) := chart.isometry_preserves_coord2
  have h_inj : Function.Injective e := e.injective
  have h_image_inter : ∀ (A B C : Set Point3), e '' (A ∩ B ∩ C) = (e '' A) ∩ (e '' B) ∩ (e '' C) := by
    intro A B C
    rw [Set.image_inter h_inj, Set.image_inter h_inj]
  have h_image_coord : ∀ (a b : ℝ), e '' {p : Point3 | p (2 : Fin 3) ∈ Set.Icc a b} =
      {q : Point3 | q (2 : Fin 3) ∈ Set.Icc a b} := by
    intro a b
    ext q
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, hp, rfl⟩; rw [h_coord p]; exact hp
    · intro hq
      refine ⟨e.symm q, ?_, e.apply_symm_apply q⟩
      have h : (e (e.symm q)) (2 : Fin 3) = (e.symm q) (2 : Fin 3) := h_coord (e.symm q)
      rw [e.apply_symm_apply] at h
      rw [← h]; exact hq
  have h_main : e '' (globalGrainSlab E z δ) = globalGrainSlab (e '' E) z δ := by
    simp only [globalGrainSlab]
    rw [h_image_inter E _ _, h_image_coord (z - δ) (z + δ), h_image_coord (-1) 1]
    <;> rfl
  exact h_main.symm

def transportGlobalGrains
    (chart : WZ1HorizontalChart)
    {δ : ℝ} {F : Streamlined.TubeFamily δ}
    {Y : Streamlined.TubeShading F} {sigma : ℝ} {C : ENNReal}
    (g : WZ1ChartedLipschitzGlobalGrainData chart Y sigma C) :
    WZ1LipschitzGlobalGrainData (transportShading chart.isometry Y) sigma C where
  slope := g.slope
  lipschitzConstant := g.lipschitzConstant
  lipschitz := g.lipschitz
  global_slab_ad := by
    intro z hz
    have hsrc := g.global_slab_ad z hz
    let e := chart.isometry
    have h_union : (transportShading e Y).union = e '' Y.union := transportShading_union e
    have h_slab : globalGrainSlab (transportShading e Y).union z δ =
        e '' (globalGrainSlab Y.union z δ) := by
      rw [h_union]
      exact transportSlab_eq chart Y.union z δ
    have h_proj : globalGrainProjection g.slope (globalGrainSlab (transportShading e Y).union z δ) =
        wz1ChartedGlobalGrainProjection chart g.slope (globalGrainSlab Y.union z δ) := by
      rw [h_slab]
      exact transportProjection_eq chart g.slope (globalGrainSlab Y.union z δ)
    rw [h_proj]
    exact hsrc

-- ============================================================================
-- 9. Main normalization construction
-- ============================================================================

def mkNormalizationData
    {fineDelta sigma changedBalancedLoss transportInputLoss outputLoss
      sourceIncidenceScale : ℝ}
    {F : Streamlined.TubeFamily fineDelta}
    {U : Streamlined.UniformTubeStructure F}
    {Y : Streamlined.TubeShading F}
    {targetScale : Streamlined.AdmissibleScale fineDelta}
    {changedBalanced : WZ1BalancedCoverData
        (sigma := sigma) (epsilon := changedBalancedLoss) U Y targetScale}
    {changedSourcePlaneMap : WZ1WeakPlaneMapData Y sourceIncidenceScale}
    {changed : WZ1ScaleChangedLipschitzPlaneMapData
        (sigma := sigma) (balancedLoss := changedBalancedLoss)
        (outputLoss := transportInputLoss) U Y targetScale changedBalanced
        changedSourcePlaneMap}
    (charted : WZ1AnchoredGlobalGrainData
        changedBalanced changedSourcePlaneMap changed outputLoss) :
    WZ1HorizontalChartNormalizationData charted := by
  let e := charted.chart.isometry
  have e_invol : ∀ x, e (e x) = x := charted.chart.isometry_involutive
  have hvol : ∀ s, volume (e '' s) = volume s := volume_image e
  have hmap : (e : Point3 → Point3) = charted.chart.mapPoint := by
    funext x
    exact charted.chart.isometry_apply x
  let G := U.coarse targetScale
  let F' := transportFamily e G
  let U' := transportUniform e hvol changedBalanced.coarseUniform
  let Y' := transportShading e charted.shading
  let extremal' := transportExtremalPair e e_invol hvol charted.extremal
  let planeMap' := transportPlaneMap e charted.planeMap
  let globalGrains' := transportGlobalGrains charted.chart charted.globalGrains
  let output : WZ1GlobalPlaninessData sigma outputLoss targetScale.1 :=
    { family := F'
      uniform := U'
      shading := Y'
      vertical_chart :=
        transportFamily_isInVerticalChart
          charted.chart G charted.vertical_chart
      extremal := extremal'
      global_grains := globalGrains'
      planeMap := planeMap'
      slope_lipschitz_bound := charted.slope_lipschitz_bound
      slope_bound := charted.slope_bound
      planeMap_vertical_bound := by
        intro p hp
        have hp' : p ∈ e '' charted.shading.union := by
          simpa [Y', transportShading_union] using hp
        rcases hp' with ⟨q, hq, rfl⟩
        have hcoord :
            (planeMap'.planeMap (e q)) (2 : Fin 3) =
              charted.planeMap.planeMap q (2 : Fin 3) := by
          calc
            (planeMap'.planeMap (e q)) (2 : Fin 3) =
                (e
                  (charted.planeMap.planeMap
                    (e.symm (e q)))) (2 : Fin 3) := rfl
            _ =
                (e (charted.planeMap.planeMap q)) (2 : Fin 3) := by
                  rw [e.symm_apply_apply]
            _ = charted.planeMap.planeMap q (2 : Fin 3) :=
              charted.chart.isometry_preserves_coord2 _
        rw [hcoord]
        exact charted.planeMap_vertical_bound q hq
      planeMap_lipschitz_bound := charted.planeMap_lipschitz_bound }
  exact
    { output
      sourceIndex := by
        have h : F'.card = G.card := by
          dsimp only [F', transportFamily] <;> rfl
        exact Equiv.cast (congr_arg Fin h)
      tube_base_eq := by
        intro i
        change e (G.tube i).base = charted.chart.mapPoint (G.tube i).base
        rw [hmap]
      tube_direction_eq := by
        intro i
        change e (G.tube i).direction = charted.chart.mapPoint (G.tube i).direction
        rw [hmap]
      shading_carrier_eq := by
        intro i
        change e '' charted.shading.carrier i =
            charted.chart.mapPoint '' charted.shading.carrier i
        rw [hmap]
      planeMap_eq := by
        intro p _hp
        dsimp only [output]
        have h1 : e.symm (e p) = p := e.left_inv p
        have h2 : planeMap'.planeMap (e p) = e (charted.planeMap.planeMap p) := by
          have h3 : planeMap'.planeMap (e p) = e (charted.planeMap.planeMap (e.symm (e p))) := by rfl
          rw [h3, h1]
        rw [← hmap]
        exact h2
      slope_eq := by rfl
      uniformity_eq := by rfl
      coarseIndex := fun _rho => by
        have h : (U'.coarse _rho).card = (changedBalanced.coarseUniform.coarse _rho).card := by
          dsimp only [U', transportUniform, transportFamily] <;> rfl
        exact Equiv.cast (congr_arg Fin h)
      coarse_tube_base_eq := by
        intro rho i
        change e ((changedBalanced.coarseUniform.coarse rho).tube i).base =
            charted.chart.mapPoint
              ((changedBalanced.coarseUniform.coarse rho).tube i).base
        rw [hmap]
      coarse_tube_direction_eq := by
        intro rho i
        change e ((changedBalanced.coarseUniform.coarse rho).tube i).direction =
            charted.chart.mapPoint
              ((changedBalanced.coarseUniform.coarse rho).tube i).direction
        rw [hmap]
      parent_eq := by
        intro rho i
        dsimp only [output, U', transportUniform, transportCover] <;> rfl
    }

/-- Normalize either horizontal chart on the full coherent configuration. -/
theorem wz1_horizontal_chart_normalization :
    WZ1HorizontalChartNormalizationStatement := by
  intro fineDelta sigma changedBalancedLoss transportInputLoss outputLoss
    sourceIncidenceScale F U Y targetScale changedBalanced
    changedSourcePlaneMap changed charted
  exact ⟨mkNormalizationData charted⟩

end Kakeya.Assouad
