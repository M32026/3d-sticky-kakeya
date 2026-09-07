import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GeneralizedADTransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalProjectionHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingNormalizedGrainsStatements

/-!
# Paper AD transport through a centered isotropic similarity

The origin-only transport is conjugated by translation. Scalar projections
therefore acquire an additive constant, which is harmless for the
paper-literal AD predicate.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

private lemma scalarProjection_rescaling
    {center v : Point3} {scale : ℝ} {E : Set Point3}
    (hscale : 0 < scale) :
    scalarProjection v (wz1IsotropicRescalingMap center scale '' E) =
      (fun value : ℝ => scale * value - scale * inner ℝ center v) ''
        scalarProjection v E := by
  ext value
  simp only [scalarProjection, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨point, hpoint, rfl⟩, rfl⟩
    refine ⟨inner ℝ point v, ⟨point, hpoint, rfl⟩, ?_⟩
    simp [wz1IsotropicRescalingMap, inner_smul_left, inner_sub_left]
    ring
  · rintro ⟨_, ⟨point, hpoint, rfl⟩, rfl⟩
    refine ⟨wz1IsotropicRescalingMap center scale point,
      ⟨point, hpoint, rfl⟩, ?_⟩
    simp [wz1IsotropicRescalingMap, inner_smul_left, inner_sub_left]
    ring

/-- Transport global paper AD through a centered isotropic similarity. -/
lemma global_ad_transport_centered_general
    {sigma loss loss_src delta' : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading : WZ1PaperTubeShading family}
    (slope : ℝ → ℝ)
    (global_ad : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice shading.union z))
        delta' (1 - sigma)
          (Kakeya.realRpowENN delta' (-loss_src)))
    {scale : ℝ} (hscale : 0 < scale)
    (center : Point3)
    {targetUnion : Set Point3}
    (htarget : targetUnion ⊆
      wz1IsotropicRescalingMap center scale '' shading.union)
    (targetSlope : ℝ → ℝ)
    (hslope : ∀ z, (horizontalSlice targetUnion z).Nonempty →
      targetSlope z = slope (center 2 + z / scale))
    (hloss_src : 0 < loss_src) (hloss_lt : loss_src < loss)
    (hsmall : Real.rpow delta' (loss - loss_src) ≤
      Real.rpow scale (-loss))
    (hdelta : 0 < delta') (hsigma : 0 < 1 - sigma) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (targetSlope z))
          (horizontalSlice targetUnion z))
        (scale * delta') (1 - sigma)
          (Kakeya.realRpowENN (scale * delta') (-loss)) := by
  intro z hz
  let sourceHeight := center 2 + z / scale
  by_cases hslice : (horizontalSlice targetUnion z).Nonempty
  · rcases hslice with ⟨target, htargetPoint, htargetHeight⟩
    have hsliceNonempty : (horizontalSlice targetUnion z).Nonempty :=
      ⟨target, htargetPoint, htargetHeight⟩
    rcases htarget htargetPoint with ⟨source, hsource, hsourceTarget⟩
    have hsourceHeight : source 2 = sourceHeight := by
      have hcoordinate := congrArg (fun point : Point3 => point 2)
        hsourceTarget
      simp only [wz1IsotropicRescalingMap, Pi.smul_apply] at hcoordinate
      rw [htargetHeight] at hcoordinate
      have hscaled : scale * (source 2 - center 2) = z := by
        exact hcoordinate
      change source 2 = center 2 + z / scale
      have hquotient : source 2 - center 2 = z / scale :=
        (eq_div_iff hscale.ne').2 (by simpa [mul_comm] using hscaled)
      linarith
    have hsourceBox := (shading.subset_body
      (Classical.choose hsource) (Classical.choose_spec hsource)).2
    have hheight : sourceHeight ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [← hsourceHeight]
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hsourceBox.2.2
    have hsourceAD := global_ad sourceHeight hheight
    let sourceSlice := horizontalSlice shading.union sourceHeight
    have hsliceImage : horizontalSlice targetUnion z ⊆
        wz1IsotropicRescalingMap center scale '' sourceSlice := by
      intro other hother
      rcases htarget hother.1 with ⟨sourceOther, hsourceOther, hmap⟩
      refine ⟨sourceOther, ⟨hsourceOther, ?_⟩, hmap⟩
      have hcoordinate := congrArg (fun point : Point3 => point 2) hmap
      simp only [wz1IsotropicRescalingMap, Pi.smul_apply] at hcoordinate
      rw [hother.2] at hcoordinate
      have hscaled : scale * (sourceOther 2 - center 2) = z := by
        exact hcoordinate
      change sourceOther 2 = center 2 + z / scale
      have hquotient : sourceOther 2 - center 2 = z / scale :=
        (eq_div_iff hscale.ne').2 (by simpa [mul_comm] using hscaled)
      linarith
    have hprojection : scalarProjection
          (globalGrainDirection (targetSlope z))
          (horizontalSlice targetUnion z) ⊆
        (fun value : ℝ => scale * value -
          scale * inner ℝ center
            (globalGrainDirection (slope sourceHeight))) ''
          scalarProjection (globalGrainDirection (slope sourceHeight))
            sourceSlice := by
      rw [hslope z hsliceNonempty, ← scalarProjection_rescaling hscale]
      intro value hvalue
      rcases hvalue with ⟨point, hpoint, rfl⟩
      exact ⟨point, hsliceImage hpoint, rfl⟩
    have hscaled := hsourceAD.smul hscale
    have htranslated := hscaled.translate
      (-scale * inner ℝ center
        (globalGrainDirection (slope sourceHeight)))
    have hconst : Kakeya.realRpowENN delta' (-loss_src) ≤
        Kakeya.realRpowENN (scale * delta') (-loss) :=
      ad_constant_comparison hdelta hscale hloss_lt hsmall
    have htranslated' := htranslated.mono_const hconst (by
      simp [Kakeya.realRpowENN])
    apply htranslated'.mono_set
    intro value hvalue
    rcases hprojection hvalue with ⟨sourceValue, hsourceValue, rfl⟩
    refine ⟨scale * sourceValue, ⟨sourceValue, hsourceValue, rfl⟩, ?_⟩
    ring
  · have hempty : horizontalSlice targetUnion z = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hslice
    have hbase := global_ad z hz
    have hscaled := hbase.smul hscale
    have hconst : Kakeya.realRpowENN delta' (-loss_src) ≤
        Kakeya.realRpowENN (scale * delta') (-loss) :=
      ad_constant_comparison hdelta hscale hloss_lt hsmall
    have hscaled' := hscaled.mono_const hconst (by
      simp [Kakeya.realRpowENN])
    apply hscaled'.mono_set
    rw [hempty]
    rintro value ⟨point, hpoint, rfl⟩
    exact False.elim hpoint
/-- Transport a local paper AD field through `p ↦ scale • (p - center)`. -/
lemma local_ad_transport_centered_general
    {sigma loss loss_src delta' : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading : WZ1PaperTubeShading family}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (local_ad : ∀ rho : ℝ, delta' ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩
              Metric.closedBall (point : Point3) (Real.sqrt rho)))
          rho (1 - sigma)
            (Kakeya.realRpowENN delta' (-loss_src)))
    {scale : ℝ} (hscale : 0 < scale) (hscaleOne : 1 ≤ scale)
    (center : Point3)
    {targetUnion : Set Point3}
    (htarget : targetUnion ⊆
      wz1IsotropicRescalingMap center scale '' shading.union)
    (targetPlaneMap : {point : Point3 // point ∈ targetUnion} → Point3)
    (hplane : ∀ point : {point : Point3 // point ∈ targetUnion},
      targetPlaneMap point = planeMap
        ⟨wz1IsotropicRescalingInverse center scale point, by
          rcases htarget point.prop with ⟨source, hsource, hpoint⟩
          have hinverse : wz1IsotropicRescalingInverse center scale
              (wz1IsotropicRescalingMap center scale source) = source := by
            ext coordinate
            simp [wz1IsotropicRescalingInverse,
              wz1IsotropicRescalingMap]
            field_simp [hscale.ne']
            ring
          rw [← hpoint, hinverse]
          exact hsource⟩)
    (hloss_src : 0 < loss_src) (hloss_lt : loss_src < loss)
    (hsmall : Real.rpow delta' (loss - loss_src) ≤
      Real.rpow scale (-loss))
    (hdelta : 0 < delta') (hsigma : 0 < 1 - sigma) :
    ∀ rho : ℝ, scale * delta' ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ targetUnion},
        PureWZ2PaperADSet1
          (scalarProjection (targetPlaneMap point)
            (targetUnion ∩
              Metric.closedBall (point : Point3) (Real.sqrt rho)))
          rho (1 - sigma)
            (Kakeya.realRpowENN (scale * delta') (-loss)) := by
  intro rho hrho hrhoOne point
  let sourcePoint : {source : Point3 // source ∈ shading.union} :=
    ⟨wz1IsotropicRescalingInverse center scale point, by
      rcases htarget point.prop with ⟨source, hsource, hpoint⟩
      have hinverse : wz1IsotropicRescalingInverse center scale
          (wz1IsotropicRescalingMap center scale source) = source := by
        ext coordinate
        simp [wz1IsotropicRescalingInverse, wz1IsotropicRescalingMap]
        field_simp [hscale.ne']
        ring
      rw [← hpoint, hinverse]
      exact hsource⟩
  let sourceScale := rho / scale
  have hsourceScale : delta' ≤ sourceScale := by
    dsimp only [sourceScale]
    calc
      delta' = (scale * delta') / scale := by field_simp [hscale.ne']
      _ ≤ rho / scale := by gcongr
  have hsourceScaleOne : sourceScale ≤ 1 := by
    dsimp only [sourceScale]
    calc
      rho / scale ≤ 1 / scale := by gcongr
      _ ≤ 1 := (div_le_one hscale).mpr hscaleOne
  let sourceSet := shading.union ∩ Metric.closedBall
    (sourcePoint : Point3) (Real.sqrt sourceScale)
  have hsourceAD := local_ad sourceScale hsourceScale hsourceScaleOne
    sourcePoint
  let targetSet := targetUnion ∩ Metric.closedBall
    (point : Point3) (Real.sqrt rho)
  have htargetImage : targetSet ⊆
      wz1IsotropicRescalingMap center scale '' sourceSet := by
    intro target htargetPoint
    rcases htarget htargetPoint.1 with ⟨source, hsource, hsourceTarget⟩
    refine ⟨source, ⟨hsource, ?_⟩, hsourceTarget⟩
    have hpointSource : (point : Point3) =
        wz1IsotropicRescalingMap center scale sourcePoint := by
      ext coordinate
      simp [sourcePoint, wz1IsotropicRescalingInverse,
        wz1IsotropicRescalingMap]
      field_simp [hscale.ne']
    have hdistScale : dist target (point : Point3) =
        scale * dist source (sourcePoint : Point3) := by
      calc
        dist target (point : Point3) =
            dist (wz1IsotropicRescalingMap center scale source)
              (wz1IsotropicRescalingMap center scale sourcePoint) := by
                rw [hsourceTarget, hpointSource]
        _ = scale * dist source (sourcePoint : Point3) := by
          rw [dist_eq_norm, dist_eq_norm]
          simp only [wz1IsotropicRescalingMap]
          have hdifference :
              scale • (source - center) -
                  scale • ((sourcePoint : Point3) - center) =
                scale • (source - (sourcePoint : Point3)) := by module
          rw [hdifference, norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
    have hdist : dist source (sourcePoint : Point3) ≤
        Real.sqrt rho / scale := by
      apply (le_div_iff₀ hscale).2
      rw [mul_comm, ← hdistScale]
      exact htargetPoint.2
    have hsqrt : Real.sqrt rho / scale ≤ Real.sqrt sourceScale := by
      have hrho : 0 ≤ rho := by linarith [mul_pos hscale hdelta]
      have hsqrtDiv : Real.sqrt sourceScale =
          Real.sqrt rho / Real.sqrt scale := by
        dsimp only [sourceScale]
        rw [Real.sqrt_div hrho]
      rw [hsqrtDiv]
      gcongr
      have hsqrtScale : Real.sqrt scale ≤ scale := by
        nlinarith [Real.sqrt_nonneg scale,
          Real.sq_sqrt hscale.le, hscaleOne]
      exact hsqrtScale
    exact hdist.trans hsqrt
  have hprojection : scalarProjection (targetPlaneMap point) targetSet ⊆
      (fun value : ℝ => scale * value -
        scale * inner ℝ center (planeMap sourcePoint)) ''
          scalarProjection (planeMap sourcePoint) sourceSet := by
    rw [hplane point, ← scalarProjection_rescaling hscale]
    intro value hvalue
    rcases hvalue with ⟨target, htargetValue, rfl⟩
    exact ⟨target, htargetImage htargetValue, rfl⟩
  have hscaled := hsourceAD.smul hscale
  have htranslated := hscaled.translate
    (-scale * inner ℝ center (planeMap sourcePoint))
  have hconst : Kakeya.realRpowENN delta' (-loss_src) ≤
      Kakeya.realRpowENN (scale * delta') (-loss) :=
    ad_constant_comparison hdelta hscale hloss_lt hsmall
  have htranslated' := htranslated.mono_const hconst (by
    simp [Kakeya.realRpowENN])
  have hrhoEq : scale * sourceScale = rho := by
    dsimp only [sourceScale]
    field_simp [hscale.ne']
  rw [hrhoEq] at htranslated'
  apply htranslated'.mono_set
  intro value hvalue
  rcases hprojection hvalue with
    ⟨sourceValue, hsourceValue, rfl⟩
  refine ⟨scale * sourceValue, ⟨sourceValue, hsourceValue, rfl⟩, ?_⟩
  ring

end Kakeya.Assouad

end
