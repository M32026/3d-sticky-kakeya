import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicExactImage
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.InverseTransposeNormal
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Exact-image plane map for the Section-6 affine change

This is the geometric half of the local-grain transport.  It is deliberately
formed on the exact affine image, before the target cubical saturation.  The
normal is the normalized inverse transpose of the projected source plane map.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- The exact affine image has a canonical source preimage at every shaded
point. -/
def PureWZ2AnisotropicPaperRetubingData.exactSourcePoint
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm)
    (target : {point : Point3 // point ∈ raw.exactShading.union}) :
    {point : Point3 // point ∈ sourceShading.union} :=
  ⟨(anisotropicCenteredRescalingAffineEquiv
      g c d m center hcd hm).symm target, by
    have htargetImage : target.1 ∈
        anisotropicCenteredRescalingMap g c d m center ''
          sourceShading.union := by
      rw [← raw.exactShading_union]
      exact target.property
    rcases htargetImage with ⟨source, hsource, heq⟩
    have htarget : target.1 =
        anisotropicCenteredRescalingAffineEquiv
          g c d m center hcd hm source := by
      rw [anisotropicCenteredRescalingAffineEquiv_apply]
      exact heq.symm
    rw [htarget, AffineEquiv.symm_apply_apply]
    exact hsource⟩

@[simp] theorem PureWZ2AnisotropicPaperRetubingData.map_exactSourcePoint
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm)
    (target : {point : Point3 // point ∈ raw.exactShading.union}) :
    anisotropicCenteredRescalingMap g c d m center
        (raw.exactSourcePoint target) = target := by
  rw [← anisotropicCenteredRescalingAffineEquiv_apply]
  exact AffineEquiv.apply_symm_apply _ _

/-- Exact-image normal obtained by applying the literal inverse transpose and
normalizing. -/
def PureWZ2AnisotropicPaperRetubingData.exactPlaneMap
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm)
    (sourcePlaneMap :
      {point : Point3 // point ∈ sourceShading.union} → Point3)
    (target : {point : Point3 // point ∈ raw.exactShading.union}) : Point3 :=
  let transported := dPhiInvT g c d m
    (sourcePlaneMap (raw.exactSourcePoint target))
  (‖transported‖⁻¹ : ℝ) • transported

theorem PureWZ2AnisotropicPaperRetubingData.exactPlaneMap_unit
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm)
    (sourcePlaneMap :
      {point : Point3 // point ∈ sourceShading.union} → Point3)
    (hsourceUnit : ∀ point, ‖sourcePlaneMap point‖ = 1)
    (target : {point : Point3 // point ∈ raw.exactShading.union}) :
    ‖raw.exactPlaneMap sourcePlaneMap target‖ = 1 := by
  let source := raw.exactSourcePoint target
  let transported := dPhiInvT g c d m (sourcePlaneMap source)
  have hsourceNonzero : sourcePlaneMap source ≠ 0 := by
    intro hzero
    have := hsourceUnit source
    rw [hzero, norm_zero] at this
    norm_num at this
  have htransportedNonzero : transported ≠ 0 := by
    exact fun hzero => hsourceNonzero <|
      dPhiInvT_injective g c d m hcd hm <| by
        rw [show dPhiInvT g c d m (sourcePlaneMap source) = transported by rfl,
          hzero]
        simp [dPhiInvT, point3]
  have hnorm : 0 < ‖transported‖ := norm_pos_iff.mpr htransportedNonzero
  change ‖(‖transported‖⁻¹ : ℝ) • transported‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp [hnorm.ne']

/-- The source-preimage map of the exact affine image has the finite
Lipschitz constant supplied by the inverse linear equivalence. -/
theorem PureWZ2AnisotropicPaperRetubingData.exactSourcePoint_lipschitz
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm) :
    LipschitzWith
      ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖₊
      raw.exactSourcePoint := by
  let inverseLinear :=
    (anisotropicRescalingLinearEquiv g c d m hcd hm).symm
      |>.toContinuousLinearEquiv
  apply LipschitzWith.of_dist_le_mul
  intro first second
  let affine := anisotropicCenteredRescalingAffineEquiv
    g c d m center hcd hm
  have hfirst : (raw.exactSourcePoint first : Point3) = affine.symm first := rfl
  have hsecond : (raw.exactSourcePoint second : Point3) = affine.symm second := rfl
  have hsub : affine.symm first - affine.symm second =
      inverseLinear ((first : Point3) - (second : Point3)) := by
    have h := AffineMap.linearMap_vsub affine.symm.toAffineMap
      (first : Point3) (second : Point3)
    change affine.symm.linear (first.1 - second.1) =
      affine.symm first.1 - affine.symm second.1 at h
    rw [AffineEquiv.linear_symm affine] at h
    dsimp only [affine] at h
    rw [anisotropicCenteredRescalingAffineEquiv_linear] at h
    change
      (anisotropicCenteredRescalingAffineEquiv g c d m center hcd hm).symm
          first.1 -
        (anisotropicCenteredRescalingAffineEquiv g c d m center hcd hm).symm
          second.1 =
      (anisotropicRescalingLinearEquiv g c d m hcd hm).symm
        (first.1 - second.1)
    exact h.symm
  have hlinear := inverseLinear.lipschitz.dist_le_mul
    (first : Point3) (second : Point3)
  rw [Subtype.dist_eq, hfirst, hsecond, dist_eq_norm, hsub]
  rw [dist_eq_norm, ← map_sub] at hlinear
  simpa only [inverseLinear, Subtype.dist_eq] using hlinear

/-- The inverse-transpose map is globally Lipschitz with its finite-dimensional
operator norm. -/
theorem dPhiInvT_lipschitz
    (g : SlopeFunction) (c d m : ℝ) :
    LipschitzWith
      ‖(dPhiInvTLinear g c d m).toContinuousLinearMap‖₊
      (dPhiInvT g c d m) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm, dist_eq_norm, ← dPhiInvT_sub]
  have hop := (dPhiInvTLinear g c d m).toContinuousLinearMap.le_opNorm
    (first - second)
  have happly :
      (dPhiInvTLinear g c d m).toContinuousLinearMap (first - second) =
        dPhiInvT g c d m (first - second) := by
    change dPhiInvTLinear g c d m (first - second) = _
    rfl
  rw [happly] at hop
  simpa only [coe_nnnorm] using hop

/-- Operator-norm form of the coordinate estimate for the inverse transpose. -/
theorem dPhiInvTLinear_opNorm_le
    (g : SlopeFunction) (c d m : ℝ)
    (hcd : c < d) (hm : 0 < m) (hmOne : m ≤ 1)
    (hdc : d - c ≤ 1 / 25)
    (hg : g.IsNormalized)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1) :
    ‖(dPhiInvTLinear g c d m).toContinuousLinearMap‖ ≤
      Real.sqrt 6 / (m * (d - c) / 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro vector
  exact dPhiInvT_opNorm_bound g c d m hcd hm hmOne hdc hg hsub vector

/-- The inverse linear map is adjoint to the inverse-transpose formula. -/
theorem dPhiInvTLinear_eq_adjoint_inverse
    (g : SlopeFunction) (c d m : ℝ)
    (hcd : c < d) (hm : 0 < m) :
    (dPhiInvTLinear g c d m).toContinuousLinearMap =
      ContinuousLinearMap.adjoint
        ((anisotropicRescalingLinearEquiv g c d m hcd hm).symm
          |>.toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro normal target
  have hinverse : dPhiLin g c d m
      ((anisotropicRescalingLinearEquiv g c d m hcd hm).symm target) =
        target := by
    rw [← anisotropicRescalingLinearMap_apply_eq_dPhiLin,
      ← anisotropicRescalingLinearEquiv_apply]
    exact (anisotropicRescalingLinearEquiv g c d m hcd hm).apply_symm_apply
      target
  have hinner := dPhi_inner_identity g c d m hcd hm
    ((anisotropicRescalingLinearEquiv g c d m hcd hm).symm target) normal
  rw [hinverse] at hinner
  change inner ℝ (dPhiInvT g c d m normal) target =
    inner ℝ normal
      ((anisotropicRescalingLinearEquiv g c d m hcd hm).symm target)
  exact (real_inner_comm (dPhiInvT g c d m normal) target).symm.trans <|
    hinner.trans <|
      (real_inner_comm
        ((anisotropicRescalingLinearEquiv g c d m hcd hm).symm target)
        normal).symm

/-- The inverse linear equivalence has the same quantitative norm bound as
its inverse transpose. -/
theorem anisotropicRescalingLinearEquiv_symm_opNorm_le
    (g : SlopeFunction) (c d m : ℝ)
    (hcd : c < d) (hm : 0 < m) (hmOne : m ≤ 1)
    (hdc : d - c ≤ 1 / 25)
    (hg : g.IsNormalized)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1) :
    ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤
      Real.sqrt 6 / (m * (d - c) / 2) := by
  let inverse :=
    (anisotropicRescalingLinearEquiv g c d m hcd hm).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap
  calc
    ‖inverse‖ = ‖ContinuousLinearMap.adjoint inverse‖ :=
      (LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint inverse).symm
    _ = ‖(dPhiInvTLinear g c d m).toContinuousLinearMap‖ := by
      rw [dPhiInvTLinear_eq_adjoint_inverse g c d m hcd hm]
    _ ≤ Real.sqrt 6 / (m * (d - c) / 2) :=
      dPhiInvTLinear_opNorm_le g c d m hcd hm hmOne hdc hg hsub

/-- Normalize an inverse-transpose field once a uniform lower norm bound is
available.  The displayed constant is intentionally explicit: the following
isotropic Lemma-8 step will absorb it into its dilation scale. -/
theorem PureWZ2AnisotropicPaperRetubingData.exactPlaneMap_lipschitz
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm)
    (sourcePlaneMap :
      {point : Point3 // point ∈ sourceShading.union} → Point3)
    {sourceK : NNReal}
    (hsourceLipschitz : LipschitzWith sourceK sourcePlaneMap)
    {lower : ℝ} (hlower : 0 < lower)
    (hnormalLower : ∀ point,
      lower ≤ ‖dPhiInvT g c d m (sourcePlaneMap point)‖) :
    LipschitzWith
      (⟨2 / lower, by positivity⟩ *
        ‖(dPhiInvTLinear g c d m).toContinuousLinearMap‖₊ *
        sourceK *
        ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
            |>.toContinuousLinearEquiv.toContinuousLinearMap‖₊)
      (raw.exactPlaneMap sourcePlaneMap) := by
  let sourceMap := raw.exactSourcePoint
  let unnormalized :
      {point : Point3 // point ∈ raw.exactShading.union} → Point3 :=
    fun point => dPhiInvT g c d m (sourcePlaneMap (sourceMap point))
  let sourcePreimageK :=
    ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap‖₊
  let inverseTransposeK :=
    ‖(dPhiInvTLinear g c d m).toContinuousLinearMap‖₊
  let normalizationK : NNReal := ⟨2 / lower, by positivity⟩
  have hsourceMap : LipschitzWith sourcePreimageK sourceMap := by
    simpa only [sourceMap, sourcePreimageK] using raw.exactSourcePoint_lipschitz
  have hunnormalized :
      LipschitzWith (inverseTransposeK * sourceK * sourcePreimageK)
        unnormalized := by
    have hlinear : LipschitzWith inverseTransposeK (dPhiInvT g c d m) := by
      simpa only [inverseTransposeK] using dPhiInvT_lipschitz g c d m
    simpa only [unnormalized, sourceMap, Function.comp_def, mul_assoc] using
      hlinear.comp (hsourceLipschitz.comp hsourceMap)
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hnormal := normalization_lipschitz
    (x := unnormalized first) (y := unnormalized second)
    hlower (hnormalLower (sourceMap first)) (hnormalLower (sourceMap second))
  have hraw := hunnormalized.dist_le_mul first second
  change dist (raw.exactPlaneMap sourcePlaneMap first)
      (raw.exactPlaneMap sourcePlaneMap second) ≤ _
  rw [dist_eq_norm]
  calc
    ‖raw.exactPlaneMap sourcePlaneMap first -
        raw.exactPlaneMap sourcePlaneMap second‖
        ≤ (2 / lower) *
            ‖unnormalized first - unnormalized second‖ := by
          simpa only [PureWZ2AnisotropicPaperRetubingData.exactPlaneMap,
            unnormalized, sourceMap] using hnormal
    _ ≤ (2 / lower) *
        (((inverseTransposeK * sourceK * sourcePreimageK : NNReal) : ℝ) *
          dist first second) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [dist_eq_norm] using hraw
    _ = ((normalizationK * inverseTransposeK * sourceK *
          sourcePreimageK : NNReal) : ℝ) * dist first second := by
      change (2 / lower) *
          ((inverseTransposeK : ℝ) * (sourceK : ℝ) *
            (sourcePreimageK : ℝ) * dist first second) = _
      rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_mul]
      change (2 / lower) *
          ((inverseTransposeK : ℝ) * (sourceK : ℝ) *
            (sourcePreimageK : ℝ) * dist first second) =
        (2 / lower * (inverseTransposeK : ℝ) * (sourceK : ℝ) *
          (sourcePreimageK : ℝ)) * dist first second
      ring

theorem PureWZ2AnisotropicPaperRetubingData.exactPlaneMap_incidence_source
    {sourceDelta targetDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (hproductLower : ∀ index point
      (hpoint : point ∈ sourceShading.carrier index),
        1 / 3 ≤
          ‖dPhiLin g c d m
            (wz1PaperDirection (sourceFamily.tube index))‖ *
          ‖dPhiInvT g c d m
            (sourceLocal.planeMap
              ⟨point, ⟨index, hpoint⟩⟩)‖) :
    ∀ index point,
      ∀ hpoint : point ∈ raw.exactShading.carrier index,
        |inner ℝ
            ((anisotropicPaperTargetFamily sourceFamily g c d m center
              targetDelta hcd hm).tube index).direction
            (raw.exactPlaneMap sourceLocal.planeMap
              ⟨point, ⟨index, hpoint⟩⟩)| ≤ 3 * sourceDelta := by
  intro index point hpoint
  rcases hpoint with ⟨sourcePoint, hsourcePoint, heq⟩
  let target : {point : Point3 // point ∈ raw.exactShading.union} :=
    ⟨point, ⟨index, sourcePoint, hsourcePoint, heq⟩⟩
  let source : {point : Point3 // point ∈ sourceShading.union} :=
    raw.exactSourcePoint target
  have hsourceEq : (source : Point3) = sourcePoint := by
    apply (anisotropicCenteredRescalingAffineEquiv
      g c d m center hcd hm).injective
    rw [anisotropicCenteredRescalingAffineEquiv_apply,
      anisotropicCenteredRescalingAffineEquiv_apply,
      raw.map_exactSourcePoint]
    exact heq.symm
  have hsourceCarrier : (source : Point3) ∈
      sourceShading.carrier index := by
    rwa [hsourceEq]
  have hsourceSubtypeEq : source =
      ⟨sourcePoint, ⟨index, hsourcePoint⟩⟩ := by
    apply Subtype.ext
    exact hsourceEq
  let directionImage := dPhiLin g c d m
    (wz1PaperDirection (sourceFamily.tube index))
  let normalImage := dPhiInvT g c d m (sourceLocal.planeMap source)
  have hdirectionPos : 0 < ‖directionImage‖ :=
    by
      have hproduct := hproductLower index (source : Point3) hsourceCarrier
      nlinarith [norm_nonneg directionImage, norm_nonneg normalImage]
  have hnormalPos : 0 < ‖normalImage‖ :=
    by
      have hproduct := hproductLower index (source : Point3) hsourceCarrier
      nlinarith [norm_nonneg directionImage, norm_nonneg normalImage]
  have hinner : inner ℝ directionImage normalImage =
      inner ℝ (wz1PaperDirection (sourceFamily.tube index))
        (sourceLocal.planeMap source) :=
    dPhi_inner_identity g c d m hcd hm _ _
  have hsourceIncidence := sourceLocal.planeMap_incidence
    index (source : Point3) hsourceCarrier
  have hsourceIncidencePaper :
      |inner ℝ (wz1PaperDirection (sourceFamily.tube index))
          (sourceLocal.planeMap source)| ≤ sourceDelta := by
    unfold wz1PaperDirection
    split_ifs
    · exact hsourceIncidence
    · simpa [inner_neg_left, abs_neg] using hsourceIncidence
  have htargetDirection :
      ((anisotropicPaperTargetFamily sourceFamily g c d m center
        targetDelta hcd hm).tube index).direction =
        (‖directionImage‖⁻¹ : ℝ) • directionImage := by
    rfl
  have htargetNormal :
      raw.exactPlaneMap sourceLocal.planeMap
          ⟨point, ⟨index, ⟨sourcePoint, hsourcePoint, heq⟩⟩⟩ =
        (‖normalImage‖⁻¹ : ℝ) • normalImage := by
    simp only [PureWZ2AnisotropicPaperRetubingData.exactPlaneMap]
    rw [show raw.exactSourcePoint target = source by rfl]
  rw [htargetDirection, htargetNormal]
  have hnormalized :
      |inner ℝ
          ((‖directionImage‖⁻¹ : ℝ) • directionImage)
          ((‖normalImage‖⁻¹ : ℝ) • normalImage)| =
        |inner ℝ directionImage normalImage| /
          (‖directionImage‖ * ‖normalImage‖) := by
    have hdabs : |(‖directionImage‖⁻¹ : ℝ)| =
        ‖directionImage‖⁻¹ := abs_of_pos (inv_pos.mpr hdirectionPos)
    have hnabs : |(‖normalImage‖⁻¹ : ℝ)| =
        ‖normalImage‖⁻¹ := abs_of_pos (inv_pos.mpr hnormalPos)
    rw [inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial, abs_mul, hdabs, hnabs]
    field_simp [hdirectionPos.ne', hnormalPos.ne']
  rw [hnormalized, hinner]
  have hdenom : 1 / 3 ≤ ‖directionImage‖ * ‖normalImage‖ := by
    simpa [directionImage, normalImage] using
      hproductLower index (source : Point3) hsourceCarrier
  calc
    |inner ℝ (wz1PaperDirection (sourceFamily.tube index))
        (sourceLocal.planeMap source)| /
          (‖directionImage‖ * ‖normalImage‖)
        ≤ 3 * |inner ℝ (wz1PaperDirection (sourceFamily.tube index))
            (sourceLocal.planeMap source)| := by
          have htwo :
              |inner ℝ (wz1PaperDirection (sourceFamily.tube index))
                  (sourceLocal.planeMap source)| /
                    (‖directionImage‖ * ‖normalImage‖) ≤
                3 * |inner ℝ (wz1PaperDirection (sourceFamily.tube index))
                  (sourceLocal.planeMap source)| := by
            apply (div_le_iff₀ (by positivity)).2
            nlinarith [abs_nonneg (inner ℝ
              (wz1PaperDirection (sourceFamily.tube index))
              (sourceLocal.planeMap source))]
          exact htwo
    _ ≤ 3 * sourceDelta := by gcongr

/-- The exact incidence estimate, weakened only when a caller actually needs
the target tube scale.  Keeping the preceding `3 * sourceDelta` estimate
available is essential when cubical saturation later spends a positive
normal-perturbation budget. -/
theorem PureWZ2AnisotropicPaperRetubingData.exactPlaneMap_incidence
    {sourceDelta targetDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (hproductLower : ∀ index point
      (hpoint : point ∈ sourceShading.carrier index),
        1 / 3 ≤
          ‖dPhiLin g c d m
            (wz1PaperDirection (sourceFamily.tube index))‖ *
          ‖dPhiInvT g c d m
            (sourceLocal.planeMap
              ⟨point, ⟨index, hpoint⟩⟩)‖)
    (hsourceTarget : 3 * sourceDelta ≤ targetDelta) :
    ∀ index point,
      ∀ hpoint : point ∈ raw.exactShading.carrier index,
        |inner ℝ
            ((anisotropicPaperTargetFamily sourceFamily g c d m center
              targetDelta hcd hm).tube index).direction
            (raw.exactPlaneMap sourceLocal.planeMap
              ⟨point, ⟨index, hpoint⟩⟩)| ≤ targetDelta := by
  intro index point hpoint
  exact (raw.exactPlaneMap_incidence_source sourceLocal hproductLower
    index point hpoint).trans hsourceTarget

/-- The exact-image inverse-transpose plane field, packaged with all of its
pointwise geometric data and an explicit finite Lipschitz constant.  Local AD
is intentionally not asserted at this intermediate scale: it is transported
only after the following isotropic normalization, exactly as in paper Lemma 8. -/
structure PureWZ2AnisotropicExactPlaneMapData
    {sourceDelta targetDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C) where
  K : NNReal
  planeMap : {point : Point3 // point ∈ raw.exactShading.union} → Point3
  planeMap_eq : planeMap = raw.exactPlaneMap sourceLocal.planeMap
  planeMap_lipschitz : LipschitzWith K planeMap
  planeMap_unit : ∀ point, ‖planeMap point‖ = 1
  planeMap_incidence_source :
    ∀ index point,
      ∀ hpoint : point ∈ raw.exactShading.carrier index,
        |inner ℝ
            ((anisotropicPaperTargetFamily sourceFamily g c d m center
              targetDelta hcd hm).tube index).direction
            (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ 3 * sourceDelta
  planeMap_incidence :
    ∀ index point,
      ∀ hpoint : point ∈ raw.exactShading.carrier index,
        |inner ℝ
            ((anisotropicPaperTargetFamily sourceFamily g c d m center
              targetDelta hcd hm).tube index).direction
            (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ targetDelta

/-- Canonical exact-image plane-map package.  Keeping this as a transparent
definition exposes its finite Lipschitz constant to the final scalar budget. -/
def PureWZ2AnisotropicPaperRetubingData.exactPlaneMapData
    {sourceDelta targetDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    {lower : ℝ} (hlower : 0 < lower)
    (hnormalLower : ∀ point,
      lower ≤ ‖dPhiInvT g c d m (sourceLocal.planeMap point)‖)
    (hproductLower : ∀ index point
      (hpoint : point ∈ sourceShading.carrier index),
        1 / 3 ≤
          ‖dPhiLin g c d m
            (wz1PaperDirection (sourceFamily.tube index))‖ *
          ‖dPhiInvT g c d m
            (sourceLocal.planeMap
              ⟨point, ⟨index, hpoint⟩⟩)‖)
    (hsourceTarget : 3 * sourceDelta ≤ targetDelta) :
    PureWZ2AnisotropicExactPlaneMapData raw sourceLocal := by
  let K : NNReal :=
    ⟨2 / lower, by positivity⟩ *
      ‖(dPhiInvTLinear g c d m).toContinuousLinearMap‖₊ *
      1 *
      ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖₊
  exact {
    K := K
    planeMap := raw.exactPlaneMap sourceLocal.planeMap
    planeMap_eq := rfl
    planeMap_lipschitz := by
      simpa only [K] using raw.exactPlaneMap_lipschitz
        sourceLocal.planeMap sourceLocal.planeMap_lipschitz
          hlower hnormalLower
    planeMap_unit := raw.exactPlaneMap_unit sourceLocal.planeMap
      sourceLocal.planeMap_unit
    planeMap_incidence_source := raw.exactPlaneMap_incidence_source
      sourceLocal hproductLower
    planeMap_incidence := raw.exactPlaneMap_incidence sourceLocal
      hproductLower hsourceTarget
  }

/-- Assemble the exact-image plane-map package from the source local grains
and quantitative nondegeneracy of the inverse-transpose images. -/
theorem PureWZ2AnisotropicPaperRetubingData.toExactPlaneMapData
    {sourceDelta targetDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    {lower : ℝ} (hlower : 0 < lower)
    (hnormalLower : ∀ point,
      lower ≤ ‖dPhiInvT g c d m (sourceLocal.planeMap point)‖)
    (hproductLower : ∀ index point
      (hpoint : point ∈ sourceShading.carrier index),
        1 / 3 ≤
          ‖dPhiLin g c d m
            (wz1PaperDirection (sourceFamily.tube index))‖ *
          ‖dPhiInvT g c d m
            (sourceLocal.planeMap
              ⟨point, ⟨index, hpoint⟩⟩)‖)
    (hsourceTarget : 3 * sourceDelta ≤ targetDelta) :
    Nonempty (PureWZ2AnisotropicExactPlaneMapData raw sourceLocal) :=
  ⟨raw.exactPlaneMapData sourceLocal hlower hnormalLower hproductLower
    hsourceTarget⟩

end Kakeya.Assouad

end
