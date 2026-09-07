import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicADTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ADTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingStatements

/-!
# Pure paper local AD under an isotropic similarity

This is the paper-carrier analogue of the closed WZ1 mild-rescaling local-AD
leaf.  It keeps the actual source witness of every target point and transports
the source plane normal through the positive similarity.  No bounded-diameter
replacement is used.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- The positive isotropic similarity used before the final diagonal map. -/
def pureWZ2IsotropicMap (center : Point3) (scale : ℝ)
    (point : Point3) : Point3 :=
  scale • (point - center)

/-- Its inverse. -/
def pureWZ2IsotropicInverse (center : Point3) (scale : ℝ)
    (point : Point3) : Point3 :=
  center + scale⁻¹ • point

@[simp] theorem pureWZ2IsotropicMap_inverse
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (point : Point3) :
    pureWZ2IsotropicMap center scale
        (pureWZ2IsotropicInverse center scale point) = point := by
  simp only [pureWZ2IsotropicMap, pureWZ2IsotropicInverse]
  have hsub : center + scale⁻¹ • point - center =
      scale⁻¹ • point := by abel
  rw [hsub, smul_smul]
  have hmul : scale * scale⁻¹ = 1 := by field_simp [hscale.ne']
  rw [hmul, one_smul]

@[simp] theorem pureWZ2IsotropicInverse_map
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (point : Point3) :
    pureWZ2IsotropicInverse center scale
        (pureWZ2IsotropicMap center scale point) = point := by
  simp only [pureWZ2IsotropicMap, pureWZ2IsotropicInverse, smul_smul]
  have hmul : scale⁻¹ * scale = 1 := by field_simp [hscale.ne']
  rw [hmul, one_smul]
  abel

/-- A target `sqrt rho` ball pulls back inside the source local-grain ball at
scale `rho / scale` when `scale ≥ 1`. -/
theorem pureWZ2Isotropic_preimage_ball
    (center : Point3) {scale rho : ℝ}
    (hscale : 1 ≤ scale) (hrho : 0 < rho)
    {sourcePoint targetPoint : Point3}
    (htarget : targetPoint =
      pureWZ2IsotropicMap center scale sourcePoint) :
    pureWZ2IsotropicInverse center scale ''
        Metric.closedBall targetPoint (Real.sqrt rho) ⊆
      Metric.closedBall sourcePoint (Real.sqrt (rho / scale)) := by
  intro source hsource
  rcases hsource with ⟨target, htargetBall, rfl⟩
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  let source := pureWZ2IsotropicInverse center scale target
  have htargetMap : pureWZ2IsotropicMap center scale source = target :=
    pureWZ2IsotropicMap_inverse center hscalePos target
  have hsourceMap :
      pureWZ2IsotropicMap center scale sourcePoint = targetPoint :=
    htarget.symm
  have hscaleDist : dist target targetPoint =
      scale * dist source sourcePoint := by
    rw [← htargetMap, ← hsourceMap]
    simp only [pureWZ2IsotropicMap, dist_eq_norm]
    have hdiff : scale • (source - center) -
          scale • (sourcePoint - center) =
        scale • (source - sourcePoint) := by
      rw [← smul_sub]
      congr 1
      abel
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hscalePos]
  have hdistEq : dist source sourcePoint =
      dist target targetPoint / scale := by
    rw [hscaleDist]
    field_simp [hscalePos.ne']
  have hsqrt : Real.sqrt rho / scale ≤ Real.sqrt (rho / scale) := by
    have hleft : 0 ≤ Real.sqrt rho / scale := by positivity
    have hright : 0 ≤ Real.sqrt (rho / scale) := Real.sqrt_nonneg _
    have hsquares : (Real.sqrt rho / scale) ^ 2 ≤
        (Real.sqrt (rho / scale)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hrho.le,
        Real.sq_sqrt (div_nonneg hrho.le hscalePos.le)]
      have hsquare : scale ≤ scale ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_left hrho.le
        (by positivity) hsquare
    nlinarith
  rw [Metric.mem_closedBall, hdistEq]
  exact (div_le_div_of_nonneg_right htargetBall hscalePos.le).trans hsqrt

/-- Genuine local-AD transport through a positive isotropic similarity.

The target set is required to retain an actual source preimage, and the target
normal is the source plane-map value at the preimage of the distinguished
target point. -/
theorem pureWZ2_isotropic_local_ad_of_fields
    {sourceDelta sigma scale rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourcePlaneMap :
      {point : Point3 // point ∈ sourceShading.union} → Point3)
    (sourcePlaneMapUnit : ∀ point, ‖sourcePlaneMap point‖ = 1)
    (sourceLocalAD : ∀ sourceRho : ℝ, sourceDelta ≤ sourceRho →
      sourceRho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ sourceShading.union},
        PureWZ2PaperADSet1
          (scalarProjection (sourcePlaneMap point)
            (sourceShading.union ∩
              Metric.closedBall (point : Point3) (Real.sqrt sourceRho)))
          sourceRho (1 - sigma) C)
    (center : Point3)
    (hsourceDelta : 0 < sourceDelta)
    (hscale : 1 ≤ scale)
    (hscaleDelta : scale * sourceDelta ≤ rho)
    (hrhoOne : rho ≤ 1)
    {targetSet : Set Point3}
    (htarget : targetSet ⊆
      pureWZ2IsotropicMap center scale '' sourceShading.union)
    (sourcePoint : {point : Point3 // point ∈ sourceShading.union})
    (targetPoint : Point3)
    (htargetPoint : targetPoint =
      pureWZ2IsotropicMap center scale sourcePoint) :
    PureWZ2PaperADSet1
      (scalarProjection
        (sourcePlaneMap sourcePoint)
        (targetSet ∩ Metric.closedBall targetPoint (Real.sqrt rho)))
      rho (1 - sigma) C := by
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  have hrho : 0 < rho := by
    exact (mul_pos hscalePos hsourceDelta).trans_le hscaleDelta
  let sourceRho := rho / scale
  have hsourceRhoLower : sourceDelta ≤ sourceRho := by
    dsimp only [sourceRho]
    calc
      sourceDelta = (scale * sourceDelta) / scale := by
        field_simp [hscalePos.ne']
      _ ≤ rho / scale := div_le_div_of_nonneg_right
        hscaleDelta hscalePos.le
  have hsourceRhoOne : sourceRho ≤ 1 := by
    dsimp only [sourceRho]
    exact (div_le_self hrho.le hscale).trans
      hrhoOne
  have hsourceAD := sourceLocalAD sourceRho hsourceRhoLower
    hsourceRhoOne sourcePoint
  let sourceSet := sourceShading.union ∩
    Metric.closedBall (sourcePoint : Point3) (Real.sqrt sourceRho)
  let targetLocalSet := targetSet ∩
    Metric.closedBall targetPoint (Real.sqrt rho)
  have hpullback : pureWZ2IsotropicInverse center scale '' targetLocalSet ⊆
      sourceSet := by
    rintro source ⟨target, htargetLocal, rfl⟩
    have hsourceUnion : pureWZ2IsotropicInverse center scale target ∈
        sourceShading.union := by
      rcases htarget htargetLocal.1 with ⟨point, hpoint, heq⟩
      have hinverse : pureWZ2IsotropicInverse center scale target = point := by
        rw [← heq, pureWZ2IsotropicInverse_map center hscalePos]
      rwa [hinverse]
    refine ⟨hsourceUnion, ?_⟩
    apply pureWZ2Isotropic_preimage_ball center hscale hrho
      (targetPoint := targetPoint) (sourcePoint := (sourcePoint : Point3))
      htargetPoint
    exact ⟨target, htargetLocal.2, rfl⟩
  let normal := sourcePlaneMap sourcePoint
  have hprojection : scalarProjection normal targetLocalSet ⊆
      (fun value : ℝ => scale * value -
        scale * inner ℝ center normal) ''
        scalarProjection normal sourceSet := by
    rintro value ⟨target, htargetLocal, rfl⟩
    rcases htarget htargetLocal.1 with ⟨source, hsource, heq⟩
    have hsourceBall : source ∈ sourceSet := by
      have hinverse : pureWZ2IsotropicInverse center scale target = source := by
        rw [← heq, pureWZ2IsotropicInverse_map center hscalePos]
      have himage : pureWZ2IsotropicInverse center scale target ∈ sourceSet :=
        hpullback ⟨target, htargetLocal, rfl⟩
      rwa [hinverse] at himage
    refine ⟨inner ℝ source normal, ⟨source, hsourceBall, rfl⟩, ?_⟩
    rw [← heq]
    simp only [pureWZ2IsotropicMap, real_inner_smul_left, inner_sub_left]
    ring
  have haffine := hsourceAD.affine_transfer
    (a := scale) (b := -(scale * inner ℝ center normal)) hscalePos
  have hscaleBase : scale * sourceRho = rho := by
    dsimp only [sourceRho]
    field_simp [hscalePos.ne']
  rw [hscaleBase] at haffine
  exact haffine.weaken_subset hprojection

/-- The fieldwise transport above specializes to the frozen local-grain
record.  Keeping this wrapper preserves the public API used by the existing
isotropic-rescaling assembly. -/
theorem pureWZ2_isotropic_local_ad
    {sourceDelta sigma scale rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (center : Point3)
    (hsourceDelta : 0 < sourceDelta)
    (hscale : 1 ≤ scale)
    (hscaleDelta : scale * sourceDelta ≤ rho)
    (hrhoOne : rho ≤ 1)
    {targetSet : Set Point3}
    (htarget : targetSet ⊆
      pureWZ2IsotropicMap center scale '' sourceShading.union)
    (sourcePoint : {point : Point3 // point ∈ sourceShading.union})
    (targetPoint : Point3)
    (htargetPoint : targetPoint =
      pureWZ2IsotropicMap center scale sourcePoint) :
    PureWZ2PaperADSet1
      (scalarProjection
        (sourceLocal.planeMap sourcePoint)
        (targetSet ∩ Metric.closedBall targetPoint (Real.sqrt rho)))
      rho (1 - sigma) C :=
  pureWZ2_isotropic_local_ad_of_fields
    sourceLocal.planeMap sourceLocal.planeMap_unit sourceLocal.local_ad
    center hsourceDelta hscale hscaleDelta hrhoOne htarget
    sourcePoint targetPoint htargetPoint

/-- Assemble the full pure local-grain record after a positive isotropic
similarity.  Every target carrier keeps its actual source parent, so both the
incidence and local-AD fields use genuine source data. -/
theorem pureWZ2_isotropic_local_grains
    {sourceDelta sigma scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (center : Point3)
    (hsourceDelta : 0 < sourceDelta)
    (hscale : 1 ≤ scale)
    {targetFamily : Kakeya.Streamlined.TubeFamily (scale * sourceDelta)}
    (targetShading : WZ1PaperTubeShading targetFamily)
    (sourceParent : Fin targetFamily.card → Fin sourceFamily.card)
    (hdirection : ∀ index, (targetFamily.tube index).direction =
      (sourceFamily.tube (sourceParent index)).direction)
    (hcarrier : ∀ index, targetShading.carrier index ⊆
      pureWZ2IsotropicMap center scale ''
        sourceShading.carrier (sourceParent index)) :
    Nonempty (PureWZ2LocalGrainData targetShading sigma C) := by
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  let inverse :
      {point : Point3 // point ∈ targetShading.union} →
        {point : Point3 // point ∈ sourceShading.union} := fun target =>
    ⟨pureWZ2IsotropicInverse center scale target, by
      rcases target.property with ⟨index, hpoint⟩
      rcases hcarrier index hpoint with ⟨source, hsource, heq⟩
      have hinverse : pureWZ2IsotropicInverse center scale target = source := by
        rw [← heq, pureWZ2IsotropicInverse_map center hscalePos]
      rw [hinverse]
      exact ⟨sourceParent index, hsource⟩⟩
  let targetPlaneMap :
      {point : Point3 // point ∈ targetShading.union} → Point3 :=
    fun target => sourceLocal.planeMap (inverse target)
  have hinverseLipschitz : LipschitzWith 1 inverse := by
    intro first second
    simp only [inverse, Subtype.edist_eq, Subtype.dist_eq, edist_dist,
      ENNReal.coe_one, one_mul]
    apply ENNReal.ofReal_le_ofReal
    simp only [pureWZ2IsotropicInverse, dist_eq_norm]
    have hdiff :
        center + scale⁻¹ • (first : Point3) -
            (center + scale⁻¹ • (second : Point3)) =
          scale⁻¹ • ((first : Point3) - (second : Point3)) := by
      rw [smul_sub]
      module
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hscalePos]
    rw [show scale⁻¹ * ‖(first : Point3) - (second : Point3)‖ =
      ‖(first : Point3) - (second : Point3)‖ / scale by
        rw [div_eq_mul_inv]
        ring]
    exact div_le_self
      (norm_nonneg ((first : Point3) - (second : Point3))) hscale
  have htargetLipschitz : LipschitzWith 1 targetPlaneMap := by
    simpa [targetPlaneMap, Function.comp_def] using
      sourceLocal.planeMap_lipschitz.comp hinverseLipschitz
  have htargetUnit : ∀ target, ‖targetPlaneMap target‖ = 1 :=
    fun target => sourceLocal.planeMap_unit (inverse target)
  have htargetIncidence : ∀ index point,
      ∀ hpoint : point ∈ targetShading.carrier index,
        |inner ℝ (targetFamily.tube index).direction
          (targetPlaneMap ⟨point, ⟨index, hpoint⟩⟩)| ≤
            scale * sourceDelta := by
    intro index point hpoint
    rcases hcarrier index hpoint with ⟨source, hsource, heq⟩
    have hinverse : pureWZ2IsotropicInverse center scale point = source := by
      rw [← heq, pureWZ2IsotropicInverse_map center hscalePos]
    have hsourceIncidence := sourceLocal.planeMap_incidence
      (sourceParent index) source hsource
    rw [hdirection index]
    change |inner ℝ (sourceFamily.tube (sourceParent index)).direction
      (sourceLocal.planeMap (inverse ⟨point, ⟨index, hpoint⟩⟩))| ≤ _
    have hinverseSubtype : inverse ⟨point, ⟨index, hpoint⟩⟩ =
        ⟨source, ⟨sourceParent index, hsource⟩⟩ := by
      apply Subtype.ext
      exact hinverse
    rw [hinverseSubtype]
    exact hsourceIncidence.trans (by
      calc
        sourceDelta = 1 * sourceDelta := by ring
        _ ≤ scale * sourceDelta := by gcongr <;> exact hsourceDelta.le)
  have htargetSubset : targetShading.union ⊆
      pureWZ2IsotropicMap center scale '' sourceShading.union := by
    rintro point ⟨index, hpoint⟩
    rcases hcarrier index hpoint with ⟨source, hsource, rfl⟩
    exact ⟨source, ⟨sourceParent index, hsource⟩, rfl⟩
  have htargetAD : ∀ rho, scale * sourceDelta ≤ rho → rho ≤ 1 →
      ∀ target : {point : Point3 // point ∈ targetShading.union},
        PureWZ2PaperADSet1
          (scalarProjection (targetPlaneMap target)
            (targetShading.union ∩
              Metric.closedBall (target : Point3) (Real.sqrt rho)))
          rho (1 - sigma) C := by
    intro rho hrhoLower hrhoOne target
    have htargetEq : (target : Point3) =
        pureWZ2IsotropicMap center scale (inverse target) := by
      exact (pureWZ2IsotropicMap_inverse center hscalePos target).symm
    simpa [targetPlaneMap] using
      pureWZ2_isotropic_local_ad sourceLocal center hsourceDelta hscale
        hrhoLower hrhoOne htargetSubset (inverse target) target htargetEq
  exact ⟨{
    planeMap := targetPlaneMap
    planeMap_lipschitz := htargetLipschitz
    planeMap_unit := htargetUnit
    planeMap_incidence := htargetIncidence
    local_ad := htargetAD
  }⟩

end Kakeya.Assouad

end
