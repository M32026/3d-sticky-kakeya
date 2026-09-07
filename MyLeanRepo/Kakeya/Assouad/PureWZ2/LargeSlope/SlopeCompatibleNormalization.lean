import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FixedRotationLinearSlope

/-!
# Slope-compatible coordinatewise normalization

After the fixed affine-diagonal step, a further diagonal map with coordinate
factors `(rX, rY, rZ)` transports a graph slope by the factor `rX / rY`
and reparametrizes height by `rZ`.  Thus the normalized first derivative is
unchanged exactly when `rX = rY * rZ`.

The concrete final normalization used below is `(lambda^2, lambda, lambda)`.
Unlike an isotropic dilation, it expands all three spatial directions while
preserving the already normalized public slope derivative.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- A centered coordinatewise diagonal map. -/
def pureWZ2CoordinatewiseDiagonalMap
    (center : Point3) (rX rY rZ : ℝ) (point : Point3) : Point3 :=
  point3
    (rX * (point 0 - center 0))
    (rY * (point 1 - center 1))
    (rZ * (point 2 - center 2))

@[simp] theorem pureWZ2CoordinatewiseDiagonalMap_coord_zero
    (center : Point3) (rX rY rZ : ℝ) (point : Point3) :
    pureWZ2CoordinatewiseDiagonalMap center rX rY rZ point 0 =
      rX * (point 0 - center 0) := by
  simp [pureWZ2CoordinatewiseDiagonalMap, point3]

@[simp] theorem pureWZ2CoordinatewiseDiagonalMap_coord_one
    (center : Point3) (rX rY rZ : ℝ) (point : Point3) :
    pureWZ2CoordinatewiseDiagonalMap center rX rY rZ point 1 =
      rY * (point 1 - center 1) := by
  simp [pureWZ2CoordinatewiseDiagonalMap, point3]

@[simp] theorem pureWZ2CoordinatewiseDiagonalMap_coord_two
    (center : Point3) (rX rY rZ : ℝ) (point : Point3) :
    pureWZ2CoordinatewiseDiagonalMap center rX rY rZ point 2 =
      rZ * (point 2 - center 2) := by
  simp [pureWZ2CoordinatewiseDiagonalMap, point3]

/-- The canonical positive normalization satisfying `rX = rY * rZ`. -/
def pureWZ2SlopeCompatibleNormalizationMap
    (center : Point3) (lambda : ℝ) (point : Point3) : Point3 :=
  pureWZ2CoordinatewiseDiagonalMap center (lambda ^ 2) lambda lambda point

/-- Linear-equivalence form of the slope-compatible normalization. -/
noncomputable def pureWZ2SlopeCompatibleNormalizationLinearEquiv
    (lambda : ℝ) (hlambda : 0 < lambda) : Point3 ≃ₗ[ℝ] Point3 :=
  pureWZ2AffineDiagonalLinearEquiv 0 (1 / lambda) (1 / lambda)
    (lambda ^ 2) (one_div_ne_zero hlambda.ne')
      (one_div_ne_zero hlambda.ne') (pow_ne_zero 2 hlambda.ne')

@[simp] theorem pureWZ2SlopeCompatibleNormalizationLinearEquiv_apply
    (lambda : ℝ) (hlambda : 0 < lambda) (vector : Point3) :
    pureWZ2SlopeCompatibleNormalizationLinearEquiv lambda hlambda vector =
      point3 (lambda ^ 2 * vector 0)
        (lambda * vector 1) (lambda * vector 2) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2SlopeCompatibleNormalizationLinearEquiv,
      pureWZ2AffineDiagonalLinearEquiv, pureWZ2AffineDiagonalLinear,
      pureWZ2HorizontalNorm, point3, hlambda.ne'] <;>
    field_simp [hlambda.ne'] <;> ring_nf <;> simp

/-- Affine-equivalence form, sending the chosen center to the origin. -/
noncomputable def pureWZ2SlopeCompatibleNormalizationAffineEquiv
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  AffineEquiv.ofLinearEquiv
    (pureWZ2SlopeCompatibleNormalizationLinearEquiv lambda hlambda) center 0

@[simp] theorem pureWZ2SlopeCompatibleNormalizationAffineEquiv_apply
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda)
    (point : Point3) :
    pureWZ2SlopeCompatibleNormalizationAffineEquiv center lambda hlambda point =
      pureWZ2SlopeCompatibleNormalizationMap center lambda point := by
  rw [pureWZ2SlopeCompatibleNormalizationAffineEquiv,
    AffineEquiv.ofLinearEquiv_apply]
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2SlopeCompatibleNormalizationLinearEquiv_apply,
      pureWZ2SlopeCompatibleNormalizationMap,
      pureWZ2CoordinatewiseDiagonalMap, point3]

/-- The slope-compatible normalization has the exact three-dimensional
Jacobian `lambda^4`. -/
theorem pureWZ2SlopeCompatibleNormalizationLinearEquiv_abs_det
    (lambda : ℝ) (hlambda : 0 < lambda) :
    |LinearMap.det
      (pureWZ2SlopeCompatibleNormalizationLinearEquiv lambda hlambda :
        Point3 →ₗ[ℝ] Point3)| = lambda ^ 4 := by
  let linear : Point3 →ₗ[ℝ] Point3 :=
    (pureWZ2SlopeCompatibleNormalizationLinearEquiv lambda hlambda :
      Point3 →ₗ[ℝ] Point3)
  let basis : Module.Basis (Fin 3) ℝ Point3 := PiLp.basisFun 2 ℝ (Fin 3)
  have hmatrix : LinearMap.toMatrix basis basis linear =
      !![lambda ^ 2, 0, 0; 0, lambda, 0; 0, 0, lambda] := by
    ext i j
    have hentry : (LinearMap.toMatrix basis basis linear) i j =
        (linear (basis j)) i := by
      rw [LinearMap.toMatrix_apply]
      exact PiLp.basisFun_repr 2 ℝ (Fin 3) (linear (basis j)) i
    rw [hentry]
    fin_cases i <;> fin_cases j <;>
      simp [linear, basis,
        pureWZ2SlopeCompatibleNormalizationLinearEquiv_apply,
        PiLp.basisFun_apply, point3]
  change |LinearMap.det linear| = lambda ^ 4
  rw [← LinearMap.det_toMatrix basis linear, hmatrix, Matrix.det_fin_three]
  simp [abs_of_pos hlambda]
  ring

/-- Exact volume scaling under the slope-compatible normalization. -/
theorem pureWZ2SlopeCompatibleNormalizationMap_volume_image
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda)
    (source : Set Point3) :
    MeasureTheory.volume
        (pureWZ2SlopeCompatibleNormalizationMap center lambda '' source) =
      ENNReal.ofReal (lambda ^ 4) * MeasureTheory.volume source := by
  let equivalence :=
    pureWZ2SlopeCompatibleNormalizationAffineEquiv center lambda hlambda
  have himage :
      pureWZ2SlopeCompatibleNormalizationMap center lambda '' source =
        equivalence '' source := by
    ext point
    simp only [Set.mem_image]
    constructor
    · rintro ⟨preimage, hpreimage, rfl⟩
      exact ⟨preimage, hpreimage,
        (pureWZ2SlopeCompatibleNormalizationAffineEquiv_apply
          center lambda hlambda preimage)⟩
    · rintro ⟨preimage, hpreimage, rfl⟩
      exact ⟨preimage, hpreimage,
        (pureWZ2SlopeCompatibleNormalizationAffineEquiv_apply
          center lambda hlambda preimage).symm⟩
  rw [himage, wz2PaperAffineEquiv_volume_image_eq]
  change ENNReal.ofReal
      |LinearMap.det
        (pureWZ2SlopeCompatibleNormalizationLinearEquiv lambda hlambda :
          Point3 →ₗ[ℝ] Point3)| * MeasureTheory.volume source = _
  rw [pureWZ2SlopeCompatibleNormalizationLinearEquiv_abs_det]

/-- The single point map used after the fixed-rotation affine-diagonal step.
Keeping this composition named prevents the final family, shading, and grain
certificates from drifting to different transformed configurations. -/
def pureWZ2SlopeCompatibleAffineDiagonalMap
    (frameSlope : ℝ) (affineCenter normalizationCenter : Point3)
    (heightScale transverseScale isotropicScale lambda : ℝ)
    (point : Point3) : Point3 :=
  pureWZ2SlopeCompatibleNormalizationMap normalizationCenter lambda
    (pureWZ2AffineDiagonalMapCentered frameSlope affineCenter heightScale
      transverseScale isotropicScale point)

/-- Affine-equivalence packaging of the exact same composite map. -/
noncomputable def pureWZ2SlopeCompatibleAffineDiagonalAffineEquiv
    (frameSlope : ℝ) (affineCenter normalizationCenter : Point3)
    (heightScale transverseScale isotropicScale lambda : ℝ)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0) (hlambda : 0 < lambda) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  (pureWZ2AffineDiagonalAffineEquivCentered frameSlope affineCenter
    heightScale transverseScale isotropicScale hheight htransverse
      hisotropic).trans
    (pureWZ2SlopeCompatibleNormalizationAffineEquiv
      normalizationCenter lambda hlambda)

@[simp] theorem pureWZ2SlopeCompatibleAffineDiagonalAffineEquiv_apply
    (frameSlope : ℝ) (affineCenter normalizationCenter : Point3)
    (heightScale transverseScale isotropicScale lambda : ℝ)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0) (hlambda : 0 < lambda)
    (point : Point3) :
    pureWZ2SlopeCompatibleAffineDiagonalAffineEquiv frameSlope affineCenter
        normalizationCenter heightScale transverseScale isotropicScale lambda
        hheight htransverse hisotropic hlambda point =
      pureWZ2SlopeCompatibleAffineDiagonalMap frameSlope affineCenter
        normalizationCenter heightScale transverseScale isotropicScale lambda
        point := by
  rw [pureWZ2SlopeCompatibleAffineDiagonalAffineEquiv,
    AffineEquiv.trans_apply,
    pureWZ2AffineDiagonalAffineEquivCentered_apply,
    pureWZ2SlopeCompatibleNormalizationAffineEquiv_apply]
  rfl

/-- With the post-normalization centered at the affine target origin, the
composite is literally another member of the existing fixed-rotation
affine-diagonal family. -/
theorem pureWZ2SlopeCompatibleAffineDiagonalMap_zero_eq
    (frameSlope : ℝ) (affineCenter : Point3)
    (heightScale transverseScale isotropicScale : ℝ)
    {lambda : ℝ} (hlambda : 0 < lambda) (point : Point3) :
    pureWZ2SlopeCompatibleAffineDiagonalMap frameSlope affineCenter 0
        heightScale transverseScale isotropicScale lambda point =
      pureWZ2AffineDiagonalMapCentered frameSlope affineCenter
        (heightScale / lambda) (transverseScale / lambda)
        (isotropicScale * lambda ^ 2) point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2SlopeCompatibleAffineDiagonalMap,
      pureWZ2SlopeCompatibleNormalizationMap,
      pureWZ2CoordinatewiseDiagonalMap,
      pureWZ2AffineDiagonalMapCentered, point3, hlambda.ne'] <;>
    field_simp [hlambda.ne'] <;> ring

/-- The composite image has exactly the `lambda^4` volume multiplier over
the fixed affine-diagonal image. -/
theorem pureWZ2SlopeCompatibleAffineDiagonalMap_volume_image
    (frameSlope : ℝ) (affineCenter normalizationCenter : Point3)
    (heightScale transverseScale isotropicScale : ℝ)
    (lambda : ℝ) (hlambda : 0 < lambda) (source : Set Point3) :
    MeasureTheory.volume
        (pureWZ2SlopeCompatibleAffineDiagonalMap frameSlope affineCenter
          normalizationCenter heightScale transverseScale isotropicScale
            lambda '' source) =
      ENNReal.ofReal (lambda ^ 4) *
        MeasureTheory.volume
          (pureWZ2AffineDiagonalMapCentered frameSlope affineCenter
            heightScale transverseScale isotropicScale '' source) := by
  rw [show
      pureWZ2SlopeCompatibleAffineDiagonalMap frameSlope affineCenter
          normalizationCenter heightScale transverseScale isotropicScale
            lambda '' source =
        pureWZ2SlopeCompatibleNormalizationMap normalizationCenter lambda ''
          (pureWZ2AffineDiagonalMapCentered frameSlope affineCenter
            heightScale transverseScale isotropicScale '' source) by
      simp only [pureWZ2SlopeCompatibleAffineDiagonalMap, Set.image_image]]
  exact pureWZ2SlopeCompatibleNormalizationMap_volume_image
    normalizationCenter lambda hlambda _

/-- The slope transported by `(lambda^2, lambda, lambda)`. -/
def pureWZ2SlopeCompatibleNormalizedSlope
    (source : SlopeFunction) (centerHeight lambda : ℝ) : SlopeFunction where
  toFun t := lambda * source (centerHeight + t / lambda)
  contDiff := by
    have hAffine : ContDiff ℝ 2
        (fun t : ℝ => centerHeight + t / lambda) :=
      contDiff_const.add (contDiff_id.div_const lambda)
    exact contDiff_const.mul (source.contDiff.comp hAffine)

/-- The target height determines the source height under the compatible map. -/
theorem pureWZ2SlopeCompatibleNormalizationMap_coord_two_iff
    (center point : Point3) {lambda : ℝ} (hlambda : 0 < lambda) (t : ℝ) :
    pureWZ2SlopeCompatibleNormalizationMap center lambda point 2 = t ↔
      point 2 = center 2 + t / lambda := by
  rw [pureWZ2SlopeCompatibleNormalizationMap,
    pureWZ2CoordinatewiseDiagonalMap_coord_two]
  constructor <;> intro h
  · have hdiff : point 2 - center 2 = t / lambda :=
      (eq_div_iff hlambda.ne').2 (by simpa [mul_comm] using h)
    linarith
  · rw [h]
    field_simp [hlambda.ne']
    ring

/-- Exact scalar-projection covariance.  The relation
`lambda^2 = lambda * lambda` is built into the concrete normalization. -/
theorem pureWZ2SlopeCompatibleNormalization_projection_pointwise
    (source : SlopeFunction) (center point : Point3)
    {lambda : ℝ} (hlambda : 0 < lambda) (t : ℝ)
    (hheight : pureWZ2SlopeCompatibleNormalizationMap center lambda point 2 = t) :
    inner ℝ (pureWZ2SlopeCompatibleNormalizationMap center lambda point)
        (globalGrainDirection
          (pureWZ2SlopeCompatibleNormalizedSlope source (center 2) lambda t)) =
      lambda ^ 2 * inner ℝ point (globalGrainDirection (source (point 2))) -
        lambda ^ 2 *
          inner ℝ center (globalGrainDirection (source (point 2))) := by
  have hsourceHeight :=
    (pureWZ2SlopeCompatibleNormalizationMap_coord_two_iff
      center point hlambda t).mp hheight
  have hinner (p : Point3) (s : ℝ) :
      inner ℝ p (globalGrainDirection s) = p 0 + s * p 1 := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
  rw [hinner, hinner, hinner]
  rw [show
        (pureWZ2SlopeCompatibleNormalizationMap center lambda point)
          0 = lambda ^ 2 * (point 0 - center 0) by
    simp [pureWZ2SlopeCompatibleNormalizationMap]]
  rw [show
        (pureWZ2SlopeCompatibleNormalizationMap center lambda point)
          1 = lambda * (point 1 - center 1) by
    simp [pureWZ2SlopeCompatibleNormalizationMap]]
  change lambda ^ 2 * (point 0 - center 0) +
      lambda * source (center 2 + t / lambda) *
        (lambda * (point 1 - center 1)) = _
  rw [show source (center 2 + t / lambda) = source (point 2) by
    rw [hsourceHeight]]
  ring

/-- Set-level projection covariance on a target horizontal slice. -/
theorem pureWZ2SlopeCompatibleNormalization_projection_set
    (source : SlopeFunction) (center : Point3)
    {lambda : ℝ} (hlambda : 0 < lambda) (set : Set Point3) (t : ℝ) :
    scalarProjection
        (globalGrainDirection
          (pureWZ2SlopeCompatibleNormalizedSlope source (center 2) lambda t))
        (horizontalSlice
          (pureWZ2SlopeCompatibleNormalizationMap center lambda '' set) t) =
      (fun value : ℝ => lambda ^ 2 * value -
        lambda ^ 2 * inner ℝ center
          (globalGrainDirection (source (center 2 + t / lambda)))) ''
        scalarProjection
          (globalGrainDirection (source (center 2 + t / lambda)))
          (horizontalSlice set (center 2 + t / lambda)) := by
  ext value
  constructor
  · rintro ⟨target, ⟨⟨sourcePoint, hsourcePoint, rfl⟩, hheight⟩, rfl⟩
    have hsourceHeight :=
      (pureWZ2SlopeCompatibleNormalizationMap_coord_two_iff
        center sourcePoint hlambda t).mp hheight
    refine ⟨inner ℝ sourcePoint
        (globalGrainDirection (source (sourcePoint 2))), ?_, ?_⟩
    · exact ⟨sourcePoint, ⟨hsourcePoint, hsourceHeight⟩, by rw [hsourceHeight]⟩
    · rw [← hsourceHeight]
      exact (pureWZ2SlopeCompatibleNormalization_projection_pointwise
        source center sourcePoint hlambda t hheight).symm
  · rintro ⟨sourceValue,
      ⟨sourcePoint, ⟨hsourcePoint, hsourceHeight⟩, rfl⟩, rfl⟩
    have hheight :
        pureWZ2SlopeCompatibleNormalizationMap center lambda sourcePoint 2 = t :=
      (pureWZ2SlopeCompatibleNormalizationMap_coord_two_iff
        center sourcePoint hlambda t).mpr hsourceHeight
    refine ⟨pureWZ2SlopeCompatibleNormalizationMap center lambda sourcePoint,
      ⟨⟨sourcePoint, hsourcePoint, rfl⟩, hheight⟩, ?_⟩
    rw [← hsourceHeight]
    exact pureWZ2SlopeCompatibleNormalization_projection_pointwise
      source center sourcePoint hlambda t hheight

/-- Exact-image global AD transport through the slope-compatible
normalization.  The projection scale grows by `lambda^2`, exactly matching
the horizontal coordinate factor in the covariance identity. -/
theorem pureWZ2_slopeCompatibleNormalization_exact_global_ad
    {sourceDelta targetDelta sigma : ℝ} {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    (sourceGlobal : PureWZ2C2GlobalGrainData sourceShading sigma C)
    (sourceSlope : SlopeFunction)
    (hsourceSlope : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      sourceSlope t = sourceGlobal.slope t)
    (center : Point3) {lambda : ℝ} (hlambda : 0 < lambda)
    (hcenterHeight : center 2 = 0)
    (hsourceHeight : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      t / lambda ∈ Set.Icc (-1 : ℝ) 1)
    (hbase : lambda ^ 2 * sourceDelta ≤ targetDelta)
    (htargetDelta : 0 < targetDelta) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (pureWZ2SlopeCompatibleNormalizedSlope sourceSlope
              (center 2) lambda t))
          (horizontalSlice
            (pureWZ2SlopeCompatibleNormalizationMap center lambda ''
              sourceShading.union) t))
        targetDelta (1 - sigma) C := by
  intro t ht
  have hsourceHeight' : center 2 + t / lambda ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hcenterHeight, zero_add]
    exact hsourceHeight t ht
  have hsource := sourceGlobal.global_ad_slope
    (center 2 + t / lambda) hsourceHeight'
  rw [← hsourceSlope (center 2 + t / lambda) hsourceHeight'] at hsource
  have hscale : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
  have haffine := PureWZ2PaperADSet1.affine_transfer
    (b := -(lambda ^ 2 * inner ℝ center
      (globalGrainDirection (sourceSlope
        (center 2 + t / lambda))))) hsource hscale
  rw [pureWZ2SlopeCompatibleNormalization_projection_set
    sourceSlope center hlambda sourceShading.union t]
  have hmap :
      (fun value : ℝ => lambda ^ 2 * value -
        lambda ^ 2 * inner ℝ center
          (globalGrainDirection (sourceSlope (center 2 + t / lambda)))) =
      fun value : ℝ => lambda ^ 2 * value +
        -(lambda ^ 2 * inner ℝ center
          (globalGrainDirection (sourceSlope (center 2 + t / lambda)))) := by
    funext value
    ring
  rw [hmap]
  exact haffine.weaken_scale htargetDelta hbase

/-- The compatible normalization does not change the first derivative of the
fixed affine public slope. -/
theorem pureWZ2SlopeCompatibleNormalizedSlope_fixed_deriv
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (data : PureWZ2FixedRotationLinearSlopeData band)
    (hlambda : 0 < lambda) :
    deriv
        (pureWZ2SlopeCompatibleNormalizedSlope data.publicSlope
          centerHeight lambda) t =
      deriv band.lemma31.data.globalSlope data.anchor /
        band.slopeScale := by
  rw [data.publicSlope_eq]
  let coefficient :=
    deriv band.lemma31.data.globalSlope data.anchor / band.slopeScale
  change deriv (fun x : ℝ =>
      lambda * (coefficient * (centerHeight + x / lambda))) t = coefficient
  have hfun : (fun x : ℝ =>
      lambda * (coefficient * (centerHeight + x / lambda))) =
      fun x : ℝ => lambda * coefficient * centerHeight + coefficient * x := by
    funext x
    field_simp [hlambda.ne']
  rw [hfun]
  simpa using
    (((hasDerivAt_id t).const_mul coefficient).const_add
      (lambda * coefficient * centerHeight)).deriv

/-- The compatible normalization also preserves the zero second derivative
of the fixed affine public slope. -/
theorem pureWZ2SlopeCompatibleNormalizedSlope_fixed_second_deriv
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (data : PureWZ2FixedRotationLinearSlopeData band)
    (hlambda : 0 < lambda) :
    deriv (deriv
      (pureWZ2SlopeCompatibleNormalizedSlope data.publicSlope
        centerHeight lambda)) t = 0 := by
  have hfirst : deriv
      (pureWZ2SlopeCompatibleNormalizedSlope data.publicSlope
        centerHeight lambda) = fun _ : ℝ =>
          deriv band.lemma31.data.globalSlope data.anchor /
            band.slopeScale := by
    funext x
    exact pureWZ2SlopeCompatibleNormalizedSlope_fixed_deriv data hlambda
  rw [hfirst]
  exact (hasDerivAt_const t _).deriv

/-- Consequently the public nonsingularity bounds survive the final
coordinatewise normalization verbatim. -/
theorem PureWZ2FixedRotationLinearSlopeData.slopeCompatible_nonsingular
    {sigma epsilon delta centerHeight lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (data : PureWZ2FixedRotationLinearSlopeData band)
    (hlambda : 0 < lambda) :
    (pureWZ2SlopeCompatibleNormalizedSlope data.publicSlope
      centerHeight lambda).IsNonsingular := by
  intro t ht
  rw [pureWZ2SlopeCompatibleNormalizedSlope_fixed_deriv data hlambda,
    pureWZ2SlopeCompatibleNormalizedSlope_fixed_second_deriv data hlambda]
  have hsource := data.publicSlope_nonsingular (0 : ℝ) (by norm_num)
  rw [data.publicSlope_eq,
    pureWZ2FixedRotationLinearSlope_deriv] at hsource
  exact ⟨hsource.1, hsource.2.1, by norm_num⟩

/-- The same result at the public interval-domain boundary. -/
theorem PureWZ2FixedRotationLinearSlopeData.slopeCompatible_public_nonsingular
    {sigma epsilon delta centerHeight lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (data : PureWZ2FixedRotationLinearSlopeData band)
    (hlambda : 0 < lambda) :
    PureWZ2C2SlopeIsNonsingular
      (pureWZ2SlopeCompatibleNormalizedSlope data.publicSlope
        centerHeight lambda).onUnitInterval :=
  SlopeFunction.nonsingular_onUnitInterval _
    (data.slopeCompatible_nonsingular hlambda)

/-- If the final normalization is centered at target height zero, the
transported public slope is literally unchanged.  This keeps the frozen
`f 0 = 0` provenance available internally without requiring it in the
paper-facing Node-6 statement. -/
theorem PureWZ2FixedRotationLinearSlopeData.slopeCompatible_zero_center_eq
    {sigma epsilon delta lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (data : PureWZ2FixedRotationLinearSlopeData band)
    (hlambda : 0 < lambda) :
    ∀ t, pureWZ2SlopeCompatibleNormalizedSlope data.publicSlope 0 lambda t =
      data.publicSlope t := by
  intro t
  rw [data.publicSlope_eq]
  simp [pureWZ2SlopeCompatibleNormalizedSlope,
    pureWZ2FixedRotationLinearSlope_apply]
  field_simp [hlambda.ne']

end Kakeya.Assouad

end
