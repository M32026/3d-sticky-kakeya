import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FixedRotationLinearSlope

/-!
# Line-class-compatible slope normalization

The diagonal map `(x,y,z) -> (lambda*x,y,lambda*z)` is the terminal
normalization compatible with both the public slope and the paper line class.
It multiplies slopes by `lambda` while dividing the height parameter by
`lambda`, so first derivatives are unchanged.  Unlike
`diag(lambda^2,lambda,lambda)`, it also preserves the lower bound on the
normalized vertical direction.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

def pureWZ2LineClassNormalizationMap
    (center : Point3) (lambda : ℝ) (point : Point3) : Point3 :=
  point3 (lambda * (point 0 - center 0))
    (point 1 - center 1) (lambda * (point 2 - center 2))

def pureWZ2LineClassNormalizationLinear
    (lambda : ℝ) (vector : Point3) : Point3 :=
  point3 (lambda * vector 0) (vector 1) (lambda * vector 2)

def pureWZ2LineClassNormalizationNormal
    (lambda : ℝ) (normal : Point3) : Point3 :=
  point3 (normal 0 / lambda) (normal 1) (normal 2 / lambda)

/-- Linear-equivalence packaging of `diag(lambda, 1, lambda)`. -/
noncomputable def pureWZ2LineClassNormalizationLinearEquiv
    (lambda : ℝ) (hlambda : 0 < lambda) : Point3 ≃ₗ[ℝ] Point3 :=
  pureWZ2AffineDiagonalLinearEquiv 0 1 (1 / lambda) lambda
    one_ne_zero (one_div_ne_zero hlambda.ne') hlambda.ne'

@[simp] theorem pureWZ2LineClassNormalizationLinearEquiv_apply
    (lambda : ℝ) (hlambda : 0 < lambda) (vector : Point3) :
    pureWZ2LineClassNormalizationLinearEquiv lambda hlambda vector =
      pureWZ2LineClassNormalizationLinear lambda vector := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2LineClassNormalizationLinearEquiv,
      pureWZ2AffineDiagonalLinearEquiv, pureWZ2AffineDiagonalLinear,
      pureWZ2HorizontalNorm, pureWZ2LineClassNormalizationLinear,
      point3, hlambda.ne'] <;>
    field_simp [hlambda.ne']

/-- Affine-equivalence packaging of the centered line-class normalization. -/
noncomputable def pureWZ2LineClassNormalizationAffineEquiv
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  AffineEquiv.ofLinearEquiv
    (pureWZ2LineClassNormalizationLinearEquiv lambda hlambda) center 0

@[simp] theorem pureWZ2LineClassNormalizationAffineEquiv_apply
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda)
    (point : Point3) :
    pureWZ2LineClassNormalizationAffineEquiv center lambda hlambda point =
      pureWZ2LineClassNormalizationMap center lambda point := by
  rw [pureWZ2LineClassNormalizationAffineEquiv,
    AffineEquiv.ofLinearEquiv_apply]
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2LineClassNormalizationLinearEquiv_apply,
      pureWZ2LineClassNormalizationLinear,
      pureWZ2LineClassNormalizationMap, point3]

/-- The exact Jacobian of `diag(lambda, 1, lambda)` is `lambda^2`. -/
theorem pureWZ2LineClassNormalizationLinearEquiv_abs_det
    (lambda : ℝ) (hlambda : 0 < lambda) :
    |LinearMap.det
      (pureWZ2LineClassNormalizationLinearEquiv lambda hlambda :
        Point3 →ₗ[ℝ] Point3)| = lambda ^ 2 := by
  let linear : Point3 →ₗ[ℝ] Point3 :=
    (pureWZ2LineClassNormalizationLinearEquiv lambda hlambda :
      Point3 →ₗ[ℝ] Point3)
  let basis : Module.Basis (Fin 3) ℝ Point3 := PiLp.basisFun 2 ℝ (Fin 3)
  have hmatrix : LinearMap.toMatrix basis basis linear =
      !![lambda, 0, 0; 0, 1, 0; 0, 0, lambda] := by
    ext i j
    have hentry : (LinearMap.toMatrix basis basis linear) i j =
        (linear (basis j)) i := by
      rw [LinearMap.toMatrix_apply]
      exact PiLp.basisFun_repr 2 ℝ (Fin 3) (linear (basis j)) i
    rw [hentry]
    fin_cases i <;> fin_cases j <;>
      simp [linear, basis,
        pureWZ2LineClassNormalizationLinearEquiv_apply,
        pureWZ2LineClassNormalizationLinear, PiLp.basisFun_apply, point3]
  change |LinearMap.det linear| = lambda ^ 2
  rw [← LinearMap.det_toMatrix basis linear, hmatrix, Matrix.det_fin_three]
  simp [abs_of_pos hlambda]
  ring

/-- Exact volume scaling for the same literal centered map. -/
theorem pureWZ2LineClassNormalizationMap_volume_image
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda)
    (source : Set Point3) :
    MeasureTheory.volume
        (pureWZ2LineClassNormalizationMap center lambda '' source) =
      ENNReal.ofReal (lambda ^ 2) * MeasureTheory.volume source := by
  let equivalence :=
    pureWZ2LineClassNormalizationAffineEquiv center lambda hlambda
  have himage :
      pureWZ2LineClassNormalizationMap center lambda '' source =
        equivalence '' source := by
    ext point
    simp only [Set.mem_image]
    constructor
    · rintro ⟨preimage, hpreimage, rfl⟩
      exact ⟨preimage, hpreimage,
        pureWZ2LineClassNormalizationAffineEquiv_apply
          center lambda hlambda preimage⟩
    · rintro ⟨preimage, hpreimage, rfl⟩
      exact ⟨preimage, hpreimage,
        (pureWZ2LineClassNormalizationAffineEquiv_apply
          center lambda hlambda preimage).symm⟩
  rw [himage, wz2PaperAffineEquiv_volume_image_eq]
  change ENNReal.ofReal
      |LinearMap.det
        (pureWZ2LineClassNormalizationLinearEquiv lambda hlambda :
          Point3 →ₗ[ℝ] Point3)| * MeasureTheory.volume source = _
  rw [pureWZ2LineClassNormalizationLinearEquiv_abs_det]

def pureWZ2LineClassNormalizedSlope
    (source : SlopeFunction) (centerHeight lambda : ℝ) : SlopeFunction where
  toFun t := lambda * source (centerHeight + t / lambda)
  contDiff := by
    have hAffine : ContDiff ℝ 2
        (fun t : ℝ => centerHeight + t / lambda) :=
      contDiff_const.add (contDiff_id.div_const lambda)
    exact contDiff_const.mul (source.contDiff.comp hAffine)

/-- The first derivative of the exact transported slope.  This is stated for
an arbitrary globally smooth source, rather than only for the affine tangent
used by the older terminal route. -/
theorem pureWZ2LineClassNormalizedSlope_deriv
    (source : SlopeFunction) (centerHeight : ℝ)
    {lambda : ℝ} (hlambda : 0 < lambda) (t : ℝ) :
    deriv (pureWZ2LineClassNormalizedSlope source centerHeight lambda) t =
      deriv source (centerHeight + t / lambda) := by
  change deriv (fun x : ℝ =>
      lambda * source (centerHeight + x / lambda)) t = _
  have hinner : DifferentiableAt ℝ
      (fun x : ℝ => source (centerHeight + x / lambda)) t := by
    exact (source.contDiff.differentiable (by norm_num)).differentiableAt.comp
      t (((differentiableAt_id.div_const lambda).const_add centerHeight))
  rw [deriv_const_mul lambda hinner]
  have hrewrite :
      (fun x : ℝ => source (centerHeight + x / lambda)) =
        fun x : ℝ => (fun y : ℝ => source (centerHeight + y))
          ((1 / lambda) * x) := by
    funext x
    congr 2
    field_simp [hlambda.ne']
  rw [hrewrite]
  rw [deriv_comp_mul_left (1 / lambda)
    (fun y : ℝ => source (centerHeight + y)) t,
    deriv_comp_const_add]
  simp only [smul_eq_mul]
  field_simp [hlambda.ne']

/-- The second derivative gains exactly one inverse power of the terminal
dilation. -/
theorem pureWZ2LineClassNormalizedSlope_second_deriv
    (source : SlopeFunction) (centerHeight : ℝ)
    {lambda : ℝ} (hlambda : 0 < lambda) (t : ℝ) :
    deriv (deriv
        (pureWZ2LineClassNormalizedSlope source centerHeight lambda)) t =
      (1 / lambda) *
        deriv (deriv source) (centerHeight + t / lambda) := by
  have hfirst : deriv
      (pureWZ2LineClassNormalizedSlope source centerHeight lambda) =
        fun x : ℝ => deriv source (centerHeight + x / lambda) := by
    funext x
    exact pureWZ2LineClassNormalizedSlope_deriv
      source centerHeight hlambda x
  rw [hfirst]
  have hrewrite :
      (fun x : ℝ => deriv source (centerHeight + x / lambda)) =
        fun x : ℝ => (fun y : ℝ => deriv source (centerHeight + y))
          ((1 / lambda) * x) := by
    funext x
    congr 2
    field_simp [hlambda.ne']
  rw [hrewrite]
  rw [deriv_comp_mul_left (1 / lambda)
    (fun y : ℝ => deriv source (centerHeight + y)) t,
    deriv_comp_const_add]
  simp only [smul_eq_mul]
  ring

/-- A line-class normalization preserves nonsingularity whenever its target
height window maps back into the source paper interval.  The second
derivative only improves by `lambda⁻¹`. -/
theorem pureWZ2LineClassNormalizedSlope_nonsingular_of_mapsTo
    (source : SlopeFunction) (hsource : source.IsNonsingular)
    (centerHeight : ℝ) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    (hsourceHeight : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      centerHeight + t / lambda ∈ Set.Icc (-1 : ℝ) 1) :
    (pureWZ2LineClassNormalizedSlope
      source centerHeight lambda).IsNonsingular := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  intro t ht
  have hbounds := hsource (centerHeight + t / lambda)
    (hsourceHeight t ht)
  rw [pureWZ2LineClassNormalizedSlope_deriv
      source centerHeight hlambdaPos t,
    pureWZ2LineClassNormalizedSlope_second_deriv
      source centerHeight hlambdaPos t]
  refine ⟨hbounds.1, hbounds.2.1, ?_⟩
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hlambdaPos)]
  calc
    (1 / lambda) *
          |deriv (deriv source) (centerHeight + t / lambda)| ≤
        1 * |deriv (deriv source) (centerHeight + t / lambda)| := by
      gcongr
      exact (div_le_one hlambdaPos).2 hlambda
    _ ≤ 1 / 100 := by simpa using hbounds.2.2

/-- Centered specialization: if `lambda >= 1`, division by `lambda` maps
`[-1,1]` to itself. -/
theorem pureWZ2LineClassNormalizedSlope_nonsingular
    (source : SlopeFunction) (hsource : source.IsNonsingular)
    {lambda : ℝ} (hlambda : 1 ≤ lambda) :
    (pureWZ2LineClassNormalizedSlope source 0 lambda).IsNonsingular := by
  apply pureWZ2LineClassNormalizedSlope_nonsingular_of_mapsTo
    source hsource 0 hlambda
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  intro t ht
  simp only [zero_add]
  constructor
  · apply (le_div_iff₀ hlambdaPos).2
    nlinarith [ht.1]
  · apply (div_le_iff₀ hlambdaPos).2
    nlinarith [ht.2]

theorem pureWZ2LineClassNormalizedSlope_fixed_deriv
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (data : PureWZ2FixedRotationLinearSlopeData band)
    (hlambda : 0 < lambda) :
    deriv
        (pureWZ2LineClassNormalizedSlope data.publicSlope centerHeight lambda) t =
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

theorem pureWZ2LineClassNormalizedSlope_fixed_second_deriv
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (data : PureWZ2FixedRotationLinearSlopeData band)
    (hlambda : 0 < lambda) :
    deriv (deriv
      (pureWZ2LineClassNormalizedSlope data.publicSlope centerHeight lambda)) t =
        0 := by
  have hfirst : deriv
      (pureWZ2LineClassNormalizedSlope data.publicSlope centerHeight lambda) =
        fun _ : ℝ =>
          deriv band.lemma31.data.globalSlope data.anchor /
            band.slopeScale := by
    funext x
    exact pureWZ2LineClassNormalizedSlope_fixed_deriv data hlambda
  rw [hfirst]
  exact (hasDerivAt_const t _).deriv

theorem PureWZ2FixedRotationLinearSlopeData.lineClassNormalized_nonsingular
    {sigma epsilon delta centerHeight lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (data : PureWZ2FixedRotationLinearSlopeData band)
    (hlambda : 0 < lambda) :
    (pureWZ2LineClassNormalizedSlope data.publicSlope
      centerHeight lambda).IsNonsingular := by
  intro t ht
  rw [pureWZ2LineClassNormalizedSlope_fixed_deriv data hlambda,
    pureWZ2LineClassNormalizedSlope_fixed_second_deriv data hlambda]
  have hsource := data.publicSlope_nonsingular (0 : ℝ) (by norm_num)
  rw [data.publicSlope_eq, pureWZ2FixedRotationLinearSlope_deriv] at hsource
  exact ⟨hsource.1, hsource.2.1, by norm_num⟩

theorem pureWZ2LineClassNormalization_projection_pointwise
    (source : SlopeFunction) (center point : Point3)
    {lambda : ℝ} (hlambda : 0 < lambda) (t : ℝ)
    (hheight : pureWZ2LineClassNormalizationMap center lambda point 2 = t) :
    inner ℝ (pureWZ2LineClassNormalizationMap center lambda point)
        (globalGrainDirection
          (pureWZ2LineClassNormalizedSlope source (center 2) lambda t)) =
      lambda * inner ℝ point (globalGrainDirection (source (point 2))) -
        lambda * inner ℝ center
          (globalGrainDirection (source (point 2))) := by
  have hsourceHeight : point 2 = center 2 + t / lambda := by
    simp only [pureWZ2LineClassNormalizationMap, point3_coord2] at hheight
    have hquotient : point 2 - center 2 = t / lambda :=
      (eq_div_iff hlambda.ne').2 (by simpa [mul_comm] using hheight)
    linarith
  simp [pureWZ2LineClassNormalizationMap,
    pureWZ2LineClassNormalizedSlope, globalGrainDirection,
    PiLp.inner_apply, Fin.sum_univ_succ, point3, hsourceHeight]
  ring

/-- Set-level projection covariance on a target horizontal slice. -/
theorem pureWZ2LineClassNormalization_projection_set
    (source : SlopeFunction) (center : Point3)
    {lambda : ℝ} (hlambda : 0 < lambda) (set : Set Point3) (t : ℝ) :
    scalarProjection
        (globalGrainDirection
          (pureWZ2LineClassNormalizedSlope source (center 2) lambda t))
        (horizontalSlice
          (pureWZ2LineClassNormalizationMap center lambda '' set) t) =
      (fun value : ℝ => lambda * value -
        lambda * inner ℝ center
          (globalGrainDirection (source (center 2 + t / lambda)))) ''
        scalarProjection
          (globalGrainDirection (source (center 2 + t / lambda)))
          (horizontalSlice set (center 2 + t / lambda)) := by
  ext value
  constructor
  · rintro ⟨target, ⟨⟨sourcePoint, hsourcePoint, rfl⟩, hheight⟩, rfl⟩
    have hsourceHeight : sourcePoint 2 = center 2 + t / lambda := by
      simp only [pureWZ2LineClassNormalizationMap, point3_coord2] at hheight
      have hquotient : sourcePoint 2 - center 2 = t / lambda :=
        (eq_div_iff hlambda.ne').2 (by simpa [mul_comm] using hheight)
      linarith
    refine ⟨inner ℝ sourcePoint
        (globalGrainDirection (source (sourcePoint 2))), ?_, ?_⟩
    · exact ⟨sourcePoint, ⟨hsourcePoint, hsourceHeight⟩, by rw [hsourceHeight]⟩
    · rw [← hsourceHeight]
      exact (pureWZ2LineClassNormalization_projection_pointwise
        source center sourcePoint hlambda t hheight).symm
  · rintro ⟨sourceValue,
      ⟨sourcePoint, ⟨hsourcePoint, hsourceHeight⟩, rfl⟩, rfl⟩
    have hheight :
        pureWZ2LineClassNormalizationMap center lambda sourcePoint 2 = t := by
      simp only [pureWZ2LineClassNormalizationMap, point3_coord2]
      rw [hsourceHeight]
      field_simp [hlambda.ne']
      ring
    refine ⟨pureWZ2LineClassNormalizationMap center lambda sourcePoint,
      ⟨⟨sourcePoint, hsourcePoint, rfl⟩, hheight⟩, ?_⟩
    rw [← hsourceHeight]
    exact pureWZ2LineClassNormalization_projection_pointwise
      source center sourcePoint hlambda t hheight

/-- Exact-image global AD transport through `diag(lambda,1,lambda)`. -/
theorem pureWZ2_lineClassNormalization_exact_global_ad
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
    (hbase : lambda * sourceDelta ≤ targetDelta)
    (htargetDelta : 0 < targetDelta) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (pureWZ2LineClassNormalizedSlope sourceSlope
              (center 2) lambda t))
          (horizontalSlice
            (pureWZ2LineClassNormalizationMap center lambda ''
              sourceShading.union) t))
        targetDelta (1 - sigma) C := by
  intro t ht
  have hsourceHeight' : center 2 + t / lambda ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hcenterHeight, zero_add]
    exact hsourceHeight t ht
  have hsource := sourceGlobal.global_ad_slope
    (center 2 + t / lambda) hsourceHeight'
  rw [← hsourceSlope (center 2 + t / lambda) hsourceHeight'] at hsource
  have haffine := PureWZ2PaperADSet1.affine_transfer
    (b := -(lambda * inner ℝ center
      (globalGrainDirection (sourceSlope
        (center 2 + t / lambda))))) hsource hlambda
  rw [pureWZ2LineClassNormalization_projection_set
    sourceSlope center hlambda sourceShading.union t]
  have hmap :
      (fun value : ℝ => lambda * value -
        lambda * inner ℝ center
          (globalGrainDirection (sourceSlope (center 2 + t / lambda)))) =
      fun value : ℝ => lambda * value +
        -(lambda * inner ℝ center
          (globalGrainDirection (sourceSlope (center 2 + t / lambda)))) := by
    funext value
    ring
  rw [hmap]
  exact haffine.weaken_scale htargetDelta hbase

/-- Exact-image global AD transport when the source AD theorem is already
available for a globally smooth slope, without first repackaging it as a
`PureWZ2C2GlobalGrainData`.  This is the direct Node-6 terminal interface. -/
theorem pureWZ2_lineClassNormalization_exact_global_ad_of_slope
    {sourceDelta targetDelta sigma : ℝ} {C : ENNReal}
    {source : Set Point3}
    (sourceSlope : SlopeFunction)
    (hsourceAD : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (sourceSlope t))
          (horizontalSlice source t))
        sourceDelta (1 - sigma) C)
    (center : Point3) {lambda : ℝ} (hlambda : 0 < lambda)
    (hcenterHeight : center 2 = 0)
    (hsourceHeight : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      t / lambda ∈ Set.Icc (-1 : ℝ) 1)
    (hbase : lambda * sourceDelta ≤ targetDelta)
    (htargetDelta : 0 < targetDelta) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (pureWZ2LineClassNormalizedSlope sourceSlope
              (center 2) lambda t))
          (horizontalSlice
            (pureWZ2LineClassNormalizationMap center lambda '' source) t))
        targetDelta (1 - sigma) C := by
  intro t ht
  have hsourceHeight' : center 2 + t / lambda ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hcenterHeight, zero_add]
    exact hsourceHeight t ht
  have hsource := hsourceAD (center 2 + t / lambda) hsourceHeight'
  have haffine := PureWZ2PaperADSet1.affine_transfer
    (b := -(lambda * inner ℝ center
      (globalGrainDirection (sourceSlope
        (center 2 + t / lambda))))) hsource hlambda
  rw [pureWZ2LineClassNormalization_projection_set
    sourceSlope center hlambda source t]
  have hmap :
      (fun value : ℝ => lambda * value -
        lambda * inner ℝ center
          (globalGrainDirection (sourceSlope (center 2 + t / lambda)))) =
      fun value : ℝ => lambda * value +
        -(lambda * inner ℝ center
          (globalGrainDirection (sourceSlope (center 2 + t / lambda)))) := by
    funext value
    ring
  rw [hmap]
  exact haffine.weaken_scale htargetDelta hbase

/-- Exact-image global AD through `diag(lambda,1,lambda)` when the source
estimate is available at every ambient height.  This is the form needed for
an exact shading supported on a compact active core: outside that core its
horizontal slices are empty, so no artificial restriction on the second
normalization center is required. -/
theorem pureWZ2_lineClassNormalization_exact_global_ad_of_slope_all
    {sourceDelta targetDelta sigma : ℝ} {C : ENNReal}
    {source : Set Point3}
    (sourceSlope : SlopeFunction)
    (hsourceAD : ∀ t : ℝ,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (sourceSlope t))
          (horizontalSlice source t))
        sourceDelta (1 - sigma) C)
    (center : Point3) {lambda : ℝ} (hlambda : 0 < lambda)
    (hbase : lambda * sourceDelta ≤ targetDelta)
    (htargetDelta : 0 < targetDelta) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (pureWZ2LineClassNormalizedSlope sourceSlope
              (center 2) lambda t))
          (horizontalSlice
            (pureWZ2LineClassNormalizationMap center lambda '' source) t))
        targetDelta (1 - sigma) C := by
  intro t _ht
  have hsource := hsourceAD (center 2 + t / lambda)
  have haffine := PureWZ2PaperADSet1.affine_transfer
    (b := -(lambda * inner ℝ center
      (globalGrainDirection (sourceSlope
        (center 2 + t / lambda))))) hsource hlambda
  rw [pureWZ2LineClassNormalization_projection_set
    sourceSlope center hlambda source t]
  have hmap :
      (fun value : ℝ => lambda * value -
        lambda * inner ℝ center
          (globalGrainDirection (sourceSlope (center 2 + t / lambda)))) =
      fun value : ℝ => lambda * value +
        -(lambda * inner ℝ center
          (globalGrainDirection (sourceSlope (center 2 + t / lambda)))) := by
    funext value
    ring
  rw [hmap]
  exact haffine.weaken_scale htargetDelta hbase

/-- The line-class normalization preserves the vertical-direction lower
bound of every unit source direction. -/
theorem pureWZ2LineClassNormalization_vertical_ratio
    {lambda : ℝ} (hlambda : 1 ≤ lambda)
    {direction : Point3} (hdirection : ‖direction‖ = 1)
    (hvertical : (1 / 2 : ℝ) ≤ |direction 2|) :
    (1 / 2 : ℝ) ≤
      |pureWZ2LineClassNormalizationLinear lambda direction 2| /
        ‖pureWZ2LineClassNormalizationLinear lambda direction‖ := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  let image := pureWZ2LineClassNormalizationLinear lambda direction
  have himageNorm : ‖image‖ ≤ lambda * ‖direction‖ := by
    have hsource := point3_coord_norm_sq direction
    have htarget := point3_coord_norm_sq image
    have hsquare : ‖image‖ ^ 2 ≤ (lambda * ‖direction‖) ^ 2 := by
      rw [htarget, mul_pow, hsource]
      simp only [image, pureWZ2LineClassNormalizationLinear, point3_coord0,
        point3_coord1, point3_coord2]
      have hy : direction 1 ^ 2 ≤ lambda ^ 2 * direction 1 ^ 2 := by
        have hscale : 1 ≤ lambda ^ 2 := by nlinarith [sq_nonneg lambda]
        nlinarith [sq_nonneg (direction 1)]
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg image)
      (mul_nonneg hlambdaPos.le (norm_nonneg direction))).mp hsquare
  have himagePos : 0 < ‖image‖ := by
    have hcoord : |image 2| ≤ ‖image‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le image (2 : Fin 3)
    have hcoordPos : 0 < |image 2| := by
      dsimp only [image, pureWZ2LineClassNormalizationLinear]
      simp only [point3_coord2, abs_mul, abs_of_pos hlambdaPos]
      positivity
    exact hcoordPos.trans_le hcoord
  have himageVertical : lambda / 2 ≤ |image 2| := by
    dsimp only [image, pureWZ2LineClassNormalizationLinear]
    simp only [point3_coord2, abs_mul, abs_of_pos hlambdaPos]
    nlinarith
  apply (le_div_iff₀ himagePos).2
  rw [hdirection] at himageNorm
  nlinarith

/-- The normalized direction/inverse-transpose-normal product has a uniform
lower bound.  Hence incidence does not acquire a growing condition-number
loss for this terminal map. -/
theorem pureWZ2LineClassNormalization_direction_normal_product_lower
    {lambda : ℝ} (hlambda : 1 ≤ lambda)
    {direction normal : Point3}
    (hdirection : ‖direction‖ = 1)
    (hvertical : (1 / 2 : ℝ) ≤ |direction 2|)
    (hnormal : ‖normal‖ = 1) :
    (1 / 2 : ℝ) ≤
      ‖pureWZ2LineClassNormalizationLinear lambda direction‖ *
      ‖pureWZ2LineClassNormalizationNormal lambda normal‖ := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  let directionImage := pureWZ2LineClassNormalizationLinear lambda direction
  let normalImage := pureWZ2LineClassNormalizationNormal lambda normal
  have hdirectionLower : ‖direction‖ ≤ ‖directionImage‖ := by
    have hsource := point3_coord_norm_sq direction
    have htarget := point3_coord_norm_sq directionImage
    have hsquare : ‖direction‖ ^ 2 ≤ ‖directionImage‖ ^ 2 := by
      rw [htarget, hsource]
      simp only [directionImage, pureWZ2LineClassNormalizationLinear,
        point3_coord0, point3_coord1, point3_coord2]
      have hscale : 1 ≤ lambda ^ 2 := by nlinarith [sq_nonneg lambda]
      nlinarith [sq_nonneg (direction 0), sq_nonneg (direction 2)]
    exact (sq_le_sq₀ (norm_nonneg direction)
      (norm_nonneg directionImage)).mp hsquare
  have hnormalLower : (1 / lambda) * ‖normal‖ ≤ ‖normalImage‖ := by
    have hsource := point3_coord_norm_sq normal
    have htarget := point3_coord_norm_sq normalImage
    have hsquare : ((1 / lambda) * ‖normal‖) ^ 2 ≤ ‖normalImage‖ ^ 2 := by
      rw [htarget, mul_pow, hsource]
      simp only [normalImage, pureWZ2LineClassNormalizationNormal,
        point3_coord0, point3_coord1, point3_coord2]
      field_simp [hlambdaPos.ne']
      have hscale : 1 ≤ lambda ^ 2 := by nlinarith [sq_nonneg lambda]
      nlinarith [sq_nonneg (normal 1)]
    exact (sq_le_sq₀ (mul_nonneg (by positivity) (norm_nonneg normal))
      (norm_nonneg normalImage)).mp hsquare
  have hdirectionStrong : lambda / 2 ≤ ‖directionImage‖ := by
    have hcoord : |directionImage 2| ≤ ‖directionImage‖ := by
      simpa [Real.norm_eq_abs] using
        PiLp.norm_apply_le directionImage (2 : Fin 3)
    have hcoordValue : |directionImage 2| = lambda * |direction 2| := by
      dsimp only [directionImage, pureWZ2LineClassNormalizationLinear]
      simp only [point3_coord2, abs_mul, abs_of_pos hlambdaPos]
    rw [hcoordValue] at hcoord
    nlinarith [mul_le_mul_of_nonneg_left hvertical hlambdaPos.le]
  rw [hdirection] at hdirectionLower
  rw [hnormal] at hnormalLower
  simp only [mul_one] at hnormalLower
  have hnormalNonnegative : 0 ≤ (1 / lambda : ℝ) := by positivity
  calc
    (1 / 2 : ℝ) = (lambda / 2) * (1 / lambda) := by
      field_simp [hlambdaPos.ne']
    _ ≤ ‖directionImage‖ * ‖normalImage‖ :=
      mul_le_mul hdirectionStrong hnormalLower hnormalNonnegative
        (norm_nonneg directionImage)

/-- The inverse transpose of `diag(lambda,1,lambda)` is nonexpanding once
`lambda >= 1`. -/
theorem pureWZ2LineClassNormalizationNormal_norm_le
    {lambda : ℝ} (hlambda : 1 ≤ lambda) (normal : Point3) :
    ‖pureWZ2LineClassNormalizationNormal lambda normal‖ ≤ ‖normal‖ := by
  have hsource := point3_coord_norm_sq normal
  have htarget := point3_coord_norm_sq
    (pureWZ2LineClassNormalizationNormal lambda normal)
  have hzero : (normal 0 / lambda) ^ 2 ≤ normal 0 ^ 2 := by
    rw [div_pow]
    exact div_le_self (sq_nonneg _) (by nlinarith [sq_nonneg lambda])
  have htwo : (normal 2 / lambda) ^ 2 ≤ normal 2 ^ 2 := by
    rw [div_pow]
    exact div_le_self (sq_nonneg _) (by nlinarith [sq_nonneg lambda])
  have hsquare :
      ‖pureWZ2LineClassNormalizationNormal lambda normal‖ ^ 2 ≤
        ‖normal‖ ^ 2 := by
    rw [htarget, hsource]
    simp only [pureWZ2LineClassNormalizationNormal, point3_coord0,
      point3_coord1, point3_coord2]
    nlinarith [hzero, htwo]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

/-- The inverse-transpose pairing identity for the line-class map. -/
theorem pureWZ2LineClassNormalization_inner_identity
    {lambda : ℝ} (hlambda : 0 < lambda)
    (direction normal : Point3) :
    inner ℝ (pureWZ2LineClassNormalizationLinear lambda direction)
        (pureWZ2LineClassNormalizationNormal lambda normal) =
      inner ℝ direction normal := by
  simp [pureWZ2LineClassNormalizationLinear,
    pureWZ2LineClassNormalizationNormal, point3, PiLp.inner_apply,
    Fin.sum_univ_succ]
  field_simp [hlambda.ne']

/-- On a literal constant-`y` source slice, the inverse of
`diag(lambda,1,lambda)` gains the full factor `lambda`. -/
theorem pureWZ2LineClassNormalization_source_dist_le_of_same_y
    {lambda : ℝ} (hlambda : 1 ≤ lambda)
    (center first second : Point3) (hsame : first 1 = second 1) :
    lambda * dist first second ≤
      dist (pureWZ2LineClassNormalizationMap center lambda first)
        (pureWZ2LineClassNormalizationMap center lambda second) := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  rw [dist_eq_norm, dist_eq_norm]
  have hdifference :
      pureWZ2LineClassNormalizationMap center lambda first -
          pureWZ2LineClassNormalizationMap center lambda second =
        lambda • (first - second) := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2LineClassNormalizationMap, point3, PiLp.sub_apply,
        PiLp.smul_apply, hsame] <;> ring
  rw [hdifference, norm_smul, Real.norm_eq_abs, abs_of_pos hlambdaPos]

/-- Pulling back two points of an exact image of a constant-`y` slice costs
exactly `lambda^-1`. -/
theorem pureWZ2LineClassNormalization_inverse_dist_le_of_same_y
    {source : Set Point3} {y0 : ℝ}
    (hsource : ∀ point ∈ source, point 1 = y0)
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    (first second : {point : Point3 //
      point ∈ pureWZ2LineClassNormalizationMap center lambda '' source}) :
    lambda *
        dist
          ((pureWZ2LineClassNormalizationAffineEquiv center lambda
            (lt_of_lt_of_le (by norm_num) hlambda)).symm first : Point3)
          ((pureWZ2LineClassNormalizationAffineEquiv center lambda
            (lt_of_lt_of_le (by norm_num) hlambda)).symm second : Point3) ≤
      dist (first : Point3) (second : Point3) := by
  let lambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  let equivalence :=
    pureWZ2LineClassNormalizationAffineEquiv center lambda lambdaPos
  let firstSource : Point3 := equivalence.symm first
  let secondSource : Point3 := equivalence.symm second
  have hfirstSource : firstSource ∈ source := by
    rcases first.property with ⟨sourcePoint, hsourcePoint, hfirst⟩
    have hfirst' : (first : Point3) = equivalence sourcePoint := by
      rw [pureWZ2LineClassNormalizationAffineEquiv_apply]
      exact hfirst.symm
    dsimp only [firstSource]
    rw [hfirst', AffineEquiv.symm_apply_apply]
    exact hsourcePoint
  have hsecondSource : secondSource ∈ source := by
    rcases second.property with ⟨sourcePoint, hsourcePoint, hsecond⟩
    have hsecond' : (second : Point3) = equivalence sourcePoint := by
      rw [pureWZ2LineClassNormalizationAffineEquiv_apply]
      exact hsecond.symm
    dsimp only [secondSource]
    rw [hsecond', AffineEquiv.symm_apply_apply]
    exact hsourcePoint
  have hsame : firstSource 1 = secondSource 1 := by
    rw [hsource firstSource hfirstSource, hsource secondSource hsecondSource]
  have hdist := pureWZ2LineClassNormalization_source_dist_le_of_same_y
    hlambda center firstSource secondSource hsame
  have hfirstMap :
      pureWZ2LineClassNormalizationMap center lambda firstSource = first := by
    rw [← pureWZ2LineClassNormalizationAffineEquiv_apply]
    exact equivalence.apply_symm_apply first
  have hsecondMap :
      pureWZ2LineClassNormalizationMap center lambda secondSource = second := by
    rw [← pureWZ2LineClassNormalizationAffineEquiv_apply]
    exact equivalence.apply_symm_apply second
  simpa only [firstSource, secondSource, hfirstMap, hsecondMap,
    Subtype.dist_eq] using hdist

/-- The line-class normalization is noncontracting in every direction when
`lambda >= 1`. -/
theorem pureWZ2LineClassNormalization_source_dist_le
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    (first second : Point3) :
    dist first second ≤
      dist (pureWZ2LineClassNormalizationMap center lambda first)
        (pureWZ2LineClassNormalizationMap center lambda second) := by
  rw [dist_eq_norm, dist_eq_norm]
  have hdifference :
      pureWZ2LineClassNormalizationMap center lambda first -
          pureWZ2LineClassNormalizationMap center lambda second =
        pureWZ2LineClassNormalizationLinear lambda (first - second) := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2LineClassNormalizationMap,
        pureWZ2LineClassNormalizationLinear, point3, PiLp.sub_apply] <;> ring
  rw [hdifference]
  have hsource := point3_coord_norm_sq (first - second)
  have htarget := point3_coord_norm_sq
    (pureWZ2LineClassNormalizationLinear lambda (first - second))
  have hsquare : ‖first - second‖ ^ 2 ≤
      ‖pureWZ2LineClassNormalizationLinear lambda (first - second)‖ ^ 2 := by
    rw [hsource, htarget]
    simp only [pureWZ2LineClassNormalizationLinear, point3_coord0,
      point3_coord1, point3_coord2]
    have hscale : 1 ≤ lambda ^ 2 := by nlinarith [sq_nonneg lambda]
    have hx : (first 0 - second 0) ^ 2 ≤
        lambda ^ 2 * (first 0 - second 0) ^ 2 := by
      nlinarith [sq_nonneg (first 0 - second 0)]
    have hz : (first 2 - second 2) ^ 2 ≤
        lambda ^ 2 * (first 2 - second 2) ^ 2 := by
      nlinarith [sq_nonneg (first 2 - second 2)]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

end Kakeya.Assouad

end
