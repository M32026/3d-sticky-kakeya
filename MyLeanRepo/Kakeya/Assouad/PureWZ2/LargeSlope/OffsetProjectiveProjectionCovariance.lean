import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.OffsetProjectiveTotalNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SignedScalarPaperAD

/-!
# Scalar-projection covariance for the total offset-projective map

The total point map is affine with linear part
`pureWZ2OffsetProjectiveTotalLinear`.  Pairing its linear part with the actual
unit transported normal gives a scalar multiple of the source projection.
The multiplier retains the sign of the projective chart coordinate; its
absolute value is used only when transferring the paper AD scale.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The total affine point map with an arbitrary translation. -/
def pureWZ2OffsetProjectiveTotalAffineMap
    (a b S lambda : ℝ) (translation : Point3) : Point3 → Point3 :=
  fun point =>
    pureWZ2OffsetProjectiveTotalLinear a b S lambda point + translation

/-- The exact signed scalar relating source projection along `normal` to
target projection along the actual normalized projective normal. -/
def pureWZ2OffsetProjectiveProjectionScale
    (a b S lambda : ℝ) (normal : Point3) : ℝ :=
  ‖pureWZ2OffsetProjectiveTotalNormal b S lambda
      (pureWZ2OffsetShearProjectiveNormal a normal)‖⁻¹ *
    (b / pureWZ2OffsetShearNormal a normal 1)

/-- The translation term in scalar-projection covariance. -/
def pureWZ2OffsetProjectiveProjectionOffset
    (a b S lambda : ℝ) (normal translation : Point3) : ℝ :=
  inner ℝ translation
    (pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda
      (pureWZ2OffsetShearProjectiveNormal a normal))

/-- Translation cancels from point differences, leaving precisely the total
linear map. -/
theorem pureWZ2OffsetProjectiveTotalAffineMap_sub
    (a b S lambda : ℝ) (translation first second : Point3) :
    pureWZ2OffsetProjectiveTotalAffineMap a b S lambda translation first -
        pureWZ2OffsetProjectiveTotalAffineMap a b S lambda translation second =
      pureWZ2OffsetProjectiveTotalLinear a b S lambda (first - second) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2OffsetProjectiveTotalAffineMap,
      pureWZ2OffsetProjectiveTotalLinear, point3] <;> ring

/-- Any point map whose differences from one fixed center are governed by the
total linear map is the corresponding total affine map.  This formulation is
translation-invariant and lets a geometric map expose only its centered
difference identity. -/
theorem pureWZ2OffsetProjective_eq_totalAffineMap_of_sub
    (a b S lambda : ℝ) (F : Point3 → Point3) (center point : Point3)
    (hsub : ∀ x, F x - F center =
      pureWZ2OffsetProjectiveTotalLinear a b S lambda (x - center)) :
    F point =
      pureWZ2OffsetProjectiveTotalAffineMap a b S lambda
        (F center -
          pureWZ2OffsetProjectiveTotalLinear a b S lambda center) point := by
  have hlinearSub :
      pureWZ2OffsetProjectiveTotalLinear a b S lambda (point - center) =
        pureWZ2OffsetProjectiveTotalLinear a b S lambda point -
          pureWZ2OffsetProjectiveTotalLinear a b S lambda center := by
    simpa [pureWZ2OffsetProjectiveTotalAffineMap] using
      (pureWZ2OffsetProjectiveTotalAffineMap_sub
        a b S lambda (0 : Point3) point center).symm
  calc
    F point = (F point - F center) + F center := by abel
    _ = pureWZ2OffsetProjectiveTotalLinear a b S lambda (point - center) +
        F center := by rw [hsub point]
    _ = (pureWZ2OffsetProjectiveTotalLinear a b S lambda point -
          pureWZ2OffsetProjectiveTotalLinear a b S lambda center) +
        F center := by rw [hlinearSub]
    _ = pureWZ2OffsetProjectiveTotalAffineMap a b S lambda
        (F center -
          pureWZ2OffsetProjectiveTotalLinear a b S lambda center) point := by
      simp only [pureWZ2OffsetProjectiveTotalAffineMap]
      abel

/-- Exact covariance for the linear part and the normalized projective normal.
No positivity assumption is imposed on the chart coordinate. -/
theorem pureWZ2OffsetProjectiveTotal_normalized_projective_inner
    {a b S lambda : ℝ}
    (hb : b ≠ 0) (hS : S ≠ 0) (hlambda : lambda ≠ 0)
    (direction normal : Point3)
    (hw : pureWZ2OffsetShearNormal a normal 1 ≠ 0) :
    inner ℝ (pureWZ2OffsetProjectiveTotalLinear a b S lambda direction)
        (pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda
          (pureWZ2OffsetShearProjectiveNormal a normal)) =
      pureWZ2OffsetProjectiveProjectionScale a b S lambda normal *
        inner ℝ direction normal := by
  rw [pureWZ2OffsetProjectiveTotalNormalizedNormal, inner_smul_right]
  rw [pureWZ2OffsetProjectiveTotal_projective_inner
    hb hS hlambda direction normal hw]
  simp only [pureWZ2OffsetProjectiveProjectionScale]
  ring

/-- Pairwise form of covariance: the translation in the total affine point
map cancels, and projection of the target difference is exactly the signed
scalar multiple of projection of the source difference. -/
theorem pureWZ2OffsetProjectiveTotalAffineMap_projection_sub
    {a b S lambda : ℝ}
    (hb : b ≠ 0) (hS : S ≠ 0) (hlambda : lambda ≠ 0)
    (normal translation first second : Point3)
    (hw : pureWZ2OffsetShearNormal a normal 1 ≠ 0) :
    inner ℝ
        (pureWZ2OffsetProjectiveTotalAffineMap a b S lambda translation first -
          pureWZ2OffsetProjectiveTotalAffineMap a b S lambda translation second)
        (pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda
          (pureWZ2OffsetShearProjectiveNormal a normal)) =
      pureWZ2OffsetProjectiveProjectionScale a b S lambda normal *
        inner ℝ (first - second) normal := by
  rw [pureWZ2OffsetProjectiveTotalAffineMap_sub]
  exact pureWZ2OffsetProjectiveTotal_normalized_projective_inner
    hb hS hlambda (first - second) normal hw

/-- The signed projection multiplier is nonzero on the projective chart. -/
theorem pureWZ2OffsetProjectiveProjectionScale_ne_zero
    {a b S lambda : ℝ} {normal : Point3}
    (hb : b ≠ 0) (hw : pureWZ2OffsetShearNormal a normal 1 ≠ 0) :
    pureWZ2OffsetProjectiveProjectionScale a b S lambda normal ≠ 0 := by
  have hnorm_pos : 0 <
      ‖pureWZ2OffsetProjectiveTotalNormal b S lambda
        (pureWZ2OffsetShearProjectiveNormal a normal)‖ :=
    zero_lt_one.trans_le
      (pureWZ2OffsetProjectiveTotalNormal_norm_lower b S lambda
        (pureWZ2OffsetShearProjectiveNormal a normal))
  exact mul_ne_zero (inv_ne_zero hnorm_pos.ne') (div_ne_zero hb hw)

/-- Pointwise affine covariance of scalar projection. -/
theorem pureWZ2OffsetProjectiveTotalAffineMap_projection_pointwise
    {a b S lambda : ℝ}
    (hb : b ≠ 0) (hS : S ≠ 0) (hlambda : lambda ≠ 0)
    (normal translation point : Point3)
    (hw : pureWZ2OffsetShearNormal a normal 1 ≠ 0) :
    inner ℝ
        (pureWZ2OffsetProjectiveTotalAffineMap a b S lambda translation point)
        (pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda
          (pureWZ2OffsetShearProjectiveNormal a normal)) =
      pureWZ2OffsetProjectiveProjectionScale a b S lambda normal *
          inner ℝ point normal +
        pureWZ2OffsetProjectiveProjectionOffset
          a b S lambda normal translation := by
  rw [show pureWZ2OffsetProjectiveTotalAffineMap
      a b S lambda translation point =
        pureWZ2OffsetProjectiveTotalLinear a b S lambda point + translation by rfl]
  rw [inner_add_left,
    pureWZ2OffsetProjectiveTotal_normalized_projective_inner
      hb hS hlambda point normal hw]
  rfl

/-- Set-level exact covariance: the target projection is a signed nonzero
scalar affine image of the source projection. -/
theorem pureWZ2OffsetProjectiveTotalAffineMap_projection_set
    {a b S lambda : ℝ}
    (hb : b ≠ 0) (hS : S ≠ 0) (hlambda : lambda ≠ 0)
    (normal translation : Point3)
    (hw : pureWZ2OffsetShearNormal a normal 1 ≠ 0)
    (source : Set Point3) :
    scalarProjection
        (pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda
          (pureWZ2OffsetShearProjectiveNormal a normal))
        (pureWZ2OffsetProjectiveTotalAffineMap
          a b S lambda translation '' source) =
      (fun value : ℝ =>
        pureWZ2OffsetProjectiveProjectionScale a b S lambda normal * value +
          pureWZ2OffsetProjectiveProjectionOffset
            a b S lambda normal translation) ''
        scalarProjection normal source := by
  ext value
  constructor
  · rintro ⟨target, ⟨point, hpoint, rfl⟩, rfl⟩
    refine ⟨inner ℝ point normal, ⟨point, hpoint, rfl⟩, ?_⟩
    exact (pureWZ2OffsetProjectiveTotalAffineMap_projection_pointwise
      hb hS hlambda normal translation point hw).symm
  · rintro ⟨sourceValue, ⟨point, hpoint, rfl⟩, rfl⟩
    refine ⟨pureWZ2OffsetProjectiveTotalAffineMap
      a b S lambda translation point, ⟨point, hpoint, rfl⟩, ?_⟩
    exact pureWZ2OffsetProjectiveTotalAffineMap_projection_pointwise
      hb hS hlambda normal translation point hw

/-- Existential form of set covariance, exposing that the affine scalar map
has nonzero linear coefficient. -/
theorem pureWZ2OffsetProjectiveTotalAffineMap_projection_set_exists
    {a b S lambda : ℝ}
    (hb : b ≠ 0) (hS : S ≠ 0) (hlambda : lambda ≠ 0)
    (normal translation : Point3)
    (hw : pureWZ2OffsetShearNormal a normal 1 ≠ 0)
    (source : Set Point3) :
    ∃ scale offset : ℝ, scale ≠ 0 ∧
      scalarProjection
          (pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda
            (pureWZ2OffsetShearProjectiveNormal a normal))
          (pureWZ2OffsetProjectiveTotalAffineMap
            a b S lambda translation '' source) =
        (fun value : ℝ => scale * value + offset) ''
          scalarProjection normal source := by
  refine ⟨pureWZ2OffsetProjectiveProjectionScale a b S lambda normal,
    pureWZ2OffsetProjectiveProjectionOffset a b S lambda normal translation,
    pureWZ2OffsetProjectiveProjectionScale_ne_zero hb hw, ?_⟩
  exact pureWZ2OffsetProjectiveTotalAffineMap_projection_set
    hb hS hlambda normal translation hw source

/-- Set-level covariance for any point map specified only by its centered
difference identity. -/
theorem pureWZ2OffsetProjective_projection_set_of_sub
    {a b S lambda : ℝ}
    (hb : b ≠ 0) (hS : S ≠ 0) (hlambda : lambda ≠ 0)
    (F : Point3 → Point3) (center normal : Point3)
    (hsub : ∀ x, F x - F center =
      pureWZ2OffsetProjectiveTotalLinear a b S lambda (x - center))
    (hw : pureWZ2OffsetShearNormal a normal 1 ≠ 0)
    (source : Set Point3) :
    scalarProjection
        (pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda
          (pureWZ2OffsetShearProjectiveNormal a normal))
        (F '' source) =
      (fun value : ℝ =>
        pureWZ2OffsetProjectiveProjectionScale a b S lambda normal * value +
          pureWZ2OffsetProjectiveProjectionOffset a b S lambda normal
            (F center -
              pureWZ2OffsetProjectiveTotalLinear a b S lambda center)) ''
        scalarProjection normal source := by
  have himage : F '' source =
      pureWZ2OffsetProjectiveTotalAffineMap a b S lambda
        (F center -
          pureWZ2OffsetProjectiveTotalLinear a b S lambda center) '' source := by
    apply Set.image_congr
    intro point hpoint
    exact pureWZ2OffsetProjective_eq_totalAffineMap_of_sub
      a b S lambda F center point hsub
  rw [himage]
  exact pureWZ2OffsetProjectiveTotalAffineMap_projection_set
    hb hS hlambda normal
      (F center - pureWZ2OffsetProjectiveTotalLinear a b S lambda center)
      hw source

/-- Paper AD transport under a signed affine map of the real line. -/
theorem PureWZ2PaperADSet1.signed_affine_transfer
    {source : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 source delta alpha C)
    {scale offset : ℝ} (hscale : scale ≠ 0) :
    PureWZ2PaperADSet1
      ((fun value : ℝ => scale * value + offset) '' source)
      (|scale| * delta) alpha C := by
  rcases lt_or_gt_of_ne hscale with hscale_neg | hscale_pos
  · have hpositive : 0 < -scale := by linarith
    have himage :
        (fun value : ℝ => scale * value + offset) '' source =
          (fun value : ℝ => (-scale) * value + offset) ''
            ((fun value : ℝ => -value) '' source) := by
      rw [Set.image_image]
      congr 1
      funext value
      ring
    rw [himage]
    have htransferred := hAD.neg_transfer.affine_transfer
      (a := -scale) (b := offset) hpositive
    simpa [abs_of_neg hscale_neg] using htransferred
  · have htransferred := hAD.affine_transfer
      (a := scale) (b := offset) hscale_pos
    simpa [abs_of_pos hscale_pos] using htransferred

/-- Exact paper-AD transfer through the total affine point map and the actual
normalized projective normal.  The target scale uses the absolute value of
the signed chart multiplier. -/
theorem pureWZ2OffsetProjectiveTotalAffineMap_projection_paperAD
    {a b S lambda delta alpha : ℝ} {C : ENNReal}
    (hb : b ≠ 0) (hS : S ≠ 0) (hlambda : lambda ≠ 0)
    (normal translation : Point3)
    (hw : pureWZ2OffsetShearNormal a normal 1 ≠ 0)
    (source : Set Point3)
    (hsource : PureWZ2PaperADSet1
      (scalarProjection normal source) delta alpha C) :
    PureWZ2PaperADSet1
      (scalarProjection
        (pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda
          (pureWZ2OffsetShearProjectiveNormal a normal))
        (pureWZ2OffsetProjectiveTotalAffineMap
          a b S lambda translation '' source))
      (|pureWZ2OffsetProjectiveProjectionScale a b S lambda normal| * delta)
      alpha C := by
  rw [pureWZ2OffsetProjectiveTotalAffineMap_projection_set
    hb hS hlambda normal translation hw source]
  exact hsource.signed_affine_transfer
    (pureWZ2OffsetProjectiveProjectionScale_ne_zero hb hw)

/-- Paper-AD transfer for any point map specified only by its centered
difference identity.  In particular, an upstream geometric map may discharge
`hsub` directly with its own `totalAffineMap_sub` theorem. -/
theorem pureWZ2OffsetProjective_projection_paperAD_of_sub
    {a b S lambda delta alpha : ℝ} {C : ENNReal}
    (hb : b ≠ 0) (hS : S ≠ 0) (hlambda : lambda ≠ 0)
    (F : Point3 → Point3) (center normal : Point3)
    (hsub : ∀ x, F x - F center =
      pureWZ2OffsetProjectiveTotalLinear a b S lambda (x - center))
    (hw : pureWZ2OffsetShearNormal a normal 1 ≠ 0)
    (source : Set Point3)
    (hsource : PureWZ2PaperADSet1
      (scalarProjection normal source) delta alpha C) :
    PureWZ2PaperADSet1
      (scalarProjection
        (pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda
          (pureWZ2OffsetShearProjectiveNormal a normal))
        (F '' source))
      (|pureWZ2OffsetProjectiveProjectionScale a b S lambda normal| * delta)
      alpha C := by
  rw [pureWZ2OffsetProjective_projection_set_of_sub
    hb hS hlambda F center normal hsub hw source]
  exact hsource.signed_affine_transfer
    (pureWZ2OffsetProjectiveProjectionScale_ne_zero hb hw)

end Kakeya.Assouad

end
