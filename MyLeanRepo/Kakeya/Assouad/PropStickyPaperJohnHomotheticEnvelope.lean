import MyLeanRepo.Kakeya.Assouad.PropStickyPaperJohnHomotheticEnvelopeStatements

/-!
# Common homothetic envelope from the outer John ellipsoid

Let `E` be the outer John ellipsoid of a three-dimensional convex body `K`,
with center `c`. The John inclusion gives
`homothety c (1 / 3) '' E ⊆ K ⊆ E`, hence
`volume E ≤ 27 * volume K`.

For every `point ∈ K`, the factor-`100` homothety of `K` about `point` lies
in the common factor-`199` homothety of `E` about `c`.
-/

noncomputable section

open MeasureTheory
open scoped Pointwise Real

namespace Kakeya.Assouad

private lemma john_homothetic_envelope_point_inclusion
    {center : Point3}
    {linear : Point3 ≃ₗ[ℝ] Point3}
    {sourcePoint homothetyCenter : Point3}
    (hsourcePoint :
      sourcePoint ∈
        JohnEllipsoid.ellipsoid center linear)
    (hcenter :
      homothetyCenter ∈
        JohnEllipsoid.ellipsoid center linear) :
    AffineMap.homothety homothetyCenter (100 : ℝ)
        sourcePoint ∈
      AffineMap.homothety center (199 : ℝ) ''
        JohnEllipsoid.ellipsoid center linear := by
  have hsourceNorm :
      ‖linear.symm (sourcePoint - center)‖ ≤ 1 :=
    (JohnEllipsoid.ellipsoid_mem_iff
      center linear sourcePoint).mp hsourcePoint
  have hcenterNorm :
      ‖linear.symm (homothetyCenter - center)‖ ≤ 1 :=
    (JohnEllipsoid.ellipsoid_mem_iff
      center linear homothetyCenter).mp hcenter
  let sourceVector :=
    linear.symm (sourcePoint - center)
  let centerVector :=
    linear.symm (homothetyCenter - center)
  let envelopePoint : Point3 :=
    center +
      (1 / 199 : ℝ) •
        ((100 : ℝ) • (sourcePoint - center) -
          (99 : ℝ) • (homothetyCenter - center))
  have henvelopeCoordinates :
      linear.symm (envelopePoint - center) =
        (1 / 199 : ℝ) •
          ((100 : ℝ) • sourceVector -
            (99 : ℝ) • centerVector) := by
    simp [envelopePoint, sourceVector, centerVector,
      map_sub, map_smul]
  have hcombination :
      ‖(100 : ℝ) • sourceVector -
          (99 : ℝ) • centerVector‖ ≤
        199 := by
    calc
      ‖(100 : ℝ) • sourceVector -
          (99 : ℝ) • centerVector‖
          ≤ ‖(100 : ℝ) • sourceVector‖ +
              ‖(99 : ℝ) • centerVector‖ :=
        norm_sub_le _ _
      _ = (100 : ℝ) * ‖sourceVector‖ +
            (99 : ℝ) * ‖centerVector‖ := by
        simp [norm_smul]
      _ ≤ (100 : ℝ) * 1 + (99 : ℝ) * 1 := by
        gcongr
      _ = 199 := by norm_num
  have henvelopePoint :
      envelopePoint ∈
        JohnEllipsoid.ellipsoid center linear := by
    rw [JohnEllipsoid.ellipsoid_mem_iff,
      henvelopeCoordinates]
    calc
      ‖(1 / 199 : ℝ) •
          ((100 : ℝ) • sourceVector -
            (99 : ℝ) • centerVector)‖ =
          (1 / 199 : ℝ) *
            ‖(100 : ℝ) • sourceVector -
              (99 : ℝ) • centerVector‖ := by
        simp [norm_smul]
      _ ≤ (1 / 199 : ℝ) * 199 := by gcongr
      _ = 1 := by norm_num
  have hscaled :
      (199 : ℝ) • (envelopePoint - center) =
        (100 : ℝ) • (sourcePoint - center) -
          (99 : ℝ) • (homothetyCenter - center) := by
    simp [envelopePoint, smul_sub, smul_smul]
  refine ⟨envelopePoint, henvelopePoint, ?_⟩
  rw [AffineMap.homothety_apply,
    AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  rw [hscaled]
  module

theorem wz2_paper_john_homothetic_envelope :
    WZ2PaperJohnHomotheticEnvelopeStatement := by
  intro convexBody hbody
  let center : Point3 :=
    JohnEllipsoid.IsConvexBody.outerJohnEllipsoidCenter hbody
  let linear : Point3 ≃ₗ[ℝ] Point3 :=
    JohnEllipsoid.IsConvexBody.outerJohnEllipsoidMap hbody
  let ellipsoid : Set Point3 :=
    JohnEllipsoid.IsConvexBody.outerJohnEllipsoid hbody
  let envelope : Set Point3 :=
    AffineMap.homothety center (199 : ℝ) '' ellipsoid
  refine ⟨envelope, ?_, ?_, ?_⟩
  · have hellipsoidConvex : Convex ℝ ellipsoid :=
      JohnEllipsoid.ellipsoid_convex center linear
    exact
      hellipsoidConvex.affine_image
        (AffineMap.homothety center (199 : ℝ))
  · have hspec :
        JohnEllipsoid.IsOuterJohnEllipsoid
          convexBody center linear :=
      JohnEllipsoid.IsConvexBody.outerJohnEllipsoid_spec hbody
    have hinner :
        AffineMap.homothety center ((3 : ℝ)⁻¹) ''
            ellipsoid ⊆
          convexBody :=
      JohnEllipsoid.IsConvexBody.homothety_subset_outerJohnEllipsoid_main
        hbody
    have hinnerVolume :
        ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid ≤
          volume convexBody := by
      calc
        ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid =
            volume
              (AffineMap.homothety
                center ((3 : ℝ)⁻¹) '' ellipsoid) := by
          rw [JohnEllipsoid.volume_homothety]
          norm_num
        _ ≤ volume convexBody := measure_mono hinner
    have hellipsoidVolume :
        volume ellipsoid ≤
          (27 : ENNReal) * volume convexBody := by
      have htwentySeven :
          (27 : ENNReal) =
            ENNReal.ofReal (27 : ℝ) := by
        norm_cast
      have hcancel :
          (27 : ENNReal) *
              ENNReal.ofReal (1 / 27 : ℝ) =
            1 := by
        rw [htwentySeven,
          ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      calc
        volume ellipsoid =
            (27 : ENNReal) *
              (ENNReal.ofReal (1 / 27 : ℝ) *
                volume ellipsoid) := by
          rw [← mul_assoc, hcancel, one_mul]
        _ ≤ (27 : ENNReal) * volume convexBody := by
          gcongr
    rw [JohnEllipsoid.volume_homothety]
    have hscale :
        ENNReal.ofReal (|(199 : ℝ)| ^ 3) =
          (199 ^ 3 : ENNReal) := by
      norm_num
    rw [hscale]
    calc
      (199 ^ 3 : ENNReal) * volume ellipsoid
          ≤ (199 ^ 3 : ENNReal) *
              ((27 : ENNReal) * volume convexBody) := by
        gcongr
      _ = (212776173 : ENNReal) * volume convexBody := by
        norm_num
        ring
  · intro homothetyCenter hcenter
    have hspec :
        JohnEllipsoid.IsOuterJohnEllipsoid
          convexBody center linear :=
      JohnEllipsoid.IsConvexBody.outerJohnEllipsoid_spec hbody
    have hcenterEllipsoid : homothetyCenter ∈ ellipsoid :=
      hspec.1 hcenter
    intro point hpoint
    rcases hpoint with ⟨sourcePoint, hsourcePoint, rfl⟩
    exact
      john_homothetic_envelope_point_inclusion
        (hspec.1 hsourcePoint) hcenterEllipsoid

end Kakeya.Assouad

end
