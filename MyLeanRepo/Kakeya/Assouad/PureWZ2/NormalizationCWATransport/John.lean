import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCWATransport.Basic
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Transport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.AffineMapVolumeTransport

/-!
# John ellipsoid transport through affine isometries

Uses the landed `JohnEllipsoid.Transport` module (linear isometry version)
plus translation to prove affine isometry transport.
-/

noncomputable section

open MeasureTheory JohnEllipsoid

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

variable (e : Point3 ≃ᵃⁱ[ℝ] Point3)

/-! ### 4. John ellipsoid transport (using landed module) -/

/-- The image of an ellipsoid under an affine isometry is an ellipsoid. -/
lemma affineIsometry_image_ellipsoid (c : Point3) (A : Point3 ≃ₗ[ℝ] Point3) :
    e '' JohnEllipsoid.ellipsoid c A =
    JohnEllipsoid.ellipsoid (e c) (JohnEllipsoid.conj e.linearIsometryEquiv A) := by
  let l := e.linearIsometryEquiv
  let v := e 0
  have h_decomp : ∀ (x : Point3), e x = v + l x := by
    intro x
    have h' := affine_isometry_map_add e 0 x
    simpa [v, l] using h'
  have h_img : e '' JohnEllipsoid.ellipsoid c A = (fun x : Point3 => v + x) '' (l '' JohnEllipsoid.ellipsoid c A) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨l x, ⟨x, hx, rfl⟩, (h_decomp x).symm⟩
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, h_decomp x⟩
  rw [h_img]
  have h1 : l '' JohnEllipsoid.ellipsoid c A =
      JohnEllipsoid.ellipsoid (l c) (JohnEllipsoid.conj l A) :=
    JohnEllipsoid.image_ellipsoid l c A
  rw [h1]
  have h2 : (fun x : Point3 => v + x) '' JohnEllipsoid.ellipsoid (l c) (JohnEllipsoid.conj l A) =
      JohnEllipsoid.ellipsoid (v + l c) (JohnEllipsoid.conj l A) := by
    let B := JohnEllipsoid.conj l A
    let d := l c
    have h_def1 : JohnEllipsoid.ellipsoid d B = (fun x : Point3 => d +ᵥ x) '' (B '' Metric.closedBall (0 : Point3) 1) := by rfl
    have h_def2 : JohnEllipsoid.ellipsoid (v + d) B = (fun x : Point3 => (v + d) +ᵥ x) '' (B '' Metric.closedBall (0 : Point3) 1) := by rfl
    rw [h_def1, h_def2, Set.image_image]
    congr
    funext z
    have h : v + (d +ᵥ z) = (v + d) +ᵥ z := by
      have h1 : d +ᵥ z = d + z := vadd_eq_add d z
      have h2 : (v + d) +ᵥ z = (v + d) + z := vadd_eq_add (v + d) z
      rw [h1, h2]
      <;> abel
    exact h
  rw [h2]
  have h3 : v + l c = e c := by
    have h4 := affine_isometry_map_add e 0 c
    simpa [v, l] using h4.symm
  rw [h3]

/-- Affine isometry transport of `IsOuterJohnEllipsoid`. -/
lemma affineIsometry_IsOuterJohnEllipsoid_image
    {K : Set Point3} {c : Point3} {A : Point3 ≃ₗ[ℝ] Point3}
    (h : JohnEllipsoid.IsOuterJohnEllipsoid K c A) :
    JohnEllipsoid.IsOuterJohnEllipsoid (e '' K) (e c)
      (JohnEllipsoid.conj e.linearIsometryEquiv A) := by
  let l := e.linearIsometryEquiv
  have h1 : e '' K ⊆ e '' JohnEllipsoid.ellipsoid c A := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, h.1 hx, rfl⟩
  rw [affineIsometry_image_ellipsoid e c A] at h1
  constructor
  · exact h1
  · intro c' A' hsub
    have hsub1 : K ⊆ e.symm '' JohnEllipsoid.ellipsoid c' A' := by
      intro x hx
      have h4 : e x ∈ e '' K := ⟨x, hx, rfl⟩
      have h5 : e x ∈ JohnEllipsoid.ellipsoid c' A' := hsub h4
      exact ⟨e x, h5, by simp⟩
    have h_img_symm : e.symm '' JohnEllipsoid.ellipsoid c' A' =
        JohnEllipsoid.ellipsoid (e.symm c')
          (JohnEllipsoid.conj e.symm.linearIsometryEquiv A') :=
      affineIsometry_image_ellipsoid e.symm c' A'
    rw [h_img_symm] at hsub1
    have h4 := h.2 (e.symm c')
      (JohnEllipsoid.conj e.symm.linearIsometryEquiv A') hsub1
    have hvol : volume (JohnEllipsoid.ellipsoid (e.symm c')
              (JohnEllipsoid.conj e.symm.linearIsometryEquiv A')) =
            volume (JohnEllipsoid.ellipsoid c' A') := by
      rw [← h_img_symm, isometry_volume_image e.symm]
    have hvol2 : volume (JohnEllipsoid.ellipsoid (e c)
              (JohnEllipsoid.conj l A)) =
            volume (JohnEllipsoid.ellipsoid c A) := by
      rw [← affineIsometry_image_ellipsoid e c A, isometry_volume_image e]
    rw [hvol] at h4
    rw [hvol2]
    exact h4

/-- Affine isometry transport of the outer John ellipsoid set.

Given `hK : IsConvexBody K` and `hK' : IsConvexBody K'` where `K' = e '' K`,
the outer John ellipsoid of `K'` is exactly `e ''` the outer John ellipsoid of `K`. -/
lemma affineIsometry_outerJohnEllipsoid_image
    {K K' : Set Point3}
    (hK : JohnEllipsoid.IsConvexBody K)
    (hK' : JohnEllipsoid.IsConvexBody K')
    (h_eq : K' = e '' K) :
    hK'.outerJohnEllipsoid = e '' hK.outerJohnEllipsoid := by
  let l := e.linearIsometryEquiv
  let c := hK.outerJohnEllipsoidCenter
  let A := hK.outerJohnEllipsoidMap
  have hE : JohnEllipsoid.IsOuterJohnEllipsoid K c A := hK.outerJohnEllipsoid_spec
  have hE' : JohnEllipsoid.IsOuterJohnEllipsoid K' (e c)
      (JohnEllipsoid.conj l A) := by
    rw [h_eq]
    exact affineIsometry_IsOuterJohnEllipsoid_image e hE
  have h_unique : JohnEllipsoid.ellipsoid (e c) (JohnEllipsoid.conj l A) =
      hK'.outerJohnEllipsoid :=
    JohnEllipsoid.IsConvexBody.outerJohnEllipsoid_unique hK' _ _ hE'
  rw [← h_unique]
  exact (affineIsometry_image_ellipsoid e c A).symm

/-- A linear isometry has determinant of absolute value 1. -/
lemma linearIsometry_det_abs_one :
    |LinearMap.det ((e.linearIsometryEquiv : Point3 →ₗ[ℝ] Point3))| = 1 := by
  let l := e.linearIsometryEquiv
  have hball : l '' Metric.closedBall (0 : Point3) 1 = Metric.closedBall (0 : Point3) 1 := by
    ext x
    simp only [Set.mem_image, Metric.mem_closedBall]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [l.norm_map] using hy
    · intro hx
      refine ⟨l.symm x, ?_, by simp⟩
      simpa [l.symm.norm_map] using hx
  have hvol : volume (JohnEllipsoid.ellipsoid (0 : Point3) l) =
      ENNReal.ofReal |LinearMap.det (l : Point3 →ₗ[ℝ] Point3)| *
        volume (Metric.closedBall (0 : Point3) 1) :=
    JohnEllipsoid.volume_ellipsoid_eq (0 : Point3) l
  have hellip : JohnEllipsoid.ellipsoid (0 : Point3) l = l '' Metric.closedBall (0 : Point3) 1 := by
    simp [JohnEllipsoid.ellipsoid]
  rw [hellip, hball] at hvol
  set V := volume (Metric.closedBall (0 : Point3) 1) with hV
  have hV_pos : 0 < V := Metric.measure_closedBall_pos volume (0 : Point3) (by norm_num)
  have hV_ne_top : V ≠ ⊤ := (ProperSpace.isCompact_closedBall (0 : Point3) 1).measure_ne_top
  have h_eq : V = ENNReal.ofReal |LinearMap.det (l : Point3 →ₗ[ℝ] Point3)| * V := hvol
  have h : ENNReal.ofReal |LinearMap.det (l : Point3 →ₗ[ℝ] Point3)| = 1 := by
    have h' : ENNReal.ofReal |LinearMap.det (l : Point3 →ₗ[ℝ] Point3)| * V = V := h_eq.symm
    have h_cancel : ∀ (a b : ENNReal), a * V = b * V → a = b := by
      intro a b h_ab
      have h_ab' : V * a = V * b := by
        rw [mul_comm V a, mul_comm V b]
        exact h_ab
      exact (ENNReal.mul_right_inj (ne_of_gt hV_pos) hV_ne_top).mp h_ab'
    have h'' : ENNReal.ofReal |LinearMap.det (l : Point3 →ₗ[ℝ] Point3)| * V = 1 * V := by
      rw [one_mul]; exact h'
    exact h_cancel _ _ h''
  have hpos : 0 ≤ |LinearMap.det (l : Point3 →ₗ[ℝ] Point3)| := by positivity
  have h_inj : ∀ (x : ℝ), 0 ≤ x → ENNReal.ofReal x = 1 → x = 1 := by
    intro x hx h
    have h' : (ENNReal.ofReal x).toReal = (1 : ENNReal).toReal := by rw [h]
    have hx' : (ENNReal.ofReal x).toReal = x := ENNReal.toReal_ofReal hx
    rw [hx'] at h'
    simpa using h'
  exact h_inj _ hpos h

/-- If two John ellipsoids have equal volume, their determinant absolute values are equal. -/
private lemma abs_det_eq_of_ellipsoid_volume_eq
    {c c' : Point3} {A A' : Point3 ≃ₗ[ℝ] Point3}
    (h : volume (JohnEllipsoid.ellipsoid c A) = volume (JohnEllipsoid.ellipsoid c' A')) :
    |LinearMap.det (A : Point3 →ₗ[ℝ] Point3)| =
    |LinearMap.det (A' : Point3 →ₗ[ℝ] Point3)| := by
  have hvol1 := JohnEllipsoid.volume_ellipsoid_eq c A
  have hvol2 := JohnEllipsoid.volume_ellipsoid_eq c' A'
  rw [hvol1, hvol2] at h
  set V := volume (Metric.closedBall (0 : Point3) 1) with hV
  have hV_pos : 0 < V := Metric.measure_closedBall_pos volume (0 : Point3) (by norm_num)
  have hV_ne_top : V ≠ ⊤ := (ProperSpace.isCompact_closedBall (0 : Point3) 1).measure_ne_top
  have h' : V * ENNReal.ofReal |LinearMap.det (A : Point3 →ₗ[ℝ] Point3)| =
             V * ENNReal.ofReal |LinearMap.det (A' : Point3 →ₗ[ℝ] Point3)| :=
    by simpa [mul_comm] using h
  have h'' : ENNReal.ofReal |LinearMap.det (A : Point3 →ₗ[ℝ] Point3)| =
              ENNReal.ofReal |LinearMap.det (A' : Point3 →ₗ[ℝ] Point3)| :=
    (ENNReal.mul_right_inj (ne_of_gt hV_pos) hV_ne_top).mp h'
  have hpos1 : 0 ≤ |LinearMap.det (A : Point3 →ₗ[ℝ] Point3)| := by positivity
  have hpos2 : 0 ≤ |LinearMap.det (A' : Point3 →ₗ[ℝ] Point3)| := by positivity
  exact (ENNReal.ofReal_eq_ofReal_iff hpos1 hpos2).mp h''

/-- The coordinate change between two normalizations related by an isometry
has determinant of absolute value 1. -/
lemma unitRescaledFiber_phi_det_one
    {ρ : ℝ} {G : Kakeya.Streamlined.TubeFamily ρ} {parent : Fin G.card}
    (normalization : WZ2PaperAssouadUnitRescalingData (G.tube parent))
    (normalization' : WZ2PaperAssouadUnitRescalingData ((imageTubeFamily e G).tube parent))
    (hvol : volume normalization'.parent_convex_body.outerJohnEllipsoid =
               volume normalization.parent_convex_body.outerJohnEllipsoid) :
    |LinearMap.det (((normalization.map.symm.linear).trans
        ((affineIsometryToEquiv e).linear.trans normalization'.map.linear)) : Point3 →ₗ[ℝ] Point3)| = 1 := by
  let hK := normalization.parent_convex_body
  let hK' := normalization'.parent_convex_body
  let A := hK.outerJohnEllipsoidMap
  let A' := hK'.outerJohnEllipsoidMap
  let e' := affineIsometryToEquiv e
  let φ_lin := (normalization.map.symm.linear).trans (e'.linear.trans normalization'.map.linear)
  have h_map1 : normalization.map.linear = (A.symm : Point3 ≃ₗ[ℝ] Point3) := by rfl
  have h_map2 : normalization'.map.linear = (A'.symm : Point3 ≃ₗ[ℝ] Point3) := by rfl
  have h_map_symm1 : normalization.map.symm.linear = (A : Point3 ≃ₗ[ℝ] Point3) := by
    have h : normalization.map.symm.linear = (normalization.map.linear).symm := by ext x; simp
    rw [h, h_map1] <;> rfl
  have h_e'_lin : e'.linear = (e.linearIsometryEquiv : Point3 ≃ₗ[ℝ] Point3) := by rfl
  have h_det1 : LinearMap.det (φ_lin : Point3 →ₗ[ℝ] Point3) =
      LinearMap.det ((e'.linear.trans normalization'.map.linear) : Point3 →ₗ[ℝ] Point3) *
      LinearMap.det (normalization.map.symm.linear : Point3 →ₗ[ℝ] Point3) :=
    LinearMap.det_comp _ _
  have h_det2 : LinearMap.det ((e'.linear.trans normalization'.map.linear) : Point3 →ₗ[ℝ] Point3) =
      LinearMap.det (normalization'.map.linear : Point3 →ₗ[ℝ] Point3) *
      LinearMap.det (e'.linear : Point3 →ₗ[ℝ] Point3) :=
    LinearMap.det_comp _ _
  have h_det : LinearMap.det (φ_lin : Point3 →ₗ[ℝ] Point3) =
      LinearMap.det (A'.symm : Point3 →ₗ[ℝ] Point3) *
      LinearMap.det ((e.linearIsometryEquiv : Point3 →ₗ[ℝ] Point3)) *
      LinearMap.det (A : Point3 →ₗ[ℝ] Point3) := by
    rw [h_det1, h_det2, h_map2, h_e'_lin, h_map_symm1] <;> ring
  rw [h_det]
  have h_detA'_symm : LinearMap.det ((A'.symm : Point3 ≃ₗ[ℝ] Point3) : Point3 →ₗ[ℝ] Point3) =
      (LinearMap.det (A' : Point3 →ₗ[ℝ] Point3))⁻¹ := by
    exact LinearEquiv.det_coe_symm A'
  rw [h_detA'_symm]
  have h_l_det : |LinearMap.det ((e.linearIsometryEquiv : Point3 →ₗ[ℝ] Point3))| = 1 :=
    linearIsometry_det_abs_one e
  have h_abs_eq : |LinearMap.det (A' : Point3 →ₗ[ℝ] Point3)| =
      |LinearMap.det (A : Point3 →ₗ[ℝ] Point3)| :=
    abs_det_eq_of_ellipsoid_volume_eq hvol
  have hA_ne_zero : LinearMap.det (A : Point3 →ₗ[ℝ] Point3) ≠ 0 := by
    have hunit : IsUnit (LinearMap.det (A : Point3 →ₗ[ℝ] Point3)) :=
      LinearEquiv.isUnit_det' A
    exact hunit.ne_zero
  have h_abs_ne_zero : |LinearMap.det (A : Point3 →ₗ[ℝ] Point3)| ≠ 0 := abs_ne_zero.mpr hA_ne_zero
  rw [abs_mul, abs_mul, abs_inv, h_l_det, h_abs_eq]
  <;> field_simp [h_abs_ne_zero] <;> ring

/-- Volume equality of outer John ellipsoids under an isometry. -/
lemma unitRescaledFiber_volume_eq
    {ρ : ℝ} {G : Kakeya.Streamlined.TubeFamily ρ} {parent : Fin G.card}
    (normalization : WZ2PaperAssouadUnitRescalingData (G.tube parent))
    (normalization' : WZ2PaperAssouadUnitRescalingData ((imageTubeFamily e G).tube parent)) :
    volume normalization'.parent_convex_body.outerJohnEllipsoid =
    volume normalization.parent_convex_body.outerJohnEllipsoid := by
  let hK := normalization.parent_convex_body
  let hK' := normalization'.parent_convex_body
  let G' := imageTubeFamily e G
  have hcarrier_eq : (G'.tube parent).carrier = e '' (G.tube parent).carrier :=
    imageTubeFamily_carrier e G parent
  have h_ellipsoid_eq : hK'.outerJohnEllipsoid = e '' hK.outerJohnEllipsoid :=
    affineIsometry_outerJohnEllipsoid_image e hK hK' hcarrier_eq
  rw [h_ellipsoid_eq, isometry_volume_image e]

end Kakeya.Assouad
end
