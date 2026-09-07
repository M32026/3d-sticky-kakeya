import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.ShapeSpace
import Mathlib.Tactic

/-!
# Connection between homothetic closeness and shape closeness

## Convention

The shape space parameter `B` corresponds to the ellipsoid
`ellipsoid c B.symm = c + B.symm '' ball`.  This is because
`ShapeClose β B₁ B₂` bounds `‖B₂ ∘ B₁⁻¹‖`, which controls the inclusion
`B₁⁻¹ '' ball ⊆ β • B₂⁻¹ '' ball`.

## Main results

- `shapeClose_imp_homothety`: `ShapeClose β B₁ B₂` implies
  `AreHomotheticallyClose β (ellipsoid c B₁.symm) (ellipsoid c B₂.symm)`.
- `homothetyAt_imp_shapeClose`: converse for centered ellipsoids at 0.
-/

noncomputable section

open Kakeya.CV

namespace Kakeya.CV

/-- If `B₁`, `B₂` are β-close in shape, then the ellipsoids with linear
parameters `B₁.symm`, `B₂.symm` and the same center are β-homothetically close.

The center of dilation is the common center `c`. -/
lemma shapeClose_imp_homothety_at {β : ℝ} (hβ : 0 < β)
    {B₁ B₂ : Point 3 ≃ₗ[ℝ] Point 3} (c : Point 3)
    (h : ShapeSpace.ShapeClose β B₁ B₂) :
    dilateAbout c β⁻¹ (JohnEllipsoid.ellipsoid c B₁.symm) ⊆
      JohnEllipsoid.ellipsoid c B₂.symm ∧
    JohnEllipsoid.ellipsoid c B₂.symm ⊆
      dilateAbout c β (JohnEllipsoid.ellipsoid c B₁.symm) := by
  let ball := Metric.closedBall (0 : Point 3) 1
  have h_inv_pos : 0 < β⁻¹ := by positivity
  have h_op1 : ∀ (y : Point 3), ‖y‖ ≤ 1 → ‖B₂ (B₁.symm y)‖ ≤ β := by
    intro y hy
    have h4 : ‖ShapeSpace.clm (B₁.symm.trans B₂) y‖ ≤
        ‖ShapeSpace.clm (B₁.symm.trans B₂)‖ * ‖y‖ :=
      ContinuousLinearMap.le_opNorm _ y
    have h5 : ShapeSpace.clm (B₁.symm.trans B₂) y = B₂ (B₁.symm y) := by
      simp [ShapeSpace.clm, ShapeSpace.clm_trans, LinearEquiv.trans_apply]
    rw [h5] at h4
    have h6 : ‖ShapeSpace.clm (B₁.symm.trans B₂)‖ ≤ β := h.1
    have h7 : ‖B₂ (B₁.symm y)‖ ≤ β * ‖y‖ := by exact h4.trans (by gcongr)
    have h8 : β * ‖y‖ ≤ β := by
      have h9 : ‖y‖ ≤ 1 := hy
      have h10 : 0 ≤ β := by positivity
      nlinarith
    linarith
  have h_op2 : ∀ (y : Point 3), ‖y‖ ≤ 1 → ‖B₁ (B₂.symm y)‖ ≤ β := by
    intro y hy
    have h4 : ‖ShapeSpace.clm (B₂.symm.trans B₁) y‖ ≤
        ‖ShapeSpace.clm (B₂.symm.trans B₁)‖ * ‖y‖ :=
      ContinuousLinearMap.le_opNorm _ y
    have h5 : ShapeSpace.clm (B₂.symm.trans B₁) y = B₁ (B₂.symm y) := by
      simp [ShapeSpace.clm, ShapeSpace.clm_trans, LinearEquiv.trans_apply]
    rw [h5] at h4
    have h6 : ‖ShapeSpace.clm (B₂.symm.trans B₁)‖ ≤ β := h.2
    have h7 : ‖B₁ (B₂.symm y)‖ ≤ β * ‖y‖ := by exact h4.trans (by gcongr)
    have h8 : β * ‖y‖ ≤ β := by
      have h9 : ‖y‖ ≤ 1 := hy
      have h10 : 0 ≤ β := by positivity
      nlinarith
    linarith
  have h_incl1 : dilateAbout c β⁻¹ (JohnEllipsoid.ellipsoid c B₁.symm) ⊆
      JohnEllipsoid.ellipsoid c B₂.symm := by
    intro z hz
    rcases hz with ⟨x, hx, hxz⟩
    rcases hx with ⟨v, hv, hxv⟩
    rcases hv with ⟨y, hy, hvy⟩
    have h_ynorm : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hy
    let w := B₂ (β⁻¹ • B₁.symm y)
    have h_w1 : w = β⁻¹ • B₂ (B₁.symm y) := by
      simp [w, B₂.map_smul]
    have h_wnorm : ‖w‖ ≤ 1 := by
      rw [h_w1]
      have h_abs : ‖(β⁻¹ : ℝ)‖ = β⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_pos h_inv_pos]
      have h : ‖β⁻¹ • B₂ (B₁.symm y)‖ = β⁻¹ * ‖B₂ (B₁.symm y)‖ := by
        rw [norm_smul, h_abs]
      rw [h]
      have h7 : ‖B₂ (B₁.symm y)‖ ≤ β := h_op1 y h_ynorm
      have h8 : β⁻¹ * ‖B₂ (B₁.symm y)‖ ≤ β⁻¹ * β :=
        mul_le_mul_of_nonneg_left h7 (by positivity)
      have h9 : β⁻¹ * β = 1 := by field_simp [hβ.ne'] <;> ring
      rw [h9] at h8
      exact h8
    have h_wball : w ∈ ball := by
      simpa [ball, Metric.mem_closedBall] using h_wnorm
    have h9 : B₂.symm w = β⁻¹ • B₁.symm y := by
      rw [h_w1]
      simp [B₂.symm_apply_apply]
      <;> rfl
    have h10 : β⁻¹ • B₁.symm y ∈ B₂.symm '' ball := ⟨w, h_wball, h9⟩
    have h_zform : z = c +ᵥ β⁻¹ • B₁.symm y := by
      rw [←hxz, ←hxv, ←hvy]
      simp [AffineMap.homothety_apply] <;> abel
    rw [h_zform]
    exact ⟨β⁻¹ • B₁.symm y, h10, rfl⟩
  have h_incl2 : JohnEllipsoid.ellipsoid c B₂.symm ⊆
      dilateAbout c β (JohnEllipsoid.ellipsoid c B₁.symm) := by
    intro z hz
    rcases hz with ⟨v, hv, hzv⟩
    rcases hv with ⟨y, hy, hvy⟩
    have h_ynorm : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hy
    let w := B₁ (β⁻¹ • B₂.symm y)
    have h_w1 : w = β⁻¹ • B₁ (B₂.symm y) := by
      simp [w, B₁.map_smul]
    have h_wnorm : ‖w‖ ≤ 1 := by
      rw [h_w1]
      have h_abs : ‖(β⁻¹ : ℝ)‖ = β⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_pos h_inv_pos]
      have h : ‖β⁻¹ • B₁ (B₂.symm y)‖ = β⁻¹ * ‖B₁ (B₂.symm y)‖ := by
        rw [norm_smul, h_abs]
      rw [h]
      have h7 : ‖B₁ (B₂.symm y)‖ ≤ β := h_op2 y h_ynorm
      have h8 : β⁻¹ * ‖B₁ (B₂.symm y)‖ ≤ β⁻¹ * β :=
        mul_le_mul_of_nonneg_left h7 (by positivity)
      have h9 : β⁻¹ * β = 1 := by field_simp [hβ.ne'] <;> ring
      rw [h9] at h8
      exact h8
    have h_wball : w ∈ ball := by
      simpa [ball, Metric.mem_closedBall] using h_wnorm
    let x : Point 3 := c +ᵥ B₁.symm w
    have h_xE1 : x ∈ JohnEllipsoid.ellipsoid c B₁.symm := by
      exact ⟨B₁.symm w, ⟨w, h_wball, rfl⟩, rfl⟩
    have h_hom : (AffineMap.homothety c β) x = c +ᵥ B₂.symm y := by
      have h1 : (AffineMap.homothety c β) x = c + β • (x - c) := by
        simp [AffineMap.homothety_apply] <;> abel
      rw [h1]
      have h2 : x - c = B₁.symm w := by simp [x] <;> abel
      rw [h2]
      have h3 : B₁.symm w = β⁻¹ • B₂.symm y := by
        rw [h_w1]
        simp [B₁.symm_apply_apply] <;> rfl
      rw [h3]
      have h4 : β • (β⁻¹ • B₂.symm y) = B₂.symm y := by
        rw [smul_smul]
        have h5 : β * β⁻¹ = 1 := by field_simp [hβ.ne']
        rw [h5, one_smul]
      rw [h4] <;> rfl
    have h_final : (AffineMap.homothety c β) x = z := by
      rw [h_hom, ←hzv, ←hvy]
      <;> rfl
    exact ⟨x, h_xE1, h_final⟩
  exact ⟨h_incl1, h_incl2⟩

/-- If `B₁`, `B₂` are β-close in shape, then the ellipsoids with linear
parameters `B₁.symm`, `B₂.symm` and the same center are β-homothetically close.
-/
lemma shapeClose_imp_homothety {β : ℝ} (hβ : 0 < β)
    {B₁ B₂ : Point 3 ≃ₗ[ℝ] Point 3} (c : Point 3)
    (h : ShapeSpace.ShapeClose β B₁ B₂) :
    AreHomotheticallyClose β
      (JohnEllipsoid.ellipsoid c B₁.symm)
      (JohnEllipsoid.ellipsoid c B₂.symm) := by
  have h_main := shapeClose_imp_homothety_at hβ c h
  exact ⟨c, h_main.1, h_main.2⟩

/-- Helper: norm of positive real scalar multiplication. -/
private lemma norm_pos_smul {c : ℝ} (hc : 0 < c) {v : Point 3} :
    ‖c • v‖ = c * ‖v‖ := by
  have h1 : ‖c • v‖ = ‖c‖ * ‖v‖ := norm_smul c v
  rw [h1]
  have h2 : ‖c‖ = c := by
    rw [Real.norm_eq_abs, abs_of_pos hc]
  rw [h2]

/-- If two centered ellipsoids are γ-homothetically close at 0, then their
inverse shapes are γ-close in the `ShapeClose` sense.

This is the converse of `shapeClose_imp_homothety_at` for the common center 0. -/
lemma homothetyAt_imp_shapeClose {γ : ℝ} (hγ : 0 < γ)
    {A₁ A₂ : Point 3 ≃ₗ[ℝ] Point 3}
    (h : AreHomotheticallyCloseAt 0 γ
          (JohnEllipsoid.ellipsoid 0 A₁)
          (JohnEllipsoid.ellipsoid 0 A₂)) :
    ShapeSpace.ShapeClose γ A₁.symm A₂.symm := by
  let ball := Metric.closedBall (0 : Point 3) 1
  have hγinv_pos : 0 < (γ⁻¹ : ℝ) := by positivity
  have h1_unit : ∀ (x : Point 3), ‖x‖ ≤ 1 → ‖A₂.symm (A₁ x)‖ ≤ γ := by
    intro x hx
    have h_xball : x ∈ ball := by simpa [ball, Metric.mem_closedBall] using hx
    have h_A1x : A₁ x ∈ A₁ '' ball := ⟨x, h_xball, rfl⟩
    have h_dilate : (γ⁻¹ : ℝ) • A₁ x ∈ dilateAbout 0 γ⁻¹ (JohnEllipsoid.ellipsoid 0 A₁) := by
      have h_in_E1 : A₁ x ∈ JohnEllipsoid.ellipsoid 0 A₁ := by
        refine ⟨A₁ x, ⟨x, h_xball, rfl⟩, ?_⟩
        simp
      exact ⟨A₁ x, h_in_E1, by simp [AffineMap.homothety_apply]⟩
    have h_in_E2 : (γ⁻¹ : ℝ) • A₁ x ∈ JohnEllipsoid.ellipsoid 0 A₂ := h.1 h_dilate
    rcases h_in_E2 with ⟨w, hw, hwz⟩
    rcases hw with ⟨y, hy, rfl⟩
    have h_ynorm : ‖y‖ ≤ 1 := by simpa [ball, Metric.mem_closedBall] using hy
    have h_eq : A₂ y = (γ⁻¹ : ℝ) • A₁ x := by simpa [vadd_eq_add] using hwz
    have h5 : y = A₂.symm ((γ⁻¹ : ℝ) • A₁ x) := by
      rw [←h_eq]; simp
    have h6 : A₂.symm ((γ⁻¹ : ℝ) • A₁ x) = (γ⁻¹ : ℝ) • A₂.symm (A₁ x) := by
      simp [A₂.symm.map_smul]
    rw [h5, h6] at h_ynorm
    have h7 : ‖(γ⁻¹ : ℝ) • A₂.symm (A₁ x)‖ = (γ⁻¹ : ℝ) * ‖A₂.symm (A₁ x)‖ :=
      norm_pos_smul hγinv_pos
    rw [h7] at h_ynorm
    have h8 : (γ⁻¹ : ℝ) * ‖A₂.symm (A₁ x)‖ ≤ 1 := h_ynorm
    have h9 : ‖A₂.symm (A₁ x)‖ ≤ γ := by
      calc ‖A₂.symm (A₁ x)‖
        = γ * ((γ⁻¹ : ℝ) * ‖A₂.symm (A₁ x)‖) := by field_simp [hγ.ne'] <;> ring
      _ ≤ γ * 1 := by gcongr
      _ = γ := by ring
    exact h9
  have h1 : ∀ (x : Point 3), ‖A₂.symm (A₁ x)‖ ≤ γ * ‖x‖ := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · let u : Point 3 := (‖x‖⁻¹ : ℝ) • x
      have hu_norm : ‖u‖ = 1 := by
        simp [u, norm_smul, hx] <;> field_simp [norm_pos_iff.mpr hx] <;> ring
      have h_bound := h1_unit u (by linarith)
      have h_eq : A₂.symm (A₁ u) = (‖x‖⁻¹ : ℝ) • A₂.symm (A₁ x) := by
        simp [u, A₁.map_smul, A₂.symm.map_smul]
      rw [h_eq] at h_bound
      have hpos2 : 0 < (‖x‖⁻¹ : ℝ) := by positivity
      have h_norm : ‖(‖x‖⁻¹ : ℝ) • A₂.symm (A₁ x)‖ = (‖x‖⁻¹ : ℝ) * ‖A₂.symm (A₁ x)‖ :=
        norm_pos_smul hpos2
      rw [h_norm] at h_bound
      have h_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      calc ‖A₂.symm (A₁ x)‖
        = ‖x‖ * ((‖x‖⁻¹ : ℝ) * ‖A₂.symm (A₁ x)‖) := by field_simp [h_pos.ne'] <;> ring
      _ ≤ ‖x‖ * γ := by gcongr
      _ = γ * ‖x‖ := by ring
  have h2_unit : ∀ (y : Point 3), ‖y‖ ≤ 1 → ‖A₁.symm (A₂ y)‖ ≤ γ := by
    intro y hy
    have h_yball : y ∈ ball := by simpa [ball, Metric.mem_closedBall] using hy
    have h_A2y : A₂ y ∈ JohnEllipsoid.ellipsoid 0 A₂ := by
      refine ⟨A₂ y, ⟨y, h_yball, rfl⟩, by simp⟩
    have h_dilate : A₂ y ∈ dilateAbout 0 γ (JohnEllipsoid.ellipsoid 0 A₁) := h.2 h_A2y
    rcases h_dilate with ⟨w, hw, hwz⟩
    rcases hw with ⟨v, hv, rfl⟩
    rcases hv with ⟨x, hx, rfl⟩
    have h_xnorm : ‖x‖ ≤ 1 := by simpa [ball, Metric.mem_closedBall] using hx
    have h_eq : (γ : ℝ) • A₁ x = A₂ y := by simpa [AffineMap.homothety_apply, vadd_eq_add] using hwz
    have h9 : A₁.symm (A₂ y) = (γ : ℝ) • x := by
      have h10 : A₁.symm (A₂ y) = A₁.symm ((γ : ℝ) • A₁ x) := by rw [h_eq]
      rw [h10]
      have h11 : A₁.symm ((γ : ℝ) • A₁ x) = (γ : ℝ) • A₁.symm (A₁ x) := by simp [A₁.symm.map_smul]
      rw [h11]
      have h12 : A₁.symm (A₁ x) = x := A₁.symm_apply_apply x
      rw [h12]
    rw [h9]
    have h13 : ‖(γ : ℝ) • x‖ = γ * ‖x‖ := norm_pos_smul hγ
    rw [h13]
    have h14 : γ * ‖x‖ ≤ γ := by
      have h15 : ‖x‖ ≤ 1 := h_xnorm
      have h16 : γ * ‖x‖ ≤ γ * (1 : ℝ) := mul_le_mul_of_nonneg_left h15 (by linarith)
      have h17 : γ * (1 : ℝ) = γ := by ring
      rw [h17] at h16
      exact h16
    exact h14
  have h2 : ∀ (y : Point 3), ‖A₁.symm (A₂ y)‖ ≤ γ * ‖y‖ := by
    intro y
    by_cases hy : y = 0
    · simp [hy] <;> positivity
    · let u : Point 3 := (‖y‖⁻¹ : ℝ) • y
      have hu_norm : ‖u‖ = 1 := by
        simp [u, norm_smul, hy] <;> field_simp [norm_pos_iff.mpr hy] <;> ring
      have h_bound := h2_unit u (by linarith)
      have h_eq : A₁.symm (A₂ u) = (‖y‖⁻¹ : ℝ) • A₁.symm (A₂ y) := by
        simp [u, A₂.map_smul, A₁.symm.map_smul]
      rw [h_eq] at h_bound
      have hpos2 : 0 < (‖y‖⁻¹ : ℝ) := by positivity
      have h_norm : ‖(‖y‖⁻¹ : ℝ) • A₁.symm (A₂ y)‖ = (‖y‖⁻¹ : ℝ) * ‖A₁.symm (A₂ y)‖ :=
        norm_pos_smul hpos2
      rw [h_norm] at h_bound
      have h_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
      calc ‖A₁.symm (A₂ y)‖
        = ‖y‖ * ((‖y‖⁻¹ : ℝ) * ‖A₁.symm (A₂ y)‖) := by field_simp [h_pos.ne'] <;> ring
      _ ≤ ‖y‖ * γ := by gcongr
      _ = γ * ‖y‖ := by ring
  have h_op1 : ‖ShapeSpace.clm (A₁.trans A₂.symm)‖ ≤ γ := by
    have h_eq2 : ShapeSpace.clm (A₁.trans A₂.symm) =
        (ShapeSpace.clm A₂.symm).comp (ShapeSpace.clm A₁) :=
      ShapeSpace.clm_trans A₁ A₂.symm
    rw [h_eq2]
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) h1
  have h_op2 : ‖ShapeSpace.clm (A₂.trans A₁.symm)‖ ≤ γ := by
    have h_eq2 : ShapeSpace.clm (A₂.trans A₁.symm) =
        (ShapeSpace.clm A₁.symm).comp (ShapeSpace.clm A₂) :=
      ShapeSpace.clm_trans A₂ A₁.symm
    rw [h_eq2]
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) h2
  have h_final1 : ‖ShapeSpace.clm ((A₁.symm).symm.trans A₂.symm)‖ ≤ γ := by
    have h_eq : (A₁.symm).symm.trans A₂.symm = A₁.trans A₂.symm := by rfl
    rw [h_eq]; exact h_op1
  have h_final2 : ‖ShapeSpace.clm ((A₂.symm).symm.trans A₁.symm)‖ ≤ γ := by
    have h_eq : (A₂.symm).symm.trans A₁.symm = A₂.trans A₁.symm := by rfl
    rw [h_eq]; exact h_op2
  exact ⟨h_final1, h_final2⟩

end Kakeya.CV
