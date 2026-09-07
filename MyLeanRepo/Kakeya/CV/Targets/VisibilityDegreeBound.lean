import MyLeanRepo.Kakeya.CV.VisibilityDegreeBound.Helpers
import MyLeanRepo.Kakeya.CV.VisibilityDegreeBound.ConvexBody

/-!
# Visibility controlled by polynomial degree

Carbery--Valdimarsson Lemma 3 in dimension three.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace Kakeya.CV

theorem visibility_degree_bound
    (hCylinder : PolynomialCylinderEstimateStatement)
    (hVisibility : VisibilityDirectionalBoundStatement) :
    VisibilityDegreeBoundStatement := by
  rcases hCylinder with ⟨C_cyl, hC_cyl_pos, hCylinder⟩
  rcases hVisibility with ⟨C_vis, hC_vis_pos, hVisibility⟩
  let M : ℝ := max 1 (C_cyl : ℝ)
  have hM_pos : 0 < M := by positivity
  have hM1 : 1 ≤ M := le_max_left _ _
  let C : ℝ := C_vis ^ (3 / 2 : ℝ) * M
  have hC_pos : 0 < C := by positivity
  use C, hC_pos
  intro k p Q c e hk hp hSing hdeg he hQ h_area
  let S : Set (Point 3) := polynomialZeroSet p ∩ Q
  let K : Set (Point 3) := visibilityBody p S
  let hCylinder' : ∀ (a u : Point 3), ‖u‖ = 1 →
      directionalSurfaceArea u p (polynomialZeroSet p ∩ unitTube a u) ≤
        (C_cyl : ℝ≥0∞) * (k : ℝ≥0∞) :=
    fun a u hu => hCylinder k p a u hp hSing hdeg hu
  have h_body : JohnEllipsoid.IsConvexBody K :=
    visibilityBody_convexBody p hp hSing k hk C_cyl hC_cyl_pos hCylinder' Q c hQ e he h_area
  have h_symm : ∀ x, x ∈ K → -x ∈ K := by
    intro x hx
    have hneg_ball : -x ∈ unitBall 3 := by
      simpa [unitBall, Metric.mem_closedBall] using hx.1
    have hneg_area : directionalSurfaceArea (-x) p S ≤ 1 := by
      rw [directionalSurfaceArea_evenness x p S]
      exact hx.2
    exact ⟨hneg_ball, hneg_area⟩
  rcases exists_orthonormal_basis_with_first e he with ⟨v, hv_orth, hv0⟩
  let s : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => 1
    | 1 => M * (k : ℝ)
    | 2 => M * (k : ℝ)
  have hs_pos : ∀ i, 0 < s i := by
    intro i
    fin_cases i <;> simp [s, hM_pos, hk] <;> positivity
  have hMk_ge1 : 1 ≤ M * (k : ℝ) := by
    have h1 : 1 ≤ M := hM1
    have h2 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have hC_le_M : (C_cyl : ℝ≥0∞) ≤ ENNReal.ofReal M := by
    have h221 : (C_cyl : ℝ≥0∞) = ENNReal.ofReal (C_cyl : ℝ) := by simp
    rw [h221]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hk_pos' : 0 < (k : ℝ) := by exact_mod_cast hk
  -- Helper lemma: Real.rpow (x^2) (1/3) = x^(2/3) for x ≥ 0
  have h_rpow2_3 : ∀ (x : ℝ), 0 ≤ x →
      Real.rpow (x ^ 2) (1 / 3 : ℝ) = Real.rpow x (2 / 3 : ℝ) := by
    intro x hx
    have h1 : Real.rpow x ((2 : ℝ) * (1 / 3 : ℝ)) =
        Real.rpow (Real.rpow x (2 : ℝ)) (1 / 3 : ℝ) :=
      Real.rpow_mul (hx := hx) (y := (2 : ℝ)) (z := (1 / 3 : ℝ))
    have h2 : Real.rpow x (2 : ℝ) = x ^ 2 := by simp
    have h3 : (2 : ℝ) * (1 / 3 : ℝ) = (2 / 3 : ℝ) := by norm_num
    rw [h3] at h1
    rw [h2] at h1
    exact h1.symm
  -- Helper lemma: (x^(2/3))^(3/2) = x for x ≥ 0
  have h_rpow32 : ∀ (x : ℝ), 0 ≤ x →
      Real.rpow (Real.rpow x (2 / 3 : ℝ)) (3 / 2 : ℝ) = x := by
    intro x hx
    have h1 : Real.rpow x ((2 / 3 : ℝ) * (3 / 2 : ℝ)) =
        Real.rpow (Real.rpow x (2 / 3 : ℝ)) (3 / 2 : ℝ) :=
      Real.rpow_mul (hx := hx) (y := (2 / 3 : ℝ)) (z := (3 / 2 : ℝ))
    have h2 : (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 := by norm_num
    rw [h2] at h1
    have h3 : Real.rpow x 1 = x := by simp
    rw [h3] at h1
    exact h1.symm
  -- Helper: for any unit direction u, the scaled point is in K
  have h_scaled_mem : ∀ (u : Point 3), ‖u‖ = 1 →
      (M * (k : ℝ))⁻¹ • u ∈ K := by
    intro u hu_norm
    have hQ_tube : Q ⊆ unitTube c u := by
      calc Q
        ⊆ Metric.closedBall c 1 := hQ
      _ ⊆ unitTube c u := unitBall_subset_unitTube c u hu_norm
    have hS_subset : S ⊆ polynomialZeroSet p ∩ unitTube c u :=
      Set.inter_subset_inter_right _ hQ_tube
    have h_cyl : directionalSurfaceArea u p (polynomialZeroSet p ∩ unitTube c u) ≤
        (C_cyl : ℝ≥0∞) * (k : ℝ≥0∞) := hCylinder' c u hu_norm
    have h_area_u : directionalSurfaceArea u p S ≤
        (C_cyl : ℝ≥0∞) * (k : ℝ≥0∞) :=
      (directionalSurfaceArea_mono u p hS_subset).trans h_cyl
    let scale : ℝ := (M * (k : ℝ))⁻¹
    have hscale_nonneg : 0 ≤ scale := by positivity
    have h_inner_le : (C_cyl : ℝ≥0∞) * (k : ℝ≥0∞) ≤
        ENNReal.ofReal M * (k : ℝ≥0∞) := mul_le_mul_right' hC_le_M _
    have h_scaled_area : directionalSurfaceArea (scale • u) p S ≤ 1 := by
      have h_hom : directionalSurfaceArea (scale • u) p S =
          ENNReal.ofReal scale * directionalSurfaceArea u p S :=
        directionalSurfaceArea_homogeneity scale hscale_nonneg u p S
      rw [h_hom]
      have h1 : ENNReal.ofReal scale * directionalSurfaceArea u p S ≤
          ENNReal.ofReal scale * ((C_cyl : ℝ≥0∞) * (k : ℝ≥0∞)) :=
        mul_le_mul_left' h_area_u _
      have h2 : ENNReal.ofReal scale * ((C_cyl : ℝ≥0∞) * (k : ℝ≥0∞)) ≤
          ENNReal.ofReal scale * (ENNReal.ofReal M * (k : ℝ≥0∞)) :=
        mul_le_mul_left' h_inner_le _
      have h_k_coe : (k : ℝ≥0∞) = ENNReal.ofReal (k : ℝ) := by simp
      have h3 : ENNReal.ofReal scale * (ENNReal.ofReal M * (k : ℝ≥0∞)) = 1 := by
        rw [h_k_coe]
        have h4 : ENNReal.ofReal scale * (ENNReal.ofReal M * ENNReal.ofReal (k : ℝ)) =
            ENNReal.ofReal (scale * (M * (k : ℝ))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          <;> rfl
        rw [h4]
        have h5 : scale * (M * (k : ℝ)) = 1 := by
          simp [scale] <;> field_simp [hM_pos.ne', hk_pos'.ne'] <;> ring
        rw [h5] <;> simp
      exact h1.trans (h2.trans h3.le)
    have h_scale_le1 : scale ≤ 1 := by
      have h_eq : scale * (M * (k : ℝ)) = 1 := by
        simp [scale] <;> field_simp [hM_pos.ne', hk_pos'.ne'] <;> ring
      calc scale
        = scale * 1 := by ring
      _ ≤ scale * (M * (k : ℝ)) := by gcongr <;> linarith
      _ = 1 := h_eq
    have h_norm_scaled : ‖scale • u‖ ≤ 1 := by
      have h_abs : ‖scale‖ = scale := by
        simpa [Real.norm_eq_abs] using abs_of_nonneg hscale_nonneg
      have h_n : ‖scale • u‖ = scale * ‖u‖ := by
        calc ‖scale • u‖
          = ‖scale‖ * ‖u‖ := norm_smul scale u
        _ = scale * ‖u‖ := by rw [h_abs]
      rw [h_n, hu_norm]
      <;> simpa using h_scale_le1
    have h_ball : scale • u ∈ unitBall 3 := by
      simpa [unitBall, Metric.mem_closedBall] using h_norm_scaled
    exact ⟨h_ball, h_scaled_area⟩
  have hmem : ∀ i, (s i)⁻¹ • v i ∈ K := by
    intro i
    by_cases h : i = 0
    · rw [h]
      have h_s0 : s 0 = 1 := by simp [s]
      rw [h_s0]
      have h1 : (1 : ℝ)⁻¹ • v 0 = e := by
        rw [hv0] <;> simp
      rw [h1]
      have h_ball : e ∈ unitBall 3 := by
        simpa [unitBall, Metric.mem_closedBall] using he.le
      exact ⟨h_ball, h_area⟩
    · have h_si : s i = M * (k : ℝ) := by
        have h_i12 : i = 1 ∨ i = 2 := by fin_cases i <;> tauto
        rcases h_i12 with (rfl | rfl) <;> simp [s]
      rw [h_si]
      exact h_scaled_mem (v i) (hv_orth.norm_eq_one i)
  have h_tv : tripleVolume v = 1 := tripleVolume_orthonormal v hv_orth
  have h_main_raw := hVisibility K h_body h_symm v s (fun i => hv_orth.norm_eq_one i) hs_pos hmem
  have h_rpow1 : Real.rpow (tripleVolume v) (1 / 3 : ℝ) = 1 := by
    rw [h_tv] <;> norm_num
  have h_sprod : ∏ i, s i = M ^ 2 * (k : ℝ) ^ 2 := by
    simp [s, Fin.prod_univ_succ] <;> ring
  have h_main : visibility p S ≤ C_vis * Real.rpow (M ^ 2 * (k : ℝ) ^ 2) (1 / 3 : ℝ) := by
    rw [h_sprod] at h_main_raw
    rw [h_rpow1] at h_main_raw
    simpa [visibility] using h_main_raw
  have h_pos1 : 0 ≤ M ^ 2 := by positivity
  have h_pos2 : 0 ≤ (k : ℝ) ^ 2 := by positivity
  have h2 : Real.rpow (M ^ 2 * (k : ℝ) ^ 2) (1 / 3 : ℝ) =
      Real.rpow M (2 / 3 : ℝ) * Real.rpow (k : ℝ) (2 / 3 : ℝ) := by
    have h_mul : Real.rpow (M ^ 2 * (k : ℝ) ^ 2) (1 / 3 : ℝ) =
        Real.rpow (M ^ 2) (1 / 3 : ℝ) * Real.rpow ((k : ℝ) ^ 2) (1 / 3 : ℝ) :=
      Real.mul_rpow h_pos1 h_pos2
    rw [h_mul]
    have h3 := h_rpow2_3 M (by positivity)
    have h4 := h_rpow2_3 (k : ℝ) (by positivity)
    rw [h3, h4]
  rw [h2] at h_main
  have h_posM : 0 ≤ M := by positivity
  have h_posk : 0 ≤ (k : ℝ) := by positivity
  have h_vis_nonneg : 0 ≤ visibility p S := by
    simp [visibility] <;> positivity
  have h_rpowM23 : 0 ≤ Real.rpow M (2 / 3 : ℝ) := Real.rpow_nonneg h_posM _
  have h_rpowk23 : 0 ≤ Real.rpow (k : ℝ) (2 / 3 : ℝ) := Real.rpow_nonneg h_posk _
  have h4 : 0 ≤ C_vis * (Real.rpow M (2 / 3 : ℝ) * Real.rpow (k : ℝ) (2 / 3 : ℝ)) := by
    positivity
  have h5 : Real.rpow (visibility p S) (3 / 2 : ℝ) ≤
      Real.rpow (C_vis * (Real.rpow M (2 / 3 : ℝ) * Real.rpow (k : ℝ) (2 / 3 : ℝ))) (3 / 2 : ℝ) :=
    Real.rpow_le_rpow h_vis_nonneg h_main (by norm_num)
  have h_posC : 0 ≤ C_vis := by positivity
  have h_prod_nonneg : 0 ≤ Real.rpow M (2 / 3 : ℝ) * Real.rpow (k : ℝ) (2 / 3 : ℝ) :=
    mul_nonneg h_rpowM23 h_rpowk23
  have h6 : Real.rpow (C_vis * (Real.rpow M (2 / 3 : ℝ) * Real.rpow (k : ℝ) (2 / 3 : ℝ))) (3 / 2 : ℝ) =
      C_vis ^ (3 / 2 : ℝ) * M * (k : ℝ) := by
    have h_mul1 : Real.rpow (C_vis * (Real.rpow M (2 / 3 : ℝ) * Real.rpow (k : ℝ) (2 / 3 : ℝ))) (3 / 2 : ℝ) =
        Real.rpow C_vis (3 / 2 : ℝ) *
        Real.rpow (Real.rpow M (2 / 3 : ℝ) * Real.rpow (k : ℝ) (2 / 3 : ℝ)) (3 / 2 : ℝ) :=
      Real.mul_rpow h_posC h_prod_nonneg
    rw [h_mul1]
    have h_mul2 : Real.rpow (Real.rpow M (2 / 3 : ℝ) * Real.rpow (k : ℝ) (2 / 3 : ℝ)) (3 / 2 : ℝ) =
        Real.rpow (Real.rpow M (2 / 3 : ℝ)) (3 / 2 : ℝ) *
        Real.rpow (Real.rpow (k : ℝ) (2 / 3 : ℝ)) (3 / 2 : ℝ) :=
      Real.mul_rpow h_rpowM23 h_rpowk23
    rw [h_mul2]
    have h7 := h_rpow32 M h_posM
    have h8 := h_rpow32 (k : ℝ) h_posk
    have h_goal : Real.rpow C_vis (3 / 2 : ℝ) *
        (Real.rpow (Real.rpow M (2 / 3 : ℝ)) (3 / 2 : ℝ) *
         Real.rpow (Real.rpow (k : ℝ) (2 / 3 : ℝ)) (3 / 2 : ℝ)) =
      C_vis ^ (3 / 2 : ℝ) * M * (k : ℝ) := by
      have h9 : Real.rpow C_vis (3 / 2 : ℝ) = C_vis ^ (3 / 2 : ℝ) := by rfl
      rw [h7, h8, h9]
      <;> ring_nf <;> ring
    exact h_goal
  rw [h6] at h5
  simpa [C] using h5

end Kakeya.CV
