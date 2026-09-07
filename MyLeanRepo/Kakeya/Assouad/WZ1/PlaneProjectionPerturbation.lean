import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# WZ1 plane-projection perturbation

Closed proof of WZ1 Lemma 13: a unit plane normal that is almost orthogonal
to two transverse directions is close to the normalized cross-product normal.
-/

namespace Kakeya.Assouad

open Matrix

/-- Helper: inner product on EuclideanSpace equals dot product. -/
lemma plane_proj_inner_dot (x y : Point3) :
    inner ℝ x y = (x : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ) := by
  have h3 := EuclideanSpace.inner_eq_star_dotProduct x y
  have h4 : inner ℝ x y = (y : Fin 3 → ℝ) ⬝ᵥ star (x : Fin 3 → ℝ) := by simpa using h3
  rw [h4]
  have hstar : star (x : Fin 3 → ℝ) = (x : Fin 3 → ℝ) := by ext i; simp
  rw [hstar]
  exact dotProduct_comm _ _

/-- Helper: norm squared on EuclideanSpace equals self dot product. -/
lemma plane_proj_norm_sq (x : Point3) :
    ‖x‖ ^ 2 = (x : Fin 3 → ℝ) ⬝ᵥ (x : Fin 3 → ℝ) := by
  have h1 : inner ℝ x x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  have h2 := plane_proj_inner_dot x x
  linarith

/-- Helper: norm of WithLp.toLp 2 x squared equals x ⬝ᵥ x. -/
lemma plane_proj_toLp_norm_sq (x : Fin 3 → ℝ) :
    ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
  calc
    ‖WithLp.toLp 2 x‖ ^ 2
      = inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 x) := by
        rw [← real_inner_self_eq_norm_sq]
  _ = (WithLp.toLp 2 x : Fin 3 → ℝ) ⬝ᵥ star (WithLp.toLp 2 x : Fin 3 → ℝ) :=
        EuclideanSpace.inner_eq_star_dotProduct _ _
  _ = (WithLp.toLp 2 x : Fin 3 → ℝ) ⬝ᵥ (WithLp.toLp 2 x : Fin 3 → ℝ) := by
        have hstar : star (WithLp.toLp 2 x : Fin 3 → ℝ) = (WithLp.toLp 2 x : Fin 3 → ℝ) := by
          ext i; simp
        rw [hstar]
  _ = x ⬝ᵥ x := by rfl

/-- Helper: final distance bound from 1 - |γ| ≤ 4ρ²/κ². -/
lemma plane_proj_final_bound (rho kappa : ℝ) (normal n_hat : Point3)
    (hnormal : ‖normal‖ = 1) (h_n_hat_norm : ‖n_hat‖ = 1)
    (gamma : ℝ) (hgamma : gamma = inner ℝ normal n_hat)
    (h_1_minus : 1 - |gamma| ≤ 4 * rho ^ 2 / kappa ^ 2)
    (hkappa : 0 < kappa) (hrho : 0 ≤ rho) :
    ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
      ‖normal - sign • n_hat‖ ≤ 10 * rho / kappa := by
  let sign : ℝ := if 0 ≤ gamma then 1 else -1
  have hsign : sign = 1 ∨ sign = -1 := by
    unfold sign
    by_cases h : 0 ≤ gamma <;> simp [h] <;> tauto
  have h_sign_gamma : sign * gamma = |gamma| := by
    unfold sign
    by_cases h : 0 ≤ gamma
    · simp [h, abs_of_nonneg] <;> ring
    · have hneg : gamma < 0 := by linarith
      simp [h, abs_of_neg hneg] <;> ring
  have h_sign_sq : sign ^ 2 = 1 := by
    rcases hsign with (h | h)
    · rw [h] <;> norm_num
    · rw [h] <;> norm_num
  have h_abs_sign : |sign| = 1 := by
    rcases hsign with (h | h)
    · rw [h] <;> norm_num
    · rw [h] <;> norm_num
  have h_smul_norm : ‖sign • n_hat‖ = 1 := by
    calc
      ‖sign • n_hat‖ = |sign| * ‖n_hat‖ := by
        exact norm_smul sign n_hat
      _ = |sign| * 1 := by rw [h_n_hat_norm] <;> ring
      _ = 1 := by rw [h_abs_sign] <;> ring
  have h_dist_sq : ‖normal - sign • n_hat‖ ^ 2 = 2 * (1 - |gamma|) := by
    have h1 : ‖normal - sign • n_hat‖ ^ 2 =
        inner ℝ (normal - sign • n_hat) (normal - sign • n_hat) := by
      rw [← real_inner_self_eq_norm_sq] <;> rfl
    rw [h1]
    have h_inner1 : inner ℝ (normal - sign • n_hat) (normal - sign • n_hat) =
        inner ℝ normal (normal - sign • n_hat) - inner ℝ (sign • n_hat) (normal - sign • n_hat) := by
      rw [inner_sub_left]
    rw [h_inner1]
    have h_inner2 : inner ℝ normal (normal - sign • n_hat) =
        inner ℝ normal normal - sign * inner ℝ normal n_hat := by
      rw [inner_sub_right, inner_smul_right] <;> ring
    have h_inner3 : inner ℝ (sign • n_hat) (normal - sign • n_hat) =
        sign * inner ℝ n_hat normal - sign ^ 2 * inner ℝ n_hat n_hat := by
      have h31 : inner ℝ (sign • n_hat) (normal - sign • n_hat) =
          inner ℝ (sign • n_hat) normal - inner ℝ (sign • n_hat) (sign • n_hat) := by
        rw [inner_sub_right]
      rw [h31]
      have h32 : inner ℝ (sign • n_hat) normal = sign * inner ℝ n_hat normal := by
        exact real_inner_smul_left n_hat normal sign
      have h33 : inner ℝ (sign • n_hat) (sign • n_hat) = sign ^ 2 * inner ℝ n_hat n_hat := by
        have h : inner ℝ (sign • n_hat) (sign • n_hat) = ‖sign • n_hat‖ ^ 2 := by
          rw [← real_inner_self_eq_norm_sq] <;> rfl
        rw [h]
        have h21 : ‖sign • n_hat‖ = ‖sign‖ * ‖n_hat‖ := norm_smul sign n_hat
        have h22 : ‖sign‖ = |sign| := Real.norm_eq_abs sign
        have h2 : ‖sign • n_hat‖ ^ 2 = |sign| ^ 2 * ‖n_hat‖ ^ 2 := by
          rw [h21, h22] <;> ring
        rw [h2]
        have h3 : |sign| ^ 2 = sign ^ 2 := by simp [sq_abs]
        have h4 : ‖n_hat‖ ^ 2 = inner ℝ n_hat n_hat := by
          rw [← real_inner_self_eq_norm_sq] <;> rfl
        rw [h3, h4] <;> ring
      rw [h32, h33] <;> ring
    rw [h_inner2, h_inner3]
    have h4 : inner ℝ normal normal = ‖normal‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq] <;> rfl
    have h5 : inner ℝ n_hat n_hat = ‖n_hat‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq] <;> rfl
    have h6 : inner ℝ n_hat normal = inner ℝ normal n_hat := by
      exact (real_inner_comm n_hat normal).symm
    rw [h4, h5, h6, hnormal, h_n_hat_norm, h_sign_sq]
    have h7 : inner ℝ normal n_hat = gamma := hgamma.symm
    rw [h7, h_sign_gamma] <;> ring
  have h_final_sq : ‖normal - sign • n_hat‖ ^ 2 ≤ 8 * rho ^ 2 / kappa ^ 2 := by
    rw [h_dist_sq]
    have h18 : 2 * (1 - |gamma|) ≤ 2 * (4 * rho ^ 2 / kappa ^ 2) := by
      gcongr <;> exact h_1_minus
    have h19 : 2 * (4 * rho ^ 2 / kappa ^ 2) = 8 * rho ^ 2 / kappa ^ 2 := by ring
    rw [h19] at h18
    exact h18
  have h_pos : 0 ≤ ‖normal - sign • n_hat‖ := norm_nonneg _
  have h_pos2 : 0 ≤ 10 * rho / kappa := by
    exact div_nonneg (by positivity) (by positivity)
  have h20 : ‖normal - sign • n_hat‖ ^ 2 ≤ (10 * rho / kappa) ^ 2 := by
    have h21 : 8 * rho ^ 2 / kappa ^ 2 ≤ (10 * rho / kappa) ^ 2 := by
      have h22 : 0 < kappa := hkappa
      field_simp [h22.ne'] <;> ring_nf <;> nlinarith
    linarith [h_final_sq, h21]
  have h_final : ‖normal - sign • n_hat‖ ≤ 10 * rho / kappa := by
    nlinarith
  exact ⟨sign, hsign, h_final⟩

/-- Helper: from `N² - d² ≤ 4ρ²` and `κ ≤ N`, deduce `1 - |d/N| ≤ 4ρ²/κ²`. -/
lemma factor_bound {N d rho kappa : ℝ}
    (hN_pos : 0 < N)
    (h_nonneg : 0 ≤ N ^ 2 - d ^ 2)
    (h_main_bound : N ^ 2 - d ^ 2 ≤ 4 * rho ^ 2)
    (hkappa : 0 < kappa)
    (hkappa' : kappa ≤ N) :
    1 - |d / N| ≤ 4 * rho ^ 2 / kappa ^ 2 := by
  have h1 : |d / N| ≤ 1 := by
    have h2 : (d / N) ^ 2 ≤ 1 := by
      have h3 : (d / N) ^ 2 = d ^ 2 / N ^ 2 := by field_simp [hN_pos.ne'] <;> ring
      rw [h3]
      have h4 : d ^ 2 ≤ N ^ 2 := by linarith
      have h5 : 0 < N ^ 2 := by positivity
      have h6 : d ^ 2 / N ^ 2 ≤ 1 := by
        rw [div_le_one h5] <;> linarith
      exact h6
    have h7 : 0 ≤ |d / N| := by positivity
    have h8 : |d / N| ^ 2 = (d / N) ^ 2 := by simp [sq_abs]
    nlinarith [sq_nonneg (d / N)]
  have h7 : 1 - |d / N| ≤ 1 - (d / N) ^ 2 := by
    have h8 : 1 - (d / N) ^ 2 = (1 - |d / N|) * (1 + |d / N|) := by
      have h9 : (d / N) ^ 2 = |d / N| ^ 2 := by simp [sq_abs]
      rw [h9] <;> ring
    rw [h8]
    have h10 : 1 + |d / N| ≥ 1 := by linarith [abs_nonneg (d / N)]
    nlinarith [abs_nonneg (d / N)]
  have h11 : 1 - (d / N) ^ 2 = (N ^ 2 - d ^ 2) / N ^ 2 := by
    field_simp [hN_pos.ne'] <;> ring
  rw [h11] at h7
  have h12 : (N ^ 2 - d ^ 2) / N ^ 2 ≤ 4 * rho ^ 2 / kappa ^ 2 := by
    have h13 : (N ^ 2 - d ^ 2) / N ^ 2 ≤ 4 * rho ^ 2 / N ^ 2 := by
      gcongr
      <;> linarith
    have h14 : N ^ 2 ≥ kappa ^ 2 := by nlinarith
    have h15 : 4 * rho ^ 2 / N ^ 2 ≤ 4 * rho ^ 2 / kappa ^ 2 := by
      gcongr
      <;> nlinarith
    linarith
  linarith

theorem wz1_plane_projection_perturbation :
    WZ1PlaneProjectionPerturbationStatement := by
  intro u v normal hu hv hnormal kappa rho hkappa hrho hkappa' h1 h2
  let n : Point3 := wz1Cross u v
  have hN_pos : 0 < ‖n‖ := by
    have h : kappa ≤ ‖n‖ := hkappa'
    exact lt_of_lt_of_le hkappa h
  let n_hat : Point3 := (‖n‖)⁻¹ • n
  have h_n_hat_norm : ‖n_hat‖ = 1 := by
    rw [show n_hat = (‖n‖)⁻¹ • n from rfl, norm_smul, Real.norm_eq_abs]
    have h1 : |(‖n‖)⁻¹| = (‖n‖)⁻¹ := by
      apply abs_of_pos
      exact inv_pos.mpr hN_pos
    rw [h1]
    field_simp [hN_pos.ne'] <;> ring
  let u' : Fin 3 → ℝ := (u : Fin 3 → ℝ)
  let v' : Fin 3 → ℝ := (v : Fin 3 → ℝ)
  let normal' : Fin 3 → ℝ := (normal : Fin 3 → ℝ)
  let c' : Fin 3 → ℝ := u' ⨯₃ v'
  have hcross_def : (n : Fin 3 → ℝ) = c' := by rfl
  have hN2 : ‖n‖ ^ 2 = c' ⬝ᵥ c' := by
    have h := plane_proj_norm_sq n
    rw [hcross_def] at h
    exact h
  have hnormal2 : normal' ⬝ᵥ normal' = 1 := by
    have h3 := plane_proj_norm_sq normal
    simpa using h3.symm.trans (by rw [hnormal] <;> ring)
  have h_dot_v : normal' ⬝ᵥ v' = inner ℝ normal v := by
    have h : inner ℝ normal v = normal' ⬝ᵥ v' := plane_proj_inner_dot normal v
    exact h.symm
  have h_dot_u : u' ⬝ᵥ normal' = inner ℝ normal u := by
    have h : inner ℝ normal u = normal' ⬝ᵥ u' := plane_proj_inner_dot normal u
    have hcomm : normal' ⬝ᵥ u' = u' ⬝ᵥ normal' := dotProduct_comm _ _
    rw [hcomm] at h
    exact h.symm
  have h_abs_dot_v : |normal' ⬝ᵥ v'| ≤ rho := by
    rw [h_dot_v] <;> exact h2
  have h_abs_dot_u : |u' ⬝ᵥ normal'| ≤ rho := by
    rw [h_dot_u] <;> exact h1
  have h_triple : normal' ⨯₃ c' = (normal' ⬝ᵥ v') • u' - (u' ⬝ᵥ normal') • v' :=
    cross_cross_eq_smul_sub_smul' normal' u' v'
  have h_eq_cross : WithLp.toLp 2 (normal' ⨯₃ c') =
      (normal' ⬝ᵥ v') • u - (u' ⬝ᵥ normal') • v := by
    rw [h_triple] <;> rfl
  have h_norm_cross_bound : ‖WithLp.toLp 2 (normal' ⨯₃ c')‖ ≤ 2 * rho := by
    rw [h_eq_cross]
    calc
      ‖(normal' ⬝ᵥ v') • u - (u' ⬝ᵥ normal') • v‖
        ≤ ‖(normal' ⬝ᵥ v') • u‖ + ‖(u' ⬝ᵥ normal') • v‖ := norm_sub_le _ _
      _ = |normal' ⬝ᵥ v'| * ‖u‖ + |u' ⬝ᵥ normal'| * ‖v‖ := by
        rw [norm_smul, norm_smul] <;> rfl
      _ = |normal' ⬝ᵥ v'| + |u' ⬝ᵥ normal'| := by rw [hu, hv] <;> ring
      _ ≤ 2 * rho := by linarith
  have h1_dot : (normal' ⨯₃ c') ⬝ᵥ (normal' ⨯₃ c') =
      (normal' ⬝ᵥ normal') * (c' ⬝ᵥ c') - (normal' ⬝ᵥ c') ^ 2 := by
    have h := cross_dot_cross normal' c' normal' c'
    have h2 : c' ⬝ᵥ normal' = normal' ⬝ᵥ c' := dotProduct_comm c' normal'
    rw [h, h2] <;> ring
  have h_lagrange : ‖WithLp.toLp 2 (normal' ⨯₃ c')‖ ^ 2 =
      ‖n‖ ^ 2 - (normal' ⬝ᵥ c') ^ 2 := by
    have h4 := plane_proj_toLp_norm_sq (normal' ⨯₃ c')
    rw [h4, h1_dot, hnormal2, hN2] <;> ring
  let d : ℝ := normal' ⬝ᵥ c'
  have h_nonneg : 0 ≤ ‖n‖ ^ 2 - d ^ 2 := by
    rw [←h_lagrange]
    exact sq_nonneg _
  have h_main_bound : ‖n‖ ^ 2 - d ^ 2 ≤ 4 * rho ^ 2 := by
    have h5 : ‖WithLp.toLp 2 (normal' ⨯₃ c')‖ ≤ 2 * rho := h_norm_cross_bound
    have h6 : 0 ≤ ‖WithLp.toLp 2 (normal' ⨯₃ c')‖ := norm_nonneg _
    have h7 : ‖WithLp.toLp 2 (normal' ⨯₃ c')‖ ^ 2 ≤ (2 * rho) ^ 2 := by
      have h8 : 0 ≤ ‖WithLp.toLp 2 (normal' ⨯₃ c')‖ := norm_nonneg _
      have h9 : 0 ≤ 2 * rho := by positivity
      nlinarith [h_norm_cross_bound]
    have h9 : (2 * rho) ^ 2 = 4 * rho ^ 2 := by ring
    have h10 : ‖WithLp.toLp 2 (normal' ⨯₃ c')‖ ^ 2 = ‖n‖ ^ 2 - d ^ 2 := h_lagrange
    rw [h10] at h7
    rw [h9] at h7
    exact h7
  let gamma : ℝ := inner ℝ normal n_hat
  have h_gamma_eq : gamma = d / ‖n‖ := by
    dsimp only [gamma]
    have h1 : inner ℝ normal n_hat = (‖n‖)⁻¹ * inner ℝ normal n := by
      have h2 : n_hat = (‖n‖)⁻¹ • n := by rfl
      rw [h2, inner_smul_right] <;> ring
    rw [h1]
    have h3 : inner ℝ normal n = normal' ⬝ᵥ c' := by
      have h4 := plane_proj_inner_dot normal n
      rw [h4, hcross_def] <;> rfl
    rw [h3]
    have h5 : normal' ⬝ᵥ c' = d := by rfl
    rw [h5]
    field_simp [hN_pos.ne'] <;> ring
  have h_1_minus : 1 - |gamma| ≤ 4 * rho ^ 2 / kappa ^ 2 := by
    rw [h_gamma_eq]
    exact factor_bound hN_pos h_nonneg h_main_bound hkappa hkappa'
  exact plane_proj_final_bound rho kappa normal n_hat hnormal h_n_hat_norm gamma rfl h_1_minus hkappa hrho

end Kakeya.Assouad
