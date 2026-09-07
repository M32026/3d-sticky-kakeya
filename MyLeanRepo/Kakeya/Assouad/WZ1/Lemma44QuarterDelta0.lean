import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44DyadicAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Helper lemmas for choosing δ₀ and proving arithmetic premises

For the dyadic regime (ζ < 1/4, E < 1), we choose δ₀ as the minimum of
several bounds so that all arithmetic premises hold uniformly.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- If `0 < z < 1/4`, then `8*alpha/z + 2*lambda - 4*alpha > 0`. -/
lemma D2_pos {alpha lambda zeta : ℝ} (halpha : 0 < alpha) (hlambda : 0 < lambda)
    (hzeta : 0 < zeta) (hzeta_small : zeta < 1 / 4) :
    0 < 8 * alpha / zeta + 2 * lambda - 4 * alpha := by
  have h1 : 1 / zeta > 4 := by
    have h2 : zeta < 1 / 4 := hzeta_small
    have h3 : 0 < zeta := hzeta
    have h4 : 1 / zeta > 1 / (1 / 4 : ℝ) := one_div_lt_one_div_of_lt h3 h2
    have h5 : 1 / (1 / 4 : ℝ) = 4 := by norm_num
    rw [h5] at h4
    exact h4
  have h6 : 8 * alpha / zeta > 32 * alpha := by
    have h7 : 8 * alpha / zeta = 8 * alpha * (1 / zeta) := by
      field_simp [hzeta.ne'] <;> ring
    rw [h7]
    have h8 : 8 * alpha * (1 / zeta) > 8 * alpha * 4 := by
      gcongr
      <;> linarith
    linarith
  linarith

/-- If `0 < z < 1/4`, then `8*alpha/z + lambda - 8*alpha > 0`. -/
lemma D3_pos {alpha lambda zeta : ℝ} (halpha : 0 < alpha) (hlambda : 0 < lambda)
    (hzeta : 0 < zeta) (hzeta_small : zeta < 1 / 4) :
    0 < 8 * alpha / zeta + lambda - 8 * alpha := by
  have h1 : 1 / zeta > 4 := by
    have h2 : zeta < 1 / 4 := hzeta_small
    have h3 : 0 < zeta := hzeta
    have h4 : 1 / zeta > 1 / (1 / 4 : ℝ) := one_div_lt_one_div_of_lt h3 h2
    have h5 : 1 / (1 / 4 : ℝ) = 4 := by norm_num
    rw [h5] at h4
    exact h4
  have h6 : 8 * alpha / zeta > 32 * alpha := by
    have h7 : 8 * alpha / zeta = 8 * alpha * (1 / zeta) := by
      field_simp [hzeta.ne'] <;> ring
    rw [h7]
    have h8 : 8 * alpha * (1 / zeta) > 8 * alpha * 4 := by
      gcongr
      <;> linarith
    linarith
  linarith

/-- Given `0 < b ≤ 1`, `0 < x`, and `δ ≤ b^(1/x)`, then `δ^x ≤ b`. -/
lemma rpow_bound_of_le {delta b x : ℝ} (hdelta : 0 < delta) (hb_pos : 0 < b) (hb_one : b ≤ 1)
    (hx_pos : 0 < x) (h : delta ≤ Real.rpow b (1 / x)) :
    Real.rpow delta x ≤ b := by
  have hb_nonneg : 0 ≤ b := by linarith
  have h1 : Real.rpow delta x ≤ Real.rpow (Real.rpow b (1 / x)) x :=
    Real.rpow_le_rpow (by linarith) h hx_pos.le
  have h2 : Real.rpow (Real.rpow b (1 / x)) x = Real.rpow b ((1 / x) * x) :=
    (Real.rpow_mul hb_nonneg (1 / x) x).symm
  rw [h2] at h1
  have h3 : (1 / x) * x = 1 := by
    field_simp [hx_pos.ne'] <;> ring
  rw [h3] at h1
  have h4 : Real.rpow b 1 = b := by simp
  rw [h4] at h1
  exact h1

/-- Given `δ ≤ 2^(-1/(4*K_exp))` with `K_exp > 0`, then `δ^(-K_exp) / 2^(1/4) ≥ 1`. -/
lemma K_ge_one_of_bound {delta K_exp : ℝ} (hdelta : 0 < delta) (hK_exp_pos : 0 < K_exp)
    (h : delta ≤ Real.rpow 2 (-(1 / (4 * K_exp)))) :
    1 ≤ Real.rpow delta (-K_exp) / Real.rpow 2 (1 / 4 : ℝ) := by
  have h1 : Real.rpow delta K_exp ≤ Real.rpow 2 (-(1 / 4 : ℝ)) := by
    have h2 : Real.rpow delta K_exp ≤ Real.rpow (Real.rpow 2 (-(1 / (4 * K_exp)))) K_exp :=
      Real.rpow_le_rpow (by linarith) h hK_exp_pos.le
    have h3 : Real.rpow (Real.rpow 2 (-(1 / (4 * K_exp)))) K_exp =
        Real.rpow 2 ((-(1 / (4 * K_exp))) * K_exp) :=
      (Real.rpow_mul (by norm_num) (-(1 / (4 * K_exp))) K_exp).symm
    rw [h3] at h2
    have h4 : (-(1 / (4 * K_exp))) * K_exp = -(1 / 4 : ℝ) := by
      field_simp [hK_exp_pos.ne'] <;> ring
    rw [h4] at h2
    exact h2
  have h_pos1 : 0 < Real.rpow delta K_exp := Real.rpow_pos_of_pos hdelta K_exp
  have h_pos2 : 0 < Real.rpow 2 (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) (1 / 4 : ℝ)
  have h5 : Real.rpow 2 (-(1 / 4 : ℝ)) = (Real.rpow 2 (1 / 4 : ℝ))⁻¹ :=
    Real.rpow_neg (by norm_num) (1 / 4 : ℝ)
  have h5' : Real.rpow 2 (-(1 / 4 : ℝ)) = 1 / Real.rpow 2 (1 / 4 : ℝ) := by
    rw [h5] <;> field_simp <;> ring
  have h1' : Real.rpow delta K_exp ≤ 1 / Real.rpow 2 (1 / 4 : ℝ) := by
    rw [h5'] at h1
    exact h1
  have h6 : Real.rpow delta (-K_exp) = (Real.rpow delta K_exp)⁻¹ :=
    Real.rpow_neg (by linarith) K_exp
  have h6' : Real.rpow delta (-K_exp) = 1 / Real.rpow delta K_exp := by
    rw [h6] <;> field_simp <;> ring
  rw [h6']
  have h7 : 1 / (1 / Real.rpow 2 (1 / 4 : ℝ)) ≤ 1 / Real.rpow delta K_exp :=
    one_div_le_one_div_of_le h_pos1 h1'
  have h8 : 1 / (1 / Real.rpow 2 (1 / 4 : ℝ)) = Real.rpow 2 (1 / 4 : ℝ) := by
    field_simp [h_pos2.ne'] <;> ring
  rw [h8] at h7
  have h9 : (1 / Real.rpow delta K_exp) / Real.rpow 2 (1 / 4 : ℝ) ≥ 1 := by
    have h10 : Real.rpow 2 (1 / 4 : ℝ) ≤ 1 / Real.rpow delta K_exp := h7
    have h11 : 0 < Real.rpow 2 (1 / 4 : ℝ) := h_pos2
    calc
      (1 / Real.rpow delta K_exp) / Real.rpow 2 (1 / 4 : ℝ)
        ≥ Real.rpow 2 (1 / 4 : ℝ) / Real.rpow 2 (1 / 4 : ℝ) := by gcongr
      _ = 1 := by
        field_simp [h11.ne'] <;> ring
  exact h9

/-- hprem2 bound: from `δ^{D2} ≤ 1/208`, prove `8*(13*R) ≤ δ^{λ+4α} * δ^{λ+4α/ζ}`. -/
lemma prem2_bound
    {delta lambda zeta alpha D2 : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hlambda : 0 < lambda) (hzeta : 0 < zeta) (halpha : 0 < alpha)
    (hD2_pos : 0 < D2)
    (hD2_def : D2 = 8 * alpha / zeta + 2 * lambda - 4 * alpha)
    (hE_def : 12 * alpha / zeta + 4 * lambda = D2 + (lambda + 4 * alpha + lambda + 4 * alpha / zeta))
    {T T' : ℝ} (hT_def : T = Real.rpow delta (12 * alpha / zeta + 4 * lambda))
    (hT'_def : T' = 2 * T)
    (hD2_bound : Real.rpow delta D2 ≤ 1 / 208)
    {R : ℝ} (hR_lt_T' : R < T') :
    8 * (13 * R) ≤ Real.rpow delta (lambda + 4 * alpha) * Real.rpow delta (lambda + 4 * alpha / zeta) := by
  have h1 : 8 * (13 * R) < 208 * T := by
    rw [hT'_def] at hR_lt_T'
    linarith
  have h_rhs1 : Real.rpow delta (lambda + 4 * alpha + lambda + 4 * alpha / zeta) =
      Real.rpow delta (lambda + 4 * alpha) * Real.rpow delta (lambda + 4 * alpha / zeta) := by
    have h := Real.rpow_add hdelta (lambda + 4 * alpha) (lambda + 4 * alpha / zeta)
    have h_eq : (lambda + 4 * alpha) + (lambda + 4 * alpha / zeta) = lambda + 4 * alpha + lambda + 4 * alpha / zeta := by ring
    rw [h_eq] at h
    exact h
  have h_rhs2 : Real.rpow delta (D2 + (lambda + 4 * alpha + lambda + 4 * alpha / zeta)) =
      Real.rpow delta D2 * Real.rpow delta (lambda + 4 * alpha + lambda + 4 * alpha / zeta) :=
    Real.rpow_add hdelta D2 (lambda + 4 * alpha + lambda + 4 * alpha / zeta)
  have h5 : 208 * T ≤ Real.rpow delta (lambda + 4 * alpha) * Real.rpow delta (lambda + 4 * alpha / zeta) := by
    rw [hT_def]
    rw [hE_def]
    rw [h_rhs2, h_rhs1]
    have h9 : 208 * Real.rpow delta D2 ≤ 1 := by linarith [hD2_bound]
    have h10 : 0 ≤ Real.rpow delta D2 := Real.rpow_nonneg (by linarith) _
    have h11 : 0 ≤ Real.rpow delta (lambda + 4 * alpha + lambda + 4 * alpha / zeta) :=
      Real.rpow_nonneg (by linarith) _
    nlinarith
  linarith

/-- Helper: `(δ^x)^4 = δ^(4*x)` for `δ > 0`. -/
lemma rpow4_eq {delta x : ℝ} (hdelta : 0 < delta) :
  (Real.rpow delta x) ^ 4 = Real.rpow delta (4 * x) := by
  have h1 : (Real.rpow delta x) ^ 2 = Real.rpow delta (2 * x) := by
    have h11 : (Real.rpow delta x) ^ 2 = Real.rpow delta x * Real.rpow delta x := by ring
    rw [h11]
    have h12 : Real.rpow delta x * Real.rpow delta x = Real.rpow delta (x + x) :=
      (Real.rpow_add hdelta x x).symm
    rw [h12]
    have h13 : x + x = 2 * x := by ring
    rw [h13]
  have h2 : (Real.rpow delta x) ^ 4 = ((Real.rpow delta x) ^ 2) ^ 2 := by ring
  rw [h2, h1]
  have h3 : (Real.rpow delta (2 * x)) ^ 2 = Real.rpow delta (4 * x) := by
    have h31 : (Real.rpow delta (2 * x)) ^ 2 = Real.rpow delta (2 * x) * Real.rpow delta (2 * x) := by ring
    rw [h31]
    have h32 : Real.rpow delta (2 * x) * Real.rpow delta (2 * x) = Real.rpow delta (2 * x + 2 * x) :=
      (Real.rpow_add hdelta (2 * x) (2 * x)).symm
    rw [h32]
    have h33 : 2 * x + 2 * x = 4 * x := by ring
    rw [h33]
  exact h3

/-- hprem3 bound: from `δ^{D3} ≤ 1/624000`, prove the hprem3 inequality. -/
lemma prem3_bound
    {delta lambda zeta alpha K_exp D3 : ℝ}
    (hdelta : 0 < delta)
    (hlambda : 0 < lambda) (hzeta : 0 < zeta) (halpha : 0 < alpha)
    (hK_exp_pos : 0 < K_exp) (hD3_pos : 0 < D3)
    (hK_exp_def : K_exp = 3 * alpha / zeta + lambda)
    (hD3_def : D3 = 8 * alpha / zeta + lambda - 8 * alpha)
    (hD3_bound : Real.rpow delta D3 ≤ 1 / 624000) :
    (312000 : ℝ) / (Real.rpow delta (-K_exp) / Real.rpow 2 (1 / 4 : ℝ)) ^ 4 *
      Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta)) ≤
    Real.rpow delta (4 * alpha) := by
  set K_int : ℝ := Real.rpow delta (-K_exp) / Real.rpow 2 (1 / 4 : ℝ) with hK_int
  have hK_int_pos : 0 < K_int := by
    dsimp only [K_int]
    have h1 : 0 < Real.rpow delta (-K_exp) := Real.rpow_pos_of_pos hdelta _
    have h2 : 0 < Real.rpow 2 (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    exact div_pos h1 h2
  have h_rpow2_4 : (Real.rpow 2 (1 / 4 : ℝ)) ^ 4 = 2 := by
    have h_nat : (Real.rpow 2 (1 / 4 : ℝ)) ^ 4 = Real.rpow (Real.rpow 2 (1 / 4 : ℝ)) (4 : ℝ) := by
      have h : (Real.rpow 2 (1 / 4 : ℝ)) ^ (4 : ℝ) = (Real.rpow 2 (1 / 4 : ℝ)) ^ 4 :=
        Real.rpow_natCast (Real.rpow 2 (1 / 4 : ℝ)) 4
      exact h.symm
    rw [h_nat]
    have h_two_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    have h_mul : Real.rpow (Real.rpow 2 (1 / 4 : ℝ)) (4 : ℝ) = Real.rpow 2 ((1 / 4 : ℝ) * (4 : ℝ)) :=
      (Real.rpow_mul h_two_nonneg (1 / 4 : ℝ) (4 : ℝ)).symm
    rw [h_mul]
    have h2 : (1 / 4 : ℝ) * (4 : ℝ) = 1 := by ring
    rw [h2] <;> simp
  have h1 : K_int ^ 4 = Real.rpow delta (-4 * K_exp) / 2 := by
    rw [hK_int]
    have h2 : (Real.rpow delta (-K_exp) / Real.rpow 2 (1 / 4 : ℝ)) ^ 4 =
        (Real.rpow delta (-K_exp)) ^ 4 / (Real.rpow 2 (1 / 4 : ℝ)) ^ 4 := by field_simp
    rw [h2, h_rpow2_4]
    have h3 : (Real.rpow delta (-K_exp)) ^ 4 = Real.rpow delta (-4 * K_exp) := by
      have h31 := rpow4_eq (x := -K_exp) hdelta
      have h32 : 4 * (-K_exp) = -4 * K_exp := by ring
      rw [h32] at h31
      exact h31
    rw [h3] <;> ring
  have h4 : (312000 : ℝ) / K_int ^ 4 = 624000 * Real.rpow delta (4 * K_exp) := by
    have h_pos4 : 0 < Real.rpow delta (4 * K_exp) := Real.rpow_pos_of_pos hdelta _
    have h_neg : Real.rpow delta (-4 * K_exp) = (Real.rpow delta (4 * K_exp))⁻¹ := by
      have h9 : -4 * K_exp = -(4 * K_exp) := by ring
      rw [h9]
      exact Real.rpow_neg hdelta.le (4 * K_exp)
    have h_eq1 : (312000 : ℝ) / K_int ^ 4 = (312000 : ℝ) / (Real.rpow delta (-4 * K_exp) / 2) := by
      rw [h1]
    rw [h_eq1]
    have h_eq2 : (312000 : ℝ) / (Real.rpow delta (-4 * K_exp) / 2) =
        624000 * (Real.rpow delta (-4 * K_exp))⁻¹ := by
      field_simp [hK_int_pos.ne'] <;> ring
    rw [h_eq2]
    rw [h_neg]
    have h_final : 624000 * ((Real.rpow delta (4 * K_exp))⁻¹)⁻¹ = 624000 * Real.rpow delta (4 * K_exp) := by
      have h_ne : (Real.rpow delta (4 * K_exp)) ≠ 0 := h_pos4.ne'
      field_simp [h_ne] <;> ring
    exact h_final
  have h_exp3 : 4 * K_exp = 12 * alpha / zeta + 4 * lambda := by
    rw [hK_exp_def] <;> ring
  have hD3_eq : D3 + 4 * alpha = 8 * alpha / zeta + lambda - 4 * alpha := by
    rw [hD3_def] <;> ring
  have h_sum_exp : (12 * alpha / zeta + 4 * lambda) + (-(3 * lambda + 4 * alpha + 4 * alpha / zeta)) =
      8 * alpha / zeta + lambda - 4 * alpha := by
    field_simp [hzeta.ne'] <;> ring
  calc
    (312000 : ℝ) / K_int ^ 4 * Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta))
      = 624000 * Real.rpow delta (4 * K_exp) * Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta)) := by
        rw [h4] <;> ring
    _ = 624000 * Real.rpow delta (12 * alpha / zeta + 4 * lambda) * Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta)) := by
        rw [h_exp3] <;> ring
    _ = 624000 * Real.rpow delta ((12 * alpha / zeta + 4 * lambda) + (-(3 * lambda + 4 * alpha + 4 * alpha / zeta))) := by
        have h_rpow : Real.rpow delta (12 * alpha / zeta + 4 * lambda) * Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta)) =
            Real.rpow delta ((12 * alpha / zeta + 4 * lambda) + (-(3 * lambda + 4 * alpha + 4 * alpha / zeta))) :=
          (Real.rpow_add hdelta (12 * alpha / zeta + 4 * lambda) (-(3 * lambda + 4 * alpha + 4 * alpha / zeta))).symm
        have h_assoc : (624000 * Real.rpow delta (12 * alpha / zeta + 4 * lambda)) * Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta)) =
            624000 * (Real.rpow delta (12 * alpha / zeta + 4 * lambda) * Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta))) := by ring
        rw [h_assoc, h_rpow]
    _ = 624000 * Real.rpow delta (8 * alpha / zeta + lambda - 4 * alpha) := by rw [h_sum_exp]
    _ = 624000 * Real.rpow delta (D3 + 4 * alpha) := by rw [hD3_eq]
    _ = (624000 * Real.rpow delta D3) * Real.rpow delta (4 * alpha) := by
        have h_rpow : Real.rpow delta (D3 + 4 * alpha) = Real.rpow delta D3 * Real.rpow delta (4 * alpha) :=
          Real.rpow_add hdelta D3 (4 * alpha)
        have h : 624000 * Real.rpow delta (D3 + 4 * alpha) = (624000 * Real.rpow delta D3) * Real.rpow delta (4 * alpha) := by
          rw [h_rpow] <;> ring
        exact h
    _ ≤ 1 * Real.rpow delta (4 * alpha) := by
        have h14 : 624000 * Real.rpow delta D3 ≤ 1 := by linarith [hD3_bound]
        have h15 : 0 ≤ Real.rpow delta (4 * alpha) := Real.rpow_nonneg (by linarith) _
        nlinarith
    _ = Real.rpow delta (4 * alpha) := by ring

end Kakeya.Assouad
