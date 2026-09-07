import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalGrainTransfer
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeImageGeometry
import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Tactic

/-!
# Inverse-transpose normal map for Lemma-8 local grains normalization

Constructs the normalized inverse-transpose of the anisotropic linear map DΦ
and proves its Lipschitz bound on unit vectors.

Given DΦ(v) = (v₀ + g_mid·v₁, K·v₁, S·v₂), the inverse transpose is:
(DΦ)^{-T}(w) = (w₀, -g_mid/K·w₀ + w₁/K, w₂/S)

## Key bounds

- Operator norm: ‖(DΦ)^{-T} w‖ ≤ √6/K · ‖w‖
- Lower bound on unit vectors: ‖(DΦ)^{-T} w‖ ≥ 1/(S+2)
- Normalized Lipschitz: ‖invTransNormal w₁ - invTransNormal w₂‖ ≤ 2√6(S+2)/K · ‖w₁ - w₂‖

## Whiteprint node

InverseTransposeNormal
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set ENNReal

variable (g : SlopeFunction) (c d m : ℝ)

/-- Helper: coordinate absolute value ≤ norm. -/
private lemma coord_abs_le_norm (v : Point3) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  have h : ‖v‖ ^ 2 = (v 0)^2 + (v 1)^2 + (v 2)^2 := point3_coord_norm_sq v
  have h2 : (v i)^2 ≤ ‖v‖^2 := by
    rw [h]
    fin_cases i <;> simp [add_assoc] <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h3 : 0 ≤ ‖v‖ := norm_nonneg v
  have h4 : |v i|^2 = (v i)^2 := by rw [sq_abs]
  nlinarith [abs_nonneg (v i), h2, h4]

/-- Helper: if 0 < x ≤ 1 then 2 ≤ 2/x. -/
private lemma two_le_two_div {x : ℝ} (hx_pos : 0 < x) (hx_le_one : x ≤ 1) : 2 ≤ 2 / x := by
  have h : 0 ≤ 1 - x := by linarith
  have h2 : 0 ≤ 2 * (1 - x) / x := by
    apply div_nonneg
    · linarith
    · linarith
  have h3 : 2 / x - 2 = 2 * (1 - x) / x := by
    field_simp [hx_pos.ne'] <;> ring
  linarith

/-- Helper: if 0 ≤ a ≤ b then a^2 ≤ b^2. -/
private lemma sq_le_sq' {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a^2 ≤ b^2 := by
  nlinarith

/-- The normalized inverse-transpose map. -/
def invTransNormal (w : Point3) : Point3 :=
  let x := dPhiInvT g c d m w
  (‖x‖⁻¹ : ℝ) • x

/--
Operator norm upper bound for (DΦ)^{-T}.

‖(DΦ)^{-T} w‖ ≤ √6/K · ‖w‖ where K = m(d-c)/2.
-/
lemma dPhiInvT_opNorm_bound
    (hcd : c < d) (hm_pos : 0 < m) (hm_one : m ≤ 1)
    (h_dc : d - c ≤ 1 / 25)
    (hg_norm : g.IsNormalized)
    (hcd_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (w : Point3) :
    ‖dPhiInvT g c d m w‖ ≤ (Real.sqrt 6 / (m * (d - c) / 2)) * ‖w‖ := by
  set a := g (c + (d - c) / 2) with ha
  set b := m * (d - c) / 2 with hb
  set S' := 2 / (d - c) with hS
  have h_dc_pos : 0 < d - c := by linarith
  have hb_pos : 0 < b := by dsimp only [b] <;> positivity
  have hb_le_one : b ≤ 1 := by
    dsimp only [b]
    nlinarith
  have hS_ge2 : 2 ≤ S' := by
    dsimp only [S']
    exact two_le_two_div h_dc_pos (by linarith)
  have h_mid_in : c + (d - c) / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    have h2 : c ≤ c + (d - c) / 2 := by linarith
    have h3 : c + (d - c) / 2 ≤ d := by linarith
    exact hcd_sub ⟨h2, h3⟩
  have h1 : |a| ≤ 1 := (hg_norm (c + (d - c) / 2) h_mid_in).1
  let x := dPhiInvT g c d m w
  have hx0 : x 0 = w 0 := by
    simp [x, dPhiInvT, point3] <;> ring
  have hx1 : x 1 = -a / b * w 0 + w 1 / b := by
    simp [x, dPhiInvT, point3] <;> ring
  have hx2 : x 2 = w 2 / S' := by
    simp [x, dPhiInvT, point3] <;> ring
  have h_abs0 : |x 0| ≤ ‖w‖ := by
    rw [hx0]
    exact coord_abs_le_norm w 0
  have h_abs1 : |x 1| ≤ (2 / b) * ‖w‖ := by
    rw [hx1]
    set u := -a / b * w 0 with hu
    set v := w 1 / b with hv
    have h_tri : |u + v| ≤ |u| + |v| := by exact abs_add_le u v
    have h2 : |u| = (|a| / b) * |w 0| := by
      have h21 : |u| = |(-a / b) * w 0| := by rfl
      rw [h21, abs_mul]
      have h22 : |(-a / b)| = |a| / b := by
        rw [abs_div, abs_neg, abs_of_pos hb_pos]
      rw [h22] <;> ring
    have h3 : |v| = |w 1| / b := by
      have h31 : |v| = |w 1 / b| := by rfl
      rw [h31, abs_div, abs_of_pos hb_pos]
    rw [h2, h3] at h_tri
    have h5 : |w 0| ≤ ‖w‖ := coord_abs_le_norm w 0
    have h6 : |w 1| ≤ ‖w‖ := coord_abs_le_norm w 1
    have h7 : |a| ≤ 1 := h1
    have h8 : (|a| / b) * |w 0| ≤ (1 / b) * ‖w‖ := by
      have h9 : (|a| / b) * |w 0| ≤ (|a| / b) * ‖w‖ :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
      have h101 : |a| / b ≤ 1 / b :=
        div_le_div_of_nonneg_right h7 (by positivity)
      have h10 : (|a| / b) * ‖w‖ ≤ (1 / b) * ‖w‖ :=
        mul_le_mul_of_nonneg_right h101 (by positivity)
      exact h9.trans h10
    have h11 : |w 1| / b ≤ (1 / b) * ‖w‖ := by
      have h12 : |w 1| / b = (1 / b) * |w 1| := by ring
      rw [h12]
      exact mul_le_mul_of_nonneg_left h6 (by positivity)
    have h13 : (|a| / b) * |w 0| + |w 1| / b ≤ (2 / b) * ‖w‖ := by
      calc (|a| / b) * |w 0| + |w 1| / b
        ≤ (1 / b) * ‖w‖ + (1 / b) * ‖w‖ := add_le_add h8 h11
      _ = (2 / b) * ‖w‖ := by ring
    exact h_tri.trans h13
  have h_abs2 : |x 2| ≤ ‖w‖ := by
    rw [hx2]
    have hS1 : 1 ≤ S' := by linarith
    have h4 : |w 2 / S'| = |w 2| / S' := by
      rw [abs_div, abs_of_nonneg (show 0 ≤ S' by linarith)]
    have h5 : |w 2| / S' ≤ |w 2| := by
      have h6 : 0 ≤ |w 2| := abs_nonneg _
      have h7 : |w 2| / S' ≤ |w 2| / 1 := div_le_div_of_nonneg_left h6 (by linarith) hS1
      simpa using h7
    rw [h4]
    exact h5.trans (coord_abs_le_norm w 2)
  have h_norm_sq : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := point3_coord_norm_sq x
  have h6 : (x 0) ^ 2 ≤ ‖w‖ ^ 2 := by
    have h7 : 0 ≤ |x 0| := abs_nonneg _
    have h8 : |x 0| ≤ ‖w‖ := h_abs0
    have h9 : |x 0| ^ 2 ≤ ‖w‖ ^ 2 := sq_le_sq' h7 h8
    have h10 : (x 0) ^ 2 = |x 0| ^ 2 := by rw [sq_abs]
    rw [h10]
    exact h9
  have h8b : (x 1) ^ 2 ≤ (4 / b ^ 2) * ‖w‖ ^ 2 := by
    have h9 : 0 ≤ |x 1| := abs_nonneg _
    have h10 : |x 1| ≤ (2 / b) * ‖w‖ := h_abs1
    have h11 : |x 1| ^ 2 ≤ ((2 / b) * ‖w‖) ^ 2 := sq_le_sq' h9 h10
    have h12 : (x 1) ^ 2 = |x 1| ^ 2 := by rw [sq_abs]
    rw [h12]
    have h13 : ((2 / b) * ‖w‖) ^ 2 = (4 / b ^ 2) * ‖w‖ ^ 2 := by ring
    rw [h13] at h11
    exact h11
  have h12b : (x 2) ^ 2 ≤ ‖w‖ ^ 2 := by
    have h13 : 0 ≤ |x 2| := abs_nonneg _
    have h14 : |x 2| ≤ ‖w‖ := h_abs2
    have h15 : |x 2| ^ 2 ≤ ‖w‖ ^ 2 := sq_le_sq' h13 h14
    have h16 : (x 2) ^ 2 = |x 2| ^ 2 := by rw [sq_abs]
    rw [h16]
    exact h15
  have h14 : b ^ 2 ≤ 1 := by
    have h15 : 0 ≤ b := by positivity
    nlinarith
  have h16 : 0 < b ^ 2 := by positivity
  have h17 : (1 : ℝ) ≤ 1 / b ^ 2 := by
    have h171 : 1 / b ^ 2 - 1 = (1 - b ^ 2) / b ^ 2 := by
      field_simp [h16.ne'] <;> ring
    have h172 : 0 ≤ (1 - b ^ 2) / b ^ 2 := by
      apply div_nonneg
      · linarith
      · positivity
    linarith [h171, h172]
  have h151 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have h15 : ‖w‖ ^ 2 ≤ (1 / b ^ 2) * ‖w‖ ^ 2 := by
    have h : (1 : ℝ) * ‖w‖ ^ 2 ≤ (1 / b ^ 2) * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right h17 h151
    simpa using h
  have h_main_sq : ‖x‖ ^ 2 ≤ (6 / b ^ 2) * ‖w‖ ^ 2 := by
    rw [h_norm_sq]
    have h20 : (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 ≤
        (1 / b ^ 2) * ‖w‖ ^ 2 + (4 / b ^ 2) * ‖w‖ ^ 2 + (1 / b ^ 2) * ‖w‖ ^ 2 := by
      linarith [h6, h8b, h12b, h15]
    have h21 : (1 / b ^ 2) * ‖w‖ ^ 2 + (4 / b ^ 2) * ‖w‖ ^ 2 + (1 / b ^ 2) * ‖w‖ ^ 2 =
        (6 / b ^ 2) * ‖w‖ ^ 2 := by ring
    rw [h21] at h20
    exact h20
  have h_pos : 0 ≤ Real.sqrt 6 / b := by positivity
  have h_sq : ((Real.sqrt 6 / b) * ‖w‖) ^ 2 = (6 / b ^ 2) * ‖w‖ ^ 2 := by
    have h22 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    calc
      ((Real.sqrt 6 / b) * ‖w‖) ^ 2
        = (Real.sqrt 6) ^ 2 / b ^ 2 * ‖w‖ ^ 2 := by ring
      _ = 6 / b ^ 2 * ‖w‖ ^ 2 := by rw [h22] <;> ring
  have h_final : ‖x‖ ≤ (Real.sqrt 6 / b) * ‖w‖ := by
    set y := (Real.sqrt 6 / b) * ‖w‖ with hy
    have h23 : 0 ≤ ‖x‖ := norm_nonneg x
    have h24 : 0 ≤ y := by
      dsimp only [y]
      positivity
    have h25 : ‖x‖ ^ 2 ≤ y ^ 2 := by
      rw [h_sq] <;> exact h_main_sq
    nlinarith
  exact h_final

/--
Lower bound for (DΦ)^{-T} on unit vectors.

For ‖w‖ = 1: ‖(DΦ)^{-T} w‖ ≥ 1/(S+2) where S = 2/(d-c).
-/
lemma dPhiInvT_lower_bound
    (hcd : c < d) (hm_pos : 0 < m) (hm_one : m ≤ 1)
    (h_dc : d - c ≤ 1 / 25)
    (hg_norm : g.IsNormalized)
    (hcd_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (w : Point3) (hw : ‖w‖ = 1) :
    1 / ((2 / (d - c)) + 2) ≤ ‖dPhiInvT g c d m w‖ := by
  set S' := 2 / (d - c) with hS
  set g_mid := g (c + (d - c) / 2) with hgmid
  have h_dc_pos : 0 < d - c := by linarith
  have h_mid_in : c + (d - c) / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    have h2 : c ≤ c + (d - c) / 2 := by linarith
    have h3 : c + (d - c) / 2 ≤ d := by linarith
    exact hcd_sub ⟨h2, h3⟩
  have hg_abs : |g_mid| ≤ 1 := (hg_norm (c + (d - c) / 2) h_mid_in).1
  set K := m * (d - c) / 2 with hK
  have hK_abs : |K| ≤ 1 := by
    dsimp only [K]
    have h4 : 0 ≤ K := by positivity
    rw [abs_of_nonneg h4]
    nlinarith
  have hS_ge2 : 2 ≤ S' := by
    dsimp only [S']
    exact two_le_two_div h_dc_pos (by linarith)
  have h1 : inner ℝ (dPhiLin g c d m w) (dPhiInvT g c d m w) = inner ℝ w w :=
    dPhi_inner_identity g c d m hcd hm_pos w w
  have h2 : inner ℝ w w = ‖w‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
  have h_inner : inner ℝ (dPhiLin g c d m w) (dPhiInvT g c d m w) = 1 := by
    rw [h1, h2, hw] <;> norm_num
  have h3 : (1 : ℝ) ≤ ‖dPhiLin g c d m w‖ * ‖dPhiInvT g c d m w‖ := by
    have h4 : inner ℝ (dPhiLin g c d m w) (dPhiInvT g c d m w) ≤
        ‖dPhiLin g c d m w‖ * ‖dPhiInvT g c d m w‖ := real_inner_le_norm _ _
    rw [h_inner] at h4
    exact h4
  have h5 : ‖dPhiLin g c d m w‖ ≤ S' + 2 := by
    have h6 : ‖dPhiLin g c d m w‖ ≤ S' * ‖w‖ := by
      simpa [dPhiLin] using anisotropicMap_opNorm_bound hg_abs hK_abs hS_ge2 w
    rw [hw] at h6
    have h7 : S' ≤ S' + 2 := by linarith
    linarith
  have h8 : 0 ≤ ‖dPhiInvT g c d m w‖ := norm_nonneg _
  have h9 : ‖dPhiLin g c d m w‖ * ‖dPhiInvT g c d m w‖ ≤ (S' + 2) * ‖dPhiInvT g c d m w‖ :=
    mul_le_mul_of_nonneg_right h5 h8
  have h7 : (1 : ℝ) ≤ (S' + 2) * ‖dPhiInvT g c d m w‖ := by
    linarith [h3, h9]
  have hS_pos : 0 < S' + 2 := by linarith
  have h10 : 1 / (S' + 2) ≤ ‖dPhiInvT g c d m w‖ := by
    have h11 : 1 ≤ (S' + 2) * ‖dPhiInvT g c d m w‖ := h7
    have h12 : 1 / (S' + 2) ≤ ((S' + 2) * ‖dPhiInvT g c d m w‖) / (S' + 2) := by
      apply div_le_div_of_nonneg_right h11 (by linarith)
    have h13 : ((S' + 2) * ‖dPhiInvT g c d m w‖) / (S' + 2) = ‖dPhiInvT g c d m w‖ := by
      field_simp [hS_pos.ne'] <;> ring
    rw [h13] at h12
    exact h12
  simpa [hS] using h10

/--
Lipschitz bound for the normalized inverse-transpose map on unit vectors.

‖invTransNormal w₁ - invTransNormal w₂‖ ≤ 2√6(S+2)/K · ‖w₁ - w₂‖

where K = m(d-c)/2 and S = 2/(d-c).

Since 2√6 < 5, this is ≤ 5(S+2)/K.
-/
lemma invTransNormal_lipschitz
    (hcd : c < d) (hm_pos : 0 < m) (hm_one : m ≤ 1)
    (h_dc : d - c ≤ 1 / 25)
    (hg_norm : g.IsNormalized)
    (hcd_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (w1 w2 : Point3)
    (hw1 : ‖w1‖ = 1) (hw2 : ‖w2‖ = 1) :
    ‖invTransNormal g c d m w1 - invTransNormal g c d m w2‖ ≤
      (2 * Real.sqrt 6 * ((2 / (d - c)) + 2) / (m * (d - c) / 2)) * ‖w1 - w2‖ := by
  set S' := 2 / (d - c) with hS
  set K := m * (d - c) / 2 with hK
  have hK_pos : 0 < K := by dsimp only [K] <;> positivity
  set x := dPhiInvT g c d m w1 with hx
  set y := dPhiInvT g c d m w2 with hy
  have hx_lower : 1 / (S' + 2) ≤ ‖x‖ :=
    dPhiInvT_lower_bound g c d m hcd hm_pos hm_one h_dc hg_norm hcd_sub w1 hw1
  have hy_lower : 1 / (S' + 2) ≤ ‖y‖ :=
    dPhiInvT_lower_bound g c d m hcd hm_pos hm_one h_dc hg_norm hcd_sub w2 hw2
  have h_m_lower : 0 < 1 / (S' + 2) := by positivity
  have h_norm_lipschitz : ‖(‖x‖⁻¹ : ℝ) • x - (‖y‖⁻¹ : ℝ) • y‖ ≤
      (2 / (1 / (S' + 2))) * ‖x - y‖ :=
    normalization_lipschitz h_m_lower hx_lower hy_lower
  have h_linear : ‖x - y‖ ≤ (Real.sqrt 6 / K) * ‖w1 - w2‖ := by
    have h_sub : x - y = dPhiInvT g c d m (w1 - w2) := by
      rw [dPhiInvT_sub g c d m w1 w2]
    rw [h_sub]
    exact dPhiInvT_opNorm_bound g c d m hcd hm_pos hm_one h_dc hg_norm hcd_sub (w1 - w2)
  have h_main : ‖invTransNormal g c d m w1 - invTransNormal g c d m w2‖ ≤
      (2 / (1 / (S' + 2))) * ((Real.sqrt 6 / K) * ‖w1 - w2‖) := by
    simpa [invTransNormal] using calc
      ‖invTransNormal g c d m w1 - invTransNormal g c d m w2‖
        ≤ (2 / (1 / (S' + 2))) * ‖x - y‖ := h_norm_lipschitz
      _ ≤ (2 / (1 / (S' + 2))) * ((Real.sqrt 6 / K) * ‖w1 - w2‖) :=
        mul_le_mul_of_nonneg_left h_linear (by positivity)
  have h9 : (2 / (1 / (S' + 2))) * ((Real.sqrt 6 / K) * ‖w1 - w2‖) =
      (2 * Real.sqrt 6 * (S' + 2) / K) * ‖w1 - w2‖ := by
    field_simp [hK_pos.ne'] <;> ring
  rw [h9] at h_main
  simpa [hS, hK] using h_main

end Kakeya.Assouad

end
