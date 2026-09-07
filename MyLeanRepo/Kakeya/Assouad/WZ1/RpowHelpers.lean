import Mathlib.Tactic

/-!
# Real.rpow helper lemmas for TargetProof

Collection of simple Real.rpow facts used throughout the
WZ1 direct coarse anchored global grain transport proof.
-/

noncomputable section

namespace Kakeya.Assouad

/-- If `x > 0`, then `x ^ e > 0` for any real exponent `e`. -/
lemma rpow_pos {x e : ℝ} (hx : 0 < x) : 0 < Real.rpow x e :=
  Real.rpow_pos_of_pos hx e

/-- If `0 < x ≤ 1` and `e ≥ 1`, then `x ^ e ≤ x`. -/
lemma rpow_le_self {x e : ℝ} (hx_pos : 0 < x) (hx_one : x ≤ 1) (he : 1 ≤ e) :
    Real.rpow x e ≤ x := by
  have h : Real.rpow x e ≤ Real.rpow x 1 :=
    Real.rpow_le_rpow_of_exponent_ge hx_pos hx_one he
  have h5 : Real.rpow x 1 = x := by simp
  rw [h5] at h
  exact h

/-- If `0 < x < 1` and `e > 0`, then `x ^ e < 1`. -/
lemma rpow_lt_one {x e : ℝ} (hx_pos : 0 < x) (hx_lt_one : x < 1) (he_pos : 0 < e) :
    Real.rpow x e < 1 :=
  Real.rpow_lt_one (by linarith) (by linarith) he_pos

/-- If `0 < x ≤ 1` and `e > 0`, then `x ^ e ≤ 1`. -/
lemma rpow_le_one {x e : ℝ} (hx_pos : 0 < x) (hx_one : x ≤ 1) (he_pos : 0 < e) :
    Real.rpow x e ≤ 1 :=
  Real.rpow_le_one (by linarith) hx_one (le_of_lt he_pos)

/-- Monotonicity in base: if `0 ≤ x ≤ y` and `e ≥ 0`, then `x ^ e ≤ y ^ e`. -/
lemma rpow_mono_base {x y e : ℝ} (hxy : x ≤ y) (hx : 0 ≤ x) (he : 0 ≤ e) :
    Real.rpow x e ≤ Real.rpow y e :=
  Real.rpow_le_rpow hx hxy he

/-- Monotonicity in exponent for base ≤ 1:
if `0 < x ≤ 1` and `e1 ≤ e2`, then `x ^ e2 ≤ x ^ e1`. -/
lemma rpow_anti_mono_exp {x e1 e2 : ℝ} (hx_pos : 0 < x) (hx_one : x ≤ 1) (h : e1 ≤ e2) :
    Real.rpow x e2 ≤ Real.rpow x e1 :=
  Real.rpow_le_rpow_of_exponent_ge hx_pos hx_one h

/-- Power composition: `(x ^ a) ^ b = x ^ (a * b)` for `x ≥ 0`. -/
lemma rpow_mul {x a b : ℝ} (hx : 0 ≤ x) :
    (Real.rpow x a) ^ b = Real.rpow x (a * b) :=
  (Real.rpow_mul hx a b).symm

/-- Given `rho = sourceDelta ^ (σ / (2 + σ))` with `0 < sourceDelta < 1`
and `0 < σ`, prove `0 < rho`. -/
lemma rho_pos_from_sourceDelta
    {sourceDelta rho sigma : ℝ}
    (hsourceDelta_pos : 0 < sourceDelta)
    (hrho_eq : rho = Real.rpow sourceDelta (sigma / (2 + sigma))) :
    0 < rho := by
  rw [hrho_eq]
  exact Real.rpow_pos_of_pos hsourceDelta_pos _

/-- Given `rho = sourceDelta ^ (σ / (2 + σ))` with `0 < sourceDelta < 1`,
prove `rho ≤ 1`. -/
lemma rho_le_one_from_sourceDelta
    {sourceDelta rho sigma : ℝ}
    (hsigma_pos : 0 < sigma)
    (hsourceDelta_pos : 0 < sourceDelta)
    (hsourceDelta_lt_one : sourceDelta < 1)
    (hrho_eq : rho = Real.rpow sourceDelta (sigma / (2 + sigma))) :
    rho ≤ 1 := by
  rw [hrho_eq]
  have h_exp_pos : 0 < sigma / (2 + sigma) := by positivity
  exact rpow_le_one hsourceDelta_pos (by linarith) h_exp_pos

/-- Given `sourceDelta ≤ sourceDelta₀ = (1/200) ^ ((2 + σ) / σ)`
and `rho = sourceDelta ^ (σ / (2 + σ))`, prove `rho ≤ 1/200`. -/
lemma rho_small_from_sourceDelta₀
    {sourceDelta sourceDelta₀ rho sigma : ℝ}
    (hsigma_pos : 0 < sigma)
    (hsourceDelta_pos : 0 < sourceDelta)
    (hsourceDelta_le : sourceDelta ≤ sourceDelta₀)
    (hsourceDelta₀_eq : sourceDelta₀ = (1 / 200 : ℝ) ^ ((2 + sigma) / sigma))
    (hrho_eq : rho = Real.rpow sourceDelta (sigma / (2 + sigma))) :
    rho ≤ 1 / 200 := by
  have h_exp_pos : 0 ≤ sigma / (2 + sigma) := by positivity
  have h1 : Real.rpow sourceDelta (sigma / (2 + sigma)) ≤
      Real.rpow sourceDelta₀ (sigma / (2 + sigma)) :=
    Real.rpow_le_rpow (by linarith) hsourceDelta_le h_exp_pos
  rw [hrho_eq]
  rw [hsourceDelta₀_eq] at h1
  set a : ℝ := (2 + sigma) / sigma with ha_def
  set b : ℝ := sigma / (2 + sigma) with hb_def
  have h_ab : a * b = 1 := by
    dsimp only [a, b]
    have h4 : 0 < 2 + sigma := by linarith
    field_simp [hsigma_pos.ne', h4.ne'] <;> ring
  have h2 : Real.rpow ((1 / 200 : ℝ) ^ a) b = (1 / 200 : ℝ) := by
    have h_comp : Real.rpow ((1 / 200 : ℝ) ^ a) b = Real.rpow (1 / 200 : ℝ) (a * b) :=
      rpow_mul (by norm_num)
    rw [h_comp, h_ab]
    simp
  rw [h2] at h1
  exact h1

/-- Convert any positive target cap on `rho` into a source-scale cap. -/
lemma rho_le_from_sourceDelta_power_cap
    {sourceDelta sourceDelta₀ rho rhoCap sigma : ℝ}
    (hsigma : 0 < sigma)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceDeltaLe : sourceDelta ≤ sourceDelta₀)
    (hrhoCap : 0 < rhoCap)
    (hsourceDelta₀ :
      sourceDelta₀ = Real.rpow rhoCap ((2 + sigma) / sigma))
    (hrho : rho = Real.rpow sourceDelta (sigma / (2 + sigma))) :
    rho ≤ rhoCap := by
  have hforward : 0 ≤ sigma / (2 + sigma) := by positivity
  have hmono :
      Real.rpow sourceDelta (sigma / (2 + sigma)) ≤
        Real.rpow sourceDelta₀ (sigma / (2 + sigma)) :=
    Real.rpow_le_rpow hsourceDelta.le hsourceDeltaLe hforward
  rw [hsourceDelta₀] at hmono
  have hcancel :
      Real.rpow (Real.rpow rhoCap ((2 + sigma) / sigma))
          (sigma / (2 + sigma)) = rhoCap := by
    calc
      Real.rpow (Real.rpow rhoCap ((2 + sigma) / sigma))
          (sigma / (2 + sigma))
          = Real.rpow rhoCap
              (((2 + sigma) / sigma) * (sigma / (2 + sigma))) :=
            (Real.rpow_mul hrhoCap.le _ _).symm
      _ = Real.rpow rhoCap 1 := by
        congr 1
        field_simp [hsigma.ne', (show 2 + sigma ≠ 0 by positivity)]
      _ = rhoCap := Real.rpow_one _
  rw [hcancel] at hmono
  rw [hrho]
  exact hmono

/-- At the WZ1 distinguished scale, the rescaled fine-radius contribution
raised to `sigma / 2` is exactly the distinguished scale again. -/
lemma sourceDelta_div_rho_rpow_half
    {sourceDelta rho sigma : ℝ}
    (hsigma : 0 < sigma)
    (hsourceDelta : 0 < sourceDelta)
    (hrho : rho = Real.rpow sourceDelta (sigma / (2 + sigma))) :
    Real.rpow (sourceDelta / rho) (sigma / 2) = rho := by
  have hrhoPos : 0 < rho := rho_pos_from_sourceDelta hsourceDelta hrho
  have hdiv :
      Real.rpow (sourceDelta / rho) (sigma / 2) =
        Real.rpow sourceDelta (sigma / 2) / Real.rpow rho (sigma / 2) :=
    Real.div_rpow hsourceDelta.le hrhoPos.le _
  rw [hdiv, hrho]
  have hdenom :
      Real.rpow (Real.rpow sourceDelta (sigma / (2 + sigma)))
          (sigma / 2) =
        Real.rpow sourceDelta ((sigma / (2 + sigma)) * (sigma / 2)) :=
    (Real.rpow_mul hsourceDelta.le _ _).symm
  rw [hdenom]
  have hquot :
      Real.rpow sourceDelta (sigma / 2) /
          Real.rpow sourceDelta ((sigma / (2 + sigma)) * (sigma / 2)) =
        Real.rpow sourceDelta
          (sigma / 2 - (sigma / (2 + sigma)) * (sigma / 2)) :=
    (Real.rpow_sub hsourceDelta _ _).symm
  rw [hquot]
  congr 1
  field_simp [hsigma.ne', (show 2 + sigma ≠ 0 by positivity)]
  ring

/-- Given `sourceDelta = rho ^ ((2 + σ) / σ)` with `0 < rho ≤ 1`
and `0 < σ`, prove `sourceDelta ≤ rho`. -/
lemma sourceDelta_le_rho_from_rho_base
    {sourceDelta rho sigma : ℝ}
    (hsigma_pos : 0 < sigma)
    (hrho_pos : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hsourceDelta_eq : sourceDelta = Real.rpow rho ((2 + sigma) / sigma)) :
    sourceDelta ≤ rho := by
  have h_exp_ge_one : 1 ≤ (2 + sigma) / sigma := by
    have h1 : 0 < sigma := hsigma_pos
    have h2 : sigma ≤ 2 + sigma := by linarith
    have h3 : 1 ≤ (2 + sigma) / sigma := by
      calc 1
        = sigma / sigma := by field_simp [h1.ne'] <;> ring
      _ ≤ (2 + sigma) / sigma := by gcongr
    exact h3
  rw [hsourceDelta_eq]
  exact rpow_le_self hrho_pos hrho_one h_exp_ge_one

/-- Given `sourceDelta = rho ^ ((2 + σ) / σ)` with `0 < rho ≤ 1`
and `0 < σ < 1`, prove `sourceDelta ≤ rho ^ 2`. -/
lemma sourceDelta_le_rho_squared_from_rho_base
    {sourceDelta rho sigma : ℝ}
    (hsigma_pos : 0 < sigma)
    (hsigma_one : sigma < 1)
    (hrho_pos : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hsourceDelta_eq : sourceDelta = Real.rpow rho ((2 + sigma) / sigma)) :
    sourceDelta ≤ rho ^ 2 := by
  have h_exp_ge_two : 2 ≤ (2 + sigma) / sigma := by
    have h1 : 0 < sigma := hsigma_pos
    have h2 : 2 * sigma ≤ 2 + sigma := by linarith
    have h3 : 2 ≤ (2 + sigma) / sigma := by
      calc 2
        = (2 * sigma) / sigma := by field_simp [h1.ne'] <;> ring
      _ ≤ (2 + sigma) / sigma := by gcongr
    exact h3
  rw [hsourceDelta_eq]
  have h3 : Real.rpow rho ((2 + sigma) / sigma) ≤ Real.rpow rho 2 :=
    Real.rpow_le_rpow_of_exponent_ge hrho_pos hrho_one h_exp_ge_two
  have h4 : Real.rpow rho 2 = rho ^ 2 := by simp
  rw [h4] at h3
  exact h3

/-- Given `sourceDelta = rho ^ ((2 + σ) / σ)` with `0 < rho ≤ 1`
and `0 < σ < 1`, prove `sourceDelta ≤ rho ^ 3`. -/
lemma sourceDelta_le_rho_cubed_from_rho_base
    {sourceDelta rho sigma : ℝ}
    (hsigma_pos : 0 < sigma)
    (hsigma_one : sigma < 1)
    (hrho_pos : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hsourceDelta_eq : sourceDelta = Real.rpow rho ((2 + sigma) / sigma)) :
    sourceDelta ≤ rho ^ 3 := by
  have h_exp_ge_three : 3 ≤ (2 + sigma) / sigma := by
    have h1 : 0 < sigma := hsigma_pos
    have h2 : 3 * sigma ≤ 2 + sigma := by linarith
    have h3 : 3 ≤ (2 + sigma) / sigma := by
      calc 3
        = (3 * sigma) / sigma := by field_simp [h1.ne'] <;> ring
      _ ≤ (2 + sigma) / sigma := by gcongr
    exact h3
  rw [hsourceDelta_eq]
  have h3 : Real.rpow rho ((2 + sigma) / sigma) ≤ Real.rpow rho 3 :=
    Real.rpow_le_rpow_of_exponent_ge hrho_pos hrho_one h_exp_ge_three
  have h4 : Real.rpow rho 3 = rho ^ 3 := by simp
  rw [h4] at h3
  exact h3

/-- Source positivity from rpow: if `0 ≤ sourceDelta` and
`0 < Real.rpow sourceDelta e` for `e > 0`, then `0 < sourceDelta`.
(If `sourceDelta = 0`, then `0 ^ e = 0` for `e > 0`.)
In WZ1, `0 ≤ sourceDelta` comes from the tube family scale context. -/
lemma sourceDelta_pos_from_rpow
    {sourceDelta e : ℝ} (he : 0 < e)
    (h_nonneg : 0 ≤ sourceDelta)
    (h : 0 < Real.rpow sourceDelta e) :
    0 < sourceDelta := by
  by_cases h0 : sourceDelta = 0
  · rw [h0] at h
    have h3 : Real.rpow 0 e = 0 := Real.zero_rpow (ne_of_gt he)
    rw [h3] at h
    exact False.elim (lt_irrefl 0 h)
  · have h4 : 0 < sourceDelta := by
      exact lt_of_le_of_ne h_nonneg (Ne.symm h0)
    exact h4

end Kakeya.Assouad
