import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Absorbing fixed constants into small powers

These elementary lemmas keep the paper's `delta^{-O(eta)}` bookkeeping out of
the geometric assembly targets.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Every finite `ENNReal` constant is dominated by `delta^(-gamma)` for all
sufficiently small positive `delta`.
-/
lemma exists_delta_realRpowENN_bound
    (D : ENNReal) (hD : D ≠ ⊤)
    {gamma : ℝ} (hgamma : 0 < gamma) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        D ≤ Kakeya.realRpowENN delta (-gamma) := by
  by_cases hD_zero : D = 0
  · exact ⟨1, by norm_num, le_rfl, fun _ _ _ => by simp [hD_zero]⟩
  have hD_real_pos : 0 < D.toReal :=
    ENNReal.toReal_pos hD_zero hD
  let delta₀ : ℝ := min 1 (Real.rpow D.toReal (-(gamma⁻¹)))
  have hpow_pos :
      0 < Real.rpow D.toReal (-(gamma⁻¹)) :=
    Real.rpow_pos_of_pos hD_real_pos _
  have hdelta₀_pos : 0 < delta₀ := by
    exact lt_min zero_lt_one hpow_pos
  have hdelta₀_one : delta₀ ≤ 1 := min_le_left _ _
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta_pos hdelta_le
  have hdelta_pow :
      delta ≤ Real.rpow D.toReal (-(gamma⁻¹)) :=
    hdelta_le.trans (min_le_right _ _)
  have hneg : -gamma < 0 := by linarith
  have hmono :
      Real.rpow (Real.rpow D.toReal (-(gamma⁻¹))) (-gamma) ≤
        Real.rpow delta (-gamma) :=
    Real.rpow_le_rpow_of_nonpos hdelta_pos hdelta_pow hneg.le
  have hpower_eq :
      Real.rpow (Real.rpow D.toReal (-(gamma⁻¹))) (-gamma) =
        D.toReal := by
    have hgamma_ne : gamma ≠ 0 := hgamma.ne'
    calc
      Real.rpow (Real.rpow D.toReal (-(gamma⁻¹))) (-gamma)
          = Real.rpow D.toReal ((-(gamma⁻¹)) * (-gamma)) := by
            exact (Real.rpow_mul hD_real_pos.le _ _).symm
      _ = Real.rpow D.toReal 1 := by
            congr 1
            field_simp [hgamma_ne]
      _ = D.toReal := Real.rpow_one _
  rw [hpower_eq] at hmono
  have hD_repr : D = ENNReal.ofReal D.toReal :=
    (ENNReal.ofReal_toReal hD).symm
  rw [hD_repr, Kakeya.realRpowENN]
  exact ENNReal.ofReal_mono hmono

/--
Any fixed nonnegative real constant is absorbed by a positive gap between
two powers of a sufficiently small positive scale.
-/
lemma exists_delta_mul_rpow_le_rpow
    (D : ℝ) (hD : 0 ≤ D)
    {alpha beta : ℝ} (hbeta_alpha : beta < alpha) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        D * Real.rpow delta alpha ≤ Real.rpow delta beta := by
  let gamma : ℝ := alpha - beta
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    linarith
  rcases exists_delta_realRpowENN_bound (ENNReal.ofReal D)
      ENNReal.ofReal_ne_top hgamma with
    ⟨delta₀, hdelta₀_pos, hdelta₀_one, hbound⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta_pos hdelta_le
  have hconstant :
      D ≤ Real.rpow delta (-gamma) := by
    have hbound' := hbound delta hdelta_pos hdelta_le
    rw [Kakeya.realRpowENN] at hbound'
    exact
      (ENNReal.ofReal_le_ofReal_iff
        (Real.rpow_nonneg hdelta_pos.le (-gamma))).mp hbound'
  calc
    D * Real.rpow delta alpha
        ≤ Real.rpow delta (-gamma) * Real.rpow delta alpha := by
          gcongr
          exact Real.rpow_nonneg hdelta_pos.le alpha
    _ = Real.rpow delta beta := by
      calc
        Real.rpow delta (-gamma) * Real.rpow delta alpha
            = Real.rpow delta ((-gamma) + alpha) :=
              (Real.rpow_add hdelta_pos _ _).symm
        _ = Real.rpow delta beta := by
          congr 1
          dsimp only [gamma]
          ring

/--
The concrete loss used after `frostman_to_tube_wolff`: for sufficiently small
`delta`, the fixed factor 24 can be absorbed by spending half of `eta`.
-/
lemma exists_delta_absorb_twenty_four
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        24 * Kakeya.realRpowENN delta (-(eta / 2)) ≤
          Kakeya.realRpowENN delta (-eta) := by
  rcases exists_delta_realRpowENN_bound (24 : ENNReal)
      (by norm_num) (show 0 < eta / 2 by positivity) with
    ⟨delta₀, hdelta₀_pos, hdelta₀_one, hbound⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta_pos hdelta_le
  have h24 :
      (24 : ENNReal) ≤
        Kakeya.realRpowENN delta (-(eta / 2)) :=
    hbound delta hdelta_pos hdelta_le
  have hmul :
      Kakeya.realRpowENN delta (-(eta / 2)) *
          Kakeya.realRpowENN delta (-(eta / 2)) =
        Kakeya.realRpowENN delta (-eta) := by
    simp only [Kakeya.realRpowENN]
    have hreal :
        Real.rpow delta (-(eta / 2)) *
            Real.rpow delta (-(eta / 2)) =
          Real.rpow delta (-eta) := by
      calc
        Real.rpow delta (-(eta / 2)) *
            Real.rpow delta (-(eta / 2))
            = Real.rpow delta (-(eta / 2) + -(eta / 2)) := by
              exact (Real.rpow_add hdelta_pos _ _).symm
        _ = Real.rpow delta (-eta) := by
              congr 1
              ring
    calc
      ENNReal.ofReal (Real.rpow delta (-(eta / 2))) *
          ENNReal.ofReal (Real.rpow delta (-(eta / 2)))
          = ENNReal.ofReal
              (Real.rpow delta (-(eta / 2)) *
                Real.rpow delta (-(eta / 2))) := by
            exact (ENNReal.ofReal_mul
              (Real.rpow_nonneg hdelta_pos.le (-(eta / 2)))).symm
      _ = ENNReal.ofReal (Real.rpow delta (-eta)) := by rw [hreal]
  calc
    24 * Kakeya.realRpowENN delta (-(eta / 2))
        ≤ Kakeya.realRpowENN delta (-(eta / 2)) *
            Kakeya.realRpowENN delta (-(eta / 2)) := by
          gcongr
    _ = Kakeya.realRpowENN delta (-eta) := hmul

/--
The power-form output of WZ Lemma 30 implies the direction-width bound used
in Step 4.  The fixed factor `20000` is absorbed by one additional
`delta^(-eta)` loss before taking the positive `sigma`-th root.
-/
lemma exists_delta_absorb_direction_power
    {sigma eta : ℝ} (hsigma : 0 < sigma) (heta : 0 < eta) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ x : ENNReal,
          x ^ sigma ≤
              20000 * Kakeya.realRpowENN delta (-2 * eta) →
            x ≤
              Kakeya.realRpowENN delta (-(3 * eta / sigma)) := by
  rcases exists_delta_realRpowENN_bound (20000 : ENNReal)
      (by norm_num) heta with
    ⟨delta₀, hdelta₀_pos, hdelta₀_one, hbound⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta_pos hdelta_le x hx
  have hconstant :
      (20000 : ENNReal) ≤
        Kakeya.realRpowENN delta (-eta) :=
    hbound delta hdelta_pos hdelta_le
  have hmul :
      Kakeya.realRpowENN delta (-eta) *
          Kakeya.realRpowENN delta (-2 * eta) =
        Kakeya.realRpowENN delta (-3 * eta) := by
    simp only [Kakeya.realRpowENN]
    have hreal :
        Real.rpow delta (-eta) *
            Real.rpow delta (-2 * eta) =
          Real.rpow delta (-3 * eta) := by
      calc
        Real.rpow delta (-eta) *
            Real.rpow delta (-2 * eta)
            = Real.rpow delta ((-eta) + (-2 * eta)) := by
              exact (Real.rpow_add hdelta_pos _ _).symm
        _ = Real.rpow delta (-3 * eta) := by
              congr 1
              ring
    calc
      ENNReal.ofReal (Real.rpow delta (-eta)) *
          ENNReal.ofReal (Real.rpow delta (-2 * eta))
          = ENNReal.ofReal
              (Real.rpow delta (-eta) *
                Real.rpow delta (-2 * eta)) := by
            exact (ENNReal.ofReal_mul
              (Real.rpow_nonneg hdelta_pos.le (-eta))).symm
      _ = ENNReal.ofReal (Real.rpow delta (-3 * eta)) := by
            rw [hreal]
  have hxpow :
      x ^ sigma ≤
        Kakeya.realRpowENN delta (-3 * eta) := by
    calc
      x ^ sigma
          ≤ 20000 *
              Kakeya.realRpowENN delta (-2 * eta) := hx
      _ ≤ Kakeya.realRpowENN delta (-eta) *
              Kakeya.realRpowENN delta (-2 * eta) := by
            gcongr
      _ = Kakeya.realRpowENN delta (-3 * eta) := hmul
  have hxroot :
      x ≤
        (Kakeya.realRpowENN delta (-3 * eta)) ^ sigma⁻¹ :=
    (ENNReal.le_rpow_inv_iff hsigma).2 hxpow
  have hroot :
      (Kakeya.realRpowENN delta (-3 * eta)) ^ sigma⁻¹ =
        Kakeya.realRpowENN delta (-(3 * eta / sigma)) := by
    simp only [Kakeya.realRpowENN]
    calc
      ENNReal.ofReal (Real.rpow delta (-3 * eta)) ^ sigma⁻¹
          = ENNReal.ofReal
              (Real.rpow (Real.rpow delta (-3 * eta)) sigma⁻¹) := by
            exact ENNReal.ofReal_rpow_of_nonneg
              (Real.rpow_nonneg hdelta_pos.le (-3 * eta))
              (inv_nonneg.mpr hsigma.le)
      _ = ENNReal.ofReal
            (Real.rpow delta ((-3 * eta) * sigma⁻¹)) := by
          exact congrArg ENNReal.ofReal
            (Real.rpow_mul hdelta_pos.le (-3 * eta) sigma⁻¹).symm
      _ = ENNReal.ofReal
            (Real.rpow delta (-(3 * eta / sigma))) := by
          congr 2
          field_simp [hsigma.ne']
  rw [hroot] at hxroot
  exact hxroot

/--
A squared logarithm is absorbed by any positive power of `δ`: for sufficiently
small `δ > 0`, `C * (log (1/δ))^2 ≤ δ^(-ε)`.

Uses `Real.log_le_rpow_div` with exponent `ε/4`, then squares and applies
`exists_delta_mul_rpow_le_rpow` to absorb the remaining constant.
-/
lemma exists_delta_log_sq_absorbed
    (C : ℝ) (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        C * (Real.log (1/δ))^2 ≤ Real.rpow δ (-ε) := by
  set α : ℝ := ε / 4 with hα_def
  have hα_pos : 0 < α := by positivity
  have hα_ne : α ≠ 0 := hα_pos.ne'
  have h2α : 2 * α = ε / 2 := by
    dsimp only [α]
    ring
  let D : ℝ := C * (1 / α)^2
  have hD_nonneg : 0 ≤ D := by
    dsimp only [D]
    positivity
  rcases exists_delta_mul_rpow_le_rpow D hD_nonneg
      (show (-ε : ℝ) < -(ε / 2) by linarith) with
    ⟨δ₀, hδ₀_pos, hδ₀_one, h_absorb⟩
  refine ⟨δ₀, hδ₀_pos, hδ₀_one, ?_⟩
  intro δ hδ_pos hδ_le
  have hδ_le_one : δ ≤ 1 := hδ_le.trans hδ₀_one
  have h_one_over_δ_ge_one : 1 ≤ 1 / δ := by
    have h : 1 / δ ≥ 1 := by
      apply one_le_one_div
      <;> linarith
    exact h
  have h_log_nonneg : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg h_one_over_δ_ge_one
  have h_rpow_pos : 0 < Real.rpow δ (-α) :=
    Real.rpow_pos_of_pos hδ_pos _
  have h1 : Real.log (1 / δ) ≤ (1 / α) * Real.rpow δ (-α) := by
    have h_log_div : Real.log (1 / δ) ≤ (1 / δ) ^ α / α :=
      Real.log_le_rpow_div (by positivity) hα_pos
    have h_rpow : (1 / δ) ^ α = Real.rpow δ (-α) := by
      have h : (1 / δ) ^ α = δ⁻¹ ^ α := by
        rw [show (1 / δ) = δ⁻¹ by field_simp]
      rw [h]
      exact (Real.rpow_neg_eq_inv_rpow δ α).symm
    rw [h_rpow] at h_log_div
    have h3 : (Real.rpow δ (-α)) / α = (1 / α) * Real.rpow δ (-α) := by
      ring
    rw [h3] at h_log_div
    exact h_log_div
  have h_rhs_pos : 0 ≤ (1 / α) * Real.rpow δ (-α) :=
    mul_nonneg (by positivity) h_rpow_pos.le
  have h2 : (Real.log (1 / δ))^2 ≤ ((1 / α) * Real.rpow δ (-α))^2 := by
    nlinarith
  have h3 : ((1 / α) * Real.rpow δ (-α))^2 = (1 / α)^2 * Real.rpow δ (-(2 * α)) := by
    have h4 : (Real.rpow δ (-α))^2 = Real.rpow δ (-(2 * α)) := by
      calc
        (Real.rpow δ (-α))^2
          = Real.rpow δ (-α) * Real.rpow δ (-α) := by ring
        _ = Real.rpow δ ((-α) + (-α)) :=
          (Real.rpow_add hδ_pos (-α) (-α)).symm
        _ = Real.rpow δ (-(2 * α)) := by
          have h : (-α) + (-α) = -(2 * α) := by linarith
          rw [h]
    calc
      ((1 / α) * Real.rpow δ (-α))^2
        = (1 / α)^2 * (Real.rpow δ (-α))^2 := by ring
      _ = (1 / α)^2 * Real.rpow δ (-(2 * α)) := by rw [h4]
  rw [h3] at h2
  have h4 : C * (Real.log (1 / δ))^2 ≤ D * Real.rpow δ (-(2 * α)) := by
    calc
      C * (Real.log (1 / δ))^2
        ≤ C * ((1 / α)^2 * Real.rpow δ (-(2 * α))) := by gcongr
      _ = D * Real.rpow δ (-(2 * α)) := by
        dsimp only [D] <;> ring
  rw [h2α] at h4
  exact h4.trans (h_absorb δ hδ_pos hδ_le)

end Kakeya.Assouad
