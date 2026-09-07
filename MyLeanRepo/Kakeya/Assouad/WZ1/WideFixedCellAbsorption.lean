import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9WideSplitStatements
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Absorption arithmetic for WZ1 wide fixed cell selection

Packages the small-scale absorption bounds needed when transferring Frostman
and line-nonconcentration from coarse classes to fixed-cell active projections.

Given a fixed constant `K` (cell-triple count times refinement loss), the
exponent gaps between coarse margin exponents and output margin exponents are:

- Frostman: `λ/2 → 3λ/4`, gap `λ/4`
- Line nonconc: `λζ/2 → 3λζ/4`, gap `λζ/4`
- Density weakening: need `δ^η / K ≥ scale^α`

All are absorbed simultaneously for sufficiently small `δ`, using
`scale < δ^(ε/10)` and `α ≤ ζλ/16`.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
All absorption conditions can be satisfied simultaneously by choosing
`etaCap` and `delta₀` small enough.

Given `alpha > 0`, `lambda > 0`, `zeta > 0`, `epsilon ∈ (0,1)`,
`alpha ≤ zeta * lambda / 16`, and a fixed constant `K`,
there exists `etaCap > 0` such that for every `0 < eta ≤ etaCap`,
there exists `delta₀ > 0` such that for all `0 < delta ≤ delta₀`
and all `0 < scale < delta^(epsilon/10)`:

1. `K * δ^(-η) ≤ scale^(-λ/4)`          (Frostman absorption)
2. `K * δ^(-η) ≤ scale^(-λζ/4)`         (line nonconc absorption)
3. `scale^α ≤ δ^η / K`                  (density weakening)
4. `scale ≤ 1/20`                       (quantitative separation)
-/
lemma wide_fixed_cell_absorption
    {alpha lambda zeta epsilon : ℝ}
    (halpha_pos : 0 < alpha)
    (hlambda_pos : 0 < lambda)
    (hzeta_pos : 0 < zeta)
    (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (halpha_le : alpha ≤ zeta * lambda / 16)
    {K : ENNReal} (hK_ne_top : K ≠ ⊤) :
    ∃ etaCap : ℝ, 0 < etaCap ∧
      ∀ (eta : ℝ), 0 < eta → eta ≤ etaCap →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
          ∀ (scale : ℝ), 0 < scale →
          scale < Real.rpow delta (epsilon / 10) →
          (K * Kakeya.realRpowENN delta (-eta) ≤
             Kakeya.realRpowENN scale (-(lambda / 4))) ∧
          (K * Kakeya.realRpowENN delta (-eta) ≤
             Kakeya.realRpowENN scale (-(lambda * zeta / 4))) ∧
          (Kakeya.realRpowENN scale alpha ≤
             Kakeya.realRpowENN delta eta / K) ∧
          (scale ≤ 1 / 20) := by
  let etaCap := min (alpha * epsilon / 20)
                  (min (epsilon * lambda * zeta / 80)
                       (lambda * epsilon / 80))
  have hetaCap_pos : 0 < etaCap := by positivity
  have h1 : etaCap < alpha * epsilon / 10 := by
    dsimp only [etaCap]
    have h : alpha * epsilon / 20 < alpha * epsilon / 10 := by gcongr <;> linarith
    exact (min_le_left _ _).trans_lt h
  have h2 : etaCap < epsilon * lambda * zeta / 40 := by
    dsimp only [etaCap]
    have h : epsilon * lambda * zeta / 80 < epsilon * lambda * zeta / 40 := by gcongr <;> linarith
    exact (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt h)
  have h3 : etaCap < lambda * epsilon / 40 := by
    dsimp only [etaCap]
    have h : lambda * epsilon / 80 < lambda * epsilon / 40 := by gcongr <;> linarith
    exact (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt h)
  refine ⟨etaCap, hetaCap_pos, fun eta heta_pos heta_le => ?_⟩
  set gammaD := alpha * epsilon / 10 - eta with hgammaD_def
  set gammaL := epsilon * lambda * zeta / 40 - eta with hgammaL_def
  set gammaF := lambda * epsilon / 40 - eta with hgammaF_def
  have hgD_pos : 0 < gammaD := by
    rw [hgammaD_def]
    linarith [heta_le.trans_lt h1]
  have hgL_pos : 0 < gammaL := by
    rw [hgammaL_def]
    linarith [heta_le.trans_lt h2]
  have hgF_pos : 0 < gammaF := by
    rw [hgammaF_def]
    linarith [heta_le.trans_lt h3]
  rcases exists_delta_realRpowENN_bound K hK_ne_top hgD_pos with
    ⟨dD, hdD_pos, hdD_one, hbD⟩
  rcases exists_delta_realRpowENN_bound K hK_ne_top hgL_pos with
    ⟨dL, hdL_pos, hdL_one, hbL⟩
  rcases exists_delta_realRpowENN_bound K hK_ne_top hgF_pos with
    ⟨dF, hdF_pos, hdF_one, hbF⟩
  let dS : ℝ := Real.rpow (1 / 20 : ℝ) (10 / epsilon)
  have hdS_pos : 0 < dS := Real.rpow_pos_of_pos (by norm_num) _
  have hdS_one : dS ≤ 1 := by
    have h1 : (0 : ℝ) ≤ (1 / 20 : ℝ) := by norm_num
    have h2 : (1 / 20 : ℝ) ≤ 1 := by norm_num
    have h3 : 0 ≤ 10 / epsilon := by positivity
    exact Real.rpow_le_one h1 h2 h3
  let delta₀ := min dD (min dL (min dF dS))
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_one : delta₀ ≤ 1 := (min_le_left _ _).trans hdD_one
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, fun delta hdelta hdelta_le scale hscale_pos hscale_lt => ?_⟩
  have hdD_le : delta ≤ dD := hdelta_le.trans (min_le_left _ _)
  have hdL_le : delta ≤ dL :=
    hdelta_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdF_le : delta ≤ dF :=
    hdelta_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdS_le : delta ≤ dS :=
    hdelta_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hK_D : K ≤ Kakeya.realRpowENN delta (-gammaD) := hbD delta hdelta hdD_le
  have hK_L : K ≤ Kakeya.realRpowENN delta (-gammaL) := hbL delta hdelta hdL_le
  have hK_F : K ≤ Kakeya.realRpowENN delta (-gammaF) := hbF delta hdelta hdF_le
  -- Helper: K * δ^(-η) ≤ δ^(-γ) * δ^(-η) = δ^(-(γ + η))
  have h_sum_D : (-gammaD) + (-eta) = -(alpha * epsilon / 10) := by
    rw [hgammaD_def] <;> ring
  have h_sum_L : (-gammaL) + (-eta) = -(epsilon * lambda * zeta / 40) := by
    rw [hgammaL_def] <;> ring
  have h_sum_F : (-gammaF) + (-eta) = -(lambda * epsilon / 40) := by
    rw [hgammaF_def] <;> ring
  have h_mul_D : K * Kakeya.realRpowENN delta (-eta) ≤
      Kakeya.realRpowENN delta (-(alpha * epsilon / 10)) := by
    have h : K * Kakeya.realRpowENN delta (-eta) ≤
        Kakeya.realRpowENN delta (-gammaD) * Kakeya.realRpowENN delta (-eta) := by
      gcongr
    have h2 : Kakeya.realRpowENN delta (-gammaD) * Kakeya.realRpowENN delta (-eta) =
        Kakeya.realRpowENN delta ((-gammaD) + (-eta)) := by
      rw [← realRpowENN_add hdelta (-gammaD) (-eta)]
    rw [h2, h_sum_D] at h
    exact h
  have h_mul_L : K * Kakeya.realRpowENN delta (-eta) ≤
      Kakeya.realRpowENN delta (-(epsilon * lambda * zeta / 40)) := by
    have h : K * Kakeya.realRpowENN delta (-eta) ≤
        Kakeya.realRpowENN delta (-gammaL) * Kakeya.realRpowENN delta (-eta) := by gcongr
    have h2 : Kakeya.realRpowENN delta (-gammaL) * Kakeya.realRpowENN delta (-eta) =
        Kakeya.realRpowENN delta ((-gammaL) + (-eta)) := by
      rw [← realRpowENN_add hdelta (-gammaL) (-eta)]
    rw [h2, h_sum_L] at h
    exact h
  have h_mul_F : K * Kakeya.realRpowENN delta (-eta) ≤
      Kakeya.realRpowENN delta (-(lambda * epsilon / 40)) := by
    have h : K * Kakeya.realRpowENN delta (-eta) ≤
        Kakeya.realRpowENN delta (-gammaF) * Kakeya.realRpowENN delta (-eta) := by gcongr
    have h2 : Kakeya.realRpowENN delta (-gammaF) * Kakeya.realRpowENN delta (-eta) =
        Kakeya.realRpowENN delta ((-gammaF) + (-eta)) := by
      rw [← realRpowENN_add hdelta (-gammaF) (-eta)]
    rw [h2, h_sum_F] at h
    exact h
  -- Scale comparisons at real level
  set r := Real.rpow delta (epsilon / 10) with hr_def
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hdelta _
  have hscale_lt_r : scale < r := hscale_lt
  have hexp_F_neg : -(lambda / 4) < 0 := by linarith
  have hexp_L_neg : -(lambda * zeta / 4) < 0 := by linarith [hlambda_pos, hzeta_pos]
  have hexp_D_pos : 0 < alpha := halpha_pos
  have hreal_F : Real.rpow scale (-(lambda / 4)) ≥ Real.rpow r (-(lambda / 4)) :=
    Real.rpow_le_rpow_of_nonpos hscale_pos hscale_lt_r.le hexp_F_neg.le
  have hreal_L : Real.rpow scale (-(lambda * zeta / 4)) ≥ Real.rpow r (-(lambda * zeta / 4)) :=
    Real.rpow_le_rpow_of_nonpos hscale_pos hscale_lt_r.le hexp_L_neg.le
  have hreal_D : Real.rpow scale alpha ≤ Real.rpow r alpha :=
    Real.rpow_le_rpow hscale_pos.le hscale_lt_r.le hexp_D_pos.le
  have hcomp_F : Real.rpow r (-(lambda / 4)) = Real.rpow delta (-(lambda * epsilon / 40)) := by
    have hmul : (delta ^ (epsilon / 10)) ^ (-(lambda / 4)) = delta ^ ((epsilon / 10) * (-(lambda / 4))) :=
      (Real.rpow_mul hdelta.le (epsilon / 10) (-(lambda / 4))).symm
    have hprod : (epsilon / 10) * (-(lambda / 4)) = -(lambda * epsilon / 40) := by ring
    simpa [hr_def, hprod] using hmul
  have hcomp_L : Real.rpow r (-(lambda * zeta / 4)) =
      Real.rpow delta (-(epsilon * lambda * zeta / 40)) := by
    have hmul : (delta ^ (epsilon / 10)) ^ (-(lambda * zeta / 4)) =
        delta ^ ((epsilon / 10) * (-(lambda * zeta / 4))) :=
      (Real.rpow_mul hdelta.le (epsilon / 10) (-(lambda * zeta / 4))).symm
    have hprod : (epsilon / 10) * (-(lambda * zeta / 4)) = -(epsilon * lambda * zeta / 40) := by ring
    simpa [hr_def, hprod] using hmul
  have hcomp_D : Real.rpow r alpha = Real.rpow delta (alpha * epsilon / 10) := by
    have hmul : (delta ^ (epsilon / 10)) ^ alpha = delta ^ ((epsilon / 10) * alpha) :=
      (Real.rpow_mul hdelta.le (epsilon / 10) alpha).symm
    have hprod : (epsilon / 10) * alpha = alpha * epsilon / 10 := by ring
    simpa [hr_def, hprod] using hmul
  have hreal_F' : Real.rpow scale (-(lambda / 4)) ≥ Real.rpow delta (-(lambda * epsilon / 40)) := by
    calc Real.rpow scale (-(lambda / 4))
      ≥ Real.rpow r (-(lambda / 4)) := hreal_F
    _ = Real.rpow delta (-(lambda * epsilon / 40)) := hcomp_F
  have hscale_F : Kakeya.realRpowENN scale (-(lambda / 4)) ≥
      Kakeya.realRpowENN delta (-(lambda * epsilon / 40)) := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_mono hreal_F'
  have hreal_L' : Real.rpow scale (-(lambda * zeta / 4)) ≥
      Real.rpow delta (-(epsilon * lambda * zeta / 40)) := by
    calc Real.rpow scale (-(lambda * zeta / 4))
      ≥ Real.rpow r (-(lambda * zeta / 4)) := hreal_L
    _ = Real.rpow delta (-(epsilon * lambda * zeta / 40)) := hcomp_L
  have hscale_L : Kakeya.realRpowENN scale (-(lambda * zeta / 4)) ≥
      Kakeya.realRpowENN delta (-(epsilon * lambda * zeta / 40)) := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_mono hreal_L'
  have hreal_D' : Real.rpow scale alpha ≤ Real.rpow delta (alpha * epsilon / 10) := by
    calc Real.rpow scale alpha
      ≤ Real.rpow r alpha := hreal_D
    _ = Real.rpow delta (alpha * epsilon / 10) := hcomp_D
  have hscale_D : Kakeya.realRpowENN scale alpha ≤
      Kakeya.realRpowENN delta (alpha * epsilon / 10) := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_mono hreal_D'
  -- Density weakening: δ^η / K ≥ scale^α
  have hK_inv : K⁻¹ ≥ Kakeya.realRpowENN delta gammaD := by
    have h4 : K ≤ Kakeya.realRpowENN delta (-gammaD) := hK_D
    have h_rpow_pos : 0 < Real.rpow delta gammaD := Real.rpow_pos_of_pos hdelta _
    have h5 : (Kakeya.realRpowENN delta (-gammaD))⁻¹ = Kakeya.realRpowENN delta gammaD := by
      have h_neg : Real.rpow delta (-gammaD) = (Real.rpow delta gammaD)⁻¹ :=
        Real.rpow_neg hdelta.le gammaD
      simp only [Kakeya.realRpowENN]
      rw [h_neg]
      have h6 : ENNReal.ofReal ((Real.rpow delta gammaD)⁻¹) =
          (ENNReal.ofReal (Real.rpow delta gammaD))⁻¹ :=
        ENNReal.ofReal_inv_of_pos h_rpow_pos
      rw [h6]
      have h7 : ((ENNReal.ofReal (Real.rpow delta gammaD))⁻¹)⁻¹ =
          ENNReal.ofReal (Real.rpow delta gammaD) := by
        simp
      exact h7
    have h6 : K⁻¹ ≥ (Kakeya.realRpowENN delta (-gammaD))⁻¹ := by gcongr
    rw [h5] at h6
    exact h6
  have h_sum_eta_D : eta + gammaD = alpha * epsilon / 10 := by
    rw [hgammaD_def] <;> ring
  have hdiv : Kakeya.realRpowENN delta eta / K ≥
      Kakeya.realRpowENN delta (alpha * epsilon / 10) := by
    have h7 : Kakeya.realRpowENN delta eta / K =
        Kakeya.realRpowENN delta eta * K⁻¹ := by
      simp [div_eq_mul_inv]
    rw [h7]
    have h8 : Kakeya.realRpowENN delta eta * K⁻¹ ≥
        Kakeya.realRpowENN delta eta * Kakeya.realRpowENN delta gammaD := by gcongr
    have h9 : Kakeya.realRpowENN delta eta * Kakeya.realRpowENN delta gammaD =
        Kakeya.realRpowENN delta (eta + gammaD) := by
      rw [← realRpowENN_add hdelta eta gammaD]
    rw [h9, h_sum_eta_D] at h8
    exact h8
  -- Scale ≤ 1/20
  have hds_pow : Real.rpow dS (epsilon / 10) = 1 / 20 := by
    dsimp only [dS]
    have h10 : (10 / epsilon) * (epsilon / 10) = 1 := by
      field_simp [hepsilon_pos.ne'] <;> ring
    have h_pos : (0 : ℝ) ≤ (1 / 20 : ℝ) := by norm_num
    have h : Real.rpow (Real.rpow (1 / 20 : ℝ) (10 / epsilon)) (epsilon / 10) =
        Real.rpow (1 / 20 : ℝ) ((10 / epsilon) * (epsilon / 10)) := by
      exact (Real.rpow_mul h_pos (10 / epsilon) (epsilon / 10)).symm
    rw [h, h10]
    <;> simp
  have hdelta_pow : Real.rpow delta (epsilon / 10) ≤ Real.rpow dS (epsilon / 10) :=
    Real.rpow_le_rpow hdelta.le hdS_le (by linarith)
  have h_scale20 : scale ≤ 1 / 20 := by
    have h : scale < Real.rpow delta (epsilon / 10) := hscale_lt
    rw [hds_pow] at hdelta_pow
    linarith
  constructor
  · calc K * Kakeya.realRpowENN delta (-eta)
        ≤ Kakeya.realRpowENN delta (-(lambda * epsilon / 40)) := h_mul_F
      _ ≤ Kakeya.realRpowENN scale (-(lambda / 4)) := hscale_F
  · constructor
    · calc K * Kakeya.realRpowENN delta (-eta)
          ≤ Kakeya.realRpowENN delta (-(epsilon * lambda * zeta / 40)) := h_mul_L
        _ ≤ Kakeya.realRpowENN scale (-(lambda * zeta / 4)) := hscale_L
    · constructor
      · calc Kakeya.realRpowENN scale alpha
            ≤ Kakeya.realRpowENN delta (alpha * epsilon / 10) := hscale_D
          _ ≤ Kakeya.realRpowENN delta eta / K := hdiv
      · exact h_scale20

end Kakeya.Assouad
