import MyLeanRepo.Kakeya.Assouad.WZ1.DiscreteThinTubes

/-!
# Exponent arithmetic for the OSW thin-tube iteration

This module contains the closed monotonicity and Archimedean steps used after
the one-step OSW iteration.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/--
Choose the first step of an arithmetic progression that reaches `target`.
-/
lemma exists_first_osw_step
    {sigma target tau : ℝ}
    (htau : 0 < tau) (hst : sigma < target) :
    ∃ N : ℕ,
      0 < N ∧
      target ≤ sigma + (N : ℝ) * tau ∧
      sigma + (N : ℝ) * tau < target + tau ∧
      ∀ n : ℕ, n < N → sigma + (n : ℝ) * tau < target := by
  let q : ℝ := (target - sigma) / tau
  let N : ℕ := Nat.ceil q
  have hq_pos : 0 < q := by
    dsimp only [q]
    positivity
  have hN_pos : 0 < N := by
    dsimp only [N]
    exact Nat.ceil_pos.mpr hq_pos
  have hq_le : q ≤ (N : ℝ) := by
    dsimp only [N]
    exact Nat.le_ceil q
  have hN_lt : (N : ℝ) < q + 1 := by
    dsimp only [N]
    exact Nat.ceil_lt_add_one hq_pos.le
  have hreach : target ≤ sigma + (N : ℝ) * tau := by
    have hmul : target - sigma ≤ (N : ℝ) * tau := by
      calc
        target - sigma = q * tau := by
          dsimp only [q]
          field_simp [htau.ne']
        _ ≤ (N : ℝ) * tau := by gcongr
    linarith
  have hovershoot : sigma + (N : ℝ) * tau < target + tau := by
    have hmul : (N : ℝ) * tau < (q + 1) * tau := by
      gcongr
    have hq : q * tau = target - sigma := by
      dsimp only [q]
      field_simp [htau.ne']
    rw [add_mul, hq, one_mul] at hmul
    linarith
  refine ⟨N, hN_pos, hreach, hovershoot, ?_⟩
  intro n hn
  have hn_le : n + 1 ≤ N := Nat.succ_le_iff.mpr hn
  have hn_cast : (n : ℝ) < (N : ℝ) := by exact_mod_cast hn
  have hmul : (n : ℝ) * tau < (N : ℝ) * tau := by gcongr
  have hstrict : sigma + (n : ℝ) * tau <
      sigma + (N : ℝ) * tau := by linarith
  by_contra hnot
  have htarget : target ≤ sigma + (n : ℝ) * tau := le_of_not_gt hnot
  have hq_n : q ≤ (n : ℝ) := by
    dsimp only [q]
    apply (div_le_iff₀ htau).mpr
    linarith
  have hceil_le : N ≤ n := by
    dsimp only [N]
    exact Nat.ceil_le.mpr hq_n
  omega

/--
Lowering the thin-tube exponent preserves a measure thin-tube estimate.

For radii at most one this is monotonicity of real powers.  For larger radii
the probability bound by one and `K ≥ 1` give the result.
-/
lemma HasMeasureThinTubes.mono_exponent
    {beta beta' K c : ℝ}
    {nu₁ nu₂ : ProbabilityMeasure Point2}
    (h : HasMeasureThinTubes beta K c nu₁ nu₂)
    (hbeta' : 0 ≤ beta') (hle : beta' ≤ beta) :
    HasMeasureThinTubes beta' K c nu₁ nu₂ := by
  rcases h with
    ⟨hbeta, hK, hc, E, hEmeas, hEsub, hEmass, htubes⟩
  refine ⟨hbeta', hK, hc, E, hEmeas, hEsub, hEmass, ?_⟩
  intro b₁ hb₁ line hb₁line hfin r hr
  have hold := htubes b₁ hb₁ line hb₁line hfin r hr
  by_cases hr_one : r ≤ 1
  · have hpow : r ^ beta ≤ r ^ beta' :=
      Real.rpow_le_rpow_of_exponent_ge hr hr_one hle
    have hreal : K * r ^ beta ≤ K * r ^ beta' :=
      mul_le_mul_of_nonneg_left hpow (by linarith [hK])
    exact hold.trans (Real.toNNReal_mono hreal)
  · have hr_ge : 1 ≤ r := by linarith
    have hpow : 1 ≤ r ^ beta' :=
      Real.one_le_rpow hr_ge hbeta'
    have hreal : 1 ≤ K * r ^ beta' := by
      nlinarith [hK]
    have hone : (1 : NNReal) ≤ Real.toNNReal (K * r ^ beta') :=
      Real.one_le_toNNReal.mpr hreal
    have hprob : nu₂
        {b₂ |
          b₂ ∈ Metric.thickening r (line : Set Point2) ∧
          (b₁, b₂) ∈ E} ≤ 1 := by
      have hmeasure :
          (nu₂ : Measure Point2)
              {b₂ |
                b₂ ∈ Metric.thickening r (line : Set Point2) ∧
                (b₁, b₂) ∈ E} ≤
            (nu₂ : Measure Point2) Set.univ :=
        measure_mono (Set.subset_univ _)
      simpa using hmeasure
    exact hprob.trans hone

/--
At scales `r ≥ delta`, a `(1-epsilon)` discrete thin-tube estimate becomes
an exponent-one estimate after paying `delta^{-epsilon}`.
-/
lemma HasDiscreteThinTubes.to_exponent_one
    {delta beta K c epsilon : ℝ}
    {G₁ G₂ : DiscreteSet 2}
    (h : HasDiscreteThinTubes delta beta K c G₁ G₂)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hepsilon : 0 ≤ epsilon)
    (hbeta_lower : 1 - epsilon ≤ beta)
    (hbeta_upper : beta ≤ 1) :
    HasDiscreteThinTubes delta 1
      (K * delta ^ (-epsilon)) c G₁ G₂ := by
  rcases h with ⟨hbeta, hK, hc, E, hEsub, hEmass, htubes⟩
  have hdelta_factor : 1 ≤ delta ^ (-epsilon) := by
    have hdelta_pos : 0 < delta := hdelta
    have hdelta_inv : 1 ≤ delta⁻¹ := by
      rw [one_le_inv₀ hdelta]
      exact hdelta_one
    have hpow : delta ^ (-epsilon) = (delta⁻¹) ^ epsilon := by
      calc
        delta ^ (-epsilon) = (delta ^ epsilon)⁻¹ :=
          Real.rpow_neg hdelta.le epsilon
        _ = (delta⁻¹) ^ epsilon :=
          (Real.inv_rpow hdelta.le epsilon).symm
    rw [hpow]
    exact Real.one_le_rpow hdelta_inv hepsilon
  have hK' : 1 ≤ K * delta ^ (-epsilon) := by
    nlinarith [hK]
  refine ⟨by norm_num, hK', hc, E, hEsub, hEmass, ?_⟩
  intro b₁ hb₁ line hb₁line hfin r hdr
  have hold := htubes b₁ hb₁ line hb₁line hfin r hdr
  have hr_pos : 0 < r := hdelta.trans_le hdr
  by_cases hr_one : r ≤ 1
  · have hpow_beta : r ^ beta ≤ r ^ (1 - epsilon) :=
      Real.rpow_le_rpow_of_exponent_ge hr_pos hr_one hbeta_lower
    have hratio : r ^ (1 - epsilon) =
        r * r ^ (-epsilon) := by
      calc
        r ^ (1 - epsilon) = r ^ (1 + (-epsilon)) := by ring_nf
        _ = r ^ (1 : ℝ) * r ^ (-epsilon) :=
          Real.rpow_add hr_pos 1 (-epsilon)
        _ = r * r ^ (-epsilon) := by rw [Real.rpow_one]
    have hpow_neg : r ^ (-epsilon) ≤ delta ^ (-epsilon) := by
      have hinv : r⁻¹ ≤ delta⁻¹ :=
        (inv_le_inv₀ hr_pos hdelta).mpr hdr
      have hp : (r⁻¹) ^ epsilon ≤ (delta⁻¹) ^ epsilon :=
        Real.rpow_le_rpow (by positivity) hinv hepsilon
      have hrw : r ^ (-epsilon) = (r⁻¹) ^ epsilon := by
        calc
          r ^ (-epsilon) = (r ^ epsilon)⁻¹ :=
            Real.rpow_neg hr_pos.le epsilon
          _ = (r⁻¹) ^ epsilon :=
            (Real.inv_rpow hr_pos.le epsilon).symm
      have hdelta_rw :
          delta ^ (-epsilon) = (delta⁻¹) ^ epsilon := by
        calc
          delta ^ (-epsilon) = (delta ^ epsilon)⁻¹ :=
            Real.rpow_neg hdelta.le epsilon
          _ = (delta⁻¹) ^ epsilon :=
            (Real.inv_rpow hdelta.le epsilon).symm
      rwa [hrw, hdelta_rw]
    have hreal :
        K * r ^ beta ≤
          (K * delta ^ (-epsilon)) * r ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      calc
        K * r ^ beta ≤ K * r ^ (1 - epsilon) :=
          mul_le_mul_of_nonneg_left hpow_beta (by linarith [hK])
        _ = K * (r * r ^ (-epsilon)) := by rw [hratio]
        _ ≤ K * (r * delta ^ (-epsilon)) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left hpow_neg hr_pos.le
          · linarith [hK]
        _ = (K * delta ^ (-epsilon)) * r := by ring
    exact hold.trans
      (mul_le_mul_right'
        (ENNReal.ofReal_le_ofReal hreal) _)
  · have hr_ge : 1 ≤ r := by linarith
    have hpow_beta : r ^ beta ≤ r ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hr_ge hbeta_upper
    have hreal :
        K * r ^ beta ≤
          (K * delta ^ (-epsilon)) * r ^ (1 : ℝ) := by
      calc
        K * r ^ beta ≤ K * r ^ (1 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow_beta (by linarith [hK])
        _ ≤ (K * delta ^ (-epsilon)) * r ^ (1 : ℝ) := by
          apply mul_le_mul_of_nonneg_right
          · calc
              K = K * 1 := by ring
              _ ≤ K * delta ^ (-epsilon) :=
                mul_le_mul_of_nonneg_left hdelta_factor
                  (by linarith [hK])
          · positivity
    exact hold.trans
      (mul_le_mul_right'
        (ENNReal.ofReal_le_ofReal hreal) _)

end Kakeya.Assouad
