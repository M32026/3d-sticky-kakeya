import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFinalStatements
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Parameter tuning for the final WZ1 projection normalization

Elementary real and `ENNReal` power estimates used when the final affine
normalization chooses a localization radius comparable to `sqrt delta`.
-/

namespace Kakeya.Assouad

/-- If `0 < delta <= 1` and `a <= b`, then `delta^b <= delta^a`. -/
lemma wz1_real_rpow_antitone
    {delta a b : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hab : a ≤ b) :
    delta ^ b ≤ delta ^ a :=
  Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one hab

/-- For `0 < delta <= 1`, `delta <= sqrt delta`. -/
lemma wz1_delta_le_sqrt_delta
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    delta ≤ delta ^ (1 / 2 : ℝ) := by
  have h :=
    Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
      (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  simpa using h

/-- For `delta <= 1/256`, `4 * sqrt delta <= delta^(1/4)`. -/
lemma wz1_four_sqrt_delta_le_delta_quarter
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_small : delta ≤ 1 / 256) :
    4 * delta ^ (1 / 2 : ℝ) ≤ delta ^ (1 / 4 : ℝ) := by
  have hdelta_nonneg : 0 ≤ delta := hdelta.le
  have hquarter_pos : 0 < delta ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos hdelta _
  have hsq : (delta ^ (1 / 4 : ℝ)) ^ 2 = delta ^ (1 / 2 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hdelta]
    norm_num
  have hquarter_le : delta ^ (1 / 4 : ℝ) ≤ 1 / 4 := by
    have hpow : delta ≤ (1 / 4 : ℝ) ^ 4 := by
      norm_num at hdelta_small ⊢
      exact hdelta_small
    have h :=
      Real.rpow_le_rpow hdelta_nonneg hpow
        (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    have hright :
        ((1 / 4 : ℝ) ^ 4) ^ (1 / 4 : ℝ) = 1 / 4 := by
      have h1 :
          ((1 / 4 : ℝ) ^ 4) ^ (1 / 4 : ℝ) =
            (1 / 4 : ℝ) ^ ((4 : ℝ) * (1 / 4 : ℝ)) := by
        rw [Real.rpow_mul (by norm_num)]
        ring
      rw [h1]
      norm_num
    rwa [hright] at h
  rw [← hsq]
  nlinarith

/-- For `delta <= 1/10000`, `sqrt delta <= 1/100`. -/
lemma wz1_sqrt_delta_le_one_hundredth
    {delta : ℝ} (hdelta : 0 < delta)
    (hdelta_small : delta ≤ 1 / 10000) :
    delta ^ (1 / 2 : ℝ) ≤ 1 / 100 := by
  have h :=
    Real.rpow_le_rpow hdelta.le hdelta_small
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hright : (1 / 10000 : ℝ) ^ (1 / 2 : ℝ) = 1 / 100 := by
    rw [show (1 / 10000 : ℝ) = (1 / 100 : ℝ) ^ 2 by norm_num]
    have h1 :
        ((1 / 100 : ℝ) ^ 2) ^ (1 / 2 : ℝ) =
          (1 / 100 : ℝ) ^ ((2 : ℝ) * (1 / 2 : ℝ)) := by
      rw [Real.rpow_mul (by norm_num)]
      ring
    rw [h1]
    norm_num
  rwa [hright] at h

/-- For `0 < delta <= 1`, `sqrt delta <= 1`. -/
lemma wz1_sqrt_delta_le_one
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    delta ^ (1 / 2 : ℝ) ≤ 1 :=
  Real.rpow_le_one hdelta.le hdelta_one (by norm_num)

/-- `ENNReal` form of the quarter-power estimate. -/
lemma wz1_four_sqrt_delta_le_delta_quarter_ennreal
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_small : delta ≤ 1 / 256) :
    4 * Kakeya.realRpowENN delta (1 / 2 : ℝ) ≤
      Kakeya.realRpowENN delta (1 / 4 : ℝ) := by
  have h :=
    wz1_four_sqrt_delta_le_delta_quarter hdelta hdelta_small
  have hleft :
      (4 : ENNReal) * Kakeya.realRpowENN delta (1 / 2 : ℝ) =
        ENNReal.ofReal (4 * delta ^ (1 / 2 : ℝ)) := by
    rw [Kakeya.realRpowENN]
    calc
      (4 : ENNReal) * ENNReal.ofReal (delta ^ (1 / 2 : ℝ)) =
          ENNReal.ofReal (4 : ℝ) *
            ENNReal.ofReal (delta ^ (1 / 2 : ℝ)) := by norm_num
      _ = ENNReal.ofReal (4 * delta ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
  rw [hleft, Kakeya.realRpowENN]
  exact ENNReal.ofReal_le_ofReal h

/--
For `0 < eta < 1/2` and sufficiently small `delta`,
`4 * sqrt delta <= delta^eta`.
-/
lemma wz1_four_sqrt_delta_le_delta_eta
    {delta eta : ℝ} (hdelta : 0 < delta) (heta : 0 < eta)
    (heta_half : eta < 1 / 2)
    (hdelta_small : delta ≤ (1 / 4) ^ (1 / (1 / 2 - eta))) :
    4 * delta ^ (1 / 2 : ℝ) ≤ delta ^ eta := by
  let exponent : ℝ := 1 / 2 - eta
  have hexponent : 0 < exponent := by
    dsimp [exponent]
    linarith
  have hpow : delta ^ exponent ≤ (1 / 4 : ℝ) := by
    have hdelta_small' :
        delta ≤ (1 / 4 : ℝ) ^ (1 / exponent) := by
      simpa [exponent] using hdelta_small
    have h :=
      Real.rpow_le_rpow hdelta.le hdelta_small' hexponent.le
    have hright :
        ((1 / 4 : ℝ) ^ (1 / exponent)) ^ exponent = 1 / 4 := by
      have h1 :
          ((1 / 4 : ℝ) ^ (1 / exponent)) ^ exponent =
            (1 / 4 : ℝ) ^ ((1 / exponent) * exponent) := by
        rw [Real.rpow_mul (by norm_num)]
      have : (1 / exponent) * exponent = 1 := by
        field_simp [hexponent.ne']
      rw [h1, this]
      norm_num
    rwa [hright] at h
  have hmul :
      delta ^ exponent * delta ^ eta ≤ (1 / 4 : ℝ) * delta ^ eta := by
    gcongr
  have hexponent_add : exponent + eta = 1 / 2 := by
    dsimp [exponent]
    ring
  rw [← Real.rpow_add hdelta, hexponent_add] at hmul
  nlinarith [Real.rpow_pos_of_pos hdelta eta]

/-- `ENNReal` form of the general small-scale estimate. -/
lemma wz1_four_sqrt_delta_le_delta_eta_ennreal
    {delta eta : ℝ} (hdelta : 0 < delta) (heta : 0 < eta)
    (heta_half : eta < 1 / 2)
    (hdelta_small : delta ≤ (1 / 4) ^ (1 / (1 / 2 - eta))) :
    4 * Kakeya.realRpowENN delta (1 / 2 : ℝ) ≤
      Kakeya.realRpowENN delta eta := by
  have h :=
    wz1_four_sqrt_delta_le_delta_eta
      hdelta heta heta_half hdelta_small
  have hleft :
      (4 : ENNReal) * Kakeya.realRpowENN delta (1 / 2 : ℝ) =
        ENNReal.ofReal (4 * delta ^ (1 / 2 : ℝ)) := by
    rw [Kakeya.realRpowENN]
    calc
      (4 : ENNReal) * ENNReal.ofReal (delta ^ (1 / 2 : ℝ)) =
          ENNReal.ofReal (4 : ℝ) *
            ENNReal.ofReal (delta ^ (1 / 2 : ℝ)) := by norm_num
      _ = ENNReal.ofReal (4 * delta ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
  rw [hleft, Kakeya.realRpowENN]
  exact ENNReal.ofReal_le_ofReal h

/-- Frostman control is monotone in its constant. -/
lemma DiscreteSet.IsFrostman.mono
    {n : ℕ} {A : DiscreteSet n} {delta s : ℝ} {C C' : ENNReal}
    (h : A.IsFrostman delta s C) (hC : C ≤ C') :
    A.IsFrostman delta s C' := by
  intro x r hr1 hr2
  exact (h x r hr1 hr2).trans (by gcongr)

/-- Uniform triple density is monotone when the density constant decreases. -/
lemma WZ1UniformTripleDensity.mono
    {c c' : ENNReal} {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (h : WZ1UniformTripleDensity c F G₁ G₂ H) (hc : c' ≤ c) :
    WZ1UniformTripleDensity c' F G₁ G₂ H := by
  rcases h with ⟨h_nonempty, h_support, h_density⟩
  refine ⟨h_nonempty, h_support, ?_⟩
  intro edge hedge I
  exact
    (mul_le_mul_right'
      hc
      (wz1VertexCardProduct
        (wz1TripleVertexClasses F G₁ G₂) (Finset.univ \ I))).trans
      (h_density edge hedge I)

end Kakeya.Assouad
