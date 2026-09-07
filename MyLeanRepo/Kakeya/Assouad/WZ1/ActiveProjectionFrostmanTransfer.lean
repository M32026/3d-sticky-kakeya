import MyLeanRepo.Kakeya.Assouad.WZ1.InducedTripleRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremLocalizationStatements

/-!
# Active-projection Frostman transfer and retention bounds

This module supports the three sequential rescaling rounds in PDF
Proposition 8.9 (wide branch).

## Main results

* `active_projection_frostman_transfer`: a uniformly dense active coordinate
  projection inherits Frostman control from its ambient vertex class, with a
  multiplicative loss equal to the reciprocal of the density constant.
* `wideSequentialFrostmanRetentionBound`: the worst-case (round-3) retention
  bound `65536 * δ^(-workingLambda-eta) ≤ δ^(-2*workingLambda)` for small
  enough `δ`.  Rounds 1 and 2 follow by monotonicity of the constant.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
An active coordinate projection of a uniformly dense tripartite graph inherits
Frostman control from the corresponding ambient vertex class.

The loss is exactly `C / c`, where `c` is the uniform triple-density constant.
This follows because the active projection contains at least a `c`-fraction of
the ambient class (`active_triple_projection_card_lower`).
-/
lemma active_projection_frostman_transfer
    {c : ENNReal}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {delta : ℝ} {C : ENNReal}
    (i : Fin 3)
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (hG_frostman : (wz1TripleVertexClasses F G₁ G₂ i).IsFrostman delta 1 C)
    (hc_pos : c ≠ 0) :
    (wz1ActiveTripleProjection H i).IsFrostman delta 1 (C / c) := by
  let A := wz1ActiveTripleProjection H i
  let ambient := wz1TripleVertexClasses F G₁ G₂ i
  have hsub : A ⊆ ambient := active_triple_projection_subset hDensity i
  have hcard : c * ambient.enncard ≤ A.enncard :=
    active_triple_projection_card_lower hDensity i
  intro x r hr1 hr2
  have h1 : A.ballCount x r ≤ ambient.ballCount x r := by
    simpa [DiscreteSet.ballCount] using
      Finset.card_le_card (Finset.filter_subset_filter _ hsub)
  have h2 : ambient.ballCount x r ≤ C * Kakeya.realRpowENN r 1 * ambient.enncard :=
    hG_frostman x r hr1 hr2
  have hA_finite : A.enncard ≠ ⊤ := by
    simp [DiscreteSet.enncard]
  have h4 : c * ambient.enncard ≤ A.enncard := hcard
  have h4' : ambient.enncard * c ≤ A.enncard := by
    have h_comm : c * ambient.enncard = ambient.enncard * c := mul_comm c ambient.enncard
    rw [h_comm] at h4
    exact h4
  have h3 : ambient.enncard ≤ A.enncard / c := by
    exact (ENNReal.le_div_iff_mul_le (Or.inl hc_pos) (Or.inr hA_finite)).mpr h4'
  have h_mul_rearrange :
      C * Kakeya.realRpowENN r 1 * (A.enncard / c) =
      (C / c) * Kakeya.realRpowENN r 1 * A.enncard := by
    have h6 : C * (A.enncard / c) = (C / c) * A.enncard := by
      simp only [div_eq_mul_inv]
      calc
        C * (A.enncard * c⁻¹)
          = C * A.enncard * c⁻¹ := by rw [mul_assoc]
        _ = C * (A.enncard * c⁻¹) := by rw [mul_assoc]
        _ = C * (c⁻¹ * A.enncard) := by rw [mul_comm A.enncard c⁻¹]
        _ = (C * c⁻¹) * A.enncard := by rw [←mul_assoc]
    calc
      C * Kakeya.realRpowENN r 1 * (A.enncard / c)
        = C * (Kakeya.realRpowENN r 1) * (A.enncard / c) := by rfl
      _ = Kakeya.realRpowENN r 1 * (C * (A.enncard / c)) := by
        simp [mul_assoc, mul_left_comm]
      _ = Kakeya.realRpowENN r 1 * ((C / c) * A.enncard) := by rw [h6]
      _ = (C / c) * Kakeya.realRpowENN r 1 * A.enncard := by
        simp [mul_assoc, mul_left_comm]
  calc
    A.ballCount x r
      ≤ ambient.ballCount x r := h1
    _ ≤ C * Kakeya.realRpowENN r 1 * ambient.enncard := h2
    _ ≤ C * Kakeya.realRpowENN r 1 * (A.enncard / c) := by gcongr
    _ = (C / c) * Kakeya.realRpowENN r 1 * A.enncard := h_mul_rearrange

/--
Worst-case Frostman retention bound for the three sequential rescaling rounds.

After three density-loss factors of `16`, the active-projection Frostman
constant is `65536 * δ^(-workingLambda-eta)`.  This lemma absorbs it into
`δ^(-2*workingLambda)` when `δ` is sufficiently small and `eta < workingLambda`.

Rounds 1 and 2 (constants `256` and `4096`) follow from this bound because
`256 ≤ 4096 ≤ 65536`.
-/
lemma wideSequentialFrostmanRetentionBound
    {delta eta workingLambda : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (heta_pos : 0 < eta)
    (hworkingLambda_pos : 0 < workingLambda)
    (heta_lt_workingLambda : eta < workingLambda)
    (hdelta_small : delta ≤ (65536 : ℝ)^(-1/(workingLambda - eta))) :
    (65536 : ENNReal) * Kakeya.realRpowENN delta (-(workingLambda + eta)) ≤
    Kakeya.realRpowENN delta (-(2 * workingLambda)) := by
  set gamma : ℝ := workingLambda - eta with hgamma_def
  have hgamma_pos : 0 < gamma := by linarith
  have h1 : Real.rpow delta gamma ≤ (1 / 65536 : ℝ) := by
    have h2 : delta ≤ (65536 : ℝ)^(-1 / gamma) := by
      simpa [hgamma_def] using hdelta_small
    have h3 : Real.rpow delta gamma ≤ Real.rpow ((65536 : ℝ)^(-1 / gamma)) gamma := by
      exact Real.rpow_le_rpow hdelta_pos.le h2 hgamma_pos.le
    have h4 : Real.rpow ((65536 : ℝ)^(-1 / gamma)) gamma = (65536 : ℝ)⁻¹ := by
      have h5 : Real.rpow ((65536 : ℝ)^(-1 / gamma)) gamma =
          Real.rpow (65536 : ℝ) ((-1 / gamma) * gamma) :=
        (Real.rpow_mul (show (0 : ℝ) ≤ (65536 : ℝ) by norm_num) (-1 / gamma) gamma).symm
      rw [h5]
      have h6 : (-1 / gamma) * gamma = -1 := by
        field_simp [hgamma_pos.ne']
      rw [h6]
      <;> norm_num
    rw [h4] at h3
    <;> norm_num at h3 ⊢ <;> exact h3
  have h5 : (65536 : ℝ) ≤ Real.rpow delta (-gamma) := by
    have h6 : Real.rpow delta (-gamma) = (Real.rpow delta gamma)⁻¹ :=
      Real.rpow_neg hdelta_pos.le gamma
    rw [h6]
    have h7 : 0 < Real.rpow delta gamma := Real.rpow_pos_of_pos hdelta_pos _
    have h8 : (Real.rpow delta gamma)⁻¹ ≥ (65536 : ℝ) := by
      have h9 : 0 < Real.rpow delta gamma := h7
      have h10 : Real.rpow delta gamma ≤ (1 / 65536 : ℝ) := h1
      have h11 : Real.rpow delta gamma * (65536 : ℝ) ≤ 1 := by
        calc
          Real.rpow delta gamma * (65536 : ℝ)
            ≤ (1 / 65536 : ℝ) * (65536 : ℝ) := by gcongr
          _ = 1 := by norm_num
      have h12 : (65536 : ℝ) ≤ (Real.rpow delta gamma)⁻¹ := by
        have h13 : (65536 : ℝ) ≤ 1 / Real.rpow delta gamma :=
          (le_div_iff₀' h7).mpr h11
        simpa [one_div] using h13
      exact h12
    exact h8
  have h9 : Real.rpow delta (-(2 * workingLambda)) =
      Real.rpow delta (-(workingLambda + eta)) * Real.rpow delta (-gamma) := by
    have h10 : -(2 * workingLambda) = (-(workingLambda + eta)) + (-gamma) := by
      simp [hgamma_def] <;> ring
    rw [h10]
    exact Real.rpow_add hdelta_pos _ _
  have h10 : (65536 : ℝ) * Real.rpow delta (-(workingLambda + eta)) ≤
      Real.rpow delta (-(2 * workingLambda)) := by
    rw [h9]
    have h11 : 0 ≤ Real.rpow delta (-(workingLambda + eta)) :=
      Real.rpow_nonneg hdelta_pos.le _
    nlinarith
  have h12 : (65536 : ENNReal) * Kakeya.realRpowENN delta (-(workingLambda + eta)) =
      ENNReal.ofReal ((65536 : ℝ) * Real.rpow delta (-(workingLambda + eta))) := by
    simp only [Kakeya.realRpowENN]
    have h13 : (65536 : ENNReal) = ENNReal.ofReal (65536 : ℝ) := by norm_cast
    rw [h13, ENNReal.ofReal_mul (by positivity)]
  rw [h12]
  exact ENNReal.ofReal_le_ofReal h10

/-- Round-1 retention bound (constant 256), follows from the round-3 bound. -/
lemma wideSequentialFrostmanRetentionBound_round1
    {delta eta workingLambda : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (heta_pos : 0 < eta)
    (hworkingLambda_pos : 0 < workingLambda)
    (heta_lt_workingLambda : eta < workingLambda)
    (hdelta_small : delta ≤ (65536 : ℝ)^(-1/(workingLambda - eta))) :
    (256 : ENNReal) * Kakeya.realRpowENN delta (-(workingLambda + eta)) ≤
    Kakeya.realRpowENN delta (-(2 * workingLambda)) := by
  have h : (256 : ENNReal) ≤ (65536 : ENNReal) := by norm_num
  have h_main := wideSequentialFrostmanRetentionBound
    hdelta_pos hdelta_le_one heta_pos hworkingLambda_pos
    heta_lt_workingLambda hdelta_small
  calc
    (256 : ENNReal) * Kakeya.realRpowENN delta (-(workingLambda + eta))
      ≤ (65536 : ENNReal) * Kakeya.realRpowENN delta (-(workingLambda + eta)) := by
        gcongr
    _ ≤ Kakeya.realRpowENN delta (-(2 * workingLambda)) := h_main

/-- Round-2 retention bound (constant 4096), follows from the round-3 bound. -/
lemma wideSequentialFrostmanRetentionBound_round2
    {delta eta workingLambda : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (heta_pos : 0 < eta)
    (hworkingLambda_pos : 0 < workingLambda)
    (heta_lt_workingLambda : eta < workingLambda)
    (hdelta_small : delta ≤ (65536 : ℝ)^(-1/(workingLambda - eta))) :
    (4096 : ENNReal) * Kakeya.realRpowENN delta (-(workingLambda + eta)) ≤
    Kakeya.realRpowENN delta (-(2 * workingLambda)) := by
  have h : (4096 : ENNReal) ≤ (65536 : ENNReal) := by norm_num
  have h_main := wideSequentialFrostmanRetentionBound
    hdelta_pos hdelta_le_one heta_pos hworkingLambda_pos
    heta_lt_workingLambda hdelta_small
  calc
    (4096 : ENNReal) * Kakeya.realRpowENN delta (-(workingLambda + eta))
      ≤ (65536 : ENNReal) * Kakeya.realRpowENN delta (-(workingLambda + eta)) := by
        gcongr
    _ ≤ Kakeya.realRpowENN delta (-(2 * workingLambda)) := h_main

end Kakeya.Assouad
