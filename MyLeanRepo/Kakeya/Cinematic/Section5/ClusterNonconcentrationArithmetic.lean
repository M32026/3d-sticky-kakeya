import Mathlib.Tactic

/-!
# Cluster non-concentration arithmetic

Convert the real cardinality estimate from PYZ Lemma 47 into the integer
half-mass condition used by the separated-cluster pigeonhole.
-/

namespace Kakeya.Cinematic

lemma two_mul_card_le_of_cast_card_le
    {clusterCard totalCard : ℕ} {factor : ℝ}
    (hfactor : 2 * factor ≤ 1)
    (hbound :
      (clusterCard : ℝ) ≤ factor * (totalCard : ℝ)) :
    2 * clusterCard ≤ totalCard := by
  have hscale :
      (2 * factor) * (totalCard : ℝ) ≤
        (totalCard : ℝ) := by
    simpa using
      mul_le_mul_of_nonneg_right hfactor (by
        show (0 : ℝ) ≤ (totalCard : ℝ)
        positivity)
  have hreal :
      (2 : ℝ) * (clusterCard : ℝ) ≤
        (totalCard : ℝ) := by
    nlinarith
  exact_mod_cast hreal

lemma cluster_half_of_incidence_nonconcentration
    {clusterCard totalCard : ℕ}
    {logLoss coefficient : ℝ}
    (hsmall : 4 * logLoss * coefficient ≤ 1)
    (hbound :
      (clusterCard : ℝ) ≤
        (2 * logLoss) * coefficient * (totalCard : ℝ)) :
    2 * clusterCard ≤ totalCard := by
  apply two_mul_card_le_of_cast_card_le
    (factor := (2 * logLoss) * coefficient)
  · nlinarith
  · exact hbound

end Kakeya.Cinematic
