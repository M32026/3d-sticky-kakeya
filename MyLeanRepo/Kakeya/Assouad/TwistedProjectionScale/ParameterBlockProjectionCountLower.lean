import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionBasicArithmetic

/-!
# Count product in paper Lemma 7.12

The translation count contributes `rho⁻²`, the local parameter count
contributes `(rho / delta)^(3s)`, and the per-tube mass contributes
`delta^(3 + loss)`.  Their product is exactly

`rho * (delta / rho)^(60 epsilon²) * delta^loss`

when `s = 1 - 20 epsilon²`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Exact power identity underlying the Lemma 7.12 count product. -/
lemma parameterBlockProjection_count_power_identity
    {delta rho epsilon loss : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho) :
    Kakeya.realRpowENN rho (-2) *
          Kakeya.realRpowENN
            (rho / delta) (3 * (1 - 20 * epsilon ^ 2)) *
          Kakeya.realRpowENN delta (3 + loss) =
      Kakeya.realRpowENN rho 1 *
        Kakeya.realRpowENN
          (delta / rho) (60 * epsilon ^ 2) *
        Kakeya.realRpowENN delta loss := by
  have hratio : 0 < delta / rho := by positivity
  have hinverse :
      Kakeya.realRpowENN
          (rho / delta) (3 * (1 - 20 * epsilon ^ 2)) =
        Kakeya.realRpowENN
          (delta / rho) (-3 * (1 - 20 * epsilon ^ 2)) := by
    simpa only [neg_mul] using
      (realRpowENN_block_div_delta
        (exponent := 3 * (1 - 20 * epsilon ^ 2))
        hdelta hrho)
  have hdelta_split :
      Kakeya.realRpowENN delta (3 + loss) =
        Kakeya.realRpowENN delta 3 *
          Kakeya.realRpowENN delta loss :=
    realRpowENN_add hdelta 3 loss
  have hdelta_three :
      Kakeya.realRpowENN delta 3 =
        Kakeya.realRpowENN (delta / rho) 3 *
          Kakeya.realRpowENN rho 3 := by
    exact
      (parameterBlockProjection_realRpowENN_div_mul
        hdelta hrho).symm
  have hrho_combine :
      Kakeya.realRpowENN rho (-2) *
          Kakeya.realRpowENN rho 3 =
        Kakeya.realRpowENN rho 1 := by
    rw [← realRpowENN_add hrho]
    congr 1
    ring
  have hratio_combine :
      Kakeya.realRpowENN
            (delta / rho) (-3 * (1 - 20 * epsilon ^ 2)) *
          Kakeya.realRpowENN (delta / rho) 3 =
        Kakeya.realRpowENN
          (delta / rho) (60 * epsilon ^ 2) := by
    rw [← realRpowENN_add hratio]
    congr 1
    ring
  rw [hinverse, hdelta_split, hdelta_three]
  calc
    Kakeya.realRpowENN rho (-2) *
          Kakeya.realRpowENN
            (delta / rho) (-3 * (1 - 20 * epsilon ^ 2)) *
          ((Kakeya.realRpowENN (delta / rho) 3 *
            Kakeya.realRpowENN rho 3) *
          Kakeya.realRpowENN delta loss) =
        (Kakeya.realRpowENN rho (-2) *
          Kakeya.realRpowENN rho 3) *
        (Kakeya.realRpowENN
            (delta / rho) (-3 * (1 - 20 * epsilon ^ 2)) *
          Kakeya.realRpowENN (delta / rho) 3) *
        Kakeya.realRpowENN delta loss := by ring
    _ =
        Kakeya.realRpowENN rho 1 *
          Kakeya.realRpowENN
            (delta / rho) (60 * epsilon ^ 2) *
          Kakeya.realRpowENN delta loss := by
      rw [hrho_combine, hratio_combine]

/--
Translation and local-cardinality lower bounds imply the scaled count product
used by the cinematic lower bound.
-/
lemma parameterBlockProjection_count_product_lower
    {delta rho epsilon loss : ℝ}
    {translations points : ENNReal}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (htranslations :
      Kakeya.realRpowENN rho (-1) ≤
        100000 * translations)
    (hpoints :
      Kakeya.realRpowENN
          (rho / delta) (1 - 20 * epsilon ^ 2) ≤
        100000 * points) :
    Kakeya.realRpowENN rho 1 *
          Kakeya.realRpowENN
            (delta / rho) (60 * epsilon ^ 2) *
          Kakeya.realRpowENN delta loss ≤
      (100000 : ENNReal) ^ 5 *
        (translations ^ 2 *
          Kakeya.realRpowENN delta (3 + loss) *
          points ^ 3) := by
  have htranslations_sq :
      Kakeya.realRpowENN rho (-2) ≤
        (100000 : ENNReal) ^ 2 * translations ^ 2 := by
    have hpow := pow_le_pow_left₀ (by positivity) htranslations 2
    have hleft :
        (Kakeya.realRpowENN rho (-1)) ^ 2 =
          Kakeya.realRpowENN rho (-2) := by
      rw [pow_two, ← realRpowENN_add hrho]
      congr 1
      ring
    have hright :
        ((100000 : ENNReal) * translations) ^ 2 =
          (100000 : ENNReal) ^ 2 * translations ^ 2 := by
      rw [mul_pow]
    rwa [hleft, hright] at hpow
  have hpoints_cube :
      Kakeya.realRpowENN
          (rho / delta) (3 * (1 - 20 * epsilon ^ 2)) ≤
        (100000 : ENNReal) ^ 3 * points ^ 3 := by
    have hpow := pow_le_pow_left₀ (by positivity) hpoints 3
    have hleft :
        (Kakeya.realRpowENN
          (rho / delta) (1 - 20 * epsilon ^ 2)) ^ 3 =
          Kakeya.realRpowENN
            (rho / delta) (3 * (1 - 20 * epsilon ^ 2)) := by
      rw [pow_three]
      rw [← realRpowENN_add (by positivity),
        ← realRpowENN_add (by positivity)]
      congr 1
      ring
    have hright :
        ((100000 : ENNReal) * points) ^ 3 =
          (100000 : ENNReal) ^ 3 * points ^ 3 := by
      rw [mul_pow]
    rwa [hleft, hright] at hpow
  rw [← parameterBlockProjection_count_power_identity
    hdelta hrho]
  calc
    Kakeya.realRpowENN rho (-2) *
          Kakeya.realRpowENN
            (rho / delta) (3 * (1 - 20 * epsilon ^ 2)) *
          Kakeya.realRpowENN delta (3 + loss) ≤
        ((100000 : ENNReal) ^ 2 * translations ^ 2) *
          ((100000 : ENNReal) ^ 3 * points ^ 3) *
          Kakeya.realRpowENN delta (3 + loss) := by
      gcongr
    _ =
        (100000 : ENNReal) ^ 5 *
          (translations ^ 2 *
            Kakeya.realRpowENN delta (3 + loss) *
            points ^ 3) := by
      ring

end Kakeya.Assouad
