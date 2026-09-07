import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseRelativeBandBroadAbsorption
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import Mathlib.Tactic

/-!
# Absorption of the relative multiplicity-band count

The number of nonempty dyadic levels above the original multiplicity floor is
controlled by the reciprocal density power, not by the absolute cardinality
of the tube family. Thus the sparse branch does not pay a global cardinality
logarithm.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- In the ordered-log case, the relative dyadic range has the elementary
cardinality bound used to cancel the original multiplicity. -/
lemma relative_log_range_mul_le_two_mul
    (N m : Nat) (hN : 0 < N) (hm : 0 < m)
    (hlogs : Nat.log 2 m <= Nat.log 2 N) :
    2 ^ (Nat.log 2 N - Nat.log 2 m) * m <= 2 * N := by
  let k := Nat.log 2 N - Nat.log 2 m
  have hlogAdd : Nat.log 2 m + k = Nat.log 2 N := by
    dsimp only [k]
    omega
  have hmUpper : m < 2 ^ (Nat.log 2 m + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) m
  have hscaled : 2 ^ k * m < 2 ^ k * 2 ^ (Nat.log 2 m + 1) :=
    (Nat.mul_lt_mul_left (show 0 < 2 ^ k by positivity)).2 hmUpper
  have hpower : 2 ^ k * 2 ^ (Nat.log 2 m + 1) =
      2 * 2 ^ (Nat.log 2 N) := by
    rw [← pow_add, show k + (Nat.log 2 m + 1) =
      Nat.log 2 N + 1 by omega, pow_succ]
    ring
  have hNLower : 2 ^ Nat.log 2 N <= N :=
    Nat.pow_log_le_self 2 hN.ne'
  calc
    2 ^ (Nat.log 2 N - Nat.log 2 m) * m = 2 ^ k * m := by rfl
    _ <= 2 ^ k * 2 ^ (Nat.log 2 m + 1) := hscaled.le
    _ = 2 * 2 ^ Nat.log 2 N := hpower
    _ <= 2 * N := by omega

namespace SparseRelativeBandPreparationData

/-- The relative band count is bounded by a fixed multiple of one plus the
physical logarithm of the inverse scale. -/
theorem bandCount_le_log_envelope
    {delta exponent kappa : Real}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambient : WZ1PaperTubeShading family}
    (prepared : SparseRelativeBandPreparationData
      (kappa := kappa) ambient (Kakeya.realRpowENN delta exponent))
    (hfamily : family.Nonempty)
    (hdelta : 0 < delta)
    (hdeltaOne : delta <= 1)
    (hexponent : 0 <= exponent) :
    (prepared.bandCount : ENNReal) <=
      ENNReal.ofReal
        ((2 + exponent / Real.log 2) * (1 + Real.log delta⁻¹)) := by
  let N : Nat := family.card
  let m : Nat := prepared.originalMultiplicity
  let k : Nat := Nat.log 2 N - Nat.log 2 m
  have hN : 0 < N := by
    change 0 < family.card
    exact hfamily
  have hm : 0 < m := by simpa [m] using prepared.originalMultiplicity_pos
  have hlogInv : 0 <= Real.log delta⁻¹ := by
    apply Real.log_nonneg
    have hinv : (1 : Real)⁻¹ <= delta⁻¹ := by gcongr
    simpa using hinv
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoefficient : 0 <= 2 + exponent / Real.log 2 := by positivity
  have henvelope :
      0 <= (2 + exponent / Real.log 2) * (1 + Real.log delta⁻¹) := by
    positivity
  by_cases hlogs : Nat.log 2 m <= Nat.log 2 N
  · have hnat := relative_log_range_mul_le_two_mul N m hN hm hlogs
    have hcast :
        ((2 ^ k : Nat) : ENNReal) * (m : ENNReal) <=
          2 * (N : ENNReal) := by
      exact_mod_cast hnat
    have hdensityScaled :
        Kakeya.realRpowENN delta exponent * ((2 ^ k : Nat) : ENNReal) *
            (m : ENNReal) <=
          2 * (m : ENNReal) := by
      calc
        Kakeya.realRpowENN delta exponent * ((2 ^ k : Nat) : ENNReal) *
            (m : ENNReal) <=
          Kakeya.realRpowENN delta exponent * (2 * (N : ENNReal)) := by
            calc
              Kakeya.realRpowENN delta exponent * ((2 ^ k : Nat) : ENNReal) *
                  (m : ENNReal) =
                Kakeya.realRpowENN delta exponent *
                  (((2 ^ k : Nat) : ENNReal) * (m : ENNReal)) := by ring
              _ <= Kakeya.realRpowENN delta exponent *
                  (2 * (N : ENNReal)) := by gcongr
        _ = 2 *
            (Kakeya.realRpowENN delta exponent * family.enncard) := by
          simp only [N, Kakeya.Streamlined.TubeFamily.enncard]
          ring
        _ <= 2 * (m : ENNReal) := by
          simpa [m] using mul_le_mul_left' prepared.original_density
            (2 : ENNReal)
    have hmZero : Ne (m : ENNReal) 0 := by exact_mod_cast hm.ne'
    have hmTop : Ne (m : ENNReal) Top.top := by simp
    have hdensityPower :
        Kakeya.realRpowENN delta exponent * ((2 ^ k : Nat) : ENNReal) <= 2 :=
      (ENNReal.mul_le_mul_iff_left hmZero hmTop).mp <| by
        simpa [mul_assoc] using hdensityScaled
    have hleftTop : Ne
        (Kakeya.realRpowENN delta exponent * ((2 ^ k : Nat) : ENNReal))
        Top.top := by
      apply ENNReal.mul_ne_top
      · simp [Kakeya.realRpowENN]
      · simp
    have hreal := (ENNReal.toReal_le_toReal hleftTop (by norm_num)).mpr
      hdensityPower
    have hdensityReal :
        (Kakeya.realRpowENN delta exponent).toReal =
          Real.rpow delta exponent := by
      simp [Kakeya.realRpowENN, ENNReal.toReal_ofReal
        (Real.rpow_nonneg hdelta.le exponent)]
    have hpowReal :
        (((2 ^ k : Nat) : ENNReal)).toReal = ((2 : Real) ^ k) := by
      rw [ENNReal.toReal_natCast]
      norm_cast
    rw [ENNReal.toReal_mul, hdensityReal, hpowReal,
      ENNReal.toReal_ofNat] at hreal
    have hpositiveLeft : 0 < Real.rpow delta exponent * (2 : Real) ^ k := by
      exact mul_pos (Real.rpow_pos_of_pos hdelta exponent)
        (pow_pos (by norm_num) k)
    have hlog := Real.log_le_log hpositiveLeft hreal
    have hlogIdentity :
        Real.log (Real.rpow delta exponent * (2 : Real) ^ k) =
          exponent * Real.log delta + (k : Real) * Real.log 2 := by
      have hlogRpow : Real.log (Real.rpow delta exponent) =
          exponent * Real.log delta := by
        exact Real.log_rpow hdelta exponent
      calc
        Real.log (Real.rpow delta exponent * (2 : Real) ^ k) =
            Real.log (Real.rpow delta exponent) +
              Real.log ((2 : Real) ^ k) :=
          Real.log_mul (Real.rpow_pos_of_pos hdelta exponent).ne'
            (pow_ne_zero k (by norm_num))
        _ = exponent * Real.log delta + (k : Real) * Real.log 2 := by
          rw [hlogRpow, Real.log_pow]
    have hlogInvIdentity : Real.log delta⁻¹ = -Real.log delta :=
      Real.log_inv delta
    have hkReal :
        (k : Real) <= 1 + exponent / Real.log 2 * Real.log delta⁻¹ := by
      rw [hlogIdentity] at hlog
      calc
        (k : Real) <=
            (Real.log 2 - exponent * Real.log delta) / Real.log 2 := by
          apply (le_div_iff₀ hlogTwo).2
          linarith
        _ = 1 + exponent / Real.log 2 * Real.log delta⁻¹ := by
          rw [hlogInvIdentity]
          field_simp [hlogTwo.ne']
          ring
    have hbandEq : prepared.bandCount = k + 1 := by
      rw [prepared.bandCount_eq]
    have hbandReal : (prepared.bandCount : Real) <=
        (2 + exponent / Real.log 2) * (1 + Real.log delta⁻¹) := by
      rw [hbandEq]
      push_cast
      have hratio : 0 <= exponent / Real.log 2 :=
        div_nonneg hexponent hlogTwo.le
      nlinarith [mul_nonneg hratio hlogInv]
    have hcastReal : (prepared.bandCount : ENNReal) =
        ENNReal.ofReal (prepared.bandCount : Real) := by simp
    rw [hcastReal]
    exact (ENNReal.ofReal_le_ofReal_iff henvelope).2 hbandReal
  · have hbandEq : prepared.bandCount = 1 := by
      rw [prepared.bandCount_eq]
      dsimp only [N, m] at hlogs
      omega
    rw [hbandEq]
    have hone : (1 : Real) <=
        (2 + exponent / Real.log 2) * (1 + Real.log delta⁻¹) := by
      have hfirst : (2 : Real) <= 2 + exponent / Real.log 2 := by
        exact le_add_of_nonneg_right (div_nonneg hexponent hlogTwo.le)
      have hsecond : (1 : Real) <= 1 + Real.log delta⁻¹ := by
        exact le_add_of_nonneg_right hlogInv
      calc
        (1 : Real) <= 2 * 1 := by norm_num
        _ <= (2 + exponent / Real.log 2) * 1 := by gcongr
        _ <= (2 + exponent / Real.log 2) *
            (1 + Real.log delta⁻¹) := by gcongr
    simpa using (ENNReal.one_le_ofReal).2 hone

/-- For every fixed finite CV coefficient, a sufficiently small scale absorbs
the square of the relative band count. -/
theorem exists_power_budget_scale
    (exponent gap : Real) (coefficient : ENNReal)
    (hexponent : 0 <= exponent)
    (hgap : 0 < gap)
    (hcoefficient : Ne coefficient Top.top) :
    ∃ delta0 : Real, 0 < delta0 ∧ delta0 <= 1 ∧
      ∀ {delta kappa : Real}
        {family : Kakeya.Streamlined.TubeFamily delta}
        {ambient : WZ1PaperTubeShading family}
        (prepared : SparseRelativeBandPreparationData
          (kappa := kappa) ambient
          (Kakeya.realRpowENN delta exponent)),
        family.Nonempty →
        0 < delta → delta <= delta0 →
        (8192 : ENNReal) * (prepared.bandCount : ENNReal) ^ 2 *
            coefficient ^ 2 <=
          Kakeya.realRpowENN delta (-gap) := by
  let envelopeCoefficient : Real := 2 + exponent / Real.log 2
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have henvelopeCoefficient : 0 <= envelopeCoefficient := by
    dsimp only [envelopeCoefficient]
    positivity
  let fixed : ENNReal := (8192 : ENNReal) * coefficient ^ 2
  have hfixedTop : Ne fixed Top.top :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hcoefficient)
  rcases Kakeya.Assouad.exists_delta_C_pow_log_absorbed_ennreal
      (n := 2) fixed hfixedTop envelopeCoefficient
      henvelopeCoefficient hgap (by norm_num) with
    ⟨delta0, hdelta0, hdelta0One, habsorb⟩
  refine ⟨delta0, hdelta0, hdelta0One, ?_⟩
  intro delta kappa family ambient prepared hfamily hdelta hdeltaBound
  have hdeltaOne : delta <= 1 := hdeltaBound.trans hdelta0One
  have hband := prepared.bandCount_le_log_envelope hfamily hdelta
    hdeltaOne hexponent
  calc
    (8192 : ENNReal) * (prepared.bandCount : ENNReal) ^ 2 *
        coefficient ^ 2 =
      fixed * (prepared.bandCount : ENNReal) ^ 2 := by
        dsimp only [fixed]
        ring
    _ <= fixed *
        (ENNReal.ofReal
          (envelopeCoefficient * (1 + Real.log delta⁻¹))) ^ 2 := by
      gcongr
    _ <= Kakeya.realRpowENN delta (-gap) :=
      habsorb delta hdelta hdeltaBound

end SparseRelativeBandPreparationData

end Kakeya.Assouad.PureWZ2

end
