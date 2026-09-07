import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseRelativeBandPreparation
import Mathlib.Tactic

/-!
# Broad-mass absorption after a relative multiplicity band

This file isolates the numerical bookkeeping in the sparse branch. The cubic
gain in the transverse-triple threshold pays the multiplicity upper bound in
the paper CV estimate. Consequently the mass floor is needed only on the
ambient normalized shading; no union-volume floor is asserted for the
selected multiplicity band.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- Abstract ENNReal bookkeeping behind sparse broad-mass absorption. -/
theorem sparse_relative_band_absorption_of_monomial_budget
    {bandCount multiplicity Q coefficient tubeScale densityPower tauPower
      ambientPower familyCard ambientMass selectedMass : ENNReal}
    (hbandCountZero : Ne bandCount 0)
    (hbandCountTop : Ne bandCount Top.top)
    (hmultiplicity :
      densityPower * familyCard <= 2 * multiplicity)
    (hQ :
      (1 / 16 : ENNReal) * multiplicity ^ 3 <= Q)
    (hambient : ambientPower * familyCard <= ambientMass)
    (hretention :
      (1 / 4 : ENNReal) * ambientMass <= bandCount * selectedMass)
    (hmonomial :
      (8192 : ENNReal) * bandCount ^ 2 * coefficient ^ 2 *
          tubeScale ^ 3 <=
        densityPower * tauPower * ambientPower ^ 2 * familyCard ^ 3) :
    (4 : ENNReal) * multiplicity * coefficient *
        tubeScale ^ (3 / 2 : Real) <=
      (Q * tauPower) ^ (1 / 2 : Real) * selectedMass := by
  let lhs : ENNReal :=
    (16 : ENNReal) * bandCount * multiplicity * coefficient *
      tubeScale ^ (3 / 2 : Real)
  let rhs : ENNReal :=
    (Q * tauPower) ^ (1 / 2 : Real) *
      (ambientPower * familyCard)
  have hsquare : lhs ^ (2 : Real) <= rhs ^ (2 : Real) := by
    have htubeSquare :
        (tubeScale ^ (3 / 2 : Real)) ^ (2 : Real) = tubeScale ^ 3 := by
      rw [← ENNReal.rpow_mul]
      norm_num [ENNReal.rpow_natCast]
    have hrootSquare :
        ((Q * tauPower) ^ (1 / 2 : Real)) ^ (2 : Real) =
          Q * tauPower := by
      rw [← ENNReal.rpow_mul]
      norm_num
    have hlhs : lhs ^ (2 : Real) =
        (256 : ENNReal) * bandCount ^ 2 * multiplicity ^ 2 *
          coefficient ^ 2 * tubeScale ^ 3 := by
      dsimp only [lhs]
      rw [ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg,
        ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg,
        htubeSquare]
      all_goals norm_num [ENNReal.rpow_natCast]
    have hrhs : rhs ^ (2 : Real) =
        Q * tauPower * ambientPower ^ 2 * familyCard ^ 2 := by
      dsimp only [rhs]
      rw [ENNReal.mul_rpow_of_nonneg, hrootSquare,
        ENNReal.mul_rpow_of_nonneg]
      all_goals norm_num [ENNReal.rpow_natCast]
      ring
    rw [hlhs, hrhs]
    refine (ENNReal.mul_le_mul_iff_right
      (a := (32 : ENNReal)) (b :=
        (256 : ENNReal) * bandCount ^ 2 * multiplicity ^ 2 *
          coefficient ^ 2 * tubeScale ^ 3)
      (c := Q * tauPower * ambientPower ^ 2 * familyCard ^ 2)
      (by norm_num) (by norm_num)).mp ?_
    calc
      (32 : ENNReal) *
          ((256 : ENNReal) * bandCount ^ 2 * multiplicity ^ 2 *
            coefficient ^ 2 * tubeScale ^ 3) =
          multiplicity ^ 2 *
            ((8192 : ENNReal) * bandCount ^ 2 * coefficient ^ 2 *
              tubeScale ^ 3) := by ring
      _ <= multiplicity ^ 2 *
          (densityPower * tauPower * ambientPower ^ 2 *
            familyCard ^ 3) := by gcongr
      _ = (densityPower * familyCard) *
          (multiplicity ^ 2 * tauPower * ambientPower ^ 2 *
            familyCard ^ 2) := by ring
      _ <= (2 * multiplicity) *
          (multiplicity ^ 2 * tauPower * ambientPower ^ 2 *
            familyCard ^ 2) := by gcongr
      _ = (32 : ENNReal) *
          ((1 / 16 : ENNReal) * multiplicity ^ 3 *
            tauPower * ambientPower ^ 2 * familyCard ^ 2) := by
        calc
          (2 * multiplicity) *
              (multiplicity ^ 2 * tauPower * ambientPower ^ 2 *
                familyCard ^ 2) =
              2 * (multiplicity ^ 3 * tauPower * ambientPower ^ 2 *
                familyCard ^ 2) := by ring
          _ = ((32 : ENNReal) * (1 / 16 : ENNReal)) *
              (multiplicity ^ 3 * tauPower * ambientPower ^ 2 *
                familyCard ^ 2) := by
            rw [show (32 : ENNReal) * (1 / 16 : ENNReal) = 2 by
              simp only [one_div]
              rw [show (32 : ENNReal) = 2 * 16 by norm_num,
                mul_assoc,
                ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
                mul_one]]
          _ = (32 : ENNReal) *
              ((1 / 16 : ENNReal) * multiplicity ^ 3 *
                tauPower * ambientPower ^ 2 * familyCard ^ 2) := by ring
      _ <= (32 : ENNReal) *
          (Q * tauPower * ambientPower ^ 2 * familyCard ^ 2) := by
        gcongr
  have hlhsRhs : lhs <= rhs :=
    (ENNReal.rpow_le_rpow_iff (z := (2 : Real)) (by norm_num)).mp hsquare
  have hscaled := mul_le_mul_left' hlhsRhs (1 / 4 : ENNReal)
  have hbeforeRetention :
      bandCount *
          ((4 : ENNReal) * multiplicity * coefficient *
            tubeScale ^ (3 / 2 : Real)) <=
        (Q * tauPower) ^ (1 / 2 : Real) *
          ((1 / 4 : ENNReal) * ambientMass) := by
    calc
      bandCount *
          ((4 : ENNReal) * multiplicity * coefficient *
            tubeScale ^ (3 / 2 : Real)) =
          (1 / 4 : ENNReal) * lhs := by
        dsimp only [lhs]
        calc
          bandCount *
              (4 * multiplicity * coefficient *
                tubeScale ^ (3 / 2 : Real)) =
              4 * (bandCount * multiplicity * coefficient *
                tubeScale ^ (3 / 2 : Real)) := by ring
          _ = ((1 / 4 : ENNReal) * 16) *
              (bandCount * multiplicity * coefficient *
                tubeScale ^ (3 / 2 : Real)) := by
            rw [show (1 / 4 : ENNReal) * 16 = 4 by
              simp only [one_div]
              rw [show (16 : ENNReal) = 4 * 4 by norm_num,
                ← mul_assoc,
                ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
                one_mul]]
          _ = (1 / 4 : ENNReal) *
              (16 * bandCount * multiplicity * coefficient *
                tubeScale ^ (3 / 2 : Real)) := by ring
      _ <= (1 / 4 : ENNReal) * rhs := hscaled
      _ = (Q * tauPower) ^ (1 / 2 : Real) *
          ((1 / 4 : ENNReal) *
            (ambientPower * familyCard)) := by
        dsimp only [rhs]
        ring
      _ <= (Q * tauPower) ^ (1 / 2 : Real) *
          ((1 / 4 : ENNReal) * ambientMass) := by gcongr
  have hwithRetention :
      bandCount *
          ((4 : ENNReal) * multiplicity * coefficient *
            tubeScale ^ (3 / 2 : Real)) <=
        bandCount *
          ((Q * tauPower) ^ (1 / 2 : Real) * selectedMass) := by
    calc
      bandCount *
          ((4 : ENNReal) * multiplicity * coefficient *
            tubeScale ^ (3 / 2 : Real)) <=
          (Q * tauPower) ^ (1 / 2 : Real) *
            ((1 / 4 : ENNReal) * ambientMass) := hbeforeRetention
      _ <= (Q * tauPower) ^ (1 / 2 : Real) *
          (bandCount * selectedMass) := by gcongr
      _ = bandCount *
          ((Q * tauPower) ^ (1 / 2 : Real) * selectedMass) := by ring
  exact (ENNReal.mul_le_mul_iff_right hbandCountZero hbandCountTop).mp
    hwithRetention

/-- The monomial budget follows from the single exponent inequality used in
the sparse branch. -/
theorem sparse_relative_band_power_monomial_budget
    {delta sigma loss tauExponent : Real}
    {bandCount coefficient familyCard : ENNReal}
    (hdelta : 0 < delta)
    (hsmall :
      (8192 : ENNReal) * bandCount ^ 2 * coefficient ^ 2 <=
        Kakeya.realRpowENN delta
          (tauExponent - sigma + 5 * loss)) :
    (8192 : ENNReal) * bandCount ^ 2 * coefficient ^ 2 *
        (ENNReal.ofReal (delta ^ 2) * familyCard) ^ 3 <=
      Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
        Kakeya.realRpowENN delta tauExponent *
        Kakeya.realRpowENN delta (loss + 2) ^ 2 *
        familyCard ^ 3 := by
  have hdeltaTwo : ENNReal.ofReal (delta ^ 2) =
      Kakeya.realRpowENN delta 2 := by
    simp [Kakeya.realRpowENN, Real.rpow_two]
  have htubeCube :
      Kakeya.realRpowENN delta 2 ^ 3 =
        Kakeya.realRpowENN delta 6 := by
    calc
      Kakeya.realRpowENN delta 2 ^ 3 =
          Kakeya.realRpowENN delta 2 *
            Kakeya.realRpowENN delta 2 *
              Kakeya.realRpowENN delta 2 := by ring
      _ = Kakeya.realRpowENN delta (2 + 2 + 2) := by
        rw [← Kakeya.Assouad.realRpowENN_add hdelta,
          ← Kakeya.Assouad.realRpowENN_add hdelta]
      _ = Kakeya.realRpowENN delta 6 := by norm_num
  have hambientSquare :
      Kakeya.realRpowENN delta (loss + 2) ^ 2 =
        Kakeya.realRpowENN delta (2 * (loss + 2)) := by
    calc
      Kakeya.realRpowENN delta (loss + 2) ^ 2 =
          Kakeya.realRpowENN delta (loss + 2) *
            Kakeya.realRpowENN delta (loss + 2) := by ring
      _ = Kakeya.realRpowENN delta ((loss + 2) + (loss + 2)) := by
        rw [← Kakeya.Assouad.realRpowENN_add hdelta]
      _ = Kakeya.realRpowENN delta (2 * (loss + 2)) := by ring
  have hleft :
      (8192 : ENNReal) * bandCount ^ 2 * coefficient ^ 2 *
          (ENNReal.ofReal (delta ^ 2) * familyCard) ^ 3 =
        ((8192 : ENNReal) * bandCount ^ 2 * coefficient ^ 2) *
          Kakeya.realRpowENN delta 6 * familyCard ^ 3 := by
    rw [hdeltaTwo, mul_pow, htubeCube]
    ring
  have hright :
      Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
          Kakeya.realRpowENN delta tauExponent *
          Kakeya.realRpowENN delta (loss + 2) ^ 2 *
          familyCard ^ 3 =
        Kakeya.realRpowENN delta
            (6 + tauExponent - sigma + 5 * loss) *
          familyCard ^ 3 := by
    rw [hambientSquare,
      ← Kakeya.Assouad.realRpowENN_add hdelta,
      ← Kakeya.Assouad.realRpowENN_add hdelta]
    congr 1
    ring
  rw [hleft, hright]
  calc
    ((8192 : ENNReal) * bandCount ^ 2 * coefficient ^ 2) *
        Kakeya.realRpowENN delta 6 * familyCard ^ 3 <=
      Kakeya.realRpowENN delta
          (tauExponent - sigma + 5 * loss) *
        Kakeya.realRpowENN delta 6 * familyCard ^ 3 := by gcongr
    _ = Kakeya.realRpowENN delta
          (6 + tauExponent - sigma + 5 * loss) *
        familyCard ^ 3 := by
      rw [← Kakeya.Assouad.realRpowENN_add hdelta]
      congr 1
      ring

namespace SparseRelativeBandPreparationData

/-- Discharge the sparse CV absorption hypothesis from the ambient normalized
mass floor and one small-delta exponent inequality. -/
theorem broad_absorption_of_power_budget
    {delta sigma loss tau tauExponent kappa : Real}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambient : WZ1PaperTubeShading family}
    {coefficient : ENNReal}
    (prepared : SparseRelativeBandPreparationData
      (kappa := kappa) ambient
      (Kakeya.realRpowENN delta (2 - sigma + 3 * loss)))
    (hdelta : 0 < delta)
    (htau : ENNReal.ofReal tau =
      Kakeya.realRpowENN delta tauExponent)
    (hambient :
      Kakeya.realRpowENN delta (loss + 2) * family.enncard <=
        ambient.mass)
    (hsmall :
      (8192 : ENNReal) * (prepared.bandCount : ENNReal) ^ 2 *
          coefficient ^ 2 <=
        Kakeya.realRpowENN delta
          (tauExponent - sigma + 5 * loss)) :
    let Q : Nat := prepared.multiplicity ^ 3 / 4
    (2 : ENNReal) * (2 * prepared.multiplicity : Nat) * coefficient *
        (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
          (3 / 2 : Real) <=
      (((Q : ENNReal) * ENNReal.ofReal tau) ^
        (1 / 2 : Real)) * prepared.shading.mass := by
  let M : Nat := prepared.multiplicity
  let Q : Nat := M ^ 3 / 4
  have hMtwo : 2 <= M := by
    have hbudget : 12 * prepared.closeThreshold <= M := by
      simpa [M] using prepared.combinatorial_budget
    have hR : 0 < prepared.closeThreshold :=
      prepared.closeThreshold_pos
    omega
  have hQNat : M ^ 3 <= 16 * Q := by
    dsimp only [Q]
    have hcube : 4 <= M ^ 3 := by
      calc
        4 <= 2 ^ 3 := by norm_num
        _ <= M ^ 3 := Nat.pow_le_pow_left hMtwo 3
    omega
  have hQ : (1 / 16 : ENNReal) * (M : ENNReal) ^ 3 <=
      (Q : ENNReal) := by
    rw [show (1 / 16 : ENNReal) * (M : ENNReal) ^ 3 =
      (M : ENNReal) ^ 3 / 16 by simp [div_eq_mul_inv, mul_comm]]
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    have hcast : (M : ENNReal) ^ 3 <= (16 * Q : Nat) := by
      exact_mod_cast hQNat
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcast
  have hdensity :
      Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
          family.enncard <= 2 * (M : ENNReal) := by
    have hscaled := mul_le_mul_left' prepared.density_lower
      (2 : ENNReal)
    have hcancel : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    calc
      Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
          family.enncard =
        2 *
          ((Kakeya.realRpowENN delta (2 - sigma + 3 * loss) / 2) *
            family.enncard) := by
          simp only [div_eq_mul_inv]
          calc
            Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
                family.enncard =
              1 * (Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
                family.enncard) := by rw [one_mul]
            _ = (2 * 2⁻¹) *
                (Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
                  family.enncard) := by rw [hcancel]
            _ = 2 *
                (Kakeya.realRpowENN delta (2 - sigma + 3 * loss) * 2⁻¹ *
                  family.enncard) := by ring
      _ <= 2 * (M : ENNReal) := by simpa [M] using hscaled
  have hbandCountPos : 0 < prepared.bandCount := by
    rw [prepared.bandCount_eq]
    omega
  have hbandCountZero : Ne (prepared.bandCount : ENNReal) 0 := by
    exact_mod_cast hbandCountPos.ne'
  have hbandCountTop : Ne (prepared.bandCount : ENNReal) Top.top := by simp
  have hmonomial := sparse_relative_band_power_monomial_budget
    (delta := delta) (sigma := sigma) (loss := loss)
    (tauExponent := tauExponent)
    (bandCount := (prepared.bandCount : ENNReal))
    (coefficient := coefficient) (familyCard := family.enncard)
    hdelta hsmall
  have hresult := sparse_relative_band_absorption_of_monomial_budget
    hbandCountZero hbandCountTop hdensity hQ hambient
    prepared.mass_retention hmonomial
  rw [htau]
  convert hresult using 1 <;> norm_num [M, Q, Nat.cast_mul] <;> ring

end SparseRelativeBandPreparationData

end Kakeya.Assouad.PureWZ2

end
