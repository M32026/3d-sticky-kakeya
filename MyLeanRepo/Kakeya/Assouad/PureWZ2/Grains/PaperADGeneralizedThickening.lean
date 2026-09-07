import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalProjectionHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.GeneralizedThickening

/-!
# General thickening stability for the paper AD predicate

The literal paper predicate has no global bounded-window requirement.  This
direct proof therefore works on each query interval and pays only the square
of the number of minimum-scale cells crossed by the thickening radius.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- If `B` lies in an `epsilon`-neighborhood of a paper AD set `A`, then `B`
has the same minimum scale and exponent, with an explicit finite loss. -/
lemma PureWZ2PaperADSet1.generalized_thickening
    {A B : Set ℝ} {delta alpha epsilon : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 A delta alpha C)
    (hclose : ∀ x ∈ B, ∃ y ∈ A, |x - y| ≤ epsilon)
    (hepsilon : 0 < epsilon) :
    PureWZ2PaperADSet1 B delta alpha
      ((2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 2 * C) := by
  rcases hAD with ⟨hdelta, halpha, halphaOne, hCone, hCtop, hcover⟩
  let k : ℕ := Nat.ceil (epsilon / delta)
  let K : ℕ := 2 * (k + 1)
  have hKpos : 0 < K := by positivity
  have htargetOne : (1 : ENNReal) ≤
      (2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 2 * C := by
    have hfactor : (1 : ENNReal) ≤
        (2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) := by
      exact_mod_cast (by omega : 1 ≤ 2 * (Nat.ceil (epsilon / delta) + 1))
    calc
      (1 : ENNReal) ≤
          (2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 2 := by
        simpa [pow_two] using mul_le_mul hfactor hfactor
          (by norm_num) (by norm_num)
      _ ≤ (2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 2 * C :=
        le_mul_of_one_le_right' hCone
  have htargetTop :
      (2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 2 * C ≠ ⊤ := by
    have hfactorTop :
        (2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ≠ ⊤ := by
      norm_num [ENNReal.mul_eq_top, ENNReal.add_eq_top]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hfactorTop) hCtop
  refine ⟨hdelta, halpha, halphaOne, htargetOne, htargetTop, ?_⟩
  intro rho hrho hdeltaRho left length hrhoLength
  have hrhoPos : 0 < rho := hdelta.trans_le hdeltaRho
  let kRho : ℕ := Nat.ceil (epsilon / rho)
  have hkRhoLe : kRho ≤ k := by
    have hdiv : epsilon / rho ≤ epsilon / delta := by gcongr
    exact Nat.ceil_le.mpr (hdiv.trans (Nat.le_ceil _))
  let sourceWindow : Set ℝ :=
    A ∩ Set.Icc (left - epsilon) (left + length + epsilon)
  have htargetThick :
      B ∩ Set.Icc left (left + length) ⊆
        Metric.cthickening epsilon sourceWindow := by
    intro value hvalue
    rcases hclose value hvalue.1 with ⟨reference, hreference, hdistance⟩
    have hreferenceWindow : reference ∈ sourceWindow := by
      refine ⟨hreference, ?_⟩
      rw [abs_le] at hdistance
      exact ⟨by linarith [hvalue.2.1, hdistance.2],
        by linarith [hvalue.2.2, hdistance.1]⟩
    exact Metric.mem_cthickening_of_dist_le value reference epsilon
      sourceWindow hreferenceWindow (by simpa [Real.dist_eq] using hdistance)
  have hmono :
      (Metric.externalCoveringNumber ⟨rho, hrho⟩
          (B ∩ Set.Icc left (left + length)) : ENNReal) ≤
        Metric.externalCoveringNumber ⟨rho, hrho⟩
          (Metric.cthickening epsilon sourceWindow) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set htargetThick
  have hthick :
      Metric.externalCoveringNumber ⟨rho, hrho⟩
          (Metric.cthickening epsilon sourceWindow) ≤
        (2 * kRho + 2 : ENat) *
          Metric.externalCoveringNumber ⟨rho, hrho⟩ sourceWindow := by
    simpa [kRho] using
      externalCoveringNumber_cthickening_general hepsilon hrhoPos
        (S := sourceWindow)
  have hthick' :
      (Metric.externalCoveringNumber ⟨rho, hrho⟩
          (Metric.cthickening epsilon sourceWindow) : ENNReal) ≤
        (2 * kRho + 2 : ENNReal) *
          (Metric.externalCoveringNumber ⟨rho, hrho⟩ sourceWindow : ENNReal) := by
    exact_mod_cast hthick
  let sourceLength : ℝ := length + 2 * epsilon
  have hsourceLength :
      sourceWindow = A ∩ Set.Icc (left - epsilon)
        ((left - epsilon) + sourceLength) := by
    simp only [sourceWindow, sourceLength]
    congr 2
    ring
  have hrhoSourceLength : rho ≤ sourceLength := by
    dsimp only [sourceLength]
    linarith
  have hsourceCover :
      (Metric.externalCoveringNumber ⟨rho, hrho⟩ sourceWindow : ENNReal) ≤
        C * Kakeya.realRpowENN (sourceLength / rho) alpha := by
    rw [hsourceLength]
    exact hcover rho hrho hdeltaRho (left - epsilon) sourceLength
      hrhoSourceLength
  have hepsilonK : epsilon ≤ (k : ℝ) * delta := by
    have hk : epsilon / delta ≤ (k : ℝ) := Nat.le_ceil _
    calc
      epsilon = (epsilon / delta) * delta := by
        field_simp [hdelta.ne']
      _ ≤ (k : ℝ) * delta := by gcongr
  have hepsilonLength : epsilon ≤ (k : ℝ) * length := by
    exact hepsilonK.trans (by
      exact mul_le_mul_of_nonneg_left
        (hdeltaRho.trans hrhoLength) (Nat.cast_nonneg k))
  have hsourceRatio : sourceLength / rho ≤
      (2 * (k : ℝ) + 1) * (length / rho) := by
    have hlength : sourceLength ≤ (2 * (k : ℝ) + 1) * length := by
      dsimp only [sourceLength]
      nlinarith
    calc
      sourceLength / rho ≤
          ((2 * (k : ℝ) + 1) * length) / rho :=
        div_le_div_of_nonneg_right hlength hrhoPos.le
      _ = (2 * (k : ℝ) + 1) * (length / rho) := by ring
  have hlengthRatio : 0 ≤ length / rho :=
    div_nonneg (hrhoPos.le.trans hrhoLength) hrhoPos.le
  have hfactorOne : 1 ≤ 2 * (k : ℝ) + 1 := by
    exact_mod_cast (by omega : 1 ≤ 2 * k + 1)
  have hsourceRpow :
      Kakeya.realRpowENN (sourceLength / rho) alpha ≤
        (2 * (k : ENNReal) + 1) *
          Kakeya.realRpowENN (length / rho) alpha := by
    have hsourceNonneg : 0 ≤ sourceLength / rho :=
      div_nonneg (by dsimp only [sourceLength]; linarith) hrhoPos.le
    have hmonoRpow :
        Kakeya.realRpowENN (sourceLength / rho) alpha ≤
          Kakeya.realRpowENN
            ((2 * (k : ℝ) + 1) * (length / rho)) alpha := by
      simp only [Kakeya.realRpowENN]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow hsourceNonneg hsourceRatio halpha.le)
    have hmulReal : Real.rpow
          ((2 * (k : ℝ) + 1) * (length / rho)) alpha =
        Real.rpow (2 * (k : ℝ) + 1) alpha *
          Real.rpow (length / rho) alpha :=
      Real.mul_rpow (by linarith) hlengthRatio
    have hmul : Kakeya.realRpowENN
          ((2 * (k : ℝ) + 1) * (length / rho)) alpha =
        Kakeya.realRpowENN (2 * (k : ℝ) + 1) alpha *
          Kakeya.realRpowENN (length / rho) alpha := by
      simp only [Kakeya.realRpowENN, hmulReal]
      exact ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) alpha)
    have hfactorRpow :
        Kakeya.realRpowENN (2 * (k : ℝ) + 1) alpha ≤
          (2 * (k : ENNReal) + 1) := by
      simp only [Kakeya.realRpowENN]
      rw [show (2 * (k : ENNReal) + 1) =
          ENNReal.ofReal (2 * (k : ℝ) + 1) by norm_cast]
      apply ENNReal.ofReal_le_ofReal
      have hpow := Real.rpow_le_rpow_of_exponent_le
        hfactorOne halphaOne
      simpa using hpow
    calc
      _ ≤ Kakeya.realRpowENN
          ((2 * (k : ℝ) + 1) * (length / rho)) alpha := hmonoRpow
      _ = Kakeya.realRpowENN (2 * (k : ℝ) + 1) alpha *
          Kakeya.realRpowENN (length / rho) alpha := hmul
      _ ≤ (2 * (k : ENNReal) + 1) *
          Kakeya.realRpowENN (length / rho) alpha := by gcongr
  have hkFactor : (2 * kRho + 2 : ENNReal) ≤
      (2 * (k : ENNReal) + 2) := by exact_mod_cast (by omega : 2 * kRho + 2 ≤ 2 * k + 2)
  have hfactorProduct :
      (2 * (k : ENNReal) + 2) * (2 * (k : ENNReal) + 1) ≤
        (K : ENNReal) ^ 2 := by
    have hleft : (2 * (k : ENNReal) + 1) ≤
        (2 * (k : ENNReal) + 2) := by
      calc
        2 * (k : ENNReal) + 1 = 1 + 2 * (k : ENNReal) := by ac_rfl
        _ ≤ 2 + 2 * (k : ENNReal) :=
          add_le_add_left (show (1 : ENNReal) ≤ 2 by norm_num) _
        _ = 2 * (k : ENNReal) + 2 := by ac_rfl
    calc
      (2 * (k : ENNReal) + 2) * (2 * (k : ENNReal) + 1) ≤
          (2 * (k : ENNReal) + 2) * (2 * (k : ENNReal) + 2) := by
        gcongr
      _ = (K : ENNReal) ^ 2 := by
        simp only [K, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
        ring
  calc
    (Metric.externalCoveringNumber ⟨rho, hrho⟩
        (B ∩ Set.Icc left (left + length)) : ENNReal) ≤
      Metric.externalCoveringNumber ⟨rho, hrho⟩
        (Metric.cthickening epsilon sourceWindow) := hmono
    _ ≤ (2 * kRho + 2 : ENNReal) *
        (Metric.externalCoveringNumber ⟨rho, hrho⟩ sourceWindow : ENNReal) :=
      hthick'
    _ ≤ (2 * kRho + 2 : ENNReal) *
        (C * Kakeya.realRpowENN (sourceLength / rho) alpha) := by gcongr
    _ ≤ (2 * (k : ENNReal) + 2) *
        (C * ((2 * (k : ENNReal) + 1) *
          Kakeya.realRpowENN (length / rho) alpha)) := by gcongr
    _ = ((2 * (k : ENNReal) + 2) *
          (2 * (k : ENNReal) + 1)) * C *
            Kakeya.realRpowENN (length / rho) alpha := by ring
    _ ≤ (K : ENNReal) ^ 2 * C *
        Kakeya.realRpowENN (length / rho) alpha := by
      gcongr
    _ = (2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 2 * C *
        Kakeya.realRpowENN (length / rho) alpha := by
      have hKcast : (K : ENNReal) =
          (2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) := by
        dsimp only [K, k]
        norm_cast
      rw [hKcast]

end Kakeya.Assouad

end
