import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.WZ1.GeneralizedThickening

/-!
# Six-delta perturbations of paper AD sets

This analytic lemma is independent of the terminal sticky construction.
Keeping it in a leaf module lets the Proposition 6.4 geometric chain reuse it
without importing the Node 5 hierarchy.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Paper-literal AD is stable under a one-sided `6 * delta` perturbation.
The explicit constant is intentionally rounded up to a convenient fixed
multiple. -/
theorem PureWZ2PaperADSet1.perturb_by_six_delta
    {source target : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (data : PureWZ2PaperADSet1 source delta alpha C)
    (hclose : ∀ value ∈ target,
      ∃ sourceValue ∈ source, |value - sourceValue| ≤ 6 * delta) :
    PureWZ2PaperADSet1 target delta alpha (192 * C) := by
  rcases data with
    ⟨hdelta, halpha, halphaOne, hC, hCtop, hcover⟩
  refine
    ⟨hdelta, halpha, halphaOne,
      hC.trans (le_mul_of_one_le_left' (by norm_num)),
      ENNReal.mul_ne_top (by norm_num) hCtop, ?_⟩
  intro rho hrho hdeltaRho left length hrhoLength
  have hrhoPos : 0 < rho := hdelta.trans_le hdeltaRho
  have hcloseSubset : target ⊆ Metric.cthickening (6 * delta) source := by
    intro value hvalue
    rcases hclose value hvalue with ⟨sourceValue, hsource, hdistance⟩
    exact Metric.mem_cthickening_of_dist_le value sourceValue
      (6 * delta) source hsource (by simpa [Real.dist_eq] using hdistance)
  let expandedLeft := left - 6 * delta
  let expandedLength := length + 12 * delta
  let sourcePart :=
    source ∩ Set.Icc expandedLeft (expandedLeft + expandedLength)
  let targetPart := target ∩ Set.Icc left (left + length)
  have hpartSubset : targetPart ⊆ Metric.cthickening (6 * delta) sourcePart := by
    intro value hvalue
    rcases hclose value hvalue.1 with
      ⟨sourceValue, hsourceValue, hdistance⟩
    have hdistanceBounds := abs_le.mp hdistance
    have hsourcePart : sourceValue ∈ sourcePart := by
      refine ⟨hsourceValue, ?_⟩
      dsimp only [expandedLeft, expandedLength]
      constructor <;> linarith [hvalue.2.1, hvalue.2.2]
    exact Metric.mem_cthickening_of_dist_le value sourceValue
      (6 * delta) sourcePart hsourcePart
      (by simpa [Real.dist_eq] using hdistance)
  have hcoverThick :
      Metric.externalCoveringNumber ⟨rho, hrho⟩ targetPart ≤
        Metric.externalCoveringNumber ⟨rho, hrho⟩
          (Metric.cthickening (6 * delta) sourcePart) :=
    Metric.externalCoveringNumber_mono_set hpartSubset
  have hthick :
      Metric.externalCoveringNumber ⟨rho, hrho⟩
          (Metric.cthickening (6 * delta) sourcePart) ≤
        (14 : ENat) *
          Metric.externalCoveringNumber ⟨rho, hrho⟩ sourcePart := by
    have hgeneral := externalCoveringNumber_cthickening_general
      (epsilon := 6 * delta) (rho := rho)
      (by positivity) hrhoPos (S := sourcePart)
    have hceil : Nat.ceil (6 * delta / rho) ≤ 6 := by
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ hrhoPos).2
      have hsix : 6 * delta ≤ 6 * rho :=
        mul_le_mul_of_nonneg_left hdeltaRho (by norm_num)
      norm_num at hsix ⊢
      exact hsix
    calc
      Metric.externalCoveringNumber ⟨rho, hrho⟩
          (Metric.cthickening (6 * delta) sourcePart) ≤
        (2 * Nat.ceil (6 * delta / rho) + 2 : ENat) *
          Metric.externalCoveringNumber ⟨rho, hrho⟩ sourcePart := hgeneral
      _ ≤ (14 : ENat) *
          Metric.externalCoveringNumber ⟨rho, hrho⟩ sourcePart := by
        gcongr
        exact_mod_cast (by omega : 2 * Nat.ceil (6 * delta / rho) + 2 ≤ 14)
  have hrhoExpanded : rho ≤ expandedLength := by
    dsimp only [expandedLength]
    nlinarith
  have hsourceCover :
      (Metric.externalCoveringNumber ⟨rho, hrho⟩ sourcePart : ENNReal) ≤
        C * Kakeya.realRpowENN (expandedLength / rho) alpha := by
    simpa [sourcePart, expandedLeft, expandedLength] using
      hcover rho hrho hdeltaRho (left - 6 * delta)
        (length + 12 * delta) hrhoExpanded
  have hlengthPos : 0 < length := hrhoPos.trans_le hrhoLength
  have hratioPos : 0 < length / rho := div_pos hlengthPos hrhoPos
  have hexpandedRatio : expandedLength / rho ≤ 13 * (length / rho) := by
    dsimp only [expandedLength]
    have hdeltaLength : delta ≤ length := hdeltaRho.trans hrhoLength
    calc
      (length + 12 * delta) / rho ≤ (13 * length) / rho := by
        exact div_le_div_of_nonneg_right (by linarith) hrhoPos.le
      _ = 13 * (length / rho) := by ring
  have hthirteenPower : Real.rpow 13 alpha ≤ 13 := by
    simpa using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 13)
        halphaOne
  have hpower :
      Kakeya.realRpowENN (expandedLength / rho) alpha ≤
        13 * Kakeya.realRpowENN (length / rho) alpha := by
    have hexpandedNonneg : 0 ≤ expandedLength / rho := by
      dsimp only [expandedLength]
      positivity
    have hmono :
        Real.rpow (expandedLength / rho) alpha ≤
          Real.rpow (13 * (length / rho)) alpha :=
      Real.rpow_le_rpow hexpandedNonneg hexpandedRatio halpha.le
    have hmul :
        Real.rpow (13 * (length / rho)) alpha =
          Real.rpow 13 alpha * Real.rpow (length / rho) alpha :=
      Real.mul_rpow (by norm_num) hratioPos.le
    have hratioPower : 0 ≤ Real.rpow (length / rho) alpha :=
      Real.rpow_nonneg hratioPos.le _
    unfold Kakeya.realRpowENN
    calc
      ENNReal.ofReal (Real.rpow (expandedLength / rho) alpha) ≤
          ENNReal.ofReal (Real.rpow (13 * (length / rho)) alpha) :=
        ENNReal.ofReal_mono hmono
      _ = ENNReal.ofReal
          (Real.rpow 13 alpha * Real.rpow (length / rho) alpha) := by
        rw [hmul]
      _ ≤ ENNReal.ofReal
          (13 * Real.rpow (length / rho) alpha) :=
        ENNReal.ofReal_mono
          (mul_le_mul_of_nonneg_right hthirteenPower hratioPower)
      _ = 13 * ENNReal.ofReal (Real.rpow (length / rho) alpha) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  change
    (Metric.externalCoveringNumber ⟨rho, hrho⟩ targetPart : ENNReal) ≤
      (192 * C) * Kakeya.realRpowENN (length / rho) alpha
  calc
    (Metric.externalCoveringNumber ⟨rho, hrho⟩ targetPart : ENNReal) ≤
        (Metric.externalCoveringNumber ⟨rho, hrho⟩
          (Metric.cthickening (6 * delta) sourcePart) : ENNReal) := by
      exact_mod_cast hcoverThick
    _ ≤ 14 *
        (Metric.externalCoveringNumber ⟨rho, hrho⟩ sourcePart : ENNReal) := by
      exact_mod_cast hthick
    _ ≤ 14 *
        (C * Kakeya.realRpowENN (expandedLength / rho) alpha) := by
      gcongr
    _ ≤ 14 * (C *
        (13 * Kakeya.realRpowENN (length / rho) alpha)) := by
      gcongr
    _ ≤ (192 * C) * Kakeya.realRpowENN (length / rho) alpha := by
      ring_nf
      gcongr
      norm_num

end Kakeya.Assouad
