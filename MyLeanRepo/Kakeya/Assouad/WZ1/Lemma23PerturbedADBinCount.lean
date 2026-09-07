import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ADBinCount
import MyLeanRepo.Kakeya.Assouad.WZ1.NeighborPackingBound

/-!
# Perturbed AD-bin count for WZ1 Lemma 23

Snapping a genuine slice point to the center of its spatial cell changes the
global scalar coordinate by at most `4 * rho`.  This module records the
resulting finite loss in the number of occupied `rho`-mesh bins.
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

/--
If every value is within `4 * rho` of a one-dimensional AD set, then its
occupied `rho`-mesh bins satisfy the same AD count up to the absolute factor
`11`.  Combined with the closed global AD-bin theorem, the final factor is
`11 * 12 = 132`.
-/
theorem wz1_lemma23_perturbed_ad_bin_count
    (rho alpha : ℝ) (C : ENNReal)
    (E : Set ℝ) (values : Finset ℝ)
    (hAD : IsADSet1 E rho alpha C)
    (hrho_le_one : rho ≤ 1)
    (hclose :
      ∀ value ∈ values,
        ∃ sourceValue ∈ E,
          |value - sourceValue| ≤ 4 * rho) :
    ((wz1Lemma23ScalarBins rho values).card : ENNReal) ≤
      132 * C * Kakeya.realRpowENN (1 / rho) alpha := by
  classical
  have hrho : 0 < rho := hAD.1
  let sourceValue : {value // value ∈ values} → ℝ :=
    fun value => Classical.choose (hclose value.1 value.2)
  have hsourceValue :
      ∀ value : {value // value ∈ values},
        sourceValue value ∈ E ∧
          |value.1 - sourceValue value| ≤ 4 * rho := by
    intro value
    exact Classical.choose_spec (hclose value.1 value.2)
  let sourceValues : Finset ℝ :=
    values.attach.image sourceValue
  have hsourceValues :
      (sourceValues : Set ℝ) ⊆ E := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨source, _, rfl⟩
    exact (hsourceValue source).1
  have hsourceBins :=
    wz1_lemma23_ad_bin_count
      rho alpha C E sourceValues hAD hrho_le_one hsourceValues
  let sourceBins := wz1Lemma23ScalarBins rho sourceValues
  let nearbyBins (sourceBin : ℤ) : Finset ℤ :=
    Finset.Icc (sourceBin - 5) (sourceBin + 5)
  have hnearbyCard :
      ∀ sourceBin : ℤ, (nearbyBins sourceBin).card = 11 := by
    intro sourceBin
    simp [nearbyBins]
    omega
  have htargetSubset :
      wz1Lemma23ScalarBins rho values ⊆
        sourceBins.biUnion nearbyBins := by
    intro targetBin htargetBin
    rcases Finset.mem_image.mp htargetBin with
      ⟨value, hvalue, rfl⟩
    let source : {value // value ∈ values} :=
      ⟨value, hvalue⟩
    let sourceBin : ℤ :=
      Int.floor (sourceValue source / rho)
    have hsourceMem : sourceValue source ∈ sourceValues := by
      exact Finset.mem_image.mpr
        ⟨source, by simp, rfl⟩
    have hsourceBinMem : sourceBin ∈ sourceBins := by
      exact Finset.mem_image.mpr
        ⟨sourceValue source, hsourceMem, rfl⟩
    have hratio :
        |value / rho - sourceValue source / rho| < 5 := by
      have hcloseSource :=
        (hsourceValue source).2
      have hdiv :
          |value / rho - sourceValue source / rho| =
            |value - sourceValue source| / rho := by
        rw [← sub_div, abs_div, abs_of_pos hrho]
      rw [hdiv]
      have hle :
          |value - sourceValue source| / rho ≤ 4 := by
        apply (div_le_iff₀ hrho).2
        nlinarith
      linarith
    have hfloor :
        |Int.floor (value / rho) - sourceBin| ≤ 5 := by
      exact wz1_abs_floor_sub_lt_le (N := 5) (by norm_num) hratio
    exact Finset.mem_biUnion.mpr
      ⟨sourceBin, hsourceBinMem, by
        simp only [nearbyBins, Finset.mem_Icc]
        have hbounds := abs_le.mp hfloor
        omega⟩
  have hcardNat :
      (wz1Lemma23ScalarBins rho values).card ≤
        11 * sourceBins.card := by
    calc
      (wz1Lemma23ScalarBins rho values).card
          ≤ (sourceBins.biUnion nearbyBins).card :=
        Finset.card_le_card htargetSubset
      _ ≤ ∑ sourceBin ∈ sourceBins,
          (nearbyBins sourceBin).card :=
        Finset.card_biUnion_le
      _ = ∑ _sourceBin ∈ sourceBins, 11 := by
        apply Finset.sum_congr rfl
        intro sourceBin _
        exact hnearbyCard sourceBin
      _ = 11 * sourceBins.card := by
        simp [mul_comm]
  have hcardENN :
      ((wz1Lemma23ScalarBins rho values).card : ENNReal) ≤
        11 * (sourceBins.card : ENNReal) := by
    exact_mod_cast hcardNat
  calc
    ((wz1Lemma23ScalarBins rho values).card : ENNReal)
        ≤ 11 * (sourceBins.card : ENNReal) :=
      hcardENN
    _ ≤ 11 *
        (12 * C * Kakeya.realRpowENN (1 / rho) alpha) := by
      gcongr
    _ = 132 * C *
        Kakeya.realRpowENN (1 / rho) alpha := by
      ring

end

end Kakeya.Assouad
