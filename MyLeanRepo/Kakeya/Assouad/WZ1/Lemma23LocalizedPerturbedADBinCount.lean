import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedADBinCount
import MyLeanRepo.Kakeya.Assouad.WZ1.NeighborPackingBound

/-!
# Localized perturbed AD-bin count for WZ1 Lemma 23

The genuine scalar values lie in one radius-`R` portion of a one-dimensional
AD set.  Snapping a genuine slice point to its spatial-cell center changes the
scalar coordinate by at most `4 * rho`.  The localized source bins cost a
factor three, and each source bin has at most eleven possible snapped target
bins, giving the absolute factor `33`.
-/

namespace Kakeya.Assouad

noncomputable section

/--
If every target value is within `4 * rho` of a source value in one localized
AD ball, then the target occupies at most
`33 * C * (R / rho)^alpha` integer `rho`-mesh bins.
-/
theorem wz1_lemma23_localized_perturbed_ad_bin_count_direct
    (rho R alpha : ℝ) (C : ENNReal)
    (E : Set ℝ) (values : Finset ℝ) (center : ℝ)
    (hAD : IsADSet1 E rho alpha C)
    (hrho_R : rho ≤ R) (hR_one : R ≤ 1)
    (hclose :
      ∀ value ∈ values,
        ∃ sourceValue ∈ E ∩ Metric.closedBall center R,
          |value - sourceValue| ≤ 4 * rho) :
    ((wz1Lemma23ScalarBins rho values).card : ENNReal) ≤
      33 * C * Kakeya.realRpowENN (R / rho) alpha := by
  classical
  have hrho : 0 < rho := hAD.1
  let sourceValue : {value // value ∈ values} → ℝ :=
    fun value => Classical.choose (hclose value.1 value.2)
  have hsourceValue :
      ∀ value : {value // value ∈ values},
        sourceValue value ∈ E ∩ Metric.closedBall center R ∧
          |value.1 - sourceValue value| ≤ 4 * rho := by
    intro value
    exact Classical.choose_spec (hclose value.1 value.2)
  let sourceValues : Finset ℝ :=
    values.attach.image sourceValue
  have hsourceValues :
      (sourceValues : Set ℝ) ⊆
        E ∩ Metric.closedBall center R := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨source, _, rfl⟩
    exact (hsourceValue source).1
  have hsourceBins :=
    wz1_lemma23_localized_ad_bin_count
      rho R alpha C E sourceValues center
      hAD hrho_R hR_one hsourceValues
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
    have hsourceMem :
        sourceValue source ∈ sourceValues := by
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
        (3 * C * Kakeya.realRpowENN (R / rho) alpha) := by
      gcongr
    _ = 33 * C *
        Kakeya.realRpowENN (R / rho) alpha := by
      ring

/--
If a finite source set lies in one radius-`R` window of an `IsADSet1`, and
every target value is within `4 * rho` of that source set, then the target
occupies at most

`33 * C * (R / rho)^alpha`

`rho`-mesh bins.
-/
theorem wz1_lemma23_localized_perturbed_ad_bin_count
    (rho R alpha : ℝ) (C : ENNReal)
    (E : Set ℝ) (sourceValues targetValues : Finset ℝ)
    (center : ℝ)
    (hAD : IsADSet1 E rho alpha C)
    (hrho_R : rho ≤ R)
    (hR_one : R ≤ 1)
    (hsource :
      (sourceValues : Set ℝ) ⊆
        E ∩ Metric.closedBall center R)
    (hclose :
      ∀ value ∈ targetValues,
        ∃ sourceValue ∈ sourceValues,
          |value - sourceValue| ≤ 4 * rho) :
    ((wz1Lemma23ScalarBins rho targetValues).card : ENNReal) ≤
      33 * C * Kakeya.realRpowENN (R / rho) alpha := by
  apply wz1_lemma23_localized_perturbed_ad_bin_count_direct
    rho R alpha C E targetValues center hAD hrho_R hR_one
  intro value hvalue
  rcases hclose value hvalue with
    ⟨sourceValue, hsourceValue, hvalueClose⟩
  exact
    ⟨sourceValue, hsource (Finset.mem_coe.mpr hsourceValue),
      hvalueClose⟩

/--
Affine localized variant used by the actual local-grain coordinates.

The source AD set is covered at radius `rho`.  An affine map with
`|a| ≤ 4` sends each source cover ball into a radius-`4 * rho` interval, and
the additional snapping error is at most `4 * rho`.  Hence every source cover
center contributes at most nineteen target bins.
-/
theorem wz1_lemma23_localized_affine_perturbed_ad_bin_count
    (rho R alpha a b : ℝ) (C : ENNReal)
    (E : Set ℝ) (targetValues : Finset ℝ)
    (center : ℝ)
    (hAD : IsADSet1 E rho alpha C)
    (hrho_R : rho ≤ R)
    (hR_one : R ≤ 1)
    (ha : |a| ≤ 4)
    (hclose :
      ∀ value ∈ targetValues,
        ∃ sourceValue ∈ E ∩ Metric.closedBall center R,
          |value - (a * sourceValue + b)| ≤ 4 * rho) :
    ((wz1Lemma23ScalarBins rho targetValues).card : ENNReal) ≤
      19 * C * Kakeya.realRpowENN (R / rho) alpha := by
  classical
  rcases hAD with
    ⟨hrho, _halpha, _halphaOne, _hCone, _hbounded, hcover⟩
  by_cases hCtop : C = ⊤
  · rw [hCtop]
    have hrpowPos :
        0 < Kakeya.realRpowENN (R / rho) alpha := by
      apply ENNReal.ofReal_pos.mpr
      apply Real.rpow_pos_of_pos
      have hR : 0 < R := hrho.trans_le hrho_R
      positivity
    have htop :
        (19 : ENNReal) * ⊤ *
            Kakeya.realRpowENN (R / rho) alpha =
          ⊤ := by
      rw [ENNReal.mul_top (by norm_num)]
      exact ENNReal.top_mul hrpowPos.ne'
    rw [htop]
    exact le_top
  · let rhoNN : NNReal := ⟨rho, hrho.le⟩
    have hrpowNeTop :
        Kakeya.realRpowENN (R / rho) alpha ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    have hboundNeTop :
        C * Kakeya.realRpowENN (R / rho) alpha ≠ ⊤ :=
      ENNReal.mul_ne_top hCtop hrpowNeTop
    have hcoverBound :
        (↑(Metric.externalCoveringNumber rhoNN
          (E ∩ Metric.closedBall center R)) : ENNReal) ≤
            C * Kakeya.realRpowENN (R / rho) alpha :=
      hcover rho hrho.le le_rfl (by linarith)
        center R hrho_R hR_one
    have hfinite :
        Metric.externalCoveringNumber rhoNN
          (E ∩ Metric.closedBall center R) ≠ ⊤ := by
      intro htop
      rw [htop] at hcoverBound
      exact hboundNeTop (top_le_iff.mp hcoverBound)
    rcases
        exists_finset_cover_of_externalCoveringNumber hfinite with
      ⟨centers, hcentersCover, hcentersCard⟩
    have hcentersCardEq :
        (centers.card : ENNReal) =
          (↑(Metric.externalCoveringNumber rhoNN
            (E ∩ Metric.closedBall center R)) : ENNReal) := by
      exact_mod_cast hcentersCard
    have hcentersCardBound :
        (centers.card : ENNReal) ≤
          C * Kakeya.realRpowENN (R / rho) alpha := by
      rw [hcentersCardEq]
      exact hcoverBound
    rw [Metric.isCover_iff_subset_iUnion_closedBall] at hcentersCover
    let centerBin (sourceCenter : ℝ) : ℤ :=
      Int.floor ((a * sourceCenter + b) / rho)
    let nearbyBins (sourceCenter : ℝ) : Finset ℤ :=
      Finset.Icc
        (centerBin sourceCenter - 9)
        (centerBin sourceCenter + 9)
    have hnearbyCard :
        ∀ sourceCenter : ℝ,
          (nearbyBins sourceCenter).card = 19 := by
      intro sourceCenter
      simp [nearbyBins]
      omega
    have htargetSubset :
        wz1Lemma23ScalarBins rho targetValues ⊆
          centers.biUnion nearbyBins := by
      intro targetBin htargetBin
      rcases Finset.mem_image.mp htargetBin with
        ⟨value, hvalue, rfl⟩
      rcases hclose value hvalue with
        ⟨sourceValue, hsourceLocal, hvalueClose⟩
      have hsourceCover := hcentersCover hsourceLocal
      rcases Set.mem_iUnion₂.mp hsourceCover with
        ⟨sourceCenter, hsourceCenter, hsourceBall⟩
      have hsourceClose :
          |sourceValue - sourceCenter| ≤ rho := by
        rw [Metric.mem_closedBall, Real.dist_eq] at hsourceBall
        change |sourceValue - sourceCenter| ≤ rho at hsourceBall
        exact hsourceBall
      have haSourceClose :
          |a * sourceValue - a * sourceCenter| ≤ 4 * rho := by
        calc
          |a * sourceValue - a * sourceCenter|
              = |a| * |sourceValue - sourceCenter| := by
                rw [← mul_sub, abs_mul]
          _ ≤ 4 * rho := by gcongr
      have htotalClose :
          |value - (a * sourceCenter + b)| ≤ 8 * rho := by
        calc
          |value - (a * sourceCenter + b)|
              = |(value - (a * sourceValue + b)) +
                  (a * sourceValue - a * sourceCenter)| := by
                congr 1
                ring
          _ ≤ |value - (a * sourceValue + b)| +
                |a * sourceValue - a * sourceCenter| :=
            abs_add_le _ _
          _ ≤ 4 * rho + 4 * rho := by gcongr
          _ = 8 * rho := by ring
      have hratio :
          |value / rho -
              (a * sourceCenter + b) / rho| < 9 := by
        have hdiv :
            |value / rho -
                (a * sourceCenter + b) / rho| =
              |value - (a * sourceCenter + b)| / rho := by
          rw [← sub_div, abs_div, abs_of_pos hrho]
        rw [hdiv]
        have hle :
            |value - (a * sourceCenter + b)| / rho ≤ 8 := by
          apply (div_le_iff₀ hrho).2
          nlinarith
        linarith
      have hfloor :
          |Int.floor (value / rho) -
              centerBin sourceCenter| ≤ 9 := by
        exact wz1_abs_floor_sub_lt_le (N := 9) (by norm_num) hratio
      exact Finset.mem_biUnion.mpr
        ⟨sourceCenter, hsourceCenter, by
          simp only [nearbyBins, Finset.mem_Icc]
          have hbounds := abs_le.mp hfloor
          omega⟩
    have hcardNat :
        (wz1Lemma23ScalarBins rho targetValues).card ≤
          19 * centers.card := by
      calc
        (wz1Lemma23ScalarBins rho targetValues).card
            ≤ (centers.biUnion nearbyBins).card :=
          Finset.card_le_card htargetSubset
        _ ≤ ∑ sourceCenter ∈ centers,
            (nearbyBins sourceCenter).card :=
          Finset.card_biUnion_le
        _ = ∑ _sourceCenter ∈ centers, 19 := by
          apply Finset.sum_congr rfl
          intro sourceCenter _
          exact hnearbyCard sourceCenter
        _ = 19 * centers.card := by
          simp [mul_comm]
    have hcardENN :
        ((wz1Lemma23ScalarBins rho targetValues).card : ENNReal) ≤
          19 * (centers.card : ENNReal) := by
      exact_mod_cast hcardNat
    calc
      ((wz1Lemma23ScalarBins rho targetValues).card : ENNReal)
          ≤ 19 * (centers.card : ENNReal) :=
        hcardENN
      _ ≤ 19 *
          (C * Kakeya.realRpowENN (R / rho) alpha) := by
        gcongr
      _ = 19 * C *
          Kakeya.realRpowENN (R / rho) alpha := by
        ring

end

end Kakeya.Assouad
