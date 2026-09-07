import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# The coarse rectangle remains in the central parameter interval
-/

namespace Kakeya.Cinematic

theorem fine_to_coarse_central
    (hContainment : FineToCoarseContainmentStatement) :
    FineToCoarseCentralStatement := by
  intro K delta t Delta C_R hK hdelta hdeltaDelta hDeltaT ht hCR hCRlarge
    I hI R hRquarter hmid
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hContainmentScale : 256 * K ^ 2 ≤ C_R := by
    nlinarith [sq_nonneg K]
  obtain ⟨S, hSfunction, hSmidpoint, hRS⟩ :=
    hContainment hK hdelta hdeltaDelta hDeltaT ht hCR
      hContainmentScale hI hRquarter
  refine ⟨S, hSfunction, hSmidpoint, hRS, ?_⟩
  have hsqrtCR : 96 * K ≤ Real.sqrt C_R := by
    have hsqrtCRsq : (Real.sqrt C_R) ^ 2 = C_R :=
      Real.sq_sqrt hCR.le
    nlinarith [Real.sqrt_nonneg C_R]
  have hratio : Delta / (C_R * t) ≤ 1 / C_R := by
    have hdenom : 0 < C_R * t := mul_pos hCR ht
    calc
      Delta / (C_R * t) ≤ t / (C_R * t) := by
        exact div_le_div_of_nonneg_right hDeltaT hdenom.le
      _ = 1 / C_R := by
        field_simp [hCR.ne', ht.ne']
  have hSlen_le : S.interval.length ≤ 1 / (96 * K) := by
    rw [S.interval_length]
    have hsqrtRatio :
        Real.sqrt (Delta / (C_R * t)) ≤ Real.sqrt (1 / C_R) :=
      Real.sqrt_le_sqrt hratio
    have hsqrtRecip : Real.sqrt (1 / C_R) = 1 / Real.sqrt C_R := by
      rw [Real.sqrt_div (by norm_num : 0 ≤ (1 : ℝ))]
      simp
    rw [hsqrtRecip] at hsqrtRatio
    calc
      Real.sqrt (Delta / (C_R * t)) ≤ 1 / Real.sqrt C_R := hsqrtRatio
      _ ≤ 1 / (96 * K) := by
        exact one_div_le_one_div_of_le (by positivity) hsqrtCR
  have hSlen_I : S.interval.length ≤ I.length / 8 := by
    calc
      S.interval.length ≤ 1 / (96 * K) := hSlen_le
      _ = (1 / (12 * K)) / 8 := by
        field_simp [hKpos.ne'] <;> norm_num
      _ ≤ I.length / 8 := by
        gcongr
        simpa [one_div] using hI.1
  intro x hx
  have hxmid :
      |(x : ℝ) - S.interval.midpoint| ≤ S.interval.length / 2 := by
    rw [abs_le]
    simp only [ParameterInterval.carrier, Set.mem_setOf_eq] at hx
    simp only [ParameterInterval.midpoint, ParameterInterval.length]
    constructor <;> linarith
  have hxmidR :
      |(x : ℝ) - R.interval.midpoint| ≤ I.length / 16 := by
    rw [← hSmidpoint]
    calc
      |(x : ℝ) - S.interval.midpoint| ≤ S.interval.length / 2 := hxmid
      _ ≤ (I.length / 8) / 2 := by gcongr
      _ = I.length / 16 := by ring
  have hxI :
      |(x : ℝ) - I.midpoint| ≤ I.length / 8 := by
    calc
      |(x : ℝ) - I.midpoint| =
          |((x : ℝ) - R.interval.midpoint) +
            (R.interval.midpoint - I.midpoint)| := by ring_nf
      _ ≤ |(x : ℝ) - R.interval.midpoint| +
          |R.interval.midpoint - I.midpoint| := abs_add_le _ _
      _ ≤ I.length / 16 + I.length / 16 := add_le_add hxmidR hmid
      _ = I.length / 8 := by ring
  change |(x : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2
  convert hxI using 1 <;> ring

end Kakeya.Cinematic
