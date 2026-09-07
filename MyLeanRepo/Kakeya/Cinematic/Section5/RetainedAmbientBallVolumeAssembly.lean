import MyLeanRepo.Kakeya.Cinematic.Section5.RetainedAmbientBallVolumeAssemblyInputs

/-!
# Retained ambient-ball volume assembly
-/

open MeasureTheory

namespace Kakeya.Cinematic

lemma retained_ambient_local_target_absorption
    (logLoss globalFactor target : ℝ)
    (hlogLoss : 0 < logLoss)
    (hglobalFactor : 0 < globalFactor)
    (htarget : 0 ≤ target) :
    logLoss *
        (ENNReal.ofReal
          (target / (logLoss * globalFactor))).toReal *
        globalFactor ≤
      target := by
  have hdenominator : 0 < logLoss * globalFactor :=
    mul_pos hlogLoss hglobalFactor
  rw [ENNReal.toReal_ofReal (div_nonneg htarget hdenominator.le)]
  have hidentity :
      logLoss * (target / (logLoss * globalFactor)) *
          globalFactor =
        target := by
    field_simp [hlogLoss.ne', hglobalFactor.ne']
  rw [hidentity]

lemma retained_ambient_local_target_witness
    (logLoss globalFactor target : ℝ)
    (hlogLoss : 0 < logLoss)
    (hglobalFactor : 0 < globalFactor)
    (htarget : 0 ≤ target) :
    ∃ B : ENNReal,
      B ≠ ⊤ ∧
      B =
        ENNReal.ofReal
          (target / (logLoss * globalFactor)) ∧
      logLoss * B.toReal * globalFactor ≤ target := by
  refine
    ⟨ENNReal.ofReal
      (target / (logLoss * globalFactor)),
      ENNReal.ofReal_ne_top, rfl, ?_⟩
  exact retained_ambient_local_target_absorption
    logLoss globalFactor target hlogLoss hglobalFactor htarget

theorem retained_ambient_ball_volume_assembly :
    RetainedAmbientBallVolumeAssemblyStatement := by
  intro E₀ E₂ F centers bins ambient D delta C_KT logLoss target B
    hD hdelta hlogLoss_nonneg hKT hB_ne_top htarget_nonneg hret hcover hlocal
    hcard habsorb
  set X := D ^ 3 * (C_KT / delta) with hX
  have hE2 : volume E₂ ≤ B * ENNReal.ofReal X :=
    ambient_ball_volume_assembly_of_katz_tao
      bins ambient hD hdelta hKT hcover hlocal hcard
  have hfactor_nonneg : 0 ≤ X := by
    have hcard_nonneg : 0 ≤ (F.card : ℝ) := by positivity
    have hKT_nonneg : 0 ≤ C_KT / delta := hcard_nonneg.trans hKT.1
    exact mul_nonneg (pow_nonneg hD 3) hKT_nonneg
  have hlogfactor_nonneg : 0 ≤ logLoss * X :=
    mul_nonneg hlogLoss_nonneg hfactor_nonneg
  have h_mul_eq :
      ENNReal.ofReal logLoss * (B * ENNReal.ofReal X) =
      B * ENNReal.ofReal (logLoss * X) := by
    have h1 : ENNReal.ofReal logLoss * (B * ENNReal.ofReal X) =
        B * (ENNReal.ofReal logLoss * ENNReal.ofReal X) :=
      mul_left_comm (ENNReal.ofReal logLoss) B (ENNReal.ofReal X)
    rw [h1, ← ENNReal.ofReal_mul hlogLoss_nonneg]
  have h_main : volume E₀ ≤ B * ENNReal.ofReal (logLoss * X) := by
    calc
      volume E₀ ≤ ENNReal.ofReal logLoss * volume E₂ := hret
      _ ≤ ENNReal.ofReal logLoss * (B * ENNReal.ofReal X) := by gcongr
      _ = B * ENNReal.ofReal (logLoss * X) := h_mul_eq
  have hB_mul_ne_top :
      B * ENNReal.ofReal (logLoss * X) ≠ ⊤ :=
    ENNReal.mul_ne_top hB_ne_top ENNReal.ofReal_ne_top
  have habsorb' : B.toReal * (logLoss * X) ≤ target := by
    have h_eq : B.toReal * (logLoss * X) = logLoss * B.toReal * X := by ring
    rw [h_eq]
    exact habsorb
  have hreal :
      (B * ENNReal.ofReal (logLoss * X)).toReal ≤
        (ENNReal.ofReal target).toReal := by
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal,
      hlogfactor_nonneg, htarget_nonneg]
    exact habsorb'
  exact h_main.trans
    ((ENNReal.toReal_le_toReal
      hB_mul_ne_top ENNReal.ofReal_ne_top).mp hreal)

lemma retained_ambient_ball_volume_assembly_of_scaled_local
    {E₀ E₂ : Set (ℝ × ℝ)}
    {F : FiniteFunctionFamily}
    {centers : Finset C2Function}
    (bins : C2Function → Set (ℝ × ℝ))
    (ambient : C2Function → FiniteFunctionFamily)
    {D delta C_KT outerLoss localTarget target : ℝ}
    (hD : 0 ≤ D)
    (hdelta : 0 < delta)
    (houterLoss : 0 ≤ outerLoss)
    (hKT : F.HasKatzTaoBound delta C_KT)
    (hlocalTarget : 0 ≤ localTarget)
    (htarget : 0 ≤ target)
    (hret :
      volume E₀ ≤ ENNReal.ofReal outerLoss * volume E₂)
    (hcover :
      E₂ ⊆ ⋃ c ∈ (centers : Set C2Function), bins c)
    (hlocal :
      ∀ c ∈ centers,
        ENNReal.ofReal outerLoss * volume (bins c) ≤
          ENNReal.ofReal localTarget * (ambient c).card)
    (hcard :
      (∑ c ∈ centers, ((ambient c).card : ℝ)) ≤
        D ^ 3 * (F.card : ℝ))
    (habsorb :
      localTarget * (D ^ 3 * (C_KT / delta)) ≤ target) :
    volume E₀ ≤ ENNReal.ofReal target := by
  have hE₂ :
      ENNReal.ofReal outerLoss * volume E₂ ≤
        ENNReal.ofReal localTarget *
          ENNReal.ofReal (D ^ 3 * (C_KT / delta)) := by
    calc
      ENNReal.ofReal outerLoss * volume E₂ ≤
          ENNReal.ofReal outerLoss *
            volume (⋃ c ∈ (centers : Set C2Function), bins c) := by
        gcongr
      _ ≤
          ENNReal.ofReal outerLoss *
            ∑ c ∈ centers, volume (bins c) := by
        gcongr
        exact measure_biUnion_finset_le centers bins
      _ =
          ∑ c ∈ centers,
            ENNReal.ofReal outerLoss * volume (bins c) := by
        rw [Finset.mul_sum]
      _ ≤
          ∑ c ∈ centers,
            ENNReal.ofReal localTarget * (ambient c).card := by
        exact Finset.sum_le_sum fun c hc => hlocal c hc
      _ =
          ENNReal.ofReal localTarget *
            ENNReal.ofReal
              (∑ c ∈ centers, ((ambient c).card : ℝ)) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [ENNReal.ofReal_sum_of_nonneg]
        · apply Finset.sum_congr rfl
          intro c hc
          simp
        · intro c hc
          positivity
      _ ≤
          ENNReal.ofReal localTarget *
            ENNReal.ofReal (D ^ 3 * (F.card : ℝ)) := by
        gcongr
      _ ≤
          ENNReal.ofReal localTarget *
            ENNReal.ofReal (D ^ 3 * (C_KT / delta)) := by
        gcongr
        exact hKT.1
  have hglobalNonneg :
      0 ≤ D ^ 3 * (C_KT / delta) := by
    have hcardNonneg : 0 ≤ (F.card : ℝ) := by positivity
    have hKTNonneg : 0 ≤ C_KT / delta :=
      hcardNonneg.trans hKT.1
    exact mul_nonneg (pow_nonneg hD 3) hKTNonneg
  calc
    volume E₀ ≤ ENNReal.ofReal outerLoss * volume E₂ := hret
    _ ≤
        ENNReal.ofReal localTarget *
          ENNReal.ofReal (D ^ 3 * (C_KT / delta)) := hE₂
    _ = ENNReal.ofReal
          (localTarget * (D ^ 3 * (C_KT / delta))) := by
      rw [← ENNReal.ofReal_mul hlocalTarget]
    _ ≤ ENNReal.ofReal target :=
      ENNReal.ofReal_le_ofReal habsorb

lemma retained_ambient_ball_volume_assembly_from_local_target
    {E₀ E₂ : Set (ℝ × ℝ)}
    {F : FiniteFunctionFamily}
    {centers : Finset C2Function}
    (bins : C2Function → Set (ℝ × ℝ))
    (ambient : C2Function → FiniteFunctionFamily)
    {D delta C_KT logLoss target : ℝ}
    (hD : 0 < D)
    (hdelta : 0 < delta)
    (hC_KT : 0 < C_KT)
    (hlogLoss : 0 < logLoss)
    (hKT : F.HasKatzTaoBound delta C_KT)
    (htarget : 0 ≤ target)
    (hret :
      volume E₀ ≤ ENNReal.ofReal logLoss * volume E₂)
    (hcover :
      E₂ ⊆ ⋃ c ∈ (centers : Set C2Function), bins c)
    (hlocal :
      ∀ c ∈ centers,
        volume (bins c) ≤
          ENNReal.ofReal
              (target /
                (logLoss * (D ^ 3 * (C_KT / delta)))) *
            (ambient c).card)
    (hcard :
      (∑ c ∈ centers, ((ambient c).card : ℝ)) ≤
        D ^ 3 * (F.card : ℝ)) :
    volume E₀ ≤ ENNReal.ofReal target := by
  have hglobalFactor :
      0 < D ^ 3 * (C_KT / delta) := by
    positivity
  exact retained_ambient_ball_volume_assembly
    bins ambient hD.le hdelta hlogLoss.le hKT
    ENNReal.ofReal_ne_top htarget hret hcover hlocal hcard
    (retained_ambient_local_target_absorption
      logLoss (D ^ 3 * (C_KT / delta)) target
      hlogLoss hglobalFactor htarget)

end Kakeya.Cinematic
