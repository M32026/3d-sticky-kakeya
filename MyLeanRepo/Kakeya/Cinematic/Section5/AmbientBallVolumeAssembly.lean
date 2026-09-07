import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientBallRestriction

/-!
# Assemble volume bounds over ambient balls
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Cinematic

lemma ambient_ball_volume_assembly
    {E : Set (ℝ × ℝ)}
    {F : FiniteFunctionFamily}
    {centers : Finset C2Function}
    (bins : C2Function → Set (ℝ × ℝ))
    (ambient : C2Function → FiniteFunctionFamily)
    {D : ℝ} {B : ENNReal}
    (hcover : E ⊆ ⋃ c ∈ (centers : Set C2Function), bins c)
    (hlocal : ∀ c ∈ centers,
      volume (bins c) ≤ B * (ambient c).card)
    (hcard : (∑ c ∈ centers, ((ambient c).card : ℝ)) ≤
      D ^ 3 * (F.card : ℝ)) :
    volume E ≤ B * ENNReal.ofReal (D ^ 3 * (F.card : ℝ)) := by
  calc
    volume E ≤ volume (⋃ c ∈ (centers : Set C2Function), bins c) :=
      measure_mono hcover
    _ ≤ ∑ c ∈ centers, volume (bins c) :=
      measure_biUnion_finset_le centers bins
    _ ≤ ∑ c ∈ centers, B * (ambient c).card := by
      exact Finset.sum_le_sum fun c hc => hlocal c hc
    _ = B * ∑ c ∈ centers, ((ambient c).card : ENNReal) := by
      rw [Finset.mul_sum]
    _ = B * ENNReal.ofReal
        (∑ c ∈ centers, ((ambient c).card : ℝ)) := by
      congr 1
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro c hc
        simp
      · intro c hc
        positivity
    _ ≤ B * ENNReal.ofReal (D ^ 3 * (F.card : ℝ)) := by
      gcongr

lemma ambient_ball_volume_assembly_of_katz_tao
    {E : Set (ℝ × ℝ)}
    {F : FiniteFunctionFamily}
    {centers : Finset C2Function}
    (bins : C2Function → Set (ℝ × ℝ))
    (ambient : C2Function → FiniteFunctionFamily)
    {D delta C_KT : ℝ} {B : ENNReal}
    (hD : 0 ≤ D)
    (hdelta : 0 < delta)
    (hKT : F.HasKatzTaoBound delta C_KT)
    (hcover : E ⊆ ⋃ c ∈ (centers : Set C2Function), bins c)
    (hlocal : ∀ c ∈ centers,
      volume (bins c) ≤ B * (ambient c).card)
    (hcard : (∑ c ∈ centers, ((ambient c).card : ℝ)) ≤
      D ^ 3 * (F.card : ℝ)) :
    volume E ≤
      B * ENNReal.ofReal (D ^ 3 * (C_KT / delta)) := by
  have hglobal :=
    ambient_ball_volume_assembly bins ambient hcover hlocal hcard
  refine hglobal.trans ?_
  have hD3_nonneg : 0 ≤ D ^ 3 := pow_nonneg hD 3
  have hreal :
      D ^ 3 * (F.card : ℝ) ≤ D ^ 3 * (C_KT / delta) :=
    mul_le_mul_of_nonneg_left hKT.1 hD3_nonneg
  exact mul_le_mul_left' (ENNReal.ofReal_le_ofReal hreal) B

lemma ambient_ball_volume_assembly_to_target
    {E : Set (ℝ × ℝ)}
    {F : FiniteFunctionFamily}
    {centers : Finset C2Function}
    (bins : C2Function → Set (ℝ × ℝ))
    (ambient : C2Function → FiniteFunctionFamily)
    {D delta C_KT target : ℝ} {B : ENNReal}
    (hD : 0 ≤ D)
    (hdelta : 0 < delta)
    (hKT : F.HasKatzTaoBound delta C_KT)
    (hB_ne_top : B ≠ ⊤)
    (htarget : 0 ≤ target)
    (hcover : E ⊆ ⋃ c ∈ (centers : Set C2Function), bins c)
    (hlocal : ∀ c ∈ centers,
      volume (bins c) ≤ B * (ambient c).card)
    (hcard : (∑ c ∈ centers, ((ambient c).card : ℝ)) ≤
      D ^ 3 * (F.card : ℝ))
    (habsorb :
      B.toReal * (D ^ 3 * (C_KT / delta)) ≤ target) :
    volume E ≤ ENNReal.ofReal target := by
  have hglobal :=
    ambient_ball_volume_assembly_of_katz_tao
      bins ambient hD hdelta hKT hcover hlocal hcard
  have hfactor_nonneg : 0 ≤ D ^ 3 * (C_KT / delta) := by
    have hcard_nonneg : 0 ≤ (F.card : ℝ) := by positivity
    have hKT_nonneg : 0 ≤ C_KT / delta :=
      hcard_nonneg.trans hKT.1
    exact mul_nonneg (pow_nonneg hD 3) hKT_nonneg
  have hB_mul_ne_top :
      B * ENNReal.ofReal (D ^ 3 * (C_KT / delta)) ≠ ⊤ :=
    ENNReal.mul_ne_top hB_ne_top ENNReal.ofReal_ne_top
  have hreal :
      (B * ENNReal.ofReal (D ^ 3 * (C_KT / delta))).toReal ≤
        (ENNReal.ofReal target).toReal := by
    simp only [ENNReal.toReal_mul, hB_ne_top, ENNReal.toReal_ofReal,
      hfactor_nonneg, htarget]
    exact habsorb
  exact hglobal.trans
    ((ENNReal.toReal_le_toReal
      hB_mul_ne_top ENNReal.ofReal_ne_top).mp hreal)

end Kakeya.Cinematic
