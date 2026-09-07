import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicPieceVolumeRefinementInputs

/-!
# Positivity and finiteness of retained level sets
-/

open MeasureTheory

namespace Kakeya.Cinematic

lemma retained_measure_pos
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E₀ E₂ : Set α} {loss : ENNReal}
    (hE₀_pos : 0 < μ E₀)
    (hretained : μ E₀ ≤ loss * μ E₂) :
    0 < μ E₂ := by
  by_contra h
  have hE₂_zero : μ E₂ = 0 := by
    simpa using h
  rw [hE₂_zero, mul_zero] at hretained
  have hE₀_zero : μ E₀ = 0 := nonpos_iff_eq_zero.mp hretained
  exact (ne_of_gt hE₀_pos) hE₀_zero

lemma retained_measure_lt_top
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E₀ E₂ : Set α}
    (hE₂_sub : E₂ ⊆ E₀)
    (hE₀_finite : μ E₀ < ⊤) :
    μ E₂ < ⊤ :=
  (measure_mono hE₂_sub).trans_lt hE₀_finite

lemma exists_retained_half_mass_cutoff
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E₀ E₂ : Set α} {loss : ENNReal} {N : ℕ}
    (hN : 0 < N)
    (hE₂_sub : E₂ ⊆ E₀)
    (hE₀_pos : 0 < μ E₀)
    (hE₀_finite : μ E₀ < ⊤)
    (hretained : μ E₀ ≤ loss * μ E₂) :
    ∃ lower : ENNReal,
      0 < lower ∧
      lower ≠ ⊤ ∧
      2 * ((N : ENNReal) * lower) = μ E₂ := by
  apply exists_positive_finite_half_mass_cutoff hN
  · exact retained_measure_pos hE₀_pos hretained
  · exact (retained_measure_lt_top hE₂_sub hE₀_finite).ne

lemma retained_small_volume
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E₀ E₂ : Set α} {loss target : ENNReal}
    (hloss_ne_zero : loss ≠ 0)
    (hloss_ne_top : loss ≠ ⊤)
    (hretained : μ E₀ ≤ loss * μ E₂)
    (hsmall : μ E₂ ≤ target / loss) :
    μ E₀ ≤ target := by
  calc
    μ E₀ ≤ loss * μ E₂ := hretained
    _ ≤ loss * (target / loss) := by gcongr
    _ = target := ENNReal.mul_div_cancel hloss_ne_zero hloss_ne_top

end Kakeya.Cinematic
