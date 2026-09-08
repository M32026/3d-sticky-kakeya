import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.IntersectionBound
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslateTubeGeometry
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Transverse translation anti-concentration

This module provides the translation component of the rigid-motion
anti-concentration argument.

## Main results

- `transverse_bad_translations_volume`: volume of translations causing overlap
  is at most `2 * U.volume` (Markov + convolution identity).
- `transverse_bad_translations_ball`: the same bound after restricting the
  translation parameter to a ball.

These lemmas supply only the `O(delta^2)` transverse-position factor.  They do
not by themselves prove the `O(delta^4)` rigid-motion collision bound, which
also requires a genuine `O(delta^2)` directional estimate.
-/

noncomputable section

open MeasureTheory Kakeya.Streamlined Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.GeneralizedFrostman

/-! ### Measurability of intersection volume function -/

/-- The function `d ↦ volume(T ∩ translateSet U d)` is measurable. -/
lemma measurable_intersection_volume {T U : Set Point3}
    (hT : MeasurableSet T) (hU : MeasurableSet U) :
    Measurable (fun d : Point3 => volume (T ∩ translateSet U d)) := by
  let S : Set (Point3 × Point3) :=
    (Set.univ ×ˢ T) ∩ (fun p : Point3 × Point3 => p.2 - p.1) ⁻¹' U
  have hS : MeasurableSet S :=
    (MeasurableSet.univ.prod hT).inter (hU.preimage (by fun_prop))
  let g : Point3 × Point3 → ENNReal := Set.indicator S (fun _ => 1)
  have hg : Measurable g := by fun_prop
  have h1 : ∀ d : Point3, {x : Point3 | (d, x) ∈ S} = T ∩ translateSet U d := by
    intro d
    ext x
    simp only [S, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hxT, h2⟩
      exact ⟨hxT, ⟨x - d, h2, by abel⟩⟩
    · rintro ⟨hxT, y, hy, rfl⟩
      exact ⟨hxT, by simpa using hy⟩
  have h_eq : ∀ d, volume (T ∩ translateSet U d) = ∫⁻ x : Point3, g (d, x) := by
    intro d
    have h_mk : Measurable (fun x : Point3 => (d, x)) := by fun_prop
    have hS_d : MeasurableSet {x : Point3 | (d, x) ∈ S} :=
      hS.preimage h_mk
    have h3 : (fun x : Point3 => g (d, x)) =
        Set.indicator {x : Point3 | (d, x) ∈ S} (fun _ => 1) := by
      funext x
      simp [g, Set.indicator]
      <;> tauto
    have h2 : ∫⁻ x : Point3, g (d, x) = volume {x : Point3 | (d, x) ∈ S} := by
      rw [h3]
      exact lintegral_indicator_one hS_d
    rw [h2, h1 d]
  have h_main : Measurable (fun d : Point3 => ∫⁻ x : Point3, g (d, x)) :=
    hg.lintegral_prod_right'
  have h3 : (fun d : Point3 => volume (T ∩ translateSet U d)) =
      fun d : Point3 => ∫⁻ x : Point3, g (d, x) := by
    funext d; exact h_eq d
  rw [h3]
  exact h_main

/-! ### Transverse overlap bound -/

/-- Volume of translations v for which `translateTube T v` is NOT essentially
distinct from U is at most `2 * U.volume`.

This is the transverse overlap bound: regardless of direction alignment,
the set of translations causing a conflict has measure O(δ²).
-/
lemma transverse_bad_translations_volume {δ : ℝ} (hδ : 0 < δ)
    (T U : Kakeya.DeltaTube δ) :
    volume {v : Point3 | ¬ (translateTube T v).EssentiallyDistinct U} ≤
      2 * U.volume := by
  let f : Point3 → ENNReal := fun v =>
    volume ((translateTube T v).carrier ∩ U.carrier)
  have hT_meas : MeasurableSet T.carrier :=
    IsClosed.measurableSet Metric.isClosed_cthickening
  have hU_meas : MeasurableSet U.carrier :=
    IsClosed.measurableSet Metric.isClosed_cthickening
  have h_f_eq : ∀ v, f v = volume (U.carrier ∩ translateSet T.carrier v) := by
    intro v
    dsimp only [f]
    have h1 : (translateTube T v).carrier = translateSet T.carrier v :=
      translateTube_carrier T v
    rw [h1]
    have h2 : (translateSet T.carrier v ∩ U.carrier) =
        (U.carrier ∩ translateSet T.carrier v) := by
      ext x; simp [and_comm]
    rw [h2]
  have h_meas : Measurable f := by
    have h3 : Measurable (fun v : Point3 =>
        volume (U.carrier ∩ translateSet T.carrier v)) :=
      measurable_intersection_volume hU_meas hT_meas
    have h4 : f = fun v : Point3 =>
        volume (U.carrier ∩ translateSet T.carrier v) := by
      funext v; exact h_f_eq v
    rw [h4]
    exact h3
  have hT_ne_top : volume T.carrier ≠ ⊤ := by
    have h : T.volume = Kakeya.deltaTubeVolume δ :=
      RandomTranslation.tube_volume_eq_deltaTubeVolume T
    have h' : volume T.carrier = T.volume := by rfl
    rw [h', h]
    exact RandomTranslation.deltaTubeVolume_ne_top
  have h_conv : ∫⁻ v, f v = T.volume * U.volume := by
    have h5 : ∫⁻ v, f v = ∫⁻ v, volume (U.carrier ∩ translateSet T.carrier v) := by
      apply lintegral_congr
      intro v; exact h_f_eq v
    rw [h5]
    have h6 := convolution_intersection_volume hU_meas hT_meas hT_ne_top
    rw [mul_comm] at h6
    exact h6
  have hV_pos : 0 < T.volume := by
    have h : T.volume = Kakeya.deltaTubeVolume δ :=
      RandomTranslation.tube_volume_eq_deltaTubeVolume T
    rw [h]
    exact RandomTranslation.deltaTubeVolume_pos hδ
  have hV_ne_top : T.volume ≠ ⊤ := by
    have h : T.volume = Kakeya.deltaTubeVolume δ :=
      RandomTranslation.tube_volume_eq_deltaTubeVolume T
    rw [h]
    exact RandomTranslation.deltaTubeVolume_ne_top
  let ε : ENNReal := T.volume / 2
  have hε_pos : ε ≠ 0 := by
    dsimp only [ε]
    exact (ENNReal.div_pos hV_pos.ne' (by norm_num)).ne'
  have hε_ne_top : ε ≠ ⊤ := by
    dsimp only [ε]
    exact ENNReal.div_ne_top hV_ne_top (by norm_num)
  have h_bad_subset : {v : Point3 | ¬ (translateTube T v).EssentiallyDistinct U} ⊆
      {v : Point3 | ε ≤ f v} := by
    intro v hv
    dsimp only [Kakeya.DeltaTube.EssentiallyDistinct] at hv
    have h7 : ¬ (f v ≤ (2 : ENNReal)⁻¹ * max (translateTube T v).volume U.volume) := by
      simpa [f] using hv
    have h8 : (translateTube T v).volume = T.volume := translateTube_volume T v
    rw [h8] at h7
    have h9 : ε ≤ (2 : ENNReal)⁻¹ * max T.volume U.volume := by
      dsimp only [ε]
      have h10 : max T.volume U.volume ≥ T.volume := le_max_left _ _
      have h11 : T.volume / 2 ≤ (2 : ENNReal)⁻¹ * max T.volume U.volume := by
        calc
          T.volume / 2 = (2 : ENNReal)⁻¹ * T.volume := by
            simp [div_eq_mul_inv] <;> ring
          _ ≤ (2 : ENNReal)⁻¹ * max T.volume U.volume := by
            gcongr
      exact h11
    by_contra h12
    have h13 : ¬ (ε ≤ f v) := h12
    have h14 : f v < ε := lt_of_not_ge h13
    have h15 : f v ≤ (2 : ENNReal)⁻¹ * max T.volume U.volume :=
      le_trans h14.le h9
    exact h7 h15
  have h_markov : volume {v : Point3 | ε ≤ f v} ≤ (∫⁻ v, f v) / ε :=
    MeasureTheory.meas_ge_le_lintegral_div h_meas.aemeasurable hε_pos hε_ne_top
  have h_final : (T.volume * U.volume) / ε = 2 * U.volume := by
    dsimp only [ε]
    have h_comm : (T.volume / 2) = T.volume * (2 : ENNReal)⁻¹ := by
      simp [div_eq_mul_inv] <;> ring
    rw [h_comm]
    have h1 : (T.volume * U.volume) / (T.volume * (2 : ENNReal)⁻¹) =
        U.volume / (2 : ENNReal)⁻¹ :=
      ENNReal.mul_div_mul_left U.volume (2 : ENNReal)⁻¹ hV_pos.ne' hV_ne_top
    rw [h1]
    have h2 : U.volume / (2 : ENNReal)⁻¹ = 2 * U.volume := by
      simp [div_eq_mul_inv] <;> ring
    rw [h2]
  calc
    volume {v : Point3 | ¬ (translateTube T v).EssentiallyDistinct U}
      ≤ volume {v : Point3 | ε ≤ f v} := measure_mono h_bad_subset
    _ ≤ (∫⁻ v, f v) / ε := h_markov
    _ = (T.volume * U.volume) / ε := by rw [h_conv]
    _ = 2 * U.volume := h_final

/-- Restricted to a ball, the volume of bad translations is still at most
`2 * U.volume`. -/
lemma transverse_bad_translations_ball {δ : ℝ} (hδ : 0 < δ)
    (T U : Kakeya.DeltaTube δ) {ρ : ℝ} (_hρ : 0 ≤ ρ) :
    volume ({v : Point3 | ¬ (translateTube T v).EssentiallyDistinct U} ∩
      Metric.closedBall (0 : Point3) ρ) ≤ 2 * U.volume := by
  have h1 : ({v : Point3 | ¬ (translateTube T v).EssentiallyDistinct U} ∩
      Metric.closedBall (0 : Point3) ρ) ⊆
      {v : Point3 | ¬ (translateTube T v).EssentiallyDistinct U} := by
    simp
  calc
    volume (_ ∩ _) ≤ volume {v : Point3 | ¬ (translateTube T v).EssentiallyDistinct U} :=
      measure_mono h1
    _ ≤ 2 * U.volume := transverse_bad_translations_volume hδ T U

end Kakeya.Streamlined.GeneralizedFrostman
