import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedMeasure.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Helper lemmas for smoothed-to-discrete thin tubes conversion

This module contains reusable definitions and lemmas used in the proof of
`wz1_smoothed_to_discrete_thin_tubes`.

## Main results

- `translatedBallMeasure`: uniform measure on a ball translated to a center
- `thickening_parallel_enlargement`: geometric tube enlargement under endpoint perturbation
- `smoothMeasure_prod_expansion`: product measure expansion for smoothed measures
- `markov_retention`: Markov bound retaining pairs above one-half mass
-/

noncomputable section

open MeasureTheory Set Metric Finset

open scoped ENNReal NNReal

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Uniform probability measure on the ball `B(a, ρ)`, obtained by translating
`ballUniformMeasure ρ` by `a`. -/
def translatedBallMeasure (ρ : ℝ) (hρ : 0 < ρ) (a : Point2) : ProbabilityMeasure Point2 :=
  (ballUniformMeasure ρ hρ).map (f := fun y : Point2 => a + y)
    (f_aemble := (by fun_prop : Measurable (fun y : Point2 => a + y)).aemeasurable)

/-- If `a ∈ ℓ`, `x ∈ B(a, ρ)`, `y ∈ B(b, ρ)`, and `b` is within distance `r` of `ℓ`,
then `y` is within distance `r + 2ρ` of the line through `x` parallel to `ℓ`. -/
lemma thickening_parallel_enlargement
    {r ρ : ℝ} {ℓ : AffineSubspace ℝ Point2}
    {a x : Point2} (ha : a ∈ ℓ) (hx : dist x a < ρ)
    {b y : Point2} (hb : dist y b < ρ)
    (h_b_in : b ∈ Metric.thickening r (ℓ : Set Point2)) :
    y ∈ Metric.thickening (r + 2 * ρ)
        (AffineSubspace.mk' x ℓ.direction : Set Point2) := by
  have h1 : ∃ (z : Point2), z ∈ (ℓ : Set Point2) ∧ dist b z < r :=
    Metric.mem_thickening_iff.mp h_b_in
  rcases h1 with ⟨z, hz_in, hbz⟩
  let w : Point2 := x + (z - a)
  have hzd : z - a ∈ ℓ.direction := AffineSubspace.vsub_mem_direction hz_in ha
  have hx_in : x ∈ (AffineSubspace.mk' x ℓ.direction : Set Point2) := by simp
  have hw_in : w ∈ (AffineSubspace.mk' x ℓ.direction : Set Point2) := by
    have h : w -ᵥ x ∈ (AffineSubspace.mk' x ℓ.direction).direction := by
      simpa [w] using hzd
    exact (AffineSubspace.vsub_right_mem_direction_iff_mem hx_in w).mp h
  have h_zw : dist z w < ρ := by
    have h2 : z - w = a - x := by simp [w] <;> abel
    have h3 : dist z w = dist a x := by
      rw [dist_eq_norm, dist_eq_norm, h2, norm_sub_rev]
    rw [h3, dist_comm a x] <;> exact hx
  have h_yw : dist y w < r + 2 * ρ := by
    calc
      dist y w
        ≤ dist y b + dist b z + dist z w := by
          calc
            dist y w
              ≤ dist y b + dist b w := dist_triangle y b w
            _ ≤ dist y b + (dist b z + dist z w) := by gcongr; exact dist_triangle b z w
            _ = dist y b + dist b z + dist z w := by ring
      _ < ρ + r + ρ := by linarith
      _ = r + 2 * ρ := by ring
  exact Metric.mem_thickening_iff.mpr ⟨w, hw_in, h_yw⟩

/-- Expand the product of two smoothed measures into a double sum over translated
ball measures. -/
lemma smoothMeasure_prod_expansion
    {G₁ G₂ : DiscreteSet 2} (h1 : G₁.Nonempty) (h2 : G₂.Nonempty)
    {ρ : ℝ} {hρ : 0 < ρ}
    {E : Set (Point2 × Point2)} (hE : MeasurableSet E) :
    ((smoothMeasure G₁ h1 ρ hρ : Measure Point2).prod (smoothMeasure G₂ h2 ρ hρ : Measure Point2)) E =
      (G₁.card : ENNReal)⁻¹ * (G₂.card : ENNReal)⁻¹ *
        ∑ a ∈ G₁, ∑ b ∈ G₂,
          (((translatedBallMeasure ρ hρ a).prod
            (translatedBallMeasure ρ hρ b) : Measure (Point2 × Point2))) E := by
  let f : Point2 → Measure Point2 := fun a =>
    (translatedBallMeasure ρ hρ a : Measure Point2)
  let g : Point2 → Measure Point2 := fun b =>
    (translatedBallMeasure ρ hρ b : Measure Point2)
  let c1 : ENNReal := (G₁.card : ENNReal)⁻¹
  let c2 : ENNReal := (G₂.card : ENNReal)⁻¹
  let μ : Measure Point2 := ∑ a ∈ G₁, f a
  let ν : Measure Point2 := ∑ b ∈ G₂, g b
  have hν1 : (smoothMeasure G₁ h1 ρ hρ : Measure Point2) = c1 • μ := by rfl
  have hν2 : (smoothMeasure G₂ h2 ρ hρ : Measure Point2) = c2 • ν := by rfl
  have h_prod_sum_left : ∀ (s : Finset Point2) (ν' : Measure Point2) [SFinite ν'],
      (∑ a ∈ s, f a).prod ν' = ∑ a ∈ s, (f a).prod ν' := by
    intro s ν'
    exact Finset.induction_on s
      (by simp)
      (fun a s ha ih => by
        have h_comm : (f a + ∑ x ∈ s, f x).prod ν' =
            ((∑ x ∈ s, f x) + f a).prod ν' := by
          congr 1; exact add_comm _ _
        rw [Finset.sum_insert ha, Finset.sum_insert ha, h_comm]
        rw [Measure.add_prod (f a)]
        rw [ih]
        exact add_comm _ _)
  have h_prod_sum_right : ∀ (μ' : Measure Point2) (s : Finset Point2) [SFinite μ'],
      μ'.prod (∑ b ∈ s, g b) = ∑ b ∈ s, μ'.prod (g b) := by
    intro μ' s
    exact Finset.induction_on s
      (by simp)
      (fun b s hb ih => by
        have h_comm : μ'.prod (g b + ∑ x ∈ s, g x) =
            μ'.prod ((∑ x ∈ s, g x) + g b) := by
          congr 1; exact add_comm _ _
        rw [Finset.sum_insert hb, Finset.sum_insert hb, h_comm]
        rw [Measure.prod_add (g b)]
        rw [ih]
        exact add_comm _ _)
  have h_sum_left : μ.prod ν = ∑ a ∈ G₁, (f a).prod ν :=
    h_prod_sum_left G₁ ν
  have h_sum_right : ∀ (a : Point2), (f a).prod ν = ∑ b ∈ G₂, (f a).prod (g b) :=
    fun a => h_prod_sum_right (f a) G₂
  have h2 : μ.prod ν = ∑ a ∈ G₁, ∑ b ∈ G₂, (f a).prod (g b) := by
    rw [h_sum_left]; apply Finset.sum_congr rfl; intro a _; exact h_sum_right a
  have h4 : (∑ a ∈ G₁, ∑ b ∈ G₂, (f a).prod (g b)) E =
      ∑ a ∈ G₁, ∑ b ∈ G₂, ((f a).prod (g b)) E := by
    rw [Measure.finsetSum_apply]; apply Finset.sum_congr rfl; intro a _; rw [Measure.finsetSum_apply]
  have h1 : (c1 • μ).prod (c2 • ν) = (c1 * c2) • μ.prod ν := by
    have h1a : (c1 • μ).prod (c2 • ν) = c1 • (μ.prod (c2 • ν)) := by rw [Measure.prod_smul_left]
    have h1b : μ.prod (c2 • ν) = c2 • μ.prod ν := by rw [Measure.prod_smul_right]
    rw [h1a, h1b]; rw [←smul_smul]
  calc
    ((c1 • μ).prod (c2 • ν)) E
      = ((c1 * c2) • μ.prod ν) E := by rw [h1]
    _ = (c1 * c2) * (μ.prod ν) E := Measure.smul_apply (c1 * c2) (μ.prod ν) E
    _ = (c1 * c2) * (∑ a ∈ G₁, ∑ b ∈ G₂, (f a).prod (g b)) E := by rw [h2]
    _ = (c1 * c2) * ∑ a ∈ G₁, ∑ b ∈ G₂, ((f a).prod (g b)) E := by rw [h4]
    _ = c1 * c2 * ∑ a ∈ G₁, ∑ b ∈ G₂, (((translatedBallMeasure ρ hρ a).prod
          (translatedBallMeasure ρ hρ b) : Measure (Point2 × Point2))) E := by rfl

/-- Markov retention: if the average of `p x` over `S` is at least `1 - c`, and each
`p x ≤ 1`, then the number of `x` with `p x ≥ 1/2` is at least `(1 - 2c) * |S|`. -/
lemma markov_retention {α : Type*} [DecidableEq α] {S : Finset α}
    (hS : S.Nonempty)
    (p : α → ENNReal) (hp_le_one : ∀ x ∈ S, p x ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) (h2c : 2 * c < 1)
    (h_sum : (1 - ENNReal.ofReal c) * (S.card : ENNReal) ≤ ∑ x ∈ S, p x) :
    (1 - ENNReal.ofReal (2 * c)) * (S.card : ENNReal) ≤
        ((S.filter (fun x => p x ≥ 1 / 2)).card : ENNReal) := by
  let E_disc := S.filter (fun x => p x ≥ 1 / 2)
  let N : ℝ := (S.card : ℝ)
  let m : ℝ := (E_disc.card : ℝ)
  let p' : α → ℝ := fun x => (p x).toReal
  have hNpos : 0 < N := by
    have h : 0 < S.card := Finset.card_pos.mpr hS
    have h' : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast h
    simpa [N] using h'
  have h_fin : ∀ x ∈ S, p x ≠ ⊤ := by
    intro x hx
    have h : p x ≤ 1 := hp_le_one x hx
    exact ne_top_of_le_ne_top (by norm_num) h
  have h_sum_fin : (∑ x ∈ S, p x) ≠ ⊤ := by
    have h : ∑ x ∈ S, p x ≤ (S.card : ENNReal) := by
      calc
        ∑ x ∈ S, p x ≤ ∑ x ∈ S, (1 : ENNReal) := Finset.sum_le_sum (fun x hx => hp_le_one x hx)
        _ = (S.card : ENNReal) := by simp
    exact ne_top_of_le_ne_top (by simp) h
  have h_left_fin : ((1 - ENNReal.ofReal c) * (S.card : ENNReal)) ≠ ⊤ := by
    have h4 : (1 - ENNReal.ofReal c) ≠ ⊤ := by simp
    exact ENNReal.mul_ne_top h4 (by simp)
  have h_sum_toReal : (∑ x ∈ S, p x).toReal = ∑ x ∈ S, p' x := by
    rw [ENNReal.toReal_sum] <;> intro x hx; exact h_fin x hx
  have hc1 : c ≤ 1 := by linarith
  have h_toReal_sub : (1 - ENNReal.ofReal c).toReal = 1 - c := by
    have h_sub : ENNReal.ofReal (1 - c) = ENNReal.ofReal 1 - ENNReal.ofReal c :=
      ENNReal.ofReal_sub (1 : ℝ) hc
    have h_eq : 1 - ENNReal.ofReal c = ENNReal.ofReal (1 - c) := by
      rw [h_sub] <;> norm_num
    rw [h_eq, ENNReal.toReal_ofReal (by linarith)]
  have h1 : (1 - c) * N ≤ ∑ x ∈ S, p' x := by
    have h_iff : ((1 - ENNReal.ofReal c) * (S.card : ENNReal)).toReal ≤ (∑ x ∈ S, p x).toReal ↔
        (1 - ENNReal.ofReal c) * (S.card : ENNReal) ≤ ∑ x ∈ S, p x :=
      ENNReal.toReal_le_toReal h_left_fin h_sum_fin
    have h2 := h_iff.mpr h_sum
    have h3 : ((1 - ENNReal.ofReal c) * (S.card : ENNReal)).toReal = (1 - c) * N := by
      rw [ENNReal.toReal_mul, h_toReal_sub] <;> simp [N]
    rw [h3, h_sum_toReal] at h2
    exact h2
  have h_p'_le_one : ∀ x ∈ S, p' x ≤ 1 := by
    intro x hx
    have h : p x ≤ 1 := hp_le_one x hx
    have h_iff : (p x).toReal ≤ (1 : ENNReal).toReal ↔ p x ≤ 1 :=
      ENNReal.toReal_le_toReal (h_fin x hx) (by norm_num)
    have h' : (p x).toReal ≤ (1 : ENNReal).toReal := h_iff.mpr h
    simpa [p'] using h'
  have h_p'_lt_half : ∀ x ∈ S, x ∉ E_disc → p' x < 1 / 2 := by
    intro x hx hnx
    have h7 : ¬(p x ≥ 1 / 2) := by
      by_contra h10
      have h11 : x ∈ E_disc := by
        apply Finset.mem_filter.mpr
        exact ⟨hx, h10⟩
      exact hnx h11
    have h8 : p x < 1 / 2 := by exact lt_of_not_ge h7
    have h_iff : (p x).toReal < (1 / 2 : ENNReal).toReal ↔ p x < 1 / 2 :=
      ENNReal.toReal_lt_toReal (h_fin x hx) (by norm_num)
    have h9 : (p x).toReal < (1 / 2 : ENNReal).toReal := h_iff.mpr h8
    simpa [p'] using h9
  have h_pointwise : ∀ x ∈ S, p' x ≤ 1 / 2 + (if x ∈ E_disc then (1 / 2 : ℝ) else 0) := by
    intro x hx
    by_cases h : x ∈ E_disc
    · rw [if_pos h]
      have h9 : p' x ≤ 1 := h_p'_le_one x hx
      linarith
    · rw [if_neg h]
      have h9 : p' x < 1 / 2 := h_p'_lt_half x hx h
      linarith
  have h_sum_upper : ∑ x ∈ S, p' x ≤ ∑ x ∈ S, (1 / 2 + (if x ∈ E_disc then (1 / 2 : ℝ) else 0)) :=
    Finset.sum_le_sum h_pointwise
  have h_sum_rhs : ∑ x ∈ S, (1 / 2 + (if x ∈ E_disc then (1 / 2 : ℝ) else 0)) = (N + m) / 2 := by
    calc
      ∑ x ∈ S, (1 / 2 + (if x ∈ E_disc then (1 / 2 : ℝ) else 0))
        = ∑ x ∈ S, (1 / 2 : ℝ) + ∑ x ∈ S, (if x ∈ E_disc then (1 / 2 : ℝ) else 0) := by
          rw [Finset.sum_add_distrib]
      _ = N / 2 + m / 2 := by
          have h1 : ∑ x ∈ S, (1 / 2 : ℝ) = N / 2 := by
            simp [N, Finset.sum_const] <;> ring
          have h2 : ∑ x ∈ S, (if x ∈ E_disc then (1 / 2 : ℝ) else 0) = m / 2 := by
            have h3 : ∑ x ∈ S, (if x ∈ E_disc then (1 / 2 : ℝ) else 0) =
                ∑ x ∈ E_disc, (1 / 2 : ℝ) := by
              rw [Finset.sum_ite]
              have h4 : S.filter (fun x => x ∈ E_disc) = E_disc := by
                ext x
                simp only [Finset.mem_filter]
                have h_sub : E_disc ⊆ S := Finset.filter_subset _ _
                constructor
                · rintro ⟨_, hxE⟩; exact hxE
                · intro hxE; exact ⟨h_sub hxE, hxE⟩
              rw [h4] <;> simp
            rw [h3]
            simp [m, Finset.sum_const] <;> ring
          rw [h1, h2]
      _ = (N + m) / 2 := by ring
  have h_upper : ∑ x ∈ S, p' x ≤ (N + m) / 2 := by
    calc
      ∑ x ∈ S, p' x ≤ ∑ x ∈ S, (1 / 2 + (if x ∈ E_disc then (1 / 2 : ℝ) else 0)) := h_sum_upper
      _ = (N + m) / 2 := h_sum_rhs
  have h_concl : (1 - 2 * c) * N ≤ m := by linarith
  have h_pos : 0 ≤ 1 - 2 * c := by linarith
  have h_eq1 : 1 - ENNReal.ofReal (2 * c) = ENNReal.ofReal (1 - 2 * c) := by
    have h_sub : ENNReal.ofReal (1 - 2 * c) = ENNReal.ofReal 1 - ENNReal.ofReal (2 * c) :=
      ENNReal.ofReal_sub (1 : ℝ) (show 0 ≤ 2 * c from by positivity)
    rw [h_sub] <;> norm_num
  have h_final : (1 - ENNReal.ofReal (2 * c)) * (S.card : ENNReal) ≤ (E_disc.card : ENNReal) := by
    rw [h_eq1]
    have h10 : ENNReal.ofReal (1 - 2 * c) * (S.card : ENNReal) = ENNReal.ofReal ((1 - 2 * c) * N) := by
      have h11 : (S.card : ENNReal) = ENNReal.ofReal N := by simp [N]
      rw [h11, ← ENNReal.ofReal_mul h_pos]
    rw [h10]
    have h12 : ENNReal.ofReal ((1 - 2 * c) * N) ≤ ENNReal.ofReal m := by gcongr
    have h13 : ENNReal.ofReal m = (E_disc.card : ENNReal) := by simp [m]
    rw [h13] at h12
    exact h12
  exact h_final

end Kakeya.Assouad
