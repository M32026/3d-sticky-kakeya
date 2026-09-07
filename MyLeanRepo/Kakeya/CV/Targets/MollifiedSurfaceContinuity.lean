import MyLeanRepo.Kakeya.CV.Statements
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Continuity of the coefficient-space mollifier

Analytic infrastructure for the mollified directional surface area used in
Carbery--Valdimarsson Section 3.

## Proof outline

For fixed `x₀`, apply the filter version of the dominated convergence theorem
to `F x := indicator (ball x ε) f`.

1. For `x` near `x₀`, `F x` is `AEStronglyMeasurable` because `f` is locally
   integrable and `ball x ε` is measurable.
2. The family is dominated by `indicator (closedBall x₀ (ε+1)) ‖f‖`, which is
   integrable since `f` is locally integrable and the closed ball is compact.
3. For a.e. `y` (outside the sphere `sphere x₀ ε`, which has measure zero),
   `x ↦ F x y` is eventually constant near `x₀`, hence continuous.
4. DCT gives continuity of `x ↦ ∫ y, F x y ∂volume = ∫ y in ball x ε, f y`.
5. `ballAverage ε f` is a constant multiple of this map.
-/

noncomputable section

open MeasureTheory Metric Set Filter

namespace Kakeya.CV

/-- The integral of a locally integrable function over a moving ball is continuous. -/
lemma ballIntegral_continuous {N : ℕ} {ε : ℝ} {f : CoefficientSpace N → ℝ}
    (hε : 0 < ε) (hf : LocallyIntegrable f volume) :
    Continuous (fun x : CoefficientSpace N => ∫ y in Metric.ball x ε, f y) := by
  have h_main : ∀ (x₀ : CoefficientSpace N), ContinuousAt
      (fun x : CoefficientSpace N => ∫ y in Metric.ball x ε, f y) x₀ := by
    intro x₀
    let K := Metric.closedBall x₀ (ε + 1)
    have hK_compact : IsCompact K := isCompact_closedBall x₀ (ε + 1)
    have hf_K : IntegrableOn f K volume := hf.integrableOn_isCompact hK_compact
    let bound : CoefficientSpace N → ℝ := Set.indicator K (fun y => ‖f y‖)
    have hK_meas : MeasurableSet K := isClosed_closedBall.measurableSet
    have h_bound_integrable : Integrable bound volume := by
      rw [integrable_indicator_iff hK_meas]
      exact hf_K.norm
    let F : CoefficientSpace N → (CoefficientSpace N → ℝ) :=
      fun x => Set.indicator (Metric.ball x ε) f
    let f' : CoefficientSpace N → ℝ := Set.indicator (Metric.ball x₀ ε) f
    have h_ball_meas : ∀ (x : CoefficientSpace N), MeasurableSet (Metric.ball x ε) :=
      fun _ => isOpen_ball.measurableSet
    have h_f_ae : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
    have h_meas : ∀ᶠ (x : CoefficientSpace N) in nhds x₀,
        AEStronglyMeasurable (F x) volume := by
      filter_upwards with x
      exact h_f_ae.indicator (h_ball_meas x)
    have h_bound' : ∀ᶠ (x : CoefficientSpace N) in nhds x₀,
        ∀ᵐ (y : CoefficientSpace N) ∂volume, ‖F x y‖ ≤ bound y := by
      have h_nhds : Metric.ball x₀ 1 ∈ nhds x₀ := Metric.ball_mem_nhds x₀ (by norm_num)
      filter_upwards [h_nhds] with x hx
      have h : ∀ (y : CoefficientSpace N), ‖F x y‖ ≤ bound y := by
        intro y
        by_cases hy : y ∈ Metric.ball x ε
        · have hxy : y ∈ K := by
            have h1 : dist y x₀ ≤ ε + 1 := by
              have h2 : dist y x < ε := hy
              have h3 : dist x x₀ < 1 := hx
              linarith [dist_triangle y x x₀]
            simpa [K, Metric.mem_closedBall] using h1
          have hfy : F x y = f y := Set.indicator_of_mem hy f
          have hby : bound y = ‖f y‖ := Set.indicator_of_mem hxy (fun y => ‖f y‖)
          rw [hfy, hby]
        · have hfy : F x y = 0 := Set.indicator_of_notMem hy f
          have h_nonneg : 0 ≤ bound y := by
            have h : bound y = 0 ∨ bound y = ‖f y‖ := by
              by_cases hxy : y ∈ K
              · right
                exact Set.indicator_of_mem hxy (fun y => ‖f y‖)
              · left
                exact Set.indicator_of_notMem hxy (fun y => ‖f y‖)
            rcases h with (h | h)
            · rw [h]
            · rw [h]; exact norm_nonneg _
          rw [hfy, norm_zero]
          exact h_nonneg
      filter_upwards with y
      exact h y
    have h_sphere_zero : volume (Metric.sphere x₀ ε) = 0 :=
      MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume x₀ hε.ne'
    have h_lim : ∀ᵐ (y : CoefficientSpace N) ∂volume,
        Tendsto (fun x : CoefficientSpace N => F x y) (nhds x₀) (nhds (f' y)) := by
      filter_upwards [compl_mem_ae_iff.mpr h_sphere_zero] with y hy
      have h_y_not_sphere : y ∉ Metric.sphere x₀ ε := hy
      by_cases h_y_in : y ∈ Metric.ball x₀ ε
      · -- y is strictly inside the ball
        have h_dist : dist y x₀ < ε := by simpa [Metric.mem_ball] using h_y_in
        have h_pos : 0 < ε - dist y x₀ := by linarith
        have h_eventually : ∀ᶠ (x : CoefficientSpace N) in nhds x₀, y ∈ Metric.ball x ε := by
          have h : ∀ᶠ (x : CoefficientSpace N) in nhds x₀, dist x x₀ < ε - dist y x₀ :=
            Metric.ball_mem_nhds x₀ h_pos
          filter_upwards [h] with x hx'
          calc dist y x ≤ dist y x₀ + dist x₀ x := dist_triangle y x₀ x
            _ = dist y x₀ + dist x x₀ := by rw [dist_comm x₀ x]
            _ < ε := by linarith
        have h_eq : (fun x : CoefficientSpace N => f' y) =ᶠ[nhds x₀] (fun x => F x y) := by
          filter_upwards [h_eventually] with x hx'
          have h1 : F x y = f y := Set.indicator_of_mem hx' f
          have h2 : f' y = f y := Set.indicator_of_mem h_y_in f
          exact h2.trans h1.symm
        exact tendsto_const_nhds.congr' h_eq
      · -- y is strictly outside the ball
        have h_dist : ε < dist y x₀ := by
          have h1 : ¬dist y x₀ < ε := by simpa [Metric.mem_ball] using h_y_in
          have h2 : dist y x₀ ≠ ε := by
            intro h3
            have h4 : y ∈ Metric.sphere x₀ ε := by
              simpa [Metric.mem_sphere, dist_eq_norm] using h3
            exact h_y_not_sphere h4
          by_contra h5
          have h6 : dist y x₀ ≤ ε := by linarith
          have h7 : dist y x₀ = ε := by linarith
          exact h2 h7
        have h_pos : 0 < dist y x₀ - ε := by linarith
        have h_eventually : ∀ᶠ (x : CoefficientSpace N) in nhds x₀, y ∉ Metric.ball x ε := by
          have h : ∀ᶠ (x : CoefficientSpace N) in nhds x₀, dist x x₀ < dist y x₀ - ε :=
            Metric.ball_mem_nhds x₀ h_pos
          filter_upwards [h] with x hx'
          have h6 : dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle y x x₀
          have h9 : ¬dist y x < ε := by linarith
          exact h9
        have h_eq : (fun x : CoefficientSpace N => f' y) =ᶠ[nhds x₀] (fun x => F x y) := by
          filter_upwards [h_eventually] with x hx'
          have h1 : F x y = 0 := Set.indicator_of_notMem hx' f
          have h2 : f' y = 0 := Set.indicator_of_notMem h_y_in f
          exact h2.trans h1.symm
        exact tendsto_const_nhds.congr' h_eq
    have h_dct : Tendsto (fun x : CoefficientSpace N => ∫ y, F x y ∂volume)
        (nhds x₀) (nhds (∫ y, f' y ∂volume)) :=
      tendsto_integral_filter_of_dominated_convergence bound h_meas h_bound' h_bound_integrable h_lim
    have h1 : ∀ (x : CoefficientSpace N), (∫ y, F x y ∂volume) = ∫ y in Metric.ball x ε, f y := by
      intro x
      exact integral_indicator (h_ball_meas x)
    have h2 : (∫ y, f' y ∂volume) = ∫ y in Metric.ball x₀ ε, f y :=
      integral_indicator (h_ball_meas x₀)
    have h_cont_at : ContinuousAt (fun x : CoefficientSpace N => ∫ y in Metric.ball x ε, f y) x₀ := by
      simpa [h1, h2, ContinuousAt] using h_dct
    exact h_cont_at
  exact continuous_iff_continuousAt.mpr h_main

theorem mollified_surface_continuity :
    MollifiedSurfaceContinuityStatement := by
  intro N ε f hε hf
  have h_main : Continuous (fun x : CoefficientSpace N => ∫ y in Metric.ball x ε, f y) :=
    ballIntegral_continuous hε hf
  let c : ℝ := (volume (Metric.ball (0 : CoefficientSpace N) ε)).toReal⁻¹
  have h_eq : ballAverage ε f = fun x => c * ∫ y in Metric.ball x ε, f y := by
    funext x
    simp [ballAverage, c]
  rw [h_eq]
  exact h_main.const_mul c

end Kakeya.CV
