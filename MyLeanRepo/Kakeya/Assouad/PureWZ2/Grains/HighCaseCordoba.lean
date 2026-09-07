import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighCaseWiring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CordobaSlabLowerNoIncidence
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CordobaLogAbsorption
import Mathlib.Tactic

/-!
# HIGH case Córdoba wiring helper

Isolates the Córdoba slab bound → slab_to_ad conversion from the main
`local_ad_from_sticky` lemma to avoid OOM caused by complex type inference
involving `PureWZ2PropertyPData`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/-- Weaker version of `high_case_cordoba_ad` that does NOT require `q ∈ propertyThree.union`.

Instead requires:
- `hq_coarse : q ∈ coarseShading.union` (derivable from `q ∈ refined.union`)
- `hP_nonempty : (propertyThree.union ∩ closedBall q tau).Nonempty`

Uses `pureWz2_cordoba_slab_lower_no_incidence_no_q` which gives the slab bound
directly in `ball(q, 4*tau)`, avoiding the 3τ → 4τ expansion. -/
lemma high_case_cordoba_ad_no_q
    {sigma tau rho L : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (epsilon₁ epsilon₃ : ℝ)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading) (tau := tau)
      epsilon₁ epsilon₃)
    (v : Point3) (hv_unit : ‖v‖ = 1)
    (q : Point3)
    (hq_coarse : q ∈ coarseShading.union)
    (hP_nonempty : (propP.propertyThree.union ∩ Metric.closedBall q tau).Nonempty)
    (S : Set Point3)
    (hS_eq : S = coarseShading.union ∩ Metric.closedBall q (4 * tau))
    (hS_meas : MeasurableSet S)
    (hS_sub_ball : S ⊆ Metric.closedBall q (4 * tau))
    (W0 V_min V_total : ℝ)
    (hW0_pos : 0 < W0)
    (hW0_eq : W0 = 40 * L)
    (hVmin_pos : 0 < V_min)
    (hVmin_def : V_min = Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200)
    (hV_total_pos : 0 < V_total)
    (hV_total : volume S ≤ ENNReal.ofReal V_total)
    (htau_def : tau = L * Real.sqrt 3)
    (htau_pos : 0 < tau)
    (htau_le_20L : tau ≤ 20 * L)
    (hL_le_tau : L ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L)
    (htau_le_one : tau ≤ 1)
    (hL_small' : L ≤ 1 / 1000)
    (hL_pos : 0 < L)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (heps₁_pos : 0 < epsilon₁)
    (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (L₀_log : ℝ)
    (hL_le_L0_log : L ≤ L₀_log)
    (h_log_main : 0 < epsilon₁ → ∀ (L' : ℝ), 0 < L' → L' ≤ L₀_log →
      ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 100 / L'^3 →
        Real.rpow L' epsilon₁ * (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ (j : Fin coarse.card) (p : Point3),
        p ∈ propP.propertyThree.carrier j →
          Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier j ∩ Metric.closedBall p tau))
    (h_ax_condition : 4 * (6 * L)^2 ≤ (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃))^2)
    (target : Set Point3)
    (h_target_sub : target ⊆ coarseShading.union ∩ Metric.closedBall q (Real.sqrt rho))
    (hsqrt_rho_le_4tau : Real.sqrt rho ≤ 4 * tau)
    (hrho_pos : 0 < rho)
    (C : ENNReal)
    (hC_one : (1 : ENNReal) ≤ C)
    (hC_top : C ≠ ⊤)
    (h_arithmetic : ENNReal.ofReal ((V_total / V_min) * (2 * (2 * W0) / rho + 2)) ≤ C) :
    PureWZ2PaperADSet1 (scalarProjection v target) rho (1 - sigma) C := by
  let P : Set ℝ := scalarProjection v (propP.propertyThree.union ∩ Metric.closedBall q tau)

  -- Córdoba slab bound for each t ∈ P using _no_q version (bound directly in ball(q,4*tau))
  have h_slab_P : ∀ t ∈ P,
      volume (S ∩ {x | |inner ℝ x v - t| ≤ W0}) ≥ ENNReal.ofReal V_min := by
    intro t ht
    have h_cordoba_raw := pureWz2_cordoba_slab_lower_no_incidence_no_q
        epsilon₁ epsilon₃ propP v hv_unit htau_le_20L
        h_propertyThree_full
        (h_log_main heps₁_pos L hL_pos hL_le_L0_log)
        h_ax_condition
        hL_pos hL_small' htau_pos hL_le_tau htau_sq htau_le_one
        hsigma_pos hsigma_lt_one heps₁_pos heps₃_pos heps_sum
        q t ht
    have h_slab_set_eq : (coarseShading.union ∩ Metric.closedBall q (4 * tau) ∩
          {x : Point3 | |inner ℝ x v - t| ≤ 40 * L}) =
        S ∩ {x : Point3 | |inner ℝ x v - t| ≤ W0} := by
      rw [hS_eq, hW0_eq] <;> rfl
    rw [h_slab_set_eq] at h_cordoba_raw
    have h_bound_eq : Kakeya.realRpowENN L (1 + 7 * epsilon₁ + epsilon₃) * ENNReal.ofReal (tau ^ 2 / 200) =
        ENNReal.ofReal V_min := by
      have h_pos1 : 0 ≤ Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) :=
        Real.rpow_nonneg hL_pos.le _
      have h_eq : Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * (tau ^ 2 / 200) = V_min := by
        rw [hVmin_def] <;> ring
      have h_mul : ENNReal.ofReal (Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * (tau ^ 2 / 200)) =
          ENNReal.ofReal (Real.rpow L (1 + 7 * epsilon₁ + epsilon₃)) * ENNReal.ofReal (tau ^ 2 / 200) :=
        ENNReal.ofReal_mul (hp := h_pos1)
      simp only [Kakeya.realRpowENN]
      rw [← h_mul, h_eq]
    rw [h_bound_eq] at h_cordoba_raw
    exact h_cordoba_raw

  -- Cover condition
  have h_cover_raw : ∀ t ∈ scalarProjection v S, ∃ t' ∈ P, |t - t'| ≤ 40 * L :=
    cover_condition_from_nonempty (L := L) hL_pos htau_def hv_unit hS_sub_ball
      (propertyThree_union := propP.propertyThree.union)
      (P := P) (hP_def := rfl) hP_nonempty
  have h_cover : ∀ t ∈ scalarProjection v S, ∃ t' ∈ P, |t - t'| ≤ W0 := by
    intro t ht
    rcases h_cover_raw t ht with ⟨t', ht', hle⟩
    refine' ⟨t', ht', _⟩
    rw [hW0_eq]
    exact hle

  exact cordoba_slab_to_ad_for_subset
    C q hq_coarse v hv_unit tau W0 htau_pos hW0_pos V_min V_total hVmin_pos hV_total_pos
    S hS_eq hS_meas hS_sub_ball P h_slab_P h_cover hV_total h_arithmetic
    target h_target_sub hsqrt_rho_le_4tau hrho_pos sigma hsigma_pos hsigma_lt_one hC_one hC_top

/-- Helper: given PropertyP and all parameters, produce the AD bound via Córdoba.

Requires `q ∈ propertyThree.union`. For a weaker version that only requires
`propertyThree.union` to intersect `ball(q, tau)`, see `high_case_cordoba_ad_no_q`. -/
lemma high_case_cordoba_ad
    {sigma tau rho L : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (epsilon₁ epsilon₃ : ℝ)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading) (tau := tau)
      epsilon₁ epsilon₃)
    (v : Point3) (hv_unit : ‖v‖ = 1)
    (q : Point3)
    (hq_prop3 : q ∈ propP.propertyThree.union)
    (S : Set Point3)
    (hS_eq : S = coarseShading.union ∩ Metric.closedBall q (4 * tau))
    (hS_meas : MeasurableSet S)
    (hS_sub_ball : S ⊆ Metric.closedBall q (4 * tau))
    (W0 V_min V_total : ℝ)
    (hW0_pos : 0 < W0)
    (hW0_eq : W0 = 40 * L)
    (hVmin_pos : 0 < V_min)
    (hVmin_def : V_min = Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200)
    (hV_total_pos : 0 < V_total)
    (hV_total : volume S ≤ ENNReal.ofReal V_total)
    (htau_def : tau = L * Real.sqrt 3)
    (htau_pos : 0 < tau)
    (htau_le_20L : tau ≤ 20 * L)
    (hL_le_tau : L ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L)
    (htau_le_one : tau ≤ 1)
    (hL_small' : L ≤ 1 / 1000)
    (hL_pos : 0 < L)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (heps₁_pos : 0 < epsilon₁)
    (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (L₀_log : ℝ)
    (hL_le_L0_log : L ≤ L₀_log)
    (h_log_main : 0 < epsilon₁ → ∀ (L' : ℝ), 0 < L' → L' ≤ L₀_log →
      ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 100 / L'^3 →
        Real.rpow L' epsilon₁ * (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ (j : Fin coarse.card) (p : Point3),
        p ∈ propP.propertyThree.carrier j →
          Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier j ∩ Metric.closedBall p tau))
    (h_ax_condition : 4 * (6 * L)^2 ≤ (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃))^2)
    (target : Set Point3)
    (h_target_sub : target ⊆ coarseShading.union ∩ Metric.closedBall q (Real.sqrt rho))
    (hsqrt_rho_le_4tau : Real.sqrt rho ≤ 4 * tau)
    (hrho_pos : 0 < rho)
    (C : ENNReal)
    (hC_one : (1 : ENNReal) ≤ C)
    (hC_top : C ≠ ⊤)
    (h_arithmetic : ENNReal.ofReal ((V_total / V_min) * (2 * (2 * W0) / rho + 2)) ≤ C) :
    PureWZ2PaperADSet1 (scalarProjection v target) rho (1 - sigma) C := by
  -- Derive hq_coarse from hq_prop3
  have h1 : propP.propertyThree.union ⊆ propP.propertyOne.union := by
    intro x hx
    rcases hx with ⟨i, hi⟩
    exact ⟨i, propP.propertyThree_sub i hi⟩
  have h2 : propP.propertyOne.union ⊆ coarseShading.union := by
    intro x hx
    rcases hx with ⟨i, hi⟩
    exact ⟨i, propP.propertyOne_sub i hi⟩
  have hq_coarse : q ∈ coarseShading.union := h2 (h1 hq_prop3)
  -- Derive hP_nonempty from hq_prop3
  have hP_nonempty : (propP.propertyThree.union ∩ Metric.closedBall q tau).Nonempty := by
    refine' ⟨q, hq_prop3, _⟩
    simpa [dist_self] using show dist q q ≤ tau from by
      have h : dist q q = 0 := dist_self q
      rw [h]
      exact htau_pos.le
  exact high_case_cordoba_ad_no_q
    epsilon₁ epsilon₃ propP v hv_unit q hq_coarse hP_nonempty
    S hS_eq hS_meas hS_sub_ball
    W0 V_min V_total hW0_pos hW0_eq hVmin_pos hVmin_def hV_total_pos hV_total
    htau_def htau_pos htau_le_20L hL_le_tau htau_sq htau_le_one
    hL_small' hL_pos hsigma_pos hsigma_lt_one heps₁_pos heps₃_pos heps_sum
    L₀_log hL_le_L0_log h_log_main h_propertyThree_full h_ax_condition
    target h_target_sub hsqrt_rho_le_4tau hrho_pos C hC_one hC_top h_arithmetic

end Kakeya.Assouad.PureWZ2

end
