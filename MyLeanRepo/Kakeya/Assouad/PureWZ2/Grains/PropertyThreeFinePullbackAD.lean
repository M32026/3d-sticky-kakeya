import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighCaseWiring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CordobaSlabLowerNoIncidence
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CordobaLogAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalSlabLower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADArithmeticPreGrain

/-! HIGH-regime local AD for a whole-cell Property-P fine pullback. -/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/-- A retained fine point has a Property-P witness within one coarse-cell
diameter. -/
lemma propertyThreeFinePullback_witness_near
    {delta rho tau : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {propertyThree : WZ1PaperTubeShading coarse}
    (hrho : 0 < rho)
    (htau : rho * Real.sqrt 3 ≤ tau)
    (point : Point3)
    (hpoint : point ∈
      (propertyThreeFinePullbackShading
        cover fineShading propertyThree).union) :
    (propertyThree.union ∩ Metric.closedBall point tau).Nonempty := by
  rcases hpoint with ⟨source, hsource⟩
  rcases propertyThreeFinePullbackShading_support
      cover fineShading propertyThree source point hsource with
    ⟨witness, hwitness, hcell⟩
  refine ⟨witness, hwitness, ?_⟩
  let cell := wz1PaperGridIndex rho witness
  have hwitnessCell : witness ∈ wz1PaperGridCube rho cell := by
    exact (mem_wz1PaperGridCube rho cell witness).mpr rfl
  have hpointCell : point ∈ wz1PaperGridCube rho cell := by
    exact (mem_wz1PaperGridCube rho cell point).mpr hcell.symm
  exact (wz1PaperGridCube_diameter hrho cell hwitnessCell hpointCell).trans htau

/-- Córdoba HIGH-case wiring when the query center need not itself belong to
Property-P.  It is enough that Property-P meets the `tau`-ball around the
query center. -/
lemma high_case_cordoba_ad_of_nearby
    {sigma tau queryScale L : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (epsilon₁ epsilon₃ : ℝ)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading) (tau := tau)
      epsilon₁ epsilon₃)
    (v : Point3) (hv_unit : ‖v‖ = 1)
    (q : Point3)
    (hq_coarse : q ∈ coarseShading.union)
    (hnear :
      (propP.propertyThree.union ∩ Metric.closedBall q tau).Nonempty)
    (S : Set Point3)
    (hS_eq : S = coarseShading.union ∩ Metric.closedBall q (4 * tau))
    (hS_meas : MeasurableSet S)
    (hS_sub_ball : S ⊆ Metric.closedBall q (4 * tau))
    (W0 V_min V_total : ℝ)
    (hW0_pos : 0 < W0)
    (hW0_eq : W0 = 40 * L)
    (hVmin_pos : 0 < V_min)
    (hVmin_def :
      V_min = Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200)
    (hV_total_pos : 0 < V_total)
    (hV_total : volume S ≤ ENNReal.ofReal V_total)
    (htau_def : tau = L * Real.sqrt 3)
    (htau_pos : 0 < tau)
    (htau_le_20L : tau ≤ 20 * L)
    (hL_le_tau : L ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L)
    (htau_le_one : tau ≤ 1)
    (hL_small : L ≤ 1 / 1000)
    (hL_pos : 0 < L)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (heps₁_pos : 0 < epsilon₁)
    (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (L₀_log : ℝ)
    (hL_le_L0_log : L ≤ L₀_log)
    (h_log_main : 0 < epsilon₁ → ∀ (L' : ℝ), 0 < L' → L' ≤ L₀_log →
      ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ (j : Fin coarse.card) (p : Point3),
        p ∈ propP.propertyThree.carrier j →
          Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier j ∩ Metric.closedBall p tau))
    (h_ax_condition :
      4 * (6 * L) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃)) ^ 2)
    (target : Set Point3)
    (h_target_sub :
      target ⊆ coarseShading.union ∩ Metric.closedBall q (Real.sqrt queryScale))
    (hsqrt_query_le_4tau : Real.sqrt queryScale ≤ 4 * tau)
    (hquery_pos : 0 < queryScale)
    (C : ENNReal)
    (hC_one : (1 : ENNReal) ≤ C)
    (hC_top : C ≠ ⊤)
    (h_arithmetic :
      ENNReal.ofReal
        ((V_total / V_min) * (2 * (2 * W0) / queryScale + 2)) ≤ C) :
    PureWZ2PaperADSet1
      (scalarProjection v target) queryScale (1 - sigma) C := by
  let P : Set ℝ :=
    scalarProjection v
      (propP.propertyThree.union ∩ Metric.closedBall q tau)
  have h_slab_P : ∀ t ∈ P,
      volume (S ∩ {x | |inner ℝ x v - t| ≤ W0}) ≥
        ENNReal.ofReal V_min := by
    intro t ht
    have hcordoba := pureWz2_cordoba_slab_lower_no_incidence_no_q
      epsilon₁ epsilon₃ propP v hv_unit htau_le_20L
      h_propertyThree_full
      (h_log_main heps₁_pos L hL_pos hL_le_L0_log)
      h_ax_condition hL_pos hL_small htau_pos hL_le_tau htau_sq htau_le_one
      hsigma_pos hsigma_lt_one heps₁_pos heps₃_pos heps_sum q t ht
    have hslab :
        {x : Point3 | |inner ℝ x v - t| ≤ 40 * L} =
          {x : Point3 | |inner ℝ x v - t| ≤ W0} := by
      rw [hW0_eq]
    rw [hslab] at hcordoba
    have hbound :
        Kakeya.realRpowENN L (1 + 7 * epsilon₁ + epsilon₃) *
            ENNReal.ofReal (tau ^ 2 / 200) =
          ENNReal.ofReal V_min := by
      have hpow : 0 ≤ Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) :=
        Real.rpow_nonneg hL_pos.le _
      have hmul :
          ENNReal.ofReal
              (Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) *
                (tau ^ 2 / 200)) =
            ENNReal.ofReal (Real.rpow L (1 + 7 * epsilon₁ + epsilon₃)) *
              ENNReal.ofReal (tau ^ 2 / 200) :=
        ENNReal.ofReal_mul hpow
      have heq :
          Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) *
              (tau ^ 2 / 200) = V_min := by
        rw [hVmin_def]
        ring
      simp only [Kakeya.realRpowENN]
      rw [← hmul, heq]
    rw [hbound] at hcordoba
    have hset :
        coarseShading.union ∩ Metric.closedBall q (4 * tau) ∩
            {x : Point3 | |inner ℝ x v - t| ≤ W0} =
          S ∩ {x : Point3 | |inner ℝ x v - t| ≤ W0} := by
      rw [hS_eq]
    rwa [← hset]
  have hcover : ∀ t ∈ scalarProjection v S,
      ∃ t' ∈ P, |t - t'| ≤ W0 := by
    intro t ht
    rcases cover_condition_from_nonempty hL_pos htau_def hv_unit
        hS_sub_ball (P := P) rfl hnear t ht with
      ⟨t', ht', hdist⟩
    refine ⟨t', ht', ?_⟩
    rw [hW0_eq]
    exact hdist
  exact cordoba_slab_to_ad_for_subset
    C q hq_coarse v hv_unit tau W0 htau_pos hW0_pos
    V_min V_total hVmin_pos hV_total_pos S hS_eq hS_meas hS_sub_ball
    P h_slab_P hcover hV_total h_arithmetic target h_target_sub
    hsqrt_query_le_4tau hquery_pos sigma hsigma_pos hsigma_lt_one
    hC_one hC_top

/-- Apply the no-center-membership Córdoba theorem to the actual fine
whole-cell pullback. -/
lemma propertyThreeFinePullback_high_local_ad
    {delta sigma tau queryScale L : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (epsilon₁ epsilon₃ : ℝ)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading) (tau := tau)
      epsilon₁ epsilon₃)
    (v : Point3) (hv_unit : ‖v‖ = 1)
    (q : Point3)
    (hq : q ∈
      (propertyThreeFinePullbackShading
        cover fineShading propP.propertyThree).union)
    (S : Set Point3)
    (hS_eq : S = coarseShading.union ∩ Metric.closedBall q (4 * tau))
    (hS_meas : MeasurableSet S)
    (hS_sub_ball : S ⊆ Metric.closedBall q (4 * tau))
    (W0 V_min V_total : ℝ)
    (hW0_pos : 0 < W0)
    (hW0_eq : W0 = 40 * L)
    (hVmin_pos : 0 < V_min)
    (hVmin_def :
      V_min = Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200)
    (hV_total_pos : 0 < V_total)
    (hV_total : volume S ≤ ENNReal.ofReal V_total)
    (htau_def : tau = L * Real.sqrt 3)
    (htau_pos : 0 < tau)
    (htau_le_20L : tau ≤ 20 * L)
    (hL_le_tau : L ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L)
    (htau_le_one : tau ≤ 1)
    (hL_small : L ≤ 1 / 1000)
    (hL_pos : 0 < L)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (heps₁_pos : 0 < epsilon₁)
    (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (L₀_log : ℝ)
    (hL_le_L0_log : L ≤ L₀_log)
    (h_log_main : 0 < epsilon₁ → ∀ (L' : ℝ), 0 < L' → L' ≤ L₀_log →
      ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ (j : Fin coarse.card) (p : Point3),
        p ∈ propP.propertyThree.carrier j →
          Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier j ∩ Metric.closedBall p tau))
    (h_ax_condition :
      4 * (6 * L) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃)) ^ 2)
    (hsqrt_query_le_4tau : Real.sqrt queryScale ≤ 4 * tau)
    (hquery_pos : 0 < queryScale)
    (C : ENNReal)
    (hC_one : (1 : ENNReal) ≤ C)
    (hC_top : C ≠ ⊤)
    (h_arithmetic :
      ENNReal.ofReal
        ((V_total / V_min) * (2 * (2 * W0) / queryScale + 2)) ≤ C) :
    PureWZ2PaperADSet1
      (scalarProjection v
        ((propertyThreeFinePullbackShading
            cover fineShading propP.propertyThree).union ∩
          Metric.closedBall q (Real.sqrt queryScale)))
      queryScale (1 - sigma) C := by
  have hq_coarse : q ∈ coarseShading.union := by
    rcases hq with ⟨source, hsource⟩
    exact ⟨selectParent cover source,
      balanced.point_compatibility source (selectParent cover source)
        (selectedParent_covers cover source) q hsource.1⟩
  have hnear :
      (propP.propertyThree.union ∩ Metric.closedBall q tau).Nonempty :=
    propertyThreeFinePullback_witness_near hL_pos
      (by rw [htau_def]) q hq
  let target :=
    (propertyThreeFinePullbackShading
      cover fineShading propP.propertyThree).union ∩
        Metric.closedBall q (Real.sqrt queryScale)
  have htarget :
      target ⊆ coarseShading.union ∩ Metric.closedBall q (Real.sqrt queryScale) := by
    intro point hpoint
    rcases hpoint.1 with ⟨source, hsource⟩
    exact ⟨⟨selectParent cover source,
      balanced.point_compatibility source (selectParent cover source)
        (selectedParent_covers cover source) point hsource.1⟩, hpoint.2⟩
  exact high_case_cordoba_ad_of_nearby
    epsilon₁ epsilon₃ propP v hv_unit q hq_coarse hnear
    S hS_eq hS_meas hS_sub_ball W0 V_min V_total hW0_pos hW0_eq
    hVmin_pos hVmin_def hV_total_pos hV_total htau_def htau_pos
    htau_le_20L hL_le_tau htau_sq htau_le_one hL_small hL_pos
    hsigma_pos hsigma_lt_one heps₁_pos heps₃_pos heps_sum
    L₀_log hL_le_L0_log h_log_main h_propertyThree_full h_ax_condition
    target htarget hsqrt_query_le_4tau hquery_pos C hC_one hC_top h_arithmetic

/-- At the critical query scale `48 * L^2`, the geometric containment and
the slab-to-AD arithmetic meet exactly.  The total-volume parameter is chosen
as the volume of the ambient ball of radius `4 * L * sqrt 3`, so callers do
not have to manufacture an unrelated volume bound. -/
lemma propertyThreeFinePullback_high_local_ad_at_critical_scale_of_inv_cube_bound
    {delta sigma tau L delta' outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (epsilon₁ epsilon₃ : ℝ)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading) (tau := tau)
      epsilon₁ epsilon₃)
    (v : Point3) (hv_unit : ‖v‖ = 1)
    (q : Point3)
    (hq : q ∈
      (propertyThreeFinePullbackShading
        cover fineShading propP.propertyThree).union)
    (S : Set Point3)
    (hS_eq : S = coarseShading.union ∩ Metric.closedBall q (4 * tau))
    (hS_meas : MeasurableSet S)
    (hS_sub_ball : S ⊆ Metric.closedBall q (4 * tau))
    (htau_def : tau = L * Real.sqrt 3)
    (htau_pos : 0 < tau)
    (htau_le_20L : tau ≤ 20 * L)
    (hL_le_tau : L ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L)
    (htau_le_one : tau ≤ 1)
    (hL_small : L ≤ 1 / 1000)
    (hL_pos : 0 < L)
    (hL_half : L ≤ 1 / 2)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (heps₁_pos : 0 < epsilon₁)
    (heps₁_lt : epsilon₁ < 1 / 20)
    (heps₃_pos : 0 < epsilon₃)
    (heps₃_def : epsilon₃ = 1 - 2 * epsilon₁)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (L₀_log : ℝ)
    (hL_le_L0_log : L ≤ L₀_log)
    (h_log_main : 0 < epsilon₁ → ∀ (L' : ℝ), 0 < L' → L' ≤ L₀_log →
      ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ (j : Fin coarse.card) (p : Point3),
        p ∈ propP.propertyThree.carrier j →
          Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier j ∩ Metric.closedBall p tau))
    (h_ax_condition :
      4 * (6 * L) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃)) ^ 2)
    (hdelta'_pos : 0 < delta')
    (hdelta'_lt_one : delta' < 1)
    (houtputLoss_pos : 0 < outputLoss)
    (hL_bound : L ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hinv_cube : Real.rpow L (-3 : ℝ) ≤
      Real.rpow delta' (-outputLoss)) :
    PureWZ2PaperADSet1
      (scalarProjection v
        ((propertyThreeFinePullbackShading
            cover fineShading propP.propertyThree).union ∩
          Metric.closedBall q (Real.sqrt (48 * L ^ 2))))
      (48 * L ^ 2) (1 - sigma)
      (Kakeya.realRpowENN delta' (-outputLoss)) := by
  let W0 : ℝ := 40 * L
  let W : ℝ := 2 * W0
  let V_min : ℝ :=
    Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200
  let V_total : ℝ := 256 * Real.pi * Real.sqrt 3 * L ^ 3
  have hW0_pos : 0 < W0 := by positivity
  have hVmin_pos : 0 < V_min := by
    dsimp only [V_min]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hL_pos _) (sq_pos_of_pos htau_pos))
      (by norm_num)
  have hVtotal_pos : 0 < V_total := by
    dsimp only [V_total]
    positivity
  have hsqrt3_cube : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    rw [pow_succ, Real.sq_sqrt] <;> norm_num
  have hball_volume :
      volume (Metric.closedBall q (4 * tau)) = ENNReal.ofReal V_total := by
    rw [EuclideanSpace.volume_closedBall_fin_three]
    rw [← ENNReal.ofReal_pow (show 0 ≤ 4 * tau by positivity)]
    rw [← ENNReal.ofReal_mul (show 0 ≤ (4 * tau) ^ 3 by positivity)]
    apply congrArg ENNReal.ofReal
    rw [htau_def]
    dsimp only [V_total]
    calc
      (4 * (L * Real.sqrt 3)) ^ 3 * (Real.pi * 4 / 3) =
          (256 / 3) * Real.pi * L ^ 3 * (Real.sqrt 3) ^ 3 := by ring
      _ = 256 * Real.pi * Real.sqrt 3 * L ^ 3 := by
        rw [hsqrt3_cube]
        ring
  have hV_total : volume S ≤ ENNReal.ofReal V_total := by
    calc
      volume S ≤ volume (Metric.closedBall q (4 * tau)) := measure_mono hS_sub_ball
      _ = ENNReal.ofReal V_total := hball_volume
  have htau_sq_eq : tau ^ 2 = 3 * L ^ 2 := by
    rw [htau_def, mul_pow, Real.sq_sqrt] <;> norm_num <;> ring
  have hVmin_product :
      V_min = (3 / 200 : ℝ) *
        Real.rpow L (3 + 7 * epsilon₁ + epsilon₃) := by
    have hpow :
        Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * L ^ 2 =
          Real.rpow L (3 + 7 * epsilon₁ + epsilon₃) := by
      have htwo : L ^ (2 : ℕ) = Real.rpow L (2 : ℝ) :=
        (Real.rpow_natCast L 2).symm
      calc
        Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * L ^ 2 =
            Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) *
              Real.rpow L (2 : ℝ) := by rw [htwo]
        _ = Real.rpow L ((1 + 7 * epsilon₁ + epsilon₃) + 2) :=
          (Real.rpow_add hL_pos _ _).symm
        _ = Real.rpow L (3 + 7 * epsilon₁ + epsilon₃) := by congr 1 <;> ring
    dsimp only [V_min]
    rw [htau_sq_eq]
    calc
      Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * (3 * L ^ 2) / 200 =
          (3 / 200 : ℝ) *
            (Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * L ^ 2) := by ring
      _ = (3 / 200 : ℝ) *
          Real.rpow L (3 + 7 * epsilon₁ + epsilon₃) := by rw [hpow]
  have hproduct :
      (V_total / V_min) * (2 * W / (48 * L ^ 2) + 2) ≤
        600000 * L ^ (-2 - 5 * epsilon₁) := by
    apply slab_to_ad_product_bound
    · exact hL_pos
    · exact hL_half
    · exact heps₃_def
    · exact le_rfl
    · positivity
    · dsimp only [W, W0]
      linarith
    · positivity
    · exact le_rfl
    · exact hVmin_product
  have harithmetic :
      ENNReal.ofReal
          ((V_total / V_min) *
            (2 * (2 * W0) / (48 * L ^ 2) + 2)) ≤
        Kakeya.realRpowENN delta' (-outputLoss) := by
    have hdelta0 :
        (600000 : ℝ) * Real.rpow L (-2 - 5 * epsilon₁) ≤
          Real.rpow L (-3 : ℝ) :=
      delta0_arith_alpha3 L epsilon₁ hL_pos
        (hL_half.trans_lt (by norm_num)) heps₁_lt hL_bound
    have hreal :
        (V_total / V_min) *
            (2 * (2 * W0) / (48 * L ^ 2) + 2) ≤
          Real.rpow delta' (-outputLoss) := by
      calc
        (V_total / V_min) *
            (2 * (2 * W0) / (48 * L ^ 2) + 2) =
            (V_total / V_min) * (2 * W / (48 * L ^ 2) + 2) := by
              simp only [W]
        _ ≤ (600000 : ℝ) * Real.rpow L (-2 - 5 * epsilon₁) := hproduct
        _ ≤ Real.rpow L (-3 : ℝ) := hdelta0
        _ ≤ Real.rpow delta' (-outputLoss) := hinv_cube
    simpa only [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal hreal
  have hC_one :
      (1 : ENNReal) ≤ Kakeya.realRpowENN delta' (-outputLoss) := by
    simp only [Kakeya.realRpowENN]
    apply ENNReal.one_le_ofReal.mpr
    have hdelta'_le_one : delta' ≤ 1 := hdelta'_lt_one.le
    have h : Real.rpow delta' 0 ≤ Real.rpow delta' (-outputLoss) :=
      Real.rpow_le_rpow_of_exponent_ge
        hdelta'_pos hdelta'_le_one (show -outputLoss ≤ 0 by linarith)
    simpa using h
  have hC_top : Kakeya.realRpowENN delta' (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  have hsqrt_critical : Real.sqrt (48 * L ^ 2) ≤ 4 * tau :=
    sqrt_rho_le_4tau hL_pos (by positivity) htau_def le_rfl
  exact propertyThreeFinePullback_high_local_ad
    balanced epsilon₁ epsilon₃ propP v hv_unit q hq
    S hS_eq hS_meas hS_sub_ball W0 V_min V_total
    hW0_pos rfl hVmin_pos rfl hVtotal_pos hV_total
    htau_def htau_pos htau_le_20L hL_le_tau htau_sq htau_le_one
    hL_small hL_pos hsigma_pos hsigma_lt_one heps₁_pos heps₃_pos heps_sum
    L₀_log hL_le_L0_log h_log_main h_propertyThree_full h_ax_condition
    hsqrt_critical (by positivity)
    (Kakeya.realRpowENN delta' (-outputLoss)) hC_one hC_top harithmetic

/-- Compatibility form of the critical-scale estimate.  The historical
power-scale hypotheses imply the invariant `L⁻³` budget used by the more
general theorem above. -/
lemma propertyThreeFinePullback_high_local_ad_at_critical_scale
    {delta sigma tau L delta' stickyLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (epsilon₁ epsilon₃ : ℝ)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading) (tau := tau)
      epsilon₁ epsilon₃)
    (v : Point3) (hv_unit : ‖v‖ = 1)
    (q : Point3)
    (hq : q ∈
      (propertyThreeFinePullbackShading
        cover fineShading propP.propertyThree).union)
    (S : Set Point3)
    (hS_eq : S = coarseShading.union ∩ Metric.closedBall q (4 * tau))
    (hS_meas : MeasurableSet S)
    (hS_sub_ball : S ⊆ Metric.closedBall q (4 * tau))
    (htau_def : tau = L * Real.sqrt 3)
    (htau_pos : 0 < tau)
    (htau_le_20L : tau ≤ 20 * L)
    (hL_le_tau : L ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L)
    (htau_le_one : tau ≤ 1)
    (hL_small : L ≤ 1 / 1000)
    (hL_pos : 0 < L)
    (hL_half : L ≤ 1 / 2)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (heps₁_pos : 0 < epsilon₁)
    (heps₁_lt : epsilon₁ < 1 / 20)
    (heps₃_pos : 0 < epsilon₃)
    (heps₃_def : epsilon₃ = 1 - 2 * epsilon₁)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (L₀_log : ℝ)
    (hL_le_L0_log : L ≤ L₀_log)
    (h_log_main : 0 < epsilon₁ → ∀ (L' : ℝ), 0 < L' → L' ≤ L₀_log →
      ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ (j : Fin coarse.card) (p : Point3),
        p ∈ propP.propertyThree.carrier j →
          Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier j ∩ Metric.closedBall p tau))
    (h_ax_condition :
      4 * (6 * L) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃)) ^ 2)
    (hdelta'_pos : 0 < delta')
    (hdelta'_lt_one : delta' < 1)
    (houtputLoss_pos : 0 < outputLoss)
    (hL_eq : L = Real.rpow delta' stickyLoss)
    (hL_bound : L ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyLoss_le_third : stickyLoss ≤ outputLoss / 3) :
    PureWZ2PaperADSet1
      (scalarProjection v
        ((propertyThreeFinePullbackShading
            cover fineShading propP.propertyThree).union ∩
          Metric.closedBall q (Real.sqrt (48 * L ^ 2))))
      (48 * L ^ 2) (1 - sigma)
      (Kakeya.realRpowENN delta' (-outputLoss)) := by
  apply propertyThreeFinePullback_high_local_ad_at_critical_scale_of_inv_cube_bound
    balanced epsilon₁ epsilon₃ propP v hv_unit q hq S hS_eq hS_meas
    hS_sub_ball htau_def htau_pos htau_le_20L hL_le_tau htau_sq
    htau_le_one hL_small hL_pos hL_half hsigma_pos hsigma_lt_one
    heps₁_pos heps₁_lt heps₃_pos heps₃_def heps_sum L₀_log
    hL_le_L0_log h_log_main h_propertyThree_full h_ax_condition
    hdelta'_pos hdelta'_lt_one houtputLoss_pos hL_bound
  rw [hL_eq]
  calc
    Real.rpow (Real.rpow delta' stickyLoss) (-3 : ℝ) =
        Real.rpow delta' (stickyLoss * (-3 : ℝ)) :=
      (Real.rpow_mul hdelta'_pos.le stickyLoss (-3 : ℝ)).symm
    _ = Real.rpow delta' (-3 * stickyLoss) := by ring_nf
    _ ≤ Real.rpow delta' (-outputLoss) := by
      apply Real.rpow_le_rpow_of_exponent_ge hdelta'_pos hdelta'_lt_one.le
      linarith

end Kakeya.Assouad.PureWZ2

end
