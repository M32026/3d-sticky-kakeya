import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.Main

/-!
# Test-set validation and finite net construction

This module contains the validated test-set checks, polynomial cardinality
bound, and the large-scale branch of the tube density test net.
-/

noncomputable section

open MeasureTheory Metric Finset
open scoped Pointwise
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet

namespace Kakeya.Streamlined

lemma test_set_valid {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (c : Point3) (hc : c ∈ centerGrid δ hδ)
    (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ frameMatrices (δ / 100) (by positivity))
    (a' b' c' : ℝ)
    (h_dims : (a', (b', c')) ∈ dimTriples δ hδ) :
    Convex ℝ (testParallelepiped c M a' b' c') ∧
    MeasurableSet (testParallelepiped c M a' b' c') ∧
    volume (testParallelepiped c M a' b' c') ≠ ⊤ ∧
    testParallelepiped c M a' b' c' ⊆ closedBall (0 : Point3) 20 := by
  let f : Point3 →ₗ[ℝ] Point3 := matrixToLin M
  let fc : Point3 →L[ℝ] Point3 := f.toContinuousLinearMap
  let S : Set Point3 := fc '' axisBox a' b' c'
  let T : Set Point3 := c +ᵥ S
  have h_dims_pos : 0 < a' ∧ 0 < b' ∧ 0 < c' :=
    dimTriples_all_pos δ hδ (a', (b', c')) h_dims
  have ha' : 0 < a' := h_dims_pos.1
  have hb' : 0 < b' := h_dims_pos.2.1
  have hc' : 0 < c' := h_dims_pos.2.2
  have h_axisBox_convex : Convex ℝ (axisBox a' b' c') :=
    convex_axisBox a' b' c'
  have hS_convex : Convex ℝ S := Convex.linear_image h_axisBox_convex f
  have hT_convex : Convex ℝ T := hS_convex.vadd c
  have h_ball_convex : Convex ℝ (closedBall (0 : Point3) 20) :=
    convex_closedBall _ _
  have h_convex : Convex ℝ (T ∩ closedBall (0 : Point3) 20) :=
    hT_convex.inter h_ball_convex
  have h_cont0 : Continuous (fun x : Point3 => x (0 : Fin 3)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0
  have h_cont1 : Continuous (fun x : Point3 => x (1 : Fin 3)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1
  have h_cont2 : Continuous (fun x : Point3 => x (2 : Fin 3)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2
  have h1_closed : IsClosed {x : Point3 | |x (0 : Fin 3)| ≤ a' / 2} :=
    isClosed_le h_cont0.abs continuous_const
  have h2_closed : IsClosed {x : Point3 | |x (1 : Fin 3)| ≤ b' / 2} :=
    isClosed_le h_cont1.abs continuous_const
  have h3_closed : IsClosed {x : Point3 | |x (2 : Fin 3)| ≤ c' / 2} :=
    isClosed_le h_cont2.abs continuous_const
  have h_axisBox_eq : axisBox a' b' c' =
      {x : Point3 | |x (0 : Fin 3)| ≤ a' / 2} ∩
      ({x : Point3 | |x (1 : Fin 3)| ≤ b' / 2} ∩
       {x : Point3 | |x (2 : Fin 3)| ≤ c' / 2}) := by
    ext x
    simp [axisBox]
  have h_axisBox_closed : IsClosed (axisBox a' b' c') := by
    rw [h_axisBox_eq]
    exact h1_closed.inter (h2_closed.inter h3_closed)
  let R := max (max a' b') c' / 2
  have hR_pos : 0 ≤ R := by positivity
  have h_axisBox_bounded : Bornology.IsBounded (axisBox a' b' c') := by
    have h_sub :
        axisBox a' b' c' ⊆
          Metric.closedBall (0 : Point3) (Real.sqrt 3 * R) := by
      intro x hx
      have h0 : |x 0| ≤ a' / 2 := hx.1
      have h1 : |x 1| ≤ b' / 2 := hx.2.1
      have h2 : |x 2| ≤ c' / 2 := hx.2.2
      have h3 : ‖x‖ ≤ Real.sqrt 3 * R := by
        have hR_def : R = max (max a' b') c' / 2 := by rfl
        have h4 : a' / 2 ≤ R := by
          rw [hR_def]
          have h41 : a' ≤ max (max a' b') c' :=
            le_trans (le_max_left a' b') (le_max_left (max a' b') c')
          linarith
        have h5 : b' / 2 ≤ R := by
          rw [hR_def]
          have h51 : b' ≤ max (max a' b') c' :=
            le_trans (le_max_right a' b') (le_max_left (max a' b') c')
          linarith
        have h6 : c' / 2 ≤ R := by
          rw [hR_def]
          have h61 : c' ≤ max (max a' b') c' :=
            le_max_right (max a' b') c'
          linarith
        have h7 : (x 0)^2 ≤ R^2 := by nlinarith [abs_le.mp h0]
        have h8 : (x 1)^2 ≤ R^2 := by nlinarith [abs_le.mp h1]
        have h9 : (x 2)^2 ≤ R^2 := by nlinarith [abs_le.mp h2]
        have h10 : ‖x‖^2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
          have h101 :
              ‖x‖ = Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2) := by
            simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ] <;> ring
          rw [h101, Real.sq_sqrt (by positivity)]
        have h11 : ‖x‖^2 ≤ 3 * R^2 := by
          rw [h10]
          nlinarith
        have h12 : 0 ≤ Real.sqrt 3 * R := by positivity
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sqrt_nonneg 3, sq_nonneg ‖x‖, h11, h12]
      simpa [Metric.mem_closedBall] using h3
    exact Metric.isBounded_closedBall.subset h_sub
  have h_axisBox_compact : IsCompact (axisBox a' b' c') :=
    Metric.isCompact_of_isClosed_isBounded h_axisBox_closed h_axisBox_bounded
  have hS_compact : IsCompact S := h_axisBox_compact.image fc.continuous
  have hT_compact : IsCompact T := hS_compact.vadd c
  have hT_closed : IsClosed T := hT_compact.isClosed
  have h_ball_closed : IsClosed (closedBall (0 : Point3) 20) :=
    isClosed_closedBall
  have h_test_closed : IsClosed (T ∩ closedBall (0 : Point3) 20) :=
    hT_closed.inter h_ball_closed
  have h_measurable : MeasurableSet (T ∩ closedBall (0 : Point3) 20) :=
    h_test_closed.measurableSet
  have h_sub : T ∩ closedBall (0 : Point3) 20 ⊆
      closedBall (0 : Point3) 20 :=
    Set.inter_subset_right
  have h_ball_vol_ne_top : volume (closedBall (0 : Point3) 20) ≠ ⊤ := by
    have h_bdd : Bornology.IsBounded (closedBall (0 : Point3) 20) :=
      Metric.isBounded_closedBall
    exact h_bdd.measure_lt_top.ne
  have h_vol_ne_top : volume (T ∩ closedBall (0 : Point3) 20) ≠ ⊤ :=
    ne_top_of_le_ne_top h_ball_vol_ne_top (measure_mono h_sub)
  have h_supported : T ∩ closedBall (0 : Point3) 20 ⊆
      closedBall (0 : Point3) 20 := h_sub
  have h_eq :
      testParallelepiped c M a' b' c' =
        T ∩ closedBall (0 : Point3) 20 := by
    rfl
  rw [h_eq]
  exact ⟨h_convex, h_measurable, h_vol_ne_top, h_supported⟩

/-- `Real.log 2 ≥ 1/2`, proved from `log x ≤ x - 1`. -/
lemma log_two_ge_half : Real.log 2 ≥ 1 / 2 := by
  have h1 : Real.log (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  have h2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp
  rw [h2] at h1
  linarith

/-- For x ≥ 0, `Nat.ceil x ≤ x + 1`. -/
lemma nat_ceil_le_add_one (x : ℝ) (hx : 0 ≤ x) :
    (Nat.ceil x : ℝ) ≤ x + 1 := by
  have h_floor_nonneg : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
  let n : ℕ := ⌊x⌋.toNat + 1
  have h_toNat : (⌊x⌋.toNat : ℤ) = ⌊x⌋ :=
    Int.toNat_of_nonneg h_floor_nonneg
  have hn1 : (n : ℝ) = (⌊x⌋ : ℝ) + 1 := by
    have h : (n : ℤ) = ⌊x⌋ + 1 := by
      simp [n, h_toNat]
    exact_mod_cast h
  have h2 : x ≤ (n : ℝ) := by
    rw [hn1]
    exact le_of_lt (Int.lt_floor_add_one x)
  have h4 : Nat.ceil x ≤ n := Nat.ceil_le.mpr h2
  have h5 : (n : ℝ) ≤ x + 1 := by
    rw [hn1]
    have h6 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    linarith
  have h7 : (Nat.ceil x : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast h4
  exact h7.trans h5

/-- For δ < 1/2, the total grid cardinality is ≤ `(1/δ)^200`. -/
lemma grid_card_bound {δ : ℝ} (hδ : 0 < δ) (hδ_small : δ < 1 / 2) :
    ((centerGrid δ hδ).card : ℝ) *
    ((frameMatrices (δ / 100) (by positivity)).card : ℝ) *
    ((dimTriples δ hδ).card : ℝ) ≤ (1 / δ) ^ 200 := by
  set centers := centerGrid δ hδ with hcenters
  set matrices := frameMatrices (δ / 100) (by positivity) with hmatrices
  set dims3 := dimTriples δ hδ with hdims3
  let invδ : ℝ := 1 / δ

  have hlog2_half : Real.log 2 ≥ 1 / 2 := log_two_ge_half
  have hinvδ_pos : 0 < invδ := by positivity
  have hinvδ_gt2 : 2 < invδ := by
    have h1 : 1 / δ > 2 := by
      have h2 : 0 < δ := hδ
      have h3 : δ < 1 / 2 := hδ_small
      have h4 : 1 / δ > 1 / (1 / 2 : ℝ) := by gcongr
      norm_num at h4 ⊢ <;> exact h4
    exact h1

  /- Bound centers.card ≤ 10^10 * invδ^3 -/
  have h_centers : (centers.card : ℝ) ≤ 10^10 * invδ^3 := by
    have h1 := centerGrid_card δ hδ
    have h2 : 25 + δ / 10 ≤ 26 := by linarith
    have h3 : (centers.card : ℝ) ≤ 64 * (26 : ℝ)^3 / (δ / 10)^3 := by
      calc (centers.card : ℝ)
        ≤ 64 * (25 + δ / 10)^3 / (δ / 10)^3 := h1
      _ ≤ 64 * (26 : ℝ)^3 / (δ / 10)^3 := by gcongr
    have h4 : 64 * (26 : ℝ)^3 / (δ / 10)^3 = (64 * (26 : ℝ)^3 * 1000) * invδ^3 := by
      have h5 : (δ / 10)^3 = δ^3 / 1000 := by ring
      rw [h5]
      have h6 : 64 * (26 : ℝ)^3 / (δ^3 / 1000) = 64 * (26 : ℝ)^3 * 1000 / δ^3 := by
        field_simp [hδ.ne']
      rw [h6]
      have h7 : invδ = 1 / δ := by rfl
      rw [h7] <;> ring
    rw [h4] at h3
    have h5 : (64 * (26 : ℝ)^3 * 1000) ≤ (10^10 : ℝ) := by norm_num
    have h6 : (64 * (26 : ℝ)^3 * 1000) * invδ^3 ≤ (10^10 : ℝ) * invδ^3 :=
      mul_le_mul_of_nonneg_right h5 (by positivity)
    exact h3.trans h6

  /- Bound matrices.card ≤ 10^30 * invδ^9 -/
  have hε_le_one : (δ / 100 : ℝ) ≤ 1 := by linarith
  have h_matrices : (matrices.card : ℝ) ≤ 10^30 * invδ^9 := by
    have h1 := frameMatrices_card (show 0 < δ / 100 from by positivity) hε_le_one
    have h2 : (matrices.card : ℝ) ≤ (11 / (δ / 100))^9 := h1
    have h3 : (11 / (δ / 100))^9 = 1100^9 * invδ^9 := by
      have h4 : 11 / (δ / 100) = 1100 / δ := by
        field_simp [hδ.ne'] <;> norm_num
      rw [h4]
      have h5 : invδ = 1 / δ := by rfl
      rw [h5] <;> ring
    rw [h3] at h2
    have h5 : (1100^9 : ℝ) ≤ 10^30 := by norm_num
    have h6 : (1100^9 : ℝ) * invδ^9 ≤ (10^30 : ℝ) * invδ^9 :=
      mul_le_mul_of_nonneg_right h5 (by positivity)
    exact h2.trans h6

  /- Bound dims3.card ≤ 10^9 * invδ^3 -/
  have h_dims : (dims3.card : ℝ) ≤ 10^9 * invδ^3 := by
    let G := dimGrid δ hδ
    have h1 : dims3 ⊆ (G ×ˢ G ×ˢ G) := Finset.filter_subset _ _
    have h2 : (dims3.card : ℝ) ≤ (G.card : ℝ)^3 := by
      have h3 : dims3.card ≤ (G ×ˢ G ×ˢ G).card := Finset.card_le_card h1
      have h4 : (G ×ˢ G ×ˢ G).card = G.card ^ 3 := by
        simp [Finset.card_product] <;> ring
      rw [h4] at h3
      exact_mod_cast h3
    have h5 : G.card ≤ dimGridK δ hδ + 1 := dimGrid_card_le δ hδ
    have h6 : (G.card : ℝ) ≤ (dimGridK δ hδ : ℝ) + 1 := by exact_mod_cast h5
    set x : ℝ := Real.log (250 / δ) / Real.log 2 with hx_def
    have hx_nonneg : 0 ≤ x := by
      rw [hx_def]
      have h_gt : 1 < 250 / δ := by
        have h : 250 / δ > 500 := by
          calc 250 / δ > 250 / (1 / 2 : ℝ) := by gcongr
               _ = 500 := by norm_num
        linarith
      have h1 : 0 < Real.log (250 / δ) := Real.log_pos h_gt
      have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact div_nonneg h1.le h2.le
    have h_ceil : (dimGridK δ hδ : ℝ) ≤ x + 1 := by
      simpa [dimGridK, hx_def] using nat_ceil_le_add_one x hx_nonneg
    have h_log_upper : Real.log (250 / δ) ≤ 250 / δ := Real.log_le_self (by positivity)
    have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h_x_bound : x ≤ 500 / δ := by
      rw [hx_def]
      have h7 : Real.log (250 / δ) / Real.log 2 ≤ (250 / δ) / Real.log 2 := by
        apply div_le_div_of_nonneg_right
        · exact h_log_upper
        · exact h_log2_pos.le
      have h8 : (250 / δ) / Real.log 2 ≤ (250 / δ) / (1 / 2 : ℝ) := by
        have h9 : 0 ≤ 250 / δ := by positivity
        have h10 : (1 / 2 : ℝ) ≤ Real.log 2 := hlog2_half
        have h11 : 0 < (1 / 2 : ℝ) := by norm_num
        have h12 : (Real.log 2)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ := by
          exact inv_anti₀ h11 hlog2_half
        have h13 : (250 / δ) * (Real.log 2)⁻¹ ≤ (250 / δ) * ((1 / 2 : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left h12 h9
        simpa [div_eq_mul_inv] using h13
      have h13 : (250 / δ) / (1 / 2 : ℝ) = 500 / δ := by ring
      linarith
    have h14 : (2 : ℝ) ≤ 4 / δ := by
      have h15 : 0 < δ := hδ
      have h16 : δ < 1 / 2 := hδ_small
      calc (2 : ℝ) ≤ 4 / (1 / 2 : ℝ) := by norm_num
           _ ≤ 4 / δ := by gcongr
    have h10 : (dimGridK δ hδ : ℝ) + 1 ≤ 504 / δ := by
      calc (dimGridK δ hδ : ℝ) + 1
        ≤ x + 2 := by linarith [h_ceil]
      _ ≤ 500 / δ + 2 := by linarith [h_x_bound]
      _ ≤ 500 / δ + 4 / δ := by exact add_le_add_right h14 (500 / δ)
      _ = 504 / δ := by ring
    have h15 : (G.card : ℝ) ≤ 504 / δ := by linarith
    have h16 : 0 ≤ (G.card : ℝ) := by positivity
    have h17 : (G.card : ℝ)^3 ≤ (504 / δ)^3 := by gcongr
    have h18 : (504 / δ)^3 = 504^3 * invδ^3 := by
      have h19 : invδ = 1 / δ := by rfl
      rw [h19] <;> ring
    calc (dims3.card : ℝ)
      ≤ (G.card : ℝ)^3 := h2
    _ ≤ (504 / δ)^3 := h17
    _ = 504^3 * invδ^3 := h18
    _ ≤ 10^9 * invδ^3 := by
      have h20 : (504^3 : ℝ) ≤ 10^9 := by norm_num
      exact mul_le_mul_of_nonneg_right h20 (by positivity)

  /- Combine bounds -/
  have h_main : (centers.card : ℝ) * (matrices.card : ℝ) * (dims3.card : ℝ) ≤
      10^49 * invδ^15 := by
    have h1a : (centers.card : ℝ) ≤ 10^10 * invδ^3 := h_centers
    have h1b : (matrices.card : ℝ) ≤ 10^30 * invδ^9 := h_matrices
    have h1c : (dims3.card : ℝ) ≤ 10^9 * invδ^3 := h_dims
    have h1 : (centers.card : ℝ) * (matrices.card : ℝ) ≤ (10^10 * invδ^3) * (10^30 * invδ^9) :=
      mul_le_mul h1a h1b (by positivity) (by positivity)
    have h2 : ((centers.card : ℝ) * (matrices.card : ℝ)) * (dims3.card : ℝ) ≤
        ((10^10 * invδ^3) * (10^30 * invδ^9)) * (10^9 * invδ^3) :=
      mul_le_mul h1 h1c (by positivity) (by positivity)
    have h3 : ((10^10 * invδ^3) * (10^30 * invδ^9)) * (10^9 * invδ^3) = 10^49 * invδ^15 := by ring
    rw [h3] at h2
    exact h2
  have h_absorb : (10^49 : ℝ) ≤ invδ^185 := by
    have h1 : (2 : ℝ)^185 ≤ invδ^185 := by gcongr
    have h2 : (10^49 : ℝ) ≤ (2 : ℝ)^185 := by norm_num
    exact h2.trans h1
  have h_final : 10^49 * invδ^15 ≤ invδ^200 := by
    have h3 : 10^49 * invδ^15 ≤ invδ^185 * invδ^15 :=
      mul_le_mul_of_nonneg_right h_absorb (by positivity)
    have h4 : invδ^185 * invδ^15 = invδ^200 := by ring
    rw [h4] at h3
    exact h3
  exact h_main.trans h_final

/-- For δ ≥ 1/2, a single test set B(0,20) suffices with loss factor 64000.

This proof does NOT use `density_reduction_to_ball`. It works directly with
the density maximizer from `deltaMax_attained`. -/
def large_delta_test_net {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hδ_large : δ ≥ 1 / 2) (L : ENNReal)
    (hL_one : 1 ≤ L) (hL_ne_top : L ≠ ⊤)
    (hL_big : (64000 : ENNReal) ≤ L) :
    RandomTranslation.TubeDensityTestNet δ := by
  let B20 : Set Point3 := Metric.closedBall (0 : Point3) 20
  let testSets : Finset (Set Point3) := {B20}

  have hB20_convex : Convex ℝ B20 := convex_closedBall (0 : Point3) 20
  have hB20_measurable : MeasurableSet B20 := isClosed_closedBall.measurableSet
  have hB20_vol_pos : 0 < volume B20 := by
    have h : (interior B20).Nonempty := by
      refine ⟨0, ?_⟩
      have h2 : (0 : Point3) ∈ Metric.ball (0 : Point3) 20 := by simp <;> norm_num
      have h3 : Metric.ball (0 : Point3) 20 ⊆ interior B20 := ball_subset_interior_closedBall
      exact h3 h2
    exact MeasureTheory.Measure.measure_pos_of_nonempty_interior volume h
  have hB20_vol_ne_top : volume B20 ≠ ⊤ := by
    have h_bdd : Bornology.IsBounded (B20) := Metric.isBounded_closedBall
    exact h_bdd.measure_lt_top.ne

  have h_density_suffices :
      ∀ (G : TubeFamily δ),
        (∀ i, (G.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 10) →
        ∀ (C : ENNReal),
          (∀ K ∈ testSets, G.toBodyFamily.density K ≤ C) →
          G.toBodyFamily.deltaMax ≤ L * C := by
    intro G hG C hC
    let F := G.toBodyFamily
    rcases deltaMax_attained F with ⟨W, hW_convex, hW_density⟩

    by_cases h_zero : F.deltaMax = 0
    · rw [h_zero] <;> simp

    have h_density_pos : 0 < F.density W := by
      rw [hW_density]
      exact bot_lt_iff_ne_bot.mpr h_zero

    have h_mass_pos : 0 < F.containedMass W := by
      by_contra h
      have h' : F.containedMass W = 0 := by simpa using h
      have h_density_zero : F.density W = 0 := by
        dsimp only [BodyFamily.density]
        rw [h'] <;> simp
      rw [h_density_zero] at h_density_pos
      exact False.elim (lt_irrefl 0 h_density_pos)

    have h_indices_nonempty : (F.containedIndices W).Nonempty := by
      by_contra h
      have h' : F.containedIndices W = ∅ := by simpa using h
      have h'' : F.containedMass W = 0 := by
        rw [BodyFamily.containedMass, h'] <;> simp
      exact h_mass_pos.ne' h''

    rcases h_indices_nonempty with ⟨i, hi⟩
    have h_tube_sub_W : (G.tube i).carrier ⊆ W := by
      have h_i_in : i ∈ F.containedIndices W := hi
      have h' : (F.body i).carrier ⊆ W := by
        simpa [BodyFamily.containedIndices, Finset.mem_filter] using h_i_in
      have h_eq : (G.tube i).carrier = (F.body i).carrier := by rfl
      rw [h_eq]; exact h'

    have h_ball_W : Metric.closedBall (G.tube i).base δ ⊆ W :=
      subset_trans (tube_contains_ball hδ (G.tube i)) h_tube_sub_W

    have h_vol_W_lower : volume W ≥ volume (Metric.closedBall (0 : Point3) δ) := by
      have h1 : volume (Metric.closedBall (G.tube i).base δ) ≤ volume W :=
        measure_mono h_ball_W
      have h2 : volume (Metric.closedBall (G.tube i).base δ) =
          volume (Metric.closedBall (0 : Point3) δ) := by
        rw [EuclideanSpace.volume_closedBall_fin_three (G.tube i).base δ,
            EuclideanSpace.volume_closedBall_fin_three (0 : Point3) δ]
      rw [h2] at h1
      exact h1

    have h_vol_W_half : volume W ≥ volume (Metric.closedBall (0 : Point3) (1 / 2)) := by
      have h3 : (1 / 2 : ℝ) ≤ δ := by linarith
      have h4 : Metric.closedBall (0 : Point3) (1 / 2) ⊆ Metric.closedBall (0 : Point3) δ := by
        intro x hx
        have h5 : dist x (0 : Point3) ≤ 1 / 2 := by simpa [Metric.mem_closedBall] using hx
        have h6 : dist x (0 : Point3) ≤ δ := by linarith
        simpa [Metric.mem_closedBall] using h6
      have h5 : volume (Metric.closedBall (0 : Point3) (1 / 2)) ≤
          volume (Metric.closedBall (0 : Point3) δ) := measure_mono h4
      exact le_trans h5 h_vol_W_lower

    have h_vol_W_pos : 0 < volume W := by
      have h_pos : 0 < volume (Metric.closedBall (0 : Point3) (1 / 2)) := by
        have h_ball : Metric.ball (0 : Point3) (1 / 2) ⊆ interior (Metric.closedBall (0 : Point3) (1 / 2)) :=
          ball_subset_interior_closedBall
        have h : (interior (Metric.closedBall (0 : Point3) (1 / 2))).Nonempty := by
          refine ⟨0, h_ball ?_⟩
          simp <;> norm_num
        exact MeasureTheory.Measure.measure_pos_of_nonempty_interior volume h
      exact lt_of_lt_of_le h_pos h_vol_W_half

    have h_vol_W_ne_top : volume W ≠ ⊤ := by
      by_contra h_top
      have h_density_zero : F.density W = 0 := by
        dsimp only [BodyFamily.density]
        rw [h_top] <;> simp
      rw [h_density_zero] at h_density_pos
      exact False.elim (lt_irrefl 0 h_density_pos)

    have h_mass_W_le_B20 : F.containedMass W ≤ F.containedMass B20 := by
      dsimp only [BodyFamily.containedMass]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [BodyFamily.containedIndices, Finset.mem_filter] at hj ⊢
        have h_tube_in_B10 : (G.tube j).carrier ⊆ Metric.closedBall (0 : Point3) 10 := hG j
        have h_B10_sub_B20 : Metric.closedBall (0 : Point3) 10 ⊆ B20 := by
          intro x hx
          have h8 : dist x (0 : Point3) ≤ 10 := by simpa [Metric.mem_closedBall] using hx
          have h9 : dist x (0 : Point3) ≤ 20 := by linarith
          simpa [B20, Metric.mem_closedBall] using h9
        have h_tube_in_B20 : (G.tube j).carrier ⊆ B20 :=
          subset_trans h_tube_in_B10 h_B10_sub_B20
        exact ⟨hj.1, h_tube_in_B20⟩
      · intro _ _ _; simp

    have h_vol_B20_le : volume B20 ≤ (64000 : ENNReal) * volume W := by
      calc volume B20
        = 64000 * volume (Metric.closedBall (0 : Point3) (1 / 2)) := ball20_ball_half_ratio
      _ ≤ 64000 * volume W := mul_le_mul_of_nonneg_left h_vol_W_half (by positivity)

    have h_vol_B20_le_L : volume B20 ≤ L * volume W := by
      have h : (64000 : ENNReal) * volume W ≤ L * volume W := by
        gcongr <;> exact hL_big
      exact h_vol_B20_le.trans h

    have h_density_B20 : F.density B20 ≤ C := hC B20 (by simp [testSets])

    have h_density_ge : F.density W ≤ L * F.density B20 := by
      dsimp only [BodyFamily.density]
      exact ennreal_density_ineq
        (F.containedMass W) (volume W)
        (F.containedMass B20) (volume B20) L
        hL_one hL_ne_top h_mass_W_le_B20 h_vol_B20_le_L
        h_vol_W_pos hB20_vol_pos h_vol_W_ne_top hB20_vol_ne_top

    have h_final : F.deltaMax ≤ L * F.density B20 := by
      rw [←hW_density]
      exact h_density_ge

    exact le_trans h_final (mul_le_mul_of_nonneg_left h_density_B20 (by positivity))

  exact
    { testSets := testSets
      testSets_convex := by
        intro K hK
        have hK' : K = B20 := by simpa [testSets] using hK
        rw [hK']; exact hB20_convex
      testSets_measurable := by
        intro K hK
        have hK' : K = B20 := by simpa [testSets] using hK
        rw [hK']; exact hB20_measurable
      testSets_volume_pos := by
        intro K hK
        have hK' : K = B20 := by simpa [testSets] using hK
        rw [hK']; exact hB20_vol_pos
      testSets_volume_ne_top := by
        intro K hK
        have hK' : K = B20 := by simpa [testSets] using hK
        rw [hK']; exact hB20_vol_ne_top
      testSets_supported := by
        intro K hK
        have hK' : K = B20 := by simpa [testSets] using hK
        exact hK'.symm ▸ by simp [B20]
      testSets_closed := by
        intro K hK
        have hK' : K = B20 := by simpa [testSets] using hK
        rw [hK']
        exact Metric.isClosed_closedBall
      lossFactor := L
      one_le_lossFactor := hL_one
      lossFactor_ne_top := hL_ne_top
      density_suffices := h_density_suffices }

end Kakeya.Streamlined
