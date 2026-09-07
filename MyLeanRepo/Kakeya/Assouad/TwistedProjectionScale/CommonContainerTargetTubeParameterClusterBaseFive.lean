import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CommonContainerDirectionCloseness
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CommonContainerBaseClosenessBaseFive
import MyLeanRepo.Kakeya.Assouad.Statements

/-!
# Common-container target-tube parameter cluster (radius-five basepoint window)

Two vertical rho-tubes in the radius-five basepoint window that lie in one
tau-tube occupy one explicit four-parameter box.
-/

noncomputable section

namespace Kakeya.Assouad

theorem common_container_target_tube_parameter_cluster_base_five :
    CommonContainerTargetTubeParameterClusterBaseFiveStatement := by
  intro rho tau hrho_pos hrho_le htau_small A B hAvert hBvert hAbase hBbase U hA_cont hB_cont
  have hrho_nonneg : 0 ≤ rho := by linarith
  have htau_nonneg : 0 ≤ tau := by linarith
  rcases direction_closeness_from_containment hrho_nonneg htau_nonneg A U hA_cont
    with ⟨signA, hsignA_cases, hA_dir_close⟩
  rcases direction_closeness_from_containment hrho_nonneg htau_nonneg B U hB_cont
    with ⟨signB, hsignB_cases, hB_dir_close⟩
  let sign : ℝ := signA * signB
  have hsign : sign = 1 ∨ sign = -1 := by
    rcases hsignA_cases with (rfl | rfl) <;>
      rcases hsignB_cases with (rfl | rfl) <;> norm_num
  have hdir_close : ‖A.direction - sign • B.direction‖ ≤ 8 * tau := by
    have h1 : A.direction - sign • B.direction =
        (A.direction - signA • U.direction) +
          signA • (U.direction - signB • B.direction) := by
      rcases hsignA_cases with (rfl | rfl)
      · simp [sign, smul_smul] <;> abel
      · simp [sign, smul_smul] <;> abel
    rw [h1]
    have h2 :
        ‖(A.direction - signA • U.direction) +
            signA • (U.direction - signB • B.direction)‖ ≤
          ‖A.direction - signA • U.direction‖ +
            ‖signA • (U.direction - signB • B.direction)‖ :=
      norm_add_le _ _
    have h3 : ‖signA • (U.direction - signB • B.direction)‖ =
        |signA| * ‖U.direction - signB • B.direction‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    have h4 : |signA| = 1 := by
      rcases hsignA_cases with (rfl | rfl) <;> norm_num
    have h5 : ‖U.direction - signB • B.direction‖ =
        ‖B.direction - signB • U.direction‖ := by
      rcases hsignB_cases with (rfl | rfl)
      · have h6 : U.direction - (1 : ℝ) • B.direction =
            -(B.direction - (1 : ℝ) • U.direction) := by
          simp <;> abel
        rw [h6, norm_neg]
      · have h6 : U.direction - (-1 : ℝ) • B.direction =
            B.direction - (-1 : ℝ) • U.direction := by
          simp <;> abel
        rw [h6]
    rw [h3, h4, h5] at h2
    linarith [hA_dir_close, hB_dir_close]
  rcases base_closeness_from_common_containment_base_five
      hrho_nonneg htau_nonneg A B U hA_cont hB_cont hAbase htau_small with
    ⟨P, hP_axis, hbase_close, hP_norm⟩
  have h_abs_sub : ∀ (a b : ℝ), |a - b| ≤ |a| + |b| := by
    intro a b
    have h : |a + (-b)| ≤ |a| + |(-b)| := norm_add_le a (-b)
    have h2 : |(-b)| = |b| := by rw [abs_neg]
    simpa [sub_eq_add_neg, h2] using h
  have hcoord : ∀ (x : Point3) (k : Fin 3), |x k| ≤ ‖x‖ := by
    intro x k
    let f : Fin 3 → ℝ := fun i => (x i)^2
    have h2 : ∀ i ∈ Finset.univ, 0 ≤ f i := by
      intro i _
      positivity
    have h1 : f k ≤ ∑ i : Fin 3, f i :=
      Finset.single_le_sum h2 (Finset.mem_univ k)
    have h_sum_nonneg : 0 ≤ ∑ i : Fin 3, f i := by positivity
    have h3 : ‖x‖^2 = ∑ i : Fin 3, f i := by
      have h4 : ‖x‖ = Real.sqrt (∑ i : Fin 3, f i) := by
        simp [EuclideanSpace.norm_eq, f]
      rw [h4, Real.sq_sqrt h_sum_nonneg]
    have h4 : (x k)^2 ≤ ‖x‖^2 := by
      simpa [f, h3] using h1
    have h5 : |x k|^2 ≤ ‖x‖^2 := by
      have h6 : |x k|^2 = (x k)^2 := by rw [sq_abs]
      rw [h6]
      exact h4
    have h7 : 0 ≤ ‖x‖ := by positivity
    have h8 : |(|x k|)| ≤ |(‖x‖)| := sq_le_sq.mp h5
    have h9 : |(|x k|)| = |x k| := by simp
    have h10 : |(‖x‖)| = ‖x‖ := by simp [abs_of_nonneg h7]
    rw [h9, h10] at h8
    exact h8
  have hdir_coord :
      ∀ k : Fin 3, |A.direction k - sign * B.direction k| ≤ 8 * tau := by
    intro k
    have h1 :
        |A.direction k - sign * B.direction k| ≤
          ‖A.direction - sign • B.direction‖ :=
      hcoord (A.direction - sign • B.direction) k
    exact le_trans h1 hdir_close
  have hB_coord : ∀ k : Fin 3, |B.direction k| ≤ 1 := by
    intro k
    have h : |B.direction k| ≤ ‖B.direction‖ := hcoord B.direction k
    rw [B.direction_unit] at h
    exact h
  have hA_coord : ∀ k : Fin 3, |A.direction k| ≤ 1 := by
    intro k
    have h : |A.direction k| ≤ ‖A.direction‖ := hcoord A.direction k
    rw [A.direction_unit] at h
    exact h
  have hA2 : A.direction 2 ≠ 0 := by
    have h : (1 / 2 : ℝ) ≤ |A.direction 2| := hAvert
    intro h0
    rw [h0] at h
    norm_num at h
  have hB2 : B.direction 2 ≠ 0 := by
    have h : (1 / 2 : ℝ) ≤ |B.direction 2| := hBvert
    intro h0
    rw [h0] at h
    norm_num at h
  have hdenom : |A.direction 2 * B.direction 2| ≥ 1 / 4 := by
    rw [abs_mul]
    nlinarith [hAvert, hBvert]
  let cA := (tubeParamsOfTube A).c
  let cB := (tubeParamsOfTube B).c
  let dA := (tubeParamsOfTube A).d
  let dB := (tubeParamsOfTube B).d
  have hcA_eq : cA = A.direction 0 / A.direction 2 := by rfl
  have hcB_eq : cB = B.direction 0 / B.direction 2 := by rfl
  have hdA_eq : dA = A.direction 1 / A.direction 2 := by rfl
  have hdB_eq : dB = B.direction 1 / B.direction 2 := by rfl
  have h_slope_diff :
      ∀ i : Fin 3,
        |A.direction i / A.direction 2 -
            B.direction i / B.direction 2| ≤ 64 * tau := by
    intro i
    set num :=
      (A.direction i - sign * B.direction i) * B.direction 2 -
        B.direction i * (A.direction 2 - sign * B.direction 2)
    have h_formula :
        A.direction i / A.direction 2 -
            B.direction i / B.direction 2 =
          num / (A.direction 2 * B.direction 2) := by
      field_simp [hA2, hB2] <;> ring
    rw [h_formula]
    have hnum_bound : |num| ≤ 16 * tau := by
      have h1 :
          |num| ≤
            |(A.direction i - sign * B.direction i) * B.direction 2| +
              |B.direction i *
                (A.direction 2 - sign * B.direction 2)| :=
        h_abs_sub _ _
      rw [abs_mul, abs_mul] at h1
      have h8 :
          |A.direction i - sign * B.direction i| *
              |B.direction 2| ≤
            (8 * tau) * 1 := by
        gcongr <;> linarith [hdir_coord i, hB_coord 2]
      have h9 :
          |B.direction i| *
              |A.direction 2 - sign * B.direction 2| ≤
            1 * (8 * tau) := by
        gcongr <;> linarith [hB_coord i, hdir_coord 2]
      linarith
    rw [abs_div]
    have hdenom_pos : 0 < |A.direction 2 * B.direction 2| := by
      linarith
    calc
      |num| / |A.direction 2 * B.direction 2| ≤
          (16 * tau) / |A.direction 2 * B.direction 2| := by
        gcongr
      _ ≤ (16 * tau) / (1 / 4 : ℝ) := by
        gcongr <;> linarith
      _ = 64 * tau := by ring
  have hc : |cA - cB| ≤ 64 * tau := by
    rw [hcA_eq, hcB_eq]
    exact h_slope_diff 0
  have hd : |dA - dB| ≤ 64 * tau := by
    rw [hdA_eq, hdB_eq]
    exact h_slope_diff 1
  let aA := (tubeParamsOfTube A).a
  let aB := (tubeParamsOfTube B).a
  let bA := (tubeParamsOfTube A).b
  let bB := (tubeParamsOfTube B).b
  have hP0 : P 0 = aB + cB * P 2 :=
    tubeAxisLine_coord_zero B hB2 hP_axis
  have hP1 : P 1 = bB + dB * P 2 :=
    tubeAxisLine_coord_one B hB2 hP_axis
  have hP2 : |P 2| ≤ 6 := by
    have h : |P 2| ≤ ‖P‖ := hcoord P 2
    linarith [hP_norm]
  have hbase_coord : ∀ k : Fin 3, |A.base k - P k| ≤ 20 * tau := by
    intro k
    have h1 : |A.base k - P k| ≤ ‖A.base - P‖ :=
      hcoord (A.base - P) k
    exact le_trans h1 hbase_close
  have hcA_bound : |cA| ≤ 2 := by
    rw [hcA_eq, abs_div]
    calc
      |A.direction 0| / |A.direction 2| ≤
          1 / |A.direction 2| := by
        gcongr <;> linarith [hA_coord 0]
      _ ≤ 1 / (1 / 2 : ℝ) := by
        gcongr <;> linarith
      _ = 2 := by norm_num
  have hdA_bound : |dA| ≤ 2 := by
    rw [hdA_eq, abs_div]
    calc
      |A.direction 1| / |A.direction 2| ≤
          1 / |A.direction 2| := by
        gcongr <;> linarith [hA_coord 1]
      _ ≤ 1 / (1 / 2 : ℝ) := by
        gcongr <;> linarith
      _ = 2 := by norm_num
  have haA_eq : aA = A.base 0 - A.base 2 * cA := by
    dsimp only [aA, cA, tubeParamsOfTube]
    field_simp [hA2] <;> ring
  have hbA_eq : bA = A.base 1 - A.base 2 * dA := by
    dsimp only [bA, dA, tubeParamsOfTube]
    field_simp [hA2] <;> ring
  have h_abs3 :
      ∀ x y z : ℝ, |x - y + z| ≤ |x| + |y| + |z| := by
    intro x y z
    have h1 : |x - y + z| ≤ |x - y| + |z| :=
      norm_add_le (x - y) z
    linarith [h_abs_sub x y]
  have ha : |aA - aB| ≤ 100000 * tau := by
    have h_aB : aB = P 0 - cB * P 2 := by linarith [hP0]
    have h_formula :
        aA - aB =
          (A.base 0 - P 0) - (A.base 2 - P 2) * cA +
            P 2 * (cB - cA) := by
      rw [haA_eq, h_aB]
      ring
    rw [h_formula]
    have h_bound :=
      h_abs3 (A.base 0 - P 0)
        ((A.base 2 - P 2) * cA) (P 2 * (cB - cA))
    rw [abs_mul, abs_mul] at h_bound
    have h5 : |cB - cA| ≤ 64 * tau := by
      simpa [abs_sub_comm] using hc
    have h_prod1 :
        |A.base 2 - P 2| * |cA| ≤ (20 * tau) * 2 := by
      gcongr <;> linarith [hbase_coord 2, hcA_bound]
    have h_prod2 :
        |P 2| * |cB - cA| ≤ 6 * (64 * tau) := by
      gcongr <;> linarith
    linarith [h_bound, hbase_coord 0, h_prod1, h_prod2]
  have hb : |bA - bB| ≤ 100000 * tau := by
    have h_bB : bB = P 1 - dB * P 2 := by linarith [hP1]
    have h_formula :
        bA - bB =
          (A.base 1 - P 1) - (A.base 2 - P 2) * dA +
            P 2 * (dB - dA) := by
      rw [hbA_eq, h_bB]
      ring
    rw [h_formula]
    have h_bound :=
      h_abs3 (A.base 1 - P 1)
        ((A.base 2 - P 2) * dA) (P 2 * (dB - dA))
    rw [abs_mul, abs_mul] at h_bound
    have h5 : |dB - dA| ≤ 64 * tau := by
      simpa [abs_sub_comm] using hd
    have h_prod1 :
        |A.base 2 - P 2| * |dA| ≤ (20 * tau) * 2 := by
      gcongr <;> linarith [hbase_coord 2, hdA_bound]
    have h_prod2 :
        |P 2| * |dB - dA| ≤ 6 * (64 * tau) := by
      gcongr <;> linarith
    linarith [h_bound, hbase_coord 1, h_prod1, h_prod2]
  have hc_final :
      |(tubeParamsOfTube A).c - (tubeParamsOfTube B).c| ≤
        100000 * tau := by
    have h9 : |cA - cB| ≤ 64 * tau := hc
    have h10 : 64 * tau ≤ 100000 * tau := by
      nlinarith [htau_nonneg]
    exact le_trans h9 h10
  have hd_final :
      |(tubeParamsOfTube A).d - (tubeParamsOfTube B).d| ≤
        100000 * tau := by
    have h9 : |dA - dB| ≤ 64 * tau := hd
    have h10 : 64 * tau ≤ 100000 * tau := by
      nlinarith [htau_nonneg]
    exact le_trans h9 h10
  exact ⟨ha, hb, hc_final, hd_final⟩

end Kakeya.Assouad
