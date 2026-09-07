module

/-
# Steps 3-5: m-dimensional Marstrand with radial directions from X^m

Quantitative version with uniform constants: c_step depends only on m, c_X, M_X.
-/

public import MyLeanRepo.MarstrandArbitraryDim
public import MyLeanRepo.CoveringMeasureTranslation
public import MyLeanRepo.ExpansionLemma
public import MyLeanRepo.NrealScalingBounded
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Metric Classical BigOperators ProductLikeIncidence
open scoped BigOperators Pointwise

namespace WeakTwoEndsSumProduct

/-! ## Helper lemmas -/

/-- Volume scaling in m-dimensional Euclidean space. -/
lemma volume_smul_set {m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    {W : Set (EuclideanSpace ℝ (Fin m))} :
    volume (c • W) = ENNReal.ofReal (c ^ m) * volume W := by
  have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by
    simpa using finrank_euclideanSpace_fin
  have h := MeasureTheory.Measure.addHaar_smul_of_nonneg volume hc W
  rw [h_finrank] at h
  exact h

/-- Volume of the Cartesian power X^m in EuclideanSpace. -/
lemma volume_cartesian_power {m : ℕ} {X : Set ℝ} (hX_meas : MeasurableSet X) :
    volume {w : EuclideanSpace ℝ (Fin m) | ∀ i, w i ∈ X} = (volume X)^m := by
  let e : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ) := WithLp.ofLp
  have h_mp : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp (Fin m)
  let s : Fin m → Set ℝ := fun _ => X
  have h_s_meas : ∀ i, MeasurableSet (s i) := fun i => hX_meas
  have h_pi_meas : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi h_s_meas
  have h_preimage : e ⁻¹' (Set.univ.pi s) = {w : EuclideanSpace ℝ (Fin m) | ∀ i, w i ∈ X} := by
    ext w
    simp only [e, Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq, s]
    <;> rfl
  have h1 : volume {w : EuclideanSpace ℝ (Fin m) | ∀ i, w i ∈ X} = volume (Set.univ.pi s) := by
    rw [← h_preimage]
    exact h_mp.measure_preimage h_pi_meas.nullMeasurableSet
  rw [h1]
  have h2 : volume (Set.univ.pi s) = ∏ i : Fin m, volume (s i) :=
    MeasureTheory.volume_pi_pi s
  rw [h2]
  have h3 : ∏ i : Fin m, volume (s i) = (volume X)^m := by
    simp [s, Finset.prod_const] <;> rfl
  exact h3

/-- There exists r_min > 0 such that volume(ball(0, r_min)) < bound. -/
lemma exists_small_ball_volume {m : ℕ} (hm : 0 < m) {bound : ℝ} (hbound_pos : 0 < bound) :
    ∃ (r_min : ℝ), 0 < r_min ∧
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) < ENNReal.ofReal bound := by
  let r : ℝ := min (1 / 2) (bound / 2) / 2
  have hr_pos : 0 < r := by
    dsimp only [r]
    have h1 : 0 < min (1 / 2) (bound / 2) := by positivity
    linarith
  have h2r_lt_one : 2 * r < 1 := by
    dsimp only [r]
    have h : 2 * r = min (1 / 2) (bound / 2) := by ring
    rw [h]
    exact min_lt_iff.mpr (Or.inl (by norm_num))
  have h2r_lt_bound : 2 * r < bound := by
    dsimp only [r]
    have h : 2 * r = min (1 / 2) (bound / 2) := by ring
    rw [h]
    exact min_lt_iff.mpr (Or.inr (by linarith))
  have h_pow_lt : (2 * r) ^ m < bound := by
    have h1 : 0 ≤ 2 * r := by positivity
    have h3 : ∀ n : ℕ, n ≥ 1 → (2 * r) ^ n ≤ 2 * r := by
      intro n hn
      induction' hn with n hn ih
      · norm_num
      · simp_all [pow_succ] <;> nlinarith
    have h4 : (2 * r) ^ m ≤ 2 * r := h3 m hm
    linarith
  have h_ball_subset : Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r ⊆
      {w : EuclideanSpace ℝ (Fin m) | ∀ i, |w i| < r} := by
    intro w hw
    have h_norm : ‖w‖ < r := by simpa [Metric.mem_ball] using hw
    intro i
    have h9 : |w i| ≤ ‖w‖ := PiLp.norm_apply_le w i
    linarith
  let e : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ) := WithLp.ofLp
  have h_mp : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp (Fin m)
  let s : Fin m → Set ℝ := fun _ => {t | |t| < r}
  have h_s_meas : ∀ i, MeasurableSet (s i) := by
    intro i
    have h_eq : s i = Set.Ioo (-r) r := by
      ext t; simp [s, abs_lt] <;> constructor <;> intro h <;> exact ⟨h.1, h.2⟩
    rw [h_eq]
    have h_open : IsOpen (Set.Ioo (-r) r) := isOpen_Ioo
    exact h_open.measurableSet
  have h_pi_meas : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi h_s_meas
  have h_set_eq : {w : EuclideanSpace ℝ (Fin m) | ∀ i, |w i| < r} = e ⁻¹' (Set.univ.pi s) := by
    ext w; simp [e, s] <;> rfl
  have h_vol_box : volume {w : EuclideanSpace ℝ (Fin m) | ∀ i, |w i| < r} =
      (volume {t : ℝ | |t| < r}) ^ m := by
    rw [h_set_eq]
    rw [h_mp.measure_preimage h_pi_meas.nullMeasurableSet]
    rw [MeasureTheory.volume_pi_pi s]
    simp [s, Finset.prod_const] <;> rfl
  have h_vol_interval : volume {t : ℝ | |t| < r} = ENNReal.ofReal (2 * r) := by
    have h9 : {t : ℝ | |t| < r} = Set.Ioo (-r) r := by
      ext t; simp [abs_lt] <;> constructor <;> intro h <;> exact ⟨h.1, h.2⟩
    rw [h9, Real.volume_Ioo]
    have h10 : ENNReal.ofReal (r - (-r)) = ENNReal.ofReal (2 * r) := by ring_nf
    rw [h10]
  have h_vol_bound : volume {w : EuclideanSpace ℝ (Fin m) | ∀ i, |w i| < r} =
      ENNReal.ofReal ((2 * r) ^ m) := by
    rw [h_vol_box, h_vol_interval]
    rw [← ENNReal.ofReal_pow] <;> positivity
  have h11 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r) ≤
      volume {w : EuclideanSpace ℝ (Fin m) | ∀ i, |w i| < r} :=
    measure_mono h_ball_subset
  rw [h_vol_bound] at h11
  have h_lt_ennreal : ENNReal.ofReal ((2 * r) ^ m) < ENNReal.ofReal bound := by exact (ofReal_lt_ofReal_iff hbound_pos).mpr h_pow_lt
  exact ⟨r, hr_pos, lt_of_le_of_lt h11 h_lt_ennreal⟩

/-- Norm bound for vectors in X^m when X ⊆ [-M_X, M_X]. -/
lemma norm_bound_of_in_box {m : ℕ} {X : Set ℝ} {M_X : ℝ} (hM_X_pos : 0 < M_X)
    (hX_bound : X ⊆ Set.Icc (-M_X) M_X)
    {w : EuclideanSpace ℝ (Fin m)} (hw : ∀ i, w i ∈ X) :
    ‖w‖ ≤ Real.sqrt (m : ℝ) * M_X := by
  have h1 : ∀ i : Fin m, |w i| ≤ M_X := by
    intro i
    have h2 : w i ∈ X := hw i
    have h3 : w i ∈ Set.Icc (-M_X) M_X := hX_bound h2
    exact abs_le.mpr ⟨h3.1, h3.2⟩
  have h5 : ∀ i : Fin m, (w i)^2 ≤ M_X^2 := by
    intro i
    have h6 : |w i| ≤ M_X := h1 i
    have h7 : -M_X ≤ w i := (abs_le.mp h6).1
    have h8 : w i ≤ M_X := (abs_le.mp h6).2
    nlinarith
  have h4 : ∑ i : Fin m, (w i)^2 ≤ (m : ℝ) * M_X^2 := by
    have h_sum : ∑ i : Fin m, (w i)^2 ≤ ∑ i : Fin m, M_X^2 := by
      apply Finset.sum_le_sum; intro i _; exact h5 i
    have h_eq : ∑ i : Fin m, M_X^2 = (m : ℝ) * M_X^2 := by
      simp [Finset.sum_const] <;> ring
    rw [h_eq] at h_sum; exact h_sum
  have h9 : ‖w‖ = Real.sqrt (∑ i : Fin m, ‖w i‖ ^ 2) := by rw [EuclideanSpace.norm_eq]
  have h10 : 0 ≤ ∑ i : Fin m, ‖w i‖ ^ 2 := by positivity
  have h_norm2 : ‖w‖ ^ 2 = ∑ i : Fin m, (w i)^2 := by
    rw [h9, Real.sq_sqrt h10]
    apply Finset.sum_congr rfl; intro i _
    have h11 : ‖w i‖ = |w i| := by simp [Real.norm_eq_abs]
    rw [h11]; have h12 : |w i| ^ 2 = (w i)^2 := by simp [abs_pow] <;> ring
    exact h12
  have h11 : ‖w‖ ^ 2 ≤ (Real.sqrt (m : ℝ) * M_X)^2 := by
    rw [h_norm2]
    have h12 : (Real.sqrt (m : ℝ) * M_X)^2 = (m : ℝ) * M_X^2 := by
      have h13 : 0 ≤ M_X := by linarith
      have h14 : 0 ≤ (m : ℝ) := by positivity
      calc (Real.sqrt (m : ℝ) * M_X)^2
        = (Real.sqrt (m : ℝ))^2 * M_X^2 := by ring
      _ = (m : ℝ) * M_X^2 := by rw [Real.sq_sqrt h14] <;> ring
    rw [h12]; exact h4
  have h15 : 0 ≤ ‖w‖ := by positivity
  have h16 : 0 ≤ Real.sqrt (m : ℝ) * M_X := by positivity
  nlinarith

/-- The linear projection of A^m along θ = c • x equals c times the scaled sumset. -/
lemma projection_eq_scaled_sumset {m : ℕ} {x : EuclideanSpace ℝ (Fin m)}
    {A : Set ℝ} {c : ℝ} {θ : EuclideanSpace ℝ (Fin m)}
    (hθ : θ = c • x) :
    ProductLikeIncidence.linearProjection θ ''
      {p : EuclideanSpace ℝ (Fin m) | ∀ i, p i ∈ A} =
    (fun t : ℝ => c * t) '' (ExpansionLemma.scaledSumset (fun i => x i) A) := by
  let e : EuclideanSpace ℝ (Fin m) ≃ (Fin m → ℝ) := WithLp.equiv 2 (Fin m → ℝ)
  have h_inner_formula : ∀ (u v : EuclideanSpace ℝ (Fin m)),
      inner ℝ u v = ∑ i : Fin m, u i * v i := by
    intro u v
    have h1 : inner ℝ u v = ∑ i : Fin m, v i * u i := by
      rw [EuclideanSpace.inner_eq_star_dotProduct u v] <;> simp [dotProduct] <;> rfl
    rw [h1]
    apply Finset.sum_congr rfl
    intro i _; ring
  ext y
  simp only [Set.mem_image, ExpansionLemma.scaledSumset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have h_inner : inner ℝ θ p = c * ∑ i : Fin m, x i * p i := by
      rw [hθ, inner_smul_left]
      have h_star : (starRingEnd ℝ) c = c := by simp
      rw [h_star, h_inner_formula x p] <;> ring
    have h3 : ProductLikeIncidence.linearProjection θ p = c * ∑ i : Fin m, x i * p i := by
      simpa [ProductLikeIncidence.linearProjection] using h_inner
    rw [h3]
    let p' : Fin m → ℝ := e p
    have hpe : ∀ i, p' i = p i := by
      intro i; simp [p', e]
    have hp' : ∀ i, p' i ∈ A := by
      intro i; rw [hpe i]; exact hp i
    have hsum : ∑ i : Fin m, x i * p' i = ∑ i : Fin m, x i * p i := by
      apply Finset.sum_congr rfl; intro i _; rw [hpe i]
    exact ⟨∑ i : Fin m, x i * p i, ⟨p', hp', by rw [hsum]⟩, rfl⟩
  · rintro ⟨s, ⟨a, ha, rfl⟩, rfl⟩
    let a' : EuclideanSpace ℝ (Fin m) := e.symm a
    have hae : ∀ i, a' i = a i := by
      intro i; simp [a', e]
    have ha'_mem : ∀ i, a' i ∈ A := by
      intro i; rw [hae i]; exact ha i
    refine ⟨a', ha'_mem, ?_⟩
    have h_inner : inner ℝ θ a' = c * ∑ i : Fin m, x i * a i := by
      rw [hθ, inner_smul_left]
      have h_star : (starRingEnd ℝ) c = c := by simp
      rw [h_star, h_inner_formula x a']
      have hsum : ∑ i : Fin m, x i * a' i = ∑ i : Fin m, x i * a i := by
        apply Finset.sum_congr rfl; intro i _; rw [hae i]
      rw [hsum] <;> ring
    have h3 : ProductLikeIncidence.linearProjection θ a' = c * ∑ i : Fin m, x i * a i := by
      simpa [ProductLikeIncidence.linearProjection] using h_inner
    rw [h3] <;> ring

/-- The scaled sumset is bounded when the coefficient set and A are bounded. -/
lemma scaledSumset_bounded {m : ℕ} {x : Fin m → ℝ} {X A : Set ℝ} {M_X : ℝ}
    (hM_X_pos : 0 < M_X) (hX_bound : X ⊆ Set.Icc (-M_X) M_X) (hx : ∀ i, x i ∈ X)
    (hA_sub : A ⊆ Set.Icc 1 2) :
    Bornology.IsBounded (ExpansionLemma.scaledSumset x A) := by
  have h1 : ∀ i, |x i| ≤ M_X := by
    intro i
    have h2 : x i ∈ X := hx i
    have h3 : x i ∈ Set.Icc (-M_X) M_X := hX_bound h2
    exact abs_le.mpr ⟨h3.1, h3.2⟩
  have h4 : ∀ (s : ℝ), s ∈ ExpansionLemma.scaledSumset x A → |s| ≤ (m : ℝ) * M_X * 2 := by
    intro s hs
    rcases hs with ⟨a, ha, rfl⟩
    have h5 : ∀ i, |a i| ≤ 2 := by
      intro i
      have h6 : a i ∈ A := ha i
      have h7 : a i ∈ Set.Icc 1 2 := hA_sub h6
      have h71 : 1 ≤ a i := h7.1
      have h72 : a i ≤ 2 := h7.2
      have h8 : 0 ≤ a i := by linarith
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    calc |∑ i : Fin m, x i * a i|
      ≤ ∑ i : Fin m, |x i * a i| := by exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin m, |x i| * |a i| := by
      apply Finset.sum_congr rfl; intro i _; rw [abs_mul]
    _ ≤ ∑ i : Fin m, M_X * 2 := by
      apply Finset.sum_le_sum; intro i _
      have h10 : |x i| * |a i| ≤ M_X * 2 := by
        calc |x i| * |a i| ≤ M_X * |a i| := by gcongr <;> exact h1 i
          _ ≤ M_X * 2 := by gcongr <;> exact h5 i
      exact h10
    _ = (m : ℝ) * M_X * 2 := by
      simp [Finset.sum_const] <;> ring
  let B_val : ℝ := (m : ℝ) * M_X * 2
  have h5 : ExpansionLemma.scaledSumset x A ⊆ Set.Icc (-B_val) B_val := by
    intro s hs
    have h6 : |s| ≤ B_val := h4 s hs
    have h7 : -B_val ≤ s := by linarith [abs_le.mp h6]
    have h8 : s ≤ B_val := by linarith [abs_le.mp h6]
    exact ⟨h7, h8⟩
  have h6 : Bornology.IsBounded (Set.Icc (-B_val) B_val) := isCompact_Icc.isBounded
  exact Bornology.IsBounded.subset h6 h5

/-- Pure ENNReal arithmetic for the final step of Steps 3-5.
    Given `hL : ofReal(u/(C*B)) ≤ 3*ofReal(δ)*N_S` and
    `h_scale : K⁻¹ * N_S ≤ N_sumset`, deduce
    `ofReal(c_step/(B*δ)) ≤ N_sumset` where `c_step = u/(3*C*K)`. -/
lemma step3_5_final_arithmetic
    (u C B δ : ℝ) (K : ℕ) (c_step : ℝ)
    (hC_pos : 0 < C) (hB_pos : 0 < B) (hδ_pos : 0 < δ) (hK_pos : 0 < K)
    (hc_step_def : c_step = u / (3 * C * (K : ℝ)))
    (N_S N_sumset : ENNReal)
    (hL : ENNReal.ofReal (u / (C * B)) ≤ 3 * ENNReal.ofReal δ * N_S)
    (h_scale : (K : ENNReal)⁻¹ * N_S ≤ N_sumset) :
    ENNReal.ofReal (c_step / (B * δ)) ≤ N_sumset := by
  have hK_real_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
  set d : ENNReal := ENNReal.ofReal δ with hd_def
  set Kinv : ENNReal := (K : ENNReal)⁻¹ with hKinv_def
  have h1 : Kinv * ENNReal.ofReal (u / (C * B)) ≤ Kinv * (3 * d * N_S) :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have h2 : Kinv * (3 * d * N_S) = 3 * d * (Kinv * N_S) := by
    ac_rfl
  have h3 : 3 * d * (Kinv * N_S) ≤ 3 * d * N_sumset :=
    mul_le_mul_of_nonneg_left h_scale (by positivity)
  have h41 : Kinv = ENNReal.ofReal ((K : ℝ)⁻¹) := by
    have h_natCast : (K : ENNReal) = ENNReal.ofReal (K : ℝ) := by
      norm_cast
    rw [hKinv_def, h_natCast, ENNReal.ofReal_inv_of_pos hK_real_pos]
  have h4 : Kinv * ENNReal.ofReal (u / (C * B)) =
      ENNReal.ofReal (u / (C * B * (K : ℝ))) := by
    rw [h41, ← ENNReal.ofReal_mul (by positivity)]
    <;> congr 1 <;> field_simp [hK_real_pos.ne'] <;> ring
  have h5 : ENNReal.ofReal (u / (C * B * (K : ℝ))) ≤ 3 * d * N_sumset := by
    rw [h4] at h1
    rw [h2] at h1
    exact le_trans h1 h3
  set B3 : ENNReal := 3 * d with hB3_def
  have hB3_eq : B3 = ENNReal.ofReal (3 * δ) := by
    simp [hB3_def, hd_def, ← ENNReal.ofReal_mul (by positivity)] <;> norm_cast
  have hB3_ne_zero : B3 ≠ 0 := by positivity
  have hB3_ne_top : B3 ≠ ⊤ := by
    rw [hB3_eq]
    exact ENNReal.top_ne_ofReal.symm
  have h6 : B3⁻¹ * ENNReal.ofReal (u / (C * B * (K : ℝ))) ≤ N_sumset := by
    have h61 : B3⁻¹ * ENNReal.ofReal (u / (C * B * (K : ℝ))) ≤
        B3⁻¹ * (B3 * N_sumset) := by
      have h5' : ENNReal.ofReal (u / (C * B * (K : ℝ))) ≤ B3 * N_sumset := by
        exact hB3_def ▸ h5
      exact mul_le_mul_of_nonneg_left h5' (by positivity)
    have h62 : B3⁻¹ * (B3 * N_sumset) = N_sumset := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hB3_ne_zero hB3_ne_top]
      <;> exact one_mul _
    rw [h62] at h61
    exact h61
  have h7 : B3⁻¹ * ENNReal.ofReal (u / (C * B * (K : ℝ))) =
      ENNReal.ofReal (u / (3 * C * B * (K : ℝ) * δ)) := by
    have hB3_inv : B3⁻¹ = ENNReal.ofReal ((3 * δ)⁻¹) := by
      rw [hB3_eq, ENNReal.ofReal_inv_of_pos (by positivity)]
    rw [hB3_inv, ← ENNReal.ofReal_mul (by positivity)]
    <;> congr 1 <;> field_simp [hδ_pos.ne'] <;> ring
  have h13 : u / (3 * C * B * (K : ℝ) * δ) = c_step / (B * δ) := by
    rw [hc_step_def]
    <;> field_simp [hC_pos.ne', hB_pos.ne', hδ_pos.ne', hK_real_pos.ne'] <;> ring
  rw [h7, h13] at h6
  exact h6

/-! ## Main theorem: Steps 3-5 -/

/-- **Steps 3-5**: Given uniform constants c_X, M_X, there exists c_step > 0
    depending only on m, c_X, M_X such that for all X, A, ν, δ, B, there exist
    x_i ∈ X with N_δ(Σ x_i·A) ≥ c_step / (B·δ). -/
theorem step3_5_marstrand_mdim
    {m : ℕ} (hm : 2 ≤ m)
    {c_X M_X : ℝ} (hcX_pos : 0 < c_X) (hM_X_pos : 0 < M_X) :
    ∃ (c_step : ℝ), 0 < c_step ∧
      ∀ {X : Set ℝ} {A : Set ℝ} {δ B : ℝ}
        (ν : Measure (EuclideanSpace ℝ (Fin m)))
        [IsProbabilityMeasure ν],
        IsCompact X →
        ENNReal.ofReal c_X ≤ volume X →
        X ⊆ Set.Icc (-M_X) M_X →
        A ⊆ Set.Icc 1 2 →
        (hδ_pos : 0 < δ) → (hB_pos : 0 < B) →
        ν.support ⊆ {x | ∀ i, x i ∈ A} →
        IsCompact ν.support →
        (h_energy : robust_projection_main.rieszEnergy (α := 1) (hδ := hδ_pos) ν ≤ ENNReal.ofReal B) →
        ∃ (x : Fin m → ℝ), (∀ i, x i ∈ X) ∧
          ENNReal.ofReal (c_step / (B * δ)) ≤ Nreal δ (ExpansionLemma.scaledSumset x A) := by
  have hm_pos : 0 < m := by linarith
  let R : ℝ := Real.sqrt (m : ℝ) * M_X
  have hR_pos : 0 < R := by positivity
  -- Choose r_min uniformly (depends only on m, c_X)
  have hP : ∃ (r_min : ℝ), 0 < r_min ∧
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) < ENNReal.ofReal (c_X ^ m / 2) :=
    exists_small_ball_volume hm_pos (by positivity)
  let r_min : ℝ := Classical.choose hP
  have hr_min_pos : 0 < r_min := (Classical.choose_spec hP).1
  have hball_small : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) <
      ENNReal.ofReal (c_X ^ m / 2) := (Classical.choose_spec hP).2
  let L_scale : ℝ := 1 / r_min
  have hL_scale_pos : 0 < L_scale := by positivity
  -- Sphere constants
  let volSphere : ENNReal := (volume.toSphere : Measure (Sphere m)) Set.univ
  have h_volSphere_pos : 0 < volSphere := by
    let vol : Measure (Sphere m) := volume.toSphere
    have hfin : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) := by
      have h : 0 < m := by linarith
      simpa [finrank_euclideanSpace_fin] using h
    let i0 : Fin m := ⟨0, by linarith⟩
    haveI : Nontrivial (EuclideanSpace ℝ (Fin m)) := by
      refine' ⟨EuclideanSpace.single i0 1, 0, _⟩
      intro h_eq
      have h9 : (EuclideanSpace.single i0 1 : EuclideanSpace ℝ (Fin m)) i0 =
          (0 : EuclideanSpace ℝ (Fin m)) i0 := by rw [h_eq]
      simpa [EuclideanSpace.single_apply] using h9
    have h5 : vol ≠ 0 := MeasureTheory.Measure.toSphere_ne_zero (μ := volume)
    have h : vol Set.univ ≠ 0 := by
      intro h2
      have h3 : vol = 0 := Measure.measure_univ_eq_zero.mp h2
      exact h5 h3
    exact pos_iff_ne_zero.mpr h
  have h_volSphere_lt_top : volSphere ≠ ⊤ :=
    MeasureTheory.measure_ne_top (volume.toSphere) Set.univ
  let u_X : ℝ := volSphere.toReal⁻¹ * (m : ℝ) * (1 / (2 * R)) ^ m * (c_X ^ m / 2)
  have hu_X_pos : 0 < u_X := by
    dsimp only [u_X]
    have h1 : 0 < volSphere.toReal := ENNReal.toReal_pos h_volSphere_pos.ne' h_volSphere_lt_top
    positivity
  let C_m := marstrandSphereConstant m
  have hC_m_pos : 0 < C_m := by
    dsimp only [C_m, marstrandSphereConstant]
    have h_d_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m from by linarith)
    exact mul_pos (mul_pos (by positivity) h_d_pos) Real.pi_pos
  -- Get uniform K_scale (depends only on L_scale, not on δ)
  rcases Nreal_scaling_bounded_uniform (hL_pos := hL_scale_pos) with
    ⟨K_scale, hK_scale_pos, hK_scale_uniform⟩
  let c_step : ℝ := u_X / (3 * C_m * (K_scale : ℝ))
  have hc_step_pos : 0 < c_step := by
    dsimp only [c_step]
    have h1 : 0 < u_X := hu_X_pos
    have h2 : 0 < (K_scale : ℝ) := by exact_mod_cast hK_scale_pos
    positivity
  refine ⟨c_step, hc_step_pos, ?_⟩
  intro X A δ B ν _ hX_compact hX_vol hX_bound hA_sub hδ_pos hB_pos hν_support hν_support_compact h_energy
  have hX_meas : MeasurableSet X := hX_compact.measurableSet
  let Xpow : Set (EuclideanSpace ℝ (Fin m)) := {w | ∀ i, w i ∈ X}
  have hXpow_vol : volume Xpow = (volume X)^m := volume_cartesian_power hX_meas
  have hXpow_lower : ENNReal.ofReal (c_X ^ m) ≤ volume Xpow := by
    rw [hXpow_vol]
    have h1 : ENNReal.ofReal c_X ≤ volume X := hX_vol
    have h2 : (ENNReal.ofReal c_X)^m ≤ (volume X)^m := by exact ENNReal.pow_le_pow_left hX_vol
    have h3 : ENNReal.ofReal (c_X ^ m) = (ENNReal.ofReal c_X)^m := by
      rw [← ENNReal.ofReal_pow] <;> linarith
    rw [h3]; exact h2
  have hXpow_norm_bound : ∀ w ∈ Xpow, ‖w‖ ≤ R := by
    intro w hw; exact norm_bound_of_in_box hM_X_pos hX_bound hw
  let W : Set (EuclideanSpace ℝ (Fin m)) := {w | (∀ i, w i ∈ X) ∧ r_min ≤ ‖w‖}
  have hXpow_meas : MeasurableSet Xpow := by
    have h2 : Xpow = ⋂ b ∈ (Set.univ : Set (Fin m)), {w : EuclideanSpace ℝ (Fin m) | w b ∈ X} := by
      ext w; simp [Xpow]
    rw [h2]
    have h_meas : ∀ (i : Fin m), MeasurableSet {w : EuclideanSpace ℝ (Fin m) | w i ∈ X} := by
      intro i
      have h_cont : Continuous (fun (w : EuclideanSpace ℝ (Fin m)) => w i) :=
        PiLp.continuous_apply (p := (2 : ℝ≥0∞)) (β := fun (_ : Fin m) => ℝ) i
      exact hX_meas.preimage h_cont.measurable
    have hs : (Set.univ : Set (Fin m)).Countable := Set.countable_univ
    exact MeasurableSet.biInter hs (fun i _ => h_meas i)
  have hW_meas : MeasurableSet W := by
    have h_cont : Continuous (fun w : EuclideanSpace ℝ (Fin m) => ‖w‖) := by fun_prop
    have h_const : Continuous (fun (_ : EuclideanSpace ℝ (Fin m)) => r_min) := continuous_const
    have h2 : MeasurableSet {w : EuclideanSpace ℝ (Fin m) | r_min ≤ ‖w‖} :=
      (isClosed_le h_const h_cont).measurableSet
    exact hXpow_meas.inter h2
  have hXpow_disj : Disjoint W (Xpow ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) := by
    rw [Set.disjoint_left]
    intro w hw1 hw2
    have h3 : r_min ≤ ‖w‖ := hw1.2
    have h4 : ‖w‖ < r_min := by
      have h5 : w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min := hw2.2
      simpa [Metric.mem_ball] using h5
    linarith
  have hW_union : Xpow = W ∪ (Xpow ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) := by
    ext w
    simp only [W, Xpow, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hXpow
      by_cases hnorm : r_min ≤ ‖w‖
      · exact Or.inl ⟨hXpow, hnorm⟩
      · have h' : ‖w‖ < r_min := by linarith
        exact Or.inr ⟨hXpow, by simpa [Metric.mem_ball] using h'⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hXpow_meas2 : MeasurableSet Xpow := hXpow_meas
  have hBall_meas : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) := isOpen_ball.measurableSet
  have hW_vol_lower : ENNReal.ofReal (c_X ^ m / 2) ≤ volume W := by
    let Bset := Xpow ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min
    have hBset_meas : MeasurableSet Bset := hXpow_meas2.inter hBall_meas
    have h_eq : volume Xpow = volume W + volume Bset := by
      have h1 : volume Xpow = volume (W ∪ Bset) := congr_arg volume hW_union
      have h2 : volume (W ∪ Bset) = volume W + volume Bset :=
        MeasureTheory.measure_union' hXpow_disj hW_meas
      exact Eq.trans h1 h2
    have h_ball2 : volume (Xpow ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) :=
      measure_mono fun x hx => hx.2
    have h_ball_small2 : volume (Xpow ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) < ENNReal.ofReal (c_X ^ m / 2) :=
      lt_of_le_of_lt h_ball2 hball_small
    by_contra h
    have h_lt : volume W < ENNReal.ofReal (c_X ^ m / 2) := by
      by_cases h_le : ENNReal.ofReal (c_X ^ m / 2) ≤ volume W
      · exact False.elim (h h_le)
      · exact lt_of_not_ge h_le
    have h_sum_lt : volume W + volume (Xpow ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) < ENNReal.ofReal (c_X ^ m) := by
      have h_ball_ne_top : volume (Xpow ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) ≠ ⊤ := by
        apply ne_top_of_le_ne_top (show volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) ≠ ⊤ from by exact measure_ball_ne_top)
        exact h_ball2
      have h_step1 : volume W + volume (Xpow ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) <
          ENNReal.ofReal (c_X ^ m / 2) + volume (Xpow ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) :=
        ENNReal.add_lt_add_right h_ball_ne_top h_lt
      have h_cX_ne_top : ENNReal.ofReal (c_X ^ m / 2) ≠ ⊤ := ENNReal.ofReal_ne_top
      have h_step2 : ENNReal.ofReal (c_X ^ m / 2) + volume (Xpow ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) <
          ENNReal.ofReal (c_X ^ m / 2) + ENNReal.ofReal (c_X ^ m / 2) :=
        ENNReal.add_lt_add_left h_cX_ne_top h_ball_small2
      have h_eq2 : ENNReal.ofReal (c_X ^ m / 2) + ENNReal.ofReal (c_X ^ m / 2) = ENNReal.ofReal (c_X ^ m) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)] <;> ring_nf
      calc volume W + volume (Xpow ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min)
        < ENNReal.ofReal (c_X ^ m / 2) + volume (Xpow ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r_min) := h_step1
      _ < ENNReal.ofReal (c_X ^ m / 2) + ENNReal.ofReal (c_X ^ m / 2) := h_step2
      _ = ENNReal.ofReal (c_X ^ m) := h_eq2
    rw [h_eq] at hXpow_lower
    exact not_le.mpr h_sum_lt hXpow_lower
  have hW_no_zero : ∀ w ∈ W, w ≠ 0 := by
    intro w hw; have h1 : r_min ≤ ‖w‖ := hw.2; have h2 : 0 < ‖w‖ := by linarith
    intro h3; rw [h3] at h2 <;> simp at h2
  have hW_bound : ∀ w ∈ W, ‖w‖ ≤ R := by
    intro w hw; exact hXpow_norm_bound w hw.1
  let U : Set (Sphere m) := {θ | ∃ w ∈ W, θ.val = ‖w‖⁻¹ • w}
  have hW_compact : IsCompact W := by
    have hXpow_closed : IsClosed Xpow := by
      have h2 : Xpow = ⋂ b ∈ (Set.univ : Set (Fin m)), {w : EuclideanSpace ℝ (Fin m) | w b ∈ X} := by
        ext w; simp [Xpow]
      rw [h2]
      exact isClosed_biInter (fun i _ => hX_compact.isClosed.preimage (by fun_prop : Continuous (fun w : EuclideanSpace ℝ (Fin m) => w i)))
    have hXpow_bounded : Bornology.IsBounded Xpow := by
      have h : Xpow ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) R := by
        intro w hw
        have h3 : ‖w‖ ≤ R := hXpow_norm_bound w hw
        simpa [Metric.mem_closedBall] using h3
      have hcb : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) R) := by exact isCompact_closedBall 0 R
      exact hcb.isBounded.subset h
    have hXpow_compact : IsCompact Xpow :=
      Metric.isCompact_iff_isClosed_bounded.mpr ⟨hXpow_closed, hXpow_bounded⟩
    have h_cont_norm : Continuous (fun w : EuclideanSpace ℝ (Fin m) => ‖w‖) := by fun_prop
    have h_const : Continuous (fun (_ : EuclideanSpace ℝ (Fin m)) => r_min) := continuous_const
    have h2 : IsClosed {w : EuclideanSpace ℝ (Fin m) | r_min ≤ ‖w‖} :=
      isClosed_le h_const h_cont_norm
    have hW_eq : W = Xpow ∩ {w : EuclideanSpace ℝ (Fin m) | r_min ≤ ‖w‖} := by
      ext w; simp [W, Xpow] <;> tauto
    rw [hW_eq]
    exact hXpow_compact.inter_right h2
  let radialProj_W : {w : EuclideanSpace ℝ (Fin m) // w ∈ W} → Sphere m := fun x =>
    let w := x.val
    have h_pos : 0 < ‖w‖ := by
      have h1 : r_min ≤ ‖w‖ := x.property.2
      linarith
    ⟨‖w‖⁻¹ • w, by
      have h_ne : ‖w‖ ≠ 0 := h_pos.ne'
      simp [Metric.mem_sphere, dist_zero_right, norm_smul] <;> field_simp [h_ne] <;> ring⟩
  have h_norm_cont : Continuous (fun x : {w : EuclideanSpace ℝ (Fin m) // w ∈ W} => ‖x.val‖) := by fun_prop
  have h_norm_ne_zero : ∀ (x : {w : EuclideanSpace ℝ (Fin m) // w ∈ W}), ‖x.val‖ ≠ 0 := by
    intro x
    have h1 : r_min ≤ ‖x.val‖ := x.property.2
    have h2 : 0 < ‖x.val‖ := by linarith
    exact h2.ne'
  have h_inv_cont : Continuous (fun x : {w : EuclideanSpace ℝ (Fin m) // w ∈ W} => ‖x.val‖⁻¹) :=
    h_norm_cont.inv₀ h_norm_ne_zero
  have h_val_cont : Continuous (fun x : {w : EuclideanSpace ℝ (Fin m) // w ∈ W} => x.val) := continuous_subtype_val
  have h_underlying_cont : Continuous (fun x : {w : EuclideanSpace ℝ (Fin m) // w ∈ W} => ‖x.val‖⁻¹ • x.val) :=
    h_inv_cont.smul h_val_cont
  have h_sphere_mem : ∀ (x : {w : EuclideanSpace ℝ (Fin m) // w ∈ W}),
      ‖x.val‖⁻¹ • x.val ∈ (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) := by
    intro x
    have h_pos : 0 < ‖x.val‖ := by
      have h1 : r_min ≤ ‖x.val‖ := x.property.2
      linarith
    have h_ne : ‖x.val‖ ≠ 0 := h_pos.ne'
    simp [Metric.mem_sphere, dist_zero_right, norm_smul] <;> field_simp [h_ne] <;> ring
  have h_radial_cont : Continuous radialProj_W :=
    Continuous.subtype_mk h_underlying_cont h_sphere_mem
  have hU_eq : U = Set.range radialProj_W := by
    ext θ
    simp only [U, Set.mem_range, Set.mem_setOf_eq]
    <;> constructor
    · rintro ⟨w, hw, h_eq⟩
      refine ⟨⟨w, hw⟩, ?_⟩
      apply Subtype.ext
      simpa [radialProj_W] using h_eq.symm
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, by simp [radialProj_W]⟩
  have hU_compact : IsCompact U := by
    rw [hU_eq]
    haveI : CompactSpace {w : EuclideanSpace ℝ (Fin m) // w ∈ W} :=
      isCompact_iff_compactSpace.mp hW_compact
    exact isCompact_range h_radial_cont
  have hU_meas : MeasurableSet U := hU_compact.measurableSet
  have hU_pos : ENNReal.ofReal u_X ≤ sphereProbabilityMeasure m U := by
    let c_scale : ℝ := 1 / (2 * R)
    have hc_scale_pos : 0 < c_scale := by positivity
    let W' : Set (EuclideanSpace ℝ (Fin m)) := c_scale • W
    have hW'_sub : W' ⊆ Set.Ioo (0 : ℝ) 1 • (Subtype.val '' U) := by
      intro y hy
      rcases hy with ⟨w, hw, rfl⟩
      have h_norm_pos : 0 < ‖w‖ := by
        have h1 : r_min ≤ ‖w‖ := hw.2
        linarith
      let θ : Sphere m := ⟨‖w‖⁻¹ • w, by
        have h_ne : ‖w‖ ≠ 0 := h_norm_pos.ne'
        simp [Metric.mem_sphere, dist_zero_right, norm_smul] <;> field_simp [h_ne] <;> ring⟩
      have hθ_in_U : θ ∈ U := ⟨w, hw, rfl⟩
      have hθ_eq : θ.val = ‖w‖⁻¹ • w := rfl
      let r : ℝ := c_scale * ‖w‖
      have hr_pos : 0 < r := mul_pos hc_scale_pos h_norm_pos
      have hr_lt_one : r < 1 := by
        dsimp only [r, c_scale]
        have h5 : ‖w‖ ≤ R := hW_bound w hw
        calc (1 / (2 * R)) * ‖w‖ ≤ (1 / (2 * R)) * R := by gcongr
          _ = 1 / 2 := by field_simp [hR_pos.ne'] <;> ring
          _ < 1 := by norm_num
      have h_ne2 : ‖w‖ ≠ 0 := h_norm_pos.ne'
      have h7 : ‖w‖ • θ.val = w := by
        rw [hθ_eq]
        simp [smul_smul, h_ne2, one_smul] <;> field_simp [h_ne2] <;> ring
      have h6 : w = ‖w‖ • θ.val := h7.symm
      have h_main : c_scale • w = r • θ.val := by
        dsimp only [r]
        have h9 : c_scale • w = c_scale • (‖w‖ • θ.val) := by
          exact congr_arg (fun x => c_scale • x) h6
        rw [h9]
        exact smul_smul (c_scale : ℝ) (‖w‖ : ℝ) θ.val
      exact ⟨r, ⟨hr_pos, hr_lt_one⟩, θ.val, ⟨θ, hθ_in_U, rfl⟩, h_main.symm⟩
    have h_vol_W' : volume W' = ENNReal.ofReal (c_scale ^ m) * volume W :=
      volume_smul_set (by positivity)
    have h_val_image_meas : MeasurableSet (Subtype.val '' U) :=
      hU_compact.image continuous_subtype_val |>.measurableSet
    have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by
      simpa using finrank_euclideanSpace_fin
    have h_toSphere : volume.toSphere U = (m : ENNReal) * volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' U)) := by
      rw [MeasureTheory.Measure.toSphere_apply' volume hU_meas, h_finrank] <;> norm_cast
    have h1 : volume W' ≤ volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' U)) :=
      measure_mono hW'_sub
    have h2 : ENNReal.ofReal (c_scale ^ m) * ENNReal.ofReal (c_X ^ m / 2) ≤
        volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' U)) := by
      calc ENNReal.ofReal (c_scale ^ m) * ENNReal.ofReal (c_X ^ m / 2)
        ≤ ENNReal.ofReal (c_scale ^ m) * volume W := by gcongr
      _ = volume W' := by rw [← h_vol_W']
      _ ≤ volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' U)) := h1
    have h3 : (m : ENNReal) * (ENNReal.ofReal (c_scale ^ m) * ENNReal.ofReal (c_X ^ m / 2)) ≤
        volume.toSphere U := by
      rw [h_toSphere]; gcongr
    have h4 : (m : ENNReal) * (ENNReal.ofReal (c_scale ^ m) * ENNReal.ofReal (c_X ^ m / 2)) =
        ENNReal.ofReal ((m : ℝ) * c_scale ^ m * (c_X ^ m / 2)) := by
      have h_cast : (m : ENNReal) = ENNReal.ofReal (m : ℝ) := by norm_cast
      rw [h_cast]
      have h_pos1 : 0 ≤ (m : ℝ) := by positivity
      have h_pos2 : 0 ≤ c_scale ^ m := by positivity
      have h_pos3 : 0 ≤ c_X ^ m / 2 := by positivity
      have h_inner : ENNReal.ofReal (c_scale ^ m) * ENNReal.ofReal (c_X ^ m / 2) =
          ENNReal.ofReal (c_scale ^ m * (c_X ^ m / 2)) :=
        (ENNReal.ofReal_mul h_pos2).symm
      rw [h_inner]
      have h_outer : ENNReal.ofReal (m : ℝ) * ENNReal.ofReal (c_scale ^ m * (c_X ^ m / 2)) =
          ENNReal.ofReal ((m : ℝ) * (c_scale ^ m * (c_X ^ m / 2))) :=
        (ENNReal.ofReal_mul h_pos1).symm
      rw [h_outer]
      <;> congr 1 <;> ring
    rw [h4] at h3
    have h_volSphere_eq : volSphere = ENNReal.ofReal volSphere.toReal := by
      rw [ENNReal.ofReal_toReal h_volSphere_lt_top]
    have h_sphere_def : sphereProbabilityMeasure m U = volSphere⁻¹ * volume.toSphere U := by rfl
    rw [h_sphere_def]
    have h7 : volSphere⁻¹ * volume.toSphere U ≥
        volSphere⁻¹ * ENNReal.ofReal ((m : ℝ) * c_scale ^ m * (c_X ^ m / 2)) := by gcongr
    have h8 : volSphere⁻¹ * ENNReal.ofReal ((m : ℝ) * c_scale ^ m * (c_X ^ m / 2)) =
        ENNReal.ofReal u_X := by
      rw [h_volSphere_eq]
      have h_pos : 0 < volSphere.toReal := ENNReal.toReal_pos h_volSphere_pos.ne' h_volSphere_lt_top
      have h9 : (ENNReal.ofReal volSphere.toReal)⁻¹ = ENNReal.ofReal (volSphere.toReal⁻¹) :=
        (ENNReal.ofReal_inv_of_pos h_pos).symm
      rw [h9]
      have h10 : 0 ≤ volSphere.toReal⁻¹ := by positivity
      rw [← ENNReal.ofReal_mul h10]
      apply congr_arg ENNReal.ofReal
      dsimp only [u_X, c_scale]
      <;> ring
    rw [h8] at h7
    exact h7
  have h_sphere_pos : 0 < sphereProbabilityMeasure m U := by
    have h1 : 0 < ENNReal.ofReal u_X := by have h2 : 0 < u_X := hu_X_pos; exact ofReal_pos.mpr hu_X_pos
    exact lt_of_lt_of_le h1 hU_pos
  have h_main : ∃ (θ : Sphere m), θ ∈ U ∧
      ENNReal.ofReal ((sphereProbabilityMeasure m U).toReal / (C_m * B)) ≤
      volume (projectionNeighborhood δ θ.val ν.support) :=
    marstrand_cone_lower_bound (hd := hm) (hε := hδ_pos) (hB := hB_pos)
      ν h_energy U hU_meas h_sphere_pos
  rcases h_main with ⟨θ, hθ_U, hV⟩
  have h_exists_x : ∃ (x_vec : EuclideanSpace ℝ (Fin m)), x_vec ∈ W ∧ θ.val = ‖x_vec‖⁻¹ • x_vec := by
    simpa [U, Set.mem_setOf_eq] using hθ_U
  rcases h_exists_x with ⟨x_vec, hxW, hθ_eq⟩
  let x : Fin m → ℝ := x_vec
  have hx_X : ∀ i, x i ∈ X := hxW.1
  have hx_norm_lower : r_min ≤ ‖x_vec‖ := hxW.2
  have hx_norm_upper : ‖x_vec‖ ≤ R := hW_bound x_vec hxW
  have hx_norm_pos : 0 < ‖x_vec‖ := by linarith
  let w_scale : ℝ := ‖x_vec‖⁻¹
  have hw_scale_pos : 0 < w_scale := by positivity
  have hw_scale_le : w_scale ≤ L_scale := by
    dsimp only [w_scale, L_scale]
    have h : r_min ≤ ‖x_vec‖ := hx_norm_lower
    have h' : ‖x_vec‖⁻¹ ≤ r_min⁻¹ := by gcongr <;> linarith
    have h_eq : r_min⁻¹ = 1 / r_min := by
      field_simp [hr_min_pos.ne'] <;> ring
    rw [h_eq] at h'
    exact h'
  let Am : Set (EuclideanSpace ℝ (Fin m)) := {p | ∀ i, p i ∈ A}
  let S : Set ℝ := linearProjection θ.val '' Am
  have h1 : projectionNeighborhood δ θ.val ν.support ⊆ projectionNeighborhood δ θ.val Am := by
    intro t ht; rcases ht with ⟨p, hp, hdist⟩; exact ⟨p, hν_support hp, hdist⟩
  have h2 : volume (projectionNeighborhood δ θ.val Am) ≥
      ENNReal.ofReal ((sphereProbabilityMeasure m U).toReal / (C_m * B)) :=
    calc volume (projectionNeighborhood δ θ.val Am)
      ≥ volume (projectionNeighborhood δ θ.val ν.support) := measure_mono h1
    _ ≥ ENNReal.ofReal ((sphereProbabilityMeasure m U).toReal / (C_m * B)) := hV
  have h3 : projectionNeighborhood δ θ.val Am = {t | ∃ s ∈ S, |s - t| < δ} := by
    ext t; simp only [projectionNeighborhood, S, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, hp, hdist⟩; exact ⟨linearProjection θ.val p, ⟨p, hp, rfl⟩, hdist⟩
    · rintro ⟨s, ⟨p, hp, rfl⟩, hdist⟩; exact ⟨p, hp, hdist⟩
  rw [h3] at h2
  have h_set_eq : {t | ∃ s ∈ S, |s - t| < δ} = {t | ∃ y ∈ S, |t - y| < δ} := by
    ext t; simp only [abs_sub_comm]
  rw [h_set_eq] at h2
  have h4 : volume {t | ∃ x ∈ S, |t - x| < δ} ≤ 3 * ENNReal.ofReal δ * Nreal δ S :=
    neighborhood_volume_le_covering hδ_pos
  have h5 : ENNReal.ofReal ((sphereProbabilityMeasure m U).toReal / (C_m * B)) ≤
      3 * ENNReal.ofReal δ * Nreal δ S := le_trans h2 h4
  have h_proj_eq : S = (fun t : ℝ => w_scale * t) '' (ExpansionLemma.scaledSumset x A) := by
    have hθ_eq2 : θ.val = w_scale • x_vec := by
      simpa [w_scale] using hθ_eq
    exact projection_eq_scaled_sumset (hθ := hθ_eq2)
  have hA_bdd : Bornology.IsBounded A := by
    have h : Bornology.IsBounded (Set.Icc (1 : ℝ) 2) := isCompact_Icc.isBounded
    exact Bornology.IsBounded.subset h hA_sub
  have h_sumset_bdd : Bornology.IsBounded (ExpansionLemma.scaledSumset x A) :=
    scaledSumset_bounded hM_X_pos hX_bound hx_X hA_sub
  have hK_bound : Nreal δ S ≤ (K_scale : ENNReal) * Nreal δ (ExpansionLemma.scaledSumset x A) := by
    rw [h_proj_eq]
    exact hK_scale_uniform δ hδ_pos (ExpansionLemma.scaledSumset x A) h_sumset_bdd w_scale hw_scale_pos hw_scale_le
  have hα_lower : u_X ≤ (sphereProbabilityMeasure m U).toReal := by
    letI : IsProbabilityMeasure (sphereProbabilityMeasure m) :=
      sphereProbabilityMeasure_isProbability (by linarith)
    have h_bdd : sphereProbabilityMeasure m U ≤ 1 := by
      have h3 : sphereProbabilityMeasure m U ≤ sphereProbabilityMeasure m Set.univ :=
        measure_mono (Set.subset_univ U)
      have h4 : sphereProbabilityMeasure m Set.univ = 1 := measure_univ
      rw [h4] at h3
      exact h3
    have hU_ne_top : sphereProbabilityMeasure m U ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) h_bdd
    have h_ofReal_ne_top : ENNReal.ofReal u_X ≠ ⊤ := ENNReal.ofReal_ne_top
    have h : ENNReal.ofReal u_X ≤ sphereProbabilityMeasure m U := hU_pos
    have h_result : (ENNReal.ofReal u_X).toReal ≤ (sphereProbabilityMeasure m U).toReal :=
      (ENNReal.toReal_le_toReal h_ofReal_ne_top hU_ne_top).mpr h
    have h_ofReal_toReal : (ENNReal.ofReal u_X).toReal = u_X :=
      ENNReal.toReal_ofReal (by linarith [hu_X_pos])
    rw [h_ofReal_toReal] at h_result
    exact h_result
  have hC_mB_pos : 0 < C_m * B := mul_pos hC_m_pos hB_pos
  have h_div_le : u_X / (C_m * B) ≤ (sphereProbabilityMeasure m U).toReal / (C_m * B) :=
    div_le_div_of_nonneg_right hα_lower (by linarith)
  have h6 : ENNReal.ofReal (u_X / (C_m * B)) ≤
      ENNReal.ofReal ((sphereProbabilityMeasure m U).toReal / (C_m * B)) :=
    ENNReal.ofReal_le_ofReal h_div_le
  have hL : ENNReal.ofReal (u_X / (C_m * B)) ≤ 3 * ENNReal.ofReal δ * Nreal δ S :=
    le_trans h6 h5
  have hK_ne_zero : (K_scale : ENNReal) ≠ 0 := by exact_mod_cast hK_scale_pos.ne'
  have hK_ne_top : (K_scale : ENNReal) ≠ ⊤ := by simp
  have h_scale_back : (1 : ENNReal) / (K_scale : ENNReal) * Nreal δ S ≤
      Nreal δ (ExpansionLemma.scaledSumset x A) := by
    have h_step1 : (1 : ENNReal) / (K_scale : ENNReal) * Nreal δ S ≤
        (1 : ENNReal) / (K_scale : ENNReal) * ((K_scale : ENNReal) * Nreal δ (ExpansionLemma.scaledSumset x A)) :=
      mul_le_mul_of_nonneg_left hK_bound (by positivity)
    have h_step2 : (1 : ENNReal) / (K_scale : ENNReal) * ((K_scale : ENNReal) * Nreal δ (ExpansionLemma.scaledSumset x A)) =
        Nreal δ (ExpansionLemma.scaledSumset x A) := by
      rw [← mul_assoc, ENNReal.div_mul_cancel hK_ne_zero hK_ne_top] <;> ring
    rw [h_step2] at h_step1
    exact h_step1
  have h_div : (1 : ENNReal) / (K_scale : ENNReal) = (K_scale : ENNReal)⁻¹ := by
    rw [div_eq_mul_inv, one_mul]
  have h_scale_back' : (K_scale : ENNReal)⁻¹ * Nreal δ S ≤
      Nreal δ (ExpansionLemma.scaledSumset x A) := by
    rw [← h_div]
    exact h_scale_back
  have hc_step_def : c_step = u_X / (3 * C_m * (K_scale : ℝ)) := by
    dsimp only [c_step] <;> ring
  have h_arithmetic := step3_5_final_arithmetic
    (u := u_X) (C := C_m) (B := B) (δ := δ) (K := K_scale) (c_step := c_step)
    hC_m_pos hB_pos hδ_pos hK_scale_pos hc_step_def
    (Nreal δ S) (Nreal δ (ExpansionLemma.scaledSumset x A))
    hL h_scale_back'
  exact ⟨x, hx_X, h_arithmetic⟩

end WeakTwoEndsSumProduct
