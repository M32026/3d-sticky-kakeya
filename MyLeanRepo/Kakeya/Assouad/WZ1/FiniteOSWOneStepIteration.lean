import MyLeanRepo.Kakeya.Assouad.WZ1.Inputs

/-!
# One-step finite iteration of the OSW radial bootstrap

This is the single-step version of the finite OSW iteration.  Keeping the
step size `tau`, rather than grouping steps in pairs, is needed for the final
near-one exponent selection in WZ1 Proposition 41.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The thin-tube constant after `N` one-step OSW bootstraps. -/
noncomputable def wz1_one_step_iterated_K
    (N : ℕ) (K C M c : ℝ) : ℝ :=
  Nat.recOn N K fun n Kn =>
    Real.rpow
      (max Kn (C ^ 2 * M / ((3 : ℝ) ^ n * c))) M

/-- The iterated one-step OSW constant remains at least one. -/
lemma wz1_one_step_iterated_K_one_le
    (N : ℕ) {K C M c : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) :
    1 ≤ wz1_one_step_iterated_K N K C M c := by
  have hM0 : 0 ≤ M := by linarith
  induction N with
  | zero => exact hK
  | succ N ih =>
    dsimp only [wz1_one_step_iterated_K]
    exact Real.one_le_rpow
      (le_max_of_le_left ih) hM0

/-- The iterated one-step OSW constant is nondecreasing in the iteration count. -/
lemma wz1_one_step_iterated_K_mono
    (N : ℕ) {K C M c : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) :
    K ≤ wz1_one_step_iterated_K N K C M c := by
  have h_step : ∀ n : ℕ,
    wz1_one_step_iterated_K n K C M c ≤
      wz1_one_step_iterated_K (n + 1) K C M c := by
    intro n
    dsimp only [wz1_one_step_iterated_K]
    set Kn := wz1_one_step_iterated_K n K C M c with hKn
    have hKn1 : 1 ≤ Kn := wz1_one_step_iterated_K_one_le n hK hM
    set X := max Kn (C ^ 2 * M / ((3 : ℝ) ^ n * c)) with hX
    have hX1 : 1 ≤ X := le_trans hKn1 (le_max_left _ _)
    have hKn_le_X : Kn ≤ X := le_max_left _ _
    have h_rpow_X : Real.rpow X M ≥ Kn := by
      have h1 : Real.rpow X 1 ≤ Real.rpow X M :=
        Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      have h2 : Real.rpow X 1 = X := by simp
      rw [h2] at h1
      exact le_trans hKn_le_X h1
    exact h_rpow_X
  induction N with
  | zero => simp [wz1_one_step_iterated_K]
  | succ N ih => exact le_trans ih (h_step N)

/--
Iterate the supplied OSW input `N` times one step at a time.

The hypotheses expose exactly the two ranges that must hold at every input
stage: the exponent remains in `[beta, 1-epsilon]`, and the exceptional
fraction `3^n * c` remains in `(0, 1/10)`.
-/
theorem wz1_finite_osw_one_step_iteration
    (h_osw : RadialBootstrappingMeasureThinTubesInput)
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧
      ∃ M : ℝ, 1 ≤ M ∧
        ∀ (N : ℕ) (sigma c K C : ℝ)
          (nu₁ nu₂ : ProbabilityMeasure Point2),
          (nu₁ : Measure Point2).support ⊆
              Metric.closedBall 0 1 →
          (nu₂ : Measure Point2).support ⊆
              Metric.closedBall 0 1 →
          (∀ n : ℕ, n < N →
            sigma + (n : ℝ) * tau ∈
              Set.Icc beta (1 - epsilon)) →
          (∀ n : ℕ, n < N →
            (3 : ℝ) ^ n * c ∈ Set.Ioo (0 : ℝ) (1 / 10)) →
          1 ≤ K →
          1 ≤ C →
          (1 : ℝ) / 2 ≤
            sInf {d : ℝ |
              ∃ x ∈ (nu₁ : Measure Point2).support,
                ∃ y ∈ (nu₂ : Measure Point2).support,
                  dist x y = d} →
          (∀ (x : Point2) (r : ℝ), 0 < r →
            nu₁ (Metric.ball x r) ≤ Real.toNNReal (C * r)) →
          (∀ (x : Point2) (r : ℝ), 0 < r →
            nu₂ (Metric.ball x r) ≤ Real.toNNReal (C * r)) →
          HasMeasureThinTubes sigma K c nu₁ nu₂ →
          HasMeasureThinTubes sigma K c nu₂ nu₁ →
            HasMeasureThinTubes
                (sigma + (N : ℝ) * tau)
                (wz1_one_step_iterated_K N K C M c)
                ((3 : ℝ) ^ N * c) nu₁ nu₂ ∧
              HasMeasureThinTubes
                (sigma + (N : ℝ) * tau)
                (wz1_one_step_iterated_K N K C M c)
                ((3 : ℝ) ^ N * c) nu₂ nu₁ := by
  rcases h_osw beta epsilon hbeta hepsilon with
    ⟨tau, htau, M, hM, hstep⟩
  refine ⟨tau, htau, M, hM, ?_⟩
  intro N sigma c K C nu₁ nu₂ hsupp₁ hsupp₂
    hsigma hc hK hC hdist hball₁ hball₂ hthin₁₂ hthin₂₁
  have hmain : ∀ n : ℕ,
      (∀ k : ℕ, k < n →
        sigma + (k : ℝ) * tau ∈
          Set.Icc beta (1 - epsilon)) →
      (∀ k : ℕ, k < n →
        (3 : ℝ) ^ k * c ∈ Set.Ioo (0 : ℝ) (1 / 10)) →
      HasMeasureThinTubes
          (sigma + (n : ℝ) * tau)
          (wz1_one_step_iterated_K n K C M c)
          ((3 : ℝ) ^ n * c) nu₁ nu₂ ∧
        HasMeasureThinTubes
          (sigma + (n : ℝ) * tau)
          (wz1_one_step_iterated_K n K C M c)
          ((3 : ℝ) ^ n * c) nu₂ nu₁ := by
    intro n
    induction n with
    | zero =>
      intro _ _
      simpa [wz1_one_step_iterated_K] using
        ⟨hthin₁₂, hthin₂₁⟩
    | succ n ih =>
      intro hsigma_succ hc_succ
      have hsigma_n :
          sigma + (n : ℝ) * tau ∈
            Set.Icc beta (1 - epsilon) :=
        hsigma_succ n (by omega)
      have hc_n :
          (3 : ℝ) ^ n * c ∈ Set.Ioo (0 : ℝ) (1 / 10) :=
        hc_succ n (by omega)
      have hprev := ih
        (fun k hk => hsigma_succ k (by omega))
        (fun k hk => hc_succ k (by omega))
      let K_n := wz1_one_step_iterated_K n K C M c
      have hK_n : 1 ≤ K_n :=
        wz1_one_step_iterated_K_one_le n hK hM
      have hnext := hstep
        (sigma + (n : ℝ) * tau)
        ((3 : ℝ) ^ n * c) K_n C nu₁ nu₂
        hsupp₁ hsupp₂ hsigma_n hc_n hK_n hC hdist
        hball₁ hball₂ hprev.1 hprev.2
      have hexponent :
          sigma + ((n + 1 : ℕ) : ℝ) * tau =
            sigma + (n : ℝ) * tau + tau := by
        simp [Nat.cast_add, Nat.cast_one]
        ring
      have hexceptional :
          (3 : ℝ) ^ (n + 1) * c =
            3 * ((3 : ℝ) ^ n * c) := by
        simp [pow_succ]
        ring
      have hconstant :
          wz1_one_step_iterated_K (n + 1) K C M c =
            Real.rpow
              (max K_n
                (C ^ 2 * M / ((3 : ℝ) ^ n * c))) M := by
        simp [wz1_one_step_iterated_K, K_n]
      rw [hexponent, hexceptional, hconstant]
      exact hnext
  exact hmain N hsigma hc

/--
Bound the delta-dependence of the iterated OSW constant.

If `K ≤ A * delta^{-p}`, `C ≤ B * delta^{-q}`, and `c ≥ delta^r`,
then `K_N ≤ D^{M^N} * delta^{-M^N * e}` where
`D = max 1 (max A (B^2*M))` and `e = max p (2*q+r)`.
-/
lemma wz1_one_step_iterated_K_bound
    (N : ℕ) {K C M c A B delta p q r : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hM : 1 ≤ M)
    (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hA : 0 < A) (hB : 0 < B)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hK_bound : K ≤ A * Real.rpow delta (-p))
    (hC_bound : C ≤ B * Real.rpow delta (-q))
    (hc_bound : Real.rpow delta r ≤ c) :
    wz1_one_step_iterated_K N K C M c ≤
        Real.rpow (max 1 (max A (B^2 * M))) (M ^ N) *
        Real.rpow delta (-(M ^ N) * max p (2*q + r)) := by
  set D := max 1 (max A (B^2 * M)) with hD
  set e := max p (2*q + r) with he
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := by linarith
  have hAD : A ≤ D := by simp [hD] <;> linarith
  have hBD : B^2 * M ≤ D := by simp [hD] <;> linarith
  have hpe : p ≤ e := le_max_left _ _
  have hqe : 2*q + r ≤ e := le_max_right _ _
  have he0 : 0 ≤ e := by linarith [hpe]
  have hMpos : 0 < M := by linarith
  have hcpos : 0 < c := by
    have h : 0 < Real.rpow delta r := Real.rpow_pos_of_pos hdelta r
    linarith
  have hdrpow_nonneg : ∀ (x : ℝ), 0 ≤ Real.rpow delta x :=
    fun x => le_of_lt (Real.rpow_pos_of_pos hdelta x)
  have h_antitone : ∀ {x y : ℝ}, x ≤ y →
      Real.rpow delta y ≤ Real.rpow delta x := by
    intro x y hxy
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1 hxy
  have h_sq_rpow : ∀ (x : ℝ),
      (Real.rpow delta x)^2 = Real.rpow delta (2*x) := by
    intro x
    have h1 : (Real.rpow delta x)^2 =
        (Real.rpow delta x) * (Real.rpow delta x) := by ring
    rw [h1]
    have h2 : (Real.rpow delta x) * (Real.rpow delta x) =
        Real.rpow delta (x + x) := by
      exact (Real.rpow_add (by linarith) x x).symm
    rw [h2]
    have h3 : x + x = 2 * x := by ring
    rw [h3]
  have h_main : ∀ n : ℕ, wz1_one_step_iterated_K n K C M c ≤
      Real.rpow D (M ^ n) * Real.rpow delta (-(M ^ n) * e) := by
    intro n
    induction n with
    | zero =>
      have h1 : Real.rpow delta (-p) ≤ Real.rpow delta (-e) :=
        h_antitone (by linarith)
      have h2 : A * Real.rpow delta (-p) ≤
          A * Real.rpow delta (-e) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      have h3 : 0 ≤ Real.rpow delta (-e) := hdrpow_nonneg (-e)
      have h4 : K ≤ D * Real.rpow delta (-e) := by
        calc K
          ≤ A * Real.rpow delta (-p) := hK_bound
        _ ≤ A * Real.rpow delta (-e) := h2
        _ ≤ D * Real.rpow delta (-e) :=
          mul_le_mul_of_nonneg_right hAD h3
      have h5 : wz1_one_step_iterated_K 0 K C M c = K := by
        simp [wz1_one_step_iterated_K]
      rw [h5]
      simpa [pow_zero] using h4
    | succ n ih =>
      set Kn := wz1_one_step_iterated_K n K C M c with hKn_def
      have hKn1 : 1 ≤ Kn :=
        wz1_one_step_iterated_K_one_le n hK hM
      have hC2 : C^2 ≤ B^2 * Real.rpow delta (-2*q) := by
        have hXpos : 0 ≤ B * Real.rpow delta (-q) := by
          exact mul_nonneg (by linarith) (hdrpow_nonneg (-q))
        have h : C^2 ≤ (B * Real.rpow delta (-q))^2 := by
          nlinarith [hC_bound, hC]
        have hsq : (B * Real.rpow delta (-q))^2 =
            B^2 * Real.rpow delta (-2*q) := by
          calc
            (B * Real.rpow delta (-q))^2
                = B^2 * (Real.rpow delta (-q))^2 := by ring
            _ = B^2 * Real.rpow delta (2 * (-q)) := by
              rw [h_sq_rpow (-q)]
            _ = B^2 * Real.rpow delta (-2*q) := by
              have hq2 : 2 * (-q) = -2*q := by ring
              rw [hq2]
        rw [hsq] at h
        exact h
      have h1c : 1 / c ≤ Real.rpow delta (-r) := by
        have hcr : 0 < Real.rpow delta r :=
          Real.rpow_pos_of_pos hdelta r
        have h : 1 / c ≤ 1 / Real.rpow delta r := by
          apply one_div_le_one_div_of_le (by positivity) (by linarith)
        have h_inv : (Real.rpow delta r)⁻¹ =
            Real.rpow delta (-r) := by
          exact (Real.rpow_neg (by linarith) r).symm
        have h2 : 1 / Real.rpow delta r =
            (Real.rpow delta r)⁻¹ := by
          simp [one_div]
        rw [h2, h_inv] at h
        exact h
      have h_exp_add :
          Real.rpow delta (-2*q) * Real.rpow delta (-r) =
            Real.rpow delta (-(2*q + r)) := by
        have h : Real.rpow delta ((-2*q) + (-r)) =
            Real.rpow delta (-2*q) * Real.rpow delta (-r) :=
          Real.rpow_add (by linarith) (-2*q) (-r)
        have h2 : (-2*q) + (-r) = -(2*q + r) := by ring
        rw [h2] at h
        exact h.symm
      have h3pos : (1 : ℝ) ≤ (3 : ℝ)^n := by
        have h : (1 : ℝ) ^ n ≤ (3 : ℝ) ^ n := by
          gcongr <;> norm_num
        simpa using h
      have hdiv : M / (3 : ℝ)^n ≤ M := by
        have h6 : M / (3 : ℝ)^n ≤ M / 1 := by
          gcongr <;> linarith
        simpa using h6
      have hcne : c ≠ 0 := by linarith
      have h3ne : (3 : ℝ)^n ≠ 0 := by positivity
      have hterm1 : C^2 * M / ((3 : ℝ)^n * c) =
          C^2 * (M / (3 : ℝ)^n) * (1 / c) := by
        field_simp [hcne, h3ne]
      have hpos_M3n : 0 ≤ M / (3 : ℝ)^n := by
        have hM0 : 0 ≤ M := by linarith
        have h3pos0 : 0 ≤ (3 : ℝ)^n := by positivity
        exact div_nonneg hM0 h3pos0
      have hpos_1c : 0 ≤ 1 / c := by positivity
      have hpos_B2 : 0 ≤ B^2 * Real.rpow delta (-2*q) := by
        exact mul_nonneg (sq_nonneg B) (hdrpow_nonneg (-2*q))
      have hterm2 :
          C^2 * (M / (3 : ℝ)^n) * (1 / c) ≤
            B^2 * Real.rpow delta (-2*q) *
              (M / (3 : ℝ)^n) * Real.rpow delta (-r) := by
        have h_a : C^2 * (M / (3 : ℝ)^n) ≤
            (B^2 * Real.rpow delta (-2*q)) *
              (M / (3 : ℝ)^n) := by
          exact mul_le_mul_of_nonneg_right hC2 hpos_M3n
        have h_b :
            (C^2 * (M / (3 : ℝ)^n)) * (1 / c) ≤
              ((B^2 * Real.rpow delta (-2*q)) *
                (M / (3 : ℝ)^n)) * (1 / c) := by
          exact mul_le_mul_of_nonneg_right h_a hpos_1c
        have h_c :
            ((B^2 * Real.rpow delta (-2*q)) *
                (M / (3 : ℝ)^n)) * (1 / c) ≤
              ((B^2 * Real.rpow delta (-2*q)) *
                (M / (3 : ℝ)^n)) * Real.rpow delta (-r) := by
          exact mul_le_mul_of_nonneg_left h1c (by positivity)
        calc
          C^2 * (M / (3 : ℝ)^n) * (1 / c)
              ≤ ((B^2 * Real.rpow delta (-2*q)) *
                  (M / (3 : ℝ)^n)) * (1 / c) := h_b
          _ ≤ ((B^2 * Real.rpow delta (-2*q)) *
                (M / (3 : ℝ)^n)) * Real.rpow delta (-r) := h_c
          _ = B^2 * Real.rpow delta (-2*q) *
                (M / (3 : ℝ)^n) * Real.rpow delta (-r) := by ring
      have hterm3 :
          B^2 * Real.rpow delta (-2*q) *
              (M / (3 : ℝ)^n) * Real.rpow delta (-r) =
            B^2 * (M / (3 : ℝ)^n) *
              Real.rpow delta (-(2*q + r)) := by
        have h_rearr :
            B^2 * Real.rpow delta (-2*q) *
                (M / (3 : ℝ)^n) * Real.rpow delta (-r) =
              B^2 * (M / (3 : ℝ)^n) *
                (Real.rpow delta (-2*q) * Real.rpow delta (-r)) := by
          ring
        rw [h_rearr, h_exp_add] <;> ring
      have hterm4 :
          B^2 * (M / (3 : ℝ)^n) *
              Real.rpow delta (-(2*q + r)) ≤
            B^2 * M * Real.rpow delta (-(2*q + r)) := by
        have h_a : B^2 * (M / (3 : ℝ)^n) ≤ B^2 * M := by
          gcongr <;> linarith
        exact mul_le_mul_of_nonneg_right h_a
          (hdrpow_nonneg (-(2*q + r)))
      have hterm5 :
          B^2 * M * Real.rpow delta (-(2*q + r)) ≤
            D * Real.rpow delta (-e) := by
        have h8 : Real.rpow delta (-(2*q + r)) ≤
            Real.rpow delta (-e) :=
          h_antitone (by linarith)
        have h9 : 0 ≤ Real.rpow delta (-(2*q + r)) :=
          hdrpow_nonneg (-(2*q + r))
        nlinarith [hBD]
      have hterm : C^2 * M / ((3 : ℝ)^n * c) ≤
          D * Real.rpow delta (-e) := by
        calc
          C^2 * M / ((3 : ℝ)^n * c)
              = C^2 * (M / (3 : ℝ)^n) * (1 / c) := hterm1
          _ ≤ B^2 * Real.rpow delta (-2*q) *
                (M / (3 : ℝ)^n) * Real.rpow delta (-r) := hterm2
          _ = B^2 * (M / (3 : ℝ)^n) *
                Real.rpow delta (-(2*q + r)) := hterm3
          _ ≤ B^2 * M * Real.rpow delta (-(2*q + r)) := hterm4
          _ ≤ D * Real.rpow delta (-e) := hterm5
      have hMn1 : (1 : ℝ) ≤ M ^ n := by
        have h : (1 : ℝ) ^ n ≤ M ^ n := by
          gcongr <;> linarith
        simpa using h
      have hD_rpow : D ≤ Real.rpow D (M ^ n) := by
        have h : (D : ℝ) ^ (1 : ℝ) ≤ (D : ℝ) ^ (M ^ n) :=
          Real.rpow_le_rpow_of_exponent_le hD1 hMn1
        simpa using h
      have hdelta_rpow : Real.rpow delta (-e) ≤
          Real.rpow delta (-(M ^ n) * e) :=
        h_antitone (by nlinarith)
      have h10 : 0 ≤ Real.rpow delta (-e) := hdrpow_nonneg (-e)
      have h11 : 0 ≤ Real.rpow D (M ^ n) :=
        Real.rpow_nonneg hD0 _
      have h9 : D * Real.rpow delta (-e) ≤
          Real.rpow D (M ^ n) *
            Real.rpow delta (-(M ^ n) * e) := by
        calc
          D * Real.rpow delta (-e)
              ≤ Real.rpow D (M ^ n) * Real.rpow delta (-e) :=
            mul_le_mul_of_nonneg_right hD_rpow h10
          _ ≤ Real.rpow D (M ^ n) *
                Real.rpow delta (-(M ^ n) * e) :=
            mul_le_mul_of_nonneg_left hdelta_rpow h11
      have hmax : max Kn (C^2 * M / ((3 : ℝ)^n * c)) ≤
          Real.rpow D (M ^ n) *
            Real.rpow delta (-(M ^ n) * e) := by
        apply max_le
        · exact ih
        · exact le_trans hterm h9
      have hpos :
          0 ≤ max Kn (C^2 * M / ((3 : ℝ)^n * c)) := by
        positivity
      have hbase_pos :
          0 ≤ Real.rpow D (M ^ n) *
            Real.rpow delta (-(M ^ n) * e) :=
        mul_nonneg (Real.rpow_nonneg hD0 _)
          (Real.rpow_nonneg hdelta.le _)
      have hM_nonneg : 0 ≤ M := by linarith
      have h_rpow1 : Real.rpow (Real.rpow D (M ^ n)) M =
          Real.rpow D ((M ^ n) * M) := by
        exact (Real.rpow_mul hD0 (M ^ n) M).symm
      have h_rpow2 :
          Real.rpow (Real.rpow delta (-(M ^ n) * e)) M =
            Real.rpow delta ((-(M ^ n) * e) * M) := by
        exact (Real.rpow_mul hdelta.le (-(M ^ n) * e) M).symm
      have h12 : (M ^ n) * M = M ^ (n + 1) := by
        exact Eq.symm (pow_succ M n)
      have h13 : ((-(M ^ n) * e) * M) =
          (-(M ^ (n + 1)) * e) := by
        have h14 : (M ^ n) * M = M ^ (n + 1) := h12
        calc
          (-(M ^ n) * e) * M
              = -((M ^ n) * M) * e := by ring
          _ = -(M ^ (n + 1)) * e := by rw [h14]
      have hmul :
          Real.rpow
              (Real.rpow D (M ^ n) *
                Real.rpow delta (-(M ^ n) * e)) M =
            Real.rpow (Real.rpow D (M ^ n)) M *
              Real.rpow (Real.rpow delta (-(M ^ n) * e)) M := by
        exact Real.mul_rpow (Real.rpow_nonneg hD0 _)
          (Real.rpow_nonneg hdelta.le _)
      have h_final :
          Real.rpow
              (max Kn (C^2 * M / ((3 : ℝ)^n * c))) M ≤
            Real.rpow D (M ^ (n + 1)) *
              Real.rpow delta (-(M ^ (n + 1)) * e) := by
        have h_step1 :
            Real.rpow
                (max Kn (C^2 * M / ((3 : ℝ)^n * c))) M ≤
              Real.rpow
                (Real.rpow D (M ^ n) *
                  Real.rpow delta (-(M ^ n) * e)) M :=
          Real.rpow_le_rpow hpos hmax hM_nonneg
        rw [hmul, h_rpow1, h_rpow2] at *
        rw [h12, h13] at *
        exact h_step1
      have h_unfold : wz1_one_step_iterated_K (n + 1) K C M c =
          Real.rpow
            (max Kn (C^2 * M / ((3 : ℝ)^n * c))) M := by
        simp [wz1_one_step_iterated_K, hKn_def]
        <;> rfl
      rw [h_unfold]
      exact h_final
  exact h_main N

end Kakeya.Assouad
