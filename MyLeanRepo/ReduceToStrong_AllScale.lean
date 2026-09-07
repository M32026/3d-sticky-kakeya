module

/-
# Reduce to Strong — All-Scale Version

Uses all-scale Frostman input throughout (Route C).

## Proof structure
1. Maximal density interval at κ/2
2. All-scale renormalization → ν with IsAllScaleFrostman (κ/2) 2^{κ/2} ν
3. Apply generalized strong ring theorem with C₀ = 2^{κ/2}, t = r₀
4. Transfer covering bounds back to original scale
5. Multi-set PR extraction from 3-fold sumset
6. Three cases (y = x, y = -x₀, y = 1)
7. Choose ε' and aggregate δ₀ thresholds
-/

public import MyLeanRepo.AllScaleFrostman
public import MyLeanRepo.AllScaleRenormalize
public import MyLeanRepo.RestrictAwayFromZero
public import MyLeanRepo.MultiSetPR
public import MyLeanRepo.RuzsaCorollaries
public import MyLeanRepo.MaximalDensityIntervalWithSupport
public import MyLeanRepo.CubeIndexSet
public import MyLeanRepo.TauMonotonicity
public import MyLeanRepo.SetDiscretizationBridge
public import MyLeanRepo.IsRealDeltaSetInheritance
public import MyLeanRepo.CoveringNumberScaling
public import MyLeanRepo.DiscretizedStrongRingCorollary
public import MyLeanRepo.OSW.RuzsaCorollaries
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical
open scoped BigOperators Pointwise

namespace WeakTwoEndsSumProduct

/-- Generalized strong ring theorem interface.
    Wraps `discretized_strong_ring_corollary` with K=1, converting the
    application-facing covering-number interface to the corrected Strong Ring
    theorem's Lebesgue-volume interface.
    Accepts arbitrary C₀ with 1 ≤ C₀ ≤ 2^κ. δ₀ depends on C₀. -/
lemma strong_ring_theorem_generalized
    (s κ : ℝ) (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hκ_pos : 0 < κ) (hκ_le_s : κ ≤ s) :
    ∃ (c ε : ℝ), 0 < c ∧ 0 < ε ∧
      ∀ (C₀ : ℝ), 1 ≤ C₀ → C₀ ≤ (2 : ℝ) ^ κ →
        ∃ (δ₀ : ℝ), 0 < δ₀ ∧
          ∀ {δ : ℝ}, δ ∈ dyadicScales → 0 < δ → δ ≤ δ₀ →
            ∀ (A : Set ℝ) (μ : Measure ℝ) (t : ℝ),
              A ⊆ Set.Icc 1 2 →
              IsRealDeltaSet δ κ (δ ^ (-ε)) A →
              Nreal δ A ≤ ENNReal.ofReal (δ ^ (-(s + ε))) →
              IsAllScaleFrostman κ C₀ μ →
              μ.support ⊆ Set.Icc 0 1 →
              δ ^ c ≤ t → t ≤ 1 →
              ∃ x ∈ μ.support,
                ENNReal.ofReal (δ ^ (-c)) * Nreal δ (scaleSet t⁻¹ A) ≤
                  Nreal δ (Set.image2 (fun a b => a + x * b)
                    (scaleSet t⁻¹ A) A) := by
  rcases discretized_strong_ring_corollary s κ hs_pos hs_lt_one hκ_pos hκ_le_s
    with ⟨c, ε_app, hc_pos, hε_app_pos, h_main⟩
  refine ⟨c, ε_app, hc_pos, hε_app_pos, ?_⟩
  intro C₀ hC₀_ge1 hC₀_le
  have hC₀_pos : 0 < C₀ := by linarith
  rcases h_main (1 : ℝ) C₀ (by norm_num) hC₀_pos hC₀_le
    with ⟨δ₀, hδ₀_pos, h_cor⟩
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ_dyadic hδ_pos hδle A μ t hA_sub hA_delta hN_bound hFrost hμ_supp htc ht_le_one
  have hA_delta' : IsRealDeltaSet δ κ ((1 : ℝ) * δ ^ (-ε_app)) A := by
    simpa using hA_delta
  have hN_bound' : Nreal δ A ≤ ENNReal.ofReal ((1 : ℝ) * δ ^ (-(s + ε_app))) := by
    simpa using hN_bound
  exact h_cor hδ_dyadic hδ_pos hδle A μ t hA_sub hA_delta' hN_bound'
    hFrost hμ_supp htc ht_le_one

/-- Convert all-scale Frostman to direction Frostman for any δ. -/
lemma IsAllScaleFrostman.toDirectionFrostman
    {δ κ C : ℝ} {μ : Measure ℝ}
    (h : IsAllScaleFrostman κ C μ)
    (h_supp : μ.support ⊆ Set.Icc 0 1)
    (hδ_pos : 0 < δ) :
    IsDirectionFrostman δ κ C μ :=
  ⟨h.1, h_supp, fun a r hδ_le_r hr_le_one => h.2.2.2 a r (by linarith)⟩

/-- An open interval of length ≤ 3 contains at most 3 integers. -/
lemma int_count_open_interval_le_three {a b : ℝ} (h_len : b - a ≤ 3)
    {s : Finset ℤ} (h : ∀ i ∈ s, a < (i : ℝ) ∧ (i : ℝ) < b) : s.card ≤ 3 := by
  by_contra h4
  have h5 : 4 ≤ s.card := by
    by_contra h6
    have h7 : s.card ≤ 3 := by linarith
    exact h4 h7
  have hne : s.Nonempty := Finset.card_pos.mp (by linarith)
  set kmin := Finset.min' s hne with hkmin_def
  set kmax := Finset.max' s hne with hkmax_def
  have hkmin : kmin ∈ s := Finset.min'_mem s hne
  have hkmax : kmax ∈ s := Finset.max'_mem s hne
  have h6 : kmin ≤ kmax := Finset.min'_le _ _ hkmax
  have h_sub : s ⊆ Finset.Icc kmin kmax := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hx, Finset.le_max' _ _ hx⟩
  have h_card : s.card ≤ (Finset.Icc kmin kmax).card := Finset.card_le_card h_sub
  have h_card2 : (Finset.Icc kmin kmax).card = (kmax - kmin + 1).toNat := by
    rw [Int.card_Icc] <;> omega
  have h4' : 3 ≤ kmax - kmin := by
    have h_nonneg : 0 ≤ kmax - kmin + 1 := by omega
    have h5 : ((Finset.Icc kmin kmax).card : ℤ) = kmax - kmin + 1 := by
      rw [h_card2]
      simp [Int.toNat_of_nonneg h_nonneg]
    have h6 : (s.card : ℤ) ≤ (Finset.Icc kmin kmax).card := by exact_mod_cast h_card
    rw [h5] at h6
    omega
  have h10 : (kmax : ℝ) - (kmin : ℝ) ≥ 3 := by
    have h101 : (kmax : ℝ) - (kmin : ℝ) = ↑(kmax - kmin) := by simp
    rw [h101]; exact_mod_cast h4'
  have h11 : b - a > 3 := by
    have h_lo : a < (kmin : ℝ) := (h kmin hkmin).1
    have h_hi : (kmax : ℝ) < b := (h kmax hkmax).2
    linarith
  linarith



set_option maxHeartbeats 2000000

/-- Helper: scaling lower bound N(x·A) ≥ (a/3)·N(A) for 0 < a ≤ x ≤ 1. -/
lemma scale_lower_bound_helper (δ x a : ℝ) (A : Set ℝ)
    (hδ_pos : 0 < δ) (hx_pos : 0 < x) (hx_le_one : x ≤ 1)
    (ha_le_x : a ≤ x) (hA_bdd : Bornology.IsBounded A) :
    Nreal δ (scaleSet x A) ≥ ENNReal.ofReal (a / 3) * Nreal δ A := by
  have h1 : Nreal δ (scaleSet x A) = Nreal (δ / x) A := Nreal_scaling hδ_pos hx_pos hA_bdd
  rw [h1]
  have h_eq : (δ / x) * x = δ := by field_simp [hx_pos.ne'] <;> ring
  have h_raw := Nreal_coarsening (div_pos hδ_pos hx_pos) hx_pos hx_le_one hA_bdd
  rw [h_eq] at h_raw
  have h2 : ENNReal.ofReal (x / 3) * Nreal δ A ≤ Nreal (δ / x) A := h_raw
  have h3 : a / 3 ≤ x / 3 := by linarith
  have h4 : ENNReal.ofReal (a / 3) ≤ ENNReal.ofReal (x / 3) := ENNReal.ofReal_le_ofReal h3
  have h5 : ENNReal.ofReal (a / 3) * Nreal δ A ≤ ENNReal.ofReal (x / 3) * Nreal δ A :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  exact h5.trans h2

/-- Helper: scaling upper bound N(y·A) ≤ 3·N(A) for 0 < y ≤ 1. -/
lemma scale_upper_bound_helper (δ y : ℝ) (A : Set ℝ)
    (hδ_pos : 0 < δ) (hy_pos : 0 < y) (hy_le_one : y ≤ 1)
    (hA_bdd : Bornology.IsBounded A) :
    Nreal δ (scaleSet y A) ≤ 3 * Nreal δ A := by
  have h1 : Nreal δ (scaleSet y A) = Nreal (δ / y) A := Nreal_scaling hδ_pos hy_pos hA_bdd
  rw [h1]
  have h_δ_le : δ ≤ δ / y := by
    have h1 : 0 < y := hy_pos
    have h2 : y ≤ 1 := hy_le_one
    have h3 : 1 ≤ 1 / y := by
      rw [one_le_div h1] <;> linarith
    have h4 : δ ≤ δ * (1 / y) := by
      have h41 : δ * 1 ≤ δ * (1 / y) := mul_le_mul_of_nonneg_left h3 hδ_pos.le
      have h42 : δ * 1 = δ := by ring
      rw [h42] at h41
      exact h41
    have h5 : δ * (1 / y) = δ / y := by ring
    rw [h5] at h4
    exact h4
  have h_ref : Nreal (δ / y) A ≤ 2 * Nreal δ A :=
    Nreal_refining hδ_pos (div_pos hδ_pos hy_pos) h_δ_le hA_bdd
  exact le_trans h_ref (by gcongr <;> norm_num)

/-- Helper: 9·β·β = δ^{-c/4} where β = (1/3)·δ^{-c/8}. -/
lemma beta_squared_helper (δ c : ℝ) (hδ_pos : 0 < δ) :
    (9 : ENNReal) * ENNReal.ofReal ((1 / 3 : ℝ) * δ ^ (-c / 8)) * ENNReal.ofReal ((1 / 3 : ℝ) * δ ^ (-c / 8)) =
    ENNReal.ofReal (δ ^ (-c / 4)) := by
  let x : ℝ := (1 / 3 : ℝ) * δ ^ (-c / 8)
  have hx_pos : 0 ≤ x := by positivity
  have h3 : (δ ^ (-c / 8)) ^ 2 = δ ^ (-c / 4) := by
    have h31 : (δ ^ (-c / 8)) ^ 2 = (δ ^ (-c / 8)) ^ (2 : ℝ) := by norm_cast
    rw [h31]
    have h32 : (δ ^ (-c / 8)) ^ (2 : ℝ) = δ ^ ((-c / 8) * (2 : ℝ)) :=
      (Real.rpow_mul hδ_pos.le (-c / 8) (2 : ℝ)).symm
    rw [h32]
    have h33 : (-c / 8) * (2 : ℝ) = -c / 4 := by ring
    rw [h33]
  have h2 : (9 : ℝ) * x * x = δ ^ (-c / 4) := by
    dsimp only [x]
    have h21 : (9 : ℝ) * ((1 / 3 : ℝ) * δ ^ (-c / 8)) * ((1 / 3 : ℝ) * δ ^ (-c / 8)) = (δ ^ (-c / 8)) ^ 2 := by ring
    rw [h21, h3]
  have h4 : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by simp
  rw [h4]
  have h5 : ENNReal.ofReal (9 : ℝ) * ENNReal.ofReal x * ENNReal.ofReal x = ENNReal.ofReal ((9 : ℝ) * x * x) := by
    rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (9 : ℝ) by norm_num)]
    rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (9 : ℝ) * x by positivity)]
    <;> ring
  rw [h5, h2]

/-- Helper: strict monotonicity of ENNReal cube with positive finite coefficient. -/
lemma ennreal_cube_strict_mono {x y : ENNReal} (h : x < y) :
    (81 : ENNReal) * x * x * x < (81 : ENNReal) * y * y * y := by
  have h1 : x * x < y * y := ENNReal.mul_lt_mul h h
  have h2 : x * x * x < y * y * y := ENNReal.mul_lt_mul h1 h
  have h6 : (81 : ENNReal) ≠ 0 := by norm_num
  have h7 : (81 : ENNReal) ≠ ⊤ := by norm_num
  have h8 : (81 : ENNReal) * (x * x * x) < (81 : ENNReal) * (y * y * y) :=
    (ENNReal.mul_lt_mul_iff_right h6 h7).mpr h2
  have h9 : (81 : ENNReal) * x * x * x = (81 : ENNReal) * (x * x * x) := by
    simp [mul_assoc]
  have h10 : (81 : ENNReal) * y * y * y = (81 : ENNReal) * (y * y * y) := by
    simp [mul_assoc]
  rw [h9, h10]
  exact h8

/-- Helper: `ofReal(a) * ofReal(b) = ofReal(a * b)` for nonnegative reals. -/
lemma ofReal_mul' {a b : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) :=
  (ENNReal.ofReal_mul ha).symm

/-- Helper: product of three ofReal terms. -/
lemma ofReal_mul3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c = ENNReal.ofReal (a * b * c) := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb)] <;> ring

/-- Helper: covering number of a bounded set is finite (≠ ⊤). -/
lemma Nreal_ne_top {δ : ℝ} {A : Set ℝ} (hδ : 0 < δ)
    (hA : Bornology.IsBounded A) : Nreal δ A ≠ ⊤ := by
  have hA' : Bornology.IsBounded (realLineCopy A) := by
    have h_eq : realLineCopy A = productLikeRealLineCopy A := by
      ext x; simp [realLineCopy, productLikeRealLineCopy]
    rw [h_eq]
    exact SetDiscretizationBridge.realLineCopy_bounded_iff.mpr hA
  have h1 : Set.Finite (dyadicCubesMeeting δ (realLineCopy A)) :=
    bourgain_projection_theorem.dyadicCubesMeeting_finite hδ hA'
  have h2 : (dyadicCoveringNumber δ (realLineCopy A)) ≠ ⊤ := by
    have h3 : Set.Finite (dyadicCubesMeeting δ (realLineCopy A)) := h1
    have h4 : (dyadicCubesMeeting δ (realLineCopy A)).encard = ↑(h3.toFinset.card) :=
      h3.encard_eq_coe_toFinset_card
    have h5 : (dyadicCoveringNumber δ (realLineCopy A)) = (dyadicCubesMeeting δ (realLineCopy A)).encard := by
      simp [dyadicCoveringNumber]
    rw [h5, h4]
    <;> simp
  simpa [Nreal, dyadicCoveringNumber] using h2

/-- Reduce general all-scale Frostman measure to strong ring theorem application. -/
lemma reduce_to_strong_allscale
    (s κ : ℝ) (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hκ_pos : 0 < κ) (hκ_le_s : κ ≤ s) :
    ∃ (c' ε' : ℝ), 0 < c' ∧ 0 < ε' ∧ ε' ≤ κ / 4 ∧
      ∀ (K : ℝ), 1 ≤ K →
        ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
          ∀ {δ : ℝ}, δ ∈ dyadicScales → 0 < δ → δ ≤ δ₀ →
            ∀ (A : Set ℝ) (μ : Measure ℝ),
              A ⊆ Set.Icc 1 2 →
              IsRealDeltaSet δ κ (K * δ ^ (-ε')) A →
              Nreal δ A ≤ ENNReal.ofReal (K * δ ^ (-(s + ε'))) →
              IsAllScaleFrostman κ (K * δ ^ (-ε')) μ →
              μ.support ⊆ Set.Icc 0 1 →
              ∃ x ∈ μ.support,
                ENNReal.ofReal (δ ^ (-c')) * Nreal δ A ≤
                  Nreal δ (Set.image2 (fun a b => a + x * b) A A) := by
  -- Step 0: Obtain strong theorem exponents for measure exponent κ/2
  -- (all_scale_renormalize halves the Frostman exponent)
  have hκ2_pos : 0 < κ / 2 := by linarith
  have hκ2_le_s : κ / 2 ≤ s := by linarith
  rcases strong_ring_theorem_generalized s (κ / 2) hs_pos hs_lt_one hκ2_pos hκ2_le_s
    with ⟨c, ε, hc_pos, hε_pos, h_strong⟩
  -- Choose ε' = min(ε/2, κ/4, c·κ/48) per operator correction
  set ε' : ℝ := min (min (ε / 2) (κ / 4)) (c * κ / 48) with hε'_def
  have hε'_pos : 0 < ε' := by positivity
  have hε'_lt_ε : ε' < ε := by
    rw [hε'_def]; have h : min (min (ε / 2) (κ / 4)) (c * κ / 48) ≤ ε / 2 := by
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hε'_le_kappa4 : ε' ≤ κ / 4 := by
    rw [hε'_def]; have h : min (min (ε / 2) (κ / 4)) (c * κ / 48) ≤ κ / 4 := by
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    exact h
  have hε'_lt_kappa2 : ε' < κ / 2 := by
    have h : ε' ≤ κ / 4 := hε'_le_kappa4
    linarith
  have hε'_le_ckappa48 : ε' ≤ c * κ / 48 := by
    rw [hε'_def]; exact min_le_right _ _
  -- Output exponent c' = c/24 (per operator correction; three-case PR bottleneck)
  set c' : ℝ := c / 24 with hc'_def
  have hc'_pos : 0 < c' := by positivity
  have h9c'_lt : 9 * c' < c - 8 * ε' / κ := by
    have h1 : 8 * ε' / κ ≤ c / 6 := by
      have h2 : ε' ≤ c * κ / 48 := hε'_le_ckappa48
      calc 8 * ε' / κ ≤ 8 * (c * κ / 48) / κ := by gcongr
        _ = c / 6 := by
          have hκ_ne : κ ≠ 0 := hκ_pos.ne'
          field_simp [hκ_ne] <;> ring
    linarith [hc_pos]
  have h_c'_lt_d12 : c' < (c - 2 * ε' / κ) / 12 := by
    have h1 : 2 * ε' / κ ≤ c / 24 := by
      have h2 : ε' ≤ c * κ / 48 := hε'_le_ckappa48
      calc 2 * ε' / κ ≤ 2 * (c * κ / 48) / κ := by gcongr
        _ = c / 24 := by
          have hκ_ne : κ ≠ 0 := hκ_pos.ne'
          field_simp [hκ_ne] <;> ring
    linarith [hc_pos]
  -- ε_tloss = 2*c'/3 for Step 6 interface
  let ε_tloss : ℝ := 2 * c' / 3
  have hε_tloss_pos : 0 < ε_tloss := by positivity
  -- Strong theorem δ₀ for C₀ = 2^{κ/2} (renormalized measure's Frostman constant)
  let C₀ : ℝ := (2 : ℝ) ^ (κ / 2)
  have hC₀_ge1 : 1 ≤ C₀ := by
    have h_k2_nonneg : 0 ≤ κ / 2 := by linarith
    have h : (2 : ℝ) ^ (0 : ℝ) ≤ (2 : ℝ) ^ (κ / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h_k2_nonneg
    have h2 : (2 : ℝ) ^ (0 : ℝ) = 1 := by simp
    linarith
  have hC₀_le : C₀ ≤ (2 : ℝ) ^ (κ / 2) := by rfl
  rcases h_strong C₀ hC₀_ge1 hC₀_le with ⟨δ₀_strong, hδ₀_strong_pos, h_strongδ⟩
  refine ⟨c', ε', hc'_pos, hε'_pos, hε'_le_kappa4, fun K hK => ?_⟩
  -- For each K, choose δ₀ small enough for:
  --   1. 2*K*δ^(κ/2 - ε') ≤ 1  (h_small for renormalization)
  --   2. K*δ^(ε - ε') ≤ 1       (constant comparison for delta-set and N bound)
  --   3. δ ≤ δ₀_strong           (strong theorem threshold)
  have h_ε_diff_pos : 0 < ε - ε' := by linarith
  have h_exp_pos : 0 < κ / 2 - ε' := by linarith
  let δ₁ : ℝ := (1 / (2 * K)) ^ (1 / (κ / 2 - ε'))
  let δ₂ : ℝ := (1 / K) ^ (1 / (ε - ε'))
  -- Additional threshold for three-case PR (absorbs constants from Ruzsa/corollary)
  have h_exp_pr_pos : 0 < c / 4 - 2 * ε' / κ := by
    have h1 : 2 * ε' / κ ≤ c / 24 := by
      have h2 : ε' ≤ c * κ / 48 := hε'_le_ckappa48
      calc 2 * ε' / κ ≤ 2 * (c * κ / 48) / κ := by gcongr
        _ = c / 24 := by
          have hκ_ne : κ ≠ 0 := hκ_pos.ne'
          field_simp [hκ_ne] <;> ring
    linarith [hc_pos]
  have h_exp_branch_pos : 0 < c / 24 - ε' / κ := by
    have h1 : ε' / κ ≤ c / 48 := by
      have h2 : ε' ≤ c * κ / 48 := hε'_le_ckappa48
      calc ε' / κ ≤ (c * κ / 48) / κ := by gcongr
        _ = c / 48 := by
          have hκ_ne : κ ≠ 0 := hκ_pos.ne'
          field_simp [hκ_ne] <;> ring
    linarith [hc_pos]
  let C_pr : ℝ := (2 * K) ^ (-2 / κ) / 10000
  let δ₄_pr : ℝ := C_pr ^ (1 / (c / 4 - 2 * ε' / κ))
  let C_branch : ℝ := (2 * K) ^ (-1 / κ) / 1000
  let δ₄_branch : ℝ := C_branch ^ (1 / (c / 24 - ε' / κ))
  let δ₄ : ℝ := min δ₄_pr δ₄_branch
  have hδ₄_pos : 0 < δ₄ := by positivity
  -- Threshold for δ^c ≤ r₀: need δ^{c - 2ε'/κ} ≤ (2K)^{-2/κ}
  have h_exp_strong_pos : 0 < c - 2 * ε' / κ := by
    have h1 : 2 * ε' / κ ≤ c / 24 := by
      have h2 : ε' ≤ c * κ / 48 := hε'_le_ckappa48
      calc 2 * ε' / κ ≤ 2 * (c * κ / 48) / κ := by gcongr
        _ = c / 24 := by field_simp [hκ_pos.ne'] <;> ring
    linarith [hc_pos]
  let C_strong : ℝ := (2 * K) ^ (-2 / κ)
  let δ₅_strong : ℝ := C_strong ^ (1 / (c - 2 * ε' / κ))
  -- Threshold for cor_sum_to_diff: need C_cor^(1/3) ≥ δ^(5c/144)
  let C_cor : ℝ := (2 * K) ^ (-1 / κ) / 243
  have hC_cor_pos : 0 < C_cor := by positivity
  have h_exp_cor_pos : 0 < 5 * c / 144 := by positivity
  let δ₆_cor : ℝ := C_cor ^ (48 / (5 * c))
  have hδ₆_cor_pos : 0 < δ₆_cor := by positivity
  let δ₀ : ℝ := min (min (min (min (min (min δ₁ δ₂) δ₀_strong) δ₄) δ₅_strong) δ₆_cor) (1 / 2)
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_one : δ₀ ≤ 1 := by
    have h : δ₀ ≤ 1 / 2 := min_le_right _ _
    linarith
  have hδ₀_le_A : δ₀ ≤ min (min (min (min (min δ₁ δ₂) δ₀_strong) δ₄) δ₅_strong) δ₆_cor := min_le_left _ _
  have hδ₀_le_B : δ₀ ≤ min (min (min (min δ₁ δ₂) δ₀_strong) δ₄) δ₅_strong :=
    le_trans hδ₀_le_A (min_le_left _ _)
  have h_step1 : δ₀ ≤ min (min (min δ₁ δ₂) δ₀_strong) δ₄ :=
    le_trans hδ₀_le_B (min_le_left (min (min (min δ₁ δ₂) δ₀_strong) δ₄) δ₅_strong)
  have hδ₀_le_C : δ₀ ≤ min (min δ₁ δ₂) δ₀_strong :=
    le_trans h_step1 (min_le_left (min (min δ₁ δ₂) δ₀_strong) δ₄)
  have h_step2 : δ₀ ≤ min δ₁ δ₂ :=
    le_trans hδ₀_le_C (min_le_left (min δ₁ δ₂) δ₀_strong)
  have hδ₀_le_D : δ₀ ≤ min δ₁ δ₂ := h_step2
  have hδ₀_le_δ1 : δ₀ ≤ δ₁ := le_trans hδ₀_le_D (min_le_left _ _)
  have hδ₀_le_δ2 : δ₀ ≤ δ₂ := le_trans hδ₀_le_D (min_le_right _ _)
  have hδ₀_le_strong : δ₀ ≤ δ₀_strong :=
    le_trans hδ₀_le_C (min_le_right (min δ₁ δ₂) δ₀_strong)
  have hδ₀_le_δ4 : δ₀ ≤ δ₄ :=
    le_trans h_step1 (min_le_right (min (min δ₁ δ₂) δ₀_strong) δ₄)
  have hδ₀_le_pr : δ₀ ≤ δ₄_pr :=
    le_trans hδ₀_le_δ4 (min_le_left δ₄_pr δ₄_branch)
  have hδ₀_le_branch : δ₀ ≤ δ₄_branch :=
    le_trans hδ₀_le_δ4 (min_le_right δ₄_pr δ₄_branch)
  have hδ₀_le_strong5 : δ₀ ≤ δ₅_strong :=
    le_trans hδ₀_le_B (min_le_right (min (min (min δ₁ δ₂) δ₀_strong) δ₄) δ₅_strong)
  have hδ₀_le_δ6_cor : δ₀ ≤ δ₆_cor :=
    le_trans hδ₀_le_A (min_le_right (min (min (min (min δ₁ δ₂) δ₀_strong) δ₄) δ₅_strong) δ₆_cor)
  have h_small_cond : ∀ {δ : ℝ}, 0 < δ → δ ≤ δ₀ →
      (2 * K) * δ ^ (κ / 2 - ε') ≤ 1 := by
    intro δ hδ_pos hδ_le
    have h1 : δ ≤ δ₁ := le_trans hδ_le hδ₀_le_δ1
    have h2 : δ ^ (κ / 2 - ε') ≤ δ₁ ^ (κ / 2 - ε') :=
      Real.rpow_le_rpow (by linarith) h1 (by linarith)
    have h3 : δ₁ ^ (κ / 2 - ε') = 1 / (2 * K) := by
      have h_pos_base : 0 ≤ 1 / (2 * K) := by positivity
      have h_exp : (1 / (κ / 2 - ε')) * (κ / 2 - ε') = 1 := by
        have h5 : (1 / (κ / 2 - ε')) = (κ / 2 - ε')⁻¹ := by simp
        rw [h5, inv_mul_cancel₀ h_exp_pos.ne']
      have h : ((1 / (2 * K)) ^ (1 / (κ / 2 - ε'))) ^ (κ / 2 - ε') = (1 / (2 * K)) := by
        rw [← Real.rpow_mul h_pos_base, h_exp, Real.rpow_one]
      simpa [δ₁] using h
    have hK2 : 0 < 2 * K := by positivity
    have h4 : (2 * K) * δ ^ (κ / 2 - ε') ≤ (2 * K) * δ₁ ^ (κ / 2 - ε') :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    calc (2 * K) * δ ^ (κ / 2 - ε')
      ≤ (2 * K) * δ₁ ^ (κ / 2 - ε') := h4
      _ = (2 * K) * (1 / (2 * K)) := by rw [h3]
      _ = 1 := by field_simp [hK2.ne'] <;> ring
  have h_const_cond : ∀ {δ : ℝ}, 0 < δ → δ ≤ δ₀ →
      K * δ ^ (ε - ε') ≤ 1 := by
    intro δ hδ_pos hδ_le
    have h1 : δ ≤ δ₂ := le_trans hδ_le hδ₀_le_δ2
    have h2 : δ ^ (ε - ε') ≤ δ₂ ^ (ε - ε') :=
      Real.rpow_le_rpow (by linarith) h1 (by linarith)
    have h3 : δ₂ ^ (ε - ε') = 1 / K := by
      have h_pos_base : 0 ≤ 1 / K := by positivity
      have h_exp : (1 / (ε - ε')) * (ε - ε') = 1 := by
        have h5 : (1 / (ε - ε')) = (ε - ε')⁻¹ := by simp
        rw [h5, inv_mul_cancel₀ h_ε_diff_pos.ne']
      have h : ((1 / K) ^ (1 / (ε - ε'))) ^ (ε - ε') = (1 / K) := by
        rw [← Real.rpow_mul h_pos_base, h_exp, Real.rpow_one]
      simpa [δ₂] using h
    have hK_pos : 0 < K := by positivity
    have h4 : K * δ ^ (ε - ε') ≤ K * δ₂ ^ (ε - ε') :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    calc K * δ ^ (ε - ε')
      ≤ K * δ₂ ^ (ε - ε') := h4
      _ = K * (1 / K) := by rw [h3]
      _ = 1 := by field_simp [hK_pos.ne'] <;> ring
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, fun {δ} hδ_dyadic hδ_pos hδ_le_δ₀ A μ hA hA_delta hN_bd hμ hμ_supp => ?_⟩
  let C_mu := K * δ ^ (-ε')
  have hC_mu_pos : 0 < C_mu := by positivity
  -- Step 1: Restrict away from zero
  rcases restrict_away_from_zero hμ hμ_supp with ⟨a, μ₁, ha_pos, ha_def, hμ₁_supp, hμ₁_supp_subset, hμ₁_frost⟩
  let C_mu2 := 2 * C_mu
  have hC_mu2_pos : 0 < C_mu2 := by positivity
  have hμ₁_supp01 : μ₁.support ⊆ Set.Icc 0 1 := by
    have h1 : μ₁.support ⊆ Set.Icc a 1 := hμ₁_supp
    have h2 : Set.Icc a 1 ⊆ Set.Icc 0 1 := by
      intro x hx
      have h3 : a ≤ x := hx.1
      have h4 : x ≤ 1 := hx.2
      constructor
      · linarith [ha_pos]
      · exact h4
    exact h1.trans h2
  -- Step 2: Direction Frostman for maximal density
  have hμ₁_dir : IsDirectionFrostman δ κ C_mu2 μ₁ :=
    hμ₁_frost.toDirectionFrostman hμ₁_supp01 hδ_pos
  -- Step 3: Maximal density interval
  have hδ_le_one : δ ≤ 1 := by linarith
  rcases maximal_density_interval_C_with_support hδ_pos hδ_le_one hκ_pos hC_mu2_pos hμ₁_dir
    with ⟨x₀, r₀, hr₀_geδ, hr₀_le1, hx0_in_support, hμ₁I₀_pos, _h_lower, h_density, h_self_sim⟩
  have hx0_ge_a : a ≤ x₀ := by
    have h : x₀ ∈ μ₁.support := hx0_in_support
    have h' : x₀ ∈ Set.Icc a 1 := hμ₁_supp h
    exact h'.1
  have hx0_pos : 0 < x₀ := by linarith [ha_pos]
  have hx0_le_one : x₀ ≤ 1 := by
    have h : x₀ ∈ Set.Icc a 1 := hμ₁_supp hx0_in_support
    exact h.2
  have hr₀_pos : 0 < r₀ := lt_of_lt_of_le hδ_pos hr₀_geδ
  let I₀ := Set.Icc x₀ (x₀ + r₀)
  have hμ₁I₀_ne_top : μ₁ I₀ ≠ ⊤ := by
    have h : μ₁ I₀ ≤ μ₁ Set.univ := measure_mono (Set.subset_univ _)
    have h2 : μ₁ Set.univ = 1 := hμ₁_frost.1
    rw [h2] at h
    exact h.trans_lt ENNReal.one_lt_top |>.ne
  have h_small : C_mu2 * δ ^ (κ / 2) ≤ 1 := by
    have h1 : C_mu2 * δ ^ (κ / 2) = (2 * K) * δ ^ (κ / 2 - ε') := by
      have h2 : δ ^ (-ε') * δ ^ (κ / 2) = δ ^ (κ / 2 - ε') := by
        have h_exp : -ε' + κ / 2 = κ / 2 - ε' := by ring
        rw [← Real.rpow_add (by linarith), h_exp]
      calc C_mu2 * δ ^ (κ / 2)
        = (2 * K) * (δ ^ (-ε') * δ ^ (κ / 2)) := by simp [C_mu2, C_mu] <;> ring
      _ = (2 * K) * δ ^ (κ / 2 - ε') := by rw [h2]
    rw [h1]
    exact h_small_cond hδ_pos hδ_le_δ₀
  -- Step 4: All-scale renormalization
  rcases all_scale_renormalize hδ_pos hκ_pos hr₀_pos hr₀_le1
      hμ₁I₀_pos hμ₁I₀_ne_top hμ₁_frost hμ₁_supp01 h_density h_self_sim h_small
    with ⟨ν, hν_univ, hν_supp, hν_frost1, hν_prov⟩

  -- Step 5: Apply strong theorem to ν with t = r₀
  -- Weaken delta-set exponent from κ to κ/2 (since r^κ ≤ r^{κ/2} for r ≤ 1)
  have hA_delta2 : IsRealDeltaSet δ (κ / 2) (δ ^ (-ε)) A := by
    have h1 : IsRealDeltaSet δ (κ / 2) (K * δ ^ (-ε')) A :=
      IsRealDeltaSet.monotone_exponent hA_delta (by linarith) (by linarith)
    have h2 : K * δ ^ (-ε') ≤ δ ^ (-ε) := by
      have h3 : K * δ ^ (ε - ε') ≤ 1 := h_const_cond hδ_pos hδ_le_δ₀
      have h4 : δ ^ (-ε') = δ ^ (-ε) * δ ^ (ε - ε') := by
        have h5 : (-ε') = (-ε) + (ε - ε') := by ring
        rw [h5]
        rw [← Real.rpow_add (by positivity)]
        <;> ring
      rw [h4]
      have h6 : K * (δ ^ (-ε) * δ ^ (ε - ε')) = δ ^ (-ε) * (K * δ ^ (ε - ε')) := by ring
      rw [h6]
      have h7 : K * δ ^ (ε - ε') ≤ 1 := h3
      have h8 : δ ^ (-ε) * (K * δ ^ (ε - ε')) ≤ δ ^ (-ε) * 1 := by gcongr
      linarith
    rcases h1 with ⟨h_bdd, h_ne, h_d, h_dyad, hδp, h_s1, h_s2, _, h_bound⟩
    refine' ⟨h_bdd, h_ne, h_d, h_dyad, hδp, h_s1, h_s2, by positivity, _⟩
    intro r Q hr hQ hδr hr1
    have h3 := h_bound hr hQ hδr hr1
    have h4 : ENNReal.ofReal (K * δ ^ (-ε')) ≤ ENNReal.ofReal (δ ^ (-ε)) :=
      ENNReal.ofReal_le_ofReal h2
    calc _ ≤ ENNReal.ofReal (K * δ ^ (-ε')) * _ * _ := h3
         _ ≤ ENNReal.ofReal (δ ^ (-ε)) * _ * _ := by gcongr
  -- Weaken size bound constant
  have hN_bd2 : Nreal δ A ≤ ENNReal.ofReal (δ ^ (-(s + ε))) := by
    have h1 : K * δ ^ (-(s + ε')) ≤ δ ^ (-(s + ε)) := by
      have h2 : K * δ ^ (ε - ε') ≤ 1 := h_const_cond hδ_pos hδ_le_δ₀
      have h3 : δ ^ (-(s + ε')) = δ ^ (-(s + ε)) * δ ^ (ε - ε') := by
        have h4 : (-(s + ε')) = (-(s + ε)) + (ε - ε') := by ring
        rw [h4]
        rw [← Real.rpow_add (by positivity)]
        <;> ring
      rw [h3]
      have h5 : K * (δ ^ (-(s + ε)) * δ ^ (ε - ε')) = δ ^ (-(s + ε)) * (K * δ ^ (ε - ε')) := by ring
      rw [h5]
      have h6 : K * δ ^ (ε - ε') ≤ 1 := h2
      have h7 : δ ^ (-(s + ε)) * (K * δ ^ (ε - ε')) ≤ δ ^ (-(s + ε)) * 1 := by gcongr
      linarith
    have h3 : Nreal δ A ≤ ENNReal.ofReal (K * δ ^ (-(s + ε'))) := hN_bd
    have h4 : ENNReal.ofReal (K * δ ^ (-(s + ε'))) ≤ ENNReal.ofReal (δ ^ (-(s + ε))) :=
      ENNReal.ofReal_le_ofReal h1
    exact le_trans h3 h4
  -- Step 5: Apply strong theorem with t = r₀
  have ht_ge : δ ^ c ≤ r₀ := by
    have h_r0_lower2 : r₀ ≥ (2 * K) ^ (-2 / κ) * δ ^ (2 * ε' / κ) := by
      have h8 : C_mu2 = 2 * K * δ ^ (-ε') := by
        simp [C_mu2, C_mu] <;> ring
      rw [h8] at _h_lower
      have h9 : (2 * K * δ ^ (-ε')) ^ (-2 / κ) = (2 * K) ^ (-2 / κ) * δ ^ (2 * ε' / κ) := by
        have h91 : (2 * K * δ ^ (-ε')) ^ (-2 / κ) = (2 * K) ^ (-2 / κ) * (δ ^ (-ε')) ^ (-2 / κ) := by
          have h_pos1 : 0 ≤ 2 * K := by positivity
          have h_pos2 : 0 ≤ δ ^ (-ε') := by positivity
          rw [Real.mul_rpow h_pos1 h_pos2] <;> rfl
        rw [h91]
        have h92 : (δ ^ (-ε')) ^ (-2 / κ) = δ ^ (2 * ε' / κ) := by
          have h_exp : (-ε') * (-2 / κ) = 2 * ε' / κ := by ring
          rw [← Real.rpow_mul (by linarith), h_exp]
        rw [h92] <;> rfl
      rw [h9] at _h_lower
      exact _h_lower
    have h10 : δ ^ (c - 2 * ε' / κ) ≤ (2 * K) ^ (-2 / κ) := by
      have h11 : δ ≤ δ₅_strong := le_trans hδ_le_δ₀ hδ₀_le_strong5
      have h12 : δ ^ (c - 2 * ε' / κ) ≤ δ₅_strong ^ (c - 2 * ε' / κ) :=
        Real.rpow_le_rpow hδ_pos.le h11 h_exp_strong_pos.le
      have h13 : δ₅_strong ^ (c - 2 * ε' / κ) = C_strong := by
        have h14 : (1 / (c - 2 * ε' / κ)) * (c - 2 * ε' / κ) = 1 := by
          have hne : (c - 2 * ε' / κ) ≠ 0 := h_exp_strong_pos.ne'
          exact one_div_mul_cancel hne
        have h15 : δ₅_strong = C_strong ^ (1 / (c - 2 * ε' / κ)) := by rfl
        have hC_strong_pos : 0 < C_strong := by
          dsimp only [C_strong]
          apply Real.rpow_pos_of_pos
          positivity
        rw [h15]
        rw [← Real.rpow_mul hC_strong_pos.le, h14, Real.rpow_one]
      rw [h13] at h12
      exact h12
    have h15 : δ ^ c = δ ^ (c - 2 * ε' / κ) * δ ^ (2 * ε' / κ) := by
      have h_exp : (c - 2 * ε' / κ) + 2 * ε' / κ = c := by ring
      rw [← Real.rpow_add (by positivity), h_exp]
    rw [h15]
    have h16 : δ ^ (c - 2 * ε' / κ) * δ ^ (2 * ε' / κ) ≤ (2 * K) ^ (-2 / κ) * δ ^ (2 * ε' / κ) := by
      gcongr
    exact h16.trans h_r0_lower2
  have hδ_le_strong : δ ≤ δ₀_strong := le_trans hδ_le_δ₀ hδ₀_le_strong
  have h_strong_result := h_strongδ (hδ_dyadic) (hδ_pos) hδ_le_strong
    A ν r₀ hA hA_delta2 hN_bd2 hν_frost1 hν_supp ht_ge hr₀_le1
  rcases h_strong_result with ⟨z, hz_supp, h_expand⟩

  -- Step 6: Scale back and three-case PR
  let y := r₀ * z
  let x := x₀ + y
  let B := scaleSet r₀⁻¹ A
  let S := Set.image2 (fun a b => a + z * b) B A
  let AyA := Set.image2 (· + ·) A (scaleSet y A)
  let AxA := Set.image2 (· + ·) A (scaleSet x A)
  let AAA := Set.image2 (· + ·) A A
  let Amx0A := Set.image2 (· - ·) A (scaleSet x₀ A)
  let Ax0A := Set.image2 (· + ·) A (scaleSet x₀ A)
  let Y : Fin 3 → Set ℝ := fun i =>
    match i with
    | 0 => A
    | 1 => scaleSet x A
    | 2 => scaleSet (-x₀) A

  -- Support provenance: x ∈ μ.support
  have h_x_in_supp : x ∈ μ.support := by
    have h1 : x₀ + r₀ * z ∈ μ₁.support := hν_prov z hz_supp
    exact hμ₁_supp_subset h1

  -- z > 0 (otherwise strong theorem gives δ^{-c} ≤ 1)
  have hA_bdd : Bornology.IsBounded A :=
    SetDiscretizationBridge.realLineCopy_bounded_iff.mp hA_delta.1
  have hA_nonempty : A.Nonempty :=
    SetDiscretizationBridge.realLineCopy_nonempty_iff.mp hA_delta.2.1
  have hz_pos : 0 < z := by
    by_contra h
    have hz_le0 : z ≤ 0 := by linarith
    have hz_ge0 : 0 ≤ z := by
      have h1 : z ∈ Set.Icc (0 : ℝ) 1 := hν_supp hz_supp
      exact h1.1
    have hz0 : z = 0 := by linarith
    have hB_nonempty : B.Nonempty := by
      rcases hA_nonempty with ⟨a_elem, ha_elem⟩
      refine ⟨r₀⁻¹ * a_elem, ?_⟩
      simp only [B, scaleSet, Set.mem_image]
      exact ⟨a_elem, ha_elem, rfl⟩
    have hB_bdd : Bornology.IsBounded B := by
      let f : ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ r₀⁻¹
      have h_eq : B = f '' A := by
        ext y
        simp [B, scaleSet, f]
        <;> constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, rfl⟩
      rw [h_eq]
      exact hA_bdd.image f
    have hB_ne_top : Nreal δ B ≠ ⊤ := by
      have h_eq : Nreal δ B = ENat.toENNReal (bourgain_projection_theorem.realCubeIndexSet δ B).encard := by
        rw [show Nreal δ B = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy B)) from rfl]
        exact bourgain_projection_theorem.realCoveringNumber_eq_card hδ_pos hB_bdd
      rw [h_eq]
      have h_fin : (bourgain_projection_theorem.realCubeIndexSet δ B).Finite :=
        bourgain_projection_theorem.realCubeIndexSet_finite hδ_pos hB_bdd
      have h_ne_top : (bourgain_projection_theorem.realCubeIndexSet δ B).encard ≠ ⊤ := h_fin.encard_lt_top.ne
      have h : ENat.toENNReal (bourgain_projection_theorem.realCubeIndexSet δ B).encard ≠ ⊤ := by
        rw [ENat.toENNReal_ne_top]
        exact h_ne_top
      exact h
    have hB_realLineCopy_nonempty : (realLineCopy B).Nonempty :=
      SetDiscretizationBridge.realLineCopy_nonempty_iff.mpr hB_nonempty
    have hB_pos : 0 < Nreal δ B := by
      have h1 : 0 < dyadicCoveringNumber δ (realLineCopy B) :=
        robust_projection.dyadic_covering_number_pos hδ_pos hB_realLineCopy_nonempty
      have h2 : Nreal δ B = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy B)) := by
        rfl
      rw [h2]
      have hne : (dyadicCoveringNumber δ (realLineCopy B)) ≠ 0 := h1.ne'
      have h3 : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy B)) ≠ 0 := by
        exact_mod_cast hne
      exact h3.bot_lt
    have hS_eq : S = B := by
      ext w
      simp only [S, Set.mem_image2]
      constructor
      · rintro ⟨b, hb, a, ha, rfl⟩
        simpa [hz0] using hb
      · intro hw
        rcases hA_nonempty with ⟨a_elem, ha_elem⟩
        refine ⟨w, hw, a_elem, ha_elem, ?_⟩
        rw [hz0]; simp
    have h_expand' : ENNReal.ofReal (δ ^ (-c)) * Nreal δ B ≤ Nreal δ B := by
      have h : ENNReal.ofReal (δ ^ (-c)) * Nreal δ B ≤ Nreal δ S := h_expand
      rw [hS_eq] at h
      exact h
    have h_contra : ENNReal.ofReal (δ ^ (-c)) ≤ 1 := by
      have h : ENNReal.ofReal (δ ^ (-c)) * Nreal δ B ≤ Nreal δ B := h_expand'
      have h2 : ENNReal.ofReal (δ ^ (-c)) ≤ 1 := by
        have h21 : ENNReal.ofReal (δ ^ (-c)) * Nreal δ B ≤ 1 * Nreal δ B := by
          simpa [one_mul] using h
        exact (ENNReal.mul_le_mul_iff_left hB_pos.ne' hB_ne_top).mp h21
      exact h2
    have h1_real : (1 : ℝ) < δ ^ (-c) := by
      have h2 : 0 < δ := hδ_pos
      have hδ1_lt_one : δ₁ < 1 := by
        have h_base_lt_one : 1 / (2 * K) < 1 := by
          have h : 1 < 2 * K := by linarith
          exact (div_lt_one (by positivity)).mpr h
        have h_exp_pos : 0 < 1 / (κ / 2 - ε') := by positivity
        exact Real.rpow_lt_one (by positivity) h_base_lt_one h_exp_pos
      have h3 : δ < 1 := by
        calc δ ≤ δ₀ := hδ_le_δ₀
          _ ≤ δ₁ := hδ₀_le_δ1
          _ < 1 := hδ1_lt_one
      have h4 : δ ^ (-c) > 1 := by
        have h5 : δ ^ c < 1 := Real.rpow_lt_one (by linarith) h3 (by linarith)
        have h6 : 0 < δ ^ c := by positivity
        have h7 : δ ^ (-c) = (δ ^ c)⁻¹ := by
          rw [Real.rpow_neg (by linarith)] <;> ring
        rw [h7]
        have h7 : 1 < (δ ^ c)⁻¹ := by
          have h8 : 0 < δ ^ c := h6
          have h9 : δ ^ c < 1 := h5
          exact (one_lt_inv₀ h8).mpr h9
        exact h7
      exact h4
    have h_false : (1 : ENNReal) < ENNReal.ofReal (δ ^ (-c)) := by
      have h_pos : 0 < δ ^ (-c) := by positivity
      exact one_lt_ofReal.mpr h1_real
    exact (not_le.mpr h_false) h_contra
  have hy_pos : 0 < y := mul_pos hr₀_pos hz_pos
  have hx_pos : 0 < x := by
    have h1 : x ∈ μ₁.support := hν_prov z hz_supp
    have h2 : μ₁.support ⊆ Set.Icc a 1 := hμ₁_supp
    have h3 : x ∈ Set.Icc a 1 := h2 h1
    have h4 : a ≤ x := h3.1
    exact lt_of_lt_of_le ha_pos h4
  have hx_le_one : x ≤ 1 := by
    have h1 : x ∈ μ₁.support := hν_prov z hz_supp
    have h2 : μ₁.support ⊆ Set.Icc a 1 := hμ₁_supp
    have h3 : x ∈ Set.Icc a 1 := h2 h1
    exact h3.2
  have hy_le_one : y ≤ 1 := by
    have hz_le_one : z ≤ 1 := by
      have h1 : ν.support ⊆ Set.Icc 0 1 := hν_supp
      have h2 : z ∈ Set.Icc 0 1 := h1 hz_supp
      exact h2.2
    calc y = r₀ * z := by rfl
      _ ≤ 1 * 1 := by gcongr <;> linarith
      _ = 1 := by ring

  -- Boundedness via set addition/subtraction
  have hB_bdd : Bornology.IsBounded B := scaleSet_bounded hA_bdd
  have hzA_bdd : Bornology.IsBounded (scaleSet z A) := scaleSet_bounded hA_bdd
  have hS_eq : S = B + scaleSet z A := by
    ext w; simp [S, scaleSet, Set.mem_image2] <;> constructor
    · rintro ⟨b, hb, a, ha, rfl⟩
      exact ⟨b, hb, z * a, ⟨a, ha, by ring⟩, by ring⟩
    · rintro ⟨b, hb, c, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨b, hb, a, ha, by ring⟩
  have hS_bdd : Bornology.IsBounded S := by rw [hS_eq]; exact hB_bdd.add hzA_bdd
  have hsyA_bdd : Bornology.IsBounded (scaleSet y A) := scaleSet_bounded hA_bdd
  have hAyA_bdd : Bornology.IsBounded AyA := hA_bdd.add hsyA_bdd
  have hsxA_bdd : Bornology.IsBounded (scaleSet x A) := scaleSet_bounded hA_bdd
  have hAxA_bdd : Bornology.IsBounded AxA := hA_bdd.add hsxA_bdd
  have hAAA_bdd : Bornology.IsBounded AAA := hA_bdd.add hA_bdd
  have hsx0A_bdd : Bornology.IsBounded (scaleSet x₀ A) := scaleSet_bounded hA_bdd
  have hAmx0A_bdd : Bornology.IsBounded Amx0A := hA_bdd.sub hsx0A_bdd
  have hAx0A_bdd : Bornology.IsBounded Ax0A := hA_bdd.add hsx0A_bdd
  have hY_bdd : ∀ i, Bornology.IsBounded (Y i) := by
    intro i
    fin_cases i
    · exact hA_bdd
    · exact scaleSet_bounded hA_bdd
    · exact scaleSet_bounded hA_bdd

  -- Nonemptiness
  have hB_nonempty : B.Nonempty := by
    rcases hA_nonempty with ⟨a, ha⟩
    refine ⟨r₀⁻¹ * a, ?_⟩
    simp only [B, scaleSet, Set.mem_image]
    exact ⟨a, ha, by ring⟩
  have hNA_ne_zero : Nreal δ A ≠ 0 := by
    have h_realLineCopy_nonempty : (realLineCopy A).Nonempty :=
      SetDiscretizationBridge.realLineCopy_nonempty_iff.mpr hA_nonempty
    have h1 : 0 < dyadicCoveringNumber δ (realLineCopy A) :=
      robust_projection.dyadic_covering_number_pos hδ_pos h_realLineCopy_nonempty
    have h2 : Nreal δ A = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) := by rfl
    rw [h2]
    have hne : (dyadicCoveringNumber δ (realLineCopy A)) ≠ 0 := h1.ne'
    have h3 : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) ≠ 0 := by
      exact_mod_cast hne
    exact h3
  have hNA_ne_top : Nreal δ A ≠ ⊤ := by
    have h_eq : Nreal δ A = ENat.toENNReal (ProductLikeIncidence.realCubeIndexSet δ A).encard :=
      ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hδ_pos hA_bdd
    rw [h_eq]
    have h_fin : (ProductLikeIncidence.realCubeIndexSet δ A).Finite :=
      ProductLikeIncidence.realCubeIndexSet_finite hδ_pos hA_bdd
    have h_ne_top : (ProductLikeIncidence.realCubeIndexSet δ A).encard ≠ ⊤ := h_fin.encard_lt_top.ne
    have h : ENat.toENNReal (ProductLikeIncidence.realCubeIndexSet δ A).encard ≠ ⊤ := by
      rw [ENat.toENNReal_ne_top]
      exact h_ne_top
    exact h

  -- r₀ lower bound
  have hr₀_lower : C_mu2 ^ (-2 / κ) ≤ r₀ := _h_lower
  have ha_eq : a = (2 * C_mu) ^ (-1 / κ) := ha_def

  -- Scale back: N(AyA) ≥ (r₀/9) * δ^{-c} * N(A)
  have h1 : Nreal δ B = Nreal (δ * r₀) A := by
    have h2 : Nreal δ B = Nreal (δ / r₀⁻¹) A := Nreal_scaling hδ_pos (by positivity) hA_bdd
    have h3 : δ / r₀⁻¹ = δ * r₀ := by
      field_simp [hr₀_pos.ne'] <;> ring
    rw [h2, h3]
  have h2 : Nreal δ A ≤ 3 * Nreal δ B := by
    rw [h1]
    have h_ref : Nreal δ A ≤ 2 * Nreal (δ * r₀) A :=
      Nreal_refining (mul_pos hδ_pos hr₀_pos) hδ_pos (by nlinarith) hA_bdd
    exact le_trans h_ref (by gcongr <;> norm_num)
  have h3 : ENNReal.ofReal (δ ^ (-c)) * Nreal δ B ≤ Nreal δ S := h_expand
  have h4 : Nreal δ AyA = Nreal (δ / r₀) S := by
    have h5 : AyA = scaleSet r₀ S := by
      ext w
      simp only [AyA, S, B, scaleSet, Set.mem_image2, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        rcases hb with ⟨c, hc, rfl⟩
        refine ⟨r₀⁻¹ * a + z * c, ?_, ?_⟩
        · exact ⟨r₀⁻¹ * a, ⟨a, ha, by ring⟩, c, hc, by ring⟩
        · have hy : y = r₀ * z := by rfl
          rw [hy] <;> field_simp [hr₀_pos.ne'] <;> ring
      · rintro ⟨s, hs, rfl⟩
        rcases hs with ⟨b, hb, a_elem, ha_elem, rfl⟩
        rcases hb with ⟨a', ha', rfl⟩
        have h_ya : y * a_elem ∈ scaleSet y A := by
          exact ⟨a_elem, ha_elem, rfl⟩
        have h_eq : a' + y * a_elem = r₀ * (r₀⁻¹ * a' + z * a_elem) := by
          have hy : y = r₀ * z := by rfl
          rw [hy] <;> field_simp [hr₀_pos.ne'] <;> ring
        exact ⟨a', ha', y * a_elem, h_ya, h_eq⟩
    rw [h5]
    exact Nreal_scaling hδ_pos hr₀_pos hS_bdd
  have h5 : ENNReal.ofReal (r₀ / 3) * Nreal δ S ≤ Nreal (δ / r₀) S := by
    have h51 : (δ / r₀) * r₀ = δ := by
      field_simp [hr₀_pos.ne'] <;> ring
    have h := Nreal_coarsening (div_pos hδ_pos hr₀_pos) hr₀_pos hr₀_le1 hS_bdd
    rw [h51] at h
    exact h
  have h_scale_back : ENNReal.ofReal (r₀ / 9) * ENNReal.ofReal (δ ^ (-c)) * Nreal δ A ≤ Nreal δ AyA := by
    have h_c9 : ENNReal.ofReal (r₀ / 9) * ENNReal.ofReal (δ ^ (-c)) =
        ENNReal.ofReal ((r₀ / 9) * δ ^ (-c)) := by
      exact (ENNReal.ofReal_mul (by positivity)).symm
    have h_c3 : ENNReal.ofReal (r₀ / 3) * ENNReal.ofReal (δ ^ (-c)) =
        ENNReal.ofReal ((r₀ / 3) * δ ^ (-c)) := by
      exact (ENNReal.ofReal_mul (by positivity)).symm
    have h_div3 : ENNReal.ofReal (1 / 3) * Nreal δ A ≤ Nreal δ B := by
      have h : Nreal δ A ≤ (3 : ENNReal) * Nreal δ B := h2
      have h' : ENNReal.ofReal (1 / 3) * Nreal δ A ≤ ENNReal.ofReal (1 / 3) * ((3 : ENNReal) * Nreal δ B) := by gcongr
      have h31 : (3 : ENNReal) = ENNReal.ofReal 3 := by norm_cast
      have h3 : ENNReal.ofReal (1 / 3) * (3 : ENNReal) = 1 := by
        rw [h31]
        have h_mul : ENNReal.ofReal (1 / 3) * ENNReal.ofReal 3 = ENNReal.ofReal ((1 / 3) * 3) := by
          rw [← ENNReal.ofReal_mul (show 0 ≤ (1 / 3 : ℝ) from by norm_num)]
        rw [h_mul]
        have h2 : (1 / 3 : ℝ) * 3 = 1 := by norm_num
        rw [h2]
        simp
      have h4 : ENNReal.ofReal (1 / 3) * ((3 : ENNReal) * Nreal δ B) = Nreal δ B := by
        rw [← mul_assoc, h3, one_mul]
      rw [h4] at h'
      exact h'
    have h_coeff : ENNReal.ofReal ((r₀ / 9) * δ ^ (-c)) =
        ENNReal.ofReal ((r₀ / 3) * δ ^ (-c)) * ENNReal.ofReal (1 / 3) := by
      have h_real : (r₀ / 9) * δ ^ (-c) = ((r₀ / 3) * δ ^ (-c)) * (1 / 3) := by ring
      rw [h_real, ← ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (r₀ / 9) * ENNReal.ofReal (δ ^ (-c)) * Nreal δ A
      = ENNReal.ofReal ((r₀ / 9) * δ ^ (-c)) * Nreal δ A := by rw [h_c9]
    _ = ENNReal.ofReal ((r₀ / 3) * δ ^ (-c)) * (ENNReal.ofReal (1 / 3) * Nreal δ A) := by
      rw [h_coeff, mul_assoc]
    _ ≤ ENNReal.ofReal ((r₀ / 3) * δ ^ (-c)) * Nreal δ B := by gcongr
    _ = ENNReal.ofReal (r₀ / 3) * (ENNReal.ofReal (δ ^ (-c)) * Nreal δ B) := by
      rw [← h_c3, mul_assoc]
    _ ≤ ENNReal.ofReal (r₀ / 3) * Nreal δ S := by gcongr <;> exact h3
    _ ≤ Nreal (δ / r₀) S := h5
    _ = Nreal δ AyA := by rw [h4]

  -- Family sum and inclusion
  have h_family_sum : Set.image2 (· + ·) A (Set.image2 (· + ·) (scaleSet x A) (scaleSet (-x₀) A)) = ProductLikeIncidence.familySum Y := by
    simp [Y, ProductLikeIncidence.familySum]
    <;> rfl
  have h_subset : AyA ⊆ ProductLikeIncidence.familySum Y := by
    rw [← h_family_sum]
    intro w hw
    rcases hw with ⟨a, ha, b, hb, rfl⟩
    rcases hb with ⟨c, hc, rfl⟩
    have h7 : x * c + (-x₀) * c = y * c := by ring
    have hxc : x * c ∈ scaleSet x A := by
      simp only [scaleSet, Set.mem_image]
      exact ⟨c, hc, by ring⟩
    have hmx0c : (-x₀) * c ∈ scaleSet (-x₀) A := by
      simp only [scaleSet, Set.mem_image]
      exact ⟨c, hc, by ring⟩
    refine ⟨a, ha, x * c + (-x₀) * c, ?_, by rw [h7]⟩
    exact ⟨x * c, hxc, (-x₀) * c, hmx0c, rfl⟩
  have h_family_large : Nreal δ (ProductLikeIncidence.familySum Y) ≥ Nreal δ AyA := by
    have h_rc : realLineCopy AyA ⊆ realLineCopy (ProductLikeIncidence.familySum Y) := by
      intro x hx
      exact h_subset hx
    exact ENat.toENNReal_mono (ProductLikeIncidence.dyadicCoveringNumber_mono h_rc)

  -- PR threshold: 648 * α^3 * N(A) < N(familySum Y)
  let α : ENNReal := ENNReal.ofReal (δ ^ (-c / 4))
  have h_pr_cond : ENNReal.ofReal (648 * (δ ^ (-c / 4)) ^ 3) * Nreal δ A <
      ENNReal.ofReal (r₀ / 9) * ENNReal.ofReal (δ ^ (-c)) * Nreal δ A := by
    have h6 : (648 * (δ ^ (-c / 4)) ^ 3 : ℝ) < (r₀ / 9) * (δ ^ (-c)) := by
      have h7 : r₀ ≥ (2 * K) ^ (-2 / κ) * δ ^ (2 * ε' / κ) := by
        have h8 : C_mu2 = 2 * K * δ ^ (-ε') := by
          simp [C_mu2, C_mu] <;> ring
        rw [h8] at hr₀_lower
        have h9 : (2 * K * δ ^ (-ε')) ^ (-2 / κ) = (2 * K) ^ (-2 / κ) * δ ^ (2 * ε' / κ) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
          have h10 : (δ ^ (-ε')) ^ (-2 / κ) = δ ^ (2 * ε' / κ) := by
            rw [← Real.rpow_mul (by positivity)] <;> ring_nf
          rw [h10] <;> ring
        rw [h9] at hr₀_lower
        exact hr₀_lower
      have h10 : δ ^ (c / 4 - 2 * ε' / κ) ≤ (2 * K) ^ (-2 / κ) / 10000 := by
        have h11 : δ ≤ δ₄_pr := le_trans hδ_le_δ₀ hδ₀_le_pr
        have h_exp_pos : 0 < c / 4 - 2 * ε' / κ := h_exp_pr_pos
        have h12 : δ ^ (c / 4 - 2 * ε' / κ) ≤ δ₄_pr ^ (c / 4 - 2 * ε' / κ) :=
          Real.rpow_le_rpow (by linarith) h11 (by linarith)
        have h13 : δ₄_pr ^ (c / 4 - 2 * ε' / κ) = C_pr := by
          have h_ne : (c / 4 - 2 * ε' / κ) ≠ 0 := h_exp_pos.ne'
          have h14 : ((1 / (c / 4 - 2 * ε' / κ)) * (c / 4 - 2 * ε' / κ)) = 1 := by
            have h_inv : (1 / (c / 4 - 2 * ε' / κ)) = (c / 4 - 2 * ε' / κ)⁻¹ := by simp
            rw [h_inv]
            exact inv_mul_cancel₀ h_ne
          simp only [δ₄_pr]
          rw [← Real.rpow_mul (show 0 ≤ C_pr from by positivity), h14, Real.rpow_one]
        rw [h13] at h12
        exact h12
      have h15 : (648 * (δ ^ (-c / 4)) ^ 3 : ℝ) = 648 * δ ^ (-3 * c / 4) := by
        have h_pos : 0 ≤ δ := by linarith
        have h162 : (δ ^ (-c / 4)) ^ 3 = δ ^ ((-c / 4) * (3 : ℝ)) := by
          have h_cast : (δ ^ (-c / 4)) ^ 3 = (δ ^ (-c / 4)) ^ (3 : ℝ) := by norm_cast
          rw [h_cast]
          exact (Real.rpow_mul h_pos (-c / 4) (3 : ℝ)).symm
        have h163 : (-c / 4) * (3 : ℝ) = -3 * c / 4 := by ring
        rw [h162, h163]
      rw [h15]
      have h17 : (r₀ / 9) * (δ ^ (-c)) ≥ ((2 * K) ^ (-2 / κ) / 9) * δ ^ (2 * ε' / κ - c) := by
        have h171 : r₀ / 9 ≥ ((2 * K) ^ (-2 / κ) / 9) * δ ^ (2 * ε' / κ) := by
          linarith [h7]
        have h172 : δ ^ (2 * ε' / κ) * δ ^ (-c) = δ ^ (2 * ε' / κ - c) := by
          have h_pos : 0 ≤ δ := by linarith
          have h : δ ^ (2 * ε' / κ) * δ ^ (-c) = δ ^ ((2 * ε' / κ) + (-c)) :=
            (Real.rpow_add hδ_pos (2 * ε' / κ) (-c)).symm
          rw [h]
          have h2 : (2 * ε' / κ) + (-c) = 2 * ε' / κ - c := by ring
          rw [h2]
        calc (r₀ / 9) * δ ^ (-c)
          ≥ (((2 * K) ^ (-2 / κ) / 9) * δ ^ (2 * ε' / κ)) * δ ^ (-c) := by gcongr
        _ = ((2 * K) ^ (-2 / κ) / 9) * (δ ^ (2 * ε' / κ) * δ ^ (-c)) := by ring
        _ = ((2 * K) ^ (-2 / κ) / 9) * δ ^ (2 * ε' / κ - c) := by rw [h172]
      have h18 : 648 * δ ^ (-3 * c / 4) < ((2 * K) ^ (-2 / κ) / 9) * δ ^ (2 * ε' / κ - c) := by
        have h_sum : (2 * ε' / κ - c) + (c / 4 - 2 * ε' / κ) = -3 * c / 4 := by ring
        have hδ_nonneg2 : 0 ≤ δ := by linarith
        have h19 : δ ^ ((2 * ε' / κ - c) + (c / 4 - 2 * ε' / κ)) = δ ^ (2 * ε' / κ - c) * δ ^ (c / 4 - 2 * ε' / κ) :=
          Real.rpow_add hδ_pos (2 * ε' / κ - c) (c / 4 - 2 * ε' / κ)
        have h19' : δ ^ (-3 * c / 4) = δ ^ (2 * ε' / κ - c) * δ ^ (c / 4 - 2 * ε' / κ) := by
          have h2 : δ ^ (-3 * c / 4) = δ ^ ((2 * ε' / κ - c) + (c / 4 - 2 * ε' / κ)) := by rw [h_sum]
          rw [h2]
          exact h19
        rw [h19']
        have h20 : 648 * δ ^ (c / 4 - 2 * ε' / κ) < (2 * K) ^ (-2 / κ) / 9 := by
          have h21 : 648 * δ ^ (c / 4 - 2 * ε' / κ) ≤ 648 * ((2 * K) ^ (-2 / κ) / 10000) := by gcongr
          have h23 : 0 < (2 * K) ^ (-2 / κ) := by positivity
          have h24 : (648 : ℝ) / 10000 < 1 / 9 := by norm_num
          have h22 : (648 / 10000 : ℝ) * (2 * K) ^ (-2 / κ) < (1 / 9 : ℝ) * (2 * K) ^ (-2 / κ) :=
            mul_lt_mul_of_pos_right h24 h23
          have h25 : 648 * ((2 * K) ^ (-2 / κ) / 10000) = (648 / 10000 : ℝ) * (2 * K) ^ (-2 / κ) := by ring
          have h26 : 648 * ((2 * K) ^ (-2 / κ) / 10000) < (2 * K) ^ (-2 / κ) / 9 := by
            rw [h25]
            have h27 : (1 / 9 : ℝ) * (2 * K) ^ (-2 / κ) = (2 * K) ^ (-2 / κ) / 9 := by ring
            rw [h27] at h22
            exact h22
          exact h21.trans_lt h26
        have h_pos : 0 < δ ^ (2 * ε' / κ - c) := by positivity
        have h_goal : (648 * δ ^ (c / 4 - 2 * ε' / κ)) * δ ^ (2 * ε' / κ - c) <
            ((2 * K) ^ (-2 / κ) / 9) * δ ^ (2 * ε' / κ - c) :=
          mul_lt_mul_of_pos_right h20 h_pos
        have h_eq : 648 * (δ ^ (2 * ε' / κ - c) * δ ^ (c / 4 - 2 * ε' / κ)) =
            (648 * δ ^ (c / 4 - 2 * ε' / κ)) * δ ^ (2 * ε' / κ - c) := by ring
        rw [h_eq]
        exact h_goal
      exact h18.trans_le h17
    have h_pos2 : 0 < (r₀ / 9) * (δ ^ (-c)) := by positivity
    have h9 : ENNReal.ofReal (648 * (δ ^ (-c / 4)) ^ 3) < ENNReal.ofReal ((r₀ / 9) * (δ ^ (-c))) :=
      (ENNReal.ofReal_lt_ofReal_iff h_pos2).mpr h6
    have h10 : ENNReal.ofReal (648 * (δ ^ (-c / 4)) ^ 3) * Nreal δ A <
        ENNReal.ofReal ((r₀ / 9) * (δ ^ (-c))) * Nreal δ A := by
      have hNA_ne_top : Nreal δ A ≠ ⊤ := Nreal_ne_top hδ_pos hA_bdd
      have h : Nreal δ A * ENNReal.ofReal (648 * (δ ^ (-c / 4)) ^ 3) <
          Nreal δ A * ENNReal.ofReal ((r₀ / 9) * (δ ^ (-c))) :=
        (ENNReal.mul_lt_mul_iff_right hNA_ne_zero hNA_ne_top).mpr h9
      simpa [mul_comm] using h
    have h11 : ENNReal.ofReal ((r₀ / 9) * (δ ^ (-c))) =
        ENNReal.ofReal (r₀ / 9) * ENNReal.ofReal (δ ^ (-c)) :=
      ENNReal.ofReal_mul (by positivity)
    rw [h11] at h10
    exact h10

  have h_pr_threshold : ENNReal.ofReal (648 * (δ ^ (-c / 4)) ^ 3) * Nreal δ A < Nreal δ (ProductLikeIncidence.familySum Y) :=
    h_pr_cond.trans_le (h_scale_back.trans h_family_large)

  -- Branch constant absorption: a ≥ C * δ^{ε'/κ} implies various inequalities
  have ha_lower : a ≥ (2 * K) ^ (-1 / κ) * δ ^ (ε' / κ) := by
    have hCmu_eq : C_mu = K * δ ^ (-ε') := by simp [C_mu] <;> ring
    rw [ha_eq, hCmu_eq]
    have h1 : 2 * (K * δ ^ (-ε')) = (2 * K) * δ ^ (-ε') := by ring
    rw [h1]
    have h2 : ((2 * K) * δ ^ (-ε')) ^ (-1 / κ) = (2 * K) ^ (-1 / κ) * (δ ^ (-ε')) ^ (-1 / κ) :=
      Real.mul_rpow (by positivity) (by positivity)
    rw [h2]
    have h3 : (δ ^ (-ε')) ^ (-1 / κ) = δ ^ (ε' / κ) := by
      have h41 : (δ ^ (-ε')) ^ (-1 / κ) = δ ^ ((-ε') * (-1 / κ)) :=
        (Real.rpow_mul hδ_pos.le (-ε') (-1 / κ)).symm
      rw [h41]
      have h42 : (-ε') * (-1 / κ) = ε' / κ := by ring
      rw [h42]
    rw [h3] <;> ring
  have h_branch1 : a ≥ 81 * δ ^ (c / 24) := by
    have h1 : δ ^ (c / 24 - ε' / κ) ≤ (2 * K) ^ (-1 / κ) / 1000 := by
      have h2 : δ ≤ δ₄_branch := le_trans hδ_le_δ₀ hδ₀_le_branch
      have h_exp_pos : 0 < c / 24 - ε' / κ := h_exp_branch_pos
      have h3 : δ ^ (c / 24 - ε' / κ) ≤ δ₄_branch ^ (c / 24 - ε' / κ) :=
        Real.rpow_le_rpow (by linarith) h2 (by linarith)
      have h4 : δ₄_branch ^ (c / 24 - ε' / κ) = C_branch := by
        have h5 : ((1 / (c / 24 - ε' / κ)) * (c / 24 - ε' / κ)) = 1 := by
          have h_ne : (c / 24 - ε' / κ) ≠ 0 := h_exp_pos.ne'
          have h_inv : (1 / (c / 24 - ε' / κ)) = (c / 24 - ε' / κ)⁻¹ := by simp
          rw [h_inv]
          exact inv_mul_cancel₀ h_ne
        simp only [δ₄_branch]
        rw [← Real.rpow_mul (by positivity), h5, Real.rpow_one]
      rw [h4] at h3
      exact h3
    have h6 : a ≥ (2 * K) ^ (-1 / κ) * δ ^ (ε' / κ) := ha_lower
    have hC_pos : 0 < (2 * K) ^ (-1 / κ) := by positivity
    have h9 : (2 * K) ^ (-1 / κ) / 81 ≥ δ ^ (c / 24 - ε' / κ) := by
      have h91 : (2 * K) ^ (-1 / κ) / 81 ≥ (2 * K) ^ (-1 / κ) / 1000 := by
        gcongr <;> norm_num
      exact h1.trans h91
    have h7 : (2 * K) ^ (-1 / κ) * δ ^ (ε' / κ) ≥ 81 * δ ^ (c / 24) := by
      have h8 : (2 * K) ^ (-1 / κ) / 81 ≥ δ ^ (c / 24 - ε' / κ) := h9
      have h91 : δ ^ (c / 24 - ε' / κ) * δ ^ (ε' / κ) = δ ^ (c / 24) := by
        have h_exp : c / 24 - ε' / κ + ε' / κ = c / 24 := by ring
        rw [← Real.rpow_add hδ_pos, h_exp]
      calc (2 * K) ^ (-1 / κ) * δ ^ (ε' / κ)
        = 81 * ((2 * K) ^ (-1 / κ) / 81) * δ ^ (ε' / κ) := by ring
      _ ≥ 81 * (δ ^ (c / 24 - ε' / κ)) * δ ^ (ε' / κ) := by
        have h_pos : 0 < δ ^ (ε' / κ) := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h8 (by norm_num)) (by positivity)
      _ = 81 * δ ^ (c / 24) := by rw [← h91] <;> ring
    exact h7.trans h6
  have h_branch2 : a ≥ 243 * δ ^ (c / 12) := by
    have h1 : c / 12 - ε' / κ ≥ c / 24 - ε' / κ := by linarith [hc_pos]
    have h2 : δ ^ (c / 12 - ε' / κ) ≤ δ ^ (c / 24 - ε' / κ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos (by linarith) (by linarith)
    have h3 : δ ^ (c / 24 - ε' / κ) ≤ (2 * K) ^ (-1 / κ) / 1000 := by
      have h4 : δ ≤ δ₄_branch := le_trans hδ_le_δ₀ hδ₀_le_branch
      have h_exp_pos : 0 < c / 24 - ε' / κ := h_exp_branch_pos
      have h5 : δ ^ (c / 24 - ε' / κ) ≤ δ₄_branch ^ (c / 24 - ε' / κ) :=
        Real.rpow_le_rpow (by linarith) h4 (by linarith)
      have h6 : δ₄_branch ^ (c / 24 - ε' / κ) = C_branch := by
        have h7 : ((1 / (c / 24 - ε' / κ)) * (c / 24 - ε' / κ)) = 1 := by
          have h_ne : (c / 24 - ε' / κ) ≠ 0 := h_exp_pos.ne'
          have h_inv : (1 / (c / 24 - ε' / κ)) = (c / 24 - ε' / κ)⁻¹ := by simp
          rw [h_inv]
          exact inv_mul_cancel₀ h_ne
        simp only [δ₄_branch]
        rw [← Real.rpow_mul (by positivity), h7, Real.rpow_one]
      rw [h6] at h5
      exact h5
    have h4 : δ ^ (c / 12 - ε' / κ) ≤ (2 * K) ^ (-1 / κ) / 1000 := h2.trans h3
    have h5 : (2 * K) ^ (-1 / κ) / 243 ≥ (2 * K) ^ (-1 / κ) / 1000 := by gcongr <;> norm_num
    have h6 : (2 * K) ^ (-1 / κ) / 243 ≥ δ ^ (c / 12 - ε' / κ) := h4.trans h5
    have h7 : (2 * K) ^ (-1 / κ) * δ ^ (ε' / κ) ≥ 243 * δ ^ (c / 12) := by
      have h_eq : (2 * K) ^ (-1 / κ) * δ ^ (ε' / κ) =
          243 * (((2 * K) ^ (-1 / κ) / 243) * δ ^ (ε' / κ)) := by ring
      rw [h_eq]
      have h9 : ((2 * K) ^ (-1 / κ) / 243) * δ ^ (ε' / κ) ≥ δ ^ (c / 12) := by
        calc ((2 * K) ^ (-1 / κ) / 243) * δ ^ (ε' / κ)
          ≥ δ ^ (c / 12 - ε' / κ) * δ ^ (ε' / κ) := by gcongr
        _ = δ ^ (c / 12) := by
          have h_exp : c / 12 - ε' / κ + ε' / κ = c / 12 := by ring
          rw [← Real.rpow_add hδ_pos, h_exp]
      gcongr
    exact h7.trans ha_lower
  have h_branch3 : a ≥ 27 * δ ^ (c / 6) := by
    have h1 : c / 6 - ε' / κ ≥ c / 24 - ε' / κ := by linarith [hc_pos]
    have h2 : δ ^ (c / 6 - ε' / κ) ≤ δ ^ (c / 24 - ε' / κ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos (by linarith) (by linarith)
    have h3 : δ ^ (c / 24 - ε' / κ) ≤ (2 * K) ^ (-1 / κ) / 1000 := by
      have h4 : δ ≤ δ₄_branch := le_trans hδ_le_δ₀ hδ₀_le_branch
      have h_exp_pos : 0 < c / 24 - ε' / κ := h_exp_branch_pos
      have h5 : δ ^ (c / 24 - ε' / κ) ≤ δ₄_branch ^ (c / 24 - ε' / κ) :=
        Real.rpow_le_rpow (by linarith) h4 (by linarith)
      have h6 : δ₄_branch ^ (c / 24 - ε' / κ) = C_branch := by
        have h7 : ((1 / (c / 24 - ε' / κ)) * (c / 24 - ε' / κ)) = 1 := by
          have h_ne : (c / 24 - ε' / κ) ≠ 0 := h_exp_pos.ne'
          have h_inv : (1 / (c / 24 - ε' / κ)) = (c / 24 - ε' / κ)⁻¹ := by simp
          rw [h_inv]
          exact inv_mul_cancel₀ h_ne
        simp only [δ₄_branch]
        rw [← Real.rpow_mul (by positivity), h7, Real.rpow_one]
      rw [h6] at h5
      exact h5
    have h4 : (2 * K) ^ (-1 / κ) / 27 ≥ (2 * K) ^ (-1 / κ) / 1000 := by gcongr <;> norm_num
    have h5 : (2 * K) ^ (-1 / κ) / 27 ≥ δ ^ (c / 6 - ε' / κ) := (h2.trans h3).trans h4
    have h6 : (2 * K) ^ (-1 / κ) * δ ^ (ε' / κ) ≥ 27 * δ ^ (c / 6) := by
      have h_eq : (2 * K) ^ (-1 / κ) * δ ^ (ε' / κ) =
          27 * (((2 * K) ^ (-1 / κ) / 27) * δ ^ (ε' / κ)) := by ring
      rw [h_eq]
      have h8 : ((2 * K) ^ (-1 / κ) / 27) * δ ^ (ε' / κ) ≥ δ ^ (c / 6) := by
        calc ((2 * K) ^ (-1 / κ) / 27) * δ ^ (ε' / κ)
          ≥ δ ^ (c / 6 - ε' / κ) * δ ^ (ε' / κ) := by gcongr
        _ = δ ^ (c / 6) := by
          have h_exp : c / 6 - ε' / κ + ε' / κ = c / 6 := by ring
          rw [← Real.rpow_add hδ_pos, h_exp]
      gcongr
    exact h6.trans ha_lower

  -- N(x·A) ≥ (a/3) * N(A)
  have h_z_ge_zero : 0 ≤ z := (hν_supp hz_supp).1
  have h_y_nonneg : 0 ≤ y := mul_nonneg hr₀_pos.le h_z_ge_zero
  have ha_le_x : a ≤ x := hx0_ge_a.trans (le_add_of_nonneg_right h_y_nonneg)
  have hNxA_lower : Nreal δ (scaleSet x A) ≥ ENNReal.ofReal (a / 3) * Nreal δ A :=
    scale_lower_bound_helper δ x a A hδ_pos hx_pos hx_le_one ha_le_x hA_bdd

  -- N(y·A) ≤ 3 * N(A)
  have hNyA_upper : Nreal δ (scaleSet y A) ≤ 3 * Nreal δ A :=
    scale_upper_bound_helper δ y A hδ_pos hy_pos hy_le_one hA_bdd

  -- Three-case PR
  let β : ENNReal := ENNReal.ofReal ((1 / 3 : ℝ) * δ ^ (-c / 8))
  have hβ2 : 9 * β * β = α := by
    simp only [β, α]
    exact beta_squared_helper δ c hδ_pos

  have hN_eq : ∀ (S : Set ℝ), Nreal δ S = ProductLikeIncidence.Nreal' δ S := by
    intro S
    dsimp only [Nreal, ProductLikeIncidence.Nreal']
    <;> congr

  by_cases h1 : Nreal δ AxA ≤ α * Nreal δ A
  · by_cases h2 : Nreal δ AAA ≤ α * Nreal δ A
    · by_cases h3 : Nreal δ Amx0A ≤ α * Nreal δ A
      · -- All three bounded: PR gives contradiction
        have h1' : ProductLikeIncidence.Nreal' δ AxA ≤ α * ProductLikeIncidence.Nreal' δ A := by
          rw [← hN_eq AxA, ← hN_eq A]; exact h1
        have h2' : ProductLikeIncidence.Nreal' δ AAA ≤ α * ProductLikeIncidence.Nreal' δ A := by
          rw [← hN_eq AAA, ← hN_eq A]; exact h2
        have h3' : ProductLikeIncidence.Nreal' δ Amx0A ≤ α * ProductLikeIncidence.Nreal' δ A := by
          rw [← hN_eq Amx0A, ← hN_eq A]; exact h3
        have hY2_eq : Set.image2 (· + ·) A (Y 2) = Amx0A := by
          ext z; simp [Y, Amx0A, scaleSet, Set.image2] <;> constructor <;> rintro ⟨a, ha, b, hb, rfl⟩ <;> exact ⟨a, ha, b, hb, by ring⟩
        have h_hyp : ∀ i, ProductLikeIncidence.Nreal' δ (Set.image2 (· + ·) A (Y i)) ≤
            ENNReal.ofReal (δ ^ (-c / 4)) * ProductLikeIncidence.Nreal' δ A := by
          intro i
          fin_cases i
          · simpa [Y, AAA] using h2'
          · simpa [Y, AxA] using h1'
          · rw [hY2_eq]; exact h3'
        have h5 := ProductLikeIncidence.discretized_multiset_pr_general hδ_pos (by norm_num) hA_bdd hY_bdd hA_nonempty
          (α := fun _ => δ ^ (-c / 4)) (by intro i; positivity) h_hyp
        have h_sum : (∑ i : Fin 3, δ ^ (-c / 4)) = 3 * δ ^ (-c / 4) := by
          simp [Finset.sum_const, Finset.card_fin] <;> ring
        have h_eq : (↑3 * (2 * ∑ i : Fin 3, δ ^ (-c / 4)) ^ 3) = 648 * (δ ^ (-c / 4)) ^ 3 := by
          rw [h_sum] <;> ring
        have h5' : ProductLikeIncidence.Nreal' δ (ProductLikeIncidence.familySum Y) ≤
            ENNReal.ofReal (648 * (δ ^ (-c / 4)) ^ 3) * ProductLikeIncidence.Nreal' δ A := by
          have h6 : ENNReal.ofReal (↑3 * (2 * ∑ i : Fin 3, δ ^ (-c / 4)) ^ 3) =
              ENNReal.ofReal (648 * (δ ^ (-c / 4)) ^ 3) := by
            rw [h_eq]
          calc ProductLikeIncidence.Nreal' δ (ProductLikeIncidence.familySum Y)
            ≤ ENNReal.ofReal (↑3 * (2 * ∑ i : Fin 3, δ ^ (-c / 4)) ^ 3) * ProductLikeIncidence.Nreal' δ A := h5
          _ = ENNReal.ofReal (648 * (δ ^ (-c / 4)) ^ 3) * ProductLikeIncidence.Nreal' δ A := by
            rw [h6]
        have h4 : Nreal δ (ProductLikeIncidence.familySum Y) ≤ ENNReal.ofReal (648 * (δ ^ (-c / 4)) ^ 3) * Nreal δ A := by
          rw [hN_eq (ProductLikeIncidence.familySum Y), hN_eq A]
          exact h5'
        exact False.elim (not_le.mpr h_pr_threshold h4)
      · -- Case 2: N(Amx0A) > α * N(A), use cor_sum_to_diff to return x₀
        have h4 : Nreal δ Amx0A > α * Nreal δ A := by exact lt_of_not_ge h3
        -- N(x₀A) ≥ (x₀/3) * N(A) ≥ (a/3) * N(A)
        have hNx0A_lower : Nreal δ (scaleSet x₀ A) ≥ ENNReal.ofReal (a / 3) * Nreal δ A :=
          scale_lower_bound_helper δ x₀ a A hδ_pos hx0_pos hx0_le_one hx0_ge_a hA_bdd
        have hx0A_nonempty : (scaleSet x₀ A).Nonempty := by
          rcases hA_nonempty with ⟨a_elem, ha_elem⟩
          exact ⟨x₀ * a_elem, ⟨a_elem, ha_elem, rfl⟩⟩
        -- cor_sum_to_diff: N(A-x₀A) * N(A) * N(x₀A) ≤ 81 * N(A+x₀A)^3
        have h5 : Nreal δ Amx0A * Nreal δ A * Nreal δ (scaleSet x₀ A) ≤
            81 * Nreal δ Ax0A * Nreal δ Ax0A * Nreal δ Ax0A := by
          have h5' := ProductLikeIncidence.ruzsa_cor_sum_to_diff hδ_pos hA_bdd (scaleSet_bounded hA_bdd) hA_nonempty hx0A_nonempty
          have h_goal : Nreal δ Amx0A * Nreal δ A * Nreal δ (scaleSet x₀ A) ≤ 81 * (Nreal δ Ax0A) ^ 3 := by
            rw [hN_eq Amx0A, hN_eq A, hN_eq (scaleSet x₀ A), hN_eq Ax0A]
            exact h5'
          have h_pow : 81 * (Nreal δ Ax0A) ^ 3 = 81 * Nreal δ Ax0A * Nreal δ Ax0A * Nreal δ Ax0A := by
            simp [pow_succ] <;> ring
          rw [h_pow] at h_goal
          exact h_goal
        -- Combine: α * (a/3) * N(A)^3 < 81 * N(Ax0A)^3
        have h61 : α * Nreal δ A * Nreal δ A * (ENNReal.ofReal (a / 3) * Nreal δ A) <
            Nreal δ Amx0A * Nreal δ A * Nreal δ (scaleSet x₀ A) := by
          calc α * Nreal δ A * Nreal δ A * (ENNReal.ofReal (a / 3) * Nreal δ A)
            = (α * Nreal δ A) * (Nreal δ A * (ENNReal.ofReal (a / 3) * Nreal δ A)) := by ring
          _ ≤ (α * Nreal δ A) * (Nreal δ A * Nreal δ (scaleSet x₀ A)) := by gcongr
          _ < Nreal δ Amx0A * (Nreal δ A * Nreal δ (scaleSet x₀ A)) := by
            have h_b : Nreal δ A * Nreal δ (scaleSet x₀ A) ≠ 0 := by
              have h2 : Nreal δ (scaleSet x₀ A) ≠ 0 := by
                have h_nonempty : (realLineCopy (scaleSet x₀ A)).Nonempty :=
                  SetDiscretizationBridge.realLineCopy_nonempty_iff.mpr hx0A_nonempty
                have h3 : 0 < dyadicCoveringNumber δ (realLineCopy (scaleSet x₀ A)) :=
                  robust_projection.dyadic_covering_number_pos hδ_pos h_nonempty
                have h4' : Nreal δ (scaleSet x₀ A) = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy (scaleSet x₀ A))) := by rfl
                rw [h4']
                have h5 : 0 < ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy (scaleSet x₀ A))) := by
                  exact_mod_cast h3
                exact h5.ne'
              exact mul_ne_zero hNA_ne_zero h2
            have h_b_top : Nreal δ A * Nreal δ (scaleSet x₀ A) ≠ ⊤ :=
              mul_ne_top (Nreal_ne_top hδ_pos hA_bdd) (Nreal_ne_top hδ_pos (scaleSet_bounded hA_bdd))
            have h_iff : (Nreal δ A * Nreal δ (scaleSet x₀ A)) * (α * Nreal δ A) < (Nreal δ A * Nreal δ (scaleSet x₀ A)) * Nreal δ Amx0A :=
              (ENNReal.mul_lt_mul_iff_right h_b h_b_top).mpr h4
            have h_comm1 : (α * Nreal δ A) * (Nreal δ A * Nreal δ (scaleSet x₀ A)) = (Nreal δ A * Nreal δ (scaleSet x₀ A)) * (α * Nreal δ A) := by rw [mul_comm]
            have h_comm2 : Nreal δ Amx0A * (Nreal δ A * Nreal δ (scaleSet x₀ A)) = (Nreal δ A * Nreal δ (scaleSet x₀ A)) * Nreal δ Amx0A := by rw [mul_comm]
            rw [h_comm1, h_comm2]
            exact h_iff
          _ = Nreal δ Amx0A * Nreal δ A * Nreal δ (scaleSet x₀ A) := by ring
        have h6 : α * Nreal δ A * Nreal δ A * (ENNReal.ofReal (a / 3) * Nreal δ A) <
            81 * Nreal δ Ax0A * Nreal δ Ax0A * Nreal δ Ax0A :=
          h61.trans_le h5
        -- From h_branch2: a ≥ 243 * δ^(c/12) ≥ 243 * δ^(c/8)
        -- So α * (a/3) ≥ 81 * δ^(-c/8) = 81 * δ^(-3c')
        have h7 : α * ENNReal.ofReal (a / 3) ≥ 81 * ENNReal.ofReal (δ ^ (-3 * c')) := by
          have h8 : a ≥ 243 * δ ^ (c / 12) := h_branch2
          have h9 : δ ^ (c / 12) ≥ δ ^ (c / 8) := by
            apply Real.rpow_le_rpow_of_exponent_ge <;> linarith
          have h10 : a ≥ 243 * δ ^ (c / 8) := by linarith
          have h11 : (a / 3 : ℝ) ≥ 81 * δ ^ (c / 8) := by linarith
          have h12 : δ ^ (-c / 4) * (a / 3) ≥ 81 * δ ^ (-c / 8) := by
            have h_exp : δ ^ (-c / 4) * δ ^ (c / 8) = δ ^ (-c / 8) := by
              have h_e : -c / 4 + c / 8 = -c / 8 := by ring
              rw [← Real.rpow_add hδ_pos, h_e]
            calc δ ^ (-c / 4) * (a / 3)
              ≥ δ ^ (-c / 4) * (81 * δ ^ (c / 8)) := by gcongr
            _ = 81 * (δ ^ (-c / 4) * δ ^ (c / 8)) := by ring
            _ = 81 * δ ^ (-c / 8) := by rw [h_exp]
          have h13 : δ ^ (-c / 8) = δ ^ (-3 * c') := by
            have h14 : c' = c / 24 := by simp [hc'_def]
            have h_exp : -c / 8 = -3 * c' := by
              rw [h14] <;> ring
            rw [h_exp]
          calc α * ENNReal.ofReal (a / 3)
            = ENNReal.ofReal (δ ^ (-c / 4)) * ENNReal.ofReal (a / 3) := by simp [α]
          _ = ENNReal.ofReal (δ ^ (-c / 4) * (a / 3)) := by rw [← ENNReal.ofReal_mul (by positivity)]
          _ ≥ ENNReal.ofReal (81 * δ ^ (-c / 8)) := ENNReal.ofReal_le_ofReal h12
          _ = 81 * ENNReal.ofReal (δ ^ (-c / 8)) := by
            have h_of1 : ENNReal.ofReal (81 * δ ^ (-c / 8)) = ENNReal.ofReal (81 : ℝ) * ENNReal.ofReal (δ ^ (-c / 8)) := by
              rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 81 by norm_num)]
            have h_of2 : ENNReal.ofReal (81 : ℝ) = (81 : ENNReal) := by simp
            rw [h_of1, h_of2]
          _ = 81 * ENNReal.ofReal (δ ^ (-3 * c')) := by rw [h13]
        -- Contradiction if N(Ax0A) < δ^(-c') * N(A)
        have h15 : Nreal δ Ax0A ≥ ENNReal.ofReal (δ ^ (-c')) * Nreal δ A := by
          by_contra h16
          set b : ENNReal := ENNReal.ofReal (δ ^ (-c')) * Nreal δ A with hb_def
          have h17 : Nreal δ Ax0A < b := by exact lt_of_not_ge h16
          have h18 : (81 : ENNReal) * Nreal δ Ax0A * Nreal δ Ax0A * Nreal δ Ax0A <
              (81 : ENNReal) * b * b * b := ennreal_cube_strict_mono h17
          have h_pos1 : 0 ≤ δ ^ (-c') := by positivity
          have h_real : (δ ^ (-c')) * (δ ^ (-c')) * (δ ^ (-c')) = δ ^ (-3 * c') := by
            have h1 : (δ ^ (-c')) * (δ ^ (-c')) = δ ^ (-2 * c') := by
              have h_e1 : -c' + -c' = -2 * c' := by ring
              rw [← Real.rpow_add hδ_pos, h_e1]
            rw [h1]
            have h_e2 : -2 * c' + -c' = -3 * c' := by ring
            rw [← Real.rpow_add hδ_pos, h_e2]
          have h_a3 : ENNReal.ofReal (δ ^ (-c')) * ENNReal.ofReal (δ ^ (-c')) * ENNReal.ofReal (δ ^ (-c')) =
              ENNReal.ofReal (δ ^ (-3 * c')) := by
            rw [ofReal_mul3 h_pos1 h_pos1, h_real]
          have h_b3 : b * b * b =
              ENNReal.ofReal (δ ^ (-3 * c')) * Nreal δ A * Nreal δ A * Nreal δ A := by
            simp only [hb_def]
            have h_assoc : (ENNReal.ofReal (δ ^ (-c')) * Nreal δ A) * (ENNReal.ofReal (δ ^ (-c')) * Nreal δ A) * (ENNReal.ofReal (δ ^ (-c')) * Nreal δ A) =
                (ENNReal.ofReal (δ ^ (-c')) * ENNReal.ofReal (δ ^ (-c')) * ENNReal.ofReal (δ ^ (-c'))) * (Nreal δ A * Nreal δ A * Nreal δ A) := by
              simp [mul_assoc, mul_comm, mul_left_comm]
            rw [h_assoc, h_a3]
            <;> simp [mul_assoc, mul_comm, mul_left_comm]
          have h19 : (81 : ENNReal) * b * b * b =
              (81 : ENNReal) * (ENNReal.ofReal (δ ^ (-3 * c')) * Nreal δ A * Nreal δ A * Nreal δ A) := by
            have h_assoc2 : (81 : ENNReal) * b * b * b = (81 : ENNReal) * (b * b * b) := by
              simp [mul_assoc]
            rw [h_assoc2, h_b3]
          rw [h19] at h18
          have h20 : α * Nreal δ A * Nreal δ A * (ENNReal.ofReal (a / 3) * Nreal δ A) =
              α * ENNReal.ofReal (a / 3) * (Nreal δ A * Nreal δ A * Nreal δ A) := by
            simp [mul_assoc, mul_comm, mul_left_comm] <;> ac_rfl
          rw [h20] at h6
          have h21 : α * ENNReal.ofReal (a / 3) * (Nreal δ A * Nreal δ A * Nreal δ A) ≥
              (81 : ENNReal) * (ENNReal.ofReal (δ ^ (-3 * c')) * Nreal δ A * Nreal δ A * Nreal δ A) := by
            have h211 : (81 : ENNReal) * (ENNReal.ofReal (δ ^ (-3 * c')) * Nreal δ A * Nreal δ A * Nreal δ A) =
                ((81 : ENNReal) * ENNReal.ofReal (δ ^ (-3 * c'))) * (Nreal δ A * Nreal δ A * Nreal δ A) := by
              simp [mul_assoc]
            rw [h211]
            exact mul_le_mul_of_nonneg_right h7 (by positivity)
          have h_contra : α * ENNReal.ofReal (a / 3) * (Nreal δ A * Nreal δ A * Nreal δ A) <
              (81 : ENNReal) * (ENNReal.ofReal (δ ^ (-3 * c')) * Nreal δ A * Nreal δ A * Nreal δ A) :=
            h6.trans h18
          exact not_le.mpr h_contra h21
        have hAx0A_eq : Ax0A = Set.image2 (fun a b => a + x₀ * b) A A := by
          ext z
          simp [Ax0A, scaleSet]
          <;> constructor
          · rintro ⟨a, ha, c, ⟨b, hb, rfl⟩, rfl⟩
            exact ⟨a, ha, b, hb, rfl⟩
          · rintro ⟨a, ha, b, hb, rfl⟩
            exact ⟨a, ha, x₀ * b, ⟨b, hb, rfl⟩, rfl⟩
        rw [hAx0A_eq] at h15
        have hx0_in_mu_support : x₀ ∈ μ.support := hμ₁_supp_subset hx0_in_support
        exact ⟨x₀, hx0_in_mu_support, h15⟩
    · -- Case 3: N(AAA) > α * N(A)
      have h4 : Nreal δ AAA > α * Nreal δ A := by exact lt_of_not_ge h2
      have hxA_nonempty : (scaleSet x A).Nonempty := by
        rcases hA_nonempty with ⟨a, ha⟩
        exact ⟨x * a, ⟨a, ha, rfl⟩⟩
      have h5 : Nreal δ AAA * Nreal δ (scaleSet x A) ≤ 9 * Nreal δ AxA * Nreal δ AxA := by
        have h5' := ProductLikeIncidence.OSW.corollary2_3 hδ_pos hA_bdd (scaleSet_bounded hA_bdd) hxA_nonempty
        rw [hN_eq AAA, hN_eq (scaleSet x A), hN_eq AxA]
        exact h5'
      have h6 : Nreal δ AxA * Nreal δ AxA ≥
          ENNReal.ofReal (δ ^ (-2 * c')) * Nreal δ A * Nreal δ A := by
        have h71 : (1 / 9 : ENNReal) * (Nreal δ AAA * Nreal δ (scaleSet x A)) ≤ (1 / 9 : ENNReal) * (9 * Nreal δ AxA * Nreal δ AxA) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
        have h72 : (1 / 9 : ENNReal) * (9 * Nreal δ AxA * Nreal δ AxA) = Nreal δ AxA * Nreal δ AxA := by
          have h9_pos : (0 : ENNReal) < (9 : ENNReal) := by norm_num
          have h9_ne_top : (9 : ENNReal) ≠ ⊤ := by simp
          have h_div : (1 / 9 : ENNReal) = (9 : ENNReal)⁻¹ := by
            simp [one_div]
          have h : (1 / 9 : ENNReal) * (9 : ENNReal) = 1 := by
            rw [h_div]
            exact ENNReal.inv_mul_cancel h9_pos.ne' h9_ne_top
          have h_assoc1 : (9 : ENNReal) * Nreal δ AxA * Nreal δ AxA = (9 : ENNReal) * (Nreal δ AxA * Nreal δ AxA) := by
            rw [mul_assoc]
          have h_assoc2 : (1 / 9 : ENNReal) * ((9 : ENNReal) * (Nreal δ AxA * Nreal δ AxA)) =
              ((1 / 9 : ENNReal) * (9 : ENNReal)) * (Nreal δ AxA * Nreal δ AxA) := by
            rw [← mul_assoc]
          rw [h_assoc1, h_assoc2, h] <;> simp
        have h73 : (1 / 9 : ENNReal) * Nreal δ AAA * Nreal δ (scaleSet x A) = (1 / 9 : ENNReal) * (Nreal δ AAA * Nreal δ (scaleSet x A)) := by
          simp [mul_assoc]
        have h7 : Nreal δ AxA * Nreal δ AxA ≥ (1 / 9 : ENNReal) * Nreal δ AAA * Nreal δ (scaleSet x A) := by
          rw [h73]
          rw [h72] at h71
          exact h71
        have h81 : Nreal δ AAA ≥ α * Nreal δ A := le_of_lt h4
        have h84 : (1 / 9 : ENNReal) * Nreal δ AAA ≥ (1 / 9 : ENNReal) * (α * Nreal δ A) :=
          mul_le_mul_of_nonneg_left h81 (by positivity)
        have h8 : (1 / 9 : ENNReal) * Nreal δ AAA * Nreal δ (scaleSet x A) ≥
            (1 / 9 : ENNReal) * α * Nreal δ A * (ENNReal.ofReal (a / 3) * Nreal δ A) := by
          have h_goal : ((1 / 9 : ENNReal) * Nreal δ AAA) * Nreal δ (scaleSet x A) ≥
              (((1 / 9 : ENNReal) * α) * Nreal δ A) * (ENNReal.ofReal (a / 3) * Nreal δ A) := by
            have h85 : (1 / 9 : ENNReal) * Nreal δ AAA ≥ ((1 / 9 : ENNReal) * α) * Nreal δ A := by
              simpa [mul_assoc] using h84
            exact mul_le_mul h85 hNxA_lower (by positivity) (by positivity)
          simpa [mul_assoc] using h_goal
        have h_pos1 : 0 ≤ (1 / 9 : ℝ) := by norm_num
        have h_pos2 : 0 ≤ δ ^ (-c / 4) := by positivity
        have h_pos3 : 0 ≤ a / 3 := by positivity
        have h9 : (1 / 9 : ENNReal) * α * Nreal δ A * (ENNReal.ofReal (a / 3) * Nreal δ A) =
            ENNReal.ofReal (a / 27 * δ ^ (-c / 4)) * Nreal δ A * Nreal δ A := by
          simp only [α]
          have h_eq1 : (1 / 9 : ENNReal) = ENNReal.ofReal (1 / 9 : ℝ) := by simp
          rw [h_eq1]
          have h_assoc : ENNReal.ofReal (1 / 9 : ℝ) * ENNReal.ofReal (δ ^ (-c / 4)) * Nreal δ A * (ENNReal.ofReal (a / 3) * Nreal δ A) =
              (ENNReal.ofReal (1 / 9 : ℝ) * ENNReal.ofReal (δ ^ (-c / 4)) * ENNReal.ofReal (a / 3)) * (Nreal δ A * Nreal δ A) := by
            simp [mul_assoc, mul_comm, mul_left_comm]
          rw [h_assoc]
          have h_mul : ENNReal.ofReal (1 / 9 : ℝ) * ENNReal.ofReal (δ ^ (-c / 4)) * ENNReal.ofReal (a / 3) =
              ENNReal.ofReal ((1 / 9 : ℝ) * δ ^ (-c / 4) * (a / 3)) := by
            have h_m1 : ENNReal.ofReal (1 / 9 : ℝ) * ENNReal.ofReal (δ ^ (-c / 4)) =
                ENNReal.ofReal ((1 / 9 : ℝ) * δ ^ (-c / 4)) := ofReal_mul' h_pos1
            rw [h_m1]
            exact ofReal_mul' (show (0 : ℝ) ≤ (1 / 9 : ℝ) * δ ^ (-c / 4) by positivity)
          rw [h_mul]
          have h_eq2 : (1 / 9 : ℝ) * δ ^ (-c / 4) * (a / 3) = a / 27 * δ ^ (-c / 4) := by ring
          rw [h_eq2]
          <;> simp [mul_assoc]
        have h10 : a / 27 * δ ^ (-c / 4) ≥ δ ^ (-2 * c') := by
          have h11 : c' = c / 24 := by simp [hc'_def]
          have h12 : a ≥ 27 * δ ^ (c / 6) := h_branch3
          have h131 : a / 27 ≥ δ ^ (c / 6) := by linarith
          have h132 : 0 ≤ δ ^ (-c / 4) := by positivity
          have h13 : a / 27 * δ ^ (-c / 4) ≥ δ ^ (c / 6) * δ ^ (-c / 4) :=
            mul_le_mul_of_nonneg_right h131 h132
          have h14 : δ ^ (c / 6) * δ ^ (-c / 4) = δ ^ (-c / 12) := by
            have h_exp : c / 6 + (-c / 4) = -c / 12 := by ring
            rw [← Real.rpow_add hδ_pos, h_exp]
          have h15 : -2 * c' = -c / 12 := by
            rw [h11] <;> ring
          have h16 : δ ^ (-2 * c') = δ ^ (-c / 12) := by rw [h15]
          rw [h16]
          rw [h14] at h13
          exact h13
        have h15 : ENNReal.ofReal (a / 27 * δ ^ (-c / 4)) ≥ ENNReal.ofReal (δ ^ (-2 * c')) :=
          ENNReal.ofReal_le_ofReal h10
        have h17 : (1 / 9 : ENNReal) * α * Nreal δ A * (ENNReal.ofReal (a / 3) * Nreal δ A) ≥
            ENNReal.ofReal (δ ^ (-2 * c')) * Nreal δ A * Nreal δ A := by
          rw [h9]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h15 (by positivity)) (by positivity)
        calc Nreal δ AxA * Nreal δ AxA
          ≥ (1 / 9 : ENNReal) * Nreal δ AAA * Nreal δ (scaleSet x A) := h7
        _ ≥ (1 / 9 : ENNReal) * α * Nreal δ A * (ENNReal.ofReal (a / 3) * Nreal δ A) := h8
        _ ≥ ENNReal.ofReal (δ ^ (-2 * c')) * Nreal δ A * Nreal δ A := h17
      have h16 : Nreal δ AxA ≥ ENNReal.ofReal (δ ^ (-c')) * Nreal δ A := by
        by_contra h17
        have h18 : Nreal δ AxA < ENNReal.ofReal (δ ^ (-c')) * Nreal δ A := by exact lt_of_not_ge h17
        have h19 : Nreal δ AxA * Nreal δ AxA <
            (ENNReal.ofReal (δ ^ (-c')) * Nreal δ A) * (ENNReal.ofReal (δ ^ (-c')) * Nreal δ A) :=
          ENNReal.mul_lt_mul h18 h18
        have h_pos1 : 0 ≤ δ ^ (-c') := by positivity
        have h20 : (ENNReal.ofReal (δ ^ (-c')) * Nreal δ A) * (ENNReal.ofReal (δ ^ (-c')) * Nreal δ A) =
            ENNReal.ofReal (δ ^ (-2 * c')) * Nreal δ A * Nreal δ A := by
          have h_assoc : (ENNReal.ofReal (δ ^ (-c')) * Nreal δ A) * (ENNReal.ofReal (δ ^ (-c')) * Nreal δ A) =
              (ENNReal.ofReal (δ ^ (-c')) * ENNReal.ofReal (δ ^ (-c'))) * (Nreal δ A * Nreal δ A) := by
            simp [mul_assoc, mul_comm, mul_left_comm]
          rw [h_assoc]
          have h_a2 : ENNReal.ofReal (δ ^ (-c')) * ENNReal.ofReal (δ ^ (-c')) =
              ENNReal.ofReal ((δ ^ (-c')) * (δ ^ (-c'))) := ofReal_mul' h_pos1
          rw [h_a2]
          have h_real2 : (δ ^ (-c')) * (δ ^ (-c')) = δ ^ (-2 * c') := by
            have h_exp : (-c') + (-c') = -2 * c' := by ring
            rw [← Real.rpow_add hδ_pos, h_exp]
          rw [h_real2]
          <;> simp [mul_assoc]
        rw [h20] at h19
        exact not_le.mpr h19 h6
      have hAxA_eq : AxA = Set.image2 (fun a b => a + x * b) A A := by
        ext z
        simp [AxA, scaleSet]
        <;> constructor
        · rintro ⟨a, ha, c, ⟨b, hb, rfl⟩, rfl⟩
          exact ⟨a, ha, b, hb, rfl⟩
        · rintro ⟨a, ha, b, hb, rfl⟩
          exact ⟨a, ha, x * b, ⟨b, hb, rfl⟩, rfl⟩
      rw [hAxA_eq] at h16
      exact ⟨x, h_x_in_supp, h16⟩
  · -- Case 1: N(AxA) > α * N(A) ≥ δ^{-c'} * N(A)
    have h4 : Nreal δ AxA > α * Nreal δ A := by exact lt_of_not_ge h1
    have h5 : α ≥ ENNReal.ofReal (δ ^ (-c')) := by
      have h6 : c / 4 ≥ c' := by
        simp [hc'_def] <;> linarith
      have h7 : δ ^ (-c / 4) ≥ δ ^ (-c') := by
        apply Real.rpow_le_rpow_of_exponent_ge <;> linarith
      exact ENNReal.ofReal_le_ofReal h7
    have h81 : α * Nreal δ A ≥ ENNReal.ofReal (δ ^ (-c')) * Nreal δ A :=
      mul_le_mul_of_nonneg_right h5 (by positivity)
    have h8 : Nreal δ AxA ≥ ENNReal.ofReal (δ ^ (-c')) * Nreal δ A :=
      le_trans h81 (le_of_lt h4)
    have hAxA_eq : AxA = Set.image2 (fun a b => a + x * b) A A := by
      ext z
      simp [AxA, scaleSet]
      <;> constructor
      · rintro ⟨a, ha, c, ⟨b, hb, rfl⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨a, ha, x * b, ⟨b, hb, rfl⟩, rfl⟩
    rw [hAxA_eq] at h8
    exact ⟨x, h_x_in_supp, h8⟩

end WeakTwoEndsSumProduct
