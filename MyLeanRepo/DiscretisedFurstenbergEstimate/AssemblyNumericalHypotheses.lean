module

/-
  Quantitative ε-budget absorption lemmas for A1→A10 assembly.

  Derives all purely numerical hypotheses from:
  - ε constraints: 12ε ≤ s, 504ε < t-s
  - Δ sufficiently small (constant + polylog absorption)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.EnergyBoundPlane
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.AffineLinePackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HCommonWiring
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

namespace DirecretisedFurstenbergEstimate.AssemblyNumerical

/-! ### Helper: exponential dominates polynomial -/

/-- For y ≥ 0 and n : ℕ, exp(y) ≥ (y/n)^n. -/
lemma exp_pow_bound {n : ℕ} {y : ℝ} (hy : 0 ≤ y) :
    (y / (n : ℝ)) ^ n ≤ Real.exp y := by
  by_cases hn : n = 0
  · simp [hn] <;> linarith [Real.exp_pos y]
  have h1 : 1 + y / (n : ℝ) ≤ Real.exp (y / (n : ℝ)) := by
    have h := Real.add_one_le_exp (y / (n : ℝ))
    linarith
  have h21 : ∀ (k : ℕ) (z : ℝ), (Real.exp z)^k = Real.exp ((k : ℝ) * z) := by
    intro k z
    induction k with
    | zero => simp
    | succ k ih =>
      calc (Real.exp z)^(k + 1)
        = (Real.exp z)^k * Real.exp z := by simp [pow_succ]
      _ = Real.exp ((k : ℝ) * z) * Real.exp z := by rw [ih]
      _ = Real.exp (((k : ℝ) * z) + z) := by rw [← Real.exp_add]
      _ = Real.exp (((k : ℝ) + 1) * z) := by ring_nf
      _ = Real.exp (((k + 1 : ℕ) : ℝ) * z) := by simp [Nat.cast_add] <;> ring
  have h2 : (Real.exp (y / (n : ℝ))) ^ n = Real.exp y := by
    rw [h21 n (y / (n : ℝ))]
    have h23 : (n : ℝ) * (y / (n : ℝ)) = y := by field_simp [hn] <;> ring
    rw [h23]
  have h3 : (y / (n : ℝ)) ^ n ≤ (1 + y / (n : ℝ)) ^ n := by
    gcongr <;> linarith
  calc (y / (n : ℝ)) ^ n
    ≤ (1 + y / (n : ℝ)) ^ n := h3
  _ ≤ (Real.exp (y / (n : ℝ))) ^ n := by gcongr
  _ = Real.exp y := h2

/-- For any C > 0, α > 0, n : ℕ, there exists X such that
    C * (x + 1)^n ≤ Real.exp (α * x) for all x ≥ X. -/
lemma polylog_absorb_exp (C α : ℝ) (n : ℕ) (hC : 0 < C) (hα : 0 < α) :
    ∃ X : ℝ, ∀ x : ℝ, x ≥ X → C * (x + 1)^n ≤ Real.exp (α * x) := by
  let m := n + 1
  let X : ℝ := max 1 (C * (2 : ℝ)^n * (m : ℝ)^m / α^m)
  use X
  intro x hx
  have hx1 : x ≥ 1 := by
    have h : X ≥ 1 := le_max_left _ _
    exact le_trans h hx
  have hxX : x ≥ C * (2 : ℝ)^n * (m : ℝ)^m / α^m := by
    have h : X ≥ _ := le_max_right _ _
    exact le_trans h hx
  have h4 : (α * x / (m : ℝ)) ^ m ≤ Real.exp (α * x) := by
    have h5 : 0 ≤ α * x := by positivity
    exact exp_pow_bound (y := α * x) (n := m) h5
  have h6 : (x + 1)^n ≤ (2 * x)^n := by
    have h7 : x + 1 ≤ 2 * x := by linarith
    gcongr <;> linarith
  have h8 : C * (x + 1)^n ≤ C * (2 * x)^n := by gcongr
  have h9 : C * (2 * x)^n ≤ (α * x / (m : ℝ)) ^ m := by
    have hdiv : (α * x / (m : ℝ)) ^ m = (α * x)^m / (m : ℝ)^m := by rw [div_pow]
    have h13 : 0 ≤ x := by linarith
    have h14 : C * (2 : ℝ)^n ≤ α^m / (m : ℝ)^m * x := by
      have h15 : x ≥ C * (2 : ℝ)^n * (m : ℝ)^m / α^m := hxX
      have h16 : 0 < α^m := by positivity
      calc C * (2 : ℝ)^n
        = (α^m / (m : ℝ)^m) * (C * (2 : ℝ)^n * (m : ℝ)^m / α^m) := by field_simp <;> ring
      _ ≤ (α^m / (m : ℝ)^m) * x := by gcongr
    have h_goal : C * (2 * x)^n ≤ (α * x)^m / (m : ℝ)^m := by
      have h17 : C * (2 * x)^n = C * (2 : ℝ)^n * x^n := by ring
      rw [h17]
      have h19 : (α * x)^m / (m : ℝ)^m = α^m / (m : ℝ)^m * x^m := by
        rw [mul_pow] <;> ring
      rw [h19]
      have h18 : x^m = x^n * x := by simp [m, pow_succ] <;> ring
      rw [h18]
      calc C * (2 : ℝ)^n * x^n
        ≤ (α^m / (m : ℝ)^m * x) * x^n := by gcongr
      _ = α^m / (m : ℝ)^m * (x^n * x) := by ring
    rw [hdiv]
    exact h_goal
  calc C * (x + 1)^n
    ≤ C * (2 * x)^n := h8
  _ ≤ (α * x / (m : ℝ)) ^ m := h9
  _ ≤ Real.exp (α * x) := h4

/-! ### Δ-scale absorption lemmas -/

/-- Constant absorption: C ≤ Δ^{-α} for 0 < Δ sufficiently small. -/
lemma const_absorb_delta (C α : ℝ) (hC : 0 < C) (hα : 0 < α) :
    ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ, 0 < Δ → Δ < Δ₀ → C ≤ Real.rpow Δ (-α) := by
  let Δ₀ : ℝ := C ^ (-(1 / α))
  have hΔ₀_pos : 0 < Δ₀ := by positivity
  use Δ₀, hΔ₀_pos
  intro Δ hΔ_pos hΔ_lt
  have h5 : (C ^ (-(1 / α))) ^ α = 1 / C := by
    have h6 : (C ^ (-(1 / α))) ^ α = C ^ ((-(1 / α)) * α) := by
      rw [← Real.rpow_mul (by linarith)] <;> ring
    rw [h6]
    have h7 : (-(1 / α)) * α = -1 := by field_simp [hα.ne'] <;> ring
    rw [h7]
    have h8 : C ^ (-1 : ℝ) = 1 / C := by
      rw [Real.rpow_neg (by linarith)] <;> simp
    exact h8
  have h3 : Δ ^ α < 1 / C := by
    have h4 : Δ ^ α < (C ^ (-(1 / α))) ^ α := Real.rpow_lt_rpow (by linarith) hΔ_lt hα
    rw [h5] at h4
    exact h4
  have h_pos : 0 < Δ ^ α := Real.rpow_pos_of_pos hΔ_pos α
  have h9 : (Δ ^ α)⁻¹ > C := by
    have h10 : (Δ ^ α)⁻¹ > (1 / C)⁻¹ := by gcongr
    have h11 : (1 / C)⁻¹ = C := by field_simp [hC.ne']
    rw [h11] at h10
    exact h10
  have h7 : Real.rpow Δ (-α) = (Real.rpow Δ α)⁻¹ := by
    have h71 := Real.rpow_neg hΔ_pos.le α
    exact h71
  rw [h7]
  exact le_of_lt h9

/-- Polylog absorption: C * (log(1/Δ) + 1)^n ≤ Δ^{-α} for Δ small enough. -/
lemma polylog_absorb_delta (C α : ℝ) (n : ℕ) (hC : 0 < C) (hα : 0 < α) :
    ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ, 0 < Δ → Δ < Δ₀ →
      C * (Real.log (1 / Δ) + 1)^n ≤ Real.rpow Δ (-α) := by
  rcases polylog_absorb_exp C α n hC hα with ⟨X, hX⟩
  let Δ₀ : ℝ := Real.exp (-X)
  have hΔ₀_pos : 0 < Δ₀ := by positivity
  use Δ₀, hΔ₀_pos
  intro Δ hΔ_pos hΔ_lt
  have h4 : Real.exp (-X) * Real.exp X = 1 := by
    have h5 : Real.exp (-X) * Real.exp X = Real.exp ((-X) + X) := by
      exact Eq.symm (Real.exp_add (-X) X)
    rw [h5]
    have h6 : (-X) + X = 0 := by ring
    rw [h6, Real.exp_zero]
  have h6 : 1 / Real.exp (-X) = Real.exp X := by
    apply (div_eq_iff (by positivity)).mpr
    have h4' : Real.exp X * Real.exp (-X) = 1 := by
      rw [mul_comm]
      exact h4
    exact h4'.symm
  have h3 : 1 / Δ > Real.exp X := by
    have h7 : 1 / Δ > 1 / Real.exp (-X) := one_div_lt_one_div_of_lt (by positivity) hΔ_lt
    rw [h6] at h7
    exact h7
  have h2 : Real.log (1 / Δ) > X := by
    have h8 : Real.log (1 / Δ) > Real.log (Real.exp X) := Real.log_lt_log (by positivity) h3
    rw [Real.log_exp] at h8
    exact h8
  have h10 : Real.rpow Δ (-α) = Real.exp (α * Real.log (1 / Δ)) := by
    have h11 : Real.rpow Δ (-α) = Real.exp ((-α) * Real.log Δ) := by
      have h11a : Real.rpow Δ (-α) = Real.exp (Real.log Δ * (-α)) := Real.rpow_def_of_pos hΔ_pos (-α)
      rw [h11a]
      <;> ring_nf
    rw [h11]
    have h12 : Real.log Δ = -Real.log (1 / Δ) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_one] <;> ring
    rw [h12] <;> ring_nf
  rw [h10]
  exact hX (Real.log (1 / Δ)) (by linarith)

/-! ### List minimum helper -/

private def minList (l : List ℝ) : ℝ := l.foldr min 1

private lemma minList_pos {l : List ℝ} (hl : ∀ x ∈ l, 0 < x) : 0 < minList l := by
  induction l with
  | nil => norm_num [minList]
  | cons a t ih =>
    have h1 : 0 < a := hl a (by simp)
    have h2 : 0 < minList t := ih (fun x hx => hl x (by simp [hx]))
    have h3 : 0 < min a (minList t) := lt_min h1 h2
    simpa [minList] using h3

private lemma minList_le {l : List ℝ} {x : ℝ} (hx : x ∈ l) : minList l ≤ x := by
  induction l with
  | nil => contradiction
  | cons a t ih =>
    have h_cases : x = a ∨ x ∈ t := by
      simp only [List.mem_cons] at hx <;> tauto
    rcases h_cases with (rfl | hxt)
    · simpa [minList] using min_le_left a (minList t)
    · have h_ih : minList t ≤ x := ih hxt
      simpa [minList] using le_trans (min_le_right a (minList t)) h_ih

/-! ### Combined numerical bounds for A1→A10 assembly -/

/-- Bundle of all purely numerical hypotheses needed by A1→A10 assembly. -/
structure AssemblyNumericalBounds (Δ s t ε : ℝ) : Prop where
  h81_le : (81 : ℝ) ≤ Real.rpow Δ (-t - ε)
  hΔ_small_A3 : 50000 * (Real.log (1 / Δ) + 1)^3 ≤ Real.rpow Δ (-ε)
  hΔ_absorb1 : 8 * (MainAppendix.affineLine_packing_constant : ℝ) * (43200 : ℝ)^s ≤ Real.rpow Δ (-2 * ε)
  hΔ_absorb2 : (8 : ℝ) ≤ Real.rpow Δ (s - t - 22 * ε)
  hΔ_small_A4 : Real.rpow Δ ε ≤ 1 / 81
  hΔ_small_pack_A4 : (4000 : ENNReal) * (AppendixA4.affinePackingM : ENNReal) ≤ ENNReal.ofReal (Real.rpow Δ (-ε))
  hK_bound : (4 * s + 3 * ε) * Real.log (1 / Δ) / Real.log 2 + 1 ≤ Real.rpow Δ (-2 * ε) / 2
  hΔ_3ε : (2 : ℝ) ≤ Real.rpow Δ (-3 * ε)
  h_small_half : Real.rpow Δ ε ≤ 1 / 2
  h_small2 : 4 + 16 * (2 : ℝ)^(t - s) ≤ Real.rpow Δ (-4 * ε)
  hΔ_small_A8 : (25 : ℝ) ≤ Real.rpow Δ (-2 * ε)
  hΔ_cover_A9 : (10000 : ℝ) ≤ Real.rpow Δ (-2 * s - ε)
  hΔ_packing_A9 : Real.rpow Δ (10 * ε) ≤ 1 / 144
  hΔ_small_A9 : 7 * Δ ≤ 1
  hΔ_coarse_absorb_A9 : (2 * 10^13 : ℝ) ≤ Real.rpow Δ (-ε)
  hΔ_fine_absorb_A9 : (16 * (MainAppendix.affineLine_packing_constant : ℝ)^2 *
      (2 * 20 * 1048576 * 256 * (3 / 2 : ℝ) * 256 * 16)) ≤ Real.rpow Δ (-453 * ε)
  hΔ_lt_1_16 : Δ < 1 / 16
  h_absorb_shear : (400 : ℝ) * (Real.sqrt 2)^s * (2 : ℝ)^s *
      Real.rpow Δ (-501 * ε) ≤ Real.rpow Δ (-600 * ε)
  h_absorb_union : (120 : ℝ) * Real.rpow Δ (-576 * ε) ≤ Real.rpow Δ (-600 * ε)
  h_small_delta : Real.rpow Δ (ε / 4) ≤ 1 / 100
  hK_large_weak : (MainAppendix.affineLine_packing_constant : ℝ) *
      ((800 * (11 : ℝ)) : ℝ)^s *
      (MainAppendix.plane_packing_constant : ℝ) * (4 : ℝ)^t *
      (MainAppendix.plane_packing_constant : ℝ) *
      Real.rpow Δ (s - t - 132 * ε) ≥ 2
  h_absorb_K_extra : (8 : ℝ) *
      (MainAppendix.affineLine_packing_constant : ℝ) *
      ((800 * (11 : ℝ)) : ℝ)^s *
      (MainAppendix.plane_packing_constant : ℝ)^3 *
      ((16 : ℝ) + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - t))) *
      Real.rpow Δ (6 * ε) ≤ Real.rpow Δ (-ε)
  h_absorb_4s3ε : ∀ (εA ρ_T : ℝ), 0 ≤ εA → εA ≤ ε / 50 →
      0 ≤ ρ_T → ρ_T ≤ ε / 20 →
      (4 : ℝ)^(2 * s + εA) ≤ Real.rpow Δ (-(3 * ε - 2 * εA - 2 * ρ_T))
  h_const_absorb_A7 : (MainAppendix.affineLine_packing_constant : ℝ)^2 *
      ((800 * (53 : ℝ)) : ℝ) * (16 : ℝ) + 1 ≤ Real.rpow Δ (-ε)
  h_absorb_4_dyadic : (16 : ℝ) ≤ Real.rpow Δ (-ε / 100)
  h_absorb_Kpack_dyadic : (1329409 : ℝ) ≤ Real.rpow Δ (-(59 * ε / 20))

/-- Produce a threshold Δ₀ such that all numerical bounds hold for 0 < Δ < Δ₀,
    given parameter constraints 0 < s < 1, s < t < 2, 0 < ε, 12ε ≤ s, 504ε < t-s. -/
lemma assembly_numerical_hypotheses
    (s t ε : ℝ)
    (hs_pos : 0 < s)
    (hs_lt_one : s < 1)
    (ht_gt_s : s < t)
    (ht_lt_two : t < 2)
    (hε_pos : 0 < ε)
    (h12ε : 12 * ε ≤ s)
    (hRKP : 576 * ε < t - s) :
    ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ, 0 < Δ → Δ < Δ₀ → AssemblyNumericalBounds Δ s t ε := by
  have h_ts_pos : 0 < t - s := by linarith
  have h_t_eps_pos : 0 < t + ε := by linarith
  have h_energy_alpha_pos : 0 < 4 * (t - s) - 27 * ε := by linarith
  have h_abs2_alpha_pos : 0 < t - s + 22 * ε := by linarith
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_2sε_pos : 0 < 2 * s + ε := by linarith
  have h_453ε_pos : 0 < 453 * ε := by positivity
  have h_21ε_pos : 0 < 21 * ε := by positivity
  have h_6ε_pos : 0 < 6 * ε := by positivity
  have h_14ε_pos : 0 < 14 * ε := by positivity

  -- Packing constant positivity
  have hpack_pos : 0 < (MainAppendix.affineLine_packing_constant : ℝ) :=
    Nat.cast_pos.mpr MainAppendix.affineLine_packing_constant_pos
  have hpackM_pos : 0 < (AppendixA4.affinePackingM : ℝ) := by
    simp [AppendixA4.affinePackingM] <;> norm_num

  -- Constants
  set C_abs1 : ℝ := 8 * (MainAppendix.affineLine_packing_constant : ℝ) * 43200 with hC_abs1_def
  set C_pack_A4 : ℝ := 4000 * (AppendixA4.affinePackingM : ℝ) with hC_pack_A4_def
  set C0 : ℝ := (4 * s + 3 * ε) / Real.log 2 with hC0_def
  set C_K : ℝ := C0 + 1 with hC_K_def
  set C_big : ℝ := 16 * (MainAppendix.affineLine_packing_constant : ℝ)^2 *
      (2 * 20 * 1048576 * 256 * (3 / 2 : ℝ) * 256 * 16) with hC_big_def
  set C_shear : ℝ := 400 * 2 * Real.sqrt 2 with hC_shear_def
  set C_K_large : ℝ := (MainAppendix.affineLine_packing_constant : ℝ) *
      ((800 * (11 : ℝ)) : ℝ)^s *
      (MainAppendix.plane_packing_constant : ℝ) * (4 : ℝ)^t *
      (MainAppendix.plane_packing_constant : ℝ) with hC_K_large_def
  set C_absorb_extra : ℝ := (8 : ℝ) *
      (MainAppendix.affineLine_packing_constant : ℝ) *
      ((800 * (11 : ℝ)) : ℝ)^s *
      (MainAppendix.plane_packing_constant : ℝ)^3 *
      ((16 : ℝ) + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - t)))
    with hC_absorb_extra_def
  set C_A7 : ℝ := (MainAppendix.affineLine_packing_constant : ℝ)^2 *
      ((800 * (53 : ℝ)) : ℝ) * (16 : ℝ) + 1
    with hC_A7_def

  have hC_abs1_pos : 0 < C_abs1 := by positivity
  have hC_pack_A4_pos : 0 < C_pack_A4 := by positivity
  have hC0_pos : 0 < C0 := by
    rw [hC0_def]
    have h : 0 < 4 * s + 3 * ε := by linarith
    positivity
  have hC_K_pos : 0 < C_K := by positivity
  have hC_big_pos : 0 < C_big := by positivity
  have hC_shear_pos : 0 < C_shear := by positivity
  have hpp_pos : 0 < (MainAppendix.plane_packing_constant : ℝ) := by
    exact_mod_cast MainAppendix.plane_packing_constant_pos
  have hC_K_large_pos : 0 < C_K_large := by
    dsimp only [C_K_large]; positivity
  have hC_absorb_extra_pos : 0 < C_absorb_extra := by
    have h1 : 0 < (1 : ℝ) - (2 : ℝ)^(s - t) := by
      have h2 : s - t < 0 := by linarith
      have h3 : (2 : ℝ)^(s - t) < 1 := by
        have h4 : (2 : ℝ)^(s - t) < (2 : ℝ)^(0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h2
        simpa using h4
      linarith
    dsimp only [C_absorb_extra]; positivity
  have hC_A7_pos : 0 < C_A7 := by
    dsimp only [C_A7]; positivity
  have h_132eps_pos : 0 < t - s + 132 * ε := by linarith
  have h_7eps_pos : 0 < 7 * ε := by positivity

  -- Absorption lemmas
  rcases const_absorb_delta (81 : ℝ) (t + ε) (by norm_num) h_t_eps_pos with ⟨Δ0, hΔ0_pos, hΔ0⟩
  rcases polylog_absorb_delta (50000 : ℝ) ε 3 (by norm_num) hε_pos with ⟨Δ1, hΔ1_pos, hΔ1⟩
  rcases const_absorb_delta C_abs1 (2 * ε) hC_abs1_pos (by positivity) with ⟨Δ2, hΔ2_pos, hΔ2⟩
  rcases const_absorb_delta (8 : ℝ) (t - s + 22 * ε) (by norm_num) h_abs2_alpha_pos with ⟨Δ3, hΔ3_pos, hΔ3⟩
  rcases const_absorb_delta C_pack_A4 ε hC_pack_A4_pos hε_pos with ⟨Δ4, hΔ4_pos, hΔ4⟩
  rcases polylog_absorb_delta C_K ε 1 hC_K_pos hε_pos with ⟨Δ5, hΔ5_pos, hΔ5⟩
  rcases const_absorb_delta (2 : ℝ) ε (by norm_num) hε_pos with ⟨Δ6, hΔ6_pos, hΔ6⟩
  rcases const_absorb_delta (2 : ℝ) (3 * ε) (by norm_num) (by positivity) with ⟨Δ7, hΔ7_pos, hΔ7⟩
  rcases const_absorb_delta (68 : ℝ) (4 * ε) (by norm_num) (by positivity) with ⟨Δ9, hΔ9_pos, hΔ9⟩
  rcases const_absorb_delta (25 : ℝ) (2 * ε) (by norm_num) (by positivity) with ⟨Δ10, hΔ10_pos, hΔ10⟩
  rcases const_absorb_delta (10000 : ℝ) (2 * s + ε) (by norm_num) h_2sε_pos with ⟨Δ11, hΔ11_pos, hΔ11⟩
  rcases const_absorb_delta (2 * 10^13 : ℝ) ε (by norm_num) hε_pos with ⟨Δ12, hΔ12_pos, hΔ12⟩
  rcases const_absorb_delta C_big (453 * ε) hC_big_pos h_453ε_pos with ⟨Δ13, hΔ13_pos, hΔ13⟩
  rcases const_absorb_delta C_shear (21 * ε) hC_shear_pos h_21ε_pos with ⟨Δ14, hΔ14_pos, hΔ14⟩
  rcases const_absorb_delta (120 : ℝ) (24 * ε) (by norm_num) (by positivity) with ⟨Δ15, hΔ15_pos, hΔ15⟩
  rcases const_absorb_delta (2 / C_K_large) (t - s + 132 * ε) (by positivity) h_132eps_pos
    with ⟨Δ16, hΔ16_pos, hΔ16⟩
  rcases const_absorb_delta C_absorb_extra (7 * ε) hC_absorb_extra_pos h_7eps_pos
    with ⟨Δ17, hΔ17_pos, hΔ17⟩
  rcases const_absorb_delta (64 : ℝ) (143 * ε / 50) (by norm_num) (by positivity)
    with ⟨Δ18, hΔ18_pos, hΔ18⟩
  rcases const_absorb_delta C_A7 ε hC_A7_pos hε_pos with ⟨Δ19, hΔ19_pos, hΔ19⟩
  rcases const_absorb_delta (16 : ℝ) (ε / 100) (by norm_num) (by positivity)
    with ⟨Δ20, hΔ20_pos, hΔ20⟩
  have h_59eps_pos : 0 < 59 * ε / 20 := by positivity
  rcases const_absorb_delta (1329409 : ℝ) (59 * ε / 20) (by norm_num) h_59eps_pos
    with ⟨Δ21, hΔ21_pos, hΔ21⟩

  -- Direct thresholds
  set Δ_A4 : ℝ := (1 / 81 : ℝ) ^ (1 / ε) with hΔ_A4_def
  set Δ_half : ℝ := (1 / 2 : ℝ) ^ (1 / ε) with hΔ_half_def
  set Δ_packing_A9 : ℝ := (1 / 144 : ℝ) ^ (1 / (10 * ε)) with hΔ_packing_A9_def
  set Δ_small_A9 : ℝ := 1 / 7 with hΔ_small_A9_def
  set Δ_1_16 : ℝ := 1 / 16 with hΔ_1_16_def
  set Δ_small_delta : ℝ := (1 / 100 : ℝ) ^ (4 / ε) with hΔ_small_delta_def

  have hΔ_A4_pos : 0 < Δ_A4 := by positivity
  have hΔ_half_pos : 0 < Δ_half := by positivity
  have hΔ_packing_A9_pos : 0 < Δ_packing_A9 := by positivity
  have hΔ_small_A9_pos : 0 < Δ_small_A9 := by positivity
  have hΔ_1_16_pos : 0 < Δ_1_16 := by positivity
  have hΔ_small_delta_pos : 0 < Δ_small_delta := by positivity

  -- Combined threshold using nested min (avoids list membership issues)
  let g1 := min Δ0 (min Δ1 (min Δ2 (min Δ3 (min Δ4 Δ5))))
  let g2 := min Δ6 (min Δ7 (min Δ9 Δ10))
  let g3 := min Δ11 (min Δ12 (min Δ13 (min Δ14 (min Δ15 (min Δ16 (min Δ17 (min Δ18 (min Δ19 (min Δ20 Δ21)))))))))
  let g4 := min Δ_A4 (min Δ_half (min Δ_packing_A9 (min Δ_small_A9 (min Δ_1_16 Δ_small_delta))))
  let Δ₀ := min g1 (min g2 (min g3 g4))

  have hg1_pos : 0 < g1 := by
    dsimp only [g1]
    apply lt_min
    · exact hΔ0_pos
    · apply lt_min
      · exact hΔ1_pos
      · apply lt_min
        · exact hΔ2_pos
        · apply lt_min
          · exact hΔ3_pos
          · apply lt_min
            · exact hΔ4_pos
            · exact hΔ5_pos
  have hg2_pos : 0 < g2 := by
    dsimp only [g2]
    apply lt_min
    · exact hΔ6_pos
    · apply lt_min
      · exact hΔ7_pos
      · apply lt_min
        · exact hΔ9_pos
        · exact hΔ10_pos
  have hg3_pos : 0 < g3 := by
    dsimp only [g3]
    apply lt_min
    · exact hΔ11_pos
    · apply lt_min
      · exact hΔ12_pos
      · apply lt_min
        · exact hΔ13_pos
        · apply lt_min
          · exact hΔ14_pos
          · apply lt_min
            · exact hΔ15_pos
            · apply lt_min
              · exact hΔ16_pos
              · apply lt_min
                · exact hΔ17_pos
                · apply lt_min
                  · exact hΔ18_pos
                  · apply lt_min
                    · exact hΔ19_pos
                    · apply lt_min
                      · exact hΔ20_pos
                      · exact hΔ21_pos
  have hg4_pos : 0 < g4 := by
    dsimp only [g4]
    apply lt_min
    · exact hΔ_A4_pos
    · apply lt_min
      · exact hΔ_half_pos
      · apply lt_min
        · exact hΔ_packing_A9_pos
        · apply lt_min
          · exact hΔ_small_A9_pos
          · apply lt_min
            · exact hΔ_1_16_pos
            · exact hΔ_small_delta_pos
  have hΔ₀_pos : 0 < Δ₀ := by
    dsimp only [Δ₀]
    apply lt_min
    · exact hg1_pos
    · apply lt_min
      · exact hg2_pos
      · apply lt_min
        · exact hg3_pos
        · exact hg4_pos

  use Δ₀, hΔ₀_pos
  intro Δ hΔ_pos hΔ_lt

  -- Group threshold bounds
  have hg1_le0 : g1 ≤ Δ0 := min_le_left _ _
  have hg1_le1 : g1 ≤ Δ1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hg1_le2 : g1 ≤ Δ2 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hg1_le3 : g1 ≤ Δ3 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hg1_le4 : g1 ≤ Δ4 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hg1_le5 : g1 ≤ Δ5 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))

  have hg2_le6 : g2 ≤ Δ6 := min_le_left _ _
  have hg2_le7 : g2 ≤ Δ7 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hg2_le9 : g2 ≤ Δ9 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hg2_le10 : g2 ≤ Δ10 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))

  have hg3_le11 : g3 ≤ Δ11 := min_le_left _ _
  have hg3_le12 : g3 ≤ Δ12 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hg3_le13 : g3 ≤ Δ13 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hg3_le14 : g3 ≤ Δ14 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hg3_le15 : g3 ≤ Δ15 :=
    le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
      le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) (min_le_left _ _)
  have hg3_le16 : g3 ≤ Δ16 :=
    le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
      le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
        le_trans (min_le_right _ _) (min_le_left _ _)
  have hg3_le17 : g3 ≤ Δ17 :=
    le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
      le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
        le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) (min_le_left _ _)
  have hg3_le18 : g3 ≤ Δ18 :=
    le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
      le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
        le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
          le_trans (min_le_right _ _) (min_le_left _ _)
  have hg3_le19 : g3 ≤ Δ19 :=
    le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
      le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
        le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
          le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) (min_le_left _ _)
  have hg3_le20 : g3 ≤ Δ20 :=
    le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
      le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
        le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
          le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
            le_trans (min_le_right _ _) (min_le_left _ _)
  have hg3_le21 : g3 ≤ Δ21 :=
    le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
      le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
        le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
          le_trans (min_le_right _ _) $ le_trans (min_le_right _ _) $
            le_trans (min_le_right _ _) (min_le_right _ _)

  have hg4_leA4 : g4 ≤ Δ_A4 := min_le_left _ _
  have hg4_leHalf : g4 ≤ Δ_half := le_trans (min_le_right _ _) (min_le_left _ _)
  have hg4_lePack : g4 ≤ Δ_packing_A9 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hg4_leSmall : g4 ≤ Δ_small_A9 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hg4_le16 : g4 ≤ Δ_1_16 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hg4_leSmallDelta : g4 ≤ Δ_small_delta := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))

  have h0_le_g1 : Δ₀ ≤ g1 := min_le_left _ _
  have h0_le_g2 : Δ₀ ≤ g2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have h0_le_g3 : Δ₀ ≤ g3 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have h0_le_g4 : Δ₀ ≤ g4 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))

  have h_lt0 : Δ < Δ0 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g1 hg1_le0)
  have h_lt1 : Δ < Δ1 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g1 hg1_le1)
  have h_lt2 : Δ < Δ2 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g1 hg1_le2)
  have h_lt3 : Δ < Δ3 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g1 hg1_le3)
  have h_lt4 : Δ < Δ4 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g1 hg1_le4)
  have h_lt5 : Δ < Δ5 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g1 hg1_le5)
  have h_lt6 : Δ < Δ6 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g2 hg2_le6)
  have h_lt7 : Δ < Δ7 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g2 hg2_le7)
  have h_lt9 : Δ < Δ9 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g2 hg2_le9)
  have h_lt10 : Δ < Δ10 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g2 hg2_le10)
  have h_lt11 : Δ < Δ11 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g3 hg3_le11)
  have h_lt12 : Δ < Δ12 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g3 hg3_le12)
  have h_lt13 : Δ < Δ13 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g3 hg3_le13)
  have h_lt14 : Δ < Δ14 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g3 hg3_le14)
  have h_lt15 : Δ < Δ15 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g3 hg3_le15)
  have h_lt16 : Δ < Δ16 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g3 hg3_le16)
  have h_lt17 : Δ < Δ17 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g3 hg3_le17)
  have h_lt18 : Δ < Δ18 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g3 hg3_le18)
  have h_lt19 : Δ < Δ19 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g3 hg3_le19)
  have h_lt20 : Δ < Δ20 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g3 hg3_le20)
  have h_lt21 : Δ < Δ21 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g3 hg3_le21)
  have h_lt_A4 : Δ < Δ_A4 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g4 hg4_leA4)
  have h_lt_half : Δ < Δ_half := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g4 hg4_leHalf)
  have h_lt_packing_A9 : Δ < Δ_packing_A9 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g4 hg4_lePack)
  have h_lt_small_A9 : Δ < Δ_small_A9 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g4 hg4_leSmall)
  have h_lt_1_16 : Δ < Δ_1_16 := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g4 hg4_le16)
  have h_lt_small_delta : Δ < Δ_small_delta := lt_of_lt_of_le hΔ_lt (le_trans h0_le_g4 hg4_leSmallDelta)

  -- hK_large_weak
  have h_h16 : (2 : ℝ) / C_K_large ≤ Real.rpow Δ (-(t - s + 132 * ε)) := hΔ16 Δ hΔ_pos h_lt16
  have h_h16_exp : Real.rpow Δ (s - t - 132 * ε) = Real.rpow Δ (-(t - s + 132 * ε)) := by ring_nf
  have h_h16' : C_K_large * Real.rpow Δ (s - t - 132 * ε) ≥ 2 := by
    rw [h_h16_exp]
    calc C_K_large * Real.rpow Δ (-(t - s + 132 * ε))
      ≥ C_K_large * ((2 : ℝ) / C_K_large) := by gcongr
    _ = 2 := by field_simp [hC_K_large_pos.ne'] <;> ring

  -- h_absorb_K_extra
  have h_h17 : C_absorb_extra ≤ Real.rpow Δ (-(7 * ε)) := hΔ17 Δ hΔ_pos h_lt17
  have h_h17_rpow : Real.rpow Δ (-(7 * ε)) * Real.rpow Δ (6 * ε) = Real.rpow Δ (-ε) := by
    have h : Real.rpow Δ ((-(7 * ε)) + (6 * ε)) = Real.rpow Δ (-(7 * ε)) * Real.rpow Δ (6 * ε) :=
      Real.rpow_add hΔ_pos (-(7 * ε)) (6 * ε)
    have h2 : (-(7 * ε)) + (6 * ε) = -ε := by ring
    rw [h2] at h
    exact h.symm
  have h_h17_pos6 : 0 ≤ Real.rpow Δ (6 * ε) := Real.rpow_nonneg hΔ_pos.le (6 * ε)
  have h_h17_mul : C_absorb_extra * Real.rpow Δ (6 * ε) ≤
      Real.rpow Δ (-(7 * ε)) * Real.rpow Δ (6 * ε) :=
    mul_le_mul_of_nonneg_right h_h17 h_h17_pos6
  have h_h17' : C_absorb_extra * Real.rpow Δ (6 * ε) ≤ Real.rpow Δ (-ε) := by
    rw [← h_h17_rpow]
    exact h_h17_mul

  -- h_absorb_4s3ε
  have h_h23 : (64 : ℝ) ≤ Real.rpow Δ (-(143 * ε / 50)) := hΔ18 Δ hΔ_pos h_lt18
  have h_absorb_4s3ε : ∀ (εA ρ_T : ℝ), 0 ≤ εA → εA ≤ ε / 50 →
      0 ≤ ρ_T → ρ_T ≤ ε / 20 →
      (4 : ℝ)^(2 * s + εA) ≤ Real.rpow Δ (-(3 * ε - 2 * εA - 2 * ρ_T)) := by
    intro εA ρ_T hεA_nonneg hεA_max hρT_nonneg hρT_max
    have h1 : 2 * s + εA ≤ 3 := by linarith [hs_lt_one]
    have h2 : (4 : ℝ)^(2 * s + εA) ≤ (64 : ℝ) := by
      have h3 : (4 : ℝ)^(2 * s + εA) ≤ (4 : ℝ)^(3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      norm_num at h3 ⊢ <;> exact h3
    have h4 : 143 * ε / 50 ≤ 3 * ε - 2 * εA - 2 * ρ_T := by linarith
    have h_lt_one : Δ < 1 := by
      have h : Δ < 1 / 16 := by simpa [Δ_1_16] using h_lt_1_16
      linarith
    have h5 : Real.rpow Δ (-(143 * ε / 50)) ≤
        Real.rpow Δ (-(3 * ε - 2 * εA - 2 * ρ_T)) := by
      have h_exp : -(143 * ε / 50) ≥ -(3 * ε - 2 * εA - 2 * ρ_T) := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos h_lt_one.le h_exp
    exact le_trans (le_trans h2 h_h23) h5

  -- h81_le
  have h_h0 : (81 : ℝ) ≤ Real.rpow Δ (-(t + ε)) := hΔ0 Δ hΔ_pos h_lt0
  have h_h0' : (81 : ℝ) ≤ Real.rpow Δ (-t - ε) := by
    have h_eq : (-(t + ε)) = -t - ε := by ring
    rw [h_eq] at h_h0
    exact h_h0

  -- hΔ_small_A3
  have h_h1 : 50000 * (Real.log (1 / Δ) + 1)^3 ≤ Real.rpow Δ (-ε) := hΔ1 Δ hΔ_pos h_lt1

  -- hΔ_absorb1
  have h_43200s : (43200 : ℝ)^s ≤ 43200 := by
    have h : (43200 : ℝ)^s ≤ (43200 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    simpa using h
  have h_h2 : 8 * (MainAppendix.affineLine_packing_constant : ℝ) * (43200 : ℝ)^s ≤ C_abs1 := by
    rw [hC_abs1_def]
    gcongr
    <;> linarith
  have h_h2' : C_abs1 ≤ Real.rpow Δ (-2 * ε) := by
    have h := hΔ2 Δ hΔ_pos h_lt2
    have h_eq : Real.rpow Δ (-(2 * ε)) = Real.rpow Δ (-2 * ε) := by ring_nf
    rw [h_eq] at h
    exact h
  have h_h2_final : 8 * (MainAppendix.affineLine_packing_constant : ℝ) * (43200 : ℝ)^s ≤ Real.rpow Δ (-2 * ε) :=
    le_trans h_h2 h_h2'

  -- hΔ_absorb2
  have h_h3 : (8 : ℝ) ≤ Real.rpow Δ (-(t - s + 22 * ε)) := hΔ3 Δ hΔ_pos h_lt3
  have h_h3' : Real.rpow Δ (s - t - 22 * ε) = Real.rpow Δ (-(t - s + 22 * ε)) := by ring_nf
  have h_h3_final : (8 : ℝ) ≤ Real.rpow Δ (s - t - 22 * ε) := by
    rw [h_h3'] <;> exact h_h3

  -- hΔ_small_A4
  have h_h4 : Real.rpow Δ ε ≤ 1 / 81 := by
    have h41 : Δ < (1 / 81 : ℝ) ^ (1 / ε) := h_lt_A4
    have h42 : Real.rpow Δ ε < Real.rpow ((1 / 81 : ℝ) ^ (1 / ε)) ε :=
      Real.rpow_lt_rpow (by positivity) h41 (by positivity)
    have h43 : ((1 / 81 : ℝ) ^ (1 / ε)) ^ ε = 1 / 81 := by
      have h44 : (1 / 81 : ℝ) ^ ((1 / ε) * ε) = ((1 / 81 : ℝ) ^ (1 / ε)) ^ ε := Real.rpow_mul (by norm_num) (1 / ε) ε
      have h45 : (1 / ε) * ε = 1 := by field_simp [hε_pos.ne'] <;> ring
      rw [h45] at h44
      simpa using h44.symm
    have h46 : Real.rpow ((1 / 81 : ℝ) ^ (1 / ε)) ε = ((1 / 81 : ℝ) ^ (1 / ε)) ^ ε := by rfl
    rw [h46, h43] at h42
    exact le_of_lt h42

  -- hΔ_small_pack_A4
  have h_h5_real : C_pack_A4 ≤ Real.rpow Δ (-ε) := hΔ4 Δ hΔ_pos h_lt4
  have h_h5_real' : ((4000 * AppendixA4.affinePackingM : ℕ) : ℝ) ≤ Real.rpow Δ (-ε) := by
    have h_eq : C_pack_A4 = ((4000 * AppendixA4.affinePackingM : ℕ) : ℝ) := by
      simp [hC_pack_A4_def, AppendixA4.affinePackingM] <;> ring
    rw [h_eq] at h_h5_real
    exact h_h5_real
  have h_h5_final : (4000 : ENNReal) * (AppendixA4.affinePackingM : ENNReal) ≤ ENNReal.ofReal (Real.rpow Δ (-ε)) := by
    have h6 : (4000 : ENNReal) * (AppendixA4.affinePackingM : ENNReal) = ↑(4000 * AppendixA4.affinePackingM) := by
      simp [Nat.cast_mul] <;> ring
    rw [h6]
    let y := Real.rpow Δ (-ε)
    have hy_pos : 0 < y := Real.rpow_pos_of_pos hΔ_pos (-ε)
    have hy : 0 ≤ y := by linarith
    let b : NNReal := Real.toNNReal y
    have hb : (b : ℝ) = y := by
      have h_eq : b = NNReal.mk y hy := Real.toNNReal_of_nonneg hy
      rw [h_eq]
      <;> simp
    have h7 : ((4000 * AppendixA4.affinePackingM : ℕ) : ℝ) ≤ y := h_h5_real'
    let n : NNReal := ↑(4000 * AppendixA4.affinePackingM)
    have hn : (n : ℝ) = ((4000 * AppendixA4.affinePackingM : ℕ) : ℝ) := by
      simp [n] <;> norm_cast
    have h9 : (n : ℝ) ≤ (b : ℝ) := by rw [hn, hb]; exact h7
    have h10 : n ≤ b := NNReal.coe_le_coe.mp h9
    have h11 : ENNReal.ofReal y = ↑b := by
      simp [ENNReal.ofReal, hy] <;> rfl
    rw [h11]
    have h12 : (↑(4000 * AppendixA4.affinePackingM) : ENNReal) = ↑n := by
      congr <;> simp [n] <;> norm_cast
    rw [h12]
    exact_mod_cast h10

  -- hK_bound
  have h_h6_poly : C_K * (Real.log (1 / Δ) + 1) ≤ Real.rpow Δ (-ε) := by
    have h := hΔ5 Δ hΔ_pos h_lt5
    have h_simp : C_K * (Real.log (1 / Δ) + 1)^1 = C_K * (Real.log (1 / Δ) + 1) := by simp
    rw [h_simp] at h
    exact h
  have h_h6_const : (2 : ℝ) ≤ Real.rpow Δ (-ε) := hΔ6 Δ hΔ_pos h_lt6
  have h_log_nonneg : 0 ≤ Real.log (1 / Δ) := by
    have h : Δ < 1 := by
      have h' : Δ < 1 / 16 := h_lt_1_16
      linarith
    have h' : 1 / Δ > 1 := by
      apply one_lt_one_div
      <;> linarith
    exact Real.log_nonneg (by linarith)
  have h_C0_nonneg : 0 ≤ C0 := by positivity
  set x := Real.log (1 / Δ) with hx_def
  have h_x_nonneg : 0 ≤ x := h_log_nonneg
  have h_h6_lhs : C0 * x + 1 ≤ C_K * (x + 1) := by
    have h1 : C_K * (x + 1) - (C0 * x + 1) = C0 + x := by
      simp [hC_K_def, hx_def] <;> ring
    have h2 : 0 ≤ C0 + x := by positivity
    linarith
  have h_h6_mid : C_K * (Real.log (1 / Δ) + 1) ≤ Real.rpow Δ (-ε) := h_h6_poly
  set a := Real.rpow Δ (-ε) with ha_def
  have ha2 : (2 : ℝ) ≤ a := h_h6_const
  have h10 : Real.rpow Δ (-2 * ε) = a * a := by
    have h11 : Real.rpow Δ ((-ε) + (-ε)) = Real.rpow Δ (-ε) * Real.rpow Δ (-ε) := Real.rpow_add hΔ_pos (-ε) (-ε)
    have h12 : (-ε) + (-ε) = -2 * ε := by ring
    rw [h12] at h11
    simpa [ha_def] using h11
  have h_h6_rhs : a ≤ (a * a) / 2 := by
    have h13 : 0 ≤ a := by positivity
    have h14 : 2 * a ≤ a * a := by
      calc 2 * a
        = a * 2 := by ring
      _ ≤ a * a := by gcongr <;> linarith
    linarith
  have h_h6_final : (4 * s + 3 * ε) * Real.log (1 / Δ) / Real.log 2 + 1 ≤ Real.rpow Δ (-2 * ε) / 2 := by
    have h11 : (4 * s + 3 * ε) * Real.log (1 / Δ) / Real.log 2 + 1 = C0 * Real.log (1 / Δ) + 1 := by
      simp [hC0_def] <;> ring
    rw [h11, h10]
    exact le_trans (le_trans h_h6_lhs h_h6_mid) h_h6_rhs

  -- hΔ_3ε
  have h_exp_eq : ∀ (n : ℝ), (-(n * ε)) = (-n * ε) := by intro n; ring
  have h_h7 : (2 : ℝ) ≤ Real.rpow Δ (-3 * ε) := by
    have h := hΔ7 Δ hΔ_pos h_lt7
    rw [h_exp_eq 3] at h
    exact h

  -- h_small_half
  have h_h8 : Real.rpow Δ ε ≤ 1 / 2 := by
    have h81 : Δ < (1 / 2 : ℝ) ^ (1 / ε) := h_lt_half
    have h82 : Real.rpow Δ ε < Real.rpow ((1 / 2 : ℝ) ^ (1 / ε)) ε :=
      Real.rpow_lt_rpow (by positivity) h81 (by positivity)
    have h83 : ((1 / 2 : ℝ) ^ (1 / ε)) ^ ε = 1 / 2 := by
      have h84 : ((1 / 2 : ℝ) ^ (1 / ε)) ^ ε = (1 / 2 : ℝ) ^ ((1 / ε) * ε) :=
      (Real.rpow_mul (by norm_num) (1 / ε) ε).symm
      rw [h84]
      have h85 : (1 / ε) * ε = 1 := by field_simp [hε_pos.ne'] <;> ring
      rw [h85] <;> norm_num
    have h83' : Real.rpow ((1 / 2 : ℝ) ^ (1 / ε)) ε = ((1 / 2 : ℝ) ^ (1 / ε)) ^ ε := by rfl
    rw [h83', h83] at h82
    exact le_of_lt h82

  -- h_small2
  have h_2ts : (2 : ℝ)^(t - s) ≤ 4 := by
    have h : t - s < 2 := by linarith
    have h' : (2 : ℝ)^(t - s) ≤ (2 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    norm_num at h' ⊢
    <;> exact h'
  have h_h10 : 4 + 16 * (2 : ℝ)^(t - s) ≤ (68 : ℝ) := by
    linarith [h_2ts]
  have h_h10' : (68 : ℝ) ≤ Real.rpow Δ (-4 * ε) := by
    have h := hΔ9 Δ hΔ_pos h_lt9
    rw [h_exp_eq 4] at h
    exact h
  have h_h10_final : 4 + 16 * (2 : ℝ)^(t - s) ≤ Real.rpow Δ (-4 * ε) :=
    le_trans h_h10 h_h10'

  -- hΔ_small_A8
  have h_h11 : (25 : ℝ) ≤ Real.rpow Δ (-2 * ε) := by
    have h := hΔ10 Δ hΔ_pos h_lt10
    rw [h_exp_eq 2] at h
    exact h

  -- hΔ_cover_A9
  have h_h12 : (10000 : ℝ) ≤ Real.rpow Δ (-2 * s - ε) := by
    have h := hΔ11 Δ hΔ_pos h_lt11
    have h_eq : (-(2 * s + ε)) = (-2 * s - ε) := by ring
    rw [h_eq] at h
    exact h

  -- hΔ_packing_A9
  have h_h13 : Real.rpow Δ (10 * ε) ≤ 1 / 144 := by
    have h131 : Δ < (1 / 144 : ℝ) ^ (1 / (10 * ε)) := h_lt_packing_A9
    have h132 : Real.rpow Δ (10 * ε) < Real.rpow ((1 / 144 : ℝ) ^ (1 / (10 * ε))) (10 * ε) :=
      Real.rpow_lt_rpow (by positivity) h131 (by positivity)
    have h133 : ((1 / 144 : ℝ) ^ (1 / (10 * ε))) ^ (10 * ε) = 1 / 144 := by
      have h134 : ((1 / 144 : ℝ) ^ (1 / (10 * ε))) ^ (10 * ε) = (1 / 144 : ℝ) ^ ((1 / (10 * ε)) * (10 * ε)) :=
      (Real.rpow_mul (by norm_num) (1 / (10 * ε)) (10 * ε)).symm
      rw [h134]
      have h135 : (1 / (10 * ε)) * (10 * ε) = 1 := by field_simp [hε_pos.ne'] <;> ring
      rw [h135] <;> norm_num
    have h133' : Real.rpow ((1 / 144 : ℝ) ^ (1 / (10 * ε))) (10 * ε) = ((1 / 144 : ℝ) ^ (1 / (10 * ε))) ^ (10 * ε) := by rfl
    rw [h133', h133] at h132
    exact le_of_lt h132

  -- hΔ_small_A9
  have h_h14 : 7 * Δ ≤ 1 := by
    have h : Δ < 1 / 7 := h_lt_small_A9
    linarith

  -- hΔ_coarse_absorb_A9
  have h_h15 : (2 * 10^13 : ℝ) ≤ Real.rpow Δ (-ε) := hΔ12 Δ hΔ_pos h_lt12

  -- hΔ_fine_absorb_A9
  have h_h16 : C_big ≤ Real.rpow Δ (-453 * ε) := by
    have h := hΔ13 Δ hΔ_pos h_lt13
    rw [h_exp_eq 453] at h
    exact h
  have h_h16_final : (16 * (MainAppendix.affineLine_packing_constant : ℝ)^2 *
      (2 * 20 * 1048576 * 256 * (3 / 2 : ℝ) * 256 * 16)) ≤ Real.rpow Δ (-453 * ε) := by
    have h_eq : C_big = (16 * (MainAppendix.affineLine_packing_constant : ℝ)^2 *
        (2 * 20 * 1048576 * 256 * (3 / 2 : ℝ) * 256 * 16)) := by
      simp [hC_big_def]
    rw [h_eq] at h_h16
    exact h_h16

  -- hΔ_lt_1_16
  have h_h17 : Δ < 1 / 16 := h_lt_1_16

  -- h_absorb_shear
  have h_shear_const : (400 : ℝ) * (Real.sqrt 2)^s * (2 : ℝ)^s ≤ C_shear := by
    have h1 : (Real.sqrt 2)^s * (2 : ℝ)^s = (2 * Real.sqrt 2)^s := by
      have h2 : (Real.sqrt 2)^s * (2 : ℝ)^s = (Real.sqrt 2 * (2 : ℝ))^s := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
      rw [h2]
      have h3 : Real.sqrt 2 * (2 : ℝ) = 2 * Real.sqrt 2 := by ring
      rw [h3]
    have h2 : (400 : ℝ) * (Real.sqrt 2)^s * (2 : ℝ)^s = (400 : ℝ) * ((Real.sqrt 2)^s * (2 : ℝ)^s) := by ring
    rw [h2, h1]
    have h_ge_one : (1 : ℝ) ≤ 2 * Real.sqrt 2 := by
      have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
        apply Real.le_sqrt_of_sq_le
        norm_num
      linarith
    have h3 : (2 * Real.sqrt 2)^s ≤ 2 * Real.sqrt 2 := by
      have h4 : (2 * Real.sqrt 2)^s ≤ (2 * Real.sqrt 2)^(1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h_ge_one (by linarith)
      simpa using h4
    have h5 : (400 : ℝ) * (2 * Real.sqrt 2)^s ≤ (400 : ℝ) * (2 * Real.sqrt 2) := by gcongr
    have h6 : C_shear = (400 : ℝ) * (2 * Real.sqrt 2) := by
      simp [hC_shear_def] <;> ring
    rw [h6]
    exact h5
  have h_h18 : C_shear ≤ Real.rpow Δ (-21 * ε) := by
    have h := hΔ14 Δ hΔ_pos h_lt14
    rw [h_exp_eq 21] at h
    exact h
  have h_h18_old : (400 : ℝ) * (Real.sqrt 2)^s * (2 : ℝ)^s ≤ Real.rpow Δ (-21 * ε) :=
    le_trans h_shear_const h_h18
  have h_h18' : (400 : ℝ) * (Real.sqrt 2)^s * (2 : ℝ)^s ≤ Real.rpow Δ (-99 * ε) := by
    have h_weaken : Real.rpow Δ (-21 * ε) ≤ Real.rpow Δ (-99 * ε) := by
      have h_exp : -21 * ε ≥ -99 * ε := by linarith
      have h_lt_one : Δ < 1 := by linarith [h_lt_1_16]
      exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos h_lt_one.le h_exp
    exact le_trans h_h18_old h_weaken
  have h_h18_final : (400 : ℝ) * (Real.sqrt 2)^s * (2 : ℝ)^s *
      Real.rpow Δ (-501 * ε) ≤ Real.rpow Δ (-600 * ε) := by
    have h_pos1 : 0 < Real.rpow Δ (-501 * ε) := Real.rpow_pos_of_pos hΔ_pos (-501 * ε)
    have h_eq : Real.rpow Δ (-600 * ε) = Real.rpow Δ (-99 * ε) * Real.rpow Δ (-501 * ε) := by
      have h : Real.rpow Δ ((-99 * ε) + (-501 * ε)) = Real.rpow Δ (-99 * ε) * Real.rpow Δ (-501 * ε) :=
        Real.rpow_add hΔ_pos (-99 * ε) (-501 * ε)
      have h2 : (-99 * ε) + (-501 * ε) = -600 * ε := by ring
      rw [h2] at h
      exact h
    rw [h_eq]
    exact mul_le_mul_of_nonneg_right h_h18' (by positivity)

  -- h_absorb_union
  have h_h19 : (120 : ℝ) ≤ Real.rpow Δ (-24 * ε) := by
    have h := hΔ15 Δ hΔ_pos h_lt15
    rw [h_exp_eq 24] at h
    exact h
  have h_h19_final : (120 : ℝ) * Real.rpow Δ (-576 * ε) ≤ Real.rpow Δ (-600 * ε) := by
    have h_eq : Real.rpow Δ (-600 * ε) = Real.rpow Δ (-24 * ε) * Real.rpow Δ (-576 * ε) := by
      have h : Real.rpow Δ ((-24 * ε) + (-576 * ε)) = Real.rpow Δ (-24 * ε) * Real.rpow Δ (-576 * ε) :=
        Real.rpow_add hΔ_pos (-24 * ε) (-576 * ε)
      have h2 : (-24 * ε) + (-576 * ε) = -600 * ε := by ring
      rw [h2] at h
      exact h
    rw [h_eq]
    have h_pos2 : 0 ≤ Real.rpow Δ (-576 * ε) := by
      exact le_of_lt (Real.rpow_pos_of_pos hΔ_pos (-576 * ε))
    exact mul_le_mul_of_nonneg_right h_h19 h_pos2

  -- h_small_delta
  have h_h20 : Real.rpow Δ (ε / 4) ≤ 1 / 100 := by
    have h201 : Δ < (1 / 100 : ℝ) ^ (4 / ε) := h_lt_small_delta
    have h202 : Real.rpow Δ (ε / 4) < Real.rpow ((1 / 100 : ℝ) ^ (4 / ε)) (ε / 4) :=
      Real.rpow_lt_rpow (by positivity) h201 (by positivity)
    have h203 : ((1 / 100 : ℝ) ^ (4 / ε)) ^ (ε / 4) = 1 / 100 := by
      have h204 : ((1 / 100 : ℝ) ^ (4 / ε)) ^ (ε / 4) = (1 / 100 : ℝ) ^ ((4 / ε) * (ε / 4)) :=
        (Real.rpow_mul (by norm_num) (4 / ε) (ε / 4)).symm
      rw [h204]
      have h205 : (4 / ε) * (ε / 4) = 1 := by field_simp [hε_pos.ne'] <;> ring
      rw [h205] <;> norm_num
    have h203' : Real.rpow ((1 / 100 : ℝ) ^ (4 / ε)) (ε / 4) = ((1 / 100 : ℝ) ^ (4 / ε)) ^ (ε / 4) := by rfl
    rw [h203', h203] at h202
    exact le_of_lt h202

  have h_h21 : C_A7 ≤ Real.rpow Δ (-ε) := hΔ19 Δ hΔ_pos h_lt19

  have h_h22 : (16 : ℝ) ≤ Real.rpow Δ (-ε / 100) := by
    have h := hΔ20 Δ hΔ_pos h_lt20
    have h_eq : (-(ε / 100)) = -ε / 100 := by ring
    rw [h_eq] at h
    exact h
  have h_h23 : (1329409 : ℝ) ≤ Real.rpow Δ (-(59 * ε / 20)) := hΔ21 Δ hΔ_pos h_lt21

  exact ⟨h_h0', h_h1, h_h2_final, h_h3_final, h_h4, h_h5_final, h_h6_final, h_h7, h_h8,
    h_h10_final, h_h11, h_h12, h_h13, h_h14, h_h15, h_h16_final, h_h17,
    h_h18_final, h_h19_final, h_h20, h_h16', h_h17', h_absorb_4s3ε, h_h21, h_h22, h_h23⟩

/-- Convert `AssemblyNumericalBounds` from scale parameter `t` to `u`
    for `t ≤ u ≤ 2`. Fields that improve for larger `u` are weakened;
    `h_small2` uses the universal bound `68` which holds for all `u ≤ 2`. -/
lemma AssemblyNumericalBounds.weaken_u
    {Δ s t u ε : ℝ}
    (h : AssemblyNumericalBounds Δ s t ε)
    (h_small2_univ : (68 : ℝ) ≤ Real.rpow Δ (-4 * ε))
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hs_pos : 0 < s) (hst : s < t)
    (htu : t ≤ u) (hu2 : u ≤ 2) :
    AssemblyNumericalBounds Δ s u ε := by
  have h81_le' : (81 : ℝ) ≤ Real.rpow Δ (-u - ε) := by
    have h_exp : -u - ε ≤ -t - ε := by linarith
    have h' : Real.rpow Δ (-t - ε) ≤ Real.rpow Δ (-u - ε) :=
      Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h_exp
    exact le_trans h.h81_le h'
  have h_absorb2' : (8 : ℝ) ≤ Real.rpow Δ (s - u - 22 * ε) := by
    have h_exp : s - u - 22 * ε ≤ s - t - 22 * ε := by linarith
    have h' : Real.rpow Δ (s - t - 22 * ε) ≤ Real.rpow Δ (s - u - 22 * ε) :=
      Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h_exp
    exact le_trans h.hΔ_absorb2 h'
  have h_us_le_2 : u - s ≤ 2 := by linarith
  have h_small2' : 4 + 16 * (2 : ℝ)^(u - s) ≤ Real.rpow Δ (-4 * ε) := by
    have h2 : (2 : ℝ)^(u - s) ≤ (2 : ℝ)^(2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h_us_le_2
    have h3 : 4 + 16 * (2 : ℝ)^(u - s) ≤ (68 : ℝ) := by
      have h4 : (2 : ℝ)^(u - s) ≤ 4 := by
        rw [show (2 : ℝ)^(2 : ℝ) = 4 by norm_num] at h2
        exact h2
      linarith
    exact le_trans h3 h_small2_univ
  have hK_large_weak' : (MainAppendix.affineLine_packing_constant : ℝ) *
      ((800 * (11 : ℝ)) : ℝ)^s *
      (MainAppendix.plane_packing_constant : ℝ) * (4 : ℝ)^u *
      (MainAppendix.plane_packing_constant : ℝ) *
      Real.rpow Δ (s - u - 132 * ε) ≥ 2 := by
    have h4u_ge_4t : (4 : ℝ)^u ≥ (4 : ℝ)^t := by
      have h_exp : t ≤ u := htu
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h_exp
    have h_rpow_ge : Real.rpow Δ (s - u - 132 * ε) ≥ Real.rpow Δ (s - t - 132 * ε) := by
      have h_exp : s - u - 132 * ε ≤ s - t - 132 * ε := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h_exp
    set K : ℝ := (MainAppendix.affineLine_packing_constant : ℝ) *
        ((800 * (11 : ℝ)) : ℝ)^s *
        (MainAppendix.plane_packing_constant : ℝ) *
        (MainAppendix.plane_packing_constant : ℝ) with hK_def
    have hK_nonneg : 0 ≤ K := by positivity
    have h_rpow_u_nonneg : 0 ≤ Real.rpow Δ (s - u - 132 * ε) := Real.rpow_nonneg hΔ_pos.le _
    have h4t_nonneg : 0 ≤ (4 : ℝ)^t := by positivity
    have h_product_ge : (4 : ℝ)^u * Real.rpow Δ (s - u - 132 * ε) ≥
        (4 : ℝ)^t * Real.rpow Δ (s - u - 132 * ε) :=
      mul_le_mul_of_nonneg_right h4u_ge_4t h_rpow_u_nonneg
    have h_product2_ge : (4 : ℝ)^t * Real.rpow Δ (s - u - 132 * ε) ≥
        (4 : ℝ)^t * Real.rpow Δ (s - t - 132 * ε) :=
      mul_le_mul_of_nonneg_left h_rpow_ge h4t_nonneg
    have h_final_ge : (4 : ℝ)^u * Real.rpow Δ (s - u - 132 * ε) ≥
        (4 : ℝ)^t * Real.rpow Δ (s - t - 132 * ε) :=
      calc (4 : ℝ)^u * Real.rpow Δ (s - u - 132 * ε)
        ≥ (4 : ℝ)^t * Real.rpow Δ (s - u - 132 * ε) := h_product_ge
      _ ≥ (4 : ℝ)^t * Real.rpow Δ (s - t - 132 * ε) := h_product2_ge
    have h_main : K * ((4 : ℝ)^u * Real.rpow Δ (s - u - 132 * ε)) ≥
        K * ((4 : ℝ)^t * Real.rpow Δ (s - t - 132 * ε)) :=
      mul_le_mul_of_nonneg_left h_final_ge hK_nonneg
    have h_goal : (MainAppendix.affineLine_packing_constant : ℝ) *
        ((800 * (11 : ℝ)) : ℝ)^s *
        (MainAppendix.plane_packing_constant : ℝ) * (4 : ℝ)^u *
        (MainAppendix.plane_packing_constant : ℝ) *
        Real.rpow Δ (s - u - 132 * ε) =
        K * ((4 : ℝ)^u * Real.rpow Δ (s - u - 132 * ε)) := by
      simp [hK_def] <;> ring
    have h_orig : (MainAppendix.affineLine_packing_constant : ℝ) *
        ((800 * (11 : ℝ)) : ℝ)^s *
        (MainAppendix.plane_packing_constant : ℝ) * (4 : ℝ)^t *
        (MainAppendix.plane_packing_constant : ℝ) *
        Real.rpow Δ (s - t - 132 * ε) =
        K * ((4 : ℝ)^t * Real.rpow Δ (s - t - 132 * ε)) := by
      simp [hK_def] <;> ring
    rw [h_goal]
    have h_K_large_orig : K * ((4 : ℝ)^t * Real.rpow Δ (s - t - 132 * ε)) ≥ 2 := by
      have h_tmp := h.hK_large_weak
      rw [h_orig] at h_tmp
      exact h_tmp
    exact ge_trans h_main h_K_large_orig
  have h_absorb_K_extra' : (8 : ℝ) *
      (MainAppendix.affineLine_packing_constant : ℝ) *
      ((800 * (11 : ℝ)) : ℝ)^s *
      (MainAppendix.plane_packing_constant : ℝ)^3 *
      ((16 : ℝ) + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) *
      Real.rpow Δ (6 * ε) ≤ Real.rpow Δ (-ε) := by
    have h_denom_u : 0 < 1 - (2 : ℝ)^(s - u) := by
      have h2 : s - u < 0 := by linarith
      have h3 : (2 : ℝ)^(s - u) < 1 := by
        have h4 : (2 : ℝ)^(s - u) < (2 : ℝ)^(0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h2
        simpa using h4
      linarith
    have h_denom_t : 0 < 1 - (2 : ℝ)^(s - t) := by
      have h2 : s - t < 0 := by linarith
      have h3 : (2 : ℝ)^(s - t) < 1 := by
        have h4 : (2 : ℝ)^(s - t) < (2 : ℝ)^(0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h2
        simpa using h4
      linarith
    have h_frac_le : (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u)) ≤ (2 : ℝ)^s / (1 - (2 : ℝ)^(s - t)) := by
      have h_exp : s - u ≤ s - t := by linarith
      have h1 : (2 : ℝ)^(s - u) ≤ (2 : ℝ)^(s - t) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h_exp
      have h2 : 1 - (2 : ℝ)^(s - u) ≥ 1 - (2 : ℝ)^(s - t) := by linarith
      have h3 : 0 ≤ (2 : ℝ)^s := by positivity
      exact div_le_div_of_nonneg_left h3 (by linarith) h2
    have h_coeff_le : (16 : ℝ) + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u)) ≤
        (16 : ℝ) + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - t)) := by linarith
    have h_pos : 0 ≤ (8 : ℝ) * (MainAppendix.affineLine_packing_constant : ℝ) *
        ((800 * (11 : ℝ)) : ℝ)^s * (MainAppendix.plane_packing_constant : ℝ)^3 := by positivity
    have h_rpow6_pos : 0 ≤ Real.rpow Δ (6 * ε) := Real.rpow_nonneg hΔ_pos.le _
    have h_coeff_u_pos : 0 ≤ (16 : ℝ) + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u)) := by positivity
    have h_C_rpow_pos : 0 ≤ (8 : ℝ) * (MainAppendix.affineLine_packing_constant : ℝ) *
        ((800 * (11 : ℝ)) : ℝ)^s * (MainAppendix.plane_packing_constant : ℝ)^3 *
        Real.rpow Δ (6 * ε) := by positivity
    calc (8 : ℝ) * (MainAppendix.affineLine_packing_constant : ℝ) *
        ((800 * (11 : ℝ)) : ℝ)^s * (MainAppendix.plane_packing_constant : ℝ)^3 *
        ((16 : ℝ) + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) * Real.rpow Δ (6 * ε)
      = ((8 : ℝ) * (MainAppendix.affineLine_packing_constant : ℝ) *
          ((800 * (11 : ℝ)) : ℝ)^s * (MainAppendix.plane_packing_constant : ℝ)^3 *
          Real.rpow Δ (6 * ε)) *
        ((16 : ℝ) + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) := by ring
    _ ≤ ((8 : ℝ) * (MainAppendix.affineLine_packing_constant : ℝ) *
          ((800 * (11 : ℝ)) : ℝ)^s * (MainAppendix.plane_packing_constant : ℝ)^3 *
          Real.rpow Δ (6 * ε)) *
        ((16 : ℝ) + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - t))) := by
      gcongr
    _ = (8 : ℝ) * (MainAppendix.affineLine_packing_constant : ℝ) *
          ((800 * (11 : ℝ)) : ℝ)^s * (MainAppendix.plane_packing_constant : ℝ)^3 *
          ((16 : ℝ) + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - t))) * Real.rpow Δ (6 * ε) := by ring
    _ ≤ Real.rpow Δ (-ε) := h.h_absorb_K_extra
  exact ⟨h81_le', h.hΔ_small_A3, h.hΔ_absorb1, h_absorb2', h.hΔ_small_A4,
    h.hΔ_small_pack_A4, h.hK_bound, h.hΔ_3ε, h.h_small_half, h_small2',
    h.hΔ_small_A8, h.hΔ_cover_A9, h.hΔ_packing_A9, h.hΔ_small_A9,
    h.hΔ_coarse_absorb_A9, h.hΔ_fine_absorb_A9, h.hΔ_lt_1_16,
    h.h_absorb_shear, h.h_absorb_union, h.h_small_delta,
    hK_large_weak', h_absorb_K_extra', h.h_absorb_4s3ε, h.h_const_absorb_A7,
    h.h_absorb_4_dyadic, h.h_absorb_Kpack_dyadic⟩

end DirecretisedFurstenbergEstimate.AssemblyNumerical
