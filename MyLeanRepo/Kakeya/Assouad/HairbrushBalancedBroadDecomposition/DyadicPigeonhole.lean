import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Basic

/-!
# Dyadic pigeonhole lemma

Given masses indexed by scales in [δ, 1], find θ ∈ [δ, 1] such that the mass
in [θ/2, θ] is at least δ^eps times the total mass.
-/

namespace Kakeya.Assouad

/-- Helper: log(2^n) = n * log 2 for n : ℕ. -/
lemma log_two_pow (n : ℕ) : Real.log ((2 : ℝ)^n) = (n : ℝ) * Real.log 2 := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    have h_pos2 : (0 : ℝ) < (2 : ℝ)^n := by positivity
    have h_ne2 : (2 : ℝ)^n ≠ 0 := h_pos2.ne'
    have h_ne2' : (2 : ℝ) ≠ 0 := by norm_num
    calc Real.log ((2 : ℝ)^(n + 1))
      = Real.log ((2 : ℝ) * (2 : ℝ)^n) := by rw [pow_succ']
    _ = Real.log 2 + Real.log ((2 : ℝ)^n) := by
      rw [Real.log_mul h_ne2' h_ne2]
    _ = Real.log 2 + (n : ℝ) * Real.log 2 := by rw [ih]
    _ = ((n + 1 : ℕ) : ℝ) * Real.log 2 := by
      simp [add_mul]
      ring

/-- Every s ∈ [δ, 1] falls into some dyadic interval [(1/2)^{k+1}, (1/2)^k]
with k ≤ floor(log₂(1/δ)). -/
lemma dyadic_coverage {δ s : ℝ} (hδ : 0 < δ) (hδ_le1 : δ ≤ 1)
    (hsδ : δ ≤ s) (hs1 : s ≤ 1) :
    ∃ (k : ℕ), k ≤ Nat.floor (Real.log (1/δ) / Real.log 2) ∧
      (1/2 : ℝ)^(k+1) ≤ s ∧ s ≤ (1/2 : ℝ)^k := by
  have hs_pos : 0 < s := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_ne' : Real.log 2 ≠ 0 := hlog2_pos.ne'
  have h1s_ge1 : 1 ≤ 1 / s := by
    apply one_le_one_div <;> linarith
  have harg1_nonneg : 0 ≤ Real.log (1 / s) / Real.log 2 := by
    have h : 0 ≤ Real.log (1 / s) := Real.log_nonneg h1s_ge1
    positivity
  let k : ℕ := Nat.floor (Real.log (1 / s) / Real.log 2)
  have hk_le1 : (k : ℝ) ≤ Real.log (1 / s) / Real.log 2 := Nat.floor_le harg1_nonneg
  have hk_lt1 : Real.log (1 / s) / Real.log 2 < (k : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (Real.log (1 / s) / Real.log 2)
    exact h
  have h1δ_ge1 : 1 ≤ 1 / δ := by
    apply one_le_one_div <;> linarith
  have hargδ_nonneg : 0 ≤ Real.log (1 / δ) / Real.log 2 := by
    have h : 0 ≤ Real.log (1 / δ) := Real.log_nonneg h1δ_ge1
    positivity
  have h_kmax : k ≤ Nat.floor (Real.log (1 / δ) / Real.log 2) := by
    have h1 : Real.log (1 / s) ≤ Real.log (1 / δ) := by gcongr
    have h2 : Real.log (1 / s) / Real.log 2 ≤ Real.log (1 / δ) / Real.log 2 := by gcongr
    have h3 : (k : ℝ) ≤ Real.log (1 / δ) / Real.log 2 := hk_le1.trans h2
    exact Nat.floor_le_floor h2
  -- s ≤ (1/2)^k
  have h41 : (k : ℝ) * Real.log 2 ≤ Real.log (1 / s) := by
    have h : (k : ℝ) * Real.log 2 ≤ (Real.log (1 / s) / Real.log 2) * Real.log 2 := by gcongr
    have h' : (Real.log (1 / s) / Real.log 2) * Real.log 2 = Real.log (1 / s) := by
      field_simp [hlog2_ne']
    rw [h'] at h
    exact h
  have h42 : Real.log ((2 : ℝ)^k) ≤ Real.log (1 / s) := by
    rw [log_two_pow k]
    exact h41
  have h43 : (2 : ℝ)^k ≤ 1 / s := by
    by_contra h
    have h' : 1 / s < (2 : ℝ)^k := by linarith
    have h'' : Real.log (1 / s) < Real.log ((2 : ℝ)^k) := Real.log_lt_log (by positivity) h'
    linarith
  have h_pos2k : 0 < (2 : ℝ)^k := by positivity
  have h44 : s * (2 : ℝ)^k ≤ 1 := by
    have h : s * (2 : ℝ)^k ≤ s * (1 / s) := by gcongr
    have h' : s * (1 / s) = 1 := by
      field_simp [hs_pos.ne']
    rw [h'] at h
    exact h
  have h_ineq2 : s ≤ (1 / 2 : ℝ)^k := by
    have h5 : s ≤ 1 / (2 : ℝ)^k := by
      have h51 : s = s * (2 : ℝ)^k / (2 : ℝ)^k := by
        field_simp [h_pos2k.ne']
      rw [h51]
      gcongr
    have h6 : (1 / 2 : ℝ)^k = 1 / (2 : ℝ)^k := by
      simp
    rw [h6]
    exact h5
  -- (1/2)^(k+1) ≤ s
  have h51 : Real.log (1 / s) < ((k : ℝ) + 1) * Real.log 2 := by
    have h_eq : Real.log (1 / s) = (Real.log (1 / s) / Real.log 2) * Real.log 2 := by
      field_simp [hlog2_ne']
    rw [h_eq]
    gcongr
  have h51' : Real.log (1 / s) < ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
    have h_cast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by simp
    rw [h_cast]
    exact h51
  have h52 : Real.log (1 / s) < Real.log ((2 : ℝ)^(k + 1)) := by
    rw [log_two_pow (k + 1)]
    exact h51'
  have h53 : 1 / s < (2 : ℝ)^(k + 1) := by
    by_contra h
    have h' : (2 : ℝ)^(k + 1) ≤ 1 / s := by linarith
    have h_pos : 0 < (2 : ℝ)^(k + 1) := by positivity
    have h'' : Real.log ((2 : ℝ)^(k + 1)) ≤ Real.log (1 / s) :=
      Real.log_le_log (by positivity) h'
    linarith [h52, h'']
  have h_pos2k1 : 0 < (2 : ℝ)^(k + 1) := by positivity
  have h54 : 1 < s * (2 : ℝ)^(k + 1) := by
    have h : 1 = s * (1 / s) := by
      field_simp [hs_pos.ne']
    rw [h]
    gcongr
  have h55 : 1 / (2 : ℝ)^(k + 1) < s := by
    have h56 : 1 / (2 : ℝ)^(k + 1) < s * (2 : ℝ)^(k + 1) / (2 : ℝ)^(k + 1) := by
      apply div_lt_div_of_pos_right h54 h_pos2k1
    have h57 : s * (2 : ℝ)^(k + 1) / (2 : ℝ)^(k + 1) = s := by
      field_simp [h_pos2k1.ne']
    rw [h57] at h56
    exact h56
  have h_ineq1 : (1 / 2 : ℝ)^(k + 1) ≤ s := by
    have h58 : (1 / 2 : ℝ)^(k + 1) = 1 / (2 : ℝ)^(k + 1) := by simp
    rw [h58]
    exact h55.le
  exact ⟨k, h_kmax, h_ineq1, h_ineq2⟩

/-- Dyadic pigeonhole: find θ ∈ [δ,1] such that mass in [θ/2, θ] is at least
δ^eps times the total mass. -/
lemma dyadic_pigeonhole_scale {δ : ℝ} (hδ : 0 < δ) (hδ_le1 : δ ≤ 1)
    (N : ℕ) (mass : Fin N → ENNReal) (scale : Fin N → ℝ)
    (h_scales : ∀ i, δ ≤ scale i ∧ scale i ≤ 1)
    (total : ENNReal) (h_total : total ≤ ∑ i : Fin N, mass i)
    (eps : ℝ) (_heps : 0 < eps)
    (h_small : (δ ^ eps) * (Real.log (1/δ) / Real.log 2 + 1) ≤ 1) :
    ∃ theta : ℝ, δ ≤ theta ∧ theta ≤ 1 ∧
      (∃ k : ℕ, theta = (1 / 2 : ℝ) ^ k) ∧
      ENNReal.ofReal (δ ^ eps) * total ≤
        ∑ i : Fin N, (if theta/2 ≤ scale i ∧ scale i ≤ theta then mass i else 0) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_ne' : Real.log 2 ≠ 0 := hlog2_pos.ne'
  let K_max : ℕ := Nat.floor (Real.log (1/δ) / Real.log 2)
  let M : ℕ := K_max + 1
  have hM_pos : 0 < M := by positivity
  have hM_ne_zero : (M : ENNReal) ≠ 0 := by exact_mod_cast hM_pos.ne'
  have hM_ne_top : (M : ENNReal) ≠ ⊤ := by simp
  have h1δ_ge1 : 1 ≤ 1 / δ := by
    apply one_le_one_div <;> linarith
  have hargδ_nonneg : 0 ≤ Real.log (1/δ) / Real.log 2 := by
    have h : 0 ≤ Real.log (1/δ) := Real.log_nonneg h1δ_ge1
    positivity
  have hK_max_le : (K_max : ℝ) ≤ Real.log (1/δ) / Real.log 2 := Nat.floor_le hargδ_nonneg
  have hM_bound : (M : ℝ) ≤ Real.log (1/δ) / Real.log 2 + 1 := by
    simpa [M] using add_le_add_right hK_max_le 1
  let inInterval (k : ℕ) (s : ℝ) : Prop :=
    (1 / 2 : ℝ) ^ (k + 1) ≤ s ∧ s ≤ (1 / 2 : ℝ) ^ k
  let intervalMass (k : ℕ) : ENNReal :=
    ∑ i : Fin N, (if inInterval k (scale i) then mass i else 0)
  -- Coverage
  have h_cover : ∀ (i : Fin N), ∃ (k : ℕ), k ∈ Finset.range M ∧ inInterval k (scale i) := by
    intro i
    rcases dyadic_coverage hδ hδ_le1 (h_scales i).1 (h_scales i).2 with ⟨k, hk, h1, h2⟩
    refine ⟨k, ?_, h1, h2⟩
    simp only [Finset.mem_range, M]
    omega
  -- Sum of interval masses ≥ total mass
  have h_sum : ∑ i : Fin N, mass i ≤ ∑ k ∈ Finset.range M, intervalMass k := by
    have h_comm : ∑ k ∈ Finset.range M, intervalMass k =
        ∑ i : Fin N, ∑ k ∈ Finset.range M, (if inInterval k (scale i) then mass i else 0) := by
      simp only [intervalMass]
      rw [Finset.sum_comm]
    rw [h_comm]
    apply Finset.sum_le_sum
    intro i _
    rcases h_cover i with ⟨k_i, hk_i_in, hk_i1, hk_i2⟩
    let h_i_int : inInterval k_i (scale i) := ⟨hk_i1, hk_i2⟩
    let f : ℕ → ENNReal := fun k => if inInterval k (scale i) then mass i else 0
    have h2 : f k_i = mass i := by
      simp [f, h_i_int]
    have h3 : f k_i ≤ ∑ k ∈ Finset.range M, f k :=
      Finset.single_le_sum (fun _ _ => bot_le) hk_i_in
    rw [h2] at h3
    exact h3
  have h_total2 : total ≤ ∑ k ∈ Finset.range M, intervalMass k := le_trans h_total h_sum
  -- Find k maximizing intervalMass
  have hM_nonempty : (Finset.range M).Nonempty :=
    Finset.nonempty_range_iff.mpr hM_pos.ne'
  rcases Finset.exists_max_image (Finset.range M) intervalMass hM_nonempty with ⟨k0, hk0_in, hk0_max⟩
  have h_max : ∀ k ∈ Finset.range M, intervalMass k ≤ intervalMass k0 := by
    intro k hk
    exact hk0_max k hk
  have h_sum_le : ∑ k ∈ Finset.range M, intervalMass k ≤ (M : ENNReal) * intervalMass k0 := by
    have h : ∑ k ∈ Finset.range M, intervalMass k ≤ ∑ k ∈ Finset.range M, intervalMass k0 :=
      Finset.sum_le_sum fun k _ => h_max k ‹_›
    have h' : ∑ k ∈ Finset.range M, intervalMass k0 = (M : ENNReal) * intervalMass k0 := by
      simp [Finset.sum_const, Finset.card_range]
    calc ∑ k ∈ Finset.range M, intervalMass k
      ≤ ∑ k ∈ Finset.range M, intervalMass k0 := h
    _ = (M : ENNReal) * intervalMass k0 := h'
  have h_total3 : total ≤ (M : ENNReal) * intervalMass k0 := le_trans h_total2 h_sum_le
  -- Average bound
  have h_div : ((M : ENNReal) * intervalMass k0) / (M : ENNReal) = intervalMass k0 := by
    have h1 : ((M : ENNReal) * intervalMass k0) / (M : ENNReal) =
        ((M : ENNReal) * intervalMass k0) * (M : ENNReal)⁻¹ := by
      rw [div_eq_mul_inv]
    rw [h1]
    have h2 : ((M : ENNReal) * intervalMass k0) * (M : ENNReal)⁻¹ =
        (M : ENNReal) * (M : ENNReal)⁻¹ * intervalMass k0 := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    rw [h2]
    have h3 : (M : ENNReal) * (M : ENNReal)⁻¹ = 1 := ENNReal.mul_inv_cancel hM_ne_zero hM_ne_top
    rw [h3, one_mul]
  have h_avg : total / (M : ENNReal) ≤ intervalMass k0 := by
    have h : total / (M : ENNReal) ≤ ((M : ENNReal) * intervalMass k0) / (M : ENNReal) := by gcongr
    rw [h_div] at h
    exact h
  -- Convert h_small to ENNReal
  have hδeps_nonneg : 0 ≤ δ ^ eps := by positivity
  have hδeps_pos : 0 < δ ^ eps := Real.rpow_pos_of_pos hδ eps
  have hM_real : (M : ℝ) * (δ ^ eps) ≤ 1 := by
    have h : (M : ℝ) * (δ ^ eps) ≤ (Real.log (1/δ) / Real.log 2 + 1) * (δ ^ eps) := by gcongr
    have h' : (Real.log (1/δ) / Real.log 2 + 1) * (δ ^ eps) = (δ ^ eps) * (Real.log (1/δ) / Real.log 2 + 1) := by ring
    rw [h'] at h
    exact h.trans h_small
  have h_ofReal_mul : ∀ (n : ℕ), (n : ENNReal) * ENNReal.ofReal (δ ^ eps) =
      ENNReal.ofReal ((n : ℝ) * (δ ^ eps)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h_pos1 : 0 ≤ (n : ℝ) * (δ ^ eps) :=
        mul_nonneg (by positivity) hδeps_nonneg
      simp [Nat.cast_add, Nat.cast_one, add_mul, ENNReal.ofReal_add h_pos1 hδeps_nonneg] at ih ⊢
  have hM_ennreal : (M : ENNReal) * ENNReal.ofReal (δ ^ eps) ≤ 1 := by
    have h7 := h_ofReal_mul M
    rw [h7]
    exact ENNReal.ofReal_le_one.mpr hM_real
  have h8 : ENNReal.ofReal (δ ^ eps) ≤ (M : ENNReal)⁻¹ := by
    have h9 : (M : ENNReal) * ENNReal.ofReal (δ ^ eps) ≤ 1 := hM_ennreal
    have h10 : (M : ENNReal)⁻¹ * ((M : ENNReal) * ENNReal.ofReal (δ ^ eps)) ≤ (M : ENNReal)⁻¹ * 1 := by gcongr
    have h11 : (M : ENNReal)⁻¹ * ((M : ENNReal) * ENNReal.ofReal (δ ^ eps)) =
        ENNReal.ofReal (δ ^ eps) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hM_ne_zero hM_ne_top, one_mul]
    rw [h11] at h10
    simpa using h10
  have h11 : ENNReal.ofReal (δ ^ eps) * total ≤ (M : ENNReal)⁻¹ * total := by gcongr
  have h12 : (M : ENNReal)⁻¹ * total = total * (M : ENNReal)⁻¹ := by exact mul_comm _ _
  have h13 : total * (M : ENNReal)⁻¹ = total / (M : ENNReal) := by rw [div_eq_mul_inv]
  have h14 : ENNReal.ofReal (δ ^ eps) * total ≤ intervalMass k0 :=
    le_trans h11 (le_trans (by rw [h12, h13]) h_avg)
  -- Set theta = (1/2)^k0
  let theta : ℝ := (1 / 2 : ℝ) ^ k0
  have h_k0_le_Kmax : k0 ≤ K_max := by
    simp only [Finset.mem_range, M] at hk0_in
    omega
  have h_theta1 : theta ≤ 1 := by
    have h : (1/2 : ℝ)^k0 ≤ (1/2 : ℝ)^0 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.zero_le k0)
    simpa [theta] using h
  have h_thetaδ : δ ≤ theta := by
    have h2 : (1/2 : ℝ)^K_max ≤ (1/2 : ℝ)^k0 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h_k0_le_Kmax
    have h3 : (1/2 : ℝ)^K_max ≥ δ := by
      have h4 : (K_max : ℝ) * Real.log 2 ≤ Real.log (1/δ) := by
        have h41 : (K_max : ℝ) * Real.log 2 ≤ (Real.log (1/δ) / Real.log 2) * Real.log 2 := by gcongr
        have h42 : (Real.log (1/δ) / Real.log 2) * Real.log 2 = Real.log (1/δ) := by
          field_simp [hlog2_ne']
        rw [h42] at h41
        exact h41
      have h5 : Real.log ((2 : ℝ)^K_max) ≤ Real.log (1/δ) := by
        rw [log_two_pow K_max]
        exact h4
      have h7 : (2 : ℝ)^K_max ≤ 1/δ := by
        by_contra h
        have h' : 1/δ < (2 : ℝ)^K_max := by linarith
        have h'' : Real.log (1/δ) < Real.log ((2 : ℝ)^K_max) := Real.log_lt_log (by positivity) h'
        linarith
      have h_pos : 0 < (2 : ℝ)^K_max := by positivity
      have h8 : δ * (2 : ℝ)^K_max ≤ 1 := by
        have h81 : δ * (2 : ℝ)^K_max ≤ δ * (1/δ) := by gcongr
        have h82 : δ * (1/δ) = 1 := by field_simp [hδ.ne']
        rw [h82] at h81
        exact h81
      have h9 : δ ≤ 1 / (2 : ℝ)^K_max := by
        have h91 : δ = δ * (2 : ℝ)^K_max / (2 : ℝ)^K_max := by
          field_simp [h_pos.ne']
        rw [h91]
        gcongr
      have h10 : (1/2 : ℝ)^K_max = 1 / (2 : ℝ)^K_max := by simp
      rw [h10]
      exact h9
    calc theta
      = (1/2 : ℝ)^k0 := rfl
    _ ≥ (1/2 : ℝ)^K_max := h2
    _ ≥ δ := h3
  have h_final : intervalMass k0 =
      ∑ i : Fin N, (if theta/2 ≤ scale i ∧ scale i ≤ theta then mass i else 0) := by
    have h15 : theta / 2 = (1 / 2 : ℝ) ^ (k0 + 1) := by
      simp [theta, pow_succ]
      ring
    simp only [intervalMass, inInterval, h15]
    rfl
  refine ⟨theta, h_thetaδ, h_theta1, ⟨k0, rfl⟩, ?_⟩
  have h_goal : ENNReal.ofReal (δ ^ eps) * total ≤ intervalMass k0 := h14
  have h_eq : intervalMass k0 = ∑ i : Fin N, (if theta/2 ≤ scale i ∧ scale i ≤ theta then mass i else 0) := h_final
  rw [h_eq] at h_goal
  exact h_goal

/--
General finite pigeonhole: given masses indexed by `Fin N` assigned to bins
`Fin K`, there exists a bin containing at least `1/K` of the total mass.
-/
lemma finset_pigeonhole_mass
    {N K : ℕ} (hN : 0 < N) (hK : 0 < K)
    (mass : Fin N → ENNReal)
    (bin : Fin N → Fin K)
    (total : ENNReal)
    (h_total : total ≤ ∑ i, mass i) :
    ∃ (k : Fin K),
      total / (K : ENNReal) ≤ ∑ i : Fin N, (if bin i = k then mass i else 0) := by
  let binMass : Fin K → ENNReal := fun k =>
    ∑ i : Fin N, (if bin i = k then mass i else 0)
  have h_sum : ∑ k : Fin K, binMass k = ∑ i : Fin N, mass i := by
    simp only [binMass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    let f : Fin K → ENNReal := fun k => if bin i = k then mass i else 0
    have h_f : ∀ b ∈ Finset.univ, b ≠ bin i → f b = 0 := by
      intro b _ hne
      have h4 : bin i ≠ b := hne.symm
      simp [f, h4]
    have h_main : ∑ k : Fin K, f k = f (bin i) :=
      Finset.sum_eq_single_of_mem (bin i) (Finset.mem_univ _) h_f
    have h_f_val : f (bin i) = mass i := by simp [f]
    rw [h_main, h_f_val]
  have h_total2 : total ≤ ∑ k : Fin K, binMass k := by
    rw [h_sum] at *
    exact h_total
  have hK_nonempty : (Finset.univ : Finset (Fin K)).Nonempty :=
    ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  rcases Finset.exists_max_image (Finset.univ : Finset (Fin K)) binMass hK_nonempty with
    ⟨k0, _hk0_in, hk0_max⟩
  have h_max : ∀ k : Fin K, binMass k ≤ binMass k0 := by
    intro k
    exact hk0_max k (Finset.mem_univ k)
  have h_sum_le : ∑ k : Fin K, binMass k ≤ (K : ENNReal) * binMass k0 := by
    have h : ∑ k : Fin K, binMass k ≤ ∑ k : Fin K, binMass k0 :=
      Finset.sum_le_sum fun k _ => h_max k
    have h' : ∑ k : Fin K, binMass k0 = (K : ENNReal) * binMass k0 := by
      simp [Finset.sum_const]
    calc
      ∑ k : Fin K, binMass k ≤ ∑ k : Fin K, binMass k0 := h
      _ = (K : ENNReal) * binMass k0 := h'
  have h_total3 : total ≤ (K : ENNReal) * binMass k0 :=
    le_trans h_total2 h_sum_le
  have hK_ne_zero : (K : ENNReal) ≠ 0 := by exact_mod_cast hK.ne'
  have hK_ne_top : (K : ENNReal) ≠ ⊤ := by simp
  have h_div : ((K : ENNReal) * binMass k0) / (K : ENNReal) = binMass k0 := by
    rw [div_eq_mul_inv]
    have h2 : ((K : ENNReal) * binMass k0) * (K : ENNReal)⁻¹ =
        (K : ENNReal) * (K : ENNReal)⁻¹ * binMass k0 := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    rw [h2]
    have h3 : (K : ENNReal) * (K : ENNReal)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel hK_ne_zero hK_ne_top
    rw [h3, one_mul]
  have h_avg : total / (K : ENNReal) ≤ binMass k0 := by
    have h : total / (K : ENNReal) ≤ ((K : ENNReal) * binMass k0) / (K : ENNReal) := by
      gcongr
    rw [h_div] at h
    exact h
  exact ⟨k0, h_avg⟩

/--
Every positive natural number `n < 2^K` falls into a unique dyadic bin
`[2^k, 2^(k+1))` for some `k < K`.
-/
lemma nat_dyadic_bin_exists (n K : ℕ) (hn_pos : 0 < n) (hK : n < 2^K) :
    ∃ (k : ℕ), k < K ∧ 2^k ≤ n ∧ n < 2^(k+1) := by
  let k : ℕ := Nat.log 2 n
  have h1 : 2^k ≤ n := Nat.pow_log_le_self 2 hn_pos.ne'
  have h2 : n < 2^(k+1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h3 : k < K := by
    by_contra h
    have h4 : K ≤ k := by omega
    have h5 : 2^K ≤ 2^k := by
      gcongr
      norm_num
    have h6 : 2^K ≤ n := le_trans h5 h1
    omega
  exact ⟨k, h3, h1, h2⟩

/--
Every real `x ∈ [floor, 1]` with `2^K * floor > 1` falls into a dyadic bin
`[2^l * floor, 2^(l+1) * floor)` for some `l < K`.
-/
lemma real_dyadic_bin_with_floor
    (x floor : ℝ) (hfloor_pos : 0 < floor) (hx_floor : floor ≤ x) (hx_one : x ≤ 1)
    (K : ℕ) (hK : 2^K * floor > 1) :
    ∃ (l : ℕ), l < K ∧ (2^l : ℝ) * floor ≤ x ∧ x < (2^(l+1) : ℝ) * floor := by
  set y : ℝ := x / floor with hy_def
  have hy_nonneg : 0 ≤ y := by
    rw [hy_def]
    have hx_pos : 0 < x := by linarith
    positivity
  have hy1 : 1 ≤ y := by
    rw [hy_def]
    have h : floor ≤ x := hx_floor
    have h' : 1 ≤ x / floor := by
      calc 1 = floor / floor := by field_simp [hfloor_pos.ne']
      _ ≤ x / floor := by gcongr
    exact h'
  have hy2 : y < (2^K : ℝ) := by
    rw [hy_def]
    have h : x < (2^K : ℝ) * floor := by linarith
    have h' : x / floor < (2^K : ℝ) := by
      calc x / floor < ((2^K : ℝ) * floor) / floor := by gcongr
      _ = (2^K : ℝ) := by field_simp [hfloor_pos.ne']
    exact h'
  have h_floor_y_pos : 0 < Nat.floor y := by
    apply Nat.floor_pos.mpr
    linarith
  let l : ℕ := Nat.log 2 (Nat.floor y)
  have h1 : (2^l : ℝ) ≤ y := by
    have h11 : 2^l ≤ Nat.floor y := Nat.pow_log_le_self 2 h_floor_y_pos.ne'
    have h12 : (Nat.floor y : ℝ) ≤ y := Nat.floor_le hy_nonneg
    have h13 : (2^l : ℝ) ≤ (Nat.floor y : ℝ) := by exact_mod_cast h11
    exact le_trans h13 h12
  have h2 : y < (2^(l+1) : ℝ) := by
    have h21 : Nat.floor y < 2^(l+1) :=
      Nat.lt_pow_succ_log_self (by norm_num) (Nat.floor y)
    have h22 : y < (Nat.floor y + 1 : ℝ) := Nat.lt_floor_add_one y
    have h23 : (Nat.floor y + 1 : ℕ) ≤ 2^(l+1) := Nat.succ_le_iff.mpr h21
    have h24 : (Nat.floor y : ℝ) + 1 ≤ (2^(l+1) : ℝ) := by
      exact_mod_cast h23
    calc y < (Nat.floor y + 1 : ℝ) := h22
      _ ≤ (2^(l+1) : ℝ) := h24
  have h3 : l < K := by
    have h31 : (Nat.floor y : ℝ) ≤ y := Nat.floor_le hy_nonneg
    have h32 : (Nat.floor y : ℝ) < (2^K : ℝ) := by linarith
    have h33 : Nat.floor y < 2^K := by exact_mod_cast h32
    by_contra h
    have h4 : K ≤ l := by omega
    have h5 : 2^K ≤ 2^l := by
      gcongr
      norm_num
    have h6 : 2^K ≤ Nat.floor y :=
      le_trans h5 (Nat.pow_log_le_self 2 h_floor_y_pos.ne')
    omega
  have h_y_mul : y * floor = x := by
    rw [hy_def]
    field_simp [hfloor_pos.ne']
  have h4 : (2^l : ℝ) * floor ≤ x := by
    have h : (2^l : ℝ) * floor ≤ y * floor := by gcongr
    rw [h_y_mul] at h
    exact h
  have h5 : x < (2^(l+1) : ℝ) * floor := by
    have h : y * floor < (2^(l+1) : ℝ) * floor := by gcongr
    rw [h_y_mul] at h
    exact h
  exact ⟨l, h3, h4, h5⟩

/--
Generic dyadic bin count bound. For `exponent > 0` and `0 < δ ≤ 1`, setting
`K := Nat.floor (exponent * log(1/δ) / log 2) + 1` gives `0 < K`,
`(K : ℝ) ≤ exponent * log(1/δ) / log 2 + 1`, and `2^K > δ^(-exponent)`.
-/
lemma dyadic_K_bound
    (exponent : ℝ) (hexponent_pos : 0 < exponent)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let K : ℕ := Nat.floor (exponent * Real.log (1/δ) / Real.log 2) + 1
    0 < K ∧
    (K : ℝ) ≤ exponent * Real.log (1/δ) / Real.log 2 + 1 ∧
    (2 : ℝ)^K > δ^(-exponent) := by
  set x : ℝ := exponent * Real.log (1/δ) / Real.log 2 with hx_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1δ_nonneg : 0 ≤ Real.log (1/δ) := by
    have h : 1 ≤ 1/δ := by
      apply one_le_one_div <;> linarith
    exact Real.log_nonneg h
  have hx_nonneg : 0 ≤ x := by
    rw [hx_def] <;> positivity
  set K : ℕ := Nat.floor x + 1 with hK_def
  have h1 : 0 < K := by
    rw [hK_def]
    have h_floor_nonneg : 0 ≤ Nat.floor x := by positivity
    omega
  have h2 : (K : ℝ) ≤ x + 1 := by
    rw [hK_def]
    have h : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx_nonneg
    have h' : ((Nat.floor x + 1 : ℕ) : ℝ) = (Nat.floor x : ℝ) + 1 := by simp
    rw [h']
    linarith
  have h3 : (x : ℝ) < (K : ℝ) := by
    rw [hK_def]
    have h : x < (Nat.floor x : ℝ) + 1 := by
      by_contra h'
      have h'' : (Nat.floor x + 1 : ℝ) ≤ x := by linarith
      have h_cast : ((Nat.floor x + 1 : ℕ) : ℝ) ≤ x := by
        simpa using h''
      have h3 : Nat.floor x + 1 ≤ Nat.floor x := Nat.le_floor h_cast
      omega
    have h' : ((Nat.floor x + 1 : ℕ) : ℝ) = (Nat.floor x : ℝ) + 1 := by simp
    rw [h']
    exact h
  have h4 : (2 : ℝ)^x < (2 : ℝ)^K := by
    have hlog : Real.log ((2 : ℝ)^x) < Real.log ((2 : ℝ)^K) := by
      have h1 : Real.log ((2 : ℝ)^x) = x * Real.log 2 := Real.log_rpow (by norm_num) _
      have h2 : Real.log ((2 : ℝ)^K) = (K : ℝ) * Real.log 2 := by
        simpa [Real.log_pow] using by ring
      rw [h1, h2]
      exact mul_lt_mul_of_pos_right h3 hlog2_pos
    have hpos1 : 0 < (2 : ℝ)^x := Real.rpow_pos_of_pos (by norm_num) _
    have hpos2 : 0 < (2 : ℝ)^K := by positivity
    exact (Real.log_lt_log_iff hpos1 hpos2).mp hlog
  have h5 : (2 : ℝ)^x = δ^(-exponent) := by
    have h6 : Real.log ((2 : ℝ)^x) = Real.log (δ^(-exponent)) := by
      calc
        Real.log ((2 : ℝ)^x)
          = x * Real.log 2 := Real.log_rpow (by norm_num) _
        _ = exponent * Real.log (1/δ) := by
          rw [hx_def]
          field_simp [hlog2_pos.ne'] <;> ring
        _ = Real.log (δ^(-exponent)) := by
          have h7 : Real.log (δ^(-exponent)) = -exponent * Real.log δ := by
            rw [Real.log_rpow (by linarith)] <;> ring
          rw [h7]
          have h8 : Real.log (1/δ) = -Real.log δ := by
            rw [Real.log_div (by norm_num) (by linarith)] <;> simp
          rw [h8] <;> ring
    have h_pos1 : 0 < (2 : ℝ)^x := Real.rpow_pos_of_pos (by norm_num) _
    have h_pos2 : 0 < δ^(-exponent) := by positivity
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr h_pos1) (Set.mem_Ioi.mpr h_pos2) h6
  have h6 : (2 : ℝ)^K > δ^(-exponent) := by
    have h7 : (2 : ℝ)^x < (2 : ℝ)^K := h4
    rw [h5] at h7
    exact h7
  exact ⟨h1, h2, h6⟩

/--
Product bound: if `log(1/δ) ≥ 1`, then the product of two dyadic bin counts
is bounded by a constant times `(log(1/δ))^2`.
-/
lemma dyadic_K_product_bound
    (cardExponent densityFloor : ℝ)
    (hcard_pos : 0 < cardExponent) (hdens_pos : 0 < densityFloor)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hL_ge_one : 1 ≤ Real.log (1/δ)) :
    let K_card := Nat.floor (cardExponent * Real.log (1/δ) / Real.log 2) + 1
    let K_density := Nat.floor (densityFloor * Real.log (1/δ) / Real.log 2) + 1
    (K_card * K_density : ℝ) ≤
      ((cardExponent / Real.log 2 + 1) * (densityFloor / Real.log 2 + 1)) *
        (Real.log (1/δ))^2 := by
  set L : ℝ := Real.log (1/δ) with hL_def
  set x : ℝ := cardExponent * L / Real.log 2 with hx_def
  set y : ℝ := densityFloor * L / Real.log 2 with hy_def
  set K_card : ℕ := Nat.floor x + 1 with hKcard_def
  set K_density : ℕ := Nat.floor y + 1 with hKdens_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx_nonneg : 0 ≤ x := by rw [hx_def] <;> positivity
  have hy_nonneg : 0 ≤ y := by rw [hy_def] <;> positivity
  have hKcard_le : (K_card : ℝ) ≤ x + 1 := by
    rw [hKcard_def]
    have h : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx_nonneg
    have h' : ((Nat.floor x + 1 : ℕ) : ℝ) = (Nat.floor x : ℝ) + 1 := by simp
    rw [h']
    linarith
  have hKdens_le : (K_density : ℝ) ≤ y + 1 := by
    rw [hKdens_def]
    have h : (Nat.floor y : ℝ) ≤ y := Nat.floor_le hy_nonneg
    have h' : ((Nat.floor y + 1 : ℕ) : ℝ) = (Nat.floor y : ℝ) + 1 := by simp
    rw [h']
    linarith
  have hL_pos : 0 < L := by linarith
  have h_x_le : x + 1 ≤ (cardExponent / Real.log 2 + 1) * L := by
    have h_goal : cardExponent * L / Real.log 2 + 1 ≤ (cardExponent / Real.log 2 + 1) * L := by
      have h_eq : (cardExponent / Real.log 2 + 1) * L = cardExponent * L / Real.log 2 + L := by ring
      rw [h_eq]
      linarith [hL_ge_one]
    simpa [hx_def] using h_goal
  have h_y_le : y + 1 ≤ (densityFloor / Real.log 2 + 1) * L := by
    have h_goal : densityFloor * L / Real.log 2 + 1 ≤ (densityFloor / Real.log 2 + 1) * L := by
      have h_eq : (densityFloor / Real.log 2 + 1) * L = densityFloor * L / Real.log 2 + L := by ring
      rw [h_eq]
      linarith [hL_ge_one]
    simpa [hy_def] using h_goal
  calc
    (K_card * K_density : ℝ)
      = (K_card : ℝ) * (K_density : ℝ) := by simp
    _ ≤ (x + 1) * (y + 1) := by gcongr
    _ ≤ ((cardExponent / Real.log 2 + 1) * L) *
           ((densityFloor / Real.log 2 + 1) * L) := by gcongr
    _ = ((cardExponent / Real.log 2 + 1) * (densityFloor / Real.log 2 + 1)) * L^2 := by ring

end Kakeya.Assouad
