module

/-
Energy averaging for robust Kaufman projection (regularized kernel).

Uses K_δ(d) = min(|d|^{-s}, δ^{-s}) to eliminate the singularity when a
discrete direction falls close to the singular projection direction.

Per-pair bound:
  ∑_{σ∈S} K_δ(|π_σ(v)|) ≤ C * |S| * log(4/δ) * ‖v‖^{-s}

Averaging theorem:
  ∑_{σ∈S} projectedEnergyReg ≤ C * |S| * log(4/δ) * planeEnergy
-/

public import MyLeanRepo.OSWPrelude
public import MyLeanRepo.robust_kaufman_projection.Base

@[expose] public section

open MeasureTheory Metric Set Finset
open scoped ENNReal NNReal

namespace RobustKaufmanProjection.EnergyAveraging

noncomputable section

variable {s : ℝ}

/-! ### Definitions -/

/-- Regularized Riesz kernel (real-valued): min(|d|^{-s}, δ^{-s}) for d ≠ 0, 0 for d = 0. -/
def regularizedKernelReal (s δ : ℝ) (d : ℝ) : ℝ :=
  if d = 0 then 0 else min (|d| ^ (-s)) (δ ^ (-s))

/-- For d ≠ 0, regularizedKernelReal equals min(|d|^{-s}, δ^{-s}). -/
lemma regularizedKernelReal_eq_min {s δ d : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hd : d ≠ 0) :
  regularizedKernelReal s δ d = min (|d| ^ (-s)) (δ ^ (-s)) := by
  rw [regularizedKernelReal, if_neg hd]

/-- Regularized Riesz kernel (ENNReal). -/
def regularizedKernel (s δ : ℝ) (d : ℝ) : ENNReal :=
  ENNReal.ofReal (regularizedKernelReal s δ d)

/-- Plane Riesz kernel: ‖x-y‖^{-s} for x ≠ y, 0 otherwise. -/
def planeKernel (s : ℝ) (x y : EuclideanPlane) : ENNReal :=
  if x = y then 0 else ENNReal.ofReal (‖x - y‖ ^ (-s))

/-- Regularized projected Riesz kernel in direction σ. Pair-aware: 0 for x=y, else max(|πσ(x-y)|, δ)^{-s}. -/
def projectedKernelReg (s δ : ℝ) (σ : ℝ) (x y : EuclideanPlane) : ENNReal :=
  if x = y then 0 else
    ENNReal.ofReal ((max |(x 0 - σ * x 1) - (y 0 - σ * y 1)| δ) ^ (-s))

/-- projectedKernelReg for x ≠ y simplifies to max(|πσ(x-y)|, δ)^{-s}. -/
lemma projectedKernelReg_of_ne {s δ σ : ℝ} {x y : EuclideanPlane} (h : x ≠ y) :
  projectedKernelReg s δ σ x y = ENNReal.ofReal ((max |(x 0 - σ * x 1) - (y 0 - σ * y 1)| δ) ^ (-s)) :=
  by rw [projectedKernelReg, if_neg h]

/-- For d ≠ 0, (max |d| δ)^(-s) = regularizedKernelReal s δ d. -/
lemma max_rpow_eq_regularized {s δ d : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hd : d ≠ 0) :
  (max |d| δ) ^ (-s) = regularizedKernelReal s δ d := by
  rw [regularizedKernelReal_eq_min hs hδ hd]
  by_cases h : |d| ≤ δ
  · have h2 : max |d| δ = δ := by
      rw [max_eq_right h]
    rw [h2]
    have h3 : δ ^ (-s) ≤ |d| ^ (-s) := Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hd) h (by linarith)
    rw [min_eq_right h3]
  · have h2 : |d| > δ := by linarith
    have h3 : max |d| δ = |d| := by rw [max_eq_left] <;> linarith
    rw [h3]
    have h4 : |d| ^ (-s) ≤ δ ^ (-s) := Real.rpow_le_rpow_of_nonpos hδ (by linarith) (by linarith)
    rw [min_eq_left h4]

/-- Measurability of planeKernel in the second argument. -/
lemma planeKernel_measurable {s : ℝ} {x : EuclideanPlane} :
    Measurable (fun y : EuclideanPlane => planeKernel s x y) := by
  have h1 : MeasurableSet {y : EuclideanPlane | x = y} := by
    simpa [Set.mem_singleton_iff, eq_comm] using measurableSet_singleton x
  have h2 : Measurable (fun y : EuclideanPlane => ‖x - y‖ ^ (-s)) := by
    have h21 : Measurable (fun y => ‖x - y‖) := by fun_prop
    have h22 : Measurable (fun (_ : EuclideanPlane) => (-s : ℝ)) := measurable_const
    have h_rpow : Measurable (fun q : ℝ × ℝ => q.1 ^ q.2) := by exact measurable_pow
    have h_pair : Measurable (fun y : EuclideanPlane => (‖x - y‖, -s)) := by fun_prop
    exact h_rpow.comp h_pair
  have h3 : Measurable (fun y : EuclideanPlane => ENNReal.ofReal (‖x - y‖ ^ (-s))) :=
    ENNReal.measurable_ofReal.comp h2
  have h_then : Measurable (fun (_ : EuclideanPlane) => (0 : ENNReal)) := by exact measurable_const
  exact Measurable.ite h1 h_then h3

/-- Plane s-energy. -/
def planeEnergy (μ : Measure EuclideanPlane) (s : ℝ) : ENNReal :=
  ∫⁻ x, ∫⁻ y, planeKernel s x y ∂μ ∂μ

/-- Regularized projected s-energy in direction σ. -/
def projectedEnergyReg (μ : Measure EuclideanPlane) (s δ : ℝ) (σ : ℝ) : ENNReal :=
  ∫⁻ x, ∫⁻ y, projectedKernelReg s δ σ x y ∂μ ∂μ

/-! ### Utility lemmas -/

private lemma log4_ge_two {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) :
    2 ≤ Real.log (4 / δ) / Real.log 2 := by
  have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : 4 / δ ≥ 4 := by
    have h3 : 0 < δ := hδ
    have h4 : δ ≤ 1 := hδ_le_one
    calc 4 / δ ≥ 4 / 1 := by gcongr
      _ = 4 := by norm_num
  have h5 : Real.log (4 / δ) ≥ Real.log 4 := Real.log_le_log (by positivity) h2
  have h6 : Real.log 4 = 2 * Real.log 2 := by
    have h7 : Real.log 4 = Real.log (2 ^ 2) := by norm_num
    rw [h7, Real.log_pow] <;> norm_num
  rw [h6] at h5
  calc Real.log (4 / δ) / Real.log 2
    ≥ (2 * Real.log 2) / Real.log 2 := by gcongr
    _ = 2 := by
      field_simp [h1.ne'] <;> ring

private lemma log4_ge_one {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) :
    1 ≤ Real.log (4 / δ) := by
  have h1 : 4 / δ ≥ 4 := by
    have h2 : 0 < δ := hδ
    have h3 : δ ≤ 1 := hδ_le_one
    calc 4 / δ ≥ 4 / 1 := by gcongr
      _ = 4 := by norm_num
  have h4 : Real.log (4 / δ) ≥ Real.log 4 := Real.log_le_log (by positivity) h1
  have h5 : (1 : ℝ) ≤ Real.log 4 := by
    have h6 : Real.exp 1 < (4 : ℝ) := by
      have h7 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
      linarith
    have h8 : Real.log (Real.exp 1) ≤ Real.log 4 := Real.log_le_log (by positivity) (le_of_lt h6)
    simpa using h8
  linarith

private lemma sqrt3_gt_one : 1 < Real.sqrt 3 := by
  have h : (1 : ℝ)^2 < (3 : ℝ) := by norm_num
  exact Real.lt_sqrt_of_sq_lt h

private lemma norm_v_rpow (v₀ v₁ : ℝ) (s : ℝ) (hs : 0 < s) :
    (Real.sqrt (v₀^2 + v₁^2)) ^ (-s) = (v₀^2 + v₁^2)^(-s/2) := by
  set x := v₀^2 + v₁^2 with hx
  have h2 : 0 ≤ x := by positivity
  by_cases hx0 : x = 0
  · have hsqrt : Real.sqrt x = 0 := by
      rw [hx0]
      simp
    rw [hsqrt]
    have hns : -s ≠ 0 := by linarith
    have hns2 : -s / 2 ≠ 0 := by linarith
    have h_goal : (0 : ℝ) ^ (-s) = (0 : ℝ) ^ (-s / 2) := by
      rw [Real.zero_rpow hns, Real.zero_rpow hns2]
    simpa [hx0] using h_goal
  · have hx_pos : 0 < x := by
      apply lt_of_le_of_ne h2
      intro h
      exact hx0 h.symm
    have h3 : Real.log (Real.sqrt x) = (1 / 2 : ℝ) * Real.log x := by
      rw [Real.log_sqrt h2] <;> ring
    have h4 : (Real.sqrt x) ^ (-s) = Real.exp ((-s) * Real.log (Real.sqrt x)) := by
      rw [Real.rpow_def_of_pos (Real.sqrt_pos.mpr hx_pos)]
      <;> ring_nf
    rw [h4, h3]
    have h5 : (-s) * ((1 / 2 : ℝ) * Real.log x) = (-s / 2) * Real.log x := by ring
    rw [h5]
    have h6 : x ^ (-s / 2) = Real.exp ((-s / 2) * Real.log x) := by
      rw [Real.rpow_def_of_pos hx_pos] <;> ring_nf
    exact h6.symm

private lemma half_rpow_algebra {x : ℝ} (hx : 0 < x) (s : ℝ) :
    (x / 2)^(-s) = (2 : ℝ)^s * x^(-s) := by
  rw [Real.div_rpow (by positivity) (by positivity)]
  have h1 : (2 : ℝ)^(-s) ≠ 0 := by positivity
  have h2 : ((2 : ℝ)^(-s))⁻¹ = (2 : ℝ)^s := by
    have h3 : (2 : ℝ)^(-s) * (2 : ℝ)^s = 1 := by
      rw [← Real.rpow_add (by norm_num)] <;> ring_nf <;> norm_num
    field_simp [h1] <;> linarith
  rw [div_eq_mul_inv, h2] <;> ring

/-! ### Dyadic power helper -/

private lemma exists_k_pow_near {a r₀ : ℝ} (hr₀ : 0 < r₀) (ha : r₀ ≤ a) {K : ℕ}
    (hK : a < (2^K : ℝ) * r₀) :
    ∃ k : ℕ, k < K ∧ (2^k : ℝ) * r₀ ≤ a ∧ a < (2^(k+1) : ℝ) * r₀ := by
  let x := a / r₀
  have h_eq : x * r₀ = a := by simp [x] <;> field_simp [hr₀.ne'] <;> ring
  have hx1 : 1 ≤ x := by
    have h2 : 1 * r₀ ≤ x * r₀ := by
      rw [one_mul, h_eq] <;> linarith
    nlinarith
  have hx2 : x < (2^K : ℝ) := by
    have h2 : x * r₀ < (2^K : ℝ) * r₀ := by
      have h3 : x * r₀ = a := h_eq
      rw [h3]; exact hK
    have h_iff : (x * r₀ < (2^K : ℝ) * r₀) ↔ (x < (2^K : ℝ)) := by exact mul_lt_mul_iff_of_pos_right hr₀
    exact h_iff.mp h2
  have hx_pos : 0 < x := by linarith
  let k := Nat.floor (Real.log x / Real.log 2)
  have hlp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_nonneg : 0 ≤ Real.log x / Real.log 2 := by
    have h1 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    positivity
  have hk1 : (k : ℝ) ≤ Real.log x / Real.log 2 := Nat.floor_le h_nonneg
  have hk2 : Real.log x / Real.log 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have h_log2k : Real.log ((2^k : ℝ)) = (k : ℝ) * Real.log 2 := by
    rw [Real.log_pow] <;> ring
  have h_log2k1 : Real.log ((2^(k+1) : ℝ)) = ((k : ℝ) + 1) * Real.log 2 := by
    rw [Real.log_pow]
    <;> simp [Nat.cast_add] <;> ring
  have h5 : (k : ℝ) * Real.log 2 ≤ Real.log x := by
    have h51 : (k : ℝ) ≤ Real.log x / Real.log 2 := hk1
    have h52 : (k : ℝ) * Real.log 2 ≤ (Real.log x / Real.log 2) * Real.log 2 := by gcongr
    have h53 : (Real.log x / Real.log 2) * Real.log 2 = Real.log x := by
      field_simp [hlp.ne'] <;> ring
    rw [h53] at h52; exact h52
  have h6 : Real.log x < ((k : ℝ) + 1) * Real.log 2 := by
    have h61 : Real.log x / Real.log 2 < (k : ℝ) + 1 := hk2
    have h62 : Real.log x < ((k : ℝ) + 1) * Real.log 2 := by
      calc Real.log x
        = (Real.log x / Real.log 2) * Real.log 2 := by field_simp [hlp.ne'] <;> ring
      _ < ((k : ℝ) + 1) * Real.log 2 := by gcongr
    exact h62
  have hkp : (2^k : ℝ) ≤ x := by
    have hpos1 : 0 < (2^k : ℝ) := by positivity
    have h : Real.log ((2^k : ℝ)) ≤ Real.log x := by
      rw [h_log2k] <;> exact h5
    exact (Real.log_le_log_iff hpos1 hx_pos).mp h
  have hkp2 : x < (2^(k+1) : ℝ) := by
    have hpos2 : 0 < (2^(k+1) : ℝ) := by positivity
    have h : Real.log x < Real.log ((2^(k+1) : ℝ)) := by
      rw [h_log2k1] <;> exact h6
    exact (Real.log_lt_log_iff hx_pos hpos2).mp h
  have hkK : k < K := by
    by_contra h
    have h' : K ≤ k := by omega
    have h'' : (2^K : ℝ) ≤ (2^k : ℝ) := by
      gcongr <;> norm_num
    have h3 : (2^k : ℝ) ≤ x := hkp
    linarith
  have h6' : (2^k : ℝ) * r₀ ≤ a := by
    have h7 : (2^k : ℝ) ≤ x := hkp
    have h8 : (2^k : ℝ) * r₀ ≤ x * r₀ := by gcongr
    have h9 : x * r₀ = a := h_eq
    rw [h9] at h8; exact h8
  have h10 : a < (2^(k+1) : ℝ) * r₀ := by
    have h11 : x < (2^(k+1) : ℝ) := hkp2
    have h12 : x * r₀ < (2^(k+1) : ℝ) * r₀ := by gcongr
    have h13 : x * r₀ = a := h_eq
    rw [h13] at h12; exact h12
  exact ⟨k, hkK, h6', h10⟩

/-! ### Per-pair directional sum bound -/

/-- Algebraic identity: (a / 2)^(-s) = a^(-s) * 2^s for a > 0, s real. -/
private lemma half_rpow_neg {a s : ℝ} (ha : 0 < a) :
    (a / 2)^(-s) = a^(-s) * (2 : ℝ)^s := by
  have h1 : (a / 2)^(-s) = a^(-s) / (2 : ℝ)^(-s) := by
    rw [Real.div_rpow (by linarith) (by norm_num)]
  rw [h1]
  have h2 : (2 : ℝ)^(-s) ≠ 0 := by positivity
  have h3 : a^(-s) / (2 : ℝ)^(-s) = a^(-s) * ((2 : ℝ)^(-s))⁻¹ := by
    rw [div_eq_mul_inv]
  rw [h3]
  have h4 : ((2 : ℝ)^(-s))⁻¹ = (2 : ℝ)^s := by
    have h5 : (2 : ℝ)^(-s) = ((2 : ℝ)^s)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)] <;> ring
    rw [h5]
    have h6 : 0 < (2 : ℝ)^s := by positivity
    rw [inv_inv]
  rw [h4] <;> ring

/-- Kernel bound for Case B1 (|σ₀| > 2): each term is bounded by 2^s * norm_v^(-s). -/
private lemma case_b1_kernel_bound {s δ norm_v v₀ v₁ σ₀ : ℝ} {S : Finset ℝ}
    (hs : 0 < s) (hδ : 0 < δ) (hS_subset : ∀ σ ∈ S, -1 ≤ σ ∧ σ ≤ 1)
    (h_norm_pos : 0 < norm_v) (h_v1_ge : |v₁| ≥ norm_v / 2) (h_v1_ne_zero : v₁ ≠ 0)
    (h_abs_decomp : ∀ σ : ℝ, v₀ - σ * v₁ = v₁ * (σ₀ - σ))
    (hσ₀_large : |σ₀| > 2) :
    ∀ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤ (2 : ℝ)^s * norm_v^(-s) := by
  intro σ hσ
  have hσ2 : -1 ≤ σ ∧ σ ≤ 1 := hS_subset σ hσ
  have hσ3 : |σ| ≤ 1 := by rcases hσ2 with ⟨h1,h2⟩; exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h_tri : |σ₀| ≤ |σ₀ - σ| + |σ| := by
    have h1 : σ₀ - σ ≤ |σ₀ - σ| := le_abs_self (σ₀ - σ)
    have h2 : σ ≤ |σ| := le_abs_self σ
    have h3 : -(σ₀ - σ) ≤ |σ₀ - σ| := by
      have h31 : -(σ₀ - σ) ≤ |-(σ₀ - σ)| := le_abs_self (-(σ₀ - σ))
      have h32 : |-(σ₀ - σ)| = |σ₀ - σ| := by rw [abs_neg]
      rw [h32] at h31; exact h31
    have h4 : -σ ≤ |σ| := by
      have h41 : -σ ≤ |-σ| := le_abs_self (-σ)
      have h42 : |-σ| = |σ| := by rw [abs_neg]
      rw [h42] at h41; exact h41
    have h5 : -(|σ₀ - σ| + |σ|) ≤ σ₀ := by linarith
    have h6 : σ₀ ≤ |σ₀ - σ| + |σ| := by linarith
    exact abs_le.mpr ⟨h5,h6⟩
  have h_lo : |σ₀| - |σ| ≤ |σ₀ - σ| := by linarith
  have h_dist : 1 ≤ |σ₀ - σ| := by linarith [h_lo, hσ₀_large, hσ3]
  have h_ne : σ₀ - σ ≠ 0 := by
    have h_pos : 0 < |σ₀ - σ| := by linarith
    exact abs_pos.mp h_pos
  have h_d_ne_zero : v₀ - σ * v₁ ≠ 0 := by
    rw [h_abs_decomp σ]; exact mul_ne_zero h_v1_ne_zero h_ne
  rw [regularizedKernelReal_eq_min hs hδ h_d_ne_zero]
  have h_abs : |v₀ - σ * v₁| = |v₁| * |σ₀ - σ| := by rw [h_abs_decomp σ, abs_mul]
  rw [h_abs]
  have h1 : min ((|v₁| * |σ₀ - σ|) ^ (-s)) (δ ^ (-s)) ≤ (|v₁| * |σ₀ - σ|) ^ (-s) :=
    min_le_left ((|v₁| * |σ₀ - σ|) ^ (-s)) (δ ^ (-s))
  have h2 : (|v₁| * |σ₀ - σ|) ^ (-s) = |v₁|^(-s) * |σ₀ - σ|^(-s) := by
    rw [Real.mul_rpow (by positivity) (by positivity)] <;> ring
  have h3 : |σ₀ - σ|^(-s) ≤ 1 := by
    have h4 : 1 ≤ |σ₀ - σ| := h_dist
    have h5 : |σ₀ - σ|^(-s) ≤ (1 : ℝ)^(-s) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) h4 (by linarith)
    have h6 : (1 : ℝ)^(-s) = 1 := by simp
    rw [h6] at h5; exact h5
  have h6 : |v₁|^(-s) ≤ (2 : ℝ)^s * norm_v^(-s) := by
    have h7 : |v₁| ≥ norm_v / 2 := h_v1_ge
    have h8 : |v₁|^(-s) ≤ (norm_v / 2)^(-s) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h7 (by linarith)
    have h91 : (norm_v / 2)^(-s) = norm_v^(-s) * (2 : ℝ)^s :=
      half_rpow_neg (a := norm_v) (s := s) h_norm_pos
    have h92 : (norm_v / 2)^(-s) = (2 : ℝ)^s * norm_v^(-s) := by
      rw [h91] <;> ring
    rw [h92] at h8; exact h8
  have h4 : |v₁|^(-s) * |σ₀ - σ|^(-s) ≤ |v₁|^(-s) := by
    have h5 : 0 ≤ |v₁|^(-s) := by positivity
    calc |v₁|^(-s) * |σ₀ - σ|^(-s)
      ≤ |v₁|^(-s) * (1 : ℝ) := mul_le_mul_of_nonneg_left h3 h5
    _ = |v₁|^(-s) := by ring
  calc min ((|v₁| * |σ₀ - σ|) ^ (-s)) (δ ^ (-s))
    ≤ (|v₁| * |σ₀ - σ|) ^ (-s) := h1
    _ = |v₁|^(-s) * |σ₀ - σ|^(-s) := h2
    _ ≤ |v₁|^(-s) := h4
    _ ≤ (2 : ℝ)^s * norm_v^(-s) := h6

/-- Cancellation lemma: x^s * x^(-s) = 1 for positive x. -/
private lemma rpow_self_cancel {x : ℝ} (hx : 0 < x) (s : ℝ) : x^s * x^(-s) = 1 := by
  have h1 : x^(-s) = (x^s)⁻¹ := by
    rw [Real.rpow_neg hx.le] <;> ring
  rw [h1]
  have h2 : x^s ≠ 0 := by positivity
  field_simp [h2]

/-- Disjointness of dyadic annuli. -/
private lemma annuli_disjoint {r₀ : ℝ} (hr₀_pos : 0 < r₀)
    (T : Finset ℝ) (σ₀ : ℝ) (k l : ℕ) (hkl : k ≠ l) :
    Disjoint (T.filter (fun σ => (2^k : ℝ) * r₀ ≤ |σ - σ₀| ∧ |σ - σ₀| < (2^(k+1) : ℝ) * r₀))
      (T.filter (fun σ => (2^l : ℝ) * r₀ ≤ |σ - σ₀| ∧ |σ - σ₀| < (2^(l+1) : ℝ) * r₀)) := by
  have h_cases : k < l ∨ l < k := by omega
  rcases h_cases with (h | h)
  · rw [Finset.disjoint_left]; intro σ hσ1 hσ2
    have h1 : |σ - σ₀| < (2^(k+1) : ℝ) * r₀ := (Finset.mem_filter.mp hσ1).2.2
    have h2 : (2^l : ℝ) * r₀ ≤ |σ - σ₀| := (Finset.mem_filter.mp hσ2).2.1
    have h4 : k + 1 ≤ l := by omega
    have h5 : (2^(k+1) : ℝ) ≤ (2^l : ℝ) := by
      gcongr <;> norm_num
    have h7 : (2^(k+1) : ℝ) * r₀ ≤ (2^l : ℝ) * r₀ := mul_le_mul_of_nonneg_right h5 (by linarith)
    have h8 : (2^l : ℝ) * r₀ < (2^(k+1) : ℝ) * r₀ := calc
      (2^l : ℝ) * r₀ ≤ |σ - σ₀| := h2
      _ < (2^(k+1) : ℝ) * r₀ := h1
    exact False.elim (not_le.mpr h8 h7)
  · rw [Finset.disjoint_left]; intro σ hσ1 hσ2
    have h1 : |σ - σ₀| < (2^(l+1) : ℝ) * r₀ := (Finset.mem_filter.mp hσ2).2.2
    have h2 : (2^k : ℝ) * r₀ ≤ |σ - σ₀| := (Finset.mem_filter.mp hσ1).2.1
    have h4 : l + 1 ≤ k := by omega
    have h5 : (2^(l+1) : ℝ) ≤ (2^k : ℝ) := by
      gcongr <;> norm_num
    have h7 : (2^(l+1) : ℝ) * r₀ ≤ (2^k : ℝ) * r₀ := mul_le_mul_of_nonneg_right h5 (by linarith)
    have h8 : (2^k : ℝ) * r₀ < (2^(l+1) : ℝ) * r₀ := calc
      (2^k : ℝ) * r₀ ≤ |σ - σ₀| := h2
      _ < (2^(l+1) : ℝ) * r₀ := h1
    exact False.elim (not_le.mpr h8 h7)

/-- Helper: x^s * x^(-s) = 1 for x > 0. -/
private lemma rpow_self_inv {x s : ℝ} (hx : 0 < x) : x^s * x^(-s) = 1 := by
  have h1 : x^(-s) = (x^s)⁻¹ := by
    rw [Real.rpow_neg (by linarith)] <;> ring
  rw [h1]
  have h2 : x^s ≠ 0 := by positivity
  field_simp [h2]

/-- Per-annulus bound for dyadic decomposition. -/
private lemma annulus_bound {s δ C_dir r₀ : ℝ} {S : Finset ℝ} {σ₀ : ℝ} {K : ℕ} {k : ℕ}
    (hs : 0 < s) (hδ : 0 < δ) (hr₀_pos : 0 < r₀) (hr₀_ge_delta : δ ≤ r₀)
    (hS_subset : ∀ σ ∈ S, -1 ≤ σ ∧ σ ≤ 1)
    (h_count : ∀ (σ : ℝ) (r : ℝ), δ ≤ r →
      (S.filter (fun x => dist x σ ≤ r)).card ≤ C_dir * r ^ s * (S.card : ℝ))
    (T : Finset ℝ) (hT_sub : T ⊆ S) (hkK : k < K) :
    let A := T.filter (fun σ => (2^k : ℝ) * r₀ ≤ |σ - σ₀| ∧ |σ - σ₀| < (2^(k+1) : ℝ) * r₀)
    ∑ σ ∈ A, |σ - σ₀| ^ (-s) ≤ C_dir * (2 : ℝ)^s * (S.card : ℝ) := by
  let A := T.filter (fun σ => (2^k : ℝ) * r₀ ≤ |σ - σ₀| ∧ |σ - σ₀| < (2^(k+1) : ℝ) * r₀)
  have h1 : ∀ σ ∈ A, |σ - σ₀| ^ (-s) ≤ ((2^k : ℝ) * r₀) ^ (-s) := by
    intro σ hσ
    have h2 : (2^k : ℝ) * r₀ ≤ |σ - σ₀| := (Finset.mem_filter.mp hσ).2.1
    exact Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  have hsub : A ⊆ S.filter (fun x => dist x σ₀ ≤ (2^(k+1) : ℝ) * r₀) := by
    intro σ hσ
    have hσT : σ ∈ T := (Finset.mem_filter.mp hσ).1
    have hσS : σ ∈ S := hT_sub hσT
    have h2 : |σ - σ₀| < (2^(k+1) : ℝ) * r₀ := (Finset.mem_filter.mp hσ).2.2
    have h3 : dist σ σ₀ ≤ (2^(k+1) : ℝ) * r₀ := by
      simpa [dist_eq_norm] using le_of_lt h2
    exact Finset.mem_filter.mpr ⟨hσS, h3⟩
  have h4 : δ ≤ (2^(k+1) : ℝ) * r₀ := by
    have h5 : (2 : ℝ)^(k+1) ≥ 2 := by
      have h6 : k + 1 ≥ 1 := by omega
      have h7 : (2 : ℝ)^(k+1) ≥ (2 : ℝ)^1 := by gcongr <;> norm_num
      norm_num at h7 ⊢ <;> exact h7
    have h6 : (2^(k+1) : ℝ) * r₀ ≥ 2 * r₀ := by gcongr
    have h7 : 2 * r₀ ≥ r₀ := by linarith [hr₀_pos]
    linarith [hr₀_ge_delta]
  have h6 : ((S.filter (fun x => dist x σ₀ ≤ (2^(k+1) : ℝ) * r₀)).card : ℝ) ≤
      C_dir * ((2^(k+1) : ℝ) * r₀) ^ s * (S.card : ℝ) := h_count σ₀ _ h4
  have h7 : (A.card : ℝ) ≤ ((S.filter (fun x => dist x σ₀ ≤ (2^(k+1) : ℝ) * r₀)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h_card : (A.card : ℝ) ≤ C_dir * ((2^(k+1) : ℝ) * r₀) ^ s * (S.card : ℝ) := h7.trans h6
  have hpos2k : 0 < (2^k : ℝ) := by positivity
  have h_a : ((2^(k+1) : ℝ) * r₀) ^ s = (2 : ℝ)^s * (2^k : ℝ)^s * r₀^s := by
    have h2 : (2^(k+1) : ℝ) = (2 : ℝ) * (2^k : ℝ) := by
      simp [pow_succ] <;> ring
    rw [h2]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)] <;> ring
  have h_b : ((2^k : ℝ) * r₀) ^ (-s) = (2^k : ℝ)^(-s) * r₀^(-s) := by
    rw [Real.mul_rpow (by positivity) (by positivity)] <;> ring
  have h_c : (2^k : ℝ)^s * (2^k : ℝ)^(-s) = 1 := rpow_self_cancel hpos2k s
  have h_d : r₀^s * r₀^(-s) = 1 := rpow_self_cancel hr₀_pos s
  calc ∑ σ ∈ A, |σ - σ₀| ^ (-s)
    ≤ ∑ σ ∈ A, ((2^k : ℝ) * r₀) ^ (-s) := Finset.sum_le_sum h1
  _ = (A.card : ℝ) * (((2^k : ℝ) * r₀) ^ (-s)) := by simp [Finset.sum_const] <;> ring
  _ ≤ (C_dir * ((2^(k+1) : ℝ) * r₀) ^ s * (S.card : ℝ)) * (((2^k : ℝ) * r₀) ^ (-s)) := by gcongr
  _ = C_dir * (2 : ℝ)^s * (S.card : ℝ) := by
    rw [h_a, h_b]
    have h_e : C_dir * ((2 : ℝ)^s * (2^k : ℝ)^s * r₀^s) * (S.card : ℝ) * ((2^k : ℝ)^(-s) * r₀^(-s)) =
        C_dir * (2 : ℝ)^s * (S.card : ℝ) := by
      have h_f : C_dir * ((2 : ℝ)^s * (2^k : ℝ)^s * r₀^s) * (S.card : ℝ) * ((2^k : ℝ)^(-s) * r₀^(-s)) =
          C_dir * (2 : ℝ)^s * ((2^k : ℝ)^s * (2^k : ℝ)^(-s)) * (r₀^s * r₀^(-s)) * (S.card : ℝ) := by ring
      rw [h_f, h_c, h_d] <;> ring
    exact h_e

/-- Inner sum final algebra: δ^s * |v₁|^(-s) * |S| * δ^(-s) = |v₁|^(-s) * |S|. -/
private lemma inner_sum_algebra {δ v₁ C_dir : ℝ} {S : Finset ℝ} (hδ : 0 < δ) (h_v1_pos : 0 < |v₁|) :
    C_dir * (δ^s * |v₁|^(-s)) * (S.card : ℝ) * δ^(-s) = C_dir * |v₁|^(-s) * (S.card : ℝ) := by
  have h11 : δ^s * δ^(-s) = 1 := rpow_self_cancel hδ s
  have h14 : C_dir * (δ^s * |v₁|^(-s)) * (S.card : ℝ) * δ^(-s) =
      C_dir * (δ^s * δ^(-s)) * |v₁|^(-s) * (S.card : ℝ) := by
    ac_rfl
  rw [h14, h11]
  have h15 : C_dir * (1 : ℝ) * |v₁|^(-s) * (S.card : ℝ) = C_dir * |v₁|^(-s) * (S.card : ℝ) := by
    ring
  exact h15

/-- Outer kernel equality: when |σ - σ₀| ≥ r₀, the regularized kernel equals |v₁|^(-s) * |σ - σ₀|^(-s). -/
private lemma outer_kernel_eq {s δ v₀ v₁ σ₀ r₀ : ℝ}
    (hδ : 0 < δ) (hs : 0 < s) (h_v1_pos : 0 < |v₁|) (hr₀_pos : 0 < r₀)
    (hr₀_def : r₀ = δ / |v₁|)
    (h_abs_decomp : ∀ σ : ℝ, v₀ - σ * v₁ = v₁ * (σ₀ - σ))
    (σ : ℝ) (h_ge : r₀ ≤ |σ - σ₀|) :
    regularizedKernelReal s δ (v₀ - σ * v₁) = |v₁|^(-s) * |σ - σ₀|^(-s) := by
  have h_abs1 : |v₀ - σ * v₁| = |v₁| * |σ - σ₀| := by
    rw [h_abs_decomp σ, abs_mul]
    have h_sym : |σ₀ - σ| = |σ - σ₀| := by rw [show σ₀ - σ = -(σ - σ₀) by ring, abs_neg]
    rw [h_sym] <;> ring
  have h_d_ge : δ ≤ |v₁| * |σ - σ₀| := by
    have h : |v₁| * |σ - σ₀| ≥ |v₁| * r₀ :=
      mul_le_mul_of_nonneg_left h_ge (abs_nonneg v₁)
    have h2 : |v₁| * r₀ = δ := by
      rw [hr₀_def]
      field_simp [h_v1_pos.ne'] <;> ring
    rw [h2] at h
    exact h
  have h_d_ne_zero : v₀ - σ * v₁ ≠ 0 := by
    have h' : 0 < |v₀ - σ * v₁| := by
      rw [h_abs1]
      linarith [hδ, h_d_ge]
    exact abs_pos.mp h'
  rw [regularizedKernelReal_eq_min hs hδ h_d_ne_zero]
  rw [h_abs1]
  have h3 : (|v₁| * |σ - σ₀|)^(-s) ≤ δ^(-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h_d_ge (by linarith)
  have h4 : min ((|v₁| * |σ - σ₀|)^(-s)) (δ^(-s)) = (|v₁| * |σ - σ₀|)^(-s) := by
    rw [min_eq_left h3]
  rw [h4]
  have h5 : (|v₁| * |σ - σ₀|)^(-s) = |v₁|^(-s) * |σ - σ₀|^(-s) := by
    rw [Real.mul_rpow (by positivity) (by positivity)] <;> ring
  rw [h5]

/-- Simple bound: 1 ≤ 2^s for s ≥ 0. -/
private lemma two_pow_ge_one {s : ℝ} (hs : 0 ≤ s) : (1 : ℝ) ≤ (2 : ℝ)^s :=
  Real.one_le_rpow (by norm_num) hs

/-- Sum over dyadic annuli. -/
private lemma outer_sum_bound {K : ℕ} {S : Finset ℝ} {σ₀ C_dir s : ℝ}
    (A : ℕ → Finset ℝ) (T : Finset ℝ)
    (h_cover : T = Finset.biUnion (Finset.range K) A)
    (h_disj2 : ∀ k l, k ≠ l → Disjoint (A k) (A l))
    (h_each : ∀ k ∈ Finset.range K, ∑ σ ∈ A k, |σ - σ₀| ^ (-s) ≤ C_dir * (2 : ℝ)^s * (S.card : ℝ)) :
    ∑ σ ∈ T, |σ - σ₀| ^ (-s) ≤ (K : ℝ) * C_dir * (2 : ℝ)^s * (S.card : ℝ) := by
  have h_disj2' : Set.PairwiseDisjoint (↑(Finset.range K)) A := by
    intro i _ j _ hne
    exact h_disj2 i j hne
  have h_sum_eq : ∑ σ ∈ T, |σ - σ₀| ^ (-s) =
      ∑ k ∈ Finset.range K, ∑ σ ∈ A k, |σ - σ₀| ^ (-s) := by
    rw [h_cover]
    exact Finset.sum_biUnion h_disj2'
  rw [h_sum_eq]
  calc ∑ k ∈ Finset.range K, ∑ σ ∈ A k, |σ - σ₀| ^ (-s)
    ≤ ∑ k ∈ Finset.range K, (C_dir * (2 : ℝ)^s * (S.card : ℝ)) := Finset.sum_le_sum h_each
  _ = (K : ℝ) * C_dir * (2 : ℝ)^s * (S.card : ℝ) := by simp [Finset.sum_const] <;> ring

/-- Combined bound: K * 2^s + 1 ≤ 2 * K * 2^s when K ≥ 1 and 2^s ≥ 1. -/
private lemma combined_bound {K s : ℝ} (hK : 1 ≤ K) (h2s : 1 ≤ (2 : ℝ)^s) :
    K * (2 : ℝ)^s + 1 ≤ 2 * K * (2 : ℝ)^s := by
  have h1 : 1 ≤ K * (2 : ℝ)^s := by
    calc 1 ≤ 1 * 1 := by norm_num
      _ ≤ K * (2 : ℝ)^s := by gcongr
  linarith

/-- Convert outer sum: ∑ kernel ≤ |v₁|^(-s) * ∑ |σ-σ₀|^(-s) -/
private lemma outer_sum2_bound {s δ v₀ v₁ σ₀ : ℝ} {S T : Finset ℝ} {K C_dir : ℝ}
    (h_outer_sum : ∑ σ ∈ T, |σ - σ₀| ^ (-s) ≤ (K : ℝ) * C_dir * (2 : ℝ)^s * (S.card : ℝ))
    (h_outer_kernel : ∀ σ ∈ T, regularizedKernelReal s δ (v₀ - σ * v₁) = |v₁|^(-s) * |σ - σ₀|^(-s))
    (h_v1_pos : 0 < |v₁|) :
    ∑ σ ∈ T, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
      |v₁|^(-s) * ((K : ℝ) * C_dir * (2 : ℝ)^s * (S.card : ℝ)) := by
  have h_eq1 : ∑ σ ∈ T, regularizedKernelReal s δ (v₀ - σ * v₁) =
      ∑ σ ∈ T, |v₁|^(-s) * |σ - σ₀|^(-s) := by
    apply Finset.sum_congr rfl
    intro σ hσ
    exact h_outer_kernel σ hσ
  rw [h_eq1]
  have h : ∑ σ ∈ T, |v₁|^(-s) * |σ - σ₀|^(-s) = |v₁|^(-s) * ∑ σ ∈ T, |σ - σ₀|^(-s) := by
    rw [Finset.mul_sum]
  rw [h]
  have h_nonneg : 0 ≤ |v₁|^(-s) := Real.rpow_nonneg (abs_nonneg v₁) (-s)
  exact mul_le_mul_of_nonneg_left h_outer_sum h_nonneg

/-- Combine inner + outer sums into final B2 bound. -/
private lemma b2_combined_bound {s δ v₀ v₁ : ℝ} {S T inner : Finset ℝ} {K C_dir : ℝ}
    (h_partition : S = T ∪ inner) (h_disj : Disjoint T inner)
    (hC_dir_nonneg : 0 ≤ C_dir)
    (h_outer_sum2 : ∑ σ ∈ T, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
        |v₁|^(-s) * ((K : ℝ) * C_dir * (2 : ℝ)^s * (S.card : ℝ)))
    (h_inner_sum : ∑ σ ∈ inner, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
        C_dir * |v₁|^(-s) * (S.card : ℝ))
    (h_K_ge1 : (1 : ℝ) ≤ (K : ℝ)) (h_2s_ge1 : (1 : ℝ) ≤ (2 : ℝ)^s) :
    ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
      |v₁|^(-s) * C_dir * (S.card : ℝ) * (2 * (K : ℝ) * (2 : ℝ)^s) := by
  have h_total : ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
      ∑ σ ∈ T, regularizedKernelReal s δ (v₀ - σ * v₁) + ∑ σ ∈ inner, regularizedKernelReal s δ (v₀ - σ * v₁) := by
    rw [h_partition, Finset.sum_union h_disj] <;> linarith
  calc ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁)
    ≤ ∑ σ ∈ T, _ + ∑ σ ∈ inner, _ := h_total
    _ ≤ |v₁|^(-s) * ((K : ℝ) * C_dir * (2 : ℝ)^s * (S.card : ℝ)) + C_dir * |v₁|^(-s) * (S.card : ℝ) := by gcongr
    _ = |v₁|^(-s) * C_dir * (S.card : ℝ) * (((K : ℝ) * (2 : ℝ)^s) + 1) := by ring
    _ ≤ |v₁|^(-s) * C_dir * (S.card : ℝ) * (2 * (K : ℝ) * (2 : ℝ)^s) := by
      have h_cb : (K : ℝ) * (2 : ℝ)^s + 1 ≤ 2 * (K : ℝ) * (2 : ℝ)^s :=
        combined_bound h_K_ge1 h_2s_ge1
      have h_v1_nonneg : 0 ≤ |v₁|^(-s) := Real.rpow_nonneg (abs_nonneg v₁) (-s)
      have h_card_nonneg : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg S.card
      have h_pos : 0 ≤ |v₁|^(-s) * C_dir * (S.card : ℝ) :=
        mul_nonneg (mul_nonneg h_v1_nonneg hC_dir_nonneg) h_card_nonneg
      exact mul_le_mul_of_nonneg_left h_cb h_pos

/-- Prove 1 ≤ K from log bounds. -/
private lemma k_ge1_lemma {K : ℕ} {δ : ℝ}
    (hK_ceil : Real.log (4 / δ) / Real.log 2 ≤ (K : ℝ))
    (h_log_ge : (2 : ℝ) ≤ Real.log (4 / δ) / Real.log 2) :
    (1 : ℝ) ≤ (K : ℝ) := by
  have h : (2 : ℝ) ≤ (K : ℝ) := le_trans h_log_ge hK_ceil
  exact le_trans (by norm_num) h

/-- Prove |v₁|^(-s) ≤ 2^s * norm_v^(-s). -/
private lemma v1_bound_lemma {s norm_v v₁ : ℝ} (hs : 0 < s)
    (h_norm_pos : 0 < norm_v) (h_v1_ge : |v₁| ≥ norm_v / 2) :
    |v₁|^(-s) ≤ (2 : ℝ)^s * norm_v^(-s) := by
  have h12 : |v₁|^(-s) ≤ (norm_v / 2)^(-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h_v1_ge (by linarith)
  rw [half_rpow_neg (a := norm_v) (s := s) h_norm_pos] at h12
  have h13 : norm_v^(-s) * (2 : ℝ)^s = (2 : ℝ)^s * norm_v^(-s) := by ring
  rw [h13] at h12
  exact h12

/-- Final bound computation for B2 case. -/
private lemma final_bound_lemma {s δ C_dir norm_v v₀ v₁ : ℝ} {S : Finset ℝ} {K : ℕ}
    (hs : 0 < s) (hC_dir_nonneg : 0 ≤ C_dir) (h_log4_ge1 : 1 ≤ Real.log (4 / δ))
    (h_combined : ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
        |v₁|^(-s) * C_dir * (S.card : ℝ) * (2 * (K : ℝ) * (2 : ℝ)^s))
    (h_K_bound : (K : ℝ) ≤ (3 / 2 : ℝ) * Real.log (4 / δ) / Real.log 2)
    (h_v1_bound : |v₁|^(-s) ≤ (2 : ℝ)^s * norm_v^(-s)) :
    ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
      C_dir * (4 : ℝ)^s * 3 / Real.log 2 * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) := by
  have h_card_nonneg : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg S.card
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_log4_nonneg : 0 ≤ Real.log (4 / δ) := by linarith
  have h_cdir_nonneg : 0 ≤ C_dir := hC_dir_nonneg
  have h_v1_nonneg : 0 ≤ |v₁|^(-s) := Real.rpow_nonneg (abs_nonneg v₁) (-s)
  have h2s_nonneg : 0 ≤ (2 : ℝ)^s := Real.rpow_nonneg (by norm_num) s
  calc ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁)
    ≤ |v₁|^(-s) * C_dir * (S.card : ℝ) * (2 * (K : ℝ) * (2 : ℝ)^s) := h_combined
    _ ≤ |v₁|^(-s) * C_dir * (S.card : ℝ) * (2 * ((3 / 2 : ℝ) * Real.log (4 / δ) / Real.log 2) * (2 : ℝ)^s) := by
      gcongr
      <;> linarith
    _ = |v₁|^(-s) * C_dir * (S.card : ℝ) * (3 * Real.log (4 / δ) / Real.log 2 * (2 : ℝ)^s) := by ring
    _ ≤ ((2 : ℝ)^s * norm_v^(-s)) * C_dir * (S.card : ℝ) * (3 * Real.log (4 / δ) / Real.log 2 * (2 : ℝ)^s) := by
      gcongr
      <;> linarith
    _ = C_dir * (4 : ℝ)^s * 3 / Real.log 2 * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) := by
      have h2s : (2 : ℝ)^s * (2 : ℝ)^s = (4 : ℝ)^s := by
        have h : (2 : ℝ)^s * (2 : ℝ)^s = (2 * (2 : ℝ))^s := by
          rw [← Real.mul_rpow] <;> norm_num
        rw [h] <;> norm_num
      have h_eq1 : ((2 : ℝ)^s * norm_v^(-s)) * C_dir * (S.card : ℝ) * (3 * Real.log (4 / δ) / Real.log 2 * (2 : ℝ)^s) =
          ((2 : ℝ)^s * (2 : ℝ)^s) * (C_dir * (S.card : ℝ) * norm_v^(-s)) * (3 * Real.log (4 / δ) / Real.log 2) := by ring
      rw [h_eq1, h2s]
      ring

/-- Conclude B2: lift from C_dir bound to C_total bound. -/
private lemma conclude_b2 {s δ C_dir C_total norm_v v₀ v₁ : ℝ} {S : Finset ℝ}
    (hs : 0 < s) (hC_dir_nonneg : 0 ≤ C_dir) (h_log4_ge1 : 1 ≤ Real.log (4 / δ))
    (h_norm_pos : 0 < norm_v)
    (hC : C_total = C_dir * (4 : ℝ)^s * 3 / Real.log 2 + (4 : ℝ)^s)
    (h_norm_rpow : norm_v^(-s) = (v₀^2 + v₁^2)^(-s/2))
    (h_final : ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
        C_dir * (4 : ℝ)^s * 3 / Real.log 2 * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s)) :
    ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
      C_total * (S.card : ℝ) * Real.log (4 / δ) * (v₀^2 + v₁^2)^(-s/2) := by
  have h_pos4 : 0 ≤ (4 : ℝ)^s := Real.rpow_nonneg (by norm_num) s
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h102 : 0 ≤ C_dir * (4 : ℝ)^s * 3 / Real.log 2 := by
    apply div_nonneg
    · positivity
    · positivity
  have h10 : 0 ≤ C_total := by
    rw [hC]
    exact add_nonneg h102 h_pos4
  have h12 : C_dir * (4 : ℝ)^s * 3 / Real.log 2 ≤ C_total := by
    rw [hC]
    exact le_add_of_nonneg_right h_pos4
  have h_card_nonneg : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg S.card
  have h_log4_nonneg : 0 ≤ Real.log (4 / δ) := by linarith [h_log4_ge1]
  have h_norm_v_nonneg : 0 ≤ norm_v^(-s) := Real.rpow_nonneg (le_of_lt h_norm_pos) (-s)
  have h14 : 0 ≤ (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) := by positivity
  have h11 : C_dir * (4 : ℝ)^s * 3 / Real.log 2 * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) ≤
      C_total * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) := by
    have h : (C_dir * (4 : ℝ)^s * 3 / Real.log 2) * ((S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s)) ≤
        C_total * ((S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s)) :=
      mul_le_mul_of_nonneg_right h12 h14
    simpa [mul_assoc] using h
  calc ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁)
    ≤ C_dir * (4 : ℝ)^s * 3 / Real.log 2 * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) := h_final
    _ ≤ C_total * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) := h11
    _ = C_total * (S.card : ℝ) * Real.log (4 / δ) * (v₀^2 + v₁^2)^(-s/2) := by
      rw [h_norm_rpow] <;> rfl

/-- Lemma: all points in T are within 2^K * r₀ of σ₀. -/
private lemma hT_lt_lemma {S T : Finset ℝ} {σ₀ r₀ : ℝ} {K : ℕ}
    (hT_sub : T ⊆ S) (h_max_dist : ∀ σ ∈ S, |σ - σ₀| ≤ 3) (hK2 : (2^K : ℝ) * r₀ ≥ 4) :
    ∀ σ ∈ T, |σ - σ₀| < (2^K : ℝ) * r₀ := by
  intro σ hσ
  have hσS : σ ∈ S := hT_sub hσ
  have hc : |σ - σ₀| ≤ 3 := h_max_dist σ hσS
  have h4 : |σ - σ₀| < 4 := by linarith
  exact lt_of_lt_of_le h4 hK2

/-- Complete dyadic annulus decomposition and outer sum bound. -/
private lemma dyadic_outer_sum {s δ C_dir r₀ : ℝ} {S : Finset ℝ} {σ₀ : ℝ} {K : ℕ}
    (hs : 0 < s) (hδ : 0 < δ) (hr₀_pos : 0 < r₀) (hr₀_ge_delta : δ ≤ r₀)
    (hS_subset : ∀ σ ∈ S, -1 ≤ σ ∧ σ ≤ 1)
    (h_count : ∀ (σ : ℝ) (r : ℝ), δ ≤ r →
      (S.filter (fun x => dist x σ ≤ r)).card ≤ C_dir * r ^ s * (S.card : ℝ))
    (T : Finset ℝ) (hT_sub : T ⊆ S)
    (hT_ge : ∀ σ ∈ T, r₀ ≤ |σ - σ₀|)
    (hT_lt : ∀ σ ∈ T, |σ - σ₀| < (2^K : ℝ) * r₀) :
    ∑ σ ∈ T, |σ - σ₀| ^ (-s) ≤ (K : ℝ) * C_dir * (2 : ℝ)^s * (S.card : ℝ) := by
  let A : ℕ → Finset ℝ := fun k =>
    T.filter (fun σ => (2^k : ℝ) * r₀ ≤ |σ - σ₀| ∧ |σ - σ₀| < (2^(k+1) : ℝ) * r₀)
  have h_cover : T = Finset.biUnion (Finset.range K) A := by
    apply Finset.ext; intro σ
    simp only [A, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      have hge : r₀ ≤ |σ - σ₀| := hT_ge σ h
      have hb : |σ - σ₀| < (2^K : ℝ) * r₀ := hT_lt σ h
      rcases exists_k_pow_near hr₀_pos hge hb with ⟨k, hkK, h1, h2⟩
      exact ⟨k, hkK, h, h1, h2⟩
    · rintro ⟨k, _, hT, _, _⟩
      exact hT
  have h_disj2 : ∀ k l, k ≠ l → Disjoint (A k) (A l) :=
    fun k l hkl => annuli_disjoint hr₀_pos T σ₀ k l hkl
  have h_each : ∀ k ∈ Finset.range K, ∑ σ ∈ A k, |σ - σ₀| ^ (-s) ≤
      C_dir * (2 : ℝ)^s * (S.card : ℝ) := by
    intro k hkK
    have hkK' : k < K := Finset.mem_range.mp hkK
    exact annulus_bound hs hδ hr₀_pos hr₀_ge_delta hS_subset h_count T hT_sub hkK'
  exact outer_sum_bound A T h_cover h_disj2 h_each

/-- Bounds on K: K ≤ 3/2 * log(4/δ) / log 2 and 1 ≤ K. -/
private lemma k_bounds {K : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hK1 : (K : ℝ) ≤ Real.log (4 / δ) / Real.log 2 + 1)
    (hK2 : Real.log (4 / δ) / Real.log 2 ≤ (K : ℝ))
    (h_log_ge : (2 : ℝ) ≤ Real.log (4 / δ) / Real.log 2) :
    (K : ℝ) ≤ (3 / 2 : ℝ) * Real.log (4 / δ) / Real.log 2 ∧ (1 : ℝ) ≤ (K : ℝ) := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : 1 ≤ (1 / 2 : ℝ) * (Real.log (4 / δ) / Real.log 2) := by
    have h3 : (1 / 2 : ℝ) * 2 ≤ (1 / 2 : ℝ) * (Real.log (4 / δ) / Real.log 2) :=
      mul_le_mul_of_nonneg_left h_log_ge (by norm_num)
    have h4 : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by norm_num
    rw [h4] at h3
    exact h3
  have h_K_bound : (K : ℝ) ≤ (3 / 2 : ℝ) * Real.log (4 / δ) / Real.log 2 := by
    calc (K : ℝ)
      ≤ Real.log (4 / δ) / Real.log 2 + 1 := hK1
    _ ≤ Real.log (4 / δ) / Real.log 2 + (1 / 2 : ℝ) * (Real.log (4 / δ) / Real.log 2) := by gcongr
    _ = (3 / 2 : ℝ) * Real.log (4 / δ) / Real.log 2 := by ring
  have h_K_ge1 : (1 : ℝ) ≤ (K : ℝ) := by
    have h6 : Real.log (4 / δ) / Real.log 2 ≥ 2 := h_log_ge
    linarith [hK2, h6]
  exact ⟨h_K_bound, h_K_ge1⟩

/-- Constant bound helper: 2^s ≤ C_total * log(4/δ). -/
private lemma constant_bounds {s δ C_dir : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hC_dir_nonneg : 0 ≤ C_dir) (h_log4_ge1 : 1 ≤ Real.log (4 / δ)) :
    let C_total := C_dir * (4 : ℝ)^s * 3 / Real.log 2 + (4 : ℝ)^s
    (2 : ℝ)^s ≤ C_total * Real.log (4 / δ) := by
  let C_total := C_dir * (4 : ℝ)^s * 3 / Real.log 2 + (4 : ℝ)^s
  have h_pos4 : 0 ≤ (4 : ℝ)^s := Real.rpow_nonneg (by norm_num) s
  have h_poslog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h102 : 0 ≤ C_dir * (4 : ℝ)^s * 3 / Real.log 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hC_dir_nonneg h_pos4) (by norm_num)) (by positivity)
  have h10 : (4 : ℝ)^s ≤ C_total := by
    dsimp only [C_total]
    exact le_add_of_nonneg_left h102
  have h11 : 0 ≤ C_total := by
    dsimp only [C_total]
    exact add_nonneg h102 h_pos4
  have h12 : C_total ≤ C_total * Real.log (4 / δ) := by
    have h13 : C_total * 1 ≤ C_total * Real.log (4 / δ) :=
      mul_le_mul_of_nonneg_left h_log4_ge1 h11
    have h14 : C_total * 1 = C_total := by ring
    rw [h14] at h13
    exact h13
  have h14 : (4 : ℝ)^s ≤ C_total * Real.log (4 / δ) := h10.trans h12
  have h5 : (2 : ℝ)^s ≤ (4 : ℝ)^s := by
    apply Real.rpow_le_rpow <;> norm_num <;> linarith [hs]
  exact h5.trans h14

/-- Per-pair bound for regularized kernel sum over direction set
    with Frostman counting bound. -/
lemma per_pair_directional_sum_bound_reg
    {S : Finset ℝ} {δ C_dir : ℝ}
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hs : 0 < s)
    (hS_subset : ∀ σ ∈ S, -1 ≤ σ ∧ σ ≤ 1)
    (hS_nonempty : S.Nonempty)
    (h_count : ∀ (σ : ℝ) (r : ℝ), δ ≤ r →
      (S.filter (fun x => dist x σ ≤ r)).card ≤ C_dir * r ^ s * (S.card : ℝ))
    (v₀ v₁ : ℝ) (hv : (v₀, v₁) ≠ (0, 0))
    (hv0 : |v₀| ≤ 1) (hv1 : |v₁| ≤ 1) :
    ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
      (C_dir * (4 : ℝ)^s * 3 / Real.log 2 + (4 : ℝ)^s) * (S.card : ℝ) *
      Real.log (4 / δ) * (v₀^2 + v₁^2)^(-s/2) := by
  let norm_v := Real.sqrt (v₀^2 + v₁^2)
  have h_pos : 0 < v₀^2 + v₁^2 := by
    by_contra h
    have h' : v₀^2 + v₁^2 ≤ 0 := by linarith
    have h'' : v₀^2 + v₁^2 = 0 := by nlinarith
    have h2 : v₀ = 0 := by nlinarith
    have h3 : v₁ = 0 := by nlinarith
    simp [h2, h3] at hv <;> tauto
  have h_norm_pos : 0 < norm_v := Real.sqrt_pos.mpr h_pos
  have h_norm_sq : norm_v ^ 2 = v₀^2 + v₁^2 := Real.sq_sqrt (by nlinarith)
  have h_norm_rpow : norm_v^(-s) = (v₀^2 + v₁^2)^(-s/2) := norm_v_rpow v₀ v₁ s hs
  set C_total := C_dir * (4 : ℝ)^s * 3 / Real.log 2 + (4 : ℝ)^s with hC
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_log_ge : 2 ≤ Real.log (4 / δ) / Real.log 2 := log4_ge_two hδ hδ_le_one
  have h_log4_ge1 : 1 ≤ Real.log (4 / δ) := log4_ge_one hδ hδ_le_one
  have hC_dir_nonneg : 0 ≤ C_dir := by
    rcases hS_nonempty with ⟨σ, hσ⟩
    have hδ' : 0 ≤ δ := by linarith
    have h1 : 0 < (S.filter (fun x => dist x σ ≤ δ)).card := by
      apply Finset.card_pos.mpr
      exact ⟨σ, by simp [hσ, dist_self, hδ']⟩
    have h2 := h_count σ δ (by linarith)
    have h3 : (S.filter (fun x => dist x σ ≤ δ)).card ≤ C_dir * δ ^ s * (S.card : ℝ) := h2
    have h4 : (0 : ℝ) ≤ ↑(S.filter (fun x => dist x σ ≤ δ)).card := by positivity
    have h5 : (0 : ℝ) ≤ C_dir * δ ^ s * (S.card : ℝ) := le_trans h4 h3
    have h6 : 0 < δ ^ s := by positivity
    have h7 : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨σ, hσ⟩
    have h8 : 0 ≤ C_dir := by
      by_contra h9
      have h10 : C_dir < 0 := by linarith
      have h11 : C_dir * δ ^ s * (S.card : ℝ) < 0 := by
        have h12 : 0 < δ ^ s * (S.card : ℝ) := mul_pos h6 h7
        have h13 : C_dir * (δ ^ s * (S.card : ℝ)) < 0 := mul_neg_of_neg_of_pos h10 h12
        simpa [mul_assoc] using h13
      linarith
    exact h8
  by_cases h_case : |v₁| < norm_v / 2
  · -- Case A: |v₁| < ‖v‖/2
    have h_v1_sq : v₁^2 < norm_v^2 / 4 := by
      have h : |v₁| < norm_v / 2 := h_case
      have h2 : 0 ≤ |v₁| := abs_nonneg v₁
      have h3 : |v₁|^2 < (norm_v / 2)^2 := by gcongr
      have h4 : v₁^2 = |v₁|^2 := by rw [sq_abs]
      have h5 : (norm_v / 2)^2 = norm_v^2 / 4 := by ring
      rw [h4]
      rw [h5] at h3
      exact h3
    have h_v0_sq : v₀^2 > 3 * norm_v^2 / 4 := by
      have h : norm_v^2 = v₀^2 + v₁^2 := by rw [← h_norm_sq] <;> ring
      nlinarith
    have h_v0_abs : |v₀| > Real.sqrt 3 * norm_v / 2 := by
      have h4 : |v₀|^2 = v₀^2 := by rw [sq_abs]
      have h5 : (Real.sqrt 3 * norm_v / 2)^2 = 3 * norm_v^2 / 4 := by
        calc (Real.sqrt 3 * norm_v / 2)^2
          = (Real.sqrt 3)^2 * norm_v^2 / 4 := by ring
        _ = 3 * norm_v^2 / 4 := by rw [Real.sq_sqrt (by norm_num)] <;> ring
      have h6 : |v₀|^2 > (Real.sqrt 3 * norm_v / 2)^2 := by
        rw [h4, h5]
        exact h_v0_sq
      have h7 : 0 ≤ |v₀| := abs_nonneg v₀
      have h8 : 0 ≤ Real.sqrt 3 * norm_v / 2 := by
        have h81 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
        have h82 : 0 ≤ norm_v := by linarith
        positivity
      nlinarith
    have h_lower : ∀ σ ∈ S, |v₀ - σ * v₁| ≥ (Real.sqrt 3 - 1) * norm_v / 2 := by
      intro σ hσ
      have hσ2 : -1 ≤ σ ∧ σ ≤ 1 := hS_subset σ hσ
      have hσ3 : |σ| ≤ 1 := by
        rcases hσ2 with ⟨h1, h2⟩
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have h4 : |σ * v₁| = |σ| * |v₁| := by rw [abs_mul]
      have h5 : |σ| * |v₁| ≤ |v₁| := by
        have h6 : |σ| ≤ 1 := hσ3
        nlinarith [abs_nonneg v₁]
      calc |v₀ - σ * v₁| ≥ |v₀| - |σ * v₁| := by exact abs_sub_abs_le_abs_sub v₀ (σ * v₁)
        _ = |v₀| - |σ| * |v₁| := by rw [h4]
        _ ≥ |v₀| - |v₁| := by linarith
        _ ≥ (Real.sqrt 3 - 1) * norm_v / 2 := by linarith
    have h_pos : 0 < (Real.sqrt 3 - 1) * norm_v / 2 := by
      have h1 : 0 < Real.sqrt 3 - 1 := by linarith [sqrt3_gt_one]
      have h2 : 0 < norm_v := h_norm_pos
      positivity
    have h_kernel : ∀ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤ (3 : ℝ)^s * norm_v^(-s) := by
      intro σ hσ
      have h_d_ne_zero : v₀ - σ * v₁ ≠ 0 := by
        have h' : 0 < |v₀ - σ * v₁| := by
          have h : |v₀ - σ * v₁| ≥ (Real.sqrt 3 - 1) * norm_v / 2 := h_lower σ hσ
          linarith
        exact abs_pos.mp h'
      have h4 : ((Real.sqrt 3 - 1) / 2) ^ (-s) ≤ (3 : ℝ)^s := by
        have h51 : 1 < Real.sqrt 3 := sqrt3_gt_one
        have h5 : 0 < (Real.sqrt 3 - 1) / 2 := by
          have h52 : 0 < Real.sqrt 3 - 1 := by linarith
          positivity
        have h6 : ((Real.sqrt 3 - 1) / 2) ^ (-s) = (((Real.sqrt 3 - 1) / 2) ^ s)⁻¹ := by
          rw [Real.rpow_neg (by linarith)] <;> ring
        rw [h6]
        have h7 : (1 / 3 : ℝ) ≤ (Real.sqrt 3 - 1) / 2 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        have h8 : (1 / 3 : ℝ)^s ≤ ((Real.sqrt 3 - 1) / 2)^s := by gcongr <;> linarith
        have h91 : 0 < (1 / 3 : ℝ) ^ s := by positivity
        have h92 : 0 < ((Real.sqrt 3 - 1) / 2) ^ s := by positivity
        have h9 : (((Real.sqrt 3 - 1) / 2) ^ s)⁻¹ ≤ ((1 / 3 : ℝ) ^ s)⁻¹ := by exact inv_anti₀ h91 h8
        have h10 : ((1 / 3 : ℝ)^s)⁻¹ = (3 : ℝ)^s := by
          have h_mul : (1 / 3 : ℝ)^s * (3 : ℝ)^s = 1 := by
            have h2 : ((1 / 3 : ℝ) * (3 : ℝ))^s = (1 / 3 : ℝ)^s * (3 : ℝ)^s := by
              rw [Real.mul_rpow (by norm_num) (by norm_num)]
            have h3 : (1 / 3 : ℝ) * (3 : ℝ) = 1 := by norm_num
            rw [h3] at h2
            simpa using h2.symm
          have h_pos : 0 < (1 / 3 : ℝ)^s := by positivity
          field_simp [h_pos.ne'] <;> linarith
        calc (((Real.sqrt 3 - 1) / 2) ^ s)⁻¹
          ≤ ((1 / 3 : ℝ) ^ s)⁻¹ := h9
          _ = (3 : ℝ)^s := h10
      have h_kern1 : regularizedKernelReal s δ (v₀ - σ * v₁) ≤ |v₀ - σ * v₁| ^ (-s) := by
        have h_eq : regularizedKernelReal s δ (v₀ - σ * v₁) = min (|v₀ - σ * v₁| ^ (-s)) (δ ^ (-s)) := by
          rw [regularizedKernelReal_eq_min hs hδ h_d_ne_zero] <;> rfl
        rw [h_eq]
        exact min_le_left _ _
      calc regularizedKernelReal s δ (v₀ - σ * v₁)
        ≤ |v₀ - σ * v₁| ^ (-s) := h_kern1
        _ ≤ ((Real.sqrt 3 - 1) * norm_v / 2) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (h_lower σ hσ) (by linarith)
        _ = ((Real.sqrt 3 - 1) / 2) ^ (-s) * norm_v ^ (-s) := by
          have h31 : (Real.sqrt 3 - 1) * norm_v / 2 = ((Real.sqrt 3 - 1) / 2) * norm_v := by ring
          rw [h31]
          have h_pos_a : 0 ≤ (Real.sqrt 3 - 1) / 2 := by
            have h : 1 < Real.sqrt 3 := sqrt3_gt_one
            linarith
          have h_pos_b : 0 ≤ norm_v := by linarith
          rw [Real.mul_rpow h_pos_a h_pos_b] <;> ring
        _ ≤ (3 : ℝ)^s * norm_v ^ (-s) := by gcongr
    have h5 : (3 : ℝ)^s ≤ (4 : ℝ)^s := by gcongr <;> norm_num
    have h7 : (S.card : ℝ) * (3 : ℝ)^s * norm_v^(-s) ≤
        C_total * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) := by
      have h8 : (3 : ℝ)^s ≤ C_total * Real.log (4 / δ) := by
        have h9 : (3 : ℝ)^s ≤ (4 : ℝ)^s := h5
        have h102 : 0 ≤ C_dir * (4 : ℝ)^s * 3 / Real.log 2 := by positivity
        have h10 : (4 : ℝ)^s ≤ C_total := by
          simp only [hC]
          linarith
        have h11 : 0 ≤ C_total := by
          simp only [hC]
          positivity
        have h12 : C_total ≤ C_total * Real.log (4 / δ) := by
          have h13 : C_total * 1 ≤ C_total * Real.log (4 / δ) := mul_le_mul_of_nonneg_left h_log4_ge1 h11
          simpa using h13
        have h14 : (4 : ℝ)^s ≤ C_total * Real.log (4 / δ) := h10.trans h12
        exact h9.trans h14
      have h_mult : 0 ≤ (S.card : ℝ) * norm_v^(-s) := by positivity
      calc (S.card : ℝ) * (3 : ℝ)^s * norm_v^(-s)
        = (S.card : ℝ) * norm_v^(-s) * (3 : ℝ)^s := by ring
        _ ≤ (S.card : ℝ) * norm_v^(-s) * (C_total * Real.log (4 / δ)) := by
          exact mul_le_mul_of_nonneg_left h8 h_mult
        _ = C_total * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) := by ring
    calc ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁)
      ≤ ∑ σ ∈ S, (3 : ℝ)^s * norm_v^(-s) := Finset.sum_le_sum h_kernel
      _ = (S.card : ℝ) * (3 : ℝ)^s * norm_v^(-s) := by simp [Finset.sum_const] <;> ring
      _ ≤ C_total * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) := h7
      _ = C_total * (S.card : ℝ) * Real.log (4 / δ) * (v₀^2 + v₁^2)^(-s/2) := by
        rw [h_norm_rpow]
  · -- Case B: |v₁| ≥ ‖v‖/2
    have h_v1_ge : |v₁| ≥ norm_v / 2 := by linarith
    have h_v1_pos : 0 < |v₁| := by
      by_contra h
      have h' : |v₁| = 0 := by linarith
      have hz : v₁ = 0 := by simpa [abs_eq_zero] using h'
      rw [hz] at h_v1_ge
      have : norm_v ≤ 0 := by linarith
      have h_cont : norm_v < norm_v := by
        exact lt_of_le_of_lt this h_norm_pos
      exact False.elim (lt_irrefl norm_v h_cont)
    have h_v1_ne_zero : v₁ ≠ 0 := by simpa [abs_eq_zero] using h_v1_pos.ne'
    set σ₀ := v₀ / v₁ with hσ₀_def
    have h_abs_decomp : ∀ σ : ℝ, v₀ - σ * v₁ = v₁ * (σ₀ - σ) := by
      intro σ; simp [hσ₀_def, h_v1_ne_zero] <;> field_simp [h_v1_ne_zero] <;> ring
    set r₀ := δ / |v₁| with hr₀_def
    have hr₀_pos : 0 < r₀ := by positivity
    have hr₀_ge_delta : δ ≤ r₀ := by
      rw [hr₀_def]
      have h : |v₁| ≤ 1 := hv1
      have h2 : δ * |v₁| ≤ δ := by
        have h3 : |v₁| ≤ 1 := h
        nlinarith [hδ]
      have h4 : δ ≤ δ / |v₁| := by
        calc δ = (δ * |v₁|) / |v₁| := by field_simp [h_v1_pos.ne'] <;> ring
          _ ≤ δ / |v₁| := by gcongr
      exact h4
    let K := Nat.ceil (Real.log (4 / δ) / Real.log 2)
    have hK1_lt : (K : ℝ) < Real.log (4 / δ) / Real.log 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hK1 : (K : ℝ) ≤ Real.log (4 / δ) / Real.log 2 + 1 := le_of_lt hK1_lt
    have hK_ceil : Real.log (4 / δ) / Real.log 2 ≤ (K : ℝ) := Nat.le_ceil _
    have h_2s_ge1 : (1 : ℝ) ≤ (2 : ℝ)^s := two_pow_ge_one (show 0 ≤ s from by linarith)
    have ⟨h_K_bound, h_K_ge1⟩ : (K : ℝ) ≤ (3 / 2 : ℝ) * Real.log (4 / δ) / Real.log 2 ∧ (1 : ℝ) ≤ (K : ℝ) :=
      k_bounds hδ hδ_le_one hK1 hK_ceil h_log_ge
    have hK2 : (2^K : ℝ) * r₀ ≥ 4 := by
      have h1 : (K : ℝ) ≥ Real.log (4 / δ) / Real.log 2 := by
        exact Nat.le_ceil (Real.log (4 / δ) / Real.log 2)
      have h2 : (2^K : ℝ) ≥ 4 / δ := by
        have h3 : Real.log ((2^K : ℝ)) ≥ Real.log (4 / δ) := by
          have h4 : Real.log ((2^K : ℝ)) = (K : ℝ) * Real.log 2 := by rw [Real.log_pow] <;> ring
          rw [h4]
          have h5 : (K : ℝ) * Real.log 2 ≥ Real.log (4 / δ) := by
            have h6 : (K : ℝ) * Real.log 2 ≥ (Real.log (4 / δ) / Real.log 2) * Real.log 2 := by gcongr
            have h7 : (Real.log (4 / δ) / Real.log 2) * Real.log 2 = Real.log (4 / δ) := by
              field_simp [h_log2_pos.ne'] <;> ring
            rw [h7] at h6; exact h6
          exact h5
        have h5 : (0 : ℝ) < 4 / δ := by positivity
        exact (Real.log_le_log_iff h5 (by positivity)).mp h3
      have h6 : (2^K : ℝ) * r₀ ≥ (4 / δ) * r₀ := by
        have h61 : (2^K : ℝ) ≥ 4 / δ := h2
        have h62 : 0 ≤ r₀ := by linarith
        exact mul_le_mul_of_nonneg_right h61 h62
      have h7 : (4 / δ) * r₀ = 4 / |v₁| := by
        rw [hr₀_def] <;> field_simp [h_v1_pos.ne'] <;> ring
      have h8 : (2^K : ℝ) * r₀ ≥ 4 / |v₁| := by
        rw [h7] at h6
        exact h6
      have h9 : 4 / |v₁| ≥ 4 := by
        have h10 : |v₁| ≤ 1 := hv1
        calc 4 / |v₁| ≥ 4 / 1 := by gcongr
          _ = 4 := by norm_num
      calc (2^K : ℝ) * r₀ ≥ 4 / |v₁| := h8
        _ ≥ 4 := h9
    by_cases hσ₀_large : |σ₀| > 2
    · -- B1: |σ₀| > 2
      have h_kernel : ∀ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤ (2 : ℝ)^s * norm_v^(-s) :=
        case_b1_kernel_bound hs hδ hS_subset h_norm_pos h_v1_ge h_v1_ne_zero h_abs_decomp hσ₀_large
      have h8 : (2 : ℝ)^s ≤ C_total * Real.log (4 / δ) :=
        constant_bounds hs hδ hδ_le_one hC_dir_nonneg h_log4_ge1
      have h_norm_v_nonneg : 0 ≤ norm_v^(-s) := Real.rpow_nonneg (by linarith) (-s)
      have h_card_nonneg : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg S.card
      have h_mult : 0 ≤ (S.card : ℝ) * norm_v^(-s) := mul_nonneg h_card_nonneg h_norm_v_nonneg
      have h7 : (S.card : ℝ) * (2 : ℝ)^s * norm_v^(-s) ≤
          C_total * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) := by
        calc (S.card : ℝ) * (2 : ℝ)^s * norm_v^(-s)
          = (S.card : ℝ) * norm_v^(-s) * (2 : ℝ)^s := by ring
        _ ≤ (S.card : ℝ) * norm_v^(-s) * (C_total * Real.log (4 / δ)) :=
          mul_le_mul_of_nonneg_left h8 h_mult
        _ = C_total * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) := by ring
      have h_sum_bound : ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
          C_total * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) := by
        calc ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁)
          ≤ ∑ σ ∈ S, (2 : ℝ)^s * norm_v^(-s) := Finset.sum_le_sum h_kernel
        _ = (S.card : ℝ) * (2 : ℝ)^s * norm_v^(-s) := by simp [Finset.sum_const] <;> ring
        _ ≤ C_total * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) := h7
      rw [h_norm_rpow] at *
      exact h_sum_bound
    · -- B2: |σ₀| ≤ 2
      have hσ₀_le : |σ₀| ≤ 2 := by linarith
      have h_max_dist : ∀ σ ∈ S, |σ - σ₀| ≤ 3 := by
        intro σ hσ
        have hσ2 : -1 ≤ σ ∧ σ ≤ 1 := hS_subset σ hσ
        have hσ3 : |σ| ≤ 1 := by rcases hσ2 with ⟨h1,h2⟩; exact abs_le.mpr ⟨by linarith, by linarith⟩
        have h_abs : |σ - σ₀| ≤ |σ| + |σ₀| := by exact abs_sub σ σ₀
        calc |σ - σ₀| ≤ |σ| + |σ₀| := h_abs
          _ ≤ 1 + 2 := by linarith
          _ = 3 := by norm_num
      let T := S.filter (fun σ => r₀ ≤ |σ - σ₀|)
      let inner := S.filter (fun σ => |σ - σ₀| < r₀)
      have h_partition : S = T ∪ inner := by
        ext σ
        simp only [T, inner, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hσS
          by_cases h : r₀ ≤ |σ - σ₀|
          · exact Or.inl ⟨hσS, h⟩
          · have h' : |σ - σ₀| < r₀ := by exact lt_of_not_ge h
            exact Or.inr ⟨hσS, h'⟩
        · rintro (⟨hσS, _⟩ | ⟨hσS, _⟩) <;> exact hσS
      have h_disj : Disjoint T inner := by
        rw [Finset.disjoint_left]; intro σ h1 h2
        have h3 : r₀ ≤ |σ - σ₀| := (Finset.mem_filter.mp h1).2
        have h4 : |σ - σ₀| < r₀ := (Finset.mem_filter.mp h2).2; linarith
      have hT_sub : T ⊆ S := by
        intro σ hσ; exact (Finset.mem_filter.mp hσ).1
      have hT_ge : ∀ σ ∈ T, r₀ ≤ |σ - σ₀| := by
        intro σ hσ; exact (Finset.mem_filter.mp hσ).2
      have hT_lt : ∀ σ ∈ T, |σ - σ₀| < (2^K : ℝ) * r₀ :=
        hT_lt_lemma hT_sub h_max_dist hK2
      -- Inner region
      have h_inner_count : inner.card ≤ C_dir * r₀^s * (S.card : ℝ) := by
        have h1 : inner ⊆ S.filter (fun x => dist x σ₀ ≤ r₀) := by
          intro σ hσ
          have hσS : σ ∈ S := (Finset.mem_filter.mp hσ).1
          have h2 : |σ - σ₀| < r₀ := (Finset.mem_filter.mp hσ).2
          have h3 : dist σ σ₀ ≤ r₀ := by simpa [dist_eq_norm] using le_of_lt h2
          exact Finset.mem_filter.mpr ⟨hσS, h3⟩
        have h4 : inner.card ≤ (S.filter (fun x => dist x σ₀ ≤ r₀)).card := Finset.card_le_card h1
        have h5 : ((S.filter (fun x => dist x σ₀ ≤ r₀)).card : ℝ) ≤ C_dir * r₀ ^ s * (S.card : ℝ) := h_count σ₀ r₀ hr₀_ge_delta
        have h6 : (inner.card : ℝ) ≤ ((S.filter (fun x => dist x σ₀ ≤ r₀)).card : ℝ) := by exact_mod_cast h4
        exact h6.trans h5
      have h_inner_sum : ∑ σ ∈ inner, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
          C_dir * |v₁|^(-s) * (S.card : ℝ) := by
        have h_kern : ∀ σ ∈ inner, regularizedKernelReal s δ (v₀ - σ * v₁) ≤ δ^(-s) := by
          intro σ hσ
          by_cases h : σ₀ - σ = 0
          · have h_zero : v₀ - σ * v₁ = 0 := by
              rw [h_abs_decomp σ, h] <;> ring
            rw [h_zero, regularizedKernelReal, if_pos rfl]
            <;> positivity
          · have h_d : v₀ - σ * v₁ ≠ 0 := by
              rw [h_abs_decomp σ]; exact mul_ne_zero h_v1_ne_zero h
            have h_eq : regularizedKernelReal s δ (v₀ - σ * v₁) = min (|v₀ - σ * v₁|^(-s)) (δ^(-s)) :=
              regularizedKernelReal_eq_min hs hδ h_d
            rw [h_eq]
            exact min_le_right _ _
        calc ∑ σ ∈ inner, _
          ≤ ∑ σ ∈ inner, δ^(-s) := Finset.sum_le_sum h_kern
          _ = (inner.card : ℝ) * δ^(-s) := by simp [Finset.sum_const] <;> ring
          _ ≤ (C_dir * r₀^s * (S.card : ℝ)) * δ^(-s) := by gcongr
          _ = C_dir * |v₁|^(-s) * (S.card : ℝ) := by
            have h9 : r₀^s = δ^s * |v₁|^(-s) := by
              rw [hr₀_def, Real.div_rpow (by positivity) (by positivity)]
              have h10 : (|v₁|^s)⁻¹ = |v₁|^(-s) := by
                rw [Real.rpow_neg (by positivity)]
              rw [div_eq_mul_inv, h10] <;> ring
            rw [h9]
            exact inner_sum_algebra hδ h_v1_pos
      -- Outer region via dyadic annuli
      have h_outer_sum : ∑ σ ∈ T, |σ - σ₀| ^ (-s) ≤
          (K : ℝ) * C_dir * (2 : ℝ)^s * (S.card : ℝ) :=
        dyadic_outer_sum hs hδ hr₀_pos hr₀_ge_delta hS_subset h_count T hT_sub hT_ge hT_lt
      have h_outer_kernel : ∀ σ ∈ T, regularizedKernelReal s δ (v₀ - σ * v₁) = |v₁|^(-s) * |σ - σ₀|^(-s) := by
        intro σ hσ
        have h_ge : r₀ ≤ |σ - σ₀| := (Finset.mem_filter.mp hσ).2
        exact outer_kernel_eq hδ hs h_v1_pos hr₀_pos hr₀_def h_abs_decomp σ h_ge
      have h_outer_sum2 : ∑ σ ∈ T, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
          |v₁|^(-s) * ((K : ℝ) * C_dir * (2 : ℝ)^s * (S.card : ℝ)) :=
        outer_sum2_bound h_outer_sum h_outer_kernel h_v1_pos
      have h_K_ge1 : (1 : ℝ) ≤ (K : ℝ) := k_ge1_lemma hK_ceil h_log_ge
      have h_combined : ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
          |v₁|^(-s) * C_dir * (S.card : ℝ) * (2 * (K : ℝ) * (2 : ℝ)^s) :=
        b2_combined_bound h_partition h_disj hC_dir_nonneg h_outer_sum2 h_inner_sum h_K_ge1 h_2s_ge1
      have h_v1_bound : |v₁|^(-s) ≤ (2 : ℝ)^s * norm_v^(-s) :=
        v1_bound_lemma hs h_norm_pos h_v1_ge
      have h_final : ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
          C_dir * (4 : ℝ)^s * 3 / Real.log 2 * (S.card : ℝ) * Real.log (4 / δ) * norm_v^(-s) :=
        final_bound_lemma hs hC_dir_nonneg h_log4_ge1 h_combined h_K_bound h_v1_bound
      exact conclude_b2 hs hC_dir_nonneg h_log4_ge1 h_norm_pos hC h_norm_rpow h_final

/-! ### Averaging theorem -/

/-- Average regularized projected energy over a finite direction set. -/
theorem projected_energy_average_reg
    {μ : Measure EuclideanPlane} [MeasureTheory.SFinite μ] [MeasureTheory.IsProbabilityMeasure μ]
    {S : Finset ℝ} {δ C_dir : ℝ}
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hs : 0 < s)
    (hS_subset : ∀ σ ∈ S, -1 ≤ σ ∧ σ ≤ 1)
    (hS_nonempty : S.Nonempty)
    (h_count : ∀ (σ : ℝ) (r : ℝ), δ ≤ r →
      (S.filter (fun x => dist x σ ≤ r)).card ≤ C_dir * r ^ s * (S.card : ℝ))
    (hμ_unit : ∀ᵐ (x : EuclideanPlane) ∂μ,
      x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ x 1 ∈ Set.Icc (0 : ℝ) 1) :
    (∑ σ ∈ S, projectedEnergyReg μ s δ σ) ≤
      ENNReal.ofReal ((C_dir * (4 : ℝ)^s * 3 / Real.log 2 + (4 : ℝ)^s) * (S.card : ℝ) * Real.log (4 / δ)) *
      planeEnergy μ s + ENNReal.ofReal (δ ^ (-s)) := by
  set C_total := C_dir * (4 : ℝ)^s * 3 / Real.log 2 + (4 : ℝ)^s with hC
  set C_ennreal := ENNReal.ofReal (C_total * (S.card : ℝ) * Real.log (4 / δ)) with hCenn
  have hC_dir_nonneg : 0 ≤ C_dir := by
    rcases hS_nonempty with ⟨σ, hσ⟩
    have h1 : 0 < (S.filter (fun x => dist x σ ≤ δ)).card := by
      apply Finset.card_pos.mpr
      exact ⟨σ, by simp [hσ, dist_self, show 0 ≤ δ by linarith]⟩
    have h2 := h_count σ δ (by linarith)
    have h3 : (0 : ℝ) ≤ C_dir * δ ^ s * (S.card : ℝ) := le_trans (by positivity) h2
    have h4 : 0 < δ ^ s := by positivity
    have h5 : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨σ, hσ⟩
    by_contra h6
    have h7 : C_dir < 0 := by linarith
    have h71 : C_dir * δ ^ s < 0 := mul_neg_of_neg_of_pos h7 h4
    have h8 : 0 < (S.card : ℝ) := h5
    have h9 : C_dir * δ ^ s * (S.card : ℝ) < 0 := mul_neg_of_neg_of_pos h71 h8
    linarith
  have hC_total_nonneg : 0 ≤ C_total := by
    have h101 : 0 ≤ C_dir := hC_dir_nonneg
    simp only [hC]
    positivity
  have h_log_pos : 0 < Real.log (4 / δ) := by
    have h4 : δ < 4 := by linarith
    have h5 : 1 < 4 / δ := (one_lt_div (by positivity)).mpr h4
    exact Real.log_pos h5
  have hC_nonneg : 0 ≤ C_total * (S.card : ℝ) * Real.log (4 / δ) := by positivity
  have h_main_ae : ∀ᵐ (x : EuclideanPlane) ∂μ, ∀ᵐ (y : EuclideanPlane) ∂μ,
      (∑ σ ∈ S, projectedKernelReg s δ σ x y) ≤
      C_ennreal * planeKernel s x y + ENNReal.ofReal (δ ^ (-s)) := by
    filter_upwards [hμ_unit] with x hx
    filter_upwards [hμ_unit] with y hy
    by_cases hxy : x = y
    · rw [hxy]
      simp [planeKernel, projectedKernelReg, regularizedKernel, regularizedKernelReal]
      <;> norm_num
    · let v₀ := x 0 - y 0
      let v₁ := x 1 - y 1
      let c : ENNReal := ENNReal.ofReal (δ ^ (-s))
      let dσ : ℝ → ℝ := fun σ => (x 0 - σ * x 1) - (y 0 - σ * y 1)
      have hv : (v₀, v₁) ≠ (0, 0) := by
        intro h; have h1 : v₀ = 0 := by simp [Prod.ext_iff] at h <;> tauto
        have h2 : v₁ = 0 := by simp [Prod.ext_iff] at h <;> tauto
        have h3 : x = y := by ext i; fin_cases i <;> simp [v₀, v₁, h1, h2] <;> linarith
        exact hxy h3
      have hv0 : |v₀| ≤ 1 := by
        have hx0 : x 0 ∈ Set.Icc (0 : ℝ) 1 := hx.1
        have hy0 : y 0 ∈ Set.Icc (0 : ℝ) 1 := hy.1
        simp only [Set.mem_Icc] at hx0 hy0
        exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      have hv1 : |v₁| ≤ 1 := by
        have hx1 : x 1 ∈ Set.Icc (0 : ℝ) 1 := hx.2
        have hy1 : y 1 ∈ Set.Icc (0 : ℝ) 1 := hy.2
        simp only [Set.mem_Icc] at hx1 hy1
        exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      have h_bound : ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) ≤
          C_total * (S.card : ℝ) * Real.log (4 / δ) * (v₀^2 + v₁^2)^(-s/2) :=
        per_pair_directional_sum_bound_reg hδ hδ_le_one hs hS_subset hS_nonempty h_count v₀ v₁ hv hv0 hv1
      have h_sum_real : (∑ σ ∈ S, regularizedKernelReal s δ ((x 0 - σ * x 1) - (y 0 - σ * y 1))) =
          ∑ σ ∈ S, regularizedKernelReal s δ (v₀ - σ * v₁) := by
        apply Finset.sum_congr rfl
        intro σ _
        dsimp only [v₀, v₁] <;> ring_nf
      have h_bound2 : ∑ σ ∈ S, regularizedKernelReal s δ ((x 0 - σ * x 1) - (y 0 - σ * y 1)) ≤
          C_total * (S.card : ℝ) * Real.log (4 / δ) * (v₀^2 + v₁^2)^(-s/2) := by
        rw [h_sum_real]; exact h_bound
      -- Decomposition: projectedKernelReg = ofReal(regularizedKernelReal) + collision
      have h_decomp : ∀ σ ∈ S, projectedKernelReg s δ σ x y =
          ENNReal.ofReal (regularizedKernelReal s δ (dσ σ)) +
          (if dσ σ = 0 then c else 0) := by
        intro σ _
        by_cases h : dσ σ = 0
        · rw [projectedKernelReg_of_ne hxy]
          have h_d0 : dσ σ = 0 := h
          have h_if : (if dσ σ = 0 then c else 0) = c := by
            rw [if_pos h_d0]
          rw [h_if]
          have h_lhs : ENNReal.ofReal ((max |dσ σ| δ) ^ (-s)) = c := by
            rw [h_d0]
            have h_max : max |(0 : ℝ)| δ = δ := by
              simp [max_eq_right, hδ.le]
            rw [h_max] <;> rfl
          have h_rhs : ENNReal.ofReal (regularizedKernelReal s δ (dσ σ)) + c = c := by
            rw [h_d0]
            simp [regularizedKernelReal, c] <;> rfl
          rw [h_lhs, h_rhs]
        · rw [projectedKernelReg_of_ne hxy]
          have h_eq : (max |dσ σ| δ) ^ (-s) = regularizedKernelReal s δ (dσ σ) :=
            max_rpow_eq_regularized hs hδ h
          rw [h_eq]
          simp [h] <;> rfl
      have h_sum_decomp : (∑ σ ∈ S, projectedKernelReg s δ σ x y) =
          ENNReal.ofReal (∑ σ ∈ S, regularizedKernelReal s δ (dσ σ)) +
          ∑ σ ∈ S, (if dσ σ = 0 then c else 0) := by
        have h3 : ∑ σ ∈ S, projectedKernelReg s δ σ x y =
            ∑ σ ∈ S, (ENNReal.ofReal (regularizedKernelReal s δ (dσ σ)) +
              (if dσ σ = 0 then c else 0)) :=
          Finset.sum_congr rfl h_decomp
        rw [h3, Finset.sum_add_distrib]
        have h4 : ∑ σ ∈ S, ENNReal.ofReal (regularizedKernelReal s δ (dσ σ)) =
            ENNReal.ofReal (∑ σ ∈ S, regularizedKernelReal s δ (dσ σ)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          · intro σ _; simp [regularizedKernelReal] <;> positivity
        rw [h4]
      -- Collision sum ≤ c (at most one σ has dσ σ = 0)
      have h_collision_le : ∑ σ ∈ S, (if dσ σ = 0 then c else 0) ≤ c := by
        by_cases hv1 : v₁ = 0
        · have hv0_ne : v₀ ≠ 0 := by
            intro h; have h' : x = y := by ext i; fin_cases i <;> simp [v₀, v₁, h, hv1] <;> linarith
            exact hxy h'
          have h_no : ∀ σ ∈ S, dσ σ ≠ 0 := by
            intro σ _
            have h : dσ σ = v₀ - σ * v₁ := by dsimp only [dσ, v₀, v₁]; ring
            have h_dσ_eq : dσ σ = v₀ := by
              rw [h, hv1] <;> ring
            rw [h_dσ_eq]
            exact hv0_ne
          have h_sum_zero : ∑ σ ∈ S, (if dσ σ = 0 then c else 0) = 0 := by
            apply Finset.sum_eq_zero; intro σ hσ; have h5 := h_no σ hσ; rw [if_neg h5] <;> simp
          rw [h_sum_zero] <;> positivity
        · let Z := S.filter (fun σ => dσ σ = 0)
          have hZ_at_most_one : Z.card ≤ 1 := by
            have h_dσ_eq : ∀ σ, dσ σ = v₀ - σ * v₁ := by
              intro σ; dsimp only [dσ, v₀, v₁]; ring
            have h_unique : ∀ σ₁ ∈ Z, ∀ σ₂ ∈ Z, σ₁ = σ₂ := by
              intro σ₁ hσ₁ σ₂ hσ₂
              have h_eq1 : dσ σ₁ = 0 := (Finset.mem_filter.mp hσ₁).2
              have h_eq2 : dσ σ₂ = 0 := (Finset.mem_filter.mp hσ₂).2
              have h1 : v₀ - σ₁ * v₁ = 0 := by
                rw [←h_dσ_eq σ₁]; exact h_eq1
              have h2 : v₀ - σ₂ * v₁ = 0 := by
                rw [←h_dσ_eq σ₂]; exact h_eq2
              have h3 : (σ₁ - σ₂) * v₁ = 0 := by linarith
              have h4 : σ₁ - σ₂ = 0 := by
                apply (mul_eq_zero.mp h3).resolve_right
                exact hv1
              linarith
            by_contra h
            have h' : 1 < Z.card := by omega
            rcases Finset.one_lt_card.mp h' with ⟨σ₁, hσ₁, σ₂, hσ₂, hne⟩
            exact hne (h_unique σ₁ hσ₁ σ₂ hσ₂)
          have h_sumZ : ∑ σ ∈ S, (if dσ σ = 0 then c else 0) = ∑ σ ∈ Z, c := by
            rw [Finset.sum_ite]
            <;> simp [Z]
          rw [h_sumZ]
          have h5 : ∑ σ ∈ Z, c = (Z.card : ENNReal) * c := by
            simp [Finset.sum_const] <;> ring
          rw [h5]
          have h6 : (Z.card : ENNReal) ≤ 1 := by exact_mod_cast hZ_at_most_one
          have h7 : (Z.card : ENNReal) * c ≤ 1 * c := by
            exact mul_le_mul_of_nonneg_right h6 (by positivity)
          simpa using h7
      rw [h_sum_decomp]
      have h3 : ENNReal.ofReal (∑ σ ∈ S, regularizedKernelReal s δ (dσ σ)) ≤
          ENNReal.ofReal (C_total * (S.card : ℝ) * Real.log (4 / δ) * (v₀^2 + v₁^2)^(-s/2)) :=
        ENNReal.ofReal_le_ofReal h_bound2
      have h4 : planeKernel s x y = ENNReal.ofReal ((v₀^2 + v₁^2)^(-s/2)) := by
        have h5 : ‖x - y‖ = Real.sqrt (v₀^2 + v₁^2) := by
          simp [v₀, v₁, EuclideanSpace.norm_eq] <;> rfl
        rw [planeKernel, if_neg hxy, h5]
        have h6 : (Real.sqrt (v₀^2 + v₁^2)) ^ (-s) = (v₀^2 + v₁^2)^(-s/2) :=
          norm_v_rpow v₀ v₁ s hs
        rw [h6]
      have h_goal : C_ennreal * planeKernel s x y =
          ENNReal.ofReal (C_total * (S.card : ℝ) * Real.log (4 / δ) * (v₀^2 + v₁^2)^(-s/2)) := by
        rw [hCenn, h4]
        rw [ENNReal.ofReal_mul hC_nonneg] <;> rfl
      exact add_le_add (h3.trans_eq h_goal.symm) h_collision_le
  have h_swap1 : (∑ σ ∈ S, projectedEnergyReg μ s δ σ) =
      ∑ σ ∈ S, ∫⁻ x, ∫⁻ y, projectedKernelReg s δ σ x y ∂μ ∂μ := by
    apply Finset.sum_congr rfl
    intro σ _
    rfl
  have h_lintegral_sum_general : ∀ (s : Finset ℝ) (g : ℝ → EuclideanPlane → ENNReal),
      (∀ σ ∈ s, Measurable (g σ)) →
      ∫⁻ x, ∑ σ ∈ s, g σ x ∂μ = ∑ σ ∈ s, ∫⁻ x, g σ x ∂μ := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro g _
      simp
    | @insert a s ha ih =>
      intro g hg
      have h_goal1 : ∫⁻ x, ∑ σ ∈ insert a s, g σ x ∂μ =
          ∫⁻ x, (g a x + ∑ σ ∈ s, g σ x) ∂μ := by
        congr with x
        rw [Finset.sum_insert ha]
      rw [h_goal1]
      have h_meas : Measurable (g a) := hg a (Finset.mem_insert_self a s)
      rw [lintegral_add_left h_meas]
      have h_restrict : ∀ σ ∈ s, Measurable (g σ) := fun σ hσ => hg σ (Finset.mem_insert_of_mem hσ)
      rw [ih g h_restrict]
      rw [Finset.sum_insert ha]
  have h_meas_reg : Measurable (fun d : ℝ => regularizedKernelReal s δ d) := by
    have h1 : Measurable (fun d : ℝ => |d| ^ (-s)) := by fun_prop
    have h2 : Measurable (fun d : ℝ => min (|d| ^ (-s)) (δ ^ (-s))) := by
      exact h1.min measurable_const
    have h4 : MeasurableSet ({0} : Set ℝ) := measurableSet_singleton (0 : ℝ)
    have h3 : Measurable (fun d : ℝ => if d = 0 then (0 : ℝ) else min (|d| ^ (-s)) (δ ^ (-s))) := by
      exact Measurable.ite h4 measurable_const h2
    simpa [regularizedKernelReal] using h3
  have h_meas_kernel : ∀ (x : EuclideanPlane) (σ : ℝ), Measurable (fun y : EuclideanPlane => projectedKernelReg s δ σ x y) := by
    intro x σ
    let d : EuclideanPlane → ℝ := fun y => (x 0 - σ * x 1) - (y 0 - σ * y 1)
    have hd_meas : Measurable d := by measurability
    have hsing : MeasurableSet ({x} : Set EuclideanPlane) := measurableSet_singleton x
    have h_main_meas : Measurable (fun y : EuclideanPlane => ENNReal.ofReal ((max |d y| δ) ^ (-s))) := by
      have h2 : Measurable (fun y => max |d y| δ) := by fun_prop
      have h3 : Measurable (fun (_ : EuclideanPlane) => (-s : ℝ)) := measurable_const
      have h_rpow : Measurable (fun q : ℝ × ℝ => q.1 ^ q.2) := by exact measurable_pow
      have h_pair : Measurable (fun y : EuclideanPlane => (max |d y| δ, -s)) := by fun_prop
      have h4 : Measurable (fun y => (max |d y| δ) ^ (-s)) := h_rpow.comp h_pair
      exact ENNReal.measurable_ofReal.comp h4
    have h_eq : (fun y : EuclideanPlane => projectedKernelReg s δ σ x y) =
        fun y : EuclideanPlane => if y = x then (0 : ENNReal) else ENNReal.ofReal ((max |d y| δ) ^ (-s)) := by
      funext y
      by_cases h : y = x
      · have hxy : x = y := h.symm
        rw [projectedKernelReg, if_pos hxy, if_pos h]
      · have hxy : x ≠ y := by intro h2; exact h h2.symm
        rw [projectedKernelReg, if_neg hxy, if_neg h] <;> rfl
    rw [h_eq]
    have h_then : Measurable (fun (_ : EuclideanPlane) => (0 : ENNReal)) := by exact measurable_const
    exact Measurable.ite hsing h_then h_main_meas
  have h_swap2 : ∑ σ ∈ S, ∫⁻ x, ∫⁻ y, projectedKernelReg s δ σ x y ∂μ ∂μ ≤
      ∫⁻ x, ∫⁻ y, ∑ σ ∈ S, projectedKernelReg s δ σ x y ∂μ ∂μ := by
    let g : ℝ → EuclideanPlane → ENNReal := fun σ x => ∫⁻ y, projectedKernelReg s δ σ x y ∂μ
    have h_sum_pointwise : ∀ (x : EuclideanPlane),
        (∑ σ ∈ S, g σ x) = ∫⁻ y, ∑ σ ∈ S, projectedKernelReg s δ σ x y ∂μ := by
      intro x
      have h_ind : ∀ (t : Finset ℝ), ∑ σ ∈ t, g σ x = ∫⁻ y, ∑ σ ∈ t, projectedKernelReg s δ σ x y ∂μ := by
        intro t
        induction t using Finset.induction with
        | empty => simp
        | @insert a t ha ih =>
          have h1 : ∑ σ ∈ insert a t, g σ x = g a x + ∑ σ ∈ t, g σ x := by
            rw [Finset.sum_insert ha]
          have h2 : ∀ (y : EuclideanPlane), ∑ σ ∈ insert a t, projectedKernelReg s δ σ x y =
              projectedKernelReg s δ a x y + ∑ σ ∈ t, projectedKernelReg s δ σ x y := by
            intro y; rw [Finset.sum_insert ha]
          have h3 : ∫⁻ y, ∑ σ ∈ insert a t, projectedKernelReg s δ σ x y ∂μ =
              ∫⁻ y, (projectedKernelReg s δ a x y + ∑ σ ∈ t, projectedKernelReg s δ σ x y) ∂μ := by
            apply lintegral_congr; intro y; exact h2 y
          rw [h1, h3]
          rw [lintegral_add_left (h_meas_kernel x a)]
          rw [ih]
      exact h_ind S
    have h_sum_le : ∑ σ ∈ S, ∫⁻ x, g σ x ∂μ ≤ ∫⁻ x, ∑ σ ∈ S, g σ x ∂μ := by
      have h_ind : ∀ (t : Finset ℝ), ∑ σ ∈ t, ∫⁻ x, g σ x ∂μ ≤ ∫⁻ x, ∑ σ ∈ t, g σ x ∂μ := by
        intro t
        induction t using Finset.induction with
        | empty => simp
        | @insert a t ha ih =>
          have h_step1 : ∑ σ ∈ insert a t, ∫⁻ x, g σ x ∂μ =
              ∫⁻ x, g a x ∂μ + ∑ σ ∈ t, ∫⁻ x, g σ x ∂μ := by
            have h : ∑ σ ∈ insert a t, ∫⁻ x, g σ x ∂μ = (∫⁻ x, g a x ∂μ) + ∑ σ ∈ t, ∫⁻ x, g σ x ∂μ := by
              rw [Finset.sum_insert ha]
              <;> rfl
            exact h
          calc ∑ σ ∈ insert a t, ∫⁻ x, g σ x ∂μ
            = ∫⁻ x, g a x ∂μ + ∑ σ ∈ t, ∫⁻ x, g σ x ∂μ := h_step1
            _ ≤ ∫⁻ x, g a x ∂μ + ∫⁻ x, ∑ σ ∈ t, g σ x ∂μ := by gcongr
            _ ≤ ∫⁻ x, (g a x + ∑ σ ∈ t, g σ x) ∂μ := by
              let f : EuclideanPlane → ENNReal := g a
              let h : EuclideanPlane → ENNReal := fun x => ∑ σ ∈ t, g σ x
              have h_lea : ∫⁻ x, f x ∂μ + ∫⁻ x, h x ∂μ ≤ ∫⁻ x, (f x + h x) ∂μ :=
                le_lintegral_add (μ := μ) (f := f) (g := h)
              exact h_lea
            _ = ∫⁻ x, ∑ σ ∈ insert a t, g σ x ∂μ := by
              have h_eq : (fun x => g a x + ∑ σ ∈ t, g σ x) = (fun x => ∑ σ ∈ insert a t, g σ x) := by
                funext x; rw [Finset.sum_insert ha]
              rw [h_eq]
      exact h_ind S
    have hfg : (fun x : EuclideanPlane => ∑ σ ∈ S, g σ x) =
        (fun x : EuclideanPlane => ∫⁻ y, ∑ σ ∈ S, projectedKernelReg s δ σ x y ∂μ) := by
      funext x; exact h_sum_pointwise x
    calc ∑ σ ∈ S, ∫⁻ x, ∫⁻ y, projectedKernelReg s δ σ x y ∂μ ∂μ
      = ∑ σ ∈ S, ∫⁻ x, g σ x ∂μ := by rfl
      _ ≤ ∫⁻ x, ∑ σ ∈ S, g σ x ∂μ := h_sum_le
      _ = ∫⁻ x, ∫⁻ y, ∑ σ ∈ S, projectedKernelReg s δ σ x y ∂μ ∂μ := by
        rw [hfg]
  have h5 : ∫⁻ x, ∫⁻ y, (∑ σ ∈ S, projectedKernelReg s δ σ x y) ∂μ ∂μ ≤
      ∫⁻ x, ∫⁻ y, (C_ennreal * planeKernel s x y + ENNReal.ofReal (δ ^ (-s))) ∂μ ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [h_main_ae] with x hx
    exact lintegral_mono_ae hx
  have hC_finite : C_ennreal ≠ ⊤ := ENNReal.ofReal_ne_top
  have hδs_finite : ENNReal.ofReal (δ ^ (-s)) ≠ ⊤ := ENNReal.ofReal_ne_top
  let c : ENNReal := ENNReal.ofReal (δ ^ (-s))
  have h6 : ∫⁻ x, ∫⁻ y, (C_ennreal * planeKernel s x y + c) ∂μ ∂μ =
      C_ennreal * planeEnergy μ s + c := by
    have h7 : ∀ (x : EuclideanPlane), ∫⁻ y, (C_ennreal * planeKernel s x y + c) ∂μ =
        C_ennreal * ∫⁻ y, planeKernel s x y ∂μ + c := by
      intro x
      have h_meas : Measurable (fun y => C_ennreal * planeKernel s x y) :=
        measurable_const.mul planeKernel_measurable
      rw [lintegral_add_left h_meas]
      have h_const : ∫⁻ y, c ∂μ = c := by
        simp [MeasureTheory.lintegral_const, MeasureTheory.measure_univ]
      rw [h_const]
      have h_mul : ∫⁻ y, C_ennreal * planeKernel s x y ∂μ = C_ennreal * ∫⁻ y, planeKernel s x y ∂μ :=
        MeasureTheory.lintegral_const_mul' C_ennreal (fun y => planeKernel s x y) hC_finite
      rw [h_mul] <;> ring
    have h8 : ∫⁻ x, (∫⁻ y, (C_ennreal * planeKernel s x y + c) ∂μ) ∂μ =
        ∫⁻ x, (C_ennreal * ∫⁻ y, planeKernel s x y ∂μ + c) ∂μ := by
      apply lintegral_congr; intro x; exact h7 x
    rw [h8]
    have h_joint : Measurable (Function.uncurry (fun (x y : EuclideanPlane) => planeKernel s x y)) := by
      let P := EuclideanPlane × EuclideanPlane
      have h1 : MeasurableSet {p : P | p.1 = p.2} :=
        measurableSet_eq_fun (measurable_fst : Measurable (Prod.fst : P → EuclideanPlane))
          (measurable_snd : Measurable (Prod.snd : P → EuclideanPlane))
      have h21 : Measurable (fun (p : P) => ‖p.1 - p.2‖) := by fun_prop
      have h_rpow : Measurable (fun q : ℝ × ℝ => q.1 ^ q.2) := by exact measurable_pow
      have h_pair : Measurable (fun (p : P) => (‖p.1 - p.2‖, -s)) := by fun_prop
      have h2 : Measurable (fun (p : P) => ‖p.1 - p.2‖ ^ (-s)) := h_rpow.comp h_pair
      have h3 : Measurable (fun (p : P) => ENNReal.ofReal (‖p.1 - p.2‖ ^ (-s))) :=
        ENNReal.measurable_ofReal.comp h2
      have h_then : Measurable (fun (_ : P) => (0 : ENNReal)) := by exact measurable_const
      exact Measurable.ite h1 h_then h3
    have h_joint_swap : Measurable (Function.uncurry (fun (y x : EuclideanPlane) => planeKernel s x y)) :=
      h_joint.comp measurable_swap
    have h_inner_meas : Measurable (fun x : EuclideanPlane => ∫⁻ y, planeKernel s x y ∂μ) :=
      Measurable.lintegral_prod_left h_joint_swap
    let F : EuclideanPlane → ENNReal := fun x => C_ennreal * ∫⁻ y, planeKernel s x y ∂μ
    let G : EuclideanPlane → ENNReal := fun _ => c
    have hF_meas : Measurable F := measurable_const.mul h_inner_meas
    have h9 : ∫⁻ x, (F x + G x) ∂μ = ∫⁻ x, F x ∂μ + ∫⁻ x, G x ∂μ :=
      lintegral_add_left hF_meas G
    rw [h9]
    have h10 : ∫⁻ x, F x ∂μ = C_ennreal * planeEnergy μ s := by
      have h11 : ∫⁻ x, F x ∂μ = C_ennreal * ∫⁻ x, (∫⁻ y, planeKernel s x y ∂μ) ∂μ :=
        MeasureTheory.lintegral_const_mul' C_ennreal _ hC_finite
      rw [h11] <;> rfl
    have h12 : ∫⁻ x, G x ∂μ = c := by
      simp [G, MeasureTheory.lintegral_const, MeasureTheory.measure_univ]
    rw [h10, h12] <;> ring
  calc (∑ σ ∈ S, projectedEnergyReg μ s δ σ)
    = ∑ σ ∈ S, ∫⁻ x, ∫⁻ y, projectedKernelReg s δ σ x y ∂μ ∂μ := h_swap1
    _ ≤ ∫⁻ x, ∫⁻ y, (∑ σ ∈ S, projectedKernelReg s δ σ x y) ∂μ ∂μ := h_swap2
    _ ≤ ∫⁻ x, ∫⁻ y, (C_ennreal * planeKernel s x y + c) ∂μ ∂μ := h5
    _ = C_ennreal * planeEnergy μ s + c := h6

end

end RobustKaufmanProjection.EnergyAveraging
