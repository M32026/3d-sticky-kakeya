module

/-
# Basic infrastructure for robust projection theorem

Projection and energy definitions shared across the OS A.7 modules. The
dyadic infrastructure and `(δ,s,C)`-set property are re-exported from the
discretised Furstenberg base module.

## Main definitions

- `realLineCopy`, `affineProjection`, `affineProjection1D`
- `Nreal`, `Nplane`
- `IsDirectionFrostman`, `IsRealDeltaSet`
- `WeakTwoEndsSumProduct`, `weakTwoEndsExponent`
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory

abbrev realLineCopy (A : Set ℝ) : Set (EuclideanSpace ℝ (Fin 1)) :=
  {x | x 0 ∈ A}

def affineProjection (y : ℝ)
    (P : Set (EuclideanSpace ℝ (Fin 2))) : Set ℝ :=
  (fun p => p 0 * y + p 1) '' P

def affineProjection1D (y : ℝ)
    (P : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 1)) :=
  realLineCopy (affineProjection y P)

def Nreal (δ : ℝ) (A : Set ℝ) : ENNReal :=
  ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A))

/-- Scaled set `t • A = {t * a : a ∈ A}`. -/
def scaleSet (t : ℝ) (A : Set ℝ) : Set ℝ :=
  (fun x => t * x) '' A

def Nplane (δ : ℝ)
    (P : Set (EuclideanSpace ℝ (Fin 2))) : ENNReal :=
  ENat.toENNReal (dyadicCoveringNumber δ P)

def IsDirectionFrostman
    (δ κ C : ℝ) (μ : Measure ℝ) : Prop :=
  μ Set.univ = 1 ∧
    μ.support ⊆ Set.Icc 0 1 ∧
    ∀ (a r : ℝ), δ ≤ r → r ≤ 1 →
      μ (Set.Icc (a - r) (a + r)) ≤
        ENNReal.ofReal (C * r ^ κ)

def IsRealDeltaSet (δ s C : ℝ) (A : Set ℝ) : Prop :=
  IsDeltaSCSet δ s C (realLineCopy A)

/-- The Bourgain Ring theorem (weak two-ends sum-product).

This is the **lower-free** statement from the paper: no lower-size premise
on `A` is required. Only an upper size bound and the Frostman measure are
needed. -/
def WeakTwoEndsSumProduct (s κ : ℝ) : Prop :=
  ∃ εnc εgain : ℝ,
    0 < εnc ∧
    εnc < min (min s κ) (1 - s) / 100 ∧
    0 < εgain ∧
    ∀ K : ℝ, 1 ≤ K →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
        ∀ {δ : ℝ}, δ ∈ dyadicScales → δ ≤ δ₀ →
          ∀ (A : Set ℝ) (μ : Measure ℝ),
            A ⊆ Set.Icc 1 2 →
            IsRealDeltaSet δ κ (K * δ ^ (-εnc)) A →
            Nreal δ A ≤
              ENNReal.ofReal (K * δ ^ (-(s + εnc))) →
            IsDirectionFrostman
              δ κ (K * δ ^ (-εnc)) μ →
            ∃ x ∈ μ.support,
              ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A ≤
                Nreal δ
                  (Set.image2 (fun a b => a + x * b) A A)

def weakTwoEndsExponent (s τ : ℝ) : ℝ :=
  min s τ / 20

/-! ## Dyadic scale selection -/

/-- For any `0 < r ≤ 1`, there exists a dyadic scale `r'` with `r ≤ r' < 2*r`
    and `r' ≤ 1`. -/
lemma dyadic_scale_selection {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ (r' : ℝ), r' ∈ dyadicScales ∧ r ≤ r' ∧ r' < 2 * r ∧ r' ≤ 1 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let x := Real.log (1 / r) / Real.log 2
  have hx_nonneg : 0 ≤ x := by
    have h1 : 1 ≤ 1 / r := by apply one_le_one_div <;> linarith
    have h2 : 0 ≤ Real.log (1 / r) := Real.log_nonneg h1
    positivity
  let m_int : ℤ := ⌊x⌋
  have hm_nonneg : 0 ≤ m_int := Int.floor_nonneg.mpr hx_nonneg
  let n : ℕ := m_int.toNat
  have hmn : (n : ℤ) = m_int := Int.toNat_of_nonneg hm_nonneg
  have h1 : (n : ℝ) ≤ x := by
    have h2 : (m_int : ℝ) ≤ x := Int.floor_le x
    have h3 : (n : ℝ) = (m_int : ℝ) := by exact_mod_cast hmn
    rw [h3] <;> exact h2
  have h2 : x < (n : ℝ) + 1 := by
    have h3 : x < (m_int : ℝ) + 1 := Int.lt_floor_add_one x
    have h4 : (m_int : ℝ) = (n : ℝ) := by exact_mod_cast hmn.symm
    rw [h4] at h3; exact h3
  have h_x_def : x * Real.log 2 = Real.log (1 / r) := by
    simp only [x]; field_simp [hlog2_pos.ne'] <;> ring
  have h4 : (2 : ℝ)^n ≤ 1 / r := by
    have h5 : (n : ℝ) * Real.log 2 ≤ Real.log (1 / r) := by
      calc (n : ℝ) * Real.log 2 ≤ x * Real.log 2 := by gcongr
        _ = Real.log (1 / r) := h_x_def
    have h6 : Real.log ((2 : ℝ)^n) = (n : ℝ) * Real.log 2 := by simp [Real.log_pow]
    have h7 : 0 < (2 : ℝ)^n := by positivity
    have h8 : 0 < 1 / r := by positivity
    have h9 : Real.log ((2 : ℝ)^n) ≤ Real.log (1 / r) := by rw [h6] <;> exact h5
    exact (Real.log_le_log_iff h7 h8).mp h9
  have h5 : 1 / r < (2 : ℝ)^(n + 1) := by
    have h6 : Real.log (1 / r) < ((n : ℝ) + 1) * Real.log 2 := by
      calc Real.log (1 / r) = x * Real.log 2 := h_x_def.symm
        _ < ((n : ℝ) + 1) * Real.log 2 := by gcongr
    have h7 : Real.log ((2 : ℝ)^(n + 1)) = ((n : ℝ) + 1) * Real.log 2 := by simp [Real.log_pow] <;> ring
    have h8 : 0 < 1 / r := by positivity
    have h9 : 0 < (2 : ℝ)^(n + 1) := by positivity
    have h10 : Real.log (1 / r) < Real.log ((2 : ℝ)^(n + 1)) := by rw [h7] <;> exact h6
    exact (Real.log_lt_log_iff h8 h9).mp h10
  let r' := (2 : ℝ)^(-(n : ℤ))
  have hr'_eq : r' = 1 / (2 : ℝ)^n := by
    simp [r', zpow_neg, zpow_ofNat] <;> field_simp <;> ring
  have hr'_dyadic : r' ∈ dyadicScales := ⟨n, by simp [r']⟩
  have h10 : 0 < (2 : ℝ)^n := by positivity
  have hr'_ge : r ≤ r' := by
    rw [hr'_eq]
    have h11 : r * (2 : ℝ)^n ≤ 1 := by
      have h12 : (2 : ℝ)^n ≤ 1 / r := h4
      have h13 : r * (2 : ℝ)^n ≤ r * (1 / r) := by gcongr
      have h14 : r * (1 / r) = 1 := by field_simp [hr.ne'] <;> ring
      rw [h14] at h13 <;> exact h13
    calc r = (r * (2 : ℝ)^n) / (2 : ℝ)^n := by field_simp [h10.ne'] <;> ring
      _ ≤ 1 / (2 : ℝ)^n := by gcongr
  have hr'_lt : r' < 2 * r := by
    rw [hr'_eq]
    have h11 : 1 < (2 : ℝ)^(n + 1) * r := by
      have h12 : 1 / r < (2 : ℝ)^(n + 1) := h5
      have h13 : r * (1 / r) < r * (2 : ℝ)^(n + 1) := by gcongr
      have h14 : r * (1 / r) = 1 := by field_simp [hr.ne'] <;> ring
      have h15 : 1 < r * (2 : ℝ)^(n + 1) := by rw [h14] at h13 <;> exact h13
      have h16 : r * (2 : ℝ)^(n + 1) = (2 : ℝ)^(n + 1) * r := by ring
      rw [h16] at h15; exact h15
    have h15 : (2 : ℝ)^(n + 1) = 2 * (2 : ℝ)^n := by simp [pow_succ] <;> ring
    rw [h15] at h11
    have h16 : 1 / (2 : ℝ)^n < 2 * r := by
      have h17 : 0 < (2 : ℝ)^n := h10
      calc 1 / (2 : ℝ)^n < (2 * (2 : ℝ)^n * r) / (2 : ℝ)^n := by gcongr
        _ = 2 * r := by field_simp [h17.ne'] <;> ring
    exact h16
  have hr'_le_one : r' ≤ 1 := by
    rw [hr'_eq]
    have h11 : 1 ≤ (2 : ℝ)^n := by
      have h12 : 0 ≤ n := by linarith
      have h13 : (2 : ℝ)^n ≥ 1 := by
        have h14 : (2 : ℝ)^n ≥ (2 : ℝ)^(0 : ℕ) := by gcongr <;> norm_num
        simpa using h14
      exact h13
    have h13 : 0 < (2 : ℝ)^n := h10
    exact (div_le_one h13).mpr h11
  exact ⟨r', hr'_dyadic, hr'_ge, hr'_lt, hr'_le_one⟩

end
