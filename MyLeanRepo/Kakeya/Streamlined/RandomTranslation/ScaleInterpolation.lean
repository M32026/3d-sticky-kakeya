import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds

/-!
# Scale grid and interpolation infrastructure

A geometric grid of scales `ρ_k = δ^{k/N}` between `δ` and `1`, used for
the multiscale random translation argument. Any admissible scale is bracketed
between two consecutive grid points with controlled ratio.

## Main results

- `scaleGrid`: the sequence `ρ_k = δ^{k/N}`
- `scaleGrid_ratio`: `ρ_k = δ^{-1/N} * ρ_{k+1}`
- `scaleGrid_bracket`: any `ρ ∈ [δ,1]` lies between `ρ_{k+1}` and `ρ_k`
- `deltaTubeVolume_mono`: monotonicity of tube volume in the radius
- `deltaTubeVolume_ratio_bound`: volume comparison for nearby scales
-/

noncomputable section

open Kakeya.Streamlined MeasureTheory

namespace Kakeya.Streamlined.RandomTranslation

/-! ### Scale grid -/

/-- The k-th grid point: `ρ_k = δ^{k/N}`. -/
def scaleGrid (δ : ℝ) (N : ℕ) (k : ℕ) : ENNReal :=
  Kakeya.realRpowENN δ ((k : ℝ) / (N : ℝ))

/-- `ρ_0 = 1`. -/
lemma scaleGrid_zero (δ : ℝ) (N : ℕ) :
    scaleGrid δ N 0 = 1 := by
  simp [scaleGrid, Kakeya.realRpowENN]

/-- `ρ_N = δ`. -/
lemma scaleGrid_N (δ : ℝ) (N : ℕ) (hN_pos : 0 < N) :
    scaleGrid δ N N = Kakeya.realRpowENN δ 1 := by
  have h : (N : ℝ) / (N : ℝ) = 1 := by
    field_simp [hN_pos.ne']
  simpa [scaleGrid, h] using rfl

/-- Helper: `realRpowENN` is antitone in exponent for `0 < δ ≤ 1`. -/
private lemma realRpowENN_antitone' {δ a b : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (h : a ≤ b) :
    Kakeya.realRpowENN δ b ≤ Kakeya.realRpowENN δ a := by
  simp only [Kakeya.realRpowENN]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h

/-- The grid is antitone: `ρ_{k+1} ≤ ρ_k` for `0 ≤ δ ≤ 1`. -/
lemma scaleGrid_antitone (δ : ℝ) (N : ℕ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (k : ℕ) : scaleGrid δ N (k + 1) ≤ scaleGrid δ N k := by
  have h1 : ((k : ℝ) / (N : ℝ)) ≤ (((k + 1 : ℕ) : ℝ) / (N : ℝ)) := by
    by_cases hN : N = 0
    · simp [hN]
    · have hN_pos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hN)
      have h2 : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        simp [Nat.cast_add] <;> linarith
      gcongr
  exact realRpowENN_antitone' hδ_pos hδ_le_one h1

/-- Helper: `realRpowENN_add`. -/
private lemma realRpowENN_add' {δ a b : ℝ} (hδ_pos : 0 < δ) :
    Kakeya.realRpowENN δ (a + b) =
      Kakeya.realRpowENN δ a * Kakeya.realRpowENN δ b := by
  simp only [Kakeya.realRpowENN]
  have h1 : Real.rpow δ (a + b) = Real.rpow δ a * Real.rpow δ b :=
    Real.rpow_add (by linarith) a b
  rw [h1]
  have ha : 0 ≤ Real.rpow δ a := Real.rpow_nonneg (by linarith) a
  have hb : 0 ≤ Real.rpow δ b := Real.rpow_nonneg (by linarith) b
  have h_mul : ENNReal.ofReal (Real.rpow δ a * Real.rpow δ b) =
      ENNReal.ofReal (Real.rpow δ a) * ENNReal.ofReal (Real.rpow δ b) := by
    rw [← ENNReal.ofReal_mul ha]
  exact h_mul

/-- Ratio of consecutive grid points: `ρ_k = δ^{-1/N} * ρ_{k+1}`. -/
lemma scaleGrid_ratio (δ : ℝ) (N : ℕ) (hδ_pos : 0 < δ) (hN_pos : 0 < N)
    (k : ℕ) :
    scaleGrid δ N k =
      Kakeya.realRpowENN δ (-(1 / (N : ℝ))) * scaleGrid δ N (k + 1) := by
  dsimp only [scaleGrid]
  have h1 : ((k : ℝ) / (N : ℝ)) =
      (-(1 / (N : ℝ))) + ((((k + 1 : ℕ) : ℝ) / (N : ℝ))) := by
    field_simp [hN_pos.ne']
    <;> simp [Nat.cast_add] <;> ring
  rw [h1]
  exact realRpowENN_add' (a := (-(1 / (N : ℝ)))) (b := (((k + 1 : ℕ) : ℝ) / (N : ℝ))) hδ_pos

/-! ### Bracketing lemma -/

/-- For any antitone real sequence `f` with `f 0 ≥ ρ ≥ f N`, there exists
`k < N` such that `f (k+1) ≤ ρ ≤ f k`. -/
private lemma antitone_bracket (f : ℕ → ℝ) (N : ℕ) (hN_pos : 0 < N)
    (h_antitone : ∀ k, f (k + 1) ≤ f k)
    (ρ : ℝ) (h_start : ρ ≤ f 0) (h_end : f N ≤ ρ) :
    ∃ k : ℕ, k < N ∧ f (k + 1) ≤ ρ ∧ ρ ≤ f k := by
  classical
  let S : Finset ℕ := (Finset.range (N + 1)).filter (fun k => ρ ≤ f k)
  have h0_in : 0 ∈ S := by
    have h1 : 0 ∈ Finset.range (N + 1) := by simp
    exact Finset.mem_filter.mpr ⟨h1, h_start⟩
  let k := Finset.max' S ⟨0, h0_in⟩
  have hk_in : k ∈ S := Finset.max'_mem S ⟨0, h0_in⟩
  rcases Finset.mem_filter.mp hk_in with ⟨hk_range, hρ_le_fk⟩
  have hk_le_N : k ≤ N := by
    have h : k < N + 1 := Finset.mem_range.mp hk_range
    omega
  by_cases hk_lt_N : k < N
  · -- Case k < N: prove f(k+1) ≤ ρ
    have h_fk1_lt_ρ : f (k + 1) < ρ := by
      by_contra h
      have h' : f (k + 1) ≥ ρ := le_of_not_gt h
      have h_k1_range : k + 1 < N + 1 := by omega
      have h_k1_in : k + 1 ∈ S := by
        have hS : S = (Finset.range (N + 1)).filter (fun k => ρ ≤ f k) := by rfl
        rw [hS, Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr h_k1_range, h'⟩
      have h_max : k + 1 ≤ k := Finset.le_max' S (k + 1) h_k1_in
      omega
    exact ⟨k, hk_lt_N, h_fk1_lt_ρ.le, hρ_le_fk⟩
  · -- Case k = N: use N - 1 instead
    have hkN : k = N := by omega
    have hρ_eq : ρ ≤ f N := by
      rw [hkN] at hρ_le_fk; exact hρ_le_fk
    have h_fN1_le : f N ≤ f (N - 1) := by
      have h3 := h_antitone (N - 1)
      have h4 : (N - 1) + 1 = N := by omega
      rw [h4] at h3; exact h3
    have h5 : ρ ≤ f (N - 1) := le_trans hρ_eq h_fN1_le
    have h6 : f N ≤ ρ := h_end
    have h7 : f ((N - 1) + 1) ≤ ρ := by
      have h8 : (N - 1) + 1 = N := by omega
      rw [h8]; exact h6
    exact ⟨N - 1, by omega, h7, h5⟩

/-- For any `ρ ∈ [δ, 1]`, there exists `k < N` such that
`ρ_{k+1} ≤ ρ ≤ ρ_k`. -/
lemma scaleGrid_bracket (δ : ℝ) (N : ℕ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hN_pos : 0 < N) (ρ : ℝ) (hρ1 : δ ≤ ρ) (hρ2 : ρ ≤ 1) :
    ∃ (k : ℕ), k < N ∧
      Kakeya.realRpowENN δ (((k + 1 : ℕ) : ℝ) / (N : ℝ)) ≤ ENNReal.ofReal ρ ∧
      ENNReal.ofReal ρ ≤ Kakeya.realRpowENN δ ((k : ℝ) / (N : ℝ)) := by
  let f : ℕ → ℝ := fun k => Real.rpow δ ((k : ℝ) / (N : ℝ))
  have h_f_antitone : ∀ k, f (k + 1) ≤ f k := by
    intro k
    have h : ((k : ℝ) / (N : ℝ)) ≤ (((k + 1 : ℕ) : ℝ) / (N : ℝ)) := by
      by_cases hN : N = 0
      · simp [hN]
      · have hN_pos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hN)
        have h2 : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
          simp [Nat.cast_add] <;> linarith
        gcongr
    exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h
  have h_f0 : f 0 = 1 := by simp [f] <;> norm_num
  have h_fN : f N = δ := by
    simp [f]
    have h : (N : ℝ) / (N : ℝ) = 1 := by field_simp [hN_pos.ne']
    rw [h] <;> simp
  have h_main := antitone_bracket f N hN_pos h_f_antitone ρ
    (by rw [h_f0] <;> exact hρ2) (by rw [h_fN] <;> exact hρ1)
  rcases h_main with ⟨k, hk_lt_N, h1, h2⟩
  refine ⟨k, hk_lt_N, ?_, ?_⟩
  · have h3 : Kakeya.realRpowENN δ (((k + 1 : ℕ) : ℝ) / (N : ℝ)) =
        ENNReal.ofReal (f (k + 1)) := by
      simp [f, Kakeya.realRpowENN] <;> rfl
    rw [h3]
    exact ENNReal.ofReal_le_ofReal h1
  · have h4 : Kakeya.realRpowENN δ ((k : ℝ) / (N : ℝ)) = ENNReal.ofReal (f k) := by
      simp [f, Kakeya.realRpowENN] <;> rfl
    rw [h4]
    exact ENNReal.ofReal_le_ofReal h2

/-! ### Tube volume monotonicity and comparison -/

/-- Tube volume is monotone in the radius. -/
lemma deltaTubeVolume_mono {δ ρ : ℝ} (h : δ ≤ ρ) :
    Kakeya.deltaTubeVolume δ ≤ Kakeya.deltaTubeVolume ρ := by
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) 1
  let S : Set Point3 := unitSegment 0 e0
  have h1 : Metric.cthickening δ S ⊆ Metric.cthickening ρ S :=
    Metric.cthickening_mono h S
  exact measure_mono h1

/-- Upper bound on `deltaTubeVolume r` for `0 < r ≤ 1`. -/
lemma deltaTubeVolume_upper_bound {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Kakeya.deltaTubeVolume r ≤ ENNReal.ofReal ((Real.pi + 8 / 3 * Real.pi) * r ^ 2) := by
  have h_capsule : Kakeya.deltaTubeVolume r ≤
      ENNReal.ofReal (Real.pi * r ^ 2 + (8 / 3 : ℝ) * Real.pi * r ^ 3) :=
    GeometricLemmas.capsule_upper_bound_instantiation r hr
  have h2 : Real.pi * r ^ 2 + (8 / 3 : ℝ) * Real.pi * r ^ 3 ≤
      (Real.pi + 8 / 3 * Real.pi) * r ^ 2 := by
    have h3 : r ^ 3 ≤ r ^ 2 := by nlinarith
    have h4 : (8 / 3 : ℝ) * Real.pi * r ^ 3 ≤ (8 / 3 : ℝ) * Real.pi * r ^ 2 := by
      gcongr
    linarith
  calc
    Kakeya.deltaTubeVolume r
      ≤ ENNReal.ofReal (Real.pi * r ^ 2 + (8 / 3 : ℝ) * Real.pi * r ^ 3) := h_capsule
    _ ≤ ENNReal.ofReal ((Real.pi + 8 / 3 * Real.pi) * r ^ 2) := by gcongr

/-- Lower bound on `deltaTubeVolume r` for `r > 0`. -/
lemma deltaTubeVolume_lower_bound {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (2 * r ^ 2) ≤ Kakeya.deltaTubeVolume r :=
  tube_volume_ge_two_delta_sq r hr

/-- Universal quadratic comparison of tube volumes at two positive radii.

For `0 < delta`, `0 < rho ≤ 1`, the volume at radius `rho` is bounded by a
universal constant times `(rho / delta)^2` and the volume at radius `delta`.
No upper comparison between the two radii is required. -/
lemma deltaTubeVolume_ratio_sq_bound
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1) :
    Kakeya.deltaTubeVolume rho ≤
      ENNReal.ofReal
          ((Real.pi + 8 / 3 * Real.pi) / 2) *
        (ENNReal.ofReal rho / ENNReal.ofReal delta) ^ 2 *
        Kakeya.deltaTubeVolume delta := by
  have hupper :
      Kakeya.deltaTubeVolume rho ≤
        ENNReal.ofReal
          ((Real.pi + 8 / 3 * Real.pi) * rho ^ 2) :=
    deltaTubeVolume_upper_bound hrho hrho_one
  have hlower :
      ENNReal.ofReal (2 * delta ^ 2) ≤
        Kakeya.deltaTubeVolume delta :=
    deltaTubeVolume_lower_bound hdelta
  let coefficient : ℝ :=
    (Real.pi + 8 / 3 * Real.pi) / 2
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  have hratio :
      0 ≤ (rho / delta) ^ 2 := sq_nonneg _
  have hreal :
      (Real.pi + 8 / 3 * Real.pi) * rho ^ 2 =
        coefficient * (rho / delta) ^ 2 *
          (2 * delta ^ 2) := by
    dsimp only [coefficient]
    field_simp [hdelta.ne']
  have hofRealRatio :
      ENNReal.ofReal ((rho / delta) ^ 2) =
        (ENNReal.ofReal rho / ENNReal.ofReal delta) ^ 2 := by
    rw [ENNReal.ofReal_pow (div_nonneg hrho.le hdelta.le) 2]
    rw [ENNReal.ofReal_div_of_pos hdelta]
  have hofRealProduct :
      ENNReal.ofReal
          (coefficient * (rho / delta) ^ 2 *
            (2 * delta ^ 2)) =
        ENNReal.ofReal coefficient *
          ENNReal.ofReal ((rho / delta) ^ 2) *
            ENNReal.ofReal (2 * delta ^ 2) := by
    calc
      ENNReal.ofReal
          (coefficient * (rho / delta) ^ 2 *
            (2 * delta ^ 2)) =
        ENNReal.ofReal
            (coefficient * (rho / delta) ^ 2) *
          ENNReal.ofReal (2 * delta ^ 2) := by
        rw [ENNReal.ofReal_mul
          (mul_nonneg hcoefficient hratio)]
      _ =
        ENNReal.ofReal coefficient *
          ENNReal.ofReal ((rho / delta) ^ 2) *
            ENNReal.ofReal (2 * delta ^ 2) := by
        rw [ENNReal.ofReal_mul hcoefficient]
  calc
    Kakeya.deltaTubeVolume rho ≤
        ENNReal.ofReal
          ((Real.pi + 8 / 3 * Real.pi) * rho ^ 2) :=
      hupper
    _ =
        ENNReal.ofReal coefficient *
          ENNReal.ofReal ((rho / delta) ^ 2) *
            ENNReal.ofReal (2 * delta ^ 2) := by
      rw [hreal, hofRealProduct]
    _ =
        ENNReal.ofReal coefficient *
          (ENNReal.ofReal rho / ENNReal.ofReal delta) ^ 2 *
            ENNReal.ofReal (2 * delta ^ 2) := by
      rw [hofRealRatio]
    _ ≤
        ENNReal.ofReal coefficient *
          (ENNReal.ofReal rho / ENNReal.ofReal delta) ^ 2 *
            Kakeya.deltaTubeVolume delta := by
      gcongr

/-- Volume ratio bound: if `0 < ρ ≤ ρ' ≤ A * ρ` and `ρ' ≤ 1`, then
`deltaTubeVolume ρ' ≤ C(A) * deltaTubeVolume ρ` where
`C(A) = ((π + 8π/3 * A) / 2) * A^2`.

Note: `A ≥ 1` follows from `ρ ≤ ρ' ≤ A * ρ` and `ρ > 0`.
-/
lemma deltaTubeVolume_ratio_bound {ρ ρ' A : ℝ}
    (hρ_pos : 0 < ρ) (hρ'_pos : 0 < ρ') (hρ_le_ρ' : ρ ≤ ρ')
    (hρ'_le_Aρ : ρ' ≤ A * ρ) (hA_pos : 0 < A) (hρ'_le_one : ρ' ≤ 1) :
    Kakeya.deltaTubeVolume ρ' ≤
      ENNReal.ofReal (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2) *
      Kakeya.deltaTubeVolume ρ := by
  have hA_ge_one : 1 ≤ A := by
    have h : ρ ≤ A * ρ := le_trans hρ_le_ρ' hρ'_le_Aρ
    nlinarith
  have h_upper : Kakeya.deltaTubeVolume ρ' ≤
      ENNReal.ofReal ((Real.pi + 8 / 3 * Real.pi) * ρ' ^ 2) :=
    deltaTubeVolume_upper_bound hρ'_pos hρ'_le_one
  have h_lower : ENNReal.ofReal (2 * ρ ^ 2) ≤ Kakeya.deltaTubeVolume ρ :=
    deltaTubeVolume_lower_bound hρ_pos
  have h_ρ'2 : ρ' ^ 2 ≤ A ^ 2 * ρ ^ 2 := by
    calc
      ρ' ^ 2 ≤ (A * ρ) ^ 2 := by gcongr
      _ = A ^ 2 * ρ ^ 2 := by ring
  have h_coeff : (Real.pi + 8 / 3 * Real.pi) ≤ (Real.pi + 8 / 3 * Real.pi * A) := by
    have h5 : (8 / 3 : ℝ) * Real.pi ≤ (8 / 3 : ℝ) * Real.pi * A := by
      calc
        (8 / 3 : ℝ) * Real.pi
          = (8 / 3 : ℝ) * Real.pi * 1 := by ring
        _ ≤ (8 / 3 : ℝ) * Real.pi * A := by gcongr
    linarith
  have h_main_real : (Real.pi + 8 / 3 * Real.pi) * ρ' ^ 2 ≤
      (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2) * (2 * ρ ^ 2) := by
    calc
      (Real.pi + 8 / 3 * Real.pi) * ρ' ^ 2
        ≤ (Real.pi + 8 / 3 * Real.pi) * (A ^ 2 * ρ ^ 2) := by gcongr
      _ = ((Real.pi + 8 / 3 * Real.pi) * A ^ 2) * ρ ^ 2 := by ring
      _ ≤ ((Real.pi + 8 / 3 * Real.pi * A) * A ^ 2) * ρ ^ 2 := by gcongr
      _ = (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2) * (2 * ρ ^ 2) := by ring
  have h4 : 0 ≤ (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2) := by positivity
  have h_main_enn : ENNReal.ofReal ((Real.pi + 8 / 3 * Real.pi) * ρ' ^ 2) ≤
      ENNReal.ofReal (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2) *
      ENNReal.ofReal (2 * ρ ^ 2) := by
    rw [← ENNReal.ofReal_mul h4]
    <;> gcongr
  calc
    Kakeya.deltaTubeVolume ρ'
      ≤ ENNReal.ofReal ((Real.pi + 8 / 3 * Real.pi) * ρ' ^ 2) := h_upper
    _ ≤ ENNReal.ofReal (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2) *
          ENNReal.ofReal (2 * ρ ^ 2) := h_main_enn
    _ ≤ ENNReal.ofReal (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2) *
          Kakeya.deltaTubeVolume ρ := by gcongr

end Kakeya.Streamlined.RandomTranslation

end
