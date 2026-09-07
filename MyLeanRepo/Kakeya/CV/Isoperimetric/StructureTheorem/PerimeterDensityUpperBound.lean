import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.CutoffFunctions
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DistributionalDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundary
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.VectorMeasureInner
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceCoareaEq
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceCoareaAEMeasurable
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.Eilenberg
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.CutoffInequality
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.SphereHausdorff
import Mathlib.Tactic

/-!
# Perimeter Density Upper Bound

For a set `U` of finite perimeter, for `perimeterMeasure U`-a.e. `x`,
the local perimeter in small balls satisfies
`perimeterIn U (ball x r) ≤ C * r^(n-1)` for all sufficiently small `r > 0`.

This is Step 1 of Maggi Theorem 15.5, used to establish the translation
bound (`h_trans_bound`) in `ReducedBoundaryData`.

## Proof route

1. **Polar decomposition**: `Dχ_U = μ.withDensityᵥ ν` with `‖ν‖ = 1` μ-a.e.
   (`TrueReducedBoundary.lean`).

2. **Key inequality** (for a.e. `r`):
   `|inner(Dχ_U(ball x r), ν(x))| ≤ μHE[n-1](U ∩ sphere x r)`

   Proof via radial cutoff `η_ε`:
   - `∫ η_ε dρ = ∫_U div(η_ε • ν(x))` (distributional derivative)
   - `|∫_U div(η_ε • ν(x))| ≤ ∫_U ‖fderiv η_ε‖` (since ‖ν(x)‖ = 1)
   - Coarea formula converts the RHS to a weighted average of `H(t) = μHE[n-1](U ∩ sphere x t)`
   - As `ε → 0`, LHS → `inner(Dχ_U(ball x r), ν(x))` and RHS → `H(r)` (Lebesgue differentiation)

3. **Sphere bound**: `H(r) ≤ n * ω_n * r^(n-1)` for a.e. `r`, via coarea + volume of balls.

4. **Lebesgue differentiation**: For μ-a.e. x,
   `inner(Dχ_U(ball x r), ν(x)) / μ(ball x r) → ‖ν(x)‖² = 1`
   Hence for small r: `μ(ball x r) ≤ 2 * |inner(Dχ_U(ball x r), ν(x))|`.

5. **Combine**: `μ(ball x r) ≤ 2nω_n r^(n-1)` for a.e. small r, then for all small r by monotonicity.

6. **`perimeterIn ≤ perimeterMeasure`**: From the variation bound.

## Whiteprint
Node `perimeter_density_upper_bound`.
-/


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

/-- `perimeterIn S Ω ≤ perimeterMeasure S Ω` for any set `Ω`.

This follows because any test field `Φ` supported in `Ω` with `‖Φ‖ ≤ 1` gives
`|∫_S div Φ| = |∫ᵛ Φ · dDχ_S| ≤ Dχ_S.variation(support Φ) ≤ perimeterMeasure S Ω`. -/
lemma perimeterIn_le_perimeterMeasure {S : Set (E n)} {Ω : Set (E n)}
    (hfin : perimeter S < ⊤) :
    perimeterIn S Ω ≤ perimeterMeasure S Ω := by
  let D := distributionalDerivative S
  let μ := perimeterMeasure S
  have hD_eq : D.variation = μ := by rfl
  have h_main : ∀ (Φ : {Φ : TestVectorField // Function.support Φ.toFun ⊆ Ω}),
      ENNReal.ofReal |∫ x in S, divergence Φ.val.toFun x| ≤ μ Ω := by
    intro Φ
    let φ := Φ.val.toFun
    have hφ_smooth := Φ.val.smooth
    have hφ_support : Function.support φ ⊆ Ω := Φ.property
    have hφ_bound : ∀ x, ‖φ x‖ ≤ 1 := Φ.val.bound
    have hφ_cont : Continuous φ := Φ.val.smooth.continuous
    have hφ_csupport : HasCompactSupport φ := Φ.val.compact
    have h_int : ∫ᵛ x, φ x ∂[innerBilinear; D] = ∫ x in S, divergence φ x :=
      distributionalDerivative_integral_formula S hfin φ hφ_smooth hφ_csupport
    have hμ_fin : μ Set.univ < ⊤ := by
      rw [← perimeter_eq_variation S hfin] <;> exact hfin
    letI : IsFiniteMeasure μ := ⟨hμ_fin⟩
    have h_int' : Integrable φ μ := hφ_cont.integrable_of_hasCompactSupport hφ_csupport
    have hφ_int : D.Integrable φ := by
      have h_eq : D.variation = μ := by rfl
      simpa [VectorMeasure.Integrable, h_eq] using h_int'
    have h1 : |∫ᵛ x, φ x ∂[innerBilinear; D]| ≤ ∫ x, ‖φ x‖ ∂μ :=
      vectorMeasure_integral_abs_bound D φ hφ_int
    let s := Function.support φ
    have hs_open : IsOpen s := Continuous.isOpen_support hφ_cont
    have hs_meas : MeasurableSet s := hs_open.measurableSet
    have h_sub_s : s ⊆ Ω := hφ_support
    have h3 : ∀ x, ‖φ x‖ ≤ Set.indicator s (fun _ => (1 : ℝ)) x := by
      intro x
      classical
      by_cases hx : x ∈ s
      · have h_indic : Set.indicator s (fun _ => (1 : ℝ)) x = 1 := by
          simp [hx]
        rw [h_indic]
        exact hφ_bound x
      · have h_indic : Set.indicator s (fun _ => (1 : ℝ)) x = 0 := by
          rw [Set.indicator_apply, if_neg hx]
        have h4 : φ x = 0 := by
          have h5 : x ∉ Function.support φ := hx
          simpa [Function.mem_support] using h5
        rw [h_indic, h4] <;> norm_num
    have h4 : Integrable (fun x => ‖φ x‖) μ := h_int'.norm
    haveI : IsFiniteMeasure (μ.restrict s) := by
      have h : (μ.restrict s) Set.univ = μ s := by simp
      have h' : (μ.restrict s) Set.univ < ⊤ := by
        rw [h]
        exact measure_lt_top μ s
      exact ⟨h'⟩
    have h5 : Integrable (Set.indicator s (fun _ => (1 : ℝ))) μ := by
      rw [integrable_indicator_iff hs_meas]
      exact integrableOn_const
    have h6 : ∫ x, ‖φ x‖ ∂μ ≤ ∫ x, Set.indicator s (fun _ => (1 : ℝ)) x ∂μ :=
      integral_mono h4 h5 h3
    have h7 : ∫ x, Set.indicator s (fun _ => (1 : ℝ)) x ∂μ = (μ s).toReal := by
      rw [integral_indicator hs_meas]
      <;> simp [Measure.restrict_apply]
      <;> rfl
    have h_μs_le : (μ s).toReal ≤ (μ Ω).toReal := by
      have h_ne_s : μ s ≠ ⊤ := (measure_lt_top μ s).ne
      have h_ne_O : μ Ω ≠ ⊤ := (measure_lt_top μ Ω).ne
      have h : μ s ≤ μ Ω := measure_mono h_sub_s
      exact (ENNReal.toReal_le_toReal h_ne_s h_ne_O).mpr h
    have h2 : ∫ x, ‖φ x‖ ∂μ ≤ (μ Ω).toReal := by
      rw [h7] at h6
      exact h6.trans h_μs_le
    have h8 : |∫ x in S, divergence φ x| ≤ (μ Ω).toReal := by
      rw [← h_int]
      exact h1.trans h2
    have hμΩ_lt_top : μ Ω < ⊤ := (measure_mono (Set.subset_univ Ω)).trans_lt hμ_fin
    have h9 : ENNReal.ofReal (μ Ω).toReal = μ Ω := ENNReal.ofReal_toReal hμΩ_lt_top.ne
    have h10 : ENNReal.ofReal |∫ x in S, divergence φ x| ≤ ENNReal.ofReal (μ Ω).toReal :=
      ENNReal.ofReal_le_ofReal h8
    rw [h9] at h10
    exact h10
  exact iSup_le h_main



/-- **Sphere measure bound**.

For any `x : E n`, `r > 0`, and measurable `U`,
`μHE[n-1](U ∩ sphere x r) ≤ ENNReal.ofReal (C * r^(n-1))`
where `C = (μHE[n-1](sphere(0,1))).toReal`.

This holds for ALL `r > 0`, not just a.e. -/
lemma sphere_measure_bound (hn : 2 ≤ n) (x : E n) (U : Set (E n)) {r : ℝ} (hr : 0 < r) :
    μHE[n - 1] (U ∩ sphere x r) ≤
      ENNReal.ofReal ((μHE[n - 1] (sphere (0 : E n) 1)).toReal * r ^ (n - 1)) := by
  have h1 : U ∩ sphere x r ⊆ sphere x r := by simp
  have h2 : μHE[n - 1] (U ∩ sphere x r) ≤ μHE[n - 1] (sphere x r) := measure_mono h1
  have h3 : μHE[n - 1] (sphere x r) =
      ENNReal.ofReal (r ^ (n - 1)) * μHE[n - 1] (sphere (0 : E n) 1) :=
    sphere_hausdorff_scale x hr
  rw [h3] at h2
  have h4 : μHE[n - 1] (sphere (0 : E n) 1) < ⊤ := unit_sphere_hausdorff_finite hn
  have h5 : ENNReal.ofReal (r ^ (n - 1)) * μHE[n - 1] (sphere (0 : E n) 1) =
      ENNReal.ofReal ((μHE[n - 1] (sphere (0 : E n) 1)).toReal * r ^ (n - 1)) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    <;> rw [ENNReal.ofReal_toReal h4.ne] <;> ring
  rw [h5] at h2
  exact h2

/-- **Monotonicity extension from a.e. to all radii**.

If `f : ℝ → ENNReal` is monotone and `f(r) ≤ g(r)` for a.e. `r ∈ (0, r0)`,
where `g(r) = C * r^p` with `C > 0` and `p : ℕ`, then
`f(r) ≤ C * 2^p * r^p` for all `r ∈ (0, r0/2)`.

Proof: for any `r < r0/2`, pick `r' ∈ (r, 2r)` where the bound holds
(possible since the bad set has measure zero). Then
`f(r) ≤ f(r') ≤ C * (r')^p ≤ C * (2r)^p = C * 2^p * r^p`. -/
lemma monotone_ae_bound_extension {f : ℝ → ENNReal} {C : ℝ} {p : ℕ} {r0 : ℝ}
    (hC_pos : 0 < C) (hr0_pos : 0 < r0)
    (hf_mono : Monotone f)
    (h_ae : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioo 0 r0),
      f r ≤ ENNReal.ofReal (C * r ^ p)) :
    ∀ r, 0 < r → r < r0 / 2 →
      f r ≤ ENNReal.ofReal (C * (2 ^ p : ℝ) * r ^ p) := by
  intro r hr_pos hr_half
  have h_interval : 0 < r ∧ r < r0 / 2 := ⟨hr_pos, hr_half⟩
  have h2r_lt_r0 : 2 * r < r0 := by linarith
  have h_ae_on_interval : ∀ᵐ (x : ℝ) ∂volume.restrict (Set.Ioo r (2 * r)),
      f x ≤ ENNReal.ofReal (C * x ^ p) := by
    have h_sub : Set.Ioo r (2 * r) ⊆ Set.Ioo 0 r0 := by
      intro x hx
      exact ⟨by linarith [hr_pos, hx.1], by linarith [h2r_lt_r0, hx.2]⟩
    have h_ae' : ∀ᵐ (x : ℝ) ∂volume, x ∈ Set.Ioo 0 r0 → f x ≤ ENNReal.ofReal (C * x ^ p) := by
      rw [ae_restrict_iff' (isOpen_Ioo.measurableSet : MeasurableSet (Set.Ioo 0 r0))] at h_ae
      exact h_ae
    rw [ae_restrict_iff' (isOpen_Ioo.measurableSet : MeasurableSet (Set.Ioo r (2 * r)))]
    filter_upwards [h_ae'] with x hx
    intro hx_in
    exact hx (h_sub hx_in)
  have h_interval_pos : 0 < volume (Set.Ioo r (2 * r)) := by
    rw [Real.volume_Ioo] <;> simp [hr_pos] <;> linarith
  have h_exists : ∃ (r' : ℝ), r' ∈ Set.Ioo r (2 * r) ∧
      f r' ≤ ENNReal.ofReal (C * r' ^ p) := by
    exact MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae h_interval_pos.ne' h_ae_on_interval
  rcases h_exists with ⟨r', hr'_in, hr'_bound⟩
  have hr_lt_r' : r < r' := hr'_in.1
  have hr'_lt_2r : r' < 2 * r := hr'_in.2
  have h6 : f r ≤ f r' := hf_mono (by linarith)
  have h7 : f r' ≤ ENNReal.ofReal (C * r' ^ p) := hr'_bound
  have h8 : C * r' ^ p ≤ C * (2 * r) ^ p := by
    gcongr
    <;> linarith
  have h9 : ENNReal.ofReal (C * r' ^ p) ≤ ENNReal.ofReal (C * (2 * r) ^ p) := by
    gcongr
  have h10 : C * (2 * r) ^ p = C * (2 ^ p : ℝ) * r ^ p := by
    ring
  rw [h10] at h9
  exact le_trans h6 (le_trans h7 h9)

/-- Sphere Hausdorff measure scales and is finite.

There exists `C < ∞` such that `μHE[n-1](sphere x r) = C * r^(n-1)` for all `r > 0`.
Finiteness follows from the coarea formula: if `C = ∞`, then the volume of any
annulus would be infinite, contradicting boundedness. -/
lemma sphere_hausdorff_finite_and_scale {x : E n} (hn : 2 ≤ n) :
    ∃ (C : ENNReal), C < ⊤ ∧ ∀ (r : ℝ), 0 < r →
      μHE[n - 1] (sphere x r) = C * ENNReal.ofReal (r ^ (n - 1)) := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by linarith)
  let C0 : ENNReal := μHE[n - 1] (sphere x 1)
  have h_scale_all : ∀ (r : ℝ), 0 < r →
      μHE[n - 1] (sphere x r) = (ENNReal.ofReal (r ^ (n - 1))) * C0 := by
    intro r hr
    have h1 : sphere x r = AffineMap.homothety x r '' sphere x 1 := by
      ext y
      simp only [Set.mem_image, Metric.mem_sphere]
      constructor
      · intro hy
        refine ⟨x + (1 / r) • (y - x), ?_, ?_⟩
        · have h10 : ‖y - x‖ = r := by simpa [dist_eq_norm] using hy
          have h : dist (x + (1 / r) • (y - x)) x = 1 := by
            have h9 : (x + (1 / r) • (y - x)) - x = (1 / r) • (y - x) := by
              simp
            rw [dist_eq_norm, h9, norm_smul, Real.norm_eq_abs,
              abs_of_pos (show 0 < 1 / r by positivity), h10]
            have h_goal : (1 / r : ℝ) * r = 1 := by field_simp [hr.ne']
            rw [h_goal]
          exact h
        · have h10 : AffineMap.homothety x r (x + (1 / r) • (y - x)) = y := by
            have h11 : AffineMap.homothety x r (x + (1 / r) • (y - x)) =
                r • ((x + (1 / r) • (y - x)) -ᵥ x) +ᵥ x := by
              rw [AffineMap.homothety_apply]
            rw [h11]
            have h12 : (x + (1 / r) • (y - x)) -ᵥ x = (1 / r) • (y - x) := by simp
            rw [h12, smul_smul]
            have h13 : r * (1 / r) = 1 := by field_simp [hr.ne']
            rw [h13, one_smul]
            simp
          exact h10
      · rintro ⟨z, hz, rfl⟩
        have h10 : ‖z - x‖ = 1 := by simpa [dist_eq_norm] using hz
        have h : dist (AffineMap.homothety x r z) x = r := by
          have h9 : AffineMap.homothety x r z = r • (z -ᵥ x) +ᵥ x := by
            rw [AffineMap.homothety_apply]
          rw [h9]
          have h10' : ‖(r • (z -ᵥ x) +ᵥ x) - x‖ = ‖r • (z - x)‖ := by simp
          rw [dist_eq_norm, h10', norm_smul, Real.norm_eq_abs, abs_of_pos hr, h10] <;> ring
        exact h
    rw [h1]
    have h_hom := MeasureTheory.euclideanHausdorffMeasure_homothety_image (n - 1) x hr.ne' (sphere x 1)
    have h2 : (‖r‖₊ : ENNReal) ^ (n - 1) = ENNReal.ofReal (r ^ (n - 1)) := by
      have h3 : (‖r‖₊ : ENNReal) = ENNReal.ofReal r := by
        have h4 : (‖r‖₊ : ℝ) = r := by
          simp [abs_of_pos hr]
        have h5 : (‖r‖₊ : ENNReal) = ENNReal.ofReal (‖r‖₊ : ℝ) := by
          rw [ENNReal.ofReal_coe_nnreal]
        rw [h5, h4]
      rw [h3]
      rw [← ENNReal.ofReal_pow (by linarith)] <;> norm_cast
    have h_hom2 : μHE[n - 1] (AffineMap.homothety x r '' sphere x 1) = (‖r‖₊ : ENNReal) ^ (n - 1) * C0 := by
      rw [h_hom]
      have h_smul_eq : (‖r‖₊ ^ (n - 1)) • C0 = (‖r‖₊ : ENNReal) ^ (n - 1) * C0 := by
        rw [ENNReal.smul_def] <;> norm_cast <;> rfl
      rw [h_smul_eq]
    simpa [h2] using h_hom2
  have hC_lt_top : C0 < ⊤ := by
    by_contra hC_top
    have hC_eq : C0 = ⊤ := by simpa using hC_top
    let A : Set (E n) := ball x 2 \ {x}
    have hA_meas : MeasurableSet A :=
      isOpen_ball.measurableSet.diff (MeasurableSet.singleton x)
    have hball_bdd : Bornology.IsBounded (ball x 2) :=
      Metric.isBounded_ball
    have hA_bdd : Bornology.IsBounded A :=
      hball_bdd.subset (fun y hy => hy.1)
    have hA_sub : A ⊆ {y | 0 < infDist y {x}} := by
      intro y hy
      have hne : y ≠ x := hy.2
      have hpos : 0 < dist y x := dist_pos.mpr hne
      simpa [infDist_singleton] using hpos
    have h_d_meas2 : FunctionLevelMeasurable (fun y : E n => infDist y {x}) := by
      have h_eq : (fun y : E n => infDist y {x}) = fun y => dist y x := by
        funext y; simp [infDist_singleton] <;> rfl
      rw [h_eq]
      exact point_distance_level_measurable hn x
    let S : Set (E n) := {y ∈ A | (1 / 2 : ℝ) < infDist y {x} ∧ infDist y {x} ≤ 3 / 2}
    have h_coarea : volume S =
        ∫⁻ t in Set.Ioc (1 / 2 : ℝ) (3 / 2), μHE[n - 1] {y ∈ A | infDist y {x} = t} :=
      distance_coarea_eq hn isClosed_singleton (singleton_nonempty x) h_d_meas2 hA_meas hA_bdd hA_sub (by norm_num)
    have h3 : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) (3 / 2), μHE[n - 1] {y ∈ A | infDist y {x} = t} = ⊤ := by
      intro t ht
      have ht_pos : 0 < t := by linarith [ht.1]
      have ht_lt2 : t < 2 := by linarith [ht.2]
      have h4 : {y ∈ A | infDist y {x} = t} = sphere x t := by
        ext y
        simp only [A, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff, infDist_singleton, Metric.mem_sphere]
        constructor
        · rintro ⟨⟨hball, hne⟩, hdist⟩
          exact hdist
        · intro hsphere
          have hdist : dist y x = t := hsphere
          have hne : y ≠ x := by
            intro h; rw [h] at hdist; simp [ht_pos.ne'] at hdist <;> linarith
          have hball : y ∈ ball x 2 := by
            simpa [ball, dist_eq_norm] using show dist y x < 2 from by linarith
          exact ⟨⟨hball, hne⟩, hdist⟩
      rw [h4]
      rw [h_scale_all t ht_pos, hC_eq]
      have h_pos2 : ENNReal.ofReal (t ^ (n - 1)) ≠ 0 := by
        have h : 0 < t ^ (n - 1) := by positivity
        have h' : ENNReal.ofReal (t ^ (n - 1)) = 0 ↔ t ^ (n - 1) ≤ 0 := ENNReal.ofReal_eq_zero
        exact h'.not.mpr (by linarith)
      exact ENNReal.top_mul h_pos2
    have h_pos : 0 < volume (Set.Ioc (1 / 2 : ℝ) (3 / 2)) := by
      rw [Real.volume_Ioc] <;> norm_num
    have h_mem : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioc (1 / 2 : ℝ) (3 / 2)), t ∈ Set.Ioc (1 / 2 : ℝ) (3 / 2) :=
      ae_restrict_mem measurableSet_Ioc
    have h_eq_ae : (fun t : ℝ => μHE[n - 1] {y ∈ A | infDist y {x} = t}) =ᵐ[volume.restrict (Set.Ioc (1 / 2 : ℝ) (3 / 2))] fun _ : ℝ => (⊤ : ENNReal) := by
      filter_upwards [h_mem] with t ht
      exact h3 t ht
    have h4 : ∫⁻ t in Set.Ioc (1 / 2 : ℝ) (3 / 2), μHE[n - 1] {y ∈ A | infDist y {x} = t} = ⊤ := by
      rw [lintegral_congr_ae h_eq_ae]
      have h5 : ∫⁻ t in Set.Ioc (1 / 2 : ℝ) (3 / 2), (⊤ : ENNReal) = ⊤ := by
        rw [MeasureTheory.setLIntegral_const (Set.Ioc (1 / 2 : ℝ) (3 / 2)) (⊤ : ENNReal)]
        rw [ENNReal.top_mul h_pos.ne']
      exact h5
    have hS_bdd : Bornology.IsBounded S := hA_bdd.subset (fun y hy => hy.1)
    have h6 : volume S < ⊤ := hS_bdd.measure_lt_top
    rw [h_coarea] at h6
    rw [h4] at h6
    <;> simpa using h6
  have h_scale_all' : ∀ (r : ℝ), 0 < r → μHE[n - 1] (sphere x r) = C0 * ENNReal.ofReal (r ^ (n - 1)) := by
    intro r hr
    have h := h_scale_all r hr
    rw [h, mul_comm]
  exact ⟨C0, hC_lt_top, h_scale_all'⟩

/-- **Coordinate-wise Besicovitch differentiation of distributional derivative**.

For each coordinate `i`, the ratio `(Dχ_U(closedBall x r)) i / μ(closedBall x r)`
converges to `(measureTheoreticNormal U x) i` for `μ`-a.e. `x`, where `μ = perimeterMeasure U`. -/
lemma coordinate_differentiation {U : Set (E n)} (h_perim_finite : perimeter U < ⊤) (i : Fin n) :
    ∀ᵐ (x : E n) ∂(perimeterMeasure U),
      Tendsto (fun r : ℝ =>
        ((distributionalDerivative U (closedBall x r)) i) /
          (perimeterMeasure U (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((measureTheoreticNormal U x) i)) := by
  let μ := perimeterMeasure U
  let f := measureTheoreticNormal U
  have hD_eq : distributionalDerivative U = μ.withDensityᵥ f :=
    (measureTheoreticNormal_withDensity h_perim_finite).2
  have h1 : μ Set.univ < ⊤ := by
    rw [← perimeter_eq_variation U h_perim_finite] <;> exact h_perim_finite
  letI : IsFiniteMeasure μ := ⟨h1⟩
  have h_norm_one : ∀ᵐ x ∂μ, ‖f x‖ = 1 := norm_measureTheoreticNormal_eq_one h_perim_finite
  have h_f_bdd : ∀ᵐ y ∂μ, ‖f y‖ ≤ 1 := by
    filter_upwards [h_norm_one] with y hy
    rw [hy] <;> norm_num
  have h_f_meas : Measurable f := by
    have h1 : ∀ (x : E n), f x =
        ∑ i : Fin n, (Classical.choose (distributionalDerivative_signedMeasure U i h_perim_finite)).rnDeriv (perimeterMeasure U) x • EuclideanSpace.single i (1 : ℝ) := by
      intro x
      simp [f, measureTheoreticNormal, h_perim_finite]
      <;> rfl
    have h_eq : f = fun x => ∑ i : Fin n, (Classical.choose (distributionalDerivative_signedMeasure U i h_perim_finite)).rnDeriv (perimeterMeasure U) x • EuclideanSpace.single i (1 : ℝ) := by
      funext x; exact h1 x
    rw [h_eq]
    exact Finset.measurable_sum Finset.univ (fun i _ =>
      (SignedMeasure.measurable_rnDeriv _ _).smul_const (EuclideanSpace.single i (1 : ℝ)))
  have h_int : Integrable f μ := by
    have h_const : Integrable (fun (_ : E n) => (1 : ℝ)) μ := integrable_const (1 : ℝ)
    exact h_const.mono' h_f_meas.aestronglyMeasurable h_f_bdd
  let proj : (E n) →L[ℝ] ℝ :=
    { toFun := fun v => v i, map_add' := by intro a b; rfl, map_smul' := by intro c a; rfl }
  let ρ : SignedMeasure (E n) := (distributionalDerivative U).mapRange proj.toAddMonoidHom proj.continuous
  have hρ_apply : ∀ (A : Set (E n)), MeasurableSet A → ρ A = (distributionalDerivative U A) i := by
    intro A _
    have h : ρ A = proj.toAddMonoidHom ((distributionalDerivative U) A) := by
      dsimp only [ρ]
      exact VectorMeasure.mapRange_apply (distributionalDerivative U) proj.continuous
    rw [h]
    <;> simp [proj]
  have h_main_bound : ∀ (E : Set (E n)), MeasurableSet E → ‖ρ E‖ₑ ≤ μ E := by
    intro E hE
    have h2 : ρ E = (distributionalDerivative U E) i := hρ_apply E hE
    rw [h2]
    have h_proj : |(distributionalDerivative U E) i| ≤ ‖distributionalDerivative U E‖ := by
      have h_inner : inner ℝ (distributionalDerivative U E) (EuclideanSpace.single i (1 : ℝ)) = (distributionalDerivative U E) i := by
        rw [EuclideanSpace.inner_single_right i (1 : ℝ)]
        <;> simp
      have h_cauchy : |inner ℝ (distributionalDerivative U E) (EuclideanSpace.single i (1 : ℝ))| ≤
          ‖distributionalDerivative U E‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
        abs_real_inner_le_norm _ _
      have h_norm_single : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
        rw [EuclideanSpace.norm_single] <;> norm_num
      rw [h_inner, h_norm_single] at h_cauchy
      <;> simpa using h_cauchy
    have h_vec_bound : ‖distributionalDerivative U E‖ ≤ (μ E).toReal := by
      have hD_eq' : (distributionalDerivative U) E = ∫ y in E, f y ∂μ := by
        rw [hD_eq, withDensityᵥ_apply h_int hE]
      rw [hD_eq']
      have h1 : (∫ y in E, f y ∂μ) = ∫ y, f y ∂(μ.restrict E) := by rfl
      have h2 : (∫ y in E, ‖f y‖ ∂μ) = ∫ y, ‖f y‖ ∂(μ.restrict E) := by rfl
      have h_norm_int : ‖∫ y in E, f y ∂μ‖ ≤ ∫ y in E, ‖f y‖ ∂μ := by
        rw [h1, h2]
        exact norm_integral_le_integral_norm (f := f) (μ := μ.restrict E)
      have h_ae_le : ae (μ.restrict E) ≤ ae μ := by
        intro s hs
        have h6 : μ sᶜ = 0 := hs
        have h7 : (μ.restrict E) sᶜ ≤ μ sᶜ := by
          have h_le : μ.restrict E ≤ μ := Measure.restrict_le_self
          exact h_le sᶜ
        rw [h6] at h7
        have h8 : (μ.restrict E) sᶜ = 0 := by exact le_zero_iff.mp h7
        exact h8
      have h_bdd_E : ∀ᵐ y ∂(μ.restrict E), ‖f y‖ ≤ 1 :=
        h_f_bdd.filter_mono h_ae_le
      have h2' : ∫ y in E, ‖f y‖ ∂μ ≤ ∫ y in E, (1 : ℝ) ∂μ := by
        exact integral_mono_ae h_int.norm.restrict (integrable_const (1 : ℝ)).restrict h_bdd_E
      have h3 : ∫ y in E, (1 : ℝ) ∂μ = (μ E).toReal := by
        have h4 : ∫ y in E, (1 : ℝ) ∂μ = (μ.restrict E).real Set.univ := by
          rw [integral_const] <;> simp
        rw [h4]
        have h5 : (μ.restrict E).real Set.univ = (μ E).toReal := by
          rw [MeasureTheory.measureReal_def (μ.restrict E) Set.univ]
          <;> simp [Measure.restrict_apply hE]
          <;> rfl
        exact h5
      rw [h3] at h2'
      exact h_norm_int.trans h2'
    have h_enorm1 : ‖(distributionalDerivative U E) i‖ₑ = ENNReal.ofReal (|(distributionalDerivative U E) i|) :=
      Real.enorm_eq_ofReal_abs ((distributionalDerivative U E) i)
    rw [h_enorm1]
    have h4 : |(distributionalDerivative U E) i| ≤ (μ E).toReal := by
      calc |(distributionalDerivative U E) i|
        ≤ ‖distributionalDerivative U E‖ := h_proj
      _ ≤ (μ E).toReal := h_vec_bound
    calc ENNReal.ofReal (|(distributionalDerivative U E) i|)
      ≤ ENNReal.ofReal (μ E).toReal := ENNReal.ofReal_le_ofReal h4
    _ ≤ μ E := by exact ENNReal.ofReal_toReal_le
  have hρ_var_le : ρ.variation ≤ μ := by
    apply Measure.le_iff.mpr
    intro A hA
    exact VectorMeasure.variation_apply_le_of_forall_enorm_le hA
      (fun E hE _ => h_main_bound E hE)
  obtain ⟨P, hP₁, hP₂, hP₃, hρpos_eq, hρneg_eq⟩ := ρ.toJordanDecomposition_spec
  let ρpos := ρ.toJordanDecomposition.posPart
  let ρneg := ρ.toJordanDecomposition.negPart
  have hρpos_eq' : ρpos = ρ.toMeasureOfZeroLE P hP₁ hP₂ := hρpos_eq
  have hρneg_eq' : ρneg = ρ.toMeasureOfLEZero Pᶜ hP₁.compl hP₃ := hρneg_eq
  have hρpos_le : ρpos ≤ μ := by
    apply Measure.le_iff.mpr
    intro A hA
    have h_PA_meas : MeasurableSet (P ∩ A) := hP₁.inter hA
    have h_nonneg : 0 ≤ ρ (P ∩ A) :=
      ρ.nonneg_of_zero_le_restrict (ρ.zero_le_restrict_subset hP₁ Set.inter_subset_left hP₂)
    have h2 : ρpos A = ENNReal.ofReal (ρ (P ∩ A)) := by
      rw [hρpos_eq', SignedMeasure.toMeasureOfZeroLE_apply ρ hP₂ hP₁ hA]
      have h_coe : (↑(NNReal.mk (ρ (P ∩ A)) h_nonneg) : ENNReal) = ENNReal.ofReal (ρ (P ∩ A)) := by
        rw [ENNReal.ofReal_eq_coe_nnreal h_nonneg] <;> rfl
      exact h_coe
    rw [h2]
    have h4 : ENNReal.ofReal (ρ (P ∩ A)) = ‖ρ (P ∩ A)‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg h_nonneg]
    rw [h4]
    have h5 : ‖ρ (P ∩ A)‖ₑ ≤ μ (P ∩ A) := h_main_bound (P ∩ A) h_PA_meas
    exact h5.trans (measure_mono Set.inter_subset_right)
  have hρneg_le : ρneg ≤ μ := by
    apply Measure.le_iff.mpr
    intro A hA
    have h_PA_meas : MeasurableSet (Pᶜ ∩ A) := hP₁.compl.inter hA
    have h_nonpos : ρ (Pᶜ ∩ A) ≤ 0 :=
      ρ.nonpos_of_restrict_le_zero (ρ.restrict_le_zero_subset hP₁.compl Set.inter_subset_left hP₃)
    have h2 : ρneg A = ENNReal.ofReal (-ρ (Pᶜ ∩ A)) := by
      rw [hρneg_eq', SignedMeasure.toMeasureOfLEZero_apply ρ hP₃ hP₁.compl hA]
      have h_coe : (↑(NNReal.mk (-ρ (Pᶜ ∩ A)) (by linarith)) : ENNReal) =
          ENNReal.ofReal (-ρ (Pᶜ ∩ A)) := by
        rw [ENNReal.ofReal_eq_coe_nnreal (by linarith)] <;> rfl
      exact h_coe
    rw [h2]
    have h4 : ENNReal.ofReal (-ρ (Pᶜ ∩ A)) = ‖ρ (Pᶜ ∩ A)‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonpos h_nonpos] <;> ring
    rw [h4]
    have h5 : ‖ρ (Pᶜ ∩ A)‖ₑ ≤ μ (Pᶜ ∩ A) := h_main_bound (Pᶜ ∩ A) h_PA_meas
    exact h5.trans (measure_mono Set.inter_subset_right)
  haveI hpos_fin : IsLocallyFiniteMeasure ρpos :=
    MeasureTheory.Measure.isLocallyFiniteMeasure_of_le hρpos_le
  haveI hneg_fin : IsLocallyFiniteMeasure ρneg :=
    MeasureTheory.Measure.isLocallyFiniteMeasure_of_le hρneg_le
  have h_rnDeriv : ∀ᵐ (x : E n) ∂μ, ρ.rnDeriv μ x = f x i := by
    have h1 : ρ = μ.withDensityᵥ (fun y => f y i) := by
      ext A hA
      have h_left : ρ A = (distributionalDerivative U A) i := hρ_apply A hA
      rw [h_left]
      have hD_eq' : (distributionalDerivative U) A = ∫ y in A, f y ∂μ := by
        rw [hD_eq, withDensityᵥ_apply h_int hA]
      rw [hD_eq']
      have h_int_i : Integrable (fun y : E n => f y i) μ := proj.integrable_comp h_int
      have h_goal : (μ.withDensityᵥ (fun y => f y i)) A = ∫ y in A, f y i ∂μ := by
        rw [withDensityᵥ_apply h_int_i hA]
      rw [h_goal]
      have h_int_A : Integrable f (μ.restrict A) := h_int.restrict
      have h_comm : proj (∫ y in A, f y ∂μ) = ∫ y in A, proj (f y) ∂μ :=
        (proj.integral_comp_comm (φ_int := h_int_A)).symm
      exact h_comm
    have h2 : μ.withDensityᵥ (ρ.rnDeriv μ) = ρ := by
      have h_ac : VectorMeasure.AbsolutelyContinuous ρ μ.toENNRealVectorMeasure := by
        rw [h1]
        exact Measure.withDensityᵥ_absolutelyContinuous μ (fun y => f y i)
      exact (SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq ρ μ).mp h_ac
    have h2' : μ.withDensityᵥ (ρ.rnDeriv μ) = μ.withDensityᵥ (fun y => f y i) := by
      calc μ.withDensityᵥ (ρ.rnDeriv μ) = ρ := h2
        _ = μ.withDensityᵥ (fun y => f y i) := h1
    have h5 : Integrable (ρ.rnDeriv μ) μ := SignedMeasure.integrable_rnDeriv ρ μ
    have h6 : Integrable (fun y => f y i) μ := proj.integrable_comp h_int
    have h3 : ρ.rnDeriv μ =ᵐ[μ] (fun y => f y i) :=
      (Integrable.withDensityᵥ_eq_iff h5 h6).mp h2'
    exact h3
  have h_pos_tendsto : ∀ᵐ (x : E n) ∂μ,
      Tendsto (fun r : ℝ => ρpos (closedBall x r) / μ (closedBall x r))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (ρpos.rnDeriv μ x)) :=
    Besicovitch.ae_tendsto_rnDeriv ρpos μ
  have h_neg_tendsto : ∀ᵐ (x : E n) ∂μ,
      Tendsto (fun r : ℝ => ρneg (closedBall x r) / μ (closedBall x r))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (ρneg.rnDeriv μ x)) :=
    Besicovitch.ae_tendsto_rnDeriv ρneg μ
  have h_rn_pos_le_one : ∀ᵐ (x : E n) ∂μ, ρpos.rnDeriv μ x ≤ 1 :=
    Measure.rnDeriv_le_one_of_le hρpos_le
  have h_rn_neg_le_one : ∀ᵐ (x : E n) ∂μ, ρneg.rnDeriv μ x ≤ 1 :=
    Measure.rnDeriv_le_one_of_le hρneg_le
  filter_upwards [h_pos_tendsto, h_neg_tendsto, h_rnDeriv, h_rn_pos_le_one, h_rn_neg_le_one]
    with x hpos hneg hrn hpos_le hneg_le
  let B := fun r : ℝ => closedBall x r
  have hB_meas : ∀ r, MeasurableSet (B r) := fun _ => isClosed_closedBall.measurableSet
  have h_pos_lim_fin : ρpos.rnDeriv μ x ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hpos_le
  have h_neg_lim_fin : ρneg.rnDeriv μ x ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hneg_le
  have h_jordan : ∀ r, (ρpos (B r)).toReal - (ρneg (B r)).toReal = ρ (B r) := by
    intro r
    have h_eq_signed : ρ.toJordanDecomposition.toSignedMeasure = ρ :=
      SignedMeasure.toSignedMeasure_toJordanDecomposition ρ
    have h3 : ρ.toJordanDecomposition.toSignedMeasure (B r) = ρ (B r) := by
      rw [h_eq_signed]
    have h4 : ρ.toJordanDecomposition.toSignedMeasure (B r) =
        (ρpos (B r)).toReal - (ρneg (B r)).toReal := by
      simp [JordanDecomposition.toSignedMeasure, VectorMeasure.sub_apply,
        Measure.toSignedMeasure_apply_measurable (hB_meas r)]
      <;> rfl
    rw [h4] at h3
    exact h3
  have hpos' : Tendsto (fun r : ℝ => (ρpos (B r) / μ (B r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((ρpos.rnDeriv μ x).toReal)) :=
    (ENNReal.continuousAt_toReal h_pos_lim_fin).tendsto.comp hpos
  have hneg' : Tendsto (fun r : ℝ => (ρneg (B r) / μ (B r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((ρneg.rnDeriv μ x).toReal)) :=
    (ENNReal.continuousAt_toReal h_neg_lim_fin).tendsto.comp hneg
  have h_sub : Tendsto (fun r : ℝ =>
      (ρpos (B r) / μ (B r)).toReal - (ρneg (B r) / μ (B r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((ρpos.rnDeriv μ) x).toReal - ((ρneg.rnDeriv μ) x).toReal)) :=
    hpos'.sub hneg'
  have h_eq_fn : (fun r : ℝ =>
      (ρpos (B r) / μ (B r)).toReal - (ρneg (B r) / μ (B r)).toReal) =
      fun r : ℝ => ((distributionalDerivative U (B r)) i) / (μ (B r)).toReal := by
    funext r
    have h1 : (ρpos (B r) / μ (B r)).toReal = (ρpos (B r)).toReal / (μ (B r)).toReal :=
      ENNReal.toReal_div _ _
    have h2 : (ρneg (B r) / μ (B r)).toReal = (ρneg (B r)).toReal / (μ (B r)).toReal :=
      ENNReal.toReal_div _ _
    have h1_div : (ρpos (B r)).toReal / (μ (B r)).toReal - (ρneg (B r)).toReal / (μ (B r)).toReal =
        ((ρpos (B r)).toReal - (ρneg (B r)).toReal) / (μ (B r)).toReal := by ring
    rw [h1, h2, h1_div, h_jordan r]
    have h4 : ρ (B r) = (distributionalDerivative U (B r)) i :=
      hρ_apply (B r) (hB_meas r)
    rw [h4] <;> ring
  have h_eq_limit : ((ρpos.rnDeriv μ) x).toReal - ((ρneg.rnDeriv μ) x).toReal = (ρ.rnDeriv μ) x := by
    dsimp only [ρpos, ρneg, SignedMeasure.rnDeriv]
    <;> rfl
  rw [h_eq_fn] at h_sub
  rw [h_eq_limit] at h_sub
  rw [hrn] at h_sub
  exact h_sub

/-- **Polar bound at reduced boundary points**.

For `perimeterMeasure U`-a.e. `x`, there exists `r0 > 0` such that for all `0 < r < r0`,
`perimeterMeasure U (closedBall x r) ≤ 2 * |inner(distributionalDerivative U (closedBall x r), ν0)|`
where `ν0 = measureTheoreticNormal U x`.

Proof: Let `ρ(A) := inner(Dχ_U(A), ν0)`. Then `ρ.variation ≤ perimeterMeasure U`.
By Besicovitch differentiation applied to `ρ⁺` and `ρ⁻`,
`ρ(closedBall x r) / μ(closedBall x r) → inner(ν0, ν0) = 1`.
Hence for small r, the ratio is ≥ 1/2. -/
lemma polar_bound_at_reduced_boundary
    {U : Set (E n)} (h_perim_finite : perimeter U < ⊤) (hn : 2 ≤ n) :
    ∀ᵐ (x : E n) ∂(perimeterMeasure U),
      ∃ (r0 : ℝ), 0 < r0 ∧ ∀ (r : ℝ), 0 < r → r < r0 →
        perimeterMeasure U (closedBall x r) ≤
          2 * ENNReal.ofReal |inner ℝ (distributionalDerivative U (closedBall x r)) (measureTheoreticNormal U x)| := by
  let μ := perimeterMeasure U
  let f := measureTheoreticNormal U
  have h_main1 : distributionalDerivative U = μ.withDensityᵥ f :=
    (measureTheoreticNormal_withDensity h_perim_finite).2
  have h_norm_one : ∀ᵐ x ∂μ, ‖f x‖ = 1 := norm_measureTheoreticNormal_eq_one h_perim_finite
  have h1 : μ Set.univ < ⊤ := by
    rw [← perimeter_eq_variation U h_perim_finite] <;> exact h_perim_finite
  letI : IsFiniteMeasure μ := ⟨h1⟩
  have h_ae : ∀ᵐ (x : E n) ∂μ,
      Tendsto (fun r : ℝ =>
        inner ℝ (distributionalDerivative U (closedBall x r)) (f x) / (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (inner ℝ (f x) (f x))) := by
    have h_all : ∀ᵐ (x : E n) ∂μ, ∀ (i : Fin n),
        Tendsto (fun r : ℝ =>
          ((distributionalDerivative U (closedBall x r)) i) / (μ (closedBall x r)).toReal)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds ((f x) i)) := by
      exact ae_all_iff.mpr (fun i => coordinate_differentiation h_perim_finite i)
    filter_upwards [h_all] with x hx
    have h_sum : Tendsto (fun r : ℝ =>
        ∑ i : Fin n, (((distributionalDerivative U (closedBall x r)) i) / (μ (closedBall x r)).toReal * (f x) i))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∑ i : Fin n, (f x) i * (f x) i)) := by
      apply tendsto_finsetSum
      intro i _
      have h_i : Tendsto (fun r : ℝ => ((distributionalDerivative U (closedBall x r)) i) / (μ (closedBall x r)).toReal)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds ((f x) i)) := hx i
      exact h_i.mul tendsto_const_nhds
    have h_eq1 : ∀ r, (∑ i : Fin n, (((distributionalDerivative U (closedBall x r)) i) / (μ (closedBall x r)).toReal * (f x) i)) =
        inner ℝ (distributionalDerivative U (closedBall x r)) (f x) / (μ (closedBall x r)).toReal := by
      intro r
      have h : inner ℝ (distributionalDerivative U (closedBall x r)) (f x) =
          ∑ i : Fin n, (distributionalDerivative U (closedBall x r)) i * (f x) i := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro i _
        exact Real.inner_apply _ _
      rw [h]
      let c := (μ (closedBall x r)).toReal
      have h_term : ∀ (i : Fin n),
          ((distributionalDerivative U (closedBall x r)) i) / c * (f x) i =
          ((distributionalDerivative U (closedBall x r)) i) * (f x) i / c := by
        intro i; ring
      have h_sum' : ∑ i : Fin n, (((distributionalDerivative U (closedBall x r)) i) / c * (f x) i) =
          ∑ i : Fin n, (((distributionalDerivative U (closedBall x r)) i) * (f x) i / c) := by
        apply Finset.sum_congr rfl; intro i _; exact h_term i
      rw [h_sum', Finset.sum_div]
    have h_eq2 : (∑ i : Fin n, (f x) i * (f x) i) = inner ℝ (f x) (f x) := by
      have h : inner ℝ (f x) (f x) = ∑ i : Fin n, (f x) i * (f x) i := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro i _
        exact Real.inner_apply _ _
      exact Eq.symm h
    rw [funext h_eq1] at h_sum
    rw [h_eq2] at h_sum
    exact h_sum
  filter_upwards [h_norm_one, h_ae] with x hx_norm hx_tendsto
  have h1 : inner ℝ (f x) (f x) = 1 := by
    have h2 : inner ℝ (f x) (f x) = ‖f x‖ ^ 2 := inner_self_eq_norm_sq_to_K (f x)
    rw [h2, hx_norm] <;> norm_num
  have h_near : ∀ᶠ (y : ℝ) in nhds (inner ℝ (f x) (f x)), (1 / 2 : ℝ) ≤ y := by
    rw [h1]
    have h : Ioi (1 / 2 : ℝ) ∈ nhds (1 : ℝ) := Ioi_mem_nhds (by norm_num)
    filter_upwards [h] with y hy
    exact le_of_lt hy
  have h3 : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      (1 / 2 : ℝ) ≤ inner ℝ (distributionalDerivative U (closedBall x r)) (f x) / (μ (closedBall x r)).toReal :=
    hx_tendsto.eventually h_near
  have h3' : ∀ᶠ (r : ℝ) in nhds 0, r ∈ Set.Ioi 0 → (1 / 2 : ℝ) ≤ inner ℝ (distributionalDerivative U (closedBall x r)) (f x) / (μ (closedBall x r)).toReal :=
    (eventually_nhdsWithin_iff.mp h3)
  rcases Metric.eventually_nhds_iff.mp h3' with ⟨r0, hr0_pos, h4⟩
  refine ⟨r0, hr0_pos, fun r hr_pos hr_lt => ?_⟩
  have h_dist : dist r 0 < r0 := by
    simpa [Real.dist_eq, abs_lt] using ⟨by linarith, by linarith⟩
  have h5 : (1 / 2 : ℝ) ≤ inner ℝ (distributionalDerivative U (closedBall x r)) (f x) / (μ (closedBall x r)).toReal :=
    h4 (y := r) h_dist hr_pos
  have hμ_pos : 0 < μ (closedBall x r) := by
    by_contra h
    have h' : μ (closedBall x r) = 0 := by simpa [not_lt] using h
    have h'' : (μ (closedBall x r)).toReal = 0 := by
      rw [h'] <;> simp
    rw [h''] at h5
    norm_num at h5
  have h7 : 0 < (μ (closedBall x r)).toReal := by
    rw [ENNReal.toReal_pos_iff] <;> exact ⟨hμ_pos, measure_lt_top μ (closedBall x r)⟩
  have h9 : (1 / 2 : ℝ) * (μ (closedBall x r)).toReal ≤ inner ℝ (distributionalDerivative U (closedBall x r)) (f x) := by
    calc (1 / 2 : ℝ) * (μ (closedBall x r)).toReal
      ≤ (inner ℝ (distributionalDerivative U (closedBall x r)) (f x) / (μ (closedBall x r)).toReal) * (μ (closedBall x r)).toReal := by gcongr
    _ = inner ℝ (distributionalDerivative U (closedBall x r)) (f x) := by
      field_simp [h7.ne'] <;> ring
  have h10 : μ (closedBall x r) ≤ 2 * ENNReal.ofReal |inner ℝ (distributionalDerivative U (closedBall x r)) (f x)| := by
    have h11 : 0 ≤ inner ℝ (distributionalDerivative U (closedBall x r)) (f x) := by linarith
    have h12 : |inner ℝ (distributionalDerivative U (closedBall x r)) (f x)| = inner ℝ (distributionalDerivative U (closedBall x r)) (f x) :=
      abs_of_nonneg h11
    rw [h12]
    have h13 : (μ (closedBall x r)).toReal ≤ 2 * inner ℝ (distributionalDerivative U (closedBall x r)) (f x) := by linarith
    have h_fin : μ (closedBall x r) < ⊤ := measure_lt_top μ (closedBall x r)
    have h_eq : ENNReal.ofReal ((μ (closedBall x r)).toReal) = μ (closedBall x r) :=
      ENNReal.ofReal_toReal h_fin.ne
    have h14 : μ (closedBall x r) ≤ ENNReal.ofReal (2 * inner ℝ (distributionalDerivative U (closedBall x r)) (f x)) := by
      rw [← h_eq]
      exact ENNReal.ofReal_le_ofReal h13
    have h15 : ENNReal.ofReal (2 * inner ℝ (distributionalDerivative U (closedBall x r)) (f x)) =
        (2 : ENNReal) * ENNReal.ofReal (inner ℝ (distributionalDerivative U (closedBall x r)) (f x)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      <;> norm_cast
    rw [h15] at h14
    exact h14
  exact h10

-- ============================================================================
-- Coarea integral formula (self-contained, bypasses IntersectionBall.lean)
-- ============================================================================

/-- General coarea formula for integrals of functions of the distance. -/
lemma coarea_integral' (hn : 2 ≤ n)
    {C : Set (E n)} (hC : IsClosed C) (hne : C.Nonempty)
    (h_d_meas : FunctionLevelMeasurable (fun x : E n => infDist x C))
    {A : Set (E n)} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_sub : A ⊆ {x | 0 < infDist x C})
    {g : ℝ → ENNReal} (hg : Measurable g) :
    ∫⁻ x in A, g (infDist x C) ∂volume =
      ∫⁻ t, g t * μHE[n - 1] {x ∈ A | infDist x C = t} ∂volume := by
  let d : E n → ℝ := fun x => infDist x C
  let μ_map : Measure ℝ := Measure.map d (volume.restrict A)
  let H : ℝ → ENNReal := fun t => μHE[n - 1] {x ∈ A | d x = t}
  let ν : Measure ℝ := volume.withDensity H
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by linarith)
  have hd_meas : Measurable d := (Metric.continuous_infDist_pt C).measurable
  have h_eq_Ioc : ∀ (a b : ℝ), a < b → μ_map (Set.Ioc a b) = ν (Set.Ioc a b) := by
    intro a b hab
    have h1 : μ_map (Set.Ioc a b) = volume {x ∈ A | a < d x ∧ d x ≤ b} := by
      have h_map1 : μ_map (Set.Ioc a b) = (volume.restrict A) (d ⁻¹' (Set.Ioc a b)) :=
        Measure.map_apply hd_meas measurableSet_Ioc
      have h_restrict : (volume.restrict A) (d ⁻¹' (Set.Ioc a b)) = volume (d ⁻¹' (Set.Ioc a b) ∩ A) :=
        Measure.restrict_apply (hd_meas measurableSet_Ioc)
      have h_set : d ⁻¹' (Set.Ioc a b) ∩ A = {x ∈ A | a < d x ∧ d x ≤ b} := by
        ext x; simp [Set.mem_preimage, Set.mem_Ioc] <;> tauto
      rw [h_map1, h_restrict, h_set]
    have h2 : ν (Set.Ioc a b) = ∫⁻ s in Set.Ioc a b, H s := by
      simpa [ν] using rfl
    rw [h1, h2]
    exact distance_coarea_eq hn hC hne h_d_meas hA hA_bdd hA_sub hab
  let C_set : Set (Set ℝ) := {S | ∃ l u, l < u ∧ Set.Ioc l u = S}
  have h_pi : IsPiSystem C_set := isPiSystem_Ioc (fun x : ℝ => x) (fun x : ℝ => x)
  have h_borel : borel ℝ = MeasurableSpace.generateFrom C_set := borel_eq_generateFrom_Ioc ℝ
  rcases hne with ⟨c₀, hc₀⟩
  have hne' : C.Nonempty := ⟨c₀, hc₀⟩
  have h_exists_R : ∃ (R : ℝ), ∀ x ∈ A, dist x c₀ ≤ R := by
    rcases hA_bdd.subset_ball c₀ with ⟨R, hR⟩
    refine ⟨R, fun x hx => (hR hx).le⟩
  rcases h_exists_R with ⟨R, hR⟩
  let M : ℝ := max R 0
  have h_bdd_d : ∀ x ∈ A, d x ≤ M := by
    intro x hx
    have h2 : d x ≤ dist x c₀ := Metric.infDist_le_dist_of_mem hc₀
    have h3 : dist x c₀ ≤ R := hR x hx
    exact h2.trans (h3.trans (le_max_left R 0))
  let a0 : ℝ := -1
  let b0 : ℝ := M + 1
  have h_support : ∀ (t : ℝ), t ∉ Set.Ioc a0 b0 → H t = 0 := by
    intro t ht
    have h3 : t ≤ a0 ∨ b0 < t := by
      have h4 : ¬(a0 < t ∧ t ≤ b0) := ht
      by_cases h5 : t ≤ a0
      · exact Or.inl h5
      · have h6 : a0 < t := by linarith
        have h7 : ¬(t ≤ b0) := by intro h8; exact h4 ⟨h6, h8⟩
        have h9 : b0 < t := by linarith
        exact Or.inr h9
    rcases h3 with (h3 | h3)
    · have h4 : {x ∈ A | d x = t} = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have h5 : d x = t := hx.2
        have h6 : 0 < d x := hA_sub hx.1
        rw [h5] at h6
        linarith
      have hH : H t = μHE[n - 1] {x ∈ A | d x = t} := by rfl
      rw [hH, h4] <;> simp
    · have h4 : {x ∈ A | d x = t} = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have h5 : d x = t := hx.2
        have h6 : d x ≤ M := h_bdd_d x hx.1
        rw [h5] at h6
        linarith
      have hH : H t = μHE[n - 1] {x ∈ A | d x = t} := by rfl
      rw [hH, h4] <;> simp
  have h_μmap_supp : μ_map (Set.Ioc a0 b0)ᶜ = 0 := by
    rw [Measure.map_apply hd_meas (measurableSet_Ioc.compl)]
    have h_empty : d ⁻¹' (Set.Ioc a0 b0)ᶜ ∩ A = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
      intro ⟨hx1, hx2⟩
      have h_pos : 0 < d x := hA_sub hx2
      have h_le : d x ≤ M := h_bdd_d x hx2
      have h_in : d x ∈ Set.Ioc a0 b0 := ⟨by linarith, by linarith⟩
      exact hx1 h_in
    rw [Measure.restrict_apply (hd_meas measurableSet_Ioc.compl), h_empty]
    <;> simp
  have h1 : μ_map Set.univ = μ_map (Set.Ioc a0 b0) := by
    have h_disj : Disjoint (Set.Ioc a0 b0) (Set.Ioc a0 b0)ᶜ := disjoint_compl_right
    have h_union : (Set.Ioc a0 b0) ∪ (Set.Ioc a0 b0)ᶜ = Set.univ := by simp
    have h : μ_map Set.univ = μ_map (Set.Ioc a0 b0) + μ_map (Set.Ioc a0 b0)ᶜ := by
      rw [← h_union, measure_union h_disj measurableSet_Ioc.compl] <;> simp
    rw [h, h_μmap_supp] <;> simp
  have h_ab : a0 < b0 := by
    dsimp only [a0, b0, M] <;> linarith [le_max_right R 0]
  have h2 : μ_map (Set.Ioc a0 b0) < ⊤ := by
    have h_eq2 : μ_map (Set.Ioc a0 b0) = volume {x ∈ A | a0 < d x ∧ d x ≤ b0} := by
      have h_coarea := distance_coarea_eq hn hC hne' h_d_meas hA hA_bdd hA_sub h_ab
      have h_ν : ν (Set.Ioc a0 b0) = ∫⁻ s in Set.Ioc a0 b0, H s ∂volume := by
        simpa [ν] using rfl
      calc μ_map (Set.Ioc a0 b0)
        = ν (Set.Ioc a0 b0) := h_eq_Ioc a0 b0 h_ab
      _ = ∫⁻ s in Set.Ioc a0 b0, H s ∂volume := h_ν
      _ = volume {x ∈ A | a0 < d x ∧ d x ≤ b0} := h_coarea.symm
    rw [h_eq2]
    have h_sub : {x ∈ A | a0 < d x ∧ d x ≤ b0} ⊆ A := fun y hy => hy.1
    have h_set_bdd : Bornology.IsBounded {x ∈ A | a0 < d x ∧ d x ≤ b0} :=
      hA_bdd.subset h_sub
    exact h_set_bdd.measure_lt_top
  have hμ_finite : IsFiniteMeasure μ_map := by
    refine' ⟨_⟩
    rw [h1]
    exact h2
  have h_ν_supp : ν (Set.Ioc a0 b0)ᶜ = 0 := by
    have h : ∀ t ∈ (Set.Ioc a0 b0)ᶜ, H t = 0 := fun t ht => h_support t ht
    have h6 : ν (Set.Ioc a0 b0)ᶜ = ∫⁻ t in (Set.Ioc a0 b0)ᶜ, H t ∂volume := by
      simp [ν]
      <;> rfl
    rw [h6]
    have h7 : ∫⁻ t in (Set.Ioc a0 b0)ᶜ, H t = 0 := by
      rw [MeasureTheory.setLIntegral_congr_fun (measurableSet_Ioc.compl) (fun t ht => h t ht)]
      <;> simp
    exact h7
  have h_univ : μ_map Set.univ = ν Set.univ := by
    have h2 : ν Set.univ = ν (Set.Ioc a0 b0) := by
      have h_disj : Disjoint (Set.Ioc a0 b0) (Set.Ioc a0 b0)ᶜ := disjoint_compl_right
      have h_union : (Set.Ioc a0 b0) ∪ (Set.Ioc a0 b0)ᶜ = Set.univ := by simp
      have h : ν Set.univ = ν (Set.Ioc a0 b0) + ν (Set.Ioc a0 b0)ᶜ := by
        rw [← h_union, measure_union h_disj measurableSet_Ioc.compl] <;> simp
      rw [h, h_ν_supp] <;> simp
    rw [h1, h2, h_eq_Ioc a0 b0 h_ab]
  let _i : IsFiniteMeasure μ_map := hμ_finite
  have h_eq : μ_map = ν := by
    exact ext_of_generate_finite C_set h_borel h_pi
      (fun s hs => by rcases hs with ⟨l, u, hlu, rfl⟩; exact h_eq_Ioc l u hlu) h_univ
  have h_main1 : ∫⁻ x in A, g (d x) ∂volume = ∫⁻ t, g t ∂μ_map := by
    have h_eq1 : ∫⁻ x in A, g (d x) ∂volume = ∫⁻ x, g (d x) ∂(volume.restrict A) := by rfl
    rw [h_eq1]
    exact (lintegral_map' hg.aemeasurable hd_meas.aemeasurable).symm
  rw [h_main1, h_eq]
  have hH_ae : AEMeasurable H volume := by
    have h1 : AEMeasurable H (volume.restrict (Set.Ioc a0 b0)) :=
      h_d_meas A hA a0 b0
    let H' := h1.mk H
    have hH'_meas : Measurable H' := h1.measurable_mk
    have h_eq1 : H =ᵐ[volume.restrict (Set.Ioc a0 b0)] H' := h1.ae_eq_mk
    let H'' := (Set.Ioc a0 b0).indicator H'
    have hH''_meas : Measurable H'' := hH'_meas.indicator measurableSet_Ioc
    have h_eq2 : H =ᵐ[volume] H'' := by
      have h3 : ∀ᵐ (t : ℝ) ∂volume, t ∈ Set.Ioc a0 b0 → H t = H' t :=
        (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp h_eq1
      filter_upwards [h3] with t ht
      by_cases h4 : t ∈ Set.Ioc a0 b0
      · have h5 : H t = H' t := ht h4
        simpa [H'', h4] using h5
      · have h6 : H t = 0 := h_support t h4
        simpa [H'', h4] using h6
    exact ⟨H'', hH''_meas, h_eq2⟩
  have h_main2 : ∫⁻ t, g t ∂ν = ∫⁻ t, g t * H t ∂volume := by
    have h := MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀' hH_ae hg.aemeasurable
    have h_comm : (fun t : ℝ => (H * g) t) = (fun t : ℝ => g t * H t) := by
      funext t
      exact mul_comm (H t) (g t)
    rw [h, h_comm]
  exact h_main2


-- ============================================================================
-- Cutoff inequality (proven in CutoffInequality.lean)
-- ============================================================================

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- **Perimeter density upper bound**.

For `perimeterMeasure U`-a.e. `x`, there exist `C > 0` and `r0 > 0` such that
`perimeterIn U (ball x r) ≤ C * r^(n-1)` for all `0 < r < r0`.

Proof:
1. Polar bound: `μ(closedBall x r) ≤ 2|inner(D(closedBall x r), ν(x))|` for small r
2. Cutoff inequality: `|inner(D(closedBall x r), ν(x))| ≤ C0*r^(n-1)` for a.e. r
3. Combine: `μ(closedBall x r) ≤ 2*C0*r^(n-1)` for a.e. small r
4. Monotonicity extension: bound holds for all small r
5. `perimeterIn U (ball x r) ≤ μ(ball x r) ≤ μ(closedBall x r)` -/
theorem perimeter_density_upper_bound
    {U : Set (E n)} (hU : IsOpen U) (hBdd : Bornology.IsBounded U)
    (h_perim_finite : perimeter U < ⊤) (hn : 2 ≤ n) :
    ∀ᵐ (x : E n) ∂(perimeterMeasure U),
      ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterIn U (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)) := by
  let μ := perimeterMeasure U
  let ν := measureTheoreticNormal U
  let D := distributionalDerivative U
  let C0_real : ℝ := (μHE[n - 1] (sphere (0 : E n) 1)).toReal
  let C0' : ℝ := max C0_real 1
  have hC0'_pos : 0 < C0' := by positivity
  have hC0_le : C0_real ≤ C0' := le_max_left _ _

  have h_polar : ∀ᵐ (x : E n) ∂μ, ∃ (r0 : ℝ), 0 < r0 ∧ ∀ (r : ℝ), 0 < r → r < r0 →
      μ (closedBall x r) ≤ 2 * ENNReal.ofReal |inner ℝ (D (closedBall x r)) (ν x)| :=
    polar_bound_at_reduced_boundary h_perim_finite hn

  have h_norm_one : ∀ᵐ (x : E n) ∂μ, ‖ν x‖ = 1 :=
    norm_measureTheoreticNormal_eq_one h_perim_finite

  have h_cutoff : ∀ (x : E n) (ν0 : E n), ‖ν0‖ = 1 →
      ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
        |inner ℝ (D (closedBall x r)) ν0| ≤ C0_real * r ^ (n - 1) :=
    fun x ν0 hν0 => cutoff_inequality hU.measurableSet hBdd h_perim_finite hn x ν0 hν0

  filter_upwards [h_polar, h_norm_one] with x hx_polar hx_norm
  rcases hx_polar with ⟨r1, hr1_pos, hx_polar⟩
  let ν0 := ν x
  have hν0_unit : ‖ν0‖ = 1 := hx_norm

  have h_cutoff_ae : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
      |inner ℝ (D (closedBall x r)) ν0| ≤ C0_real * r ^ (n - 1) :=
    h_cutoff x ν0 hν0_unit

  have h_ae_bound : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioo 0 r1),
      μ (closedBall x r) ≤ ENNReal.ofReal ((2 * C0') * r ^ (n - 1)) := by
    rw [ae_restrict_iff' (isOpen_Ioo.measurableSet)]
    have h2 : ∀ᵐ (r : ℝ) ∂volume, r ∈ Set.Ioi (0 : ℝ) →
        |inner ℝ (D (closedBall x r)) ν0| ≤ C0_real * r ^ (n - 1) := by
      rw [ae_restrict_iff' isOpen_Ioi.measurableSet] at h_cutoff_ae
      exact h_cutoff_ae
    filter_upwards [h2] with r hr_cutoff
    intro hr_in
    have hr_pos : 0 < r := hr_in.1
    have hr_lt : r < r1 := hr_in.2
    have h1 : μ (closedBall x r) ≤ 2 * ENNReal.ofReal |inner ℝ (D (closedBall x r)) ν0| :=
      hx_polar r hr_pos hr_lt
    have hP : |inner ℝ (D (closedBall x r)) ν0| ≤ C0_real * r ^ (n - 1) := hr_cutoff hr_pos
    have h_rpow_pos : 0 ≤ r ^ (n - 1) := by positivity
    have h3 : |inner ℝ (D (closedBall x r)) ν0| ≤ C0' * r ^ (n - 1) := by
      calc |inner ℝ (D (closedBall x r)) ν0|
        ≤ C0_real * r ^ (n - 1) := hP
      _ ≤ C0' * r ^ (n - 1) := by
        exact mul_le_mul_of_nonneg_right hC0_le h_rpow_pos
    have h_pos1 : 0 ≤ C0' * r ^ (n - 1) := by positivity
    have h10 : ENNReal.ofReal |inner ℝ (D (closedBall x r)) ν0| ≤
        ENNReal.ofReal (C0' * r ^ (n - 1)) :=
      (ENNReal.ofReal_le_ofReal_iff h_pos1).mpr h3
    have h11 : (2 : ENNReal) * ENNReal.ofReal |inner ℝ (D (closedBall x r)) ν0| ≤
        (2 : ENNReal) * ENNReal.ofReal (C0' * r ^ (n - 1)) :=
      mul_le_mul_left' h10 (2 : ENNReal)
    have h12 : (2 : ENNReal) * ENNReal.ofReal (C0' * r ^ (n - 1)) ≤
        ENNReal.ofReal ((2 * C0') * r ^ (n - 1)) := by
      have h_ring : (2 * C0') * r ^ (n - 1) = (2 : ℝ) * (C0' * r ^ (n - 1)) := by ring
      rw [h_ring]
      have h_mul_eq : ENNReal.ofReal ((2 : ℝ) * (C0' * r ^ (n - 1))) =
          ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (C0' * r ^ (n - 1)) := by
        rw [ENNReal.ofReal_mul] <;> positivity
      have h_coe : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by
        simpa using ENNReal.ofReal_coe_nat 2
      rw [h_mul_eq, h_coe] <;> exact le_refl _
    have h4 : 2 * ENNReal.ofReal |inner ℝ (D (closedBall x r)) ν0| ≤
        ENNReal.ofReal ((2 * C0') * r ^ (n - 1)) :=
      le_trans h11 h12
    exact h1.trans h4

  let C_final : ℝ := (2 * C0') * (2 ^ (n - 1) : ℝ)
  have hC_final_pos : 0 < C_final := by positivity

  have h_all_small : ∀ r, 0 < r → r < r1 / 2 →
      μ (closedBall x r) ≤ ENNReal.ofReal (C_final * r ^ (n - 1)) :=
    monotone_ae_bound_extension (by positivity) hr1_pos
      (fun r₁ r₂ h => measure_mono (closedBall_subset_closedBall h)) h_ae_bound

  refine ⟨C_final, r1 / 2, hC_final_pos, by positivity, fun r hr_pos hr_lt => ?_⟩
  have h4 : perimeterIn U (ball x r) ≤ μ (ball x r) :=
    perimeterIn_le_perimeterMeasure h_perim_finite
  have h5 : μ (ball x r) ≤ μ (closedBall x r) := measure_mono ball_subset_closedBall
  have h6 : μ (closedBall x r) ≤ ENNReal.ofReal (C_final * r ^ (n - 1)) :=
    h_all_small r hr_pos hr_lt
  exact h4.trans (h5.trans h6)

end Geometry.StructureTheorem
