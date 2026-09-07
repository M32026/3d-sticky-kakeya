module

/-
  FrontEndLemmas.FrontEndCompositionHelpers

  Standalone helper lemmas extracted from FrontEndComposition to reduce
  per-file elaboration cost and avoid OOM during compilation.

  Contains ~38 helper lemmas for:
  - Dyadic scale arithmetic (dyadicDelta injectivity, step, anti-monotonicity)
  - Affine line offset bounds
  - Real.rpow numerical absorption inequalities
  - M even/lower/upper bound helpers
  - Scale transfer exponent inequalities
  - Dyadic square center coordinate and distance bounds
  - Swap-adaptation helpers for S-sets and separation

  These lemmas are in the FrontEndComposition namespace so the main theorem
  file can access them without qualification.

  ## Proof route (source-first exact-scale normalization)

  1. **Parameter selection**: `parameter_selection` → ε, A, η_axiom, δ₀_axiom,
     η_upper, δ₀, numerical bounds, QTTC, RKP.
  2. **Public exponent**: εA = ε/50. Internal εA_int = εA + ρ_scale = ε/25.
  3. **Exact even dyadic scale ABOVE public δ**:
     `exists_even_dyadic_scale_above` → even n, δ ≤ δ_n ≤ 4δ.
     Set m = n/2, Δ = _root_.dyadicDelta m, δ_n = _root_.dyadicDelta n = Δ².
  4. **Scale transfer** (δ → δ_n):
     - Coarsen S-set: two-step `coarsen_scale`, constant 81, absorb into εA_int.
     - Transfer sqrt covering via `sqrt_regularity_transfer_above`.
     - Tube S-sets similarly.
     - Incidence automatic (δ_n ≥ δ).
     - Failure bounds absorb K_scale factors into εA_int.
  5. **cardP thinning**: `cardP_thinning` at δ_n → Pbar with |Pbar| ≤ δ_n^{-u}.
  6. **NiceConfiguration**: `source_to_nice_configuration` at δ_n on Pbar.
  7. **Scale alignment**: prove n_cfg = n by dyadic uniqueness.
  8. **Numerical bounds**: `h_num_bounds` with predefined K_pack (before B1).
  9. **B1 bridge** (stub): `B1BridgeDecomposition` using source S-set for coarse lower.
  10. **Counter data** (stub): `CounterAssumptionData`.
  11. **uniform_appendix_A_alternative**: derive False from both bounds failing.
  12. **Conclude**: fine bound ∨ coarse bound.

  Whiteprint node: front_end_lemmas / front_end_composition
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.ScaleNormalization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.DeltasSetTreeExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction.ParameterSelection
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.UniformAppendixAAlternative
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction.B1InductionApplication
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.SourceToNiceConfigurationFront
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SnappingSSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.EndpointAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.TFullUpperBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1FrontUpperBounds
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.NiceConfigToA1
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TwoSBoundHelper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TDeltaGlobalConstruction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.CGlobalCardBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_FromA1
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_PerSquare
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A1_to_LinkedA2
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A1_to_A4_v2_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_to_A3_Bridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.Provenance17Delta
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.TSubSource
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.HDyadicBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AssemblyNumericalHypotheses
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.B1ToA1Skeleton
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section


namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.FrontEndComposition

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open DirecretisedFurstenbergEstimate.FrontEndLemmas
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction
open DirecretisedFurstenbergEstimate.Section9
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate.FrontEndLemmas.B1Assembly
open DirecretisedFurstenbergEstimate.FrontEndLemmas.B1FrontUpperBounds
open DiscretisedFurstenbergEstimate.InductionConfigurations
open HeavyParentFiltering
open B1HardFields
open SquareGeometry
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter

/-- Local injectivity of _root_.dyadicDelta. -/
lemma dyadicDelta_injective_local : Function.Injective _root_.dyadicDelta := by
  intro m n h
  simp only [_root_.dyadicDelta] at h
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_log : Real.log (Real.rpow 2 (-↑m)) = Real.log (Real.rpow 2 (-↑n)) := by rw [h]
  have h_log_m : Real.log (Real.rpow 2 (-↑m)) = (-↑m : ℝ) * Real.log 2 :=
    Real.log_rpow (show (0 : ℝ) < 2 from by norm_num) (-↑m)
  have h_log_n : Real.log (Real.rpow 2 (-↑n)) = (-↑n : ℝ) * Real.log 2 :=
    Real.log_rpow (show (0 : ℝ) < 2 from by norm_num) (-↑n)
  have h_eq : (-↑m : ℝ) * Real.log 2 = (-↑n : ℝ) * Real.log 2 := by
    rw [←h_log_m, ←h_log_n]; exact h_log
  have h5 : (-↑m : ℝ) = (-↑n : ℝ) := by
    have h_diff : ((-↑m : ℝ) - (-↑n : ℝ)) * Real.log 2 = 0 := by linarith
    have h' : (-↑m : ℝ) - (-↑n : ℝ) = 0 := by
      exact (mul_eq_zero.mp h_diff).resolve_right hlog_pos.ne'
    linarith
  have h6 : (m : ℝ) = (n : ℝ) := by linarith
  exact_mod_cast h6

/-- If `‖p‖ ≤ 1`, `δ_n ≤ 1`, and `p` is within `δ_n` of affine line `ℓ`,
    then `‖ℓ.offset‖ ≤ 2`. Extracted as a standalone lemma to avoid elaboration
    timeouts in the Real.rpow-dense main proof context. -/
lemma affine_line_offset_bound {δ_n : ℝ} (p : EuclideanPlane) (ℓ : AffineLine)
    (h_p_norm : ‖p‖ ≤ 1) (hδ_n_pos : 0 < δ_n) (hδ_n_le_one : δ_n ≤ 1)
    (h_inc : p ∈ Metric.cthickening δ_n (ℓ.1 : Set EuclideanPlane)) :
    ‖ℓ.offset‖ ≤ 2 := by
  let q : EuclideanPlane := ↑(EuclideanGeometry.orthogonalProjection ℓ.1 p)
  have hq_in : q ∈ ℓ.1 := (EuclideanGeometry.orthogonalProjection ℓ.1 p).2
  have h_dist_eq : dist p q = Metric.infDist p ℓ.1 := by
    have h := EuclideanGeometry.dist_orthogonalProjection_eq_infDist ℓ.1 p
    simpa [q] using h
  have h_infEDist_le : Metric.infEDist p ℓ.1 ≤ ENNReal.ofReal δ_n :=
    Metric.mem_cthickening_iff.mp h_inc
  have h_ne_top : Metric.infEDist p ℓ.1 ≠ ⊤ :=
    Metric.infEDist_ne_top (ℓ.nonempty)
  have h_ofReal_ne_top : (ENNReal.ofReal δ_n) ≠ ⊤ := by simp
  have h_infDist_le : Metric.infDist p ℓ.1 ≤ δ_n := by
    have h3 : ENNReal.toReal (Metric.infEDist p ℓ.1) ≤ ENNReal.toReal (ENNReal.ofReal δ_n) :=
      (ENNReal.toReal_le_toReal h_ne_top h_ofReal_ne_top).mpr h_infEDist_le
    have h4 : ENNReal.toReal (ENNReal.ofReal δ_n) = δ_n := ENNReal.toReal_ofReal hδ_n_pos.le
    simpa [Metric.infDist, h4] using h3
  have hdist : dist p q ≤ δ_n := by
    rw [h_dist_eq]; exact h_infDist_le
  have hq_norm : ‖q‖ ≤ 1 + δ_n := by
    have h_tri : dist q 0 ≤ dist q p + dist p 0 := dist_triangle q p 0
    have h4 : dist q 0 = ‖q‖ := by simp
    have h5 : dist q p = dist p q := dist_comm q p
    have h6 : dist p 0 = ‖p‖ := by simp
    rw [h4, h5, h6] at h_tri
    have h7 : dist p q + ‖p‖ = ‖p‖ + dist p q := add_comm (dist p q) ‖p‖
    rw [h7] at h_tri
    have h_upper : ‖p‖ + dist p q ≤ 1 + δ_n := add_le_add h_p_norm hdist
    exact le_trans h_tri h_upper
  have hq_norm2 : ‖q‖ ≤ 2 := by
    calc ‖q‖ ≤ 1 + δ_n := hq_norm
      _ ≤ 1 + 1 := by gcongr
      _ = 2 := by norm_num
  have hproj : ‖ℓ.offset‖ ≤ ‖q‖ := by
    have h1 : dist (0 : EuclideanPlane) ℓ.offset = Metric.infDist (0 : EuclideanPlane) ℓ.1 := by
      have h := EuclideanGeometry.dist_orthogonalProjection_eq_infDist ℓ.1 (0 : EuclideanPlane)
      simpa [AffineLine.offset] using h
    have h2 : Metric.infDist (0 : EuclideanPlane) ℓ.1 ≤ dist (0 : EuclideanPlane) q :=
      Metric.infDist_le_dist_of_mem hq_in
    have h3 : dist (0 : EuclideanPlane) ℓ.offset ≤ dist (0 : EuclideanPlane) q :=
      le_trans (le_of_eq h1) h2
    simpa using h3
  exact le_trans hproj hq_norm2

/-- Wrapper for `affine_line_offset_bound` that builds the full `h_offset`
    hypothesis needed by `source_to_nice_configuration`. Kept outside the
    Real.rpow-dense main proof context to avoid tactic timeouts. -/
lemma offset_bound_wrapper
    {δ_n δA δ : ℝ} {Pbar_set : Set EuclideanPlane}
    {tubeFamily_bar : (p : EuclideanPlane) → p ∈ Pbar_set → Set AffineLine}
    (hPbar_subset_ball : Pbar_set ⊆ Metric.closedBall (0 : EuclideanPlane) 1)
    (hIncidence_bar_n : ∀ (p : EuclideanPlane) (hp : p ∈ Pbar_set),
      ∀ (T : AffineLine), T ∈ tubeFamily_bar p hp →
        p ∈ Metric.cthickening δ_n (T.1 : Set EuclideanPlane))
    (hδ_n_pos : 0 < δ_n)
    (hδ_n_le_4δ' : δ_n ≤ 4 * δ)
    (hδ_le_δA : δ ≤ δA)
    (hδA_le_third_const : δA ≤ 1 / 37) :
    ∀ (p : EuclideanPlane) (hp : p ∈ Pbar_set),
      ∀ (ℓ : AffineLine), ℓ ∈ tubeFamily_bar p hp →
        ℓ.offset ∈ Metric.closedBall (0 : EuclideanPlane) 2 := by
  intro p hp ℓ hℓ
  have h_p_in_ball : ‖p‖ ≤ 1 := by
    have h : p ∈ Metric.closedBall (0 : EuclideanPlane) 1 := hPbar_subset_ball hp
    have hdist : dist p (0 : EuclideanPlane) ≤ 1 := Metric.mem_closedBall.mp h
    have heq : dist p (0 : EuclideanPlane) = ‖p‖ := by
      simp [dist_comm]
    rw [heq] at hdist
    exact hdist
  have h_inc : p ∈ Metric.cthickening δ_n (ℓ.1 : Set EuclideanPlane) :=
    hIncidence_bar_n p hp ℓ hℓ
  have hδ_n_le_one : δ_n ≤ 1 := by
    have h1 : δ_n ≤ 4 * δA :=
      le_trans hδ_n_le_4δ' (mul_le_mul_of_nonneg_left hδ_le_δA (by norm_num))
    have h2 : 4 * δA ≤ 1 := by
      have h3 : δA ≤ 1 / 37 := hδA_le_third_const
      have h4 : 4 * δA ≤ 4 * (1 / 37 : ℝ) := mul_le_mul_of_nonneg_left h3 (by norm_num)
      have h5 : 4 * (1 / 37 : ℝ) ≤ 1 := by norm_num
      exact le_trans h4 h5
    exact le_trans h1 h2
  have h3 : ‖ℓ.offset‖ ≤ 2 := affine_line_offset_bound p ℓ h_p_in_ball hδ_n_pos hδ_n_le_one h_inc
  simpa [Metric.mem_closedBall, dist_zero_right] using h3

/-- Helper: prove δ_n ≤ 1 from threshold bounds, outside heavy context. -/
lemma delta_n_le_one {δ_n δA δ : ℝ}
    (hδ_n_le_4δ' : δ_n ≤ 4 * δ)
    (hδ_le_δA : δ ≤ δA)
    (hδA_le_third_const : δA ≤ 1 / 37) :
    δ_n ≤ 1 := by
  have h1 : δ_n ≤ 4 * δA := by
    calc δ_n ≤ 4 * δ := hδ_n_le_4δ'
      _ ≤ 4 * δA := by gcongr
  have h2 : 4 * δA ≤ 1 := by
    calc 4 * δA ≤ 4 * (1 / 37 : ℝ) := by gcongr
      _ ≤ 1 := by norm_num
  exact le_trans h1 h2

/-- Helper: prove δ_n ≤ δ₀_nice from threshold bounds, outside heavy context. -/
lemma delta_n_le_nice {δ_n δA δ δ₀_nice : ℝ}
    (hδ_n_le_4δ' : δ_n ≤ 4 * δ)
    (hδ_le_δA : δ ≤ δA)
    (hδA_le_nice : δA ≤ δ₀_nice / 4) :
    δ_n ≤ δ₀_nice := by
  have h1 : δ_n ≤ 4 * δA := by
    calc δ_n ≤ 4 * δ := hδ_n_le_4δ'
      _ ≤ 4 * δA := by gcongr
  have h2 : 4 * δA ≤ δ₀_nice := by
    calc 4 * δA ≤ 4 * (δ₀_nice / 4) := by gcongr
      _ = δ₀_nice := by ring
  exact le_trans h1 h2

/-- Helper: prove `1 ≤ δ_n^{-ε}` when `0 < δ_n < 1` and `ε > 0`. -/
lemma one_le_rpow_neg {δ_n ε : ℝ} (hδ_n_pos : 0 < δ_n) (hδ_n_lt_one : δ_n < 1) (hε_pos : 0 < ε) :
    1 ≤ Real.rpow δ_n (-ε) := by
  have h_neg : -ε < 0 := by linarith
  have h : Real.rpow δ_n (-ε) > 1 :=
    Real.one_lt_rpow_of_pos_of_lt_one_of_neg hδ_n_pos hδ_n_lt_one h_neg
  exact h.le

/-- Helper: prove `0 < δ^x` for any real `x` when `0 < δ`. -/
lemma rpow_pos_helper (δ x : ℝ) (hδ : 0 < δ) : 0 < Real.rpow δ x :=
  Real.rpow_pos_of_pos hδ x

/-- Helper: prove allTubes_bar is bounded, outside heavy context. -/
lemma tubes_bounded
    {Pbar_set : Set EuclideanPlane}
    {Tp : (p : EuclideanPlane) → p ∈ Pbar_set → Set AffineLine}
    (h_offset : ∀ (p : EuclideanPlane) (hp : p ∈ Pbar_set),
      ∀ (ℓ : AffineLine), ℓ ∈ Tp p hp → ℓ.offset ∈ Metric.closedBall (0 : EuclideanPlane) 2)
    (allTubes_bar : Set AffineLine)
    (h_allTubes : allTubes_bar = ⋃ p, ⋃ hp : p ∈ Pbar_set, Tp p hp) :
    Bornology.IsBounded allTubes_bar := by
  by_cases h_empty : allTubes_bar = ∅
  · rw [h_empty]; exact Bornology.isBounded_empty
  · rcases Set.nonempty_iff_ne_empty.mpr h_empty with ⟨ℓ₀, hℓ₀⟩
    have h_dir_norm : ∀ (ℓ : AffineLine), ‖ℓ.1.direction.starProjection‖ = 1 := by
      intro ℓ
      have h1 : 0 < Module.finrank ℝ ℓ.1.direction := by
        rw [ℓ.2]
        norm_num
      have hne : ℓ.1.direction ≠ ⊥ := by
        intro h
        have hfr := ℓ.2
        rw [h] at hfr
        simp at hfr <;> norm_num at hfr
      exact Submodule.norm_starProjection ℓ.1.direction hne
    have h_off_bound : ∀ ℓ ∈ allTubes_bar, ‖ℓ.offset‖ ≤ 2 := by
      intro ℓ hℓ
      rw [h_allTubes] at hℓ
      have h_exists : ∃ (p : EuclideanPlane) (hp : p ∈ Pbar_set), ℓ ∈ Tp p hp := by
        simpa [Set.mem_iUnion] using hℓ
      rcases h_exists with ⟨p, hp, hℓ_in⟩
      have h : ℓ.offset ∈ Metric.closedBall (0 : EuclideanPlane) 2 := h_offset p hp ℓ hℓ_in
      have h2 : ‖ℓ.offset‖ ≤ 2 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using h
      exact h2
    have h_main : allTubes_bar ⊆ Metric.closedBall ℓ₀ 6 := by
      intro ℓ hℓ
      have h4 : dist ℓ ℓ₀ ≤ 6 := by
        have h5 : ‖ℓ.1.direction.starProjection - ℓ₀.1.direction.starProjection‖ ≤ 2 := by
          calc ‖ℓ.1.direction.starProjection - ℓ₀.1.direction.starProjection‖
            ≤ ‖ℓ.1.direction.starProjection‖ + ‖ℓ₀.1.direction.starProjection‖ := norm_sub_le _ _
          _ = 1 + 1 := by rw [h_dir_norm ℓ, h_dir_norm ℓ₀]
          _ = 2 := by norm_num
        have h6 : ‖ℓ.offset - ℓ₀.offset‖ ≤ 4 := by
          have h61 : ‖ℓ.offset‖ ≤ 2 := h_off_bound ℓ hℓ
          have h62 : ‖ℓ₀.offset‖ ≤ 2 := h_off_bound ℓ₀ hℓ₀
          calc ‖ℓ.offset - ℓ₀.offset‖
            ≤ ‖ℓ.offset‖ + ‖ℓ₀.offset‖ := norm_sub_le _ _
          _ ≤ 2 + 2 := by linarith
          _ = 4 := by norm_num
        have h_dist : dist ℓ ℓ₀ = ‖ℓ.1.direction.starProjection - ℓ₀.1.direction.starProjection‖ + ‖ℓ.offset - ℓ₀.offset‖ := by
          rfl
        rw [h_dist]
        linarith
      exact h4
    have h_pairwise : ∀ (x : AffineLine), x ∈ allTubes_bar → ∀ (y : AffineLine), y ∈ allTubes_bar → dist x y ≤ 12 := by
      intro x hx y hy
      have hx' : dist x ℓ₀ ≤ 6 := h_main hx
      have hy' : dist y ℓ₀ ≤ 6 := h_main hy
      calc dist x y ≤ dist x ℓ₀ + dist ℓ₀ y := dist_triangle x ℓ₀ y
        _ = dist x ℓ₀ + dist y ℓ₀ := by rw [dist_comm ℓ₀ y]
        _ ≤ 6 + 6 := by linarith
        _ = 12 := by norm_num
    exact Metric.isBounded_iff.mpr ⟨12, h_pairwise⟩

/-- Step property of _root_.dyadicDelta: δ_{k+1} = (1/2) * δ_k. -/
lemma dyadicDelta_step' (k : ℕ) :
    _root_.dyadicDelta (k + 1) = (1 / 2 : ℝ) * _root_.dyadicDelta k := by
  simp only [_root_.dyadicDelta]
  have h3 : (-( (k + 1 : ℕ) : ℝ)) = (-(k : ℝ)) + (-1 : ℝ) := by
    simp [Nat.cast_add] <;> ring
  rw [h3]
  have h4 : Real.rpow 2 ((-(k : ℝ)) + (-1 : ℝ)) =
      Real.rpow 2 (-(k : ℝ)) * Real.rpow 2 (-1 : ℝ) :=
    Real.rpow_add (by norm_num) _ _
  rw [h4]
  have h5 : Real.rpow 2 (-1 : ℝ) = 1 / 2 := by norm_num
  rw [h5] <;> ring

/-- Anti-monotonicity of _root_.dyadicDelta: a ≤ b → δ_b ≤ δ_a. -/
lemma dyadicDelta_anti' (a b : ℕ) (h : a ≤ b) :
    _root_.dyadicDelta b ≤ _root_.dyadicDelta a := by
  simp only [_root_.dyadicDelta]
  have h3 : (b : ℝ) ≥ (a : ℝ) := by exact_mod_cast h
  have h4 : -(b : ℝ) ≤ -(a : ℝ) := by linarith
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h4

/-- From δ_{n_cfg} ≤ δ_n and δ_n < 2 * δ_{n_cfg}, deduce n_cfg ≤ n. -/
lemma ncfg_le_n_from_dyadic (n n_cfg : ℕ)
    (h1 : _root_.dyadicDelta n_cfg ≤ _root_.dyadicDelta n)
    (h2 : _root_.dyadicDelta n < 2 * _root_.dyadicDelta n_cfg)
    (h_step : ∀ k : ℕ, _root_.dyadicDelta (k + 1) = (1 / 2 : ℝ) * _root_.dyadicDelta k)
    (h_anti : ∀ a b : ℕ, a ≤ b → _root_.dyadicDelta b ≤ _root_.dyadicDelta a) :
    n_cfg ≤ n := by
  by_contra h
  have h3 : n + 1 ≤ n_cfg := by omega
  have h4 : _root_.dyadicDelta n_cfg ≤ _root_.dyadicDelta (n + 1) := h_anti (n + 1) n_cfg h3
  have h5 : _root_.dyadicDelta (n + 1) = (1 / 2 : ℝ) * _root_.dyadicDelta n := h_step n
  rw [h5] at h4
  have h_pos : 0 < _root_.dyadicDelta n := by
    simp only [_root_.dyadicDelta]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have h6 : 2 * _root_.dyadicDelta n_cfg ≤ _root_.dyadicDelta n := by
    calc 2 * _root_.dyadicDelta n_cfg
      ≤ 2 * ((1 / 2 : ℝ) * _root_.dyadicDelta n) := by gcongr
    _ = _root_.dyadicDelta n := by ring
  exact False.elim (not_lt.mpr h6 h2)

/-- From δ_{n_cfg} ≤ δ_n, deduce n ≤ n_cfg (using anti-monotonicity). -/
lemma n_le_ncfg_from_dyadic (n n_cfg : ℕ)
    (h1 : _root_.dyadicDelta n_cfg ≤ _root_.dyadicDelta n)
    (h_step : ∀ k : ℕ, _root_.dyadicDelta (k + 1) = (1 / 2 : ℝ) * _root_.dyadicDelta k)
    (h_anti : ∀ a b : ℕ, a ≤ b → _root_.dyadicDelta b ≤ _root_.dyadicDelta a) :
    n ≤ n_cfg := by
  by_contra h
  have h3 : n_cfg + 1 ≤ n := by omega
  have h4 : _root_.dyadicDelta n ≤ _root_.dyadicDelta (n_cfg + 1) := h_anti (n_cfg + 1) n h3
  have h5 : _root_.dyadicDelta (n_cfg + 1) = (1 / 2 : ℝ) * _root_.dyadicDelta n_cfg := h_step n_cfg
  rw [h5] at h4
  have h_pos : 0 < _root_.dyadicDelta n := by
    simp only [_root_.dyadicDelta]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have h_pos_cfg : 0 < _root_.dyadicDelta n_cfg := by
    simp only [_root_.dyadicDelta]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have h7 : _root_.dyadicDelta n < _root_.dyadicDelta n_cfg := by
    calc _root_.dyadicDelta n
      ≤ (1 / 2 : ℝ) * _root_.dyadicDelta n_cfg := h4
    _ < _root_.dyadicDelta n_cfg := by
      have h9 : (1 / 2 : ℝ) * _root_.dyadicDelta n_cfg < _root_.dyadicDelta n_cfg := by
        linarith [h_pos_cfg]
      exact h9
  have h10 : _root_.dyadicDelta n_cfg ≤ _root_.dyadicDelta n := h1
  linarith

/-- Helper: prove `4000 * 44^s ≤ δ_n^{-ε/2}` from `δ_n ≤ 4 * δA_tube`. -/
lemma tube_sset_absorb_helper (δ_n δA_tube ε s : ℝ)
    (hδ_n_pos : 0 < δ_n) (hδA_tube_pos : 0 < δA_tube)
    (hε_pos : 0 < ε) (hs_pos : 0 ≤ s) (hδ_n_le : δ_n ≤ 4 * δA_tube)
    (hδA_tube_def : δA_tube = (4000 * (44 : ℝ)^s)^(-2 / ε) / 4) :
    (4000 : ℝ) * 44^s ≤ Real.rpow δ_n (-ε / 2) := by
  have h11 : 0 < 4 * δA_tube := mul_pos (by norm_num) hδA_tube_pos
  have h_eps2_pos : 0 < ε / 2 := by linarith
  have h1 : Real.rpow δ_n (ε / 2) ≤ Real.rpow (4 * δA_tube) (ε / 2) :=
    Real.rpow_le_rpow (by linarith) hδ_n_le (by linarith)
  have h_pos1 : 0 < Real.rpow δ_n (ε / 2) := Real.rpow_pos_of_pos hδ_n_pos (ε / 2)
  have h_pos2 : 0 < Real.rpow (4 * δA_tube) (ε / 2) := Real.rpow_pos_of_pos h11 (ε / 2)
  have h12 : Real.rpow δ_n (-ε / 2) ≥ Real.rpow (4 * δA_tube) (-ε / 2) := by
    have h_exp : (-ε / 2) = -(ε / 2) := by ring
    have h2 : Real.rpow δ_n (-ε / 2) = (Real.rpow δ_n (ε / 2))⁻¹ := by
      rw [h_exp]
      simpa using Real.rpow_neg hδ_n_pos.le (ε / 2)
    have h3 : Real.rpow (4 * δA_tube) (-ε / 2) = (Real.rpow (4 * δA_tube) (ε / 2))⁻¹ := by
      rw [h_exp]
      simpa using Real.rpow_neg h11.le (ε / 2)
    rw [h2, h3]
    have h4 : (Real.rpow (4 * δA_tube) (ε / 2))⁻¹ ≤ (Real.rpow δ_n (ε / 2))⁻¹ := by
      gcongr <;> positivity
    exact h4
  have h_base_pos : 0 < (4000 * (44 : ℝ)^s) := by
    have h44_pos : 0 < (44 : ℝ)^s := Real.rpow_pos_of_pos (by norm_num) s
    exact mul_pos (by norm_num) h44_pos
  have h14 : 4 * δA_tube = (4000 * (44 : ℝ)^s)^(-2 / ε) := by
    calc 4 * δA_tube
      = 4 * (((4000 * (44 : ℝ)^s)^(-2 / ε)) / 4) := by rw [hδA_tube_def]
    _ = (4000 * (44 : ℝ)^s)^(-2 / ε) := by
      field_simp
      <;> ring
  have h13 : Real.rpow (4 * δA_tube) (-ε / 2) = (4000 : ℝ) * 44^s := by
    rw [h14]
    have h15 : Real.rpow (Real.rpow (4000 * (44 : ℝ)^s) (-2 / ε)) (-ε / 2) =
        (4000 * (44 : ℝ)^s) := by
      have h_rpow_mul : Real.rpow (Real.rpow (4000 * (44 : ℝ)^s) (-2 / ε)) (-ε / 2) =
          Real.rpow (4000 * (44 : ℝ)^s) ((-2 / ε) * (-ε / 2)) :=
        (Real.rpow_mul h_base_pos.le (-2 / ε) (-ε / 2)).symm
      rw [h_rpow_mul]
      have h16 : (-2 / ε) * (-ε / 2) = 1 := by
        field_simp [hε_pos.ne'] <;> ring
      rw [h16]
      simp
    simpa using h15
  rw [h13] at h12
  exact h12

/-- Helper: prove M % 2 = 0 from dyadic representation and lower bound.
    Extracted to avoid timeout in dense Real.rpow context. -/
lemma m_even_helper
    (M : ℕ) (δ_n δA s lam ρ_M e_max : ℝ)
    (hM_dyadic : ∃ k : ℕ, M = 2 ^ k)
    (hM_lower : (M : ℝ) ≥ δ_n ^ (-s + lam + ρ_M))
    (hδ_n_pos : 0 < δ_n)
    (hδ_n_lt_one : δ_n < 1)
    (hδA_pos : 0 < δA)
    (hδ_n_le_4δA : δ_n ≤ 4 * δA)
    (hδA_le_M : δA ≤ (1 / 4 : ℝ) * Real.rpow 2 (1 / e_max))
    (h_exponent_le : -s + lam + ρ_M ≤ e_max)
    (he_max_neg : e_max < 0) :
    M % 2 = 0 := by
  rcases hM_dyadic with ⟨k, hM_eq⟩
  set q : ℝ := -e_max with hq_def
  have hq_pos : 0 < q := by linarith
  have h4δA_le : 4 * δA ≤ Real.rpow 2 (-1 / q) := by
    have h2 : 4 * ((1 / 4 : ℝ) * Real.rpow 2 (1 / e_max)) = Real.rpow 2 (1 / e_max) := by ring
    have h3 : (1 / e_max : ℝ) = -1 / q := by
      simp [hq_def] <;> ring
    calc 4 * δA ≤ 4 * ((1 / 4 : ℝ) * Real.rpow 2 (1 / e_max)) := by gcongr
      _ = Real.rpow 2 (1 / e_max) := h2
      _ = Real.rpow 2 (-1 / q) := by rw [h3]
  have h_main1 : (4 * δA) ^ q ≤ 1 / 2 := by
    have h_pos4 : 0 < 4 * δA := by positivity
    have h3 : (4 * δA) ^ q ≤ (Real.rpow 2 (-1 / q)) ^ q :=
      Real.rpow_le_rpow h_pos4.le h4δA_le hq_pos.le
    have h4 : (Real.rpow 2 (-1 / q)) ^ q = 1 / 2 := by
      have h_two_nonneg : 0 ≤ (2 : ℝ) := by norm_num
      have h41 : Real.rpow (Real.rpow 2 (-1 / q)) q = Real.rpow 2 ((-1 / q) * q) :=
        (Real.rpow_mul h_two_nonneg (-1 / q) q).symm
      have h42 : (-1 / q) * q = -1 := by
        field_simp [hq_pos.ne'] <;> ring
      calc (Real.rpow 2 (-1 / q)) ^ q
        = Real.rpow (Real.rpow 2 (-1 / q)) q := by rfl
      _ = Real.rpow 2 ((-1 / q) * q) := h41
      _ = Real.rpow 2 (-1) := by rw [h42]
      _ = 1 / 2 := by norm_num
    rw [h4] at h3
    exact h3
  have hδ_n_q_le : δ_n ^ q ≤ (4 * δA) ^ q :=
    Real.rpow_le_rpow hδ_n_pos.le hδ_n_le_4δA hq_pos.le
  have hδ_n_q_le_half : δ_n ^ q ≤ 1 / 2 := by
    calc δ_n ^ q ≤ (4 * δA) ^ q := hδ_n_q_le
         _ ≤ 1 / 2 := h_main1
  have hδ_n_e_max_ge2 : δ_n ^ e_max ≥ 2 := by
    have h5 : δ_n ^ e_max = 1 / (δ_n ^ q) := by
      have h6 : e_max = -q := by simp [hq_def] <;> ring
      rw [h6]
      rw [Real.rpow_neg hδ_n_pos.le q] <;> ring
    rw [h5]
    have h7 : 0 < δ_n ^ q := by positivity
    have h8 : 1 / (δ_n ^ q) ≥ 2 := by
      calc 1 / (δ_n ^ q) ≥ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le h7 hδ_n_q_le_half
           _ = 2 := by norm_num
    exact h8
  have h_main3 : δ_n ^ e_max ≤ δ_n ^ (-s + lam + ρ_M) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_n_pos hδ_n_lt_one.le h_exponent_le
  have hM_ge2 : (M : ℝ) ≥ 2 := by
    calc (M : ℝ) ≥ δ_n ^ (-s + lam + ρ_M) := hM_lower
         _ ≥ δ_n ^ e_max := h_main3
         _ ≥ 2 := hδ_n_e_max_ge2
  have hk_pos : 1 ≤ k := by
    by_contra h
    have h' : k = 0 := by omega
    rw [h'] at hM_eq
    have hM1 : (M : ℝ) = 1 := by exact_mod_cast hM_eq
    have h_cont : (M : ℝ) ≥ 2 := hM_ge2
    rw [hM1] at h_cont
    norm_num at h_cont
  rw [hM_eq]
  have h10 : 2 ∣ 2 ^ k := by
    apply dvd_pow_self
    <;> omega
  exact Nat.mod_eq_zero_of_dvd h10

/-- Helper: prove M/2 ≥ Δ^{-2s+2ε} from M lower bound.
    Extracted to avoid timeout in dense Real.rpow context. -/
lemma m_fine_lower_helper
    (M : ℕ) (δ_n Δ s ε lam ρ_M : ℝ)
    (hlam : lam = ε / 2)
    (hM_lower : (M : ℝ) ≥ δ_n ^ (-s + lam + ρ_M))
    (hδ_n_eq2 : δ_n = Δ ^ 2)
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_one : Δ < 1)
    (hε_pos : 0 < ε)
    (hρ_M_le : ρ_M ≤ ε / 20)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100) :
    (M : ℝ) / 2 ≥ Real.rpow Δ (-2 * s + 2 * ε) := by
  have h1 : (M : ℝ) ≥ Real.rpow Δ (-2 * s + ε + 2 * ρ_M) := by
    have h_exp : Real.rpow δ_n (-s + lam + ρ_M) =
        Real.rpow Δ (-2 * s + ε + 2 * ρ_M) := by
      have hlam' : -s + lam + ρ_M = -s + ε / 2 + ρ_M := by rw [hlam] <;> ring
      rw [hlam']
      rw [hδ_n_eq2]
      have h3 : (Δ ^ 2 : ℝ) = Real.rpow Δ (2 : ℝ) := (Real.rpow_natCast Δ 2).symm
      rw [h3]
      have h4 : Real.rpow (Real.rpow Δ (2 : ℝ)) (-s + ε / 2 + ρ_M) =
          Real.rpow Δ ((2 : ℝ) * (-s + ε / 2 + ρ_M)) :=
        (Real.rpow_mul hΔ_pos.le (2 : ℝ) (-s + ε / 2 + ρ_M)).symm
      rw [h4]
      have h5 : (2 : ℝ) * (-s + ε / 2 + ρ_M) = -2 * s + ε + 2 * ρ_M := by ring
      rw [h5]
    have hM_lower' : (M : ℝ) ≥ Real.rpow δ_n (-s + lam + ρ_M) := hM_lower
    rw [h_exp] at hM_lower'
    exact hM_lower'
  have h4 : 2 * ρ_M - ε ≤ -9 * ε / 10 := by linarith
  have h5 : Real.rpow Δ (2 * ρ_M - ε) ≥ Real.rpow Δ (-9 * ε / 10) :=
    Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h4
  have h_small9 : Real.rpow Δ (9 * ε / 10) ≤ 1 / 2 := by
    have h6 : 9 * ε / 10 ≥ ε / 4 := by linarith
    have h7 : Real.rpow Δ (9 * ε / 10) ≤ Real.rpow Δ (ε / 4) :=
      Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h6
    calc Real.rpow Δ (9 * ε / 10)
      ≤ Real.rpow Δ (ε / 4) := h7
    _ ≤ 1 / 100 := h_small
    _ ≤ 1 / 2 := by norm_num
  have h_pos9 : 0 < Real.rpow Δ (9 * ε / 10) := Real.rpow_pos_of_pos hΔ_pos (9 * ε / 10)
  have h_neg : Real.rpow Δ (-9 * ε / 10) = (Real.rpow Δ (9 * ε / 10))⁻¹ := by
    have h9 : Real.rpow Δ (-(9 * ε / 10)) = (Real.rpow Δ (9 * ε / 10))⁻¹ :=
      Real.rpow_neg (by linarith) (9 * ε / 10)
    have h10 : -9 * ε / 10 = -(9 * ε / 10) := by ring
    rw [h10]; exact h9
  have h7 : Real.rpow Δ (-9 * ε / 10) ≥ 2 := by
    rw [h_neg]
    have h12 : Real.rpow Δ (9 * ε / 10) ≤ 1 / 2 := h_small9
    have h13 : (Real.rpow Δ (9 * ε / 10))⁻¹ ≥ 2 := by
      have h14 : 0 < Real.rpow Δ (9 * ε / 10) := h_pos9
      have h15 : (Real.rpow Δ (9 * ε / 10))⁻¹ ≥ (1 / 2 : ℝ)⁻¹ := by gcongr
      have h16 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
      rw [h16] at h15
      exact h15
    exact h13
  have h11 : Real.rpow Δ (2 * ρ_M - ε) ≥ 2 := by
    calc Real.rpow Δ (2 * ρ_M - ε)
      ≥ Real.rpow Δ (-9 * ε / 10) := h5
    _ ≥ 2 := h7
  have h13 : Real.rpow Δ (-2 * s + ε + 2 * ρ_M) =
      Real.rpow Δ (-2 * s + 2 * ε) * Real.rpow Δ (2 * ρ_M - ε) := by
    have h14 : Real.rpow Δ ((-2 * s + 2 * ε) + (2 * ρ_M - ε)) =
        Real.rpow Δ (-2 * s + 2 * ε) * Real.rpow Δ (2 * ρ_M - ε) :=
      Real.rpow_add hΔ_pos (-2 * s + 2 * ε) (2 * ρ_M - ε)
    have h15 : (-2 * s + 2 * ε) + (2 * ρ_M - ε) = -2 * s + ε + 2 * ρ_M := by ring
    rw [h15] at h14
    exact h14
  rw [h13] at h1
  have h16 : 0 ≤ Real.rpow Δ (-2 * s + 2 * ε) := Real.rpow_nonneg (by linarith) _
  have h17 : (M : ℝ) ≥ 2 * Real.rpow Δ (-2 * s + 2 * ε) := by
    calc (M : ℝ)
      ≥ Real.rpow Δ (-2 * s + 2 * ε) * Real.rpow Δ (2 * ρ_M - ε) := h1
    _ ≥ Real.rpow Δ (-2 * s + 2 * ε) * 2 := by gcongr
    _ = 2 * Real.rpow Δ (-2 * s + 2 * ε) := by ring
  linarith

/-- Helper: prove M ≤ Δ^{-2s-ε} from M upper bound.
    Extracted to avoid timeout in dense Real.rpow context. -/
lemma m_fine_upper_helper
    (M : ℕ) (δ_n Δ s ε : ℝ)
    (hM_upper : (M : ℝ) ≤ 28 * Real.rpow δ_n (-s))
    (hδ_n_eq2 : δ_n = Δ ^ 2)
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_one : Δ < 1)
    (hε_pos : 0 < ε)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100) :
    (M : ℝ) ≤ Real.rpow Δ (-2 * s - ε) := by
  have h1 : (M : ℝ) ≤ 28 * Real.rpow δ_n (-s) := hM_upper
  have h2 : Real.rpow δ_n (-s) = Real.rpow Δ (-2 * s) := by
    rw [hδ_n_eq2]
    have h4 : Real.rpow (Δ ^ 2) (-s) = Real.rpow Δ (-2 * s) := by
      have h3 : (Δ ^ 2 : ℝ) = Real.rpow Δ (2 : ℝ) := (Real.rpow_natCast Δ 2).symm
      rw [h3]
      have h_rpow : Real.rpow (Real.rpow Δ (2 : ℝ)) (-s) = Real.rpow Δ ((2 : ℝ) * (-s)) :=
        (Real.rpow_mul hΔ_pos.le (2 : ℝ) (-s)).symm
      rw [h_rpow]
      have h_exp : (2 : ℝ) * (-s) = -2 * s := by ring
      rw [h_exp]
    exact h4
  rw [h2] at h1
  have h5 : (28 : ℝ) ≤ Real.rpow Δ (-ε) := by
    have h6 : Real.rpow Δ ε ≤ 1 / 28 := by
      have h7 : Real.rpow Δ ε ≤ Real.rpow Δ (ε / 4) :=
        Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le (by linarith)
      have h8 : Real.rpow Δ (ε / 4) ≤ 1 / 100 := h_small
      have h9 : Real.rpow Δ ε ≤ 1 / 100 := le_trans h7 h8
      have h10 : (1 / 100 : ℝ) ≤ 1 / 28 := by norm_num
      exact le_trans h9 h10
    have h10 : Real.rpow Δ (-ε) = (Real.rpow Δ ε)⁻¹ := by
      exact Real.rpow_neg hΔ_pos.le ε
    rw [h10]
    have h11 : 0 < Real.rpow Δ ε := Real.rpow_pos_of_pos hΔ_pos ε
    have h12 : (Real.rpow Δ ε)⁻¹ ≥ (1 / 28 : ℝ)⁻¹ := by gcongr
    have h13 : (1 / 28 : ℝ)⁻¹ = 28 := by norm_num
    rw [h13] at h12
    exact h12
  calc (M : ℝ)
    ≤ 28 * Real.rpow Δ (-2 * s) := h1
  _ ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-2 * s) := by
    gcongr <;> linarith
  _ = Real.rpow Δ (-2 * s - ε) := by
    have h_sum := Real.rpow_add hΔ_pos (-ε) (-2 * s)
    have h_exp : (-ε) + (-2 * s) = -2 * s - ε := by ring
    rw [h_exp] at h_sum
    exact h_sum.symm

/-- Helper: scale transfer exponent inequality.
    Given δ_n ≤ 4δ and δ_n^{-ρ_scale} ≥ 10000 · 81 · 4^{εA},
    prove δ^{-a} ≤ δ_n^{-(a+ρ_scale)} for 0 ≤ a ≤ 3. -/
lemma scale_transfer_exp_helper (δ δ_n ρ_scale εA : ℝ)
    (hδ_pos : 0 < δ) (hδ_n_pos : 0 < δ_n)
    (hδ_n_le_4δ : δ_n ≤ 4 * δ)
    (hεA_pos : 0 < εA)
    (h_scale_absorb : Real.rpow δ_n (-ρ_scale) ≥ 10000 * 81 * (4 : ℝ)^εA) :
    ∀ (a : ℝ), 0 ≤ a → a ≤ 3 →
      Real.rpow δ (-a) ≤ Real.rpow δ_n (-(a + ρ_scale)) := by
  intro a ha_nonneg ha_le3
  have h1 : Real.rpow δ_n (-(a + ρ_scale)) =
      Real.rpow δ_n (-a) * Real.rpow δ_n (-ρ_scale) := by
    have h_sum : -(a + ρ_scale) = (-a) + (-ρ_scale) := by ring
    rw [h_sum]
    exact Real.rpow_add hδ_n_pos (-a) (-ρ_scale)
  rw [h1]
  have h2 : δ_n / 4 ≤ δ := by linarith
  have h2pos : 0 < δ_n / 4 := by positivity
  have h3 : Real.rpow (δ_n / 4) a ≤ Real.rpow δ a :=
    Real.rpow_le_rpow (by positivity) h2 ha_nonneg
  have h4 : Real.rpow δ (-a) ≤ Real.rpow (δ_n / 4) (-a) := by
    have h5 : Real.rpow δ (-a) = (Real.rpow δ a)⁻¹ := by
      rw [show (-a) = -(a) from by ring]
      exact Real.rpow_neg hδ_pos.le a
    have h6 : Real.rpow (δ_n / 4) (-a) = (Real.rpow (δ_n / 4) a)⁻¹ := by
      rw [show (-a) = -(a) from by ring]
      exact Real.rpow_neg h2pos.le a
    rw [h5, h6]
    have hpos1 : 0 < Real.rpow δ a := Real.rpow_pos_of_pos hδ_pos a
    have hpos2 : 0 < Real.rpow (δ_n / 4) a := Real.rpow_pos_of_pos h2pos a
    gcongr
  have h5 : Real.rpow (δ_n / 4) (-a) = (4 : ℝ)^a * Real.rpow δ_n (-a) := by
    have h51 : (δ_n / 4 : ℝ) = δ_n * (4 : ℝ)⁻¹ := by ring
    rw [h51]
    have h52 : Real.rpow (δ_n * (4 : ℝ)⁻¹) (-a) =
        Real.rpow δ_n (-a) * Real.rpow ((4 : ℝ)⁻¹) (-a) :=
      Real.mul_rpow hδ_n_pos.le (by positivity)
    rw [h52]
    have h53 : Real.rpow ((4 : ℝ)⁻¹) (-a) = (4 : ℝ)^a := by
      have h54 : (4 : ℝ)⁻¹ = Real.rpow 4 (-1 : ℝ) := by
        simp [Real.rpow_neg_one] <;> ring
      rw [h54]
      have h55 : Real.rpow (Real.rpow 4 (-1 : ℝ)) (-a) =
          Real.rpow 4 ((-1 : ℝ) * (-a)) :=
        (Real.rpow_mul (by norm_num) (-1 : ℝ) (-a)).symm
      rw [h55]
      have h56 : (-1 : ℝ) * (-a) = a := by ring
      rw [h56] <;> rfl
    rw [h53] <;> ring
  rw [h5] at h4
  have h6 : (4 : ℝ)^(-a) * Real.rpow δ (-a) ≤ Real.rpow δ_n (-a) := by
    have h7 : (4 : ℝ)^(-a) * Real.rpow δ (-a) ≤
        (4 : ℝ)^(-a) * ((4 : ℝ)^a * Real.rpow δ_n (-a)) := by gcongr
    have h8 : (4 : ℝ)^(-a) * (4 : ℝ)^a = 1 := by
      have h9 : (4 : ℝ)^(-a) * (4 : ℝ)^a = (4 : ℝ)^((-a) + a) :=
        (Real.rpow_add (by norm_num) (-a) a).symm
      rw [h9]
      have h10 : (-a) + a = 0 := by ring
      rw [h10]
      simp
    have h9 : (4 : ℝ)^(-a) * ((4 : ℝ)^a * Real.rpow δ_n (-a)) = Real.rpow δ_n (-a) := by
      rw [← mul_assoc, h8, one_mul]
    rw [h9] at h7
    exact h7
  have h7 : Real.rpow δ_n (-ρ_scale) ≥ (4 : ℝ)^a := by
    have h8 : (4 : ℝ)^εA ≥ 1 := by
      have h9 : (4 : ℝ)^(0 : ℝ) ≤ (4 : ℝ)^εA :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
      simpa using h9
    have h10 : 10000 * 81 * (4 : ℝ)^εA ≥ 64 := by
      have h_pos : 0 ≤ (10000 * 81 : ℝ) := by norm_num
      have h11 : (10000 * 81 : ℝ) ≤ (10000 * 81 : ℝ) * (4 : ℝ)^εA := by
        simpa [mul_one] using mul_le_mul_of_nonneg_left h8 h_pos
      norm_num at h11 ⊢ <;> linarith
    have h12 : (4 : ℝ)^a ≤ 64 := by
      have h13 : (4 : ℝ)^a ≤ (4 : ℝ)^(3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) ha_le3
      have h14 : (4 : ℝ)^(3 : ℝ) = 64 := by norm_num
      rw [h14] at h13; exact h13
    linarith [h_scale_absorb]
  have h8 : (4 : ℝ)^(-a) * Real.rpow δ_n (-ρ_scale) ≥ 1 := by
    have h9 : (4 : ℝ)^(-a) * Real.rpow δ_n (-ρ_scale) ≥
        (4 : ℝ)^(-a) * (4 : ℝ)^a := by gcongr
    have h10 : (4 : ℝ)^(-a) * (4 : ℝ)^a = 1 := by
      have h11 : (4 : ℝ)^(-a) * (4 : ℝ)^a = (4 : ℝ)^((-a) + a) :=
        (Real.rpow_add (by norm_num) (-a) a).symm
      rw [h11]
      have h12 : (-a) + a = 0 := by ring
      rw [h12] <;> simp
    linarith
  have h9 : 0 ≤ Real.rpow δ (-a) := Real.rpow_nonneg hδ_pos.le _
  calc Real.rpow δ (-a)
    ≤ Real.rpow δ (-a) * ((4 : ℝ)^(-a) * Real.rpow δ_n (-ρ_scale)) :=
      le_mul_of_one_le_right h9 h8
  _ = (4 : ℝ)^(-a) * Real.rpow δ (-a) * Real.rpow δ_n (-ρ_scale) := by ring
  _ ≤ Real.rpow δ_n (-a) * Real.rpow δ_n (-ρ_scale) := by
    have h12 : 0 ≤ Real.rpow δ_n (-ρ_scale) := Real.rpow_nonneg hδ_n_pos.le _
    exact mul_le_mul_of_nonneg_right h6 h12

/-- Helper: `(Δ^2)^y = Δ^(2*y)` for `Δ > 0`. -/
lemma rpow_square_identity (Δ : ℝ) (hΔ_pos : 0 < Δ) (y : ℝ) :
    Real.rpow (Δ^2) y = Real.rpow Δ (2 * y) := by
  have h1 : (Δ^2 : ℝ) = Real.rpow Δ (2 : ℝ) := by
    have h11 : Real.rpow Δ (2 : ℝ) = Δ^2 := Real.rpow_two Δ
    exact h11.symm
  rw [h1]
  have h2 : Real.rpow (Real.rpow Δ (2 : ℝ)) y = Real.rpow Δ ((2 : ℝ) * y) :=
    (Real.rpow_mul hΔ_pos.le (2 : ℝ) y).symm
  exact h2

/-- Numerical bound for h_absorb_sset:
    `25 * 625 * 2^u * δ_n^(-ρ_mass) * δ_n^(-εA_int) ≤ δ_n^(-ε)`.
    Extracted as a standalone lemma to avoid tactic timeouts in dense
    Real.rpow contexts. -/
lemma absorb_sset_lemma (δ_n u ε ρ_mass εA_int : ℝ)
    (hδ_n_pos : 0 < δ_n)
    (hδ_n_le_one : δ_n ≤ 1)
    (hu_two : u ≤ 2)
    (_hε_pos : 0 < ε)
    (h_sum_le : ρ_mass + εA_int ≤ ε / 2)
    (h_small : Real.rpow δ_n (ε / 8) ≤ 1 / 100) :
    (25 : ℝ) * 625 * (2 : ℝ)^u * Real.rpow δ_n (-ρ_mass) * Real.rpow δ_n (-εA_int) ≤
    Real.rpow δ_n (-ε) := by
  have h1 : (2 : ℝ)^u ≤ 4 := by
    have h11 : (1 : ℝ) < (2 : ℝ) := by norm_num
    have h12 : (2 : ℝ)^u ≤ (2 : ℝ)^(2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h11.le hu_two
    have h13 : (2 : ℝ)^(2 : ℝ) = 4 := by norm_num
    rw [h13] at h12; exact h12
  have h2 : (25 : ℝ) * 625 * (2 : ℝ)^u ≤ 62500 := by
    calc
      (25 : ℝ) * 625 * (2 : ℝ)^u ≤ 25 * 625 * 4 := by gcongr
      _ = 62500 := by norm_num
  have h3 : Real.rpow δ_n (-ρ_mass) * Real.rpow δ_n (-εA_int) =
      Real.rpow δ_n (-(ρ_mass + εA_int)) := by
    have h31 : Real.rpow δ_n ((-ρ_mass) + (-εA_int)) =
        Real.rpow δ_n (-ρ_mass) * Real.rpow δ_n (-εA_int) :=
      Real.rpow_add hδ_n_pos (-ρ_mass) (-εA_int)
    have h32 : (-ρ_mass) + (-εA_int) = -(ρ_mass + εA_int) := by ring
    rw [h32] at h31
    exact h31.symm
  have h41 : -ε / 2 ≤ -(ρ_mass + εA_int) := by linarith
  have h4 : Real.rpow δ_n (-(ρ_mass + εA_int)) ≤ Real.rpow δ_n (-ε / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_n_pos hδ_n_le_one h41
  have h51 : Real.rpow δ_n (-ε / 8) = (Real.rpow δ_n (ε / 8))⁻¹ := by
    have h_eq : -ε / 8 = -(ε / 8) := by ring
    rw [h_eq]
    exact Real.rpow_neg hδ_n_pos.le (ε / 8)
  have h5 : Real.rpow δ_n (-ε / 8) ≥ 100 := by
    rw [h51]
    have h52 : 0 < Real.rpow δ_n (ε / 8) := Real.rpow_pos_of_pos hδ_n_pos _
    have h53 : (Real.rpow δ_n (ε / 8))⁻¹ ≥ (1 / 100 : ℝ)⁻¹ := by gcongr
    simpa using h53
  have h61 : Real.rpow δ_n (-ε / 2) = (Real.rpow δ_n (-ε / 8)) ^ 4 := by
    have h_eq1 : -ε / 2 = (-ε / 8) + (-ε / 8) + (-ε / 8) + (-ε / 8) := by ring
    rw [h_eq1]
    simp [Real.rpow_add hδ_n_pos]
    ; ring
  have h6 : Real.rpow δ_n (-ε / 2) ≥ 62500 := by
    rw [h61]
    have h63 : (100 : ℝ) ≤ Real.rpow δ_n (-ε / 8) := h5
    have h64 : (100 : ℝ)^4 ≤ (Real.rpow δ_n (-ε / 8)) ^ 4 := by gcongr
    have h65 : (100 : ℝ)^4 = (100000000 : ℝ) := by norm_num
    rw [h65] at h64
    linarith
  have h7 : 0 ≤ Real.rpow δ_n (-ε / 2) := Real.rpow_nonneg hδ_n_pos.le _
  have h8 : 62500 * Real.rpow δ_n (-ε / 2) ≤
      Real.rpow δ_n (-ε / 2) * Real.rpow δ_n (-ε / 2) :=
    mul_le_mul_of_nonneg_right h6 h7
  have h9 : Real.rpow δ_n (-ε / 2) * Real.rpow δ_n (-ε / 2) = Real.rpow δ_n (-ε) := by
    have h91 : Real.rpow δ_n ((-ε / 2) + (-ε / 2)) =
        Real.rpow δ_n (-ε / 2) * Real.rpow δ_n (-ε / 2) :=
      Real.rpow_add hδ_n_pos (-ε / 2) (-ε / 2)
    have h92 : (-ε / 2) + (-ε / 2) = -ε := by ring
    rw [h92] at h91
    exact h91.symm
  have h10 : 0 ≤ Real.rpow δ_n (-(ρ_mass + εA_int)) := Real.rpow_nonneg hδ_n_pos.le _
  calc
    (25 : ℝ) * 625 * (2 : ℝ)^u * Real.rpow δ_n (-ρ_mass) * Real.rpow δ_n (-εA_int)
      = (25 : ℝ) * 625 * (2 : ℝ)^u *
          (Real.rpow δ_n (-ρ_mass) * Real.rpow δ_n (-εA_int)) := by ring
    _ = (25 : ℝ) * 625 * (2 : ℝ)^u * Real.rpow δ_n (-(ρ_mass + εA_int)) := by rw [h3]
    _ ≤ 62500 * Real.rpow δ_n (-(ρ_mass + εA_int)) := by
      exact mul_le_mul_of_nonneg_right h2 h10
    _ ≤ 62500 * Real.rpow δ_n (-ε / 2) := by
      exact mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ ≤ Real.rpow δ_n (-ε / 2) * Real.rpow δ_n (-ε / 2) := h8
    _ = Real.rpow δ_n (-ε) := h9

/-- Helper: δ_n = Δ^2 and 0 < Δ < 1 implies δ_n ≤ 1. -/
lemma delta_n_le_one_lemma (δ_n Δ : ℝ) (hδ_n_eq2 : δ_n = Δ^2)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1) : δ_n ≤ 1 := by
  rw [hδ_n_eq2]
  have h2 : 0 ≤ Δ := hΔ_pos.le
  have h3 : Δ ≤ 1 := hΔ_lt_one.le
  calc Δ^2 ≤ 1^2 := by gcongr
    _ = 1 := by norm_num

/-- Helper: Real.rpow δ_n (ε/8) ≤ 1/100 from Real.rpow Δ (ε/4) ≤ 1/100. -/
lemma small8_lemma (δ_n Δ ε : ℝ) (hδ_n_eq2 : δ_n = Δ^2)
    (hΔ_pos : 0 < Δ) (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100) :
    Real.rpow δ_n (ε / 8) ≤ 1 / 100 := by
  have h12 : δ_n = Δ ^ 2 := hδ_n_eq2
  rw [h12]
  have h13 : Real.rpow (Δ ^ 2) (ε / 8) = Real.rpow Δ (ε / 4) := by
    have h14 := rpow_square_identity Δ hΔ_pos (ε / 8)
    have h15 : (2 : ℝ) * (ε / 8) = ε / 4 := by ring
    rw [h14, h15]
  rw [h13]
  exact h_small_eps

/-- Helper: Real.rpow Δ (ε/20) ≤ 1/2 from Real.rpow Δ (ε/4) ≤ 1/100. -/
lemma small2_lemma (Δ ε : ℝ) (hΔ_pos : 0 < Δ)
    (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100) :
    Real.rpow Δ (ε / 20) ≤ 1 / 2 := by
  have h1 : Real.rpow Δ (ε / 20) = (Real.rpow Δ (ε / 4)) ^ (1 / 5 : ℝ) := by
    have h_eq : (ε / 4) * (1 / 5 : ℝ) = ε / 20 := by ring
    have h_mul : Real.rpow Δ ((ε / 4) * (1 / 5 : ℝ)) =
        (Real.rpow Δ (ε / 4)) ^ (1 / 5 : ℝ) := Real.rpow_mul hΔ_pos.le (ε / 4) (1 / 5 : ℝ)
    rw [h_eq] at h_mul
    exact h_mul
  rw [h1]
  have h4 : Real.rpow Δ (ε / 4) ≤ 1 / 100 := h_small_eps
  have h5 : 0 ≤ Real.rpow Δ (ε / 4) := Real.rpow_nonneg hΔ_pos.le _
  have h6 : (Real.rpow Δ (ε / 4)) ^ (1 / 5 : ℝ) ≤ (1 / 100 : ℝ) ^ (1 / 5 : ℝ) := by gcongr
  have h7 : (1 / 100 : ℝ) ^ (1 / 5 : ℝ) ≤ 1 / 2 := by
    have h8 : (1 / 100 : ℝ) ≤ (1 / 2 : ℝ) ^ (5 : ℝ) := by norm_num
    have h9 : 0 ≤ (1 / 2 : ℝ) := by norm_num
    have h10 : (1 / 100 : ℝ) ^ (1 / 5 : ℝ) ≤ ((1 / 2 : ℝ) ^ (5 : ℝ)) ^ (1 / 5 : ℝ) := by gcongr
    have h11 : ((1 / 2 : ℝ) ^ (5 : ℝ)) ^ (1 / 5 : ℝ) = (1 / 2 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num) (5 : ℝ) (1 / 5 : ℝ)] <;> norm_num
    rw [h11] at h10; exact h10
  exact le_trans h6 h7

/-- Helper: Real.rpow Δ (3*ε/10) ≤ 1/2 from Real.rpow Δ (ε/4) ≤ 1/100. -/
lemma small3_lemma (Δ ε : ℝ) (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hε_pos : 0 < ε) (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100) :
    Real.rpow Δ (3 * ε / 10) ≤ 1 / 2 := by
  have h1 : ε / 4 ≤ 3 * ε / 10 := by
    have h2 : 0 < ε := hε_pos
    linarith
  have h2 : Real.rpow Δ (3 * ε / 10) ≤ Real.rpow Δ (ε / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h1
  have h3 : Real.rpow Δ (ε / 4) ≤ 1 / 100 := h_small_eps
  have h4 : (1 / 100 : ℝ) ≤ 1 / 2 := by norm_num
  exact le_trans (le_trans h2 h3) h4

/-- B1 threshold arithmetic: from budget constraints and δA threshold,
    derive the three facts needed by `b1_assembly`.

    Given `ρ_mass ≤ reserved_budget`, `εA = ε/50`, `reserved_budget = ε/20`,
    and the δA_B1 threshold constraint, returns:
      (1) `2 * εA + 2 * ρ_mass < ε / 5`
      (2) `δA ≤ (1/4) * C_B1 ^ (2 / e_B1)` (passed through from input)
      (3) `Δ ^ (ε/5 - 2*εA - 2*ρ_mass) ≤ C_B1` -/
lemma b1_threshold_arith
    (ε εA ρ_mass reserved_budget Δ δA C_B1 e_B1 : ℝ)
    (hε_pos : 0 < ε)
    (hεA_eq : εA = ε / 50)
    (hreserved_eq : reserved_budget = ε / 20)
    (hρ_mass_le : ρ_mass ≤ reserved_budget)
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_one : Δ < 1)
    (he_B1_pos : 0 < e_B1)
    (he_B1_eq : e_B1 = ε / 5 - 2 * εA - 2 * reserved_budget)
    (hC_B1_pos : 0 < C_B1)
    (hδA_nonneg : 0 ≤ δA)
    (hδA_le_B1 : δA ≤ (1 / 4 : ℝ) * C_B1 ^ (2 / e_B1))
    (hΔ_le_2sqrtδA : Δ ≤ 2 * Real.sqrt δA) :
    (2 * εA + 2 * ρ_mass < ε / 5) ∧
    (δA ≤ (1 / 4 : ℝ) * C_B1 ^ (2 / e_B1)) ∧
    (Real.rpow Δ (ε / 5 - 2 * εA - 2 * ρ_mass) ≤ C_B1) := by
  -- ========================================================================
  -- Fact 1: 2 * εA + 2 * ρ_mass < ε / 5
  -- ========================================================================
  have h_exponent_eps5 : 2 * εA + 2 * ρ_mass < ε / 5 := by
    have h1 : ρ_mass ≤ ε / 20 := by
      calc ρ_mass ≤ reserved_budget := hρ_mass_le
           _ = ε / 20 := by rw [hreserved_eq]
    rw [hεA_eq]
    linarith

  -- Let e be the actual exponent with ρ_mass
  let e : ℝ := ε / 5 - 2 * εA - 2 * ρ_mass

  -- ========================================================================
  -- Fact 3: Δ^e ≤ C_B1
  -- ========================================================================

  -- Step 1: e ≥ e_B1 (since ρ_mass ≤ reserved_budget)
  have h_e_ge : e_B1 ≤ e := by
    dsimp only [e]
    rw [he_B1_eq]
    linarith [hρ_mass_le]

  -- Step 2: Δ^e ≤ Δ^e_B1 (rpow antitone for 0 < Δ < 1)
  have h4 : Real.rpow Δ e ≤ Real.rpow Δ e_B1 :=
    Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h_e_ge

  -- Step 3: Δ ≤ C_B1^(1/e_B1)
  have h_pos_CB1_rpow : 0 ≤ (1 / 2 : ℝ) * C_B1 ^ (1 / e_B1) := by positivity
  have h_sqrt_eq : Real.sqrt ((1 / 4 : ℝ) * C_B1 ^ (2 / e_B1)) =
      (1 / 2 : ℝ) * C_B1 ^ (1 / e_B1) := by
    have h8 : (1 / 4 : ℝ) * C_B1 ^ (2 / e_B1) =
        ((1 / 2 : ℝ) * C_B1 ^ (1 / e_B1)) ^ 2 := by
      have h9 : C_B1 ^ (2 / e_B1) = (C_B1 ^ (1 / e_B1)) ^ 2 := by
        have h91 : (2 / e_B1) = (1 / e_B1) + (1 / e_B1) := by ring
        rw [h91, Real.rpow_add hC_B1_pos] <;> ring
      rw [h9] <;> ring
    rw [h8]
    rw [Real.sqrt_sq h_pos_CB1_rpow]
  have hΔ_le_CB1 : Δ ≤ C_B1 ^ (1 / e_B1) := by
    calc Δ
      ≤ 2 * Real.sqrt δA := hΔ_le_2sqrtδA
    _ ≤ 2 * Real.sqrt ((1 / 4 : ℝ) * C_B1 ^ (2 / e_B1)) := by
      gcongr
      <;> linarith
    _ = 2 * ((1 / 2 : ℝ) * C_B1 ^ (1 / e_B1)) := by rw [h_sqrt_eq]
    _ = C_B1 ^ (1 / e_B1) := by ring

  -- Step 4: Δ^e_B1 ≤ C_B1 via log monotonicity
  have hlog1 : Real.log Δ ≤ Real.log (C_B1 ^ (1 / e_B1)) :=
    Real.log_le_log (by positivity) hΔ_le_CB1
  have hlog2 : Real.log (C_B1 ^ (1 / e_B1)) = (1 / e_B1) * Real.log C_B1 :=
    Real.log_rpow hC_B1_pos (1 / e_B1)
  have hlog3 : e_B1 * Real.log Δ ≤ Real.log C_B1 := by
    calc e_B1 * Real.log Δ
      ≤ e_B1 * Real.log (C_B1 ^ (1 / e_B1)) := by gcongr
    _ = e_B1 * ((1 / e_B1) * Real.log C_B1) := by rw [hlog2]
    _ = Real.log C_B1 := by field_simp [he_B1_pos.ne'] <;> ring
  have hlog4 : Real.log (Real.rpow Δ e_B1) = e_B1 * Real.log Δ :=
    Real.log_rpow hΔ_pos e_B1
  have hpos1 : 0 < Real.rpow Δ e_B1 := Real.rpow_pos_of_pos hΔ_pos e_B1
  have h12 : Real.rpow Δ e_B1 ≤ C_B1 := by
    have h : Real.log (Real.rpow Δ e_B1) ≤ Real.log C_B1 := by
      rw [hlog4]; exact hlog3
    exact (Real.log_le_log_iff hpos1 hC_B1_pos).mp h

  -- Step 5: combine Δ^e ≤ Δ^e_B1 ≤ C_B1
  have h13 : Real.rpow Δ e ≤ C_B1 := le_trans h4 h12

  exact ⟨h_exponent_eps5, hδA_le_B1, h13⟩

/-- Absorb `4 * log(3/Δ) + 1` into `Δ^(-3*ε)`. -/
lemma log_absorption_lemma
    (Δ ε δA : ℝ)
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_one : Δ < 1)
    (hε_pos : 0 < ε)
    (hδA_nonneg : 0 ≤ δA)
    (hΔ_le_2sqrtδA : Δ ≤ 2 * Real.sqrt δA)
    (hδA_le_log1 : δA ≤ (1 / 4 : ℝ) * (ε / (8 * (3 : ℝ)^ε))^(1 / ε))
    (hδA_le_log2 : δA ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ)^(2 / (3 * ε))) :
    4 * Real.log (3 / Δ) + 1 ≤ Real.rpow Δ (-3 * ε) := by
  have hε_ne : ε ≠ 0 := hε_pos.ne'
  set B1 : ℝ := ε / (8 * (3 : ℝ)^ε) with hB1_def
  set B2 : ℝ := (1 / 2 : ℝ) with hB2_def
  have hB1_nonneg : 0 ≤ B1 := by positivity
  have hB2_nonneg : 0 ≤ B2 := by norm_num

  -- ========================================================================
  -- Part A: Δ ≤ B1^(1/(2ε)), therefore Δ^(2ε) ≤ B1
  -- ========================================================================
  have h_sqrt_quarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [Real.sqrt_eq_cases] <;> norm_num

  have h_sqrt_B1 : Real.sqrt ((1 / 4 : ℝ) * B1^(1 / ε)) =
      (1 / 2 : ℝ) * B1^(1 / (2 * ε)) := by
    have h1 : Real.sqrt ((1 / 4 : ℝ) * B1^(1 / ε)) =
        Real.sqrt (1 / 4 : ℝ) * Real.sqrt (B1^(1 / ε)) := by
      rw [Real.sqrt_mul (by norm_num)]
    rw [h1, h_sqrt_quarter]
    have h2 : Real.sqrt (B1^(1 / ε)) = B1^(1 / (2 * ε)) := by
      have h3 : Real.sqrt (B1^(1 / ε)) = (B1^(1 / ε))^(1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow] <;> positivity
      rw [h3]
      have h4 : (B1^(1 / ε))^(1 / 2 : ℝ) = B1^((1 / ε) * (1 / 2 : ℝ)) := by
        exact (Real.rpow_mul hB1_nonneg (1 / ε) (1 / 2 : ℝ)).symm
      rw [h4]
      have h5 : (1 / ε) * (1 / 2 : ℝ) = 1 / (2 * ε) := by ring
      rw [h5]
    rw [h2] <;> ring

  have hΔ_le_B1 : Δ ≤ B1^(1 / (2 * ε)) := by
    calc Δ
      ≤ 2 * Real.sqrt δA := hΔ_le_2sqrtδA
    _ ≤ 2 * Real.sqrt ((1 / 4 : ℝ) * B1^(1 / ε)) := by
      gcongr <;> linarith [hδA_le_log1]
    _ = 2 * ((1 / 2 : ℝ) * B1^(1 / (2 * ε))) := by rw [h_sqrt_B1]
    _ = B1^(1 / (2 * ε)) := by ring

  have hΔ2ε : Real.rpow Δ (2 * ε) ≤ B1 := by
    have h10 : Real.rpow Δ (2 * ε) ≤ Real.rpow (B1^(1 / (2 * ε))) (2 * ε) :=
      Real.rpow_le_rpow (by positivity) hΔ_le_B1 (by positivity)
    have h11 : Real.rpow (B1^(1 / (2 * ε))) (2 * ε) = B1 := by
      have h12 : Real.rpow (B1^(1 / (2 * ε))) (2 * ε) =
          B1^((1 / (2 * ε)) * (2 * ε)) := by
        exact (Real.rpow_mul hB1_nonneg (1 / (2 * ε)) (2 * ε)).symm
      rw [h12]
      have h13 : (1 / (2 * ε)) * (2 * ε) = 1 := by
        field_simp [hε_ne] <;> ring
      rw [h13]
      simp
    rw [h11] at h10
    exact h10

  -- ========================================================================
  -- Part B: Δ ≤ B2^(1/(3ε)), therefore Δ^(3ε) ≤ B2 = 1/2
  -- ========================================================================
  have h_sqrt_B2 : Real.sqrt ((1 / 4 : ℝ) * B2^(2 / (3 * ε))) =
      (1 / 2 : ℝ) * B2^(1 / (3 * ε)) := by
    have h1 : Real.sqrt ((1 / 4 : ℝ) * B2^(2 / (3 * ε))) =
        Real.sqrt (1 / 4 : ℝ) * Real.sqrt (B2^(2 / (3 * ε))) := by
      rw [Real.sqrt_mul (by norm_num)]
    rw [h1, h_sqrt_quarter]
    have h2 : Real.sqrt (B2^(2 / (3 * ε))) = B2^(1 / (3 * ε)) := by
      have h3 : Real.sqrt (B2^(2 / (3 * ε))) = (B2^(2 / (3 * ε)))^(1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow] <;> positivity
      rw [h3]
      have h4 : (B2^(2 / (3 * ε)))^(1 / 2 : ℝ) = B2^((2 / (3 * ε)) * (1 / 2 : ℝ)) := by
        exact (Real.rpow_mul hB2_nonneg (2 / (3 * ε)) (1 / 2 : ℝ)).symm
      rw [h4]
      have h5 : (2 / (3 * ε)) * (1 / 2 : ℝ) = 1 / (3 * ε) := by ring
      rw [h5]
    rw [h2] <;> ring

  have hΔ_le_B2 : Δ ≤ B2^(1 / (3 * ε)) := by
    calc Δ
      ≤ 2 * Real.sqrt δA := hΔ_le_2sqrtδA
    _ ≤ 2 * Real.sqrt ((1 / 4 : ℝ) * B2^(2 / (3 * ε))) := by
      gcongr <;> linarith [hδA_le_log2]
    _ = 2 * ((1 / 2 : ℝ) * B2^(1 / (3 * ε))) := by rw [h_sqrt_B2]
    _ = B2^(1 / (3 * ε)) := by ring

  have hΔ3ε : Real.rpow Δ (3 * ε) ≤ 1 / 2 := by
    have h10 : Real.rpow Δ (3 * ε) ≤ Real.rpow (B2^(1 / (3 * ε))) (3 * ε) :=
      Real.rpow_le_rpow (by positivity) hΔ_le_B2 (by positivity)
    have h11 : Real.rpow (B2^(1 / (3 * ε))) (3 * ε) = B2 := by
      have h12 : Real.rpow (B2^(1 / (3 * ε))) (3 * ε) =
          B2^((1 / (3 * ε)) * (3 * ε)) := by
        exact (Real.rpow_mul hB2_nonneg (1 / (3 * ε)) (3 * ε)).symm
      rw [h12]
      have h13 : (1 / (3 * ε)) * (3 * ε) = 1 := by
        field_simp [hε_ne] <;> ring
      rw [h13]
      simp
    rw [h11] at h10
    simpa [hB2_def] using h10

  -- ========================================================================
  -- Part C: Combine via log inequality
  -- ========================================================================
  have hΔε_pos : 0 < Real.rpow Δ ε := Real.rpow_pos_of_pos hΔ_pos ε
  have hΔ3ε_pos : 0 < Real.rpow Δ (3 * ε) := Real.rpow_pos_of_pos hΔ_pos (3 * ε)
  have h3ε_rpow_pos : 0 < (3 : ℝ)^ε := by positivity

  -- (3/Δ)^ε = 3^ε / Δ^ε
  have h_rpow_div : Real.rpow (3 / Δ) ε = (3 : ℝ)^ε / Real.rpow Δ ε :=
    Real.div_rpow (by norm_num) hΔ_pos.le ε

  -- log(3/Δ) ≤ (3/Δ)^ε / ε
  have hlog : Real.log (3 / Δ) ≤ Real.rpow (3 / Δ) ε / ε :=
    Real.log_le_rpow_div (by positivity) hε_pos

  -- 4 * log(3/Δ) + 1 ≤ 4 * 3^ε / (ε * Δ^ε) + 1
  have h_bound1 : 4 * Real.log (3 / Δ) + 1 ≤
      4 * ((3 : ℝ)^ε / (ε * Real.rpow Δ ε)) + 1 := by
    have h : Real.log (3 / Δ) ≤ (3 : ℝ)^ε / (ε * Real.rpow Δ ε) := by
      calc Real.log (3 / Δ)
          ≤ Real.rpow (3 / Δ) ε / ε := hlog
        _ = ((3 : ℝ)^ε / Real.rpow Δ ε) / ε := by rw [h_rpow_div]
        _ = (3 : ℝ)^ε / (ε * Real.rpow Δ ε) := by ring
    linarith

  -- Δ^ε * Δ^(2ε) = Δ^(3ε)
  have h18 : Real.rpow Δ ε * Real.rpow Δ (2 * ε) = Real.rpow Δ (3 * ε) := by
    have h : Real.rpow Δ (ε + 2 * ε) = Real.rpow Δ ε * Real.rpow Δ (2 * ε) :=
      Real.rpow_add hΔ_pos ε (2 * ε)
    have h2 : ε + 2 * ε = 3 * ε := by ring
    rw [h2] at h
    exact h.symm

  -- 4 * 3^ε * Δ^(2ε) / ε + Δ^(3ε) ≤ 1
  have h_goal : 4 * (3 : ℝ)^ε * Real.rpow Δ (2 * ε) / ε + Real.rpow Δ (3 * ε) ≤ 1 := by
    have h_term1 : 4 * (3 : ℝ)^ε * Real.rpow Δ (2 * ε) / ε ≤ 1 / 2 := by
      calc 4 * (3 : ℝ)^ε * Real.rpow Δ (2 * ε) / ε
          ≤ 4 * (3 : ℝ)^ε * B1 / ε := by gcongr
        _ = 1 / 2 := by
          simp only [hB1_def]
          field_simp [hε_ne, h3ε_rpow_pos.ne'] <;> ring
    have h_term2 : Real.rpow Δ (3 * ε) ≤ 1 / 2 := hΔ3ε
    linarith

  -- (4 * 3^ε / (ε * Δ^ε) + 1) * Δ^(3ε) = 4 * 3^ε * Δ^(2ε) / ε + Δ^(3ε)
  have h_mult : (4 * ((3 : ℝ)^ε / (ε * Real.rpow Δ ε)) + 1) * Real.rpow Δ (3 * ε) =
      4 * (3 : ℝ)^ε * Real.rpow Δ (2 * ε) / ε + Real.rpow Δ (3 * ε) := by
    have h_distrib : (4 * ((3 : ℝ)^ε / (ε * Real.rpow Δ ε)) + 1) * Real.rpow Δ (3 * ε) =
        4 * (3 : ℝ)^ε / (ε * Real.rpow Δ ε) * Real.rpow Δ (3 * ε) + Real.rpow Δ (3 * ε) := by ring
    rw [h_distrib]
    have h_frac : 4 * (3 : ℝ)^ε / (ε * Real.rpow Δ ε) * Real.rpow Δ (3 * ε) =
        4 * (3 : ℝ)^ε * Real.rpow Δ (2 * ε) / ε := by
      have h9 : Real.rpow Δ (3 * ε) = Real.rpow Δ ε * Real.rpow Δ (2 * ε) := h18.symm
      rw [h9]
      field_simp [hΔε_pos.ne'] <;> ring
    rw [h_frac] <;> ring

  -- 4 * 3^ε / (ε * Δ^ε) + 1 ≤ (Δ^(3ε))⁻¹
  have h_bound2 : (4 * ((3 : ℝ)^ε / (ε * Real.rpow Δ ε)) + 1) ≤
      (Real.rpow Δ (3 * ε))⁻¹ := by
    have h_pos3 : 0 < Real.rpow Δ (3 * ε) := hΔ3ε_pos
    have h : (4 * ((3 : ℝ)^ε / (ε * Real.rpow Δ ε)) + 1) * Real.rpow Δ (3 * ε) ≤ 1 := by
      rw [h_mult]
      exact h_goal
    set X : ℝ := 4 * ((3 : ℝ)^ε / (ε * Real.rpow Δ ε)) + 1 with hX_def
    have h5 : X ≤ (Real.rpow Δ (3 * ε))⁻¹ := by
      have h6 : Real.rpow Δ (3 * ε) ≠ 0 := h_pos3.ne'
      have h_eq : X = (X * Real.rpow Δ (3 * ε)) / Real.rpow Δ (3 * ε) := by
        have h7 : (X * Real.rpow Δ (3 * ε)) / Real.rpow Δ (3 * ε) = X := by
          field_simp [h6] <;> ring
        exact h7.symm
      rw [h_eq]
      calc (X * Real.rpow Δ (3 * ε)) / Real.rpow Δ (3 * ε)
          ≤ 1 / Real.rpow Δ (3 * ε) := by gcongr
        _ = (Real.rpow Δ (3 * ε))⁻¹ := by simp [one_div]
    exact h5

  -- Δ^(-3ε) = (Δ^(3ε))⁻¹
  have h_rpow_neg : Real.rpow Δ (-3 * ε) = (Real.rpow Δ (3 * ε))⁻¹ := by
    have h9 : -3 * ε = -(3 * ε) := by ring
    rw [h9]
    exact Real.rpow_neg hΔ_pos.le (3 * ε)

  calc 4 * Real.log (3 / Δ) + 1
      ≤ 4 * ((3 : ℝ)^ε / (ε * Real.rpow Δ ε)) + 1 := h_bound1
    _ ≤ (Real.rpow Δ (3 * ε))⁻¹ := h_bound2
    _ = Real.rpow Δ (-3 * ε) := h_rpow_neg.symm

/-- Helper: `|center_q 0 - x 0| ≤ δ_n / 2` when `x ∈ q.toSet`. -/
lemma center_x_coord_bound {n : ℕ} {δ_n : ℝ}
    (h_eq_n : DiscretisedFurstenbergEstimate.dyadicDelta n = δ_n)
    (q : DiscretisedFurstenbergEstimate.DyadicSquare n)
    (x : EuclideanPlane) (hx : x ∈ q.toSet) :
    |(localSquareCenter q) 0 - x 0| ≤ δ_n / 2 := by
  have hcx : (localSquareCenter q) 0 = ((q.i : ℝ) + 1 / 2) * δ_n := by
    simp [localSquareCenter, h_eq_n] <;> ring
  have hxi1 : (q.i : ℝ) * δ_n ≤ x 0 := by
    have h : (q.i : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta n ≤ x 0 := hx.1
    rwa [h_eq_n] at h
  have hxi2 : x 0 < ((q.i : ℝ) + 1) * δ_n := by
    have h : x 0 < ((q.i : ℝ) + 1) * DiscretisedFurstenbergEstimate.dyadicDelta n := hx.2.1
    rwa [h_eq_n] at h
  rw [hcx]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Helper: `|center_q 1 - x 1| ≤ δ_n / 2` when `x ∈ q.toSet`. -/
lemma center_y_coord_bound {n : ℕ} {δ_n : ℝ}
    (h_eq_n : DiscretisedFurstenbergEstimate.dyadicDelta n = δ_n)
    (q : DiscretisedFurstenbergEstimate.DyadicSquare n)
    (x : EuclideanPlane) (hx : x ∈ q.toSet) :
    |(localSquareCenter q) 1 - x 1| ≤ δ_n / 2 := by
  have hcy : (localSquareCenter q) 1 = ((q.j : ℝ) + 1 / 2) * δ_n := by
    simp [localSquareCenter, h_eq_n] <;> ring
  have hyi1 : (q.j : ℝ) * δ_n ≤ x 1 := by
    have h : (q.j : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta n ≤ x 1 := hx.2.2.1
    rwa [h_eq_n] at h
  have hyi2 : x 1 < ((q.j : ℝ) + 1) * δ_n := by
    have h : x 1 < ((q.j : ℝ) + 1) * DiscretisedFurstenbergEstimate.dyadicDelta n := hx.2.2.2
    rwa [h_eq_n] at h
  rw [hcy]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Helper: distance from dyadic square center to any point in the square
    is at most √2 * δ_n / 2. -/
lemma square_center_dist_bound {n : ℕ} {δ_n : ℝ}
    (q : DiscretisedFurstenbergEstimate.DyadicSquare n)
    (x : EuclideanPlane) (hx : x ∈ q.toSet)
    (h_eq_n : DiscretisedFurstenbergEstimate.dyadicDelta n = δ_n) :
    ‖localSquareCenter q - x‖ ≤ Real.sqrt 2 * δ_n / 2 := by
  set v := localSquareCenter q - x with hv_def
  have hdx : |v 0| ≤ δ_n / 2 := center_x_coord_bound h_eq_n q x hx
  have hdy : |v 1| ≤ δ_n / 2 := center_y_coord_bound h_eq_n q x hx
  have h_norm_sq : ‖v‖ ^ 2 = (v 0)^2 + (v 1)^2 := by
    have h : ‖v‖ = Real.sqrt ((v 0)^2 + (v 1)^2) := by
      simpa [EuclideanSpace.norm_eq, Fin.sum_univ_two] using rfl
    rw [h]
    have hpos : 0 ≤ (v 0)^2 + (v 1)^2 := by positivity
    rw [Real.sq_sqrt hpos]
  have hdx2 : (v 0)^2 ≤ (δ_n / 2)^2 := by
    have h : |v 0| ≤ δ_n / 2 := hdx
    have h' : (v 0)^2 = |v 0|^2 := by rw [sq_abs]
    rw [h']; gcongr
  have hdy2 : (v 1)^2 ≤ (δ_n / 2)^2 := by
    have h : |v 1| ≤ δ_n / 2 := hdy
    have h' : (v 1)^2 = |v 1|^2 := by rw [sq_abs]
    rw [h']; gcongr
  have h9 : ‖v‖ ^ 2 ≤ (Real.sqrt 2 * δ_n / 2)^2 := by
    rw [h_norm_sq]
    have h10 : (Real.sqrt 2 * δ_n / 2)^2 = 2 * (δ_n / 2)^2 := by
      have h11 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith
    rw [h10]; linarith
  have h_nonneg1 : 0 ≤ ‖v‖ := by positivity
  have hδ_n_pos : 0 < δ_n := by
    have h : 0 < DiscretisedFurstenbergEstimate.dyadicDelta n :=
      DiscretisedFurstenbergEstimate.dyadicDelta_pos n
    rwa [h_eq_n] at h
  have h_nonneg2 : 0 ≤ Real.sqrt 2 * δ_n / 2 := by positivity
  nlinarith

/-- `‖a‖ ≤ ‖b‖ + ‖a - b‖`. -/
lemma norm_triangle_rev {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
  calc ‖a‖ = ‖b + (a - b)‖ := by abel_nf
  _ ≤ ‖b‖ + ‖a - b‖ := norm_add_le b (a - b)

/-- `localSquareCenter q ∈ q.toSet`. -/
lemma localSquareCenter_mem_toSet {n : ℕ} {δ_n : ℝ}
    (h_eq_n : DiscretisedFurstenbergEstimate.dyadicDelta n = δ_n)
    (q : DiscretisedFurstenbergEstimate.DyadicSquare n) :
    localSquareCenter q ∈ q.toSet := by
  have hδ_pos : 0 < DiscretisedFurstenbergEstimate.dyadicDelta n :=
    DiscretisedFurstenbergEstimate.dyadicDelta_pos n
  have hcx : localSquareCenter q 0 = ((q.i : ℝ) + 1 / 2) * δ_n := by
    simp [localSquareCenter, h_eq_n] <;> ring
  have hcy : localSquareCenter q 1 = ((q.j : ℝ) + 1 / 2) * δ_n := by
    simp [localSquareCenter, h_eq_n] <;> ring
  simp only [DiscretisedFurstenbergEstimate.DyadicSquare.toSet, Set.mem_setOf_eq]
  constructor
  · rw [hcx, ←h_eq_n]
    apply mul_le_mul_of_nonneg_right _ hδ_pos.le
    norm_num
  · constructor
    · rw [hcx, ←h_eq_n]
      apply mul_lt_mul_of_pos_right _ hδ_pos
      norm_num
    · constructor
      · rw [hcy, ←h_eq_n]
        apply mul_le_mul_of_nonneg_right _ hδ_pos.le
        norm_num
      · rw [hcy, ←h_eq_n]
        apply mul_lt_mul_of_pos_right _ hδ_pos
        norm_num

/-- Standalone h_match_backward: for every fine-square center q, there exists
    a point p in Ref_fin within distance δ_n.
    Extracted to avoid whnf timeout from unfolding Ref_fin let-binding. -/
lemma match_backward_lemma {n : ℕ} {δ_n : ℝ}
    (P₀ : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n))
    (P_oriented : Set EuclideanPlane)
    (Ref_fin : Finset EuclideanPlane)
    (h_eq_n : DiscretisedFurstenbergEstimate.dyadicDelta n = δ_n)
    (h_squares_meet : ∀ p ∈ P₀, (p.toSet ∩ P_oriented).Nonempty)
    (hP_oriented_sub_Ref : P_oriented ⊆ (Ref_fin : Set EuclideanPlane)) :
    ∀ q ∈ P₀.image localSquareCenter,
      ∃ p ∈ (Ref_fin : Set EuclideanPlane), dist q p ≤ δ_n := by
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨sq, hsq, rfl⟩
  have h_meet : (sq.toSet ∩ P_oriented).Nonempty := h_squares_meet sq hsq
  rcases h_meet with ⟨x, hx_sq, hx_Por⟩
  have hx_Ref : x ∈ (Ref_fin : Set EuclideanPlane) := hP_oriented_sub_Ref hx_Por
  have hδ_n_pos : 0 < δ_n := by
    rw [←h_eq_n]
    exact DiscretisedFurstenbergEstimate.dyadicDelta_pos n
  have h_bound : ‖localSquareCenter sq - x‖ ≤ Real.sqrt 2 * δ_n / 2 :=
    square_center_dist_bound sq x hx_sq h_eq_n
  have hsqrt_le_one : Real.sqrt 2 / 2 ≤ 1 := by
    have h : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith
  have h_main : ‖localSquareCenter sq - x‖ ≤ δ_n := by
    calc ‖localSquareCenter sq - x‖
      ≤ Real.sqrt 2 * δ_n / 2 := h_bound
    _ = (Real.sqrt 2 / 2) * δ_n := by ring
    _ ≤ 1 * δ_n := by
      exact mul_le_mul_of_nonneg_right hsqrt_le_one hδ_n_pos.le
    _ = δ_n := by ring
  have h_dist : dist (localSquareCenter sq) x = ‖localSquareCenter sq - x‖ := by
    simp [dist_eq_norm]
  exact ⟨x, hx_Ref, by rw [h_dist]; exact h_main⟩

/-- Convert norm bound to closedBall membership for EuclideanPlane.
    Extracted to avoid whnf timeouts inside the dense main proof context. -/
lemma norm_le_to_closedBall {x : EuclideanPlane} {r : ℝ}
    (h : ‖x‖ ≤ r) : x ∈ Metric.closedBall (0 : EuclideanPlane) r := by
  have h' : dist x (0 : EuclideanPlane) ≤ r := by
    have h_eq : dist x (0 : EuclideanPlane) = ‖x‖ := dist_zero_right x
    rw [h_eq]; exact h
  exact h'

/-- Convert closedBall membership to norm bound for EuclideanPlane.
    Extracted to avoid whnf timeouts inside the dense main proof context. -/
lemma closedBall_to_norm_le {x : EuclideanPlane} {r : ℝ}
    (h : x ∈ Metric.closedBall (0 : EuclideanPlane) r) : ‖x‖ ≤ r := by
  have h' : dist x (0 : EuclideanPlane) ≤ r := Metric.mem_closedBall.mp h
  have h_eq : dist x (0 : EuclideanPlane) = ‖x‖ := dist_zero_right x
  rw [h_eq] at h'; exact h'

/-- Extract witness from finset image membership. Extracted to avoid
    whnf timeouts from `rcases` in dense proof context. -/
lemma finset_image_extract {α β : Type*} [DecidableEq β] {f : α → β} {s : Finset α} {y : β}
    (hy : y ∈ s.image f) : ∃ (x : α), x ∈ s ∧ f x = y :=
  Finset.mem_image.mp hy

/-- Convert subset along a set equality. Extracted to avoid whnf timeouts
    from `eq.subst` in dense proof context. -/
lemma subset_eq_convert {X : Type*} {A B C : Set X}
    (h : A ⊆ B) (e : B = C) : A ⊆ C :=
  e ▸ h

/-- Prove swapped centers are in a ball, given unswapped centers are.
    Extracted to avoid whnf timeouts from `rcases` in dense proof context. -/
lemma swapped_centers_in_ball {n : ℕ} {P₀ : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)} {R : ℝ}
    (hR : (P₀.image localSquareCenter : Set EuclideanPlane) ⊆ Metric.closedBall 0 R)
    {y : EuclideanPlane}
    (hy : y ∈ P₀.image (CoordinatePartition.swapCoords ∘ localSquareCenter)) :
    y ∈ Metric.closedBall 0 R := by
  have h_exists : ∃ (q : _), q ∈ P₀ ∧ CoordinatePartition.swapCoords (localSquareCenter q) = y :=
    Finset.mem_image.mp hy
  rcases h_exists with ⟨q, hq, h_eq⟩
  have h_in : localSquareCenter q ∈ (P₀.image localSquareCenter : Set EuclideanPlane) :=
    Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have h_ball : localSquareCenter q ∈ Metric.closedBall 0 R := hR h_in
  have h_norm : ‖localSquareCenter q‖ ≤ R := closedBall_to_norm_le h_ball
  have h_swap_norm : ‖CoordinatePartition.swapCoords (localSquareCenter q)‖ = ‖localSquareCenter q‖ :=
    CoordinatePartition.swapCoordsLI.norm_map (localSquareCenter q)
  have h_final : ‖CoordinatePartition.swapCoords (localSquareCenter q)‖ ≤ R := by
    rw [h_swap_norm]; exact h_norm
  have h_goal : CoordinatePartition.swapCoords (localSquareCenter q) ∈ Metric.closedBall 0 R :=
    norm_le_to_closedBall h_final
  rw [h_eq] at h_goal
  exact h_goal

/-- Prove `P_oriented ⊆ closedBall 0 1` uniformly in swapped and unswapped
    branches, using the linear isometry property of `swapCoords`.
    Extracted to avoid heartbeat timeouts from inline `simp` in dense context. -/
lemma p_oriented_ball_helper
    {P_ret Pbar_set P_oriented : Set EuclideanPlane}
    {swapped : Bool}
    (hP_ret_subset : P_ret ⊆ Pbar_set)
    (hPbar_subset_ball : Pbar_set ⊆ Metric.closedBall (0 : EuclideanPlane) 1)
    (h_swapped_true : swapped = true → P_oriented ⊆ CoordinatePartition.swapCoords '' P_ret)
    (h_swapped_false : swapped = false → P_oriented ⊆ P_ret) :
    P_oriented ⊆ Metric.closedBall (0 : EuclideanPlane) 1 := by
  by_cases h_sw : swapped = true
  · have h_sub : P_oriented ⊆ CoordinatePartition.swapCoords '' P_ret := h_swapped_true h_sw
    have h2 : P_ret ⊆ Metric.closedBall (0 : EuclideanPlane) 1 :=
      Set.Subset.trans hP_ret_subset hPbar_subset_ball
    have h3 : CoordinatePartition.swapCoords '' P_ret ⊆ Metric.closedBall (0 : EuclideanPlane) 1 := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hx_ball : x ∈ Metric.closedBall (0 : EuclideanPlane) 1 := h2 hx
      have h_norm : ‖x‖ ≤ 1 := closedBall_to_norm_le hx_ball
      have h_swap_norm : ‖CoordinatePartition.swapCoords x‖ = ‖x‖ :=
        CoordinatePartition.swapCoordsLI.norm_map x
      have h_final : ‖CoordinatePartition.swapCoords x‖ ≤ 1 := by
        rw [h_swap_norm]; exact h_norm
      exact norm_le_to_closedBall h_final
    exact Set.Subset.trans h_sub h3
  · have h_sw' : swapped = false := by
      cases swapped <;> simp_all
    have h_sub : P_oriented ⊆ P_ret := h_swapped_false h_sw'
    exact Set.Subset.trans (Set.Subset.trans h_sub hP_ret_subset) hPbar_subset_ball

/-- Bound all dyadic-square centers in a ball of radius `1 + √2 * δ_n / 2`.
    For each square `q ∈ P₀`, `h_squares_meet` gives a point `x ∈ q.toSet ∩ P_oriented`.
    Since `P_oriented ⊆ closedBall 0 1`, we have `‖x‖ ≤ 1`.
    By `square_center_dist_bound`, `‖localSquareCenter q - x‖ ≤ √2 * δ_n / 2`.
    Triangle inequality gives `‖localSquareCenter q‖ ≤ 1 + √2 * δ_n / 2`. -/
lemma centers_in_ball {n : ℕ} {δ_n : ℝ}
    (P₀ : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n))
    (P_oriented : Set EuclideanPlane)
    (h_eq_n : DiscretisedFurstenbergEstimate.dyadicDelta n = δ_n)
    (hP_oriented_ball : P_oriented ⊆ Metric.closedBall (0 : EuclideanPlane) 1)
    (h_squares_meet : ∀ (q : DiscretisedFurstenbergEstimate.DyadicSquare n),
        q ∈ P₀ → ((q.toSet : Set EuclideanPlane) ∩ P_oriented).Nonempty) :
    (P₀.image localSquareCenter : Set EuclideanPlane) ⊆
      Metric.closedBall (0 : EuclideanPlane) (1 + Real.sqrt 2 * δ_n / 2) := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
  have h_meet : ((q.toSet : Set EuclideanPlane) ∩ P_oriented).Nonempty :=
    h_squares_meet q hq
  rcases h_meet with ⟨x, hx_q, hx_Por⟩
  have hx_ball : x ∈ Metric.closedBall (0 : EuclideanPlane) 1 :=
    hP_oriented_ball hx_Por
  have h_norm_x : ‖x‖ ≤ 1 := closedBall_to_norm_le hx_ball
  have h_bound : ‖localSquareCenter q - x‖ ≤ Real.sqrt 2 * δ_n / 2 :=
    square_center_dist_bound q x hx_q h_eq_n
  have h_norm_center : ‖localSquareCenter q‖ ≤ 1 + Real.sqrt 2 * δ_n / 2 := by
    calc ‖localSquareCenter q‖
      ≤ ‖x‖ + ‖localSquareCenter q - x‖ := norm_triangle_rev (localSquareCenter q) x
    _ ≤ 1 + Real.sqrt 2 * δ_n / 2 := by linarith
  exact norm_le_to_closedBall h_norm_center

/-- Adapt Pbar card bound from _root_.dyadicDelta to δ_n. Extracted to avoid
    whnf timeouts from `simpa` in dense proof context. -/
lemma adapt_pbar_card {α : Type*} {P : Finset α} {δ δ' : ℝ} {u : ℝ}
    (h : (P.card : ℝ) ≤ 100 * Real.rpow δ (-u))
    (h_eq : δ' = δ) :
    (P.card : ℝ) ≤ 100 * Real.rpow δ' (-u) := by
  have h2 : Real.rpow δ (-u) = Real.rpow δ' (-u) := by rw [←h_eq]
  rw [h2] at h
  exact h

/-- Simple algebraic helper: `δ_n ≤ 4 * δ` implies `δ_n / 4 ≤ δ`.
    Extracted to avoid whnf timeout from `linarith` in dense proof context. -/
lemma quarter_le_of_four_le {δ_n δ : ℝ} (h : δ_n ≤ 4 * δ) : δ_n / 4 ≤ δ := by
  calc δ_n / 4 ≤ (4 * δ) / 4 := by gcongr
       _ = δ := by ring

/-- Adapt IsDeltaSSet to the if-swapped set. Extracted to avoid
    whnf timeouts from `by_cases` in dense proof context. -/
lemma adapt_sset_if_swapped {δ u C : ℝ} {Pbar : Finset EuclideanPlane} {swapped : Bool}
    (hPbar_sset_n : IsDeltaSSet δ u C (Pbar : Set EuclideanPlane)) :
    IsDeltaSSet δ u C (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)
     else (Pbar : Set EuclideanPlane)) := by
  by_cases h_sw : swapped = true
  · rw [if_pos h_sw]
    have h_img : CoordinatePartition.swapCoords '' (Pbar : Set EuclideanPlane) = (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane) :=
      Finset.coe_image.symm
    have h_main : IsDeltaSSet δ u C (CoordinatePartition.swapCoords '' (Pbar : Set EuclideanPlane)) :=
      IsDeltaSSet.swapCoords_image hPbar_sset_n
    rw [h_img] at h_main
    exact h_main
  · rw [if_neg h_sw]
    exact hPbar_sset_n

/-- Adapt pairwise separation to the if-swapped set. Extracted to avoid
    whnf timeouts from `by_cases` in dense proof context. -/
lemma adapt_sep_if_swapped {δ : ℝ} {Pbar : Finset EuclideanPlane} {swapped : Bool}
    (hPbar_sep_deltas : Set.Pairwise (Pbar : Set EuclideanPlane) (fun p q => δ ≤ dist p q)) :
    Set.Pairwise (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)
     else (Pbar : Set EuclideanPlane)) (fun p q => δ ≤ dist p q) := by
  by_cases h_sw : swapped = true
  · rw [if_pos h_sw]
    intro p hp q hq hne
    rcases Finset.mem_image.mp hp with ⟨p', hp', rfl⟩
    rcases Finset.mem_image.mp hq with ⟨q', hq', rfl⟩
    have hne' : p' ≠ q' := by intro h; rw [h] at hne; exact hne rfl
    have h : δ ≤ dist p' q' := by
      exact hPbar_sep_deltas (x := p') (y := q') hp' hq' hne'
    have h_iso : dist (CoordinatePartition.swapCoords p') (CoordinatePartition.swapCoords q') = dist p' q' :=
      CoordinatePartition.swapCoords_isometry.dist_eq p' q'
    rw [h_iso]; exact h
  · rw [if_neg h_sw]
    exact hPbar_sep_deltas

/-- Prove `δ_n ≤ Δ / 4` from `δ_n = Δ^2`, `0 < Δ < 1`, `0 < ε < 1`,
  and `Δ^(ε/4) ≤ 1/100`. Extracted to avoid linarith stack overflow
  in the large FrontEndComposition context. -/
lemma delta_quarter_bound
    (Δ ε δ_n : ℝ)
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_one : Δ < 1)
    (hε_pos : 0 < ε)
    (hε_lt_one : ε < 1)
    (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (hδ_n_eq2 : δ_n = Δ ^ 2) :
    δ_n ≤ Δ / 4 := by
  have h1 : (1 : ℝ) > ε / 4 := by linarith
  have h2 : Δ < Real.rpow Δ (ε / 4) := by
    have h21 : Real.rpow Δ 1 < Real.rpow Δ (ε / 4) :=
      Real.rpow_lt_rpow_of_exponent_gt hΔ_pos hΔ_lt_one h1
    have h22 : Real.rpow Δ 1 = Δ := by simp
    rw [h22] at h21
    exact h21
  have h3 : Δ < 1 / 100 := by linarith [h2, h_small_eps]
  have h4 : Δ ≤ 1 / 4 := by linarith
  have h5 : Δ ^ 2 ≤ Δ / 4 := by
    calc Δ ^ 2
      = Δ * Δ := by ring
    _ ≤ Δ * (1 / 4) := by gcongr <;> linarith
    _ = Δ / 4 := by ring
  rw [hδ_n_eq2]
  exact h5

end DirecretisedFurstenbergEstimate.FrontEndLemmas.FrontEndComposition

end
