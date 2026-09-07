module

/-
  Theorem 6.1 Main Assembly Helpers

  Stable, fully-proved helper lemmas extracted from Theorem61MainAssembly.lean
  to reduce re-elaboration time during assembly debugging.

  Contains:
  - Numerical and positivity lemmas
  - Coarse point/tube majorants and polylog absorption
  - Fine chain adapters (CP, Kglobal, CQ)
  - Retained S-set transfer
  - Fine branch full transfer
  - Geometry and frontend adapters

  Whiteprint node: theorem61_main_assembly (helpers sub-component)
  Status: COMPLETE — all lemmas proved, no sorrys
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Contracts.AppendixA
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5Wrapper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.SSetExponentCap
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CProp5Absorption
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers2
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.HeavyParentUniformClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.GlobalRetainedRegular
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseParentSSetRatio
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseBranchAssemblyClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseBranchAdapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.Gap1Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataType
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1BridgeHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.HeavyConfigHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.ScaleConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FixedScaleAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FixedScaleAdapterRadius
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FixedPackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.ProvenanceRadiusAddition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FineBranchTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FullParameterSelection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.StandaloneParentGeometry
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_SSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.PolynomialMajorants
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataConstructor
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CleanFineCor25Chain
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CleanB1Geometry
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CRetCancellationClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CoarseBranchFromB1Data
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.ExactMFrontend
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.IncidenceOffsetBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.RetainedRegularityClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable


noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Slope bound for a dyadic tube from its a-index strip bound. -/
lemma full_T0_slope_bound
    {n : ℕ} (hn_pos : 0 < n)
    {T : DiscretisedFurstenbergEstimate.DyadicTube n}
    (h_strip : -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ)) :
    |T.slope| ≤ 1 := by
  have h1 : -(2 ^ n : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h_strip.1
  have h2 : (T.a : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast h_strip.2
  have h_abs_a : |(T.a : ℝ)| ≤ (2 ^ n : ℝ) := by
    have h3 : (T.a : ℝ) ≤ (2 ^ n : ℝ) := le_of_lt h2
    exact abs_le.mpr ⟨h1, h3⟩
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have h_slope_eq : |T.slope| = |(T.a : ℝ)| * dyadicDelta n := by
    have h_main : |(T.a : ℝ) * dyadicDelta n| = |(T.a : ℝ)| * dyadicDelta n := by
      rw [abs_mul, abs_of_pos hδ_pos]
    simpa [DiscretisedFurstenbergEstimate.DyadicTube.slope] using h_main
  rw [h_slope_eq]
  have h5 : |(T.a : ℝ)| * dyadicDelta n ≤ (2 ^ n : ℝ) * dyadicDelta n :=
    mul_le_mul_of_nonneg_right h_abs_a (by linarith)
  have h6 : (2 ^ n : ℝ) * dyadicDelta n = 1 := by
    have h_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
    have h_eq : dyadicDelta n = (1 : ℝ) / (2 ^ n : ℝ) := by
      rw [dyadicDelta] <;> ring
    rw [h_eq]
    field_simp [h_pos.ne'] <;> ring
  rw [h6] at h5
  exact h5



end DiscretisedFurstenbergEstimate.CombiningTheoremRework

namespace DirecretisedFurstenbergEstimate

open RegularIncidence
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.CombiningTheoremRework
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DiscretisedFurstenbergEstimate.CoveringUtils
open DyadicCardToNcover (toAffineLine)

/-- Helper: 9^(u/2) ≤ 9 for u ≤ 2. Isolated to avoid timeout from large context. -/
lemma nine_half_pow_le_nine (u : ℝ) (hu2 : u ≤ 2) : (9 : ℝ)^(u / 2) ≤ 9 := by
  have h10 : u / 2 ≤ 1 := by linarith
  have h_base : (1 : ℝ) ≤ 9 := by norm_num
  have h_rpow : (9 : ℝ)^(u / 2) ≤ (9 : ℝ)^(1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h_base h10
  simpa using h_rpow

/-- Helper: budget inequality for two copies of (εA-εInc)/3. Isolated to avoid timeout. -/
lemma fine_budget_thirds {εA εInc : ℝ} (h : εInc ≤ εA) :
    εInc ≤ εA - (εA - εInc) / 3 - (εA - εInc) / 3 := by
  have h_pos : 0 ≤ εA - εInc := by linarith
  have h_pos3 : 0 ≤ (εA - εInc) / 3 := by positivity
  have h_eq : εA - (εA - εInc) / 3 - (εA - εInc) / 3 = εInc + (εA - εInc) / 3 := by ring
  rw [h_eq]
  exact le_add_of_nonneg_right h_pos3

/-- Helper: sqrt identity for dyadic deltas at even scale. -/
lemma dyadic_delta_sqrt_eq (n m : ℕ) (h_even : n = 2 * m) :
    Real.sqrt (9 * DiscretisedFurstenbergEstimate.dyadicDelta n) =
    3 * DiscretisedFurstenbergEstimate.dyadicDelta m := by
  have h1 : DiscretisedFurstenbergEstimate.dyadicDelta n =
      (DiscretisedFurstenbergEstimate.dyadicDelta m)^2 := by
    rw [h_even]
    <;> simp [DiscretisedFurstenbergEstimate.dyadicDelta] <;> ring
  rw [h1]
  have h2 : 0 < DiscretisedFurstenbergEstimate.dyadicDelta m :=
    DiscretisedFurstenbergEstimate.dyadicDelta_pos m
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq h2.le] <;> ring

notation "δd" => DiscretisedFurstenbergEstimate.dyadicDelta

/-- Helper: ElementaryIncidence.δ m equals dyadicDelta m for m : ℕ.
Extracted to avoid norm_cast timeout inside the giant theorem. -/
lemma delta_eq_dyadicDelta (m : ℕ) :
    DiscretisedFurstenbergEstimate.δ m = DiscretisedFurstenbergEstimate.dyadicDelta m := by
  have h1 : DiscretisedFurstenbergEstimate.δ m = (2 : ℝ)^(-(m : ℤ)) := by rfl
  have h2 : (2 : ℝ)^(-(m : ℤ)) = 1 / (2 : ℝ)^m := by
    have h21 : (2 : ℝ)^(m : ℤ) = (2 : ℝ)^m := by
      exact zpow_natCast (2 : ℝ) m
    have h22 : (2 : ℝ)^(-(m : ℤ)) = ((2 : ℝ)^(m : ℤ))⁻¹ := by
      rw [zpow_neg] <;> ring
    rw [h22, h21] <;> ring
  have h3 : DiscretisedFurstenbergEstimate.dyadicDelta m = 1 / (2 : ℝ)^m := by
    rw [DiscretisedFurstenbergEstimate.dyadicDelta] <;> simp
  rw [h1, h2, h3]

/-- Helper: dyadicDelta m = 1 / 2^m. -/
lemma dyadicDelta_eq_inv_pow (m : ℕ) :
    DiscretisedFurstenbergEstimate.dyadicDelta m = 1 / (2 : ℝ)^m := by
  rw [DiscretisedFurstenbergEstimate.dyadicDelta] <;> simp

/-- dyadicDelta m < 1 when m ≥ 2. -/
lemma dyadicDelta_lt_one (m : ℕ) (hm : 2 ≤ m) :
    DiscretisedFurstenbergEstimate.dyadicDelta m < 1 := by
  have h1 : DiscretisedFurstenbergEstimate.dyadicDelta m = 1 / (2 : ℝ)^m :=
    dyadicDelta_eq_inv_pow m
  rw [h1]
  have h2 : (4 : ℝ) ≤ (2 : ℝ)^m := by
    have h3 : (2 : ℕ)^m ≥ 4 := by
      have h4 : m ≥ 2 := hm
      have h5 : ∀ n : ℕ, n ≥ 2 → (2 : ℕ)^n ≥ 4 := by
        intro n hn
        induction' hn with k hk ih
        · norm_num
        · simp [pow_succ] at * <;> omega
      exact h5 m h4
    exact_mod_cast h3
  have h6 : 1 / (2 : ℝ)^m ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  linarith

/-- Helper: from δd n ≤ 1/8 and n = 2*m, derive 2 ≤ m. -/
lemma hm_ge2_from_delta (n m : ℕ) (h_even : n = 2 * m)
    (hδn_le_eighth : δd n ≤ 1 / 8) : 2 ≤ m := by
  have h21 : δd n = 1 / (2 : ℝ)^n := by
    rw [DiscretisedFurstenbergEstimate.dyadicDelta] <;> rfl
  have h22 : (1 / 2 : ℝ)^n = 1 / (2 : ℝ)^n := by
    rw [div_pow] <;> norm_num
  have h2 : δd n = (1 / 2 : ℝ)^n := by
    rw [h21, ←h22]
  rw [h2] at hδn_le_eighth
  have h3 : n ≥ 3 := by
    by_contra h4
    have h5 : n ≤ 2 := by omega
    have h_disj : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases h_disj with (rfl | rfl | rfl) <;> norm_num at hδn_le_eighth <;> linarith
  have h6 : n = 2 * m := h_even
  omega

/-- Helper: algebraic rearrangement of coarse geo bound. -/
lemma coarse_geo_bound_algebra
    (s εA δn : ℝ) (hδn_pos : 0 < δn) (coarseT0_card : ℕ)
    (h4 : ((9 * δn)^(-(s + εA)) : ℝ) ≤ (262144 : ℝ)^2 * (coarseT0_card : ℝ)) :
    (coarseT0_card : ℝ) ≥
      ((9 : ℝ)^(-(s + εA)) / (262144 : ℝ)^2) * δn^(-(s + εA)) := by
  have h6 : ((9 * δn)^(-(s + εA)) : ℝ) =
      (9 : ℝ)^(-(s + εA)) * δn^(-(s + εA)) := by
    have hδn_nonneg : 0 ≤ δn := le_of_lt hδn_pos
    rw [Real.mul_rpow (by norm_num) hδn_nonneg] <;> ring
  have h7 : (0 : ℝ) < (262144 : ℝ)^2 := by positivity
  have h8 : (coarseT0_card : ℝ) ≥ ((9 * δn)^(-(s + εA)) : ℝ) / (262144 : ℝ)^2 := by
    calc ((9 * δn)^(-(s + εA)) : ℝ) / (262144 : ℝ)^2
      ≤ ((262144 : ℝ)^2 * (coarseT0_card : ℝ)) / (262144 : ℝ)^2 := by gcongr
    _ = (coarseT0_card : ℝ) := by
      field_simp [h7.ne'] <;> ring
  rw [h6] at h8
  have h9 : ((9 : ℝ)^(-(s + εA)) * δn^(-(s + εA))) / (262144 : ℝ)^2 =
      ((9 : ℝ)^(-(s + εA)) / (262144 : ℝ)^2) * δn^(-(s + εA)) := by ring
  rw [h9] at h8
  exact h8

abbrev DSq (n : ℕ) := DiscretisedFurstenbergEstimate.DyadicSquare n
abbrev DTb (n : ℕ) := DiscretisedFurstenbergEstimate.DyadicTube n

/-- Type of the uniform Prop 5 specification, for explicit annotation. -/
abbrev UniformProp5Spec (s K : ℝ) : Prop :=
  ∀ (t : ℝ), s ≤ t → t ≤ 1 →
    ∀ {n : ℕ} (C_P C_T M : ℝ),
      0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ n →
      ∀ (P : Finset (DiscretisedFurstenbergEstimate.DSquare n)),
        P.Nonempty →
        DiscretisedFurstenbergEstimate.IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ n) t C_P P →
        (∀ (x y : DiscretisedFurstenbergEstimate.DSquare n), x ∈ P → y ∈ P → dist x y ≤ 3) →
        (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
        ∀ (Tp : DiscretisedFurstenbergEstimate.TubeFamily n),
          (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
          (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
          (∀ p ∈ P, DiscretisedFurstenbergEstimate.IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ n) s C_T (Tp p)) →
          (∀ p ∈ P, M / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
          let T := P.biUnion fun p => Tp p
          (T.card : ℝ) ≥ (1 / K) * Real.log (1 / DiscretisedFurstenbergEstimate.δ n) ^ (-K) *
            (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ n) ^ (-s) *
              (M * (DiscretisedFurstenbergEstimate.δ n) ^ s) ^ ((t - s) / (1 - s))

/-- Apply uniform_prop5_wrapper_with_K, specializing hK_spec internally.
Extracted to avoid whnf timeout in the large theorem context. -/
lemma apply_prop5_wrapper
    (m : ℕ) (s t C₁ C_P K : ℝ) (M : ℕ)
    (hK_pos : 0 < K)
    (hK_spec : UniformProp5Spec s K)
    (hsu0 : s ≤ t) (hu0_one : t ≤ 1)
    (config : DiscretisedFurstenbergEstimate.CombiningTheorem.NiceConfiguration m s C₁ M)
    (hn_ge_2 : 2 ≤ m)
    (hM_pos : 0 < M)
    (hP_nonempty : config.P₀.Nonempty)
    (hCP : 0 < C_P)
    (hCP_ge1 : 1 ≤ C_P)
    (hC₁ : 0 < C₁)
    (hC1_ge1 : 1 ≤ C₁)
    (hs_nonneg : 0 ≤ s)
    (hP_set : DiscretisedFurstenbergEstimate.IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.dyadicDelta m) t C_P
        (DiscretisedFurstenbergEstimate.DyadicConversion.finsetDyadicToDSquare config.P₀))
    (h_slope : ∀ T ∈ config.T₀, |T.slope| ≤ 1)
    (h_diam : ∀ (p q : DiscretisedFurstenbergEstimate.DSquare m),
        p ∈ DiscretisedFurstenbergEstimate.DyadicConversion.finsetDyadicToDSquare config.P₀ →
        q ∈ DiscretisedFurstenbergEstimate.DyadicConversion.finsetDyadicToDSquare config.P₀ → dist p q ≤ 3)
    (h_unit : ∀ (p : DiscretisedFurstenbergEstimate.DSquare m),
        p ∈ DiscretisedFurstenbergEstimate.DyadicConversion.finsetDyadicToDSquare config.P₀ →
        ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) :
    (config.T₀.card : ℝ) ≥
      (1 / K) * Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta m) ^ (-K) *
        (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) *
        (DiscretisedFurstenbergEstimate.dyadicDelta m) ^ (-s) *
        ((M : ℝ) * (DiscretisedFurstenbergEstimate.dyadicDelta m) ^ s) ^ ((t - s) / (1 - s)) := by
  have hK_spec_u0 := hK_spec t hsu0 hu0_one (n := m)
  exact uniform_prop5_wrapper_with_K
    (hK_pos := hK_pos)
    (hK_spec := hK_spec_u0)
    (config := config)
    (hn_ge_2 := hn_ge_2)
    (hM_pos := hM_pos)
    (hP_nonempty := hP_nonempty)
    (hCP := hCP)
    (hCP_ge1 := hCP_ge1)
    (hC₁ := hC₁)
    (hC1_ge1 := hC1_ge1)
    (hs_nonneg := hs_nonneg)
    (hP_set := hP_set)
    (h_slope := h_slope)
    (h_diam := h_diam)
    (h_unit := h_unit)

/-- Core polylog absorption: given a denominator bound and absorption spec,
prove C_prop5 ≥ δn^loss. Extracted to reduce theorem body size. -/
lemma prop5_polylog_absorption_core
    (K C_P CΔ s : ℝ)
    (n m : ℕ)
    (hK_pos : 0 < K)
    (h_even : n = 2 * m)
    (hn_pos : 0 < n)
    (C_poly : ℝ)
    (hC_poly_pos : 0 < C_poly)
    (a : ℝ)
    (d : ℕ)
    (loss : ℝ)
    (δ_thresh : ℝ)
    (h_abs_spec : ∀ (k : ℕ), δd k ≤ δ_thresh →
        (2^K / K) * Real.log (1 / δd k)^(-K) * (δd k)^a / (C_poly * (k:ℝ)^d) ≥ (δd k)^loss)
    (hδn_le : δd n ≤ δ_thresh)
    (hδn_pos : 0 < δd n)
    (hδn_lt_one : δd n < 1)
    (h_denom_bound : C_P * 13 * CΔ * (2:ℝ)^s ≤ C_poly * (n:ℝ)^d * (δd n)^(-a))
    (hs_nonneg : 0 ≤ s)
    (hCP_pos : 0 < C_P)
    (hCΔ_pos : 0 < CΔ) :
    Section6.C_prop5_at_coarse_scale K C_P CΔ s (δd m) ≥ (δd n)^loss := by
  have h_scale_conv : Section6.C_prop5_at_coarse_scale K C_P CΔ s (δd m) =
      (2^K / K) * Real.log (1 / δd n)^(-K) / (C_P * 13 * CΔ * (2:ℝ)^s) :=
    Section6.C_prop5_coarse_to_fine_scale K C_P CΔ s n m h_even hK_pos hn_pos
  have h42 : 0 < C_P * 13 * CΔ * (2:ℝ)^s := by positivity
  have hnd_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  have h_rpow_pos : 0 < (δd n)^(-a) := Real.rpow_pos_of_pos hδn_pos (-a)
  have h43 : 0 < C_poly * (n:ℝ)^d * (δd n)^(-a) := by
    apply mul_pos
    · apply mul_pos hC_poly_pos
      positivity
    · exact h_rpow_pos
  have h47 : (δd n)^(-a) * (δd n)^a = 1 := by
    have h48 : (δd n)^(-a) * (δd n)^a = (δd n)^(-a + a) := by
      rw [← Real.rpow_add hδn_pos] <;> ring
    rw [h48]
    have h49 : -a + a = 0 := by ring
    rw [h49]
    simp
  have h45 : 1 / (C_P * 13 * CΔ * (2:ℝ)^s) ≥ (δd n)^a / (C_poly * (n:ℝ)^d) := by
    calc
      1 / (C_P * 13 * CΔ * (2:ℝ)^s)
        ≥ 1 / (C_poly * (n:ℝ)^d * (δd n)^(-a)) := by gcongr
      _ = (δd n)^a / (C_poly * (n:ℝ)^d) := by
        field_simp [h43.ne'] <;> rw [h47] <;> ring
  have h_log_pos : 0 < Real.log (1 / δd n) := by
    have h1 : 1 < 1 / δd n := by
      apply one_lt_one_div
      <;> linarith
    exact Real.log_pos h1
  have h_log_rpow_pos : 0 < Real.log (1 / δd n)^(-K) := Real.rpow_pos_of_pos h_log_pos (-K)
  have h2K_pos : 0 < (2^K / K : ℝ) := by positivity
  have h_factor_pos : 0 < (2^K / K : ℝ) * Real.log (1 / δd n)^(-K) := mul_pos h2K_pos h_log_rpow_pos
  have h44 : (2^K / K) * Real.log (1 / δd n)^(-K) / (C_P * 13 * CΔ * (2:ℝ)^s) ≥
      (2^K / K) * Real.log (1 / δd n)^(-K) * (δd n)^a / (C_poly * (n:ℝ)^d) := by
    calc
      (2^K / K) * Real.log (1 / δd n)^(-K) / (C_P * 13 * CΔ * (2:ℝ)^s)
        = (2^K / K) * Real.log (1 / δd n)^(-K) * (1 / (C_P * 13 * CΔ * (2:ℝ)^s)) := by ring
      _ ≥ (2^K / K) * Real.log (1 / δd n)^(-K) * ((δd n)^a / (C_poly * (n:ℝ)^d)) := by
          gcongr
      _ = (2^K / K) * Real.log (1 / δd n)^(-K) * (δd n)^a / (C_poly * (n:ℝ)^d) := by ring
  have h49 : (2^K / K) * Real.log (1 / δd n)^(-K) * (δd n)^a / (C_poly * (n:ℝ)^d) ≥ (δd n)^loss :=
    h_abs_spec n hδn_le
  rw [h_scale_conv]
  exact le_trans h49 h44

/-- Positivity of C_prop5_at_coarse_scale, extracted to avoid timeout in
the large theorem context. -/
lemma C_prop5_at_coarse_scale_pos
    (K C_P CΔ s δm : ℝ)
    (hK_pos : 0 < K) (hCP_pos : 0 < C_P) (hCΔ_pos : 0 < CΔ)
    (hs_nonneg : 0 ≤ s) (hδm_pos : 0 < δm) (hδm_lt_one : δm < 1) :
    0 < Section6.C_prop5_at_coarse_scale K C_P CΔ s δm := by
  have h_log_pos : 0 < Real.log (1 / δm) := by
    have h1 : 1 < 1 / δm := by
      apply one_lt_one_div
      <;> linarith
    exact Real.log_pos h1
  have h_rpow_pos : 0 < Real.log (1 / δm) ^ (-K) := Real.rpow_pos_of_pos h_log_pos (-K)
  have h_rpow2_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
  have h_denom_pos : 0 < C_P * 13 * CΔ * Real.rpow 2 s := by positivity
  have h_one_div_K_pos : 0 < 1 / K := one_div_pos.mpr hK_pos
  have h_main : 0 < (1 / K) * Real.log (1 / δm) ^ (-K) / (C_P * 13 * CΔ * Real.rpow 2 s) := by
    apply div_pos
    · exact mul_pos h_one_div_K_pos h_rpow_pos
    · exact h_denom_pos
  simpa [Section6.C_prop5_at_coarse_scale] using h_main

/-- Convert raw Prop 5 wrapper conclusion to the C_prop5 form. -/
lemma prop5_match_coarse_form
    {K C_P C₁ s δ M α card : ℝ} {u0 : ℝ}
    (hα : α = (u0 - s) / (1 - s))
    (h_raw : card ≥ (1 / K) * Real.log (1 / δ)^(-K) *
        (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) * M * δ^(-s) *
        (M * δ^s)^((u0 - s) / (1 - s)))
    (hK_pos : 0 < K) (hCP_pos : 0 < C_P) (hC1_pos : 0 < C₁)
    (hδ_pos : 0 < δ) (hs_nonneg : 0 ≤ s) :
    card ≥ Section6.C_prop5_at_coarse_scale K C_P C₁ s δ * M * δ^(-s) * (M * δ^s)^α := by
  rw [hα]
  have h_rpow2_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
  have h_eq : (1 / K) * Real.log (1 / δ)^(-K) *
        (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) * M * δ^(-s) *
        (M * δ^s)^((u0 - s) / (1 - s)) =
      Section6.C_prop5_at_coarse_scale K C_P C₁ s δ * M * δ^(-s) *
        (M * δ^s)^((u0 - s) / (1 - s)) := by
    dsimp only [Section6.C_prop5_at_coarse_scale]
    field_simp [hK_pos.ne', hCP_pos.ne', hC1_pos.ne', h_rpow2_pos.ne'] <;> ring
  rw [h_eq] at h_raw
  exact h_raw

/-- Bound (4n+7)^7 ≤ (11n)^7 for n ≥ 1. -/
lemma four_n_plus_seven_le_eleven_n_pow7 {n : ℕ} (hn_pos : 0 < n) :
    (4 * (n : ℝ) + 7)^7 ≤ (11 * (n : ℝ))^7 := by
  have h : 4 * (n : ℝ) + 7 ≤ 11 * (n : ℝ) := by
    have h' : (n : ℝ) ≥ 1 := by exact_mod_cast hn_pos
    linarith
  have h' : 0 ≤ 4 * (n : ℝ) + 7 := by positivity
  gcongr

/-- Bound (2 * Real.sqrt 2)^u ≤ 8 when 0 ≤ u ≤ 2. -/
lemma two_sqrt2_pow_le_eight (u : ℝ) (hu0 : 0 ≤ u) (hu2 : u ≤ 2) :
    (2 * Real.sqrt 2)^u ≤ 8 := by
  have h_base : 1 ≤ 2 * Real.sqrt 2 := by
    have h1 : (1 : ℝ)^2 ≤ (2 : ℝ) := by norm_num
    have h2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le h1
    linarith
  have h_pow : (2 * Real.sqrt 2)^u ≤ (2 * Real.sqrt 2)^(2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h_base hu2
  have h_eq : (2 * Real.sqrt 2)^(2 : ℝ) = 8 := by
    have h3 : (2 * Real.sqrt 2)^(2 : ℝ) = (2 * Real.sqrt 2)^2 := by norm_cast
    rw [h3]
    have h4 : (2 * Real.sqrt 2)^2 = 4 * (Real.sqrt 2)^2 := by
      rw [mul_pow] <;> norm_num
    rw [h4]
    have h5 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    rw [h5] <;> norm_num
  exact h_pow.trans (le_of_eq h_eq)

/-- One-leverage for natural powers: 1 ≤ n^k when n > 0. -/
lemma one_le_nat_pow {n : ℕ} (hn : 0 < n) (k : ℕ) : 1 ≤ (n : ℝ)^k := by
  have h1 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have h21 : 1 ≤ n := by linarith
  have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h21
  have h3 : (1 : ℝ)^k ≤ (n : ℝ)^k := by gcongr
  simpa using h3

/-- Coarse point majorant: 162 * C_point * (2 * K_B1) * (2*sqrt2)^u ≤ poly * n^23 * δn^{-(εReg+pointLoss)}. -/
lemma coarse_point_majorant
    (n : ℕ) (hn_pos : 0 < n)
    (C_point K_B1 : ℝ)
    (u : ℝ) (hu0 : 0 ≤ u) (hu2 : u ≤ 2)
    (εReg pointLoss : ℝ)
    (hδn_pos : 0 < δd n)
    (hC_point_nonneg : 0 ≤ C_point)
    (hK_B1_nonneg : 0 ≤ K_B1)
    (h_majorant_point : C_point ≤ (δd n)^(-(εReg + pointLoss)) * (10:ℝ)^50 * (n:ℝ)^16)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n:ℝ) + 7)^7) :
    162 * C_point * (2 * K_B1) * (2 * Real.sqrt 2)^u ≤
      (162 * (10:ℝ)^50 * 2 * 2700 * 3145728 * 8 * (11:ℝ)^7) * (n:ℝ)^23 * (δd n)^(-(εReg + pointLoss)) := by
  have h11 : (2 * Real.sqrt 2)^u ≤ 8 := two_sqrt2_pow_le_eight u hu0 hu2
  have h14 : (4 * (n : ℝ) + 7)^7 ≤ (11 * (n : ℝ))^7 := four_n_plus_seven_le_eleven_n_pow7 hn_pos
  have h17 : (11 * (n : ℝ))^7 = (11 : ℝ)^7 * (n : ℝ)^7 := by ring
  have h_rpow_nonneg : 0 ≤ (δd n)^(-(εReg + pointLoss)) := Real.rpow_nonneg hδn_pos.le _
  have h_pos_a : 0 ≤ (δd n)^(-(εReg + pointLoss)) * (10:ℝ)^50 * (n:ℝ)^16 := by positivity
  have h_pos_b : 0 ≤ 2 * (2700 * 3145728 * (4 * (n:ℝ) + 7)^7) := by positivity
  have h_step1 : 162 * C_point * (2 * K_B1) * (2 * Real.sqrt 2)^u ≤
      162 * ((δd n)^(-(εReg + pointLoss)) * (10:ℝ)^50 * (n:ℝ)^16) *
          (2 * (2700 * 3145728 * (4 * (n:ℝ) + 7)^7)) * 8 := by
    gcongr
    <;> assumption
  calc
    162 * C_point * (2 * K_B1) * (2 * Real.sqrt 2)^u
      ≤ 162 * ((δd n)^(-(εReg + pointLoss)) * (10:ℝ)^50 * (n:ℝ)^16) *
            (2 * (2700 * 3145728 * (4 * (n:ℝ) + 7)^7)) * 8 := h_step1
    _ = (162 * (10:ℝ)^50 * 2 * 2700 * 3145728 * 8) * (n:ℝ)^16 * (4 * (n:ℝ) + 7)^7 * (δd n)^(-(εReg + pointLoss)) := by ring
    _ ≤ (162 * (10:ℝ)^50 * 2 * 2700 * 3145728 * 8) * (n:ℝ)^16 * ((11:ℝ)^7 * (n:ℝ)^7) * (δd n)^(-(εReg + pointLoss)) := by
      have h14' : (4 * (n : ℝ) + 7)^7 ≤ (11 : ℝ)^7 * (n : ℝ)^7 := le_trans h14 (le_of_eq h17)
      have h_nonneg1 : 0 ≤ (162 * (10:ℝ)^50 * 2 * 2700 * 3145728 * 8) * (n:ℝ)^16 := by positivity
      have h_nonneg2 : 0 ≤ (δd n)^(-(εReg + pointLoss)) := Real.rpow_nonneg hδn_pos.le _
      nlinarith
    _ = (162 * (10:ℝ)^50 * 2 * 2700 * 3145728 * 8 * (11:ℝ)^7) * (n:ℝ)^23 * (δd n)^(-(εReg + pointLoss)) := by ring

/-- Coarse tube majorant: data.CΔ ≤ poly * n^7 * δn^{-(εReg+tubeLoss)}. -/
lemma coarse_tube_majorant
    (n : ℕ) (hn_pos : 0 < n)
    (data_CΔ K_B1 C₁ εReg tubeLoss : ℝ)
    (hδn_pos : 0 < δd n)
    (hCΔ_compare : data_CΔ ≤ K_B1 * C₁)
    (hC₁_bound : C₁ ≤ (δd n)^(-(εReg + tubeLoss)))
    (hK_B1_nonneg : 0 ≤ K_B1)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n:ℝ) + 7)^7) :
    data_CΔ ≤ (2700 * 3145728 * (11:ℝ)^7) * (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss)) := by
  have h14 : (4 * (n : ℝ) + 7)^7 ≤ (11 * (n : ℝ))^7 := four_n_plus_seven_le_eleven_n_pow7 hn_pos
  have h17 : (11 * (n : ℝ))^7 = (11 : ℝ)^7 * (n : ℝ)^7 := by ring
  have h14' : (4 * (n : ℝ) + 7)^7 ≤ (11 : ℝ)^7 * (n : ℝ)^7 :=
    le_trans h14 (le_of_eq h17)
  have h_rpow_nonneg : 0 ≤ (δd n)^(-(εReg + tubeLoss)) := Real.rpow_nonneg hδn_pos.le _
  have h31 : K_B1 * C₁ ≤ K_B1 * (δd n)^(-(εReg + tubeLoss)) :=
    mul_le_mul_of_nonneg_left hC₁_bound hK_B1_nonneg
  calc
    data_CΔ ≤ K_B1 * C₁ := hCΔ_compare
    _ ≤ K_B1 * (δd n)^(-(εReg + tubeLoss)) := h31
    _ ≤ (2700 * 3145728 * (4 * (n:ℝ) + 7)^7) * (δd n)^(-(εReg + tubeLoss)) := by gcongr
    _ ≤ (2700 * 3145728 * (11:ℝ)^7) * (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss)) := by
      have h_coeff_nonneg : 0 ≤ (2700 * 3145728 : ℝ) := by positivity
      have h : (2700 * 3145728 * (4 * (n : ℝ) + 7)^7) * (δd n)^(-(εReg + tubeLoss))
          ≤ (2700 * 3145728 * ((11 : ℝ)^7 * (n : ℝ)^7)) * (δd n)^(-(εReg + tubeLoss)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h14' h_coeff_nonneg) h_rpow_nonneg
      have h_eq : (2700 * 3145728 * ((11 : ℝ)^7 * (n : ℝ)^7)) * (δd n)^(-(εReg + tubeLoss)) =
          (2700 * 3145728 * (11:ℝ)^7) * (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss)) := by ring
      rw [h_eq] at h
      exact h

/-- Combined denominator bound for coarse polylog absorption. -/
lemma coarse_denom_bound
    (n : ℕ) (hn_pos : 0 < n)
    (s εReg pointLoss tubeLoss : ℝ)
    (C_coarse_point data_CΔ : ℝ)
    (C_poly_point C_poly_tube C_poly_prop5 : ℝ)
    (h_Ccoarse_bound : C_coarse_point ≤ (162 * (10:ℝ)^50 * 2 * 2700 * 3145728 * 8 * (11:ℝ)^7) * (n:ℝ)^23 * (δd n)^(-(εReg + pointLoss)))
    (h_CΔ_bound : data_CΔ ≤ (2700 * 3145728 * (11:ℝ)^7) * (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss)))
    (hεReg_pos : 0 < εReg) (hpointLoss_pos : 0 < pointLoss) (htubeLoss_pos : 0 < tubeLoss)
    (hδn_pos : 0 < δd n)
    (hδn_lt_one : δd n < 1)
    (hC_coarse_point_nonneg : 0 ≤ C_coarse_point)
    (hdata_CΔ_nonneg : 0 ≤ data_CΔ)
    (hC_poly_point_def : C_poly_point = (162 * (10:ℝ)^50 * 2 * 2700 * 3145728 * 8 * (11:ℝ)^7) + 1)
    (hC_poly_tube_def : C_poly_tube = (2700 * 3145728 * (11:ℝ)^7) + 1)
    (hC_poly_prop5_def : C_poly_prop5 = C_poly_point * C_poly_tube * 13 * (2:ℝ)^s) :
    max C_coarse_point 1 * 13 * max data_CΔ 1 * (2:ℝ)^s ≤
    C_poly_prop5 * (n:ℝ)^30 * (δd n)^(-(2 * εReg + pointLoss + tubeLoss)) := by
  have h22 : 0 < εReg + pointLoss := by linarith
  have h39 : 0 < εReg + tubeLoss := by linarith
  have hδn_le_one : δd n ≤ 1 := hδn_lt_one.le
  have hδn_inv_ge1 : 1 ≤ (δd n)^(-(εReg + pointLoss)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδn_pos hδn_le_one (by linarith)
  have hδn_inv_ge1' : 1 ≤ (δd n)^(-(εReg + tubeLoss)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδn_pos hδn_le_one (by linarith)
  have hn23_ge1 : 1 ≤ (n:ℝ)^23 := one_le_nat_pow hn_pos 23
  have hn7_ge1 : 1 ≤ (n:ℝ)^7 := one_le_nat_pow hn_pos 7
  have h29 : 1 ≤ 1 * (n:ℝ)^23 * (δd n)^(-(εReg + pointLoss)) := by
    have h_pos1 : 0 ≤ (n:ℝ)^23 := by positivity
    have h_pos2 : 0 ≤ (δd n)^(-(εReg + pointLoss)) := Real.rpow_nonneg hδn_pos.le _
    calc 1 ≤ (n:ℝ)^23 := hn23_ge1
      _ ≤ (n:ℝ)^23 * (δd n)^(-(εReg + pointLoss)) := by
        exact le_mul_of_one_le_right h_pos1 hδn_inv_ge1
      _ = 1 * (n:ℝ)^23 * (δd n)^(-(εReg + pointLoss)) := by ring
  have h_CP_prop5_bound : max C_coarse_point 1 ≤ C_poly_point * (n:ℝ)^23 * (δd n)^(-(εReg + pointLoss)) := by
    rw [hC_poly_point_def]
    have h26 : max C_coarse_point 1 ≤ C_coarse_point + 1 := by
      exact max_le (by linarith [hC_coarse_point_nonneg]) (by linarith)
    have h27 : C_coarse_point + 1 ≤
        ((162 * (10:ℝ)^50 * 2 * 2700 * 3145728 * 8 * (11:ℝ)^7) + 1) * (n:ℝ)^23 * (δd n)^(-(εReg + pointLoss)) := by
      linarith [h_Ccoarse_bound, h29]
    exact le_trans h26 h27
  have h38 : 1 ≤ 1 * (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss)) := by
    have h_pos1 : 0 ≤ (n:ℝ)^7 := by positivity
    have h_pos2 : 0 ≤ (δd n)^(-(εReg + tubeLoss)) := Real.rpow_nonneg hδn_pos.le _
    calc 1 ≤ (n:ℝ)^7 := hn7_ge1
      _ ≤ (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss)) := by
        exact le_mul_of_one_le_right h_pos1 hδn_inv_ge1'
      _ = 1 * (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss)) := by ring
  have h_CΔ_prop5_bound : max data_CΔ 1 ≤ C_poly_tube * (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss)) := by
    rw [hC_poly_tube_def]
    have h35 : max data_CΔ 1 ≤ data_CΔ + 1 := by
      exact max_le (by linarith [hdata_CΔ_nonneg]) (by linarith)
    have h36 : data_CΔ + 1 ≤
        ((2700 * 3145728 * (11:ℝ)^7) + 1) * (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss)) := by
      linarith [h_CΔ_bound, h38]
    exact le_trans h35 h36
  have h_pos : 0 ≤ (13 : ℝ) * (2:ℝ)^s := by positivity
  have h_mul : max C_coarse_point 1 * max data_CΔ 1 ≤
      (C_poly_point * (n:ℝ)^23 * (δd n)^(-(εReg + pointLoss))) *
      (C_poly_tube * (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss))) :=
    mul_le_mul h_CP_prop5_bound h_CΔ_prop5_bound (by positivity) (by positivity)
  have h5 : max C_coarse_point 1 * 13 * max data_CΔ 1 * (2:ℝ)^s =
      (max C_coarse_point 1 * max data_CΔ 1) * (13 * (2:ℝ)^s) := by ring
  have h6 : (max C_coarse_point 1 * max data_CΔ 1) * (13 * (2:ℝ)^s) ≤
      ((C_poly_point * (n:ℝ)^23 * (δd n)^(-(εReg + pointLoss))) *
       (C_poly_tube * (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss)))) * (13 * (2:ℝ)^s) :=
    mul_le_mul_of_nonneg_right h_mul h_pos
  have h_rpow : (δd n)^(-(εReg + pointLoss)) * (δd n)^(-(εReg + tubeLoss)) =
      (δd n)^(-(2 * εReg + pointLoss + tubeLoss)) := by
    rw [← Real.rpow_add hδn_pos] <;> ring_nf
  have h_nat_pow : (n:ℝ)^23 * (n:ℝ)^7 = (n:ℝ)^30 := by ring
  have h7 : ((C_poly_point * (n:ℝ)^23 * (δd n)^(-(εReg + pointLoss))) *
       (C_poly_tube * (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss)))) * (13 * (2:ℝ)^s) =
      C_poly_prop5 * (n:ℝ)^30 * (δd n)^(-(2 * εReg + pointLoss + tubeLoss)) := by
    rw [hC_poly_prop5_def]
    calc
      ((C_poly_point * (n:ℝ)^23 * (δd n)^(-(εReg + pointLoss))) *
       (C_poly_tube * (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss)))) * (13 * (2:ℝ)^s)
        = C_poly_point * C_poly_tube * (13 * (2:ℝ)^s) * ((n:ℝ)^23 * (n:ℝ)^7) *
          ((δd n)^(-(εReg + pointLoss)) * (δd n)^(-(εReg + tubeLoss))) := by ring
      _ = C_poly_point * C_poly_tube * (13 * (2:ℝ)^s) * (n:ℝ)^30 *
          (δd n)^(-(2 * εReg + pointLoss + tubeLoss)) := by
        rw [h_nat_pow, h_rpow] <;> ring
      _ = (C_poly_point * C_poly_tube * 13 * (2:ℝ)^s) * (n:ℝ)^30 *
          (δd n)^(-(2 * εReg + pointLoss + tubeLoss)) := by ring
  rw [h5]
  exact le_trans h6 (le_of_eq h7)


/-- Non-negativity of C_point = C_heavy * 9 * K_global, extracted to avoid
    timeout from positivity/dsimp inside the large main theorem body. -/
lemma C_point_nonneg_lemma
    (C_P : ℝ) (hCP_nonneg : 0 ≤ C_P) (N : ℕ)
    (K_global : ℝ) (hK_global_pos : 0 < K_global) :
    0 ≤ (C_P * 18 * (numDyadicLevels N : ℝ)) * 9 * K_global := by
  have h1 : 0 ≤ C_P * 18 * (numDyadicLevels N : ℝ) :=
    mul_nonneg (mul_nonneg hCP_nonneg (by norm_num)) (Nat.cast_nonneg _)
  have h2 : 0 ≤ K_global := hK_global_pos.le
  exact mul_nonneg (mul_nonneg h1 (by norm_num)) h2

/-- Non-negativity of C_coarse_point, extracted to avoid timeout. -/
lemma C_coarse_point_nonneg_lemma
    (C_point R_harbor : ℝ) (u : ℝ)
    (hC_point_nonneg : 0 ≤ C_point)
    (hR_harbor_nonneg : 0 ≤ R_harbor) :
    0 ≤ 162 * C_point * R_harbor * (2 * Real.sqrt 2) ^ u := by
  have h3 : 0 ≤ (2 * Real.sqrt 2) ^ u := Real.rpow_nonneg (by positivity) _
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC_point_nonneg) hR_harbor_nonneg) h3

/-- Non-negativity of data.CΔ from C₁ ≤ K * CΔ and C₁ ≥ 1, K ≥ 1. -/
lemma data_CΔ_nonneg_lemma
    (C₁ K data_CΔ : ℝ) (hC1_ge1 : 1 ≤ C₁) (hK_ge1 : 1 ≤ K)
    (h_compare : C₁ ≤ K * data_CΔ) : 0 ≤ data_CΔ := by
  have hK_pos : 0 < K := by linarith
  have hC1_pos : 0 < C₁ := by linarith
  by_contra h
  have h' : data_CΔ ≤ 0 := by linarith
  have h'' : K * data_CΔ ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) h'
  linarith

/-- Combined non-negativity helper for polylog absorption, extracted to avoid
    tactic timeouts inside the large main theorem body. -/
lemma polylog_nonneg_helper
    (C_point K_B1 : ℝ) (u : ℝ)
    (C₁ data_CΔ : ℝ)
    (hC_point_nonneg : 0 ≤ C_point)
    (hK_B1_ge1 : 1 ≤ K_B1)
    (hC1_ge1 : 1 ≤ C₁)
    (hCΔ_compare2 : C₁ ≤ K_B1 * data_CΔ) :
    (0 ≤ (2 * K_B1)) ∧
    (0 ≤ 162 * C_point * (2 * K_B1) * (2 * Real.sqrt 2) ^ u) ∧
    (0 ≤ data_CΔ) := by
  have hK_B1_nonneg : 0 ≤ K_B1 := le_trans zero_le_one hK_B1_ge1
  have hR_harbor_nonneg : 0 ≤ (2 * K_B1) := mul_nonneg zero_le_two hK_B1_nonneg
  have h3 : 0 ≤ (2 * Real.sqrt 2) ^ u := Real.rpow_nonneg (by positivity) _
  have hC_coarse : 0 ≤ 162 * C_point * (2 * K_B1) * (2 * Real.sqrt 2) ^ u :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC_point_nonneg) hR_harbor_nonneg) h3
  have hdata : 0 ≤ data_CΔ :=
    data_CΔ_nonneg_lemma C₁ K_B1 data_CΔ hC1_ge1 hK_B1_ge1 hCΔ_compare2
  exact ⟨hR_harbor_nonneg, hC_coarse, hdata⟩

/-- Top-level adapter for the coarse coefficient/absorption block.
    All constants are defined internally to avoid rfl timeouts in the large theorem context. -/
lemma coarse_absorption_adapter
    (n m : ℕ) (hn_pos : 0 < n) (h_even : n = 2 * m)
    (K s εReg pointLoss tubeLoss : ℝ)
    (C_point K_B1 u C₁ data_CΔ : ℝ)
    (hu0 : 0 ≤ u) (hu2 : u ≤ 2)
    (loss_coarse δ_prop5 : ℝ)
    -- Majorants
    (h_majorant_point : C_point ≤ (δd n)^(-(εReg + pointLoss)) * (10:ℝ)^50 * (n:ℝ)^16)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n:ℝ) + 7)^7)
    (hC₁_bound : C₁ ≤ (δd n)^(-(εReg + tubeLoss)))
    -- Fields and positivity
    (hK_pos : 0 < K)
    (hs_nonneg : 0 ≤ s)
    (hC_point_nonneg : 0 ≤ C_point)
    (hK_ge1 : 1 ≤ K_B1)
    (hC1_ge1 : 1 ≤ C₁)
    (hCΔ_compare1 : data_CΔ ≤ K_B1 * C₁)
    (hCΔ_compare2 : C₁ ≤ K_B1 * data_CΔ)
    (hεReg_pos : 0 < εReg) (hpointLoss_pos : 0 < pointLoss) (htubeLoss_pos : 0 < tubeLoss)
    (hδn_pos : 0 < δd n) (hδn_lt_one : δd n < 1)
    (hδn_le_prop5 : δd n ≤ δ_prop5)
    -- Absorption spec with explicit constants
    (h_abs_prop5_spec : ∀ (k : ℕ), δd k ≤ δ_prop5 →
        (2^K / K) * Real.log (1 / δd k)^(-K) * (δd k)^(2 * εReg + pointLoss + tubeLoss) /
          (((162 * (10:ℝ)^50 * 2 * 2700 * 3145728 * 8 * (11:ℝ)^7) + 1) *
           ((2700 * 3145728 * (11:ℝ)^7) + 1) * 13 * (2:ℝ)^s *
           (k:ℝ)^30) ≥ (δd k)^loss_coarse) :
    Section6.C_prop5_at_coarse_scale K
      (max (162 * C_point * (2 * K_B1) * (2 * Real.sqrt 2)^u) 1)
      (max data_CΔ 1)
      s (δd m) ≥ (δd n)^loss_coarse := by
  let R_harbor : ℝ := 2 * K_B1
  let C_coarse_point : ℝ := 162 * C_point * R_harbor * (2 * Real.sqrt 2)^u
  let C_P_prop5 : ℝ := max C_coarse_point 1
  let CΔ_prop5 : ℝ := max data_CΔ 1
  let C_poly_point : ℝ := (162 * (10:ℝ)^50 * 2 * 2700 * 3145728 * 8 * (11:ℝ)^7) + 1
  let C_poly_tube : ℝ := (2700 * 3145728 * (11:ℝ)^7) + 1
  let C_poly_prop5 : ℝ := C_poly_point * C_poly_tube * 13 * (2:ℝ)^s
  let a_prop5 : ℝ := 2 * εReg + pointLoss + tubeLoss
  let degree_prop5 : ℕ := 30
  have hK_B1_nonneg : 0 ≤ K_B1 := le_trans zero_le_one hK_ge1
  have hR_harbor_nonneg : 0 ≤ R_harbor := mul_nonneg zero_le_two hK_B1_nonneg
  have hC_coarse_point_nonneg : 0 ≤ C_coarse_point :=
    C_coarse_point_nonneg_lemma C_point R_harbor u hC_point_nonneg hR_harbor_nonneg
  have hdata_CΔ_nonneg : 0 ≤ data_CΔ :=
    data_CΔ_nonneg_lemma C₁ K_B1 data_CΔ hC1_ge1 hK_ge1 hCΔ_compare2
  have h_Ccoarse_bound : C_coarse_point ≤
      (162 * (10:ℝ)^50 * 2 * 2700 * 3145728 * 8 * (11:ℝ)^7) * (n:ℝ)^23 * (δd n)^(-(εReg + pointLoss)) :=
    coarse_point_majorant n hn_pos C_point K_B1 u hu0 hu2 εReg pointLoss hδn_pos
      hC_point_nonneg hK_B1_nonneg h_majorant_point hK_B1_bound
  have h_CΔ_bound : data_CΔ ≤
      (2700 * 3145728 * (11:ℝ)^7) * (n:ℝ)^7 * (δd n)^(-(εReg + tubeLoss)) :=
    coarse_tube_majorant n hn_pos data_CΔ K_B1 C₁ εReg tubeLoss hδn_pos
      hCΔ_compare1 hC₁_bound hK_B1_nonneg hK_B1_bound
  have h_denom_bound0 : max C_coarse_point 1 * 13 * max data_CΔ 1 * (2:ℝ)^s ≤
      C_poly_prop5 * (n:ℝ)^30 * (δd n)^(-(2 * εReg + pointLoss + tubeLoss)) :=
    coarse_denom_bound n hn_pos s εReg pointLoss tubeLoss C_coarse_point data_CΔ
      C_poly_point C_poly_tube C_poly_prop5 h_Ccoarse_bound h_CΔ_bound
      hεReg_pos hpointLoss_pos htubeLoss_pos hδn_pos hδn_lt_one
      hC_coarse_point_nonneg hdata_CΔ_nonneg
      rfl rfl rfl
  have h_denom_bound : C_P_prop5 * 13 * CΔ_prop5 * (2:ℝ)^s ≤
      C_poly_prop5 * (n:ℝ)^degree_prop5 * (δd n)^(-a_prop5) := by
    simpa [C_P_prop5, CΔ_prop5, degree_prop5, a_prop5] using h_denom_bound0
  have hC_poly_prop5_pos : 0 < C_poly_prop5 := by positivity
  have hC_P_prop5_pos : 0 < C_P_prop5 := by
    have h : 1 ≤ C_P_prop5 := by
      simp [C_P_prop5, C_coarse_point, R_harbor] <;> linarith
    linarith
  have hCΔ_prop5_pos : 0 < CΔ_prop5 := by
    have h : 1 ≤ CΔ_prop5 := by
      simp [CΔ_prop5] <;> linarith
    linarith
  exact prop5_polylog_absorption_core
    K C_P_prop5 CΔ_prop5 s n m hK_pos h_even hn_pos
    C_poly_prop5 hC_poly_prop5_pos
    a_prop5 degree_prop5 loss_coarse δ_prop5
    h_abs_prop5_spec
    hδn_le_prop5 hδn_pos hδn_lt_one
    h_denom_bound
    hs_nonneg
    hC_P_prop5_pos hCΔ_prop5_pos

/-- Combined coarse loss ledger adapter: returns all 4 facts about loss_coarse
    and the selector budget in a single top-level call to isolate tactic execution
    from the large main theorem context. -/
lemma coarse_loss_ledger_adapter
    (s t u : ℝ)
    (hs1 : s < 1) (hst : s < t) (hu_t : t ≤ u)
    (εA loss_parent coarseGain netGain localLoss lambda rho_M loss_B1 : ℝ)
    (hεA_pos : 0 < εA)
    (hloss_parent_pos : 0 < loss_parent)
    (hnetGain_pos : 0 < netGain)
    (hbudget : netGain ≤ coarseGain - localLoss - lambda - rho_M - loss_B1 - loss_parent)
    (hcoarseGain_le : coarseGain ≤ εA * ((min t 1 - s) / (1 - s)) / 2)
    (hlocalLoss_pos : 0 < localLoss)
    (hlambda_pos : 0 < lambda)
    (hrho_M_pos : 0 < rho_M)
    (hloss_B1_pos : 0 < loss_B1) :
    let α_base := (min t 1 - s) / (1 - s)
    let α_actual := (min u 1 - s) / (1 - s)
    let coarseGain_raw := εA * α_base / 2
    (0 ≤ loss_parent / 2) ∧
    (loss_parent / 2 < (εA - loss_parent) * α_actual / 2) ∧
    (loss_parent / 2 ≤ loss_parent / 2) ∧
    (netGain ≤ coarseGain_raw - localLoss - lambda - rho_M - loss_B1 - loss_parent) := by
  set α_base : ℝ := (min t 1 - s) / (1 - s) with hα_base_def
  set α_actual : ℝ := (min u 1 - s) / (1 - s) with hα_actual_def
  set coarseGain_raw : ℝ := εA * α_base / 2 with hcoarseGain_raw_def
  have h1s : 0 < 1 - s := by linarith
  have hα_base_pos : 0 < α_base := by
    rw [hα_base_def]
    have h : s < min t 1 := lt_min hst hs1
    have h2 : 0 < min t 1 - s := by linarith
    exact div_pos h2 h1s
  have hα_base_le_one : α_base ≤ 1 := by
    rw [hα_base_def]
    have h : min t 1 ≤ 1 := min_le_right _ _
    have h2 : min t 1 - s ≤ 1 - s := by linarith
    exact (div_le_one h1s).mpr h2
  have h_min_le : min t 1 ≤ min u 1 :=
    min_le_min hu_t (by norm_num)
  have hα_base_le_actual : α_base ≤ α_actual := by
    rw [hα_base_def, hα_actual_def]
    have h2 : min t 1 - s ≤ min u 1 - s := by
      exact sub_le_sub_right h_min_le s
    exact div_le_div_of_nonneg_right h2 (by linarith)
  have h_loss_parent_lt_coarseGain : loss_parent < coarseGain := by
    have h_pos_sum : 0 < localLoss + lambda + rho_M + loss_B1 := by positivity
    have h : coarseGain - (localLoss + lambda + rho_M + loss_B1) - loss_parent > 0 := by
      have h2 : netGain ≤ coarseGain - localLoss - lambda - rho_M - loss_B1 - loss_parent := hbudget
      have h3 : 0 < netGain := hnetGain_pos
      have h4 : 0 < coarseGain - localLoss - lambda - rho_M - loss_B1 - loss_parent :=
        lt_of_lt_of_le h3 h2
      simpa [sub_sub] using h4
    have h5 : coarseGain - (localLoss + lambda + rho_M + loss_B1) > loss_parent := by linarith
    have h6 : coarseGain > localLoss + lambda + rho_M + loss_B1 + loss_parent := by linarith
    linarith
  have h_loss_parent_lt_half : loss_parent < εA * α_base / 2 :=
    lt_of_lt_of_le h_loss_parent_lt_coarseGain hcoarseGain_le
  have h_α_actual_pos : 0 < α_actual :=
    lt_of_lt_of_le hα_base_pos hα_base_le_actual
  have h_half_nonneg : 0 ≤ 1 - α_base / 2 := by
    have h : α_base ≤ 1 := hα_base_le_one
    linarith
  have h12 : 0 ≤ εA * (1 - α_base / 2) :=
    mul_nonneg hεA_pos.le h_half_nonneg
  have h_half_ge : 1 - α_base / 2 ≥ 1 / 2 := by
    have h : α_base ≤ 1 := hα_base_le_one
    linarith
  have h10 : εA * (1 - α_base / 2) * α_actual ≥ εA * α_base / 2 := by
    have h11 : α_actual ≥ α_base := hα_base_le_actual
    have h17 : εA * (1 - α_base / 2) * α_actual ≥ εA * (1 - α_base / 2) * α_base :=
      mul_le_mul_of_nonneg_left h11 h12
    have h18 : εA * (1 - α_base / 2) * α_base ≥ εA * α_base / 2 := by
      have h19 : 0 ≤ εA * α_base := by positivity
      calc εA * (1 - α_base / 2) * α_base
        = εA * α_base * (1 - α_base / 2) := by ring
      _ ≥ εA * α_base * (1 / 2 : ℝ) := by gcongr <;> linarith
      _ = εA * α_base / 2 := by ring
    calc εA * (1 - α_base / 2) * α_actual
      ≥ εA * (1 - α_base / 2) * α_base := h17
    _ ≥ εA * α_base / 2 := h18
  have h9 : εA - loss_parent > εA * (1 - α_base / 2) := by
    have h21 : loss_parent < εA * α_base / 2 := h_loss_parent_lt_half
    have h22 : εA * (1 - α_base / 2) = εA - εA * α_base / 2 := by ring
    rw [h22]
    linarith
  have h_main : (εA - loss_parent) * α_actual > loss_parent := by
    have h23 : 0 < α_actual := h_α_actual_pos
    have h24 : (εA - loss_parent) * α_actual > εA * (1 - α_base / 2) * α_actual :=
      mul_lt_mul_of_pos_right h9 h23
    calc (εA - loss_parent) * α_actual
      > εA * (1 - α_base / 2) * α_actual := h24
    _ ≥ εA * α_base / 2 := h10
    _ > loss_parent := h_loss_parent_lt_half
  have h_small : loss_parent / 2 < (εA - loss_parent) * α_actual / 2 := by
    have h27 : 0 < (2 : ℝ) := by norm_num
    exact div_lt_div_of_pos_right h_main h27
  have h_nonneg : 0 ≤ loss_parent / 2 := by
    have h28 : 0 ≤ loss_parent := by linarith [hloss_parent_pos]
    exact div_nonneg h28 (by norm_num)
  have h_le_half : loss_parent / 2 ≤ loss_parent / 2 := by rfl
  have h_cg_le : coarseGain ≤ coarseGain_raw := by
    rw [hcoarseGain_raw_def]
    exact hcoarseGain_le
  have h_selector : netGain ≤ coarseGain_raw - localLoss - lambda - rho_M - loss_B1 - loss_parent := by
    have h29 : netGain ≤ coarseGain - localLoss - lambda - rho_M - loss_B1 - loss_parent := hbudget
    have h30 : coarseGain ≤ coarseGain_raw := h_cg_le
    linarith
  exact ⟨h_nonneg, h_small, h_le_half, h_selector⟩

/-- Extract hnm_ge2: n=2m and δn ≤ 1/8 implies n-m=m ≥ 2. -/
lemma hnm_ge2_adapter
    (n m : ℕ) (h_even : n = 2 * m)
    (hδn_le_eighth : δd n ≤ 1 / 8) :
    2 ≤ n - m := by
  have h_eq : δd n = 1 / (2 ^ n : ℝ) := dyadicDelta_eq_inv_pow n
  have h1 : (2 ^ n : ℝ) ≥ 8 := by
    rw [h_eq] at hδn_le_eighth
    have h_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
    have h2 : 1 / (2 ^ n : ℝ) ≤ 1 / 8 := hδn_le_eighth
    have h3 : (2 ^ n : ℝ) ≥ 8 := by
      calc (2 ^ n : ℝ)
        = 1 / (1 / (2 ^ n : ℝ)) := by field_simp [h_pos.ne'] <;> ring
      _ ≥ 1 / (1 / 8 : ℝ) := by gcongr
      _ = 8 := by norm_num
    exact h3
  have h4 : n ≥ 3 := by
    by_contra h5
    have h6 : n < 3 := by linarith
    have h7 : 2 ^ n < 2 ^ 3 := Nat.pow_lt_pow_right (by norm_num) h6
    have h8 : (2 ^ n : ℝ) < 8 := by exact_mod_cast h7
    linarith
  have h9 : 2 * m ≥ 3 := by
    have h10 : n = 2 * m := h_even
    linarith
  have h11 : m ≥ 2 := by
    by_contra h12
    have h13 : m ≤ 1 := by linarith
    have h14 : 2 * m ≤ 2 := by
      calc 2 * m ≤ 2 * 1 := by gcongr
        _ = 2 := by norm_num
    linarith
  have h15 : n - m = m := by omega
  rw [h15]
  exact h11

/-- Fine chain C_P majorant: C_P * 18 * numDyadicLevels(N) ≤ 10^8 * n * δn^{-(εReg+pointLoss)}. -/
lemma fine_chain_CP_majorant_adapter
    (n : ℕ) (hn_pos : 0 < n)
    (N : ℕ) (hN_le : N ≤ 4^n)
    (C_P εReg pointLoss : ℝ)
    (hC_P_bound : C_P ≤ (10 : ℝ)^6 * (δd n)^(-(εReg + pointLoss)))
    (hδn_pos : 0 < δd n) :
    C_P * 18 * (numDyadicLevels N : ℝ) ≤
      (10 : ℝ)^8 * (n : ℝ) * (δd n)^(-(εReg + pointLoss)) := by
  have h_num_levels : numDyadicLevels N ≤ 2 * n + 2 :=
    numDyadicLevels_le_linear hN_le
  have h_n_ge1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn_pos
  have h_2n2_le_4n : (2 * (n : ℝ) + 2) ≤ 4 * (n : ℝ) := by
    have h : 1 ≤ (n : ℝ) := h_n_ge1
    linarith
  have h1 : C_P ≤ (10 : ℝ)^6 * (δd n)^(-(εReg + pointLoss)) := hC_P_bound
  have h2 : (numDyadicLevels N : ℝ) ≤ 2 * (n : ℝ) + 2 := by
    exact_mod_cast h_num_levels
  have h_coeff : (10 : ℝ)^6 * 18 * 4 ≤ (10 : ℝ)^8 := by norm_num
  have h_pos : 0 ≤ (n : ℝ) * (δd n)^(-(εReg + pointLoss)) := by positivity
  calc C_P * 18 * (numDyadicLevels N : ℝ)
    ≤ (10 : ℝ)^6 * (δd n)^(-(εReg + pointLoss)) * 18 * (2 * (n : ℝ) + 2) := by gcongr
  _ ≤ (10 : ℝ)^6 * (δd n)^(-(εReg + pointLoss)) * 18 * (4 * (n : ℝ)) := by gcongr
  _ = (10 : ℝ)^6 * 18 * 4 * ((n : ℝ) * (δd n)^(-(εReg + pointLoss))) := by ring
  _ ≤ (10 : ℝ)^8 * ((n : ℝ) * (δd n)^(-(εReg + pointLoss))) := mul_le_mul_of_nonneg_right h_coeff h_pos
  _ = (10 : ℝ)^8 * (n : ℝ) * (δd n)^(-(εReg + pointLoss)) := by ring

/-- Fine chain K_global majorant: K_global ≤ 2 * (2700 * 3145728 * 11^7)^2 * n^14. -/
lemma fine_chain_Kglobal_majorant_adapter
    (n : ℕ) (hn_pos : 0 < n)
    (K_global K_B1 : ℝ)
    (hK_B1_ge1 : 1 ≤ K_B1)
    (hK_global_bound : K_global ≤ 2 * K_B1^2)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7) :
    K_global ≤ (2 * (2700 * 3145728 * (11:ℝ)^7)^2) * (n : ℝ)^14 := by
  have h_4n7_le_11n : (4 * (n : ℝ) + 7) ≤ 11 * (n : ℝ) := by
    have h : (n : ℝ) ≥ 1 := by exact_mod_cast hn_pos
    linarith
  have hK_B1_nonneg : 0 ≤ K_B1 := by linarith
  have h_rhs_nonneg : 0 ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7 := by positivity
  have h2 : K_B1^2 ≤ (2700 * 3145728 * (4 * (n : ℝ) + 7)^7)^2 := by
    gcongr
  calc K_global
    ≤ 2 * K_B1^2 := hK_global_bound
  _ ≤ 2 * (2700 * 3145728 * (4 * (n : ℝ) + 7)^7)^2 := by exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  _ = 2 * (2700 * 3145728)^2 * (4 * (n : ℝ) + 7)^14 := by ring
  _ ≤ 2 * (2700 * 3145728)^2 * (11 * (n : ℝ))^14 := by gcongr
  _ = 2 * (2700 * 3145728 * (11:ℝ)^7)^2 * (n : ℝ)^14 := by ring

/-- Fine chain CP complete: combines CP majorant + polynomial absorption into final bound. -/
lemma fine_chain_CP_complete_adapter
    (n : ℕ)
    (C_point_chain C_fine_point_poly εReg pointLoss finePointPolyLoss pointRegularityLoss : ℝ)
    (δn : ℝ) (hδn_pos : 0 < δn)
    (h_CP_majorant : C_point_chain ≤ (10 : ℝ)^8 * (n : ℝ) * δn^(-(εReg + pointLoss)))
    (h_fine_point_abs_raw : C_fine_point_poly * (n : ℝ)^1 ≤ δn^(-finePointPolyLoss))
    (hpointRegularityLoss_eq : pointRegularityLoss = εReg + pointLoss + finePointPolyLoss)
    (h_eq : C_fine_point_poly = (10 : ℝ)^8) :
    C_point_chain ≤ δn^(-pointRegularityLoss) := by
  have h_fine_point_abs : C_fine_point_poly * (n : ℝ) ≤ δn^(-finePointPolyLoss) := by
    have h6 : (n : ℝ)^1 = (n : ℝ) := pow_one (n : ℝ)
    have h7 : C_fine_point_poly * (n : ℝ)^1 = C_fine_point_poly * (n : ℝ) := by rw [h6]
    rw [h7] at h_fine_point_abs_raw
    exact h_fine_point_abs_raw
  rw [hpointRegularityLoss_eq]
  have h1 : C_point_chain ≤ C_fine_point_poly * (n : ℝ) * δn^(-(εReg + pointLoss)) := by
    rw [h_eq]
    exact h_CP_majorant
  have h_pos : 0 ≤ δn^(-(εReg + pointLoss)) := by positivity
  have h2 : C_point_chain ≤ δn^(-finePointPolyLoss) * δn^(-(εReg + pointLoss)) := by
    calc C_point_chain
      ≤ C_fine_point_poly * (n : ℝ) * δn^(-(εReg + pointLoss)) := h1
      _ = (C_fine_point_poly * (n : ℝ)) * δn^(-(εReg + pointLoss)) := by ring
      _ ≤ δn^(-finePointPolyLoss) * δn^(-(εReg + pointLoss)) := mul_le_mul_of_nonneg_right h_fine_point_abs h_pos
  have h3 : δn^(-finePointPolyLoss) * δn^(-(εReg + pointLoss)) = δn^(-(εReg + pointLoss + finePointPolyLoss)) := by
    have h31 : δn^(-finePointPolyLoss) * δn^(-(εReg + pointLoss)) = δn^((-finePointPolyLoss) + (-(εReg + pointLoss))) :=
      (Real.rpow_add hδn_pos (-finePointPolyLoss) (-(εReg + pointLoss))).symm
    have h32 : (-finePointPolyLoss) + (-(εReg + pointLoss)) = -(εReg + pointLoss + finePointPolyLoss) := by ring
    rw [h32] at h31
    exact h31
  rw [h3] at h2
  exact h2

/-- Fine chain Kglobal complete: combines Kglobal majorant + polynomial absorption. -/
lemma fine_chain_Kglobal_complete_adapter
    (n : ℕ) (hn_pos : 0 < n)
    (K_global K_B1 C_fine_global_poly fineGlobalPolyLoss : ℝ)
    (δn : ℝ) (hδn_pos : 0 < δn)
    (hK_B1_ge1 : 1 ≤ K_B1)
    (hK_global_bound : K_global ≤ 2 * K_B1^2)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7)
    (h_abs_fine_global : C_fine_global_poly * (n : ℝ)^14 ≤ δn^(-fineGlobalPolyLoss))
    (h_C_fine_global_eq : C_fine_global_poly = 2 * (2700 * 3145728 * (11:ℝ)^7)^2) :
    K_global ≤ δn^(-fineGlobalPolyLoss) := by
  have h_Kglobal_majorant : K_global ≤ C_fine_global_poly * (n : ℝ)^14 := by
    have h := fine_chain_Kglobal_majorant_adapter n hn_pos K_global K_B1 hK_B1_ge1 hK_global_bound hK_B1_bound
    rw [h_C_fine_global_eq]
    exact h
  exact le_trans h_Kglobal_majorant h_abs_fine_global

/-- Final fine chains adapter: NO equality hypotheses, all constants hardcoded. -/
lemma fine_chains_final_adapter
    (n : ℕ) (hn_pos : 0 < n)
    (δn : ℝ) (hδn_pos : 0 < δn)
    (C_point_chain εReg pointLoss finePointPolyLoss pointRegularityLoss : ℝ)
    (h_CP_majorant : C_point_chain ≤ (10 : ℝ)^8 * (n : ℝ) * δn^(-(εReg + pointLoss)))
    (hpointRegularityLoss_eq : pointRegularityLoss = εReg + pointLoss + finePointPolyLoss)
    (h_abs_fine_point : (10 : ℝ)^8 * (n : ℝ)^1 ≤ δn^(-finePointPolyLoss))
    (K_global K_B1 : ℝ)
    (hK_B1_ge1 : 1 ≤ K_B1)
    (hK_global_bound : K_global ≤ 2 * K_B1^2)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7)
    (fineGlobalPolyLoss : ℝ)
    (h_abs_fine_global : (2 * (2700 * 3145728 * (11:ℝ)^7)^2) * (n : ℝ)^14 ≤ δn^(-fineGlobalPolyLoss)) :
    (C_point_chain ≤ δn^(-pointRegularityLoss)) ∧ (K_global ≤ δn^(-fineGlobalPolyLoss)) := by
  have h_fine_point_abs : (10 : ℝ)^8 * (n : ℝ) ≤ δn^(-finePointPolyLoss) := by
    have h6 : (n : ℝ)^1 = (n : ℝ) := pow_one (n : ℝ)
    have h7 : (10 : ℝ)^8 * (n : ℝ)^1 = (10 : ℝ)^8 * (n : ℝ) := by rw [h6]
    rw [h7] at h_abs_fine_point
    exact h_abs_fine_point
  have h_CP : C_point_chain ≤ δn^(-pointRegularityLoss) := by
    rw [hpointRegularityLoss_eq]
    have h_pos : 0 ≤ δn^(-(εReg + pointLoss)) := by positivity
    have h2 : C_point_chain ≤ δn^(-finePointPolyLoss) * δn^(-(εReg + pointLoss)) := by
      calc C_point_chain
        ≤ (10 : ℝ)^8 * (n : ℝ) * δn^(-(εReg + pointLoss)) := h_CP_majorant
        _ = ((10 : ℝ)^8 * (n : ℝ)) * δn^(-(εReg + pointLoss)) := by ring
        _ ≤ δn^(-finePointPolyLoss) * δn^(-(εReg + pointLoss)) := mul_le_mul_of_nonneg_right h_fine_point_abs h_pos
    have h31 : δn^(-finePointPolyLoss) * δn^(-(εReg + pointLoss)) = δn^((-finePointPolyLoss) + (-(εReg + pointLoss))) :=
      (Real.rpow_add hδn_pos (-finePointPolyLoss) (-(εReg + pointLoss))).symm
    have h32 : (-finePointPolyLoss) + (-(εReg + pointLoss)) = -(εReg + pointLoss + finePointPolyLoss) := by ring
    rw [h31, h32] at h2
    exact h2
  have h_Kglobal_majorant : K_global ≤ (2 * (2700 * 3145728 * (11:ℝ)^7)^2) * (n : ℝ)^14 :=
    fine_chain_Kglobal_majorant_adapter n hn_pos K_global K_B1 hK_B1_ge1 hK_global_bound hK_B1_bound
  have h_Kg : K_global ≤ δn^(-fineGlobalPolyLoss) :=
    le_trans h_Kglobal_majorant h_abs_fine_global
  exact ⟨h_CP, h_Kg⟩

/-- Helper: 1 ≤ δn^{-b} when 0 < δn ≤ 1 and b > 0. -/
lemma one_le_neg_rpow (δn : ℝ) (hδn_pos : 0 < δn) (hδn_le1 : δn ≤ 1)
    (b : ℝ) (hb_pos : 0 < b) : (1 : ℝ) ≤ δn^(-b) := by
  have h5 : -b ≤ 0 := by linarith
  have h6 : δn^(-b) ≥ (1 : ℝ)^(-b) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hδn_le1 h5
  simpa using h6

/-- Fine chain CQ complete: proves CQ_val ≤ δn^{-b_fine} from raw bounds. -/
lemma fine_chain_CQ_complete_adapter
    (n : ℕ) (hn_pos : 0 < n)
    (δn : ℝ) (hδn_pos : 0 < δn)
    (CQ_val K_B1 C₁ : ℝ)
    (h_CQ_raw : CQ_val ≤ K_B1 * C₁)
    (hK_B1_nonneg : 0 ≤ K_B1)
    (hC₁_nonneg : 0 ≤ C₁)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7)
    (εReg tubeLoss fineCQPolyLoss b_fine : ℝ)
    (hC₁_bound : C₁ ≤ δn^(-(εReg + tubeLoss)))
    (hb_fine_eq : b_fine = εReg + tubeLoss + fineCQPolyLoss)
    (h_abs_fine_CQ : (2700 * 3145728 * (11:ℝ)^7) * (n : ℝ)^7 ≤ δn^(-fineCQPolyLoss)) :
    CQ_val ≤ δn^(-b_fine) := by
  set C_fine_CQ_poly : ℝ := 2700 * 3145728 * (11:ℝ)^7 with hC_fine_CQ_def
  have h_4n7_le_11n : (4 * (n : ℝ) + 7) ≤ 11 * (n : ℝ) := by
    have h : (n : ℝ) ≥ 1 := by exact_mod_cast hn_pos
    linarith
  have h_majorant : CQ_val ≤ C_fine_CQ_poly * (n : ℝ)^7 * δn^(-(εReg + tubeLoss)) := by
    calc CQ_val
      ≤ K_B1 * C₁ := h_CQ_raw
      _ ≤ (2700 * 3145728 * (4 * (n : ℝ) + 7)^7) * C₁ := by
        exact mul_le_mul_of_nonneg_right hK_B1_bound hC₁_nonneg
      _ ≤ (2700 * 3145728 * (4 * (n : ℝ) + 7)^7) * δn^(-(εReg + tubeLoss)) := by
        exact mul_le_mul_of_nonneg_left hC₁_bound (by positivity)
      _ ≤ (2700 * 3145728 * (11 * (n : ℝ))^7) * δn^(-(εReg + tubeLoss)) := by
        gcongr <;> linarith
      _ = C_fine_CQ_poly * (n : ℝ)^7 * δn^(-(εReg + tubeLoss)) := by
        rw [hC_fine_CQ_def]
        <;> ring_nf <;> ring
  have h_pos : 0 ≤ δn^(-(εReg + tubeLoss)) := by positivity
  have h_bound : CQ_val ≤ δn^(-fineCQPolyLoss) * δn^(-(εReg + tubeLoss)) := by
    calc CQ_val
      ≤ C_fine_CQ_poly * (n : ℝ)^7 * δn^(-(εReg + tubeLoss)) := h_majorant
      _ = (C_fine_CQ_poly * (n : ℝ)^7) * δn^(-(εReg + tubeLoss)) := by ring
      _ ≤ δn^(-fineCQPolyLoss) * δn^(-(εReg + tubeLoss)) := mul_le_mul_of_nonneg_right h_abs_fine_CQ h_pos
  have h31 : δn^(-fineCQPolyLoss) * δn^(-(εReg + tubeLoss)) = δn^((-fineCQPolyLoss) + (-(εReg + tubeLoss))) :=
    (Real.rpow_add hδn_pos (-fineCQPolyLoss) (-(εReg + tubeLoss))).symm
  have h32 : (-fineCQPolyLoss) + (-(εReg + tubeLoss)) = -(εReg + tubeLoss + fineCQPolyLoss) := by ring
  rw [hb_fine_eq]
  rw [h31, h32] at h_bound
  exact h_bound

/-- Fine chain CQ max adapter: proves max(CQ_val,1) ≤ δn^{-b_fine}, handling all internal steps. -/
lemma fine_chain_CQ_max_adapter
    (n : ℕ) (hn_pos : 0 < n)
    (δn : ℝ) (hδn_pos : 0 < δn) (hδn_le1 : δn ≤ 1)
    (CQ_val K_B1 C₁ εReg tubeLoss fineCQPolyLoss b_fine : ℝ)
    (hK_B1_nonneg : 0 ≤ K_B1)
    (hC₁_nonneg : 0 ≤ C₁)
    (h_CQ_raw : CQ_val ≤ K_B1 * C₁)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7)
    (hC₁_bound : C₁ ≤ δn^(-(εReg + tubeLoss)))
    (hb_fine_eq : b_fine = εReg + tubeLoss + fineCQPolyLoss)
    (hεReg_pos : 0 < εReg)
    (htubeLoss_pos : 0 < tubeLoss)
    (hfineCQPolyLoss_pos : 0 < fineCQPolyLoss)
    (h_abs_fine_CQ : (2700 * 3145728 * (11:ℝ)^7) * (n : ℝ)^7 ≤ δn^(-fineCQPolyLoss)) :
    max CQ_val 1 ≤ δn^(-b_fine) := by
  have h_CQ_bound : CQ_val ≤ δn^(-b_fine) :=
    fine_chain_CQ_complete_adapter n hn_pos δn hδn_pos CQ_val K_B1 C₁
      h_CQ_raw hK_B1_nonneg hC₁_nonneg hK_B1_bound εReg tubeLoss fineCQPolyLoss b_fine
      hC₁_bound hb_fine_eq h_abs_fine_CQ
  have hbf_pos : 0 < b_fine := by
    rw [hb_fine_eq]
    exact add_pos (add_pos hεReg_pos htubeLoss_pos) hfineCQPolyLoss_pos
  have h1_le_bound : (1 : ℝ) ≤ δn^(-b_fine) :=
    one_le_neg_rpow δn hδn_pos hδn_le1 b_fine hbf_pos
  exact max_le h_CQ_bound h1_le_bound

/-- RETAINED S-SET TRANSFER — canonical version from ember/retained_sset_transfer.lean

    Transfer IsDeltaSSet from a superset S to a subset S', given a cardinality
    ratio and the 5-fold packing bound for DyadicTubes. -/
lemma retained_sset_transfer
    {n : ℕ} {s C₁ K : ℝ}
    {S S' : Finset (DiscretisedFurstenbergEstimate.DyadicTube n)}
    (hS : IsDeltaSSet (DiscretisedFurstenbergEstimate.dyadicDelta n) s C₁ (S : Set (DiscretisedFurstenbergEstimate.DyadicTube n)))
    (hS'_sub : S' ⊆ S)
    (h_card_ratio : (S.card : ENNReal) ≤ ENNReal.ofReal K * (S'.card : ENNReal))
    (hK_pos : 0 < K)
    (hC₁_pos : 0 < C₁)
    (hs_nonneg : 0 ≤ s)
    (hS'_nonempty : S'.Nonempty) :
    IsDeltaSSet (DiscretisedFurstenbergEstimate.dyadicDelta n) s (5 * K * C₁) (S' : Set (DiscretisedFurstenbergEstimate.DyadicTube n)) := by
  let δ : ℝ := DiscretisedFurstenbergEstimate.dyadicDelta n
  have hδ_pos : 0 < δ := DiscretisedFurstenbergEstimate.dyadicDelta_pos n
  let NcoverS := Metric.externalCoveringNumber δ.toNNReal (S : Set (DiscretisedFurstenbergEstimate.DyadicTube n))
  let NcoverS' := Metric.externalCoveringNumber δ.toNNReal (S' : Set (DiscretisedFurstenbergEstimate.DyadicTube n))
  have h_self_cover : Metric.IsCover δ.toNNReal (S : Set (DiscretisedFurstenbergEstimate.DyadicTube n)) (S : Set (DiscretisedFurstenbergEstimate.DyadicTube n)) := by
    intro x hx
    exact ⟨x, hx, by simp [Metric.mem_closedBall]⟩
  have hNcover_S_le_card : (NcoverS : ENNReal) ≤ (S.card : ENNReal) := by
    have h1 : NcoverS ≤ (S : Set (DiscretisedFurstenbergEstimate.DyadicTube n)).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h_self_cover
    have h2 : (S : Set (DiscretisedFurstenbergEstimate.DyadicTube n)).encard = (S.card : ENNReal) := by simp
    have h3 : (NcoverS : ENNReal) ≤ ((S : Set (DiscretisedFurstenbergEstimate.DyadicTube n)).encard : ENNReal) := by exact_mod_cast h1
    rw [h2] at h3
    exact h3
  have h_five_cover : (S'.card : ENNReal) ≤ (5 : ENNReal) * (NcoverS' : ENNReal) := by
    have h := DiscretisedFurstenbergEstimate.InductionOnScales.card_le_five_cover S'
    have h2 : (S' : Set (DiscretisedFurstenbergEstimate.DyadicTube n)).encard = (S'.card : ENNReal) := by simp
    have h3 : ((S' : Set (DiscretisedFurstenbergEstimate.DyadicTube n)).encard : ENNReal) ≤ (5 : ENNReal) * (NcoverS' : ENNReal) := by exact_mod_cast h
    rw [h2] at h3
    exact h3
  have hNcover_S_le : NcoverS ≤ (5 : ENNReal) * ENNReal.ofReal K * NcoverS' := by
    calc NcoverS
      ≤ (S.card : ENNReal) := hNcover_S_le_card
    _ ≤ ENNReal.ofReal K * (S'.card : ENNReal) := h_card_ratio
    _ ≤ ENNReal.ofReal K * ((5 : ENNReal) * NcoverS') := by gcongr
    _ = (5 : ENNReal) * ENNReal.ofReal K * NcoverS' := by ring
  let C' : ℝ := 5 * K * C₁
  have hC'_pos : 0 < C' := by
    dsimp only [C'] <;> positivity
  have h_const_eq : ENNReal.ofReal C₁ * ((5 : ENNReal) * ENNReal.ofReal K) = ENNReal.ofReal C' := by
    have h_pos1 : 0 ≤ K := by linarith
    have h_pos2 : 0 ≤ C₁ := by linarith
    have h1 : ENNReal.ofReal C₁ * ((5 : ENNReal) * ENNReal.ofReal K) =
        (5 : ENNReal) * (ENNReal.ofReal K * ENNReal.ofReal C₁) := by ring
    rw [h1]
    have h2 : ENNReal.ofReal K * ENNReal.ofReal C₁ = ENNReal.ofReal (K * C₁) := by
      rw [←ENNReal.ofReal_mul h_pos1] <;> rfl
    rw [h2]
    have h3 : (5 : ENNReal) * ENNReal.ofReal (K * C₁) = ENNReal.ofReal (5 * (K * C₁)) := by
      have h_mul2 : ENNReal.ofReal ((5 : ℝ) * (K * C₁)) =
          ENNReal.ofReal (5 : ℝ) * ENNReal.ofReal (K * C₁) :=
        ENNReal.ofReal_mul (by norm_num)
      have h5 : ENNReal.ofReal (5 : ℝ) = (5 : ENNReal) := by norm_cast
      simpa [h5] using h_mul2.symm
    rw [h3]
    have h4 : 5 * (K * C₁) = C' := by simp [C'] <;> ring
    rw [h4]
  have h_main : ∀ (x : DiscretisedFurstenbergEstimate.DyadicTube n) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal ((S' : Set (DiscretisedFurstenbergEstimate.DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * (NcoverS' : ENNReal) := by
    intro x r hr
    have h_sub1 : (S' : Set (DiscretisedFurstenbergEstimate.DyadicTube n)) ∩ Metric.closedBall x r ⊆
        (S : Set (DiscretisedFurstenbergEstimate.DyadicTube n)) ∩ Metric.closedBall x r := by
      intro y hy
      exact ⟨hS'_sub hy.1, hy.2⟩
    have hNcover_mono : (Metric.externalCoveringNumber δ.toNNReal ((S' : Set (DiscretisedFurstenbergEstimate.DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal ((S : Set (DiscretisedFurstenbergEstimate.DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub1
    have hS_cond := hS.2.2.2.2 x r hr
    have h3 : (Metric.externalCoveringNumber δ.toNNReal ((S : Set (DiscretisedFurstenbergEstimate.DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C₁ * (ENNReal.ofReal r) ^ s * (NcoverS : ENNReal) := hS_cond
    have h4 : (Metric.externalCoveringNumber δ.toNNReal ((S : Set (DiscretisedFurstenbergEstimate.DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C₁ * (ENNReal.ofReal r) ^ s * ((5 : ENNReal) * ENNReal.ofReal K * NcoverS') := by
      calc (Metric.externalCoveringNumber δ.toNNReal ((S : Set (DiscretisedFurstenbergEstimate.DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal)
        ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal r) ^ s * (NcoverS : ENNReal) := h3
      _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal r) ^ s * ((5 : ENNReal) * ENNReal.ofReal K * NcoverS') := by
          gcongr <;> exact hNcover_S_le
    have h5 : ENNReal.ofReal C₁ * (ENNReal.ofReal r) ^ s * ((5 : ENNReal) * ENNReal.ofReal K * NcoverS') =
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * (NcoverS' : ENNReal) := by
      have h6 : ENNReal.ofReal C₁ * ((5 : ENNReal) * ENNReal.ofReal K) = ENNReal.ofReal C' := h_const_eq
      rw [show ENNReal.ofReal C₁ * (ENNReal.ofReal r) ^ s * ((5 : ENNReal) * ENNReal.ofReal K * NcoverS') =
          (ENNReal.ofReal C₁ * ((5 : ENNReal) * ENNReal.ofReal K)) * ((ENNReal.ofReal r) ^ s * NcoverS') by ring]
      rw [h6] <;> ring
    rw [h5] at h4
    exact le_trans hNcover_mono h4
  exact ⟨hS'_nonempty, hδ_pos, hC'_pos, hs_nonneg, h_main⟩

/-- Helper: convert a real cardinality ratio to ENNReal. -/
lemma card_ratio_to_ennreal
    {n : ℕ} {S S' : Finset (DiscretisedFurstenbergEstimate.DyadicTube n)} {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (h : (S.card : ℝ) ≤ K * (S'.card : ℝ)) :
    (S.card : ENNReal) ≤ ENNReal.ofReal K * (S'.card : ENNReal) := by
  have h2 : ENNReal.ofReal (S.card : ℝ) ≤ ENNReal.ofReal (K * (S'.card : ℝ)) :=
    ENNReal.ofReal_le_ofReal h
  have h3 : ENNReal.ofReal (S.card : ℝ) = (S.card : ENNReal) :=
    ENNReal.ofReal_natCast S.card
  have h4 : ENNReal.ofReal (K * (S'.card : ℝ)) =
      ENNReal.ofReal K * (S'.card : ENNReal) := by
    rw [ENNReal.ofReal_mul hK_nonneg]
    rw [ENNReal.ofReal_natCast S'.card]
  rw [h3, h4] at h2
  exact h2

/-- Retained S-set from B1 data. Given heavy config and B1InductionData,
    for any retained square q, the retained tube family is an IsDeltaSSet
    with constant 5 * data.K * C₁. -/
lemma retained_sset_from_b1_data
    {n m : ℕ} {hnm : m ≤ n}
    {s t C₁ : ℝ} {M : ℕ}
    {config_heavy : CTNiceConfiguration n s C₁ M}
    {data : DirecretisedFurstenbergEstimate.Section6.B1InductionData n m hnm s t C₁ M config_heavy}
    (q : DSq n) (hq : q ∈ data.P)
    (hC₁ : 1 ≤ C₁) (hs : 0 < s) :
    IsDeltaSSet (δd n) s (5 * data.K * C₁)
      (data.tubeFamily q hq : Set (DTb n)) := by
  let S' : Finset (DTb n) := data.tubeFamily q hq
  let S : Finset (DTb n) := config_heavy.tubeFamily q (data.hP_sub hq)
  have h_sub : (S' : Set (DTb n)) ⊆ (S : Set (DTb n)) := data.h_tube_sub q hq
  have hS : IsDeltaSSet (δd n) s C₁ (S : Set (DTb n)) :=
    config_heavy.h_delta_s_set q (data.hP_sub hq)
  have h_card_S : S.card = M := by
    simpa [S] using config_heavy.h_size q (data.hP_sub hq)
  have hM_le : (M : ℝ) ≤ data.K * (S'.card : ℝ) := data.h_tube_size q hq
  have hK_pos : 0 < data.K := lt_of_lt_of_le (by norm_num) data.hK_ge1
  have hC₁_pos : 0 < C₁ := lt_of_lt_of_le (by norm_num) hC₁
  have hs_nonneg : 0 ≤ s := le_of_lt hs
  have hK_nonneg : 0 ≤ data.K := le_of_lt hK_pos
  have hS'_nonempty : S'.Nonempty := by
    have hM_pos : 0 < M := by
      have h1 : S.Nonempty := hS.1
      have h2 : 0 < S.card := Finset.Nonempty.card_pos h1
      rw [←h_card_S] <;> exact h2
    by_contra h
    have h0 : S'.card = 0 := by
      simpa [Finset.not_nonempty_iff_eq_empty] using h
    rw [h0] at hM_le
    have h_contra : (M : ℝ) ≤ 0 := by simpa using hM_le
    have h_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
    exact False.elim (not_le.mpr h_pos h_contra)
  have h_card_ratio : (S.card : ENNReal) ≤ ENNReal.ofReal data.K * (S'.card : ENNReal) := by
    have h1 : (S.card : ℝ) ≤ data.K * (S'.card : ℝ) := by
      rw [h_card_S] <;> exact hM_le
    exact card_ratio_to_ennreal hK_nonneg h1
  exact retained_sset_transfer hS h_sub h_card_ratio hK_pos hC₁_pos hs_nonneg hS'_nonempty

/-- Tube constant majorant: max 1 (10 * C_T) ≤ δ_n^{-(εReg+tubeLoss)} * 10^20 * n^7
    where C_T = 5 * dataK * C₁. -/
lemma tube_majorant
    {n : ℕ} {εReg tubeLoss C₁ dataK : ℝ}
    (hn_pos : 0 < n)
    (hεReg_pos : 0 < εReg)
    (htubeLoss_pos : 0 < tubeLoss)
    (hC₁_ge1 : 1 ≤ C₁)
    (hK_ge1 : 1 ≤ dataK)
    (hC₁_bound : C₁ ≤ (DiscretisedFurstenbergEstimate.dyadicDelta n)^(-(εReg + tubeLoss)))
    (hK_bound : dataK ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7) :
    max 1 (10 * (5 * dataK * C₁)) ≤
      (DiscretisedFurstenbergEstimate.dyadicDelta n)^(-(εReg + tubeLoss)) * (10 : ℝ)^20 * (n : ℝ)^7 := by
  have h_n_ge1 : (n : ℝ) ≥ 1 := by exact_mod_cast hn_pos
  have h4n7_le : 4 * (n : ℝ) + 7 ≤ 11 * (n : ℝ) := by linarith
  have hK_poly : dataK ≤ (10 : ℝ)^18 * (n : ℝ)^7 := by
    calc dataK
      ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7 := hK_bound
    _ ≤ 2700 * 3145728 * (11 * (n : ℝ))^7 := by gcongr
    _ = 2700 * 3145728 * (11 : ℝ)^7 * (n : ℝ)^7 := by ring
    _ ≤ (10 : ℝ)^18 * (n : ℝ)^7 := by
      have h_const : 2700 * 3145728 * (11 : ℝ)^7 ≤ (10 : ℝ)^18 := by norm_num
      gcongr
  have h50K : 50 * dataK ≤ (10 : ℝ)^20 * (n : ℝ)^7 := by
    calc 50 * dataK
      ≤ 50 * ((10 : ℝ)^18 * (n : ℝ)^7) := by gcongr
    _ = (50 : ℝ) * (10 : ℝ)^18 * (n : ℝ)^7 := by ring
    _ ≤ (10 : ℝ)^20 * (n : ℝ)^7 := by
      have h : (50 : ℝ) * (10 : ℝ)^18 ≤ (10 : ℝ)^20 := by norm_num
      gcongr
  have hCT_ge1 : 1 ≤ 5 * dataK * C₁ := by
    have h1 : 1 ≤ dataK := hK_ge1
    have h4 : 1 ≤ C₁ := hC₁_ge1
    nlinarith
  have h_max : max 1 (10 * (5 * dataK * C₁)) = 10 * (5 * dataK * C₁) := by
    have h5 : 1 ≤ 10 * (5 * dataK * C₁) := by
      have h6 : 1 ≤ 5 * dataK * C₁ := hCT_ge1
      linarith
    rw [max_eq_right] <;> linarith
  rw [h_max]
  have hδn_pos : 0 < DiscretisedFurstenbergEstimate.dyadicDelta n :=
    DiscretisedFurstenbergEstimate.dyadicDelta_pos n
  have h_main : 10 * (5 * dataK * C₁) ≤
      (DiscretisedFurstenbergEstimate.dyadicDelta n)^(-(εReg + tubeLoss)) * (10 : ℝ)^20 * (n : ℝ)^7 := by
    have h_rpow_nonneg : 0 ≤ (DiscretisedFurstenbergEstimate.dyadicDelta n)^(-(εReg + tubeLoss)) :=
      Real.rpow_nonneg hδn_pos.le _
    have h50K_nonneg : 0 ≤ 50 * dataK := by positivity
    calc 10 * (5 * dataK * C₁)
      = 50 * dataK * C₁ := by ring
    _ ≤ 50 * dataK * (DiscretisedFurstenbergEstimate.dyadicDelta n)^(-(εReg + tubeLoss)) := by
      exact mul_le_mul_of_nonneg_left hC₁_bound h50K_nonneg
    _ = (DiscretisedFurstenbergEstimate.dyadicDelta n)^(-(εReg + tubeLoss)) * (50 * dataK) := by ring
    _ ≤ (DiscretisedFurstenbergEstimate.dyadicDelta n)^(-(εReg + tubeLoss)) * ((10 : ℝ)^20 * (n : ℝ)^7) := by
      gcongr <;> exact h50K
    _ = (DiscretisedFurstenbergEstimate.dyadicDelta n)^(-(εReg + tubeLoss)) * (10 : ℝ)^20 * (n : ℝ)^7 := by ring
  exact h_main

/-- Point majorant integration wrapper.
    Given C_P ≤ δ_n^{-(εReg+pointLoss)} and polynomial bounds, proves
    C_P * 18 * numDyadicLevels(N) * 9 * K_global ≤ δ_n^{-(εReg+pointLoss)} * 10^50 * n^16. -/
lemma point_majorant_integration
    {n N : ℕ} {C_P K_B1 K_global : ℝ}
    {εReg pointLoss : ℝ}
    (δ_n : ℝ)
    (hn_pos : 0 < n)
    (hN_pos : 0 < N)
    (hN_le : N ≤ 4^n)
    (hδn_pos : 0 < δ_n)
    (hK_B1_nonneg : 0 ≤ K_B1)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7)
    (hK_global_nonneg : 0 ≤ K_global)
    (hK_global_bound : K_global ≤ 2 * K_B1^2)
    (hC_P_bound : C_P ≤ δ_n^(-(εReg + pointLoss))) :
    C_P * 18 * (numDyadicLevels N : ℝ) * 9 * K_global ≤
    δ_n^(-(εReg + pointLoss)) * (10 : ℝ)^50 * (n : ℝ)^16 := by
  set X : ℝ := (1 : ℝ) * 18 * (numDyadicLevels N : ℝ) * 9 * K_global with hX_def
  have h_poly : X ≤ (10 : ℝ)^45 * (n : ℝ)^15 :=
    C_point_poly_bound_general hn_pos hN_pos hN_le
      (show (1 : ℝ) ≤ (10 : ℝ)^6 from by norm_num)
      (show (0 : ℝ) ≤ (1 : ℝ) from by norm_num)
      hK_B1_nonneg hK_B1_bound hK_global_nonneg hK_global_bound
  have hX_simp : X = 18 * (numDyadicLevels N : ℝ) * 9 * K_global := by
    simp [hX_def] <;> ring
  have h_posX : 0 ≤ X := by positivity
  have h_pos_delta : 0 ≤ δ_n^(-(εReg + pointLoss)) := by
    apply Real.rpow_nonneg; exact hδn_pos.le
  have h_n_ge1 : (n : ℝ) ≥ 1 := by exact_mod_cast hn_pos
  have h4 : (10 : ℝ)^45 * (n : ℝ)^15 ≤ (10 : ℝ)^50 * (n : ℝ)^16 := by
    have h5 : (n : ℝ)^15 ≤ (n : ℝ)^16 := by
      have h6 : 1 ≤ (n : ℝ) := h_n_ge1
      calc (n : ℝ)^15
        = (n : ℝ)^15 * 1 := by ring
      _ ≤ (n : ℝ)^15 * (n : ℝ) := by gcongr
      _ = (n : ℝ)^16 := by simp [pow_succ] <;> ring
    have h7 : (10 : ℝ)^45 ≤ (10 : ℝ)^50 := by norm_num
    have h8 : (10 : ℝ)^45 * (n : ℝ)^15 ≤ (10 : ℝ)^50 * (n : ℝ)^15 :=
      mul_le_mul_of_nonneg_right h7 (by positivity)
    have h9 : (10 : ℝ)^50 * (n : ℝ)^15 ≤ (10 : ℝ)^50 * (n : ℝ)^16 :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    exact le_trans h8 h9
  have h1 : C_P * 18 * (numDyadicLevels N : ℝ) * 9 * K_global ≤
      δ_n^(-(εReg + pointLoss)) * X := by
    have h2 : C_P * 18 * (numDyadicLevels N : ℝ) * 9 * K_global = C_P * X := by
      rw [hX_simp] <;> ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right hC_P_bound h_posX
  calc C_P * 18 * (numDyadicLevels N : ℝ) * 9 * K_global
    ≤ δ_n^(-(εReg + pointLoss)) * X := h1
  _ ≤ δ_n^(-(εReg + pointLoss)) * ((10 : ℝ)^45 * (n : ℝ)^15) := by
    exact mul_le_mul_of_nonneg_left h_poly h_pos_delta
  _ ≤ δ_n^(-(εReg + pointLoss)) * ((10 : ℝ)^50 * (n : ℝ)^16) := by
    exact mul_le_mul_of_nonneg_left h4 h_pos_delta
  _ = δ_n^(-(εReg + pointLoss)) * (10 : ℝ)^50 * (n : ℝ)^16 := by ring

/-- Fine branch full transfer: Appendix A fine bound at 9δ_n on retained dyadic
    tubes, through S0 provenance and packing, to original family Ncover at δ. -/
lemma fine_branch_full
    {n : ℕ} {δ_n δ' δ : ℝ}
    {s εA εInc ρ_T loss_fine : ℝ}
    (retainedTubes : Finset (DTb n))
    (originalFamily : Set AffineLine)
    (hδn_pos : 0 < δ_n)
    (hδn_eq : δ_n = δd n)
    (hδn_one : δ_n ≤ 1)
    (hδ'_pos : 0 < δ')
    (hδ'_eq : δ' = δ / 4)
    (hδ_pos : 0 < δ)
    (h_scale : δ_n ≤ δ')
    (h_scale2 : δ' < 4 * δ_n)
    (hδn_leδ : δ_n ≤ δ)
    (hm : ∀ T ∈ retainedTubes, |T.slope| ≤ 1)
    (hb : ∀ T ∈ retainedTubes, |T.intercept| ≤ 3)
    (hs_pos : 0 < s)
    (hεA_pos : 0 < εA)
    (hεInc_pos : 0 < εInc)
    (hρ_T_nonneg : 0 ≤ ρ_T)
    (hloss_fine_nonneg : 0 ≤ loss_fine)
    (h_budget : εInc ≤ εA - ρ_T - loss_fine)
    (h_absorb_Cpack : (FixedPackingBound.C_pack : ℝ) ≤ δ_n ^ (-ρ_T))
    (h_scale_small : δ_n ^ (-loss_fine) ≥ (9 : ℝ)^(2 * s + εA))
    (h_fine9 : ENNReal.ofReal ((9 * δ_n) ^ (-(2 * s + εA))) ≤
        RegularIncidence.Ncover (9 * δ_n) (toAffineLine '' (retainedTubes : Set (DTb n))))
    (h_thick : ∀ (T : DTb n), T ∈ retainedTubes →
        ∃ (ℓ : AffineLine), ℓ ∈ originalFamily ∧
          dist (toAffineLine T) (RegularIncidence.S0_line ℓ) ≤ (15 / 2 : ℝ) * δ') :
    ENNReal.ofReal (δ ^ (-(2 * s + εInc))) ≤
      RegularIncidence.Ncover δ originalFamily := by
  let C_pack := FixedPackingBound.C_pack
  let A : Set AffineLine := toAffineLine '' (retainedTubes : Set (DTb n))
  have hA_fin : A.Finite := Set.Finite.image _ (Finset.finite_toSet _)
  have h_packing : ∀ (x : AffineLine),
      (A ∩ Metric.closedBall x (64 * δ_n)).ncard ≤ C_pack := by
    intro x
    have h := FixedPackingBound.fixed_packing_bound hm hb x
    have h_set : A ∩ Metric.closedBall x (64 * δ_n) =
        toAffineLine '' (retainedTubes : Set (DTb n)) ∩
        Metric.closedBall x (64 * δd n) := by
      have hA : A = toAffineLine '' (retainedTubes : Set (DTb n)) := by
        dsimp only [A] <;> rfl
      have h9 : (64 * δ_n) = (64 * δd n) := by rw [hδn_eq]
      rw [hA, h9]
    rw [h_set]
    exact h
  have h_thick' : ∀ (a : AffineLine), a ∈ A →
      ∃ (b : AffineLine), b ∈ RegularIncidence.S0_line '' originalFamily ∧ dist a b ≤ (15 / 2 : ℝ) * δ' := by
    intro a ha
    rcases ha with ⟨T, hT, rfl⟩
    rcases h_thick T hT with ⟨ℓ, hℓ, hdist⟩
    exact ⟨RegularIncidence.S0_line ℓ, Set.mem_image_of_mem _ hℓ, hdist⟩
  have hLipschitz : ∀ (x y : AffineLine),
      dist (RegularIncidence.S0_line x) (RegularIncidence.S0_line y) ≤ 2 * dist x y := by
    intro x y
    have h := RegularIncidence.S0_line_lipschitz
    exact h.dist_le_mul x y
  have h_prov_ncard : A.ncard ≤ (C_pack : ENNReal) * RegularIncidence.Ncover δ originalFamily :=
    ProvenanceRadiusAddition.provenance_radius_addition_transfer
      (hA_fin := hA_fin)
      (hδn_pos := hδn_pos)
      (hδ'_pos := hδ'_pos)
      (hδ_pos := hδ_pos)
      (h_scale2 := h_scale2)
      (hδ'_eq := hδ'_eq)
      (h_thick := h_thick')
      (hLipschitz := hLipschitz)
      (h_packing := h_packing)
  have h_inj : Set.InjOn toAffineLine (retainedTubes : Set (DTb n)) := by
    intro T1 hT1 T2 hT2 h_eq
    exact FixedPackingBound.toAffineLine_injective_on_bounded
      ⟨hm T1 hT1, hb T1 hT1⟩ ⟨hm T2 hT2, hb T2 hT2⟩ h_eq
  have h_card_eq : A.ncard = (retainedTubes.card : ENNReal) := by
    rw [Set.ncard_image_of_injOn h_inj] <;> simp
  have h_prov : (retainedTubes.card : ENNReal) ≤
      (C_pack : ENNReal) * RegularIncidence.Ncover δ originalFamily := by
    rw [←h_card_eq]
    exact h_prov_ncard
  have h_Cpack_le : (C_pack : ENNReal) ≤ ENNReal.ofReal (δ_n ^ (-ρ_T)) := by
    have h1 : (C_pack : ℝ) ≤ δ_n ^ (-ρ_T) := h_absorb_Cpack
    have h2 : 0 ≤ δ_n ^ (-ρ_T) := by positivity
    have h3 : (C_pack : ENNReal) = ENNReal.ofReal (C_pack : ℝ) := by simp
    rw [h3]
    exact ENNReal.ofReal_le_ofReal h1
  have h_card_bound : (retainedTubes.card : ENNReal) ≤
      ENNReal.ofReal (δ_n ^ (-ρ_T)) * RegularIncidence.Ncover δ originalFamily := by
    calc (retainedTubes.card : ENNReal)
      ≤ (C_pack : ENNReal) * RegularIncidence.Ncover δ originalFamily := h_prov
    _ ≤ ENNReal.ofReal (δ_n ^ (-ρ_T)) * RegularIncidence.Ncover δ originalFamily := by
      gcongr <;> exact h_Cpack_le
  exact SourceFacingTheorem61.fine_branch_transfer
    (hδn_pos := hδn_pos) (hδn_one := hδn_one)
    (hδ_pos := hδ_pos) (hδn_leδ := hδn_leδ)
    (hs_pos := hs_pos)
    (hεA_pos := hεA_pos) (hεInc_pos := hεInc_pos)
    (hρ_T_nonneg := hρ_T_nonneg)
    (retainedDyadic := retainedTubes)
    (f := toAffineLine)
    (h_fine_bound := h_fine9)
    (h_card_bound := h_card_bound)
    (loss_fine := loss_fine) (hloss_fine_nonneg := hloss_fine_nonneg)
    (h_budget := h_budget)
    (h_scale_small := h_scale_small)

/-- Absorb a positive constant C into δ^{-loss} for sufficiently small δ. -/
lemma absorb_constant_local (C loss : ℝ) (hC_pos : 0 < C) (hloss_pos : 0 < loss) :
    ∃ (δR : ℝ), 0 < δR ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ δR → C ≤ δ ^ (-loss) := by
  let δR : ℝ := C ^ (-1 / loss)
  have hδR_pos : 0 < δR := by positivity
  refine' ⟨δR, hδR_pos, _⟩
  intro δ hδ_pos hδ_le
  have h_exp_nonpos : -loss ≤ 0 := by linarith
  have h1 : δR ^ (-loss) ≤ δ ^ (-loss) :=
    Real.rpow_le_rpow_of_nonpos hδ_pos hδ_le h_exp_nonpos
  have h2 : δR ^ (-loss) = C := by
    dsimp only [δR]
    rw [← Real.rpow_mul hC_pos.le]
    have h3 : (-1 / loss) * (-loss) = 1 := by
      field_simp [hloss_pos.ne'] <;> ring
    rw [h3]; simp
  rw [h2] at h1
  exact h1

/-- S0 maps B(0,1) into B(0,3/4). Needed for point square provenance. -/
lemma S0_norm_le_three_quarters {p : EuclideanPlane} (h : ‖p‖ ≤ 1) : ‖S0 p‖ ≤ 3 / 4 := by
  have h_qvec_norm : ‖quarterVec‖ ≤ 1 / 2 := by
    have h1 : ‖quarterVec‖ ^ 2 = 1 / 8 := by
      simp [quarterVec, EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> norm_num
    have h2 : 0 ≤ ‖quarterVec‖ := by positivity
    nlinarith
  calc ‖S0 p‖
    = ‖(1 / 4 : ℝ) • p + quarterVec‖ := by rfl
  _ ≤ ‖(1 / 4 : ℝ) • p‖ + ‖quarterVec‖ := norm_add_le _ _
  _ = (1 / 4 : ℝ) * ‖p‖ + ‖quarterVec‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)] <;> ring
  _ ≤ (1 / 4 : ℝ) * 1 + 1 / 2 := by gcongr
  _ = 3 / 4 := by ring

/-- Convert frontend ENNReal mass bound to real mass bound using rho_sqrt ≤ rho_mass. -/
lemma frontend_mass_adapter
    {n : ℕ} {u rho_sqrt rho_mass : ℝ} {card : ℕ}
    (hδn_pos : 0 < δd n) (hδn_lt_one : δd n < 1)
    (hrho_sqrt_le_rho_mass : rho_sqrt ≤ rho_mass)
    (h_mass_enn : (card : ENNReal) ≥ ENNReal.ofReal ((δd n)^(-u + rho_sqrt))) :
    (card : ℝ) ≥ (δd n)^(-u + rho_mass) := by
  have h_exp : -u + rho_sqrt ≤ -u + rho_mass := by linarith
  have h_pow : (δd n)^(-u + rho_mass) ≤ (δd n)^(-u + rho_sqrt) :=
    Real.rpow_le_rpow_of_exponent_ge hδn_pos hδn_lt_one.le h_exp
  have h_enn : (card : ENNReal) ≥ ENNReal.ofReal ((δd n)^(-u + rho_mass)) := by
    calc (card : ENNReal)
      ≥ ENNReal.ofReal ((δd n)^(-u + rho_sqrt)) := h_mass_enn
    _ ≥ ENNReal.ofReal ((δd n)^(-u + rho_mass)) := by
      exact ENNReal.ofReal_le_ofReal h_pow
  exact_mod_cast h_enn

end DirecretisedFurstenbergEstimate

end
